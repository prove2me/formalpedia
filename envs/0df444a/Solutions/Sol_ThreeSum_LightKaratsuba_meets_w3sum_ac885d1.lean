-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:15.405355+00:00
-- url     : https://prove2.me/submissions/98158bf4-86b2-45c5-a6f1-6f5a704081bc

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_LightKaratsuba_base_ends
import Theorems.Thm_ThreeSum_LightKaratsuba_base_product
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightKaratsuba_ten_temp_le_word
import Definitions.Def_WeightedCache3SUM_Alias_86468cc403fc1e4a
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (C : Procs P pSelf pHalf pLinear pFill) (hw : (lim.space : ℤ) ≤ lim.word) {k a b out work U : ℕ}
    {as bs : List ℤ} {μ : ℕ → ℤ} (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k) (hAseg : Seg μ a as)
    (hBseg : Seg μ b bs) (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ)) (haf : a + 2 ^ k ≤ work)
    (hbf : b + 2 ^ k ≤ work) (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (wordBound (2 ^ k) U : ℤ) ≤ lim.word) :
    ∀ d,
      d + k + 1 ≤ lim.depth →
        Meets lim P pSelf d [2 ^ k, a, b, out, work] μ (time k) (fun _ μ' => Result μ out (2 ^ k) work as bs μ') :=
  by
  induction k generalizing a b out work U as bs μ with
  | zero =>
    simp only [pow_zero] at hAlen hBlen haf hbf hof hspace hword ⊢
    intro d hd
    have hvA : |μ a| ≤ (U : ℤ) := by
      have hr := hAseg.getD (by omega : 0 < as.length) 0
      simpa only [← hr, Nat.add_zero] using hA 0
    have hvB : |μ b| ≤ (U : ℤ) := by
      have hr := hBseg.getD (by omega : 0 < bs.length) 0
      simpa only [← hr, Nat.add_zero] using hB 0
    have hp : |μ a * μ b| ≤ (U : ℤ) ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hvA hvB (abs_nonneg _) (Nat.cast_nonneg U)
    have hpw : (U : ℤ) ^ 2 ≤ lim.word :=
      by
      have hh : 10 * ((4 * 1 * U ^ 2 : ℕ) : ℤ) ≤ wordBound 1 U := by exact_mod_cast ten_temp_le_word 1 U (by decide)
      push_cast at hh
      nlinarith only [hh, hword, sq_nonneg (U : ℤ)]
    have hbases :=
      base_ends (P := P) (d := d) (a := a) (b := b) (out := out) (work := work) hw (by omega) (by omega) (by omega)
        (hp.trans hpw)
    refine Meets.of_body C.self ?_
    unfold body
    refine
      Ends.iteLast (fun hc => False.elim (by simpa using hc)) (fun _ => ?_) (hT := by simp [time, Cond.cost, Expr.cost])
    refine hbases.mono (by norm_num [time, Cond.cost, Expr.cost]) ?_
    intro σ' hr
    exact ⟨base_product hAseg hBseg hAlen hBlen hr.1 hr.2.1, fun j hj => hr.2.2 j hj.2⟩
  | succ k ih =>
    intro d hd
    have hp : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
    have hpZ : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by norm_num) k
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have heZ : (2 : ℤ) ^ (k + 1) = 2 * ((2 ^ k : ℕ) : ℤ) :=
      by
      push_cast
      rw [pow_succ, mul_comm]
    rw [he] at hAlen hBlen haf hbf hof hspace hword ⊢
    rw [heZ]
    refine Meets.of_body C.self ?_
    unfold body
    refine
      Ends.iteLast (fun _ => ?_) (fun hc => ?_) (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | (ring_nf; omega)))
    ·
      exact
        recurse_ends C rfl hw hAlen hBlen hAseg hBseg hA hB haf hbf hof hspace hword (by omega)
          (fun a' b' out' work' U' as' bs' μ' hla hlb hsa hsb hba hbb hfa hfb hfo hsp hwo =>
            ih hla hlb hsa hsb hba hbb hfa hfb hfo hsp hwo (d + 1) (by omega))
    · have hfalse : ¬(1 : ℤ) < 2 * (2 : ℤ) ^ k := by simpa using hc
      have hone : (1 : ℤ) ≤ (2 : ℤ) ^ k := hpZ
      omega
end ThreeSum.LightKaratsuba
