-- Prove2me | solution 1 for ThreeSum.LightCyclic.correlation_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:34.327691+00:00
-- url     : https://prove2.me/submissions/45c7344c-9107-47e4-a253-6de7c5398492

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_ThreeSum_LightCyclic_fold_correlation_meets
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_CyclicFold_coeffBound_padTo
import Theorems.Thm_ThreeSum_CyclicFold_padTo_length
import Theorems.Thm_ThreeSum_CyclicFold_vector_length
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_ten_temp_le_word
set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution {pThis pMultiply pHalf pLinear pFill : ℕ} (hThis : P[pThis]? = some (body pMultiply pLinear))
    (C : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill) {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2 ^ k)
    (hAseg : Seg μ a (padTo (2 ^ k) (vector p F))) (hBseg : Seg μ b (padTo (2 ^ k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ)) (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work) (hpf : prod + 2 * 2 ^ k ≤ work) (hdf : dst + p ≤ work)
    (hsep : Apart prod (2 * 2 ^ k) dst p) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2 ^ k) U : ℤ) ≤ lim.word) (hd : d + k + 2 ≤ lim.depth) :
    Meets lim P pThis d [2 ^ k, a, b, prod, dst, work, p] μ (combinedTime k p) fun _ μ' =>
      (∀ r < p, μ' (dst + r) = (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod + 2 * 2 ^ k ≤ j) → (j < dst ∨ dst + p ≤ j) → μ' j = μ j) :=
  by
  have hn : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
  have hAlen : (padTo (2 ^ k) (vector p F)).length = 2 ^ k := padTo_length _ _ (by rw [vector_length]; exact hpn)
  have hBlen : (padTo (2 ^ k) (vector p (fun z => H (-z)))).length = 2 ^ k :=
    padTo_length _ _ (by rw [vector_length]; exact hpn)
  have hfoldword : 4 * (p : ℤ) * (U : ℤ) ^ 2 ≤ lim.word :=
    by
    have ht := LightKaratsuba.ten_temp_le_word (2 ^ k) U hn
    have hpU := Nat.mul_le_mul_right (U ^ 2) (Nat.mul_le_mul_left 4 hpn)
    have ht' : 4 * p * U ^ 2 ≤ LightKaratsuba.wordBound (2 ^ k) U := by nlinarith
    exact (by exact_mod_cast ht' : 4 * (p : ℤ) * (U : ℤ) ^ 2 ≤ (LightKaratsuba.wordBound (2 ^ k) U : ℤ)).trans hword
  apply Meets.of_body hThis
  unfold body combinedTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg (coeffBound_padTo hA (2 ^ k))
              (coeffBound_padTo hB (2 ^ k)) haf hbf hpf hspace hword (d + 1) (by omega))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg (coeffBound_padTo hA (2 ^ k)) (coeffBound_padTo hB (2 ^ k))
            haf hbf hpf hspace hword (d + 1) (by omega))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro res μ₁ hK; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((fold_correlation_meets C.linear (μ := μ₁) (n := 2 ^ k) F H hw hpn (by omega) (by omega) hsep hA hB hK.1
              hfoldword)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (fold_correlation_meets C.linear (μ := μ₁) (n := 2 ^ k) F H hw hpn (by omega) (by omega) hsep hA hB hK.1
            hfoldword)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro res₂ μ₂ hF; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hF.1, ?_⟩
  intro j hj hpj hdj
  exact (hF.2 j hdj).trans (hK.2 j ⟨hj, hpj⟩)
end ThreeSum.LightCyclic
