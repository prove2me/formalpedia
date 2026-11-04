-- Prove2me | solution 1 for ThreeSum.LightPolynomialCoefficient.reduced_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:24.671779+00:00
-- url     : https://prove2.me/submissions/ff72fbbd-5929-49bb-9ee4-4ecda2086be0

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_bound
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightPolynomialCoefficient
theorem _root_.solution {proc pRaw pDigit pDivide srcA srcB n m k p : ℕ}
    (hp : P[proc]? = some (reducedBody pRaw pDigit)) (hraw : P[pRaw]? = some body)
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 1 < lim.depth) (hA : srcA + n ≤ lim.space)
    (hB : srcB + m ≤ lim.space) (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ))
    (hreadB : ∀ i < m, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i < p) (hg : ∀ i < m, g i < p)
    (hword : ((20 * ((n + 1) * (p + 1) ^ 2 + k + m + 10) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, n, m, k, p] μ (reducedTime n p)
      (fun r ν => r = (coefficient p f g n m k : ℤ) ∧ ν = μ) :=
  by
  have hrawBound := raw_bound f g hf hg (j := n) le_rfl (k := k)
  have hwordRaw : (((n + 1) * (p + 1) ^ 2 + k + m + 10 : ℕ) : ℤ) ≤ lim.word := by omega
  have hbase : n * p ^ 2 ≤ (n + 1) * (p + 1) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
  have hwordDigit : (LightRadixDigit.word (rawCoefficient f g n m k) 1 p : ℤ) ≤ lim.word :=
    by
    apply le_trans (Int.ofNat_le.mpr ?_) hword
    unfold LightRadixDigit.word
    nlinarith [Nat.le_refl ((n + 1) * (p + 1) ^ 2)]
  have hval : ((rawCoefficient f g n m k : ℕ) : ℤ) ≤ lim.word :=
    by
    unfold LightRadixDigit.word at hwordDigit
    omega
  have hpWord : (p : ℤ) ≤ lim.word := by
    unfold LightRadixDigit.word at hwordDigit
    omega
  have hone : (1 : ℤ) ≤ lim.word := by omega
  have htimeDigit : LightRadixDigit.time (rawCoefficient f g n m k) ≤ 40 * (n * p ^ 2 + 1) + 100 :=
    by
    unfold LightRadixDigit.time
    omega
  apply Meets.of_body hp
  unfold reducedBody reducedTime
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
          ((meets (depth := depth + 1) hraw μ f g hw hA hB hreadA hreadB hf hg hwordRaw) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (meets (depth := depth + 1) hraw μ f g hw hA hB hreadA hreadB hf hg hwordRaw) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    on_goal -1 => (rintro r ν ⟨hr, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  subst r
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
          ((LightRadixDigit.meets (d := depth + 1) hdigit hdivide μ hd hwordDigit) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (LightRadixDigit.meets (d := depth + 1) hdigit hdivide μ hd hwordDigit) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightRadixDigit.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightRadixDigit.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightRadixDigit.time] <;> omega)
    on_goal -1 => (rintro r ν ⟨hr, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  subst r
  simp [coefficient]
end ThreeSum.LightPolynomialCoefficient
