-- Prove2me | solution 1 for ThreeSum.LightNaturalDot.reduced_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:32:19.292672+00:00
-- url     : https://prove2.me/submissions/a4849540-e3fb-4299-b5d8-f15fff43e029

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Theorems.Thm_ThreeSum_LightNaturalDot_dot_le
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_le
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightNaturalDot
theorem _root_.solution {proc pDot pDigit pDivide srcA srcB n p U V : ℕ}
    (hmain : P[proc]? = some (reducedBody pDot pDigit)) (hdot : P[pDot]? = some body)
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 1 < lim.depth) (hA : srcA + n ≤ lim.space)
    (hB : srcB + n ≤ lim.space) (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ))
    (hreadB : ∀ i < n, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i ≤ U) (hg : ∀ i < n, g i ≤ V)
    (hword : ((20 * ((n + 1) * (U + 1) * (V + 1) + p + 10) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, n, p] μ (reducedTime n U V)
      (fun z ν => z = (((dot f g n) % p : ℕ) : ℤ) ∧ ν = μ) :=
  by
  have hdotBound := dot_le f g hf hg (j := n) le_rfl
  have htotal : n * (U * V) ≤ (n + 1) * (U + 1) * (V + 1) := by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul (show n ≤ n + 1 by omega) (Nat.mul_le_mul (show U ≤ U + 1 by omega) (show V ≤ V + 1 by omega))
  have hwordDot : (((n + 1) * (U + 1) * (V + 1) + 10 : ℕ) : ℤ) ≤ lim.word := by omega
  have hwordDigit : (LightRadixDigit.word (dot f g n) 1 p : ℤ) ≤ lim.word :=
    by
    apply le_trans (Int.ofNat_le.mpr ?_) hword
    unfold LightRadixDigit.word
    omega
  have hvalue : (dot f g n : ℤ) ≤ lim.word := by unfold LightRadixDigit.word at hwordDigit; omega
  have hpWord : (p : ℤ) ≤ lim.word := by unfold LightRadixDigit.word at hwordDigit; omega
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  have htime : LightRadixDigit.time (dot f g n) ≤ 40 * (n * (U * V) + 1) + 100 :=
    by
    unfold LightRadixDigit.time
    omega
  apply Meets.of_body hmain
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
          ((meets (depth := depth + 1) hdot μ f g hw hA hB hreadA hreadB hf hg hwordDot) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (meets (depth := depth + 1) hdot μ f g hw hA hB hreadA hreadB hf hg hwordDot) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightBooleanDot.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightBooleanDot.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightBooleanDot.time] <;> omega)
    on_goal -1 => (rintro z ν ⟨hz, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  subst z
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
    on_goal -1 => (rintro z ν ⟨hz, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  subst z
  simp
end ThreeSum.LightNaturalDot
