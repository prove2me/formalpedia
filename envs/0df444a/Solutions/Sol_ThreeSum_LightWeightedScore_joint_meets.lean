-- Prove2me | solution 1 for ThreeSum.LightWeightedScore.joint_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:45.493562+00:00
-- url     : https://prove2.me/submissions/7fb96e25-fd59-4714-b94a-c14046720bf8

import Definitions.Def_Submission_ThreeSum_WeightedScore
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
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
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightResidues_emodTime_le
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
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
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedScore
open Light WeightedModuli WeightedScore LightResidues
variable {lim : Limits} {P : Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightWeightedScore
theorem _root_.solution {pJoint pEmod : ℕ} (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody) {μ : ℕ → ℤ} {q p maxMod free : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d < lim.depth) (hq : 0 < q) (hp : 0 < p) (hmax : q * p ≤ maxMod)
    (hspace : free + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space) (hword : (8 * maxMod + 16 : ℕ) ≤ lim.word) :
    Meets lim P pJoint d [q, p, free] μ (jointTime maxMod) fun r μ' => r = (joint q p : ℤ) ∧ Kept μ μ' free :=
  by
  have hqmax : q ≤ maxMod := (Nat.le_mul_of_pos_right q hp).trans hmax
  have hpmax : p ≤ maxMod := (Nat.le_mul_of_pos_left p hq).trans hmax
  have hpre : Emod.Pre lim p maxMod free :=
    ⟨hp, hw, by
      have hpZ : (p : ℤ) ≤ maxMod := by exact_mod_cast hpmax
      have hwZ : (8 * (maxMod : ℤ) + 16) ≤ lim.word := by exact_mod_cast hword
      omega, hspace⟩
  have hx : |(q : ℤ)| ≤ (maxMod : ℤ) := by simpa using (Int.ofNat_le.mpr hqmax)
  have ht := emodTime_le (p := p) hx
  simp only [Int.natAbs_natCast] at ht
  unfold emodTime residueBudget at ht
  have hlog : Nat.log 2 (1 + maxMod) = Nat.log 2 (maxMod + 1) := by rw [Nat.add_comm]
  have hmulZ : (q : ℤ) * (p : ℤ) ≤ lim.word :=
    by
    have hh : ((q * p : ℕ) : ℤ) ≤ (maxMod : ℤ) := by exact_mod_cast hmax
    have hwZ : (8 * (maxMod : ℤ) + 16) ≤ lim.word := by exact_mod_cast hword
    push_cast at hh
    omega
  apply Meets.of_body hjoint
  unfold jointBody jointTime
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
    | refine _root_.Light.Ends.callToThen ((emod_meets (x := (q : ℤ)) hem hpre hx) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (emod_meets (x := (q : ℤ)) hem hpre hx) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residueBudget]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [residueBudget] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, residueBudget] <;> omega)
    on_goal -1 => (rintro result μ₁ ⟨hresult, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst result
  refine
    Ends.iteLast (fun hz => ?_) (fun hnz => ?_)
      (by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
      (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residueBudget]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [residueBudget] <;>
            first
            | omega
            | (ring_nf; omega)))
  · have hdiv : p ∣ q := by
      have hh : (q : ℤ) % (p : ℤ) = 0 := by simpa using hz
      exact Int.natCast_dvd_natCast.mp (Int.dvd_of_emod_eq_zero hh)
    apply Ends.skip
    exact ⟨by simp [joint, hdiv], hkeep⟩
  · have hnot : ¬p ∣ q := by
      intro hh
      apply hnz
      have he : (q : ℤ) % (p : ℤ) = 0 := Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hh)
      simpa using he
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (q * p : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, jointTime,
              residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [jointTime, residueBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, jointTime, residueBudget] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [joint, hnot], hkeep⟩
end ThreeSum.LightWeightedScore
