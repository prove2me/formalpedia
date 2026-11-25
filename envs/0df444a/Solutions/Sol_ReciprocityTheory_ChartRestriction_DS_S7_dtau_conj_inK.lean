-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dtau_conj_inK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:25.567746+00:00
-- url     : https://prove2.me/submissions/14c8c6b1-3f0a-4fc5-9a28-f15afa92d4f2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_inK_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_exists_oneParam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    T.op k * T.dτ A * T.op k⁻¹ = T.dτ (toMK k * A * toMK k⁻¹) := by
  obtain ⟨γ, -, hγ, -⟩ := exists_oneParam ε hA
  have h1 := ((T.hasDeriv A hA γ hγ).const_mul (T.op k)).mul_const (T.op k⁻¹)
  have h2 := T.hasDeriv _ (inK_conj k hA) (fun t => k * γ t * k⁻¹) (fun t => by
    have e : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e, hγ, show ((t : ℂ) • (toMK k * A * toMK k⁻¹)) = toMK k * ((t : ℂ) • A) * toMK k⁻¹ by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    exact (Matrix.exp_units_conj ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).symm)
  have e : (fun t => T.op (k * γ t * k⁻¹)) = fun t => T.op k * T.op (γ t) * T.op k⁻¹ :=
    funext fun t => by simp only [KType.op, map_mul]; rfl
  rw [e] at h2
  exact h1.unique h2
end ReciprocityTheory.ChartRestriction.DS.S7
