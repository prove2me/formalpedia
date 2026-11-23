-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exists_norm_actM_pow_le_of_inK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:24.201912+00:00
-- url     : https://prove2.me/submissions/4d10a4a4-48bc-41d9-82b8-8035f7c82854

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ClosureK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_actM_mem_layer_of_inK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_layer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {V : Submodule ℂ D} (hE : IsGlRep E)
    (hV : IsKStableSub ε E V) (hVf : FiniteDimensional ℂ V) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : inK ε Z) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ layer ε E V k, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ (layer ε E V k) := finiteDimensional_layer hVf k
  let T : layer ε E V k →ₗ[ℂ] layer ε E V k :=
    (actM E Z).restrict (fun x hx => actM_mem_layer_of_inK hE hV hZ hx)
  let T' := LinearMap.toContinuousLinearMap T
  refine ⟨‖T'‖, norm_nonneg _, fun x hx m => ?_⟩
  have hpow : ∀ m : ℕ, ((actM E Z) ^ m) x = (((T ^ m) ⟨x, hx⟩ : layer ε E V k) : D) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  have hnorm : ∀ (m : ℕ) (y : layer ε E V k), ‖(T ^ m) y‖ ≤ ‖T'‖ ^ m * ‖y‖ := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      calc ‖T ((T ^ m) y)‖ = ‖T' ((T ^ m) y)‖ := rfl
        _ ≤ ‖T'‖ * ‖(T ^ m) y‖ := T'.le_opNorm _
        _ ≤ ‖T'‖ * (‖T'‖ ^ m * ‖y‖) := by gcongr; exact ih y
        _ = ‖T'‖ ^ (m + 1) * ‖y‖ := by ring
  rw [hpow]
  exact hnorm m ⟨x, hx⟩
end ReciprocityTheory.ChartRestriction.DS
