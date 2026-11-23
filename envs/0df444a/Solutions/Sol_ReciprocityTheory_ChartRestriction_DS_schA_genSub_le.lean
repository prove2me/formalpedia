-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.schA_genSub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:39.104299+00:00
-- url     : https://prove2.me/submissions/21fe6fba-e22e-4038-83fb-9730d97f3f70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_SchurA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {Λ : Fin n → ℝ} (hV : IsKIrrHW ε E Λ V) (X : Submodule ℂ M)
    (hX : ∀ a b, ∀ x ∈ X, E a b x ∈ X) {x : M} (hxV : x ∈ V) (hxX : x ∈ X) (hx0 : x ≠ 0) :
    genSub E V ≤ X := by
  obtain ⟨-, hVk, hirr, -⟩ := hV
  have hst : IsKStableSub ε E (V ⊓ X) := fun a b hab v hv => ⟨hVk a b hab v hv.1, hX a b v hv.2⟩
  have hVX : V ≤ X := by
    rcases hirr (V ⊓ X) inf_le_left hst with h | h
    · have hx : x ∈ V ⊓ X := ⟨hxV, hxX⟩
      rw [h] at hx
      exact absurd ((Submodule.mem_bot ℂ).1 hx) hx0
    · exact inf_eq_left.1 h
  unfold genSub
  exact sInf_le ⟨hVX, hX⟩
end ReciprocityTheory.ChartRestriction.DS
