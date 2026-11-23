-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.orth_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:23.085519+00:00
-- url     : https://prove2.me/submissions/e2e2bdb3-bcdf-4e3e-94c3-0e13373ba0fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inner_map_map__a3d9c3698dd1

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
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hg' : g' ∈ UJset ε) (hgg : g * g' = 1) (T : Submodule ℂ H) (hT : ∀ x ∈ T, σ g' x ∈ T) :
    ∀ x ∈ Tᗮ, σ g x ∈ Tᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hy' : σ g (σ g' y) = y := by
    have h := hσ.1.2 g hg g' hg'
    rw [hgg, hσ.1.1] at h
    have h' := congrArg (fun f : H →L[ℂ] H => f y) h
    simpa using h'.symm
  rw [← hy', inner_map_map' hσ hg]
  exact hx _ (hT y hy)
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
