-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inner_map_map__a3d9c3698dd1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:50.711534+00:00
-- url     : https://prove2.me/submissions/8bb5057d-3dce-4b5e-bd5a-7bd847d88e85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA

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
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (x y : H) : inner ℂ (σ g x) (σ g y) = inner ℂ x y :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
