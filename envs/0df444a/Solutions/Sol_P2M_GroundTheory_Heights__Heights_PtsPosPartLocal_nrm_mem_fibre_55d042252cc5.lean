-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_mem_fibre_55d042252cc5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:44.711248+00:00
-- url     : https://prove2.me/submissions/4680fa16-d57e-49b3-8fab-5123acb96e6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_map_nrm_56a440ac24b8
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {P : Ideal (MRing ι)} (hPh : IsMultiHomogIdeal P) (k0 : K)
    {z' : (Σ k, ι k) → ℂ} (hz' : z' ∈ mcPts P) (h0 : Ψ (segre z') 0 ≠ 0) :
    nrm Ψ (segre z') ∈ fibre P Ψ (crd Ψ (segre z')) := by
  classical
  set c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z') 0)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h0]
    · simp [hcdef, Function.update_of_ne hk]
  have hprod : ∏ k, c k = (Ψ (segre z') 0)⁻¹ := by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * z' p, mcPts_smul hPh c hc hz', ?_, map_nrm h0⟩
  rw [segre_smul, hprod]
  rfl
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
