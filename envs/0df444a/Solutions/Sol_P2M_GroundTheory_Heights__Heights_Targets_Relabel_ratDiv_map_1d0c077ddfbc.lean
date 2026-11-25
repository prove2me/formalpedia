-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_ratDiv_map_1d0c077ddfbc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:36.797917+00:00
-- url     : https://prove2.me/submissions/3df27a46-7f28-4f3b-b8d8-356655a5985c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_exists_map_eq_b759d115fba2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_divCycle_map_apply_89989eae05a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv (V.map (ringEquiv F e h)) (ringEquiv F e h f) (ringEquiv F e h g) =
      Finsupp.mapDomain (Ideal.map (ringEquiv F e h)) (ratDiv V f g) := by
  ext W'
  obtain ⟨W, rfl⟩ := exists_map_eq e h W'
  rw [Finsupp.mapDomain_apply (map_ringEquiv_injective (ringEquiv F e h))]
  simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, divCycle_map_apply]
end GroundTheory.Heights₂.Heights.Targets.Relabel
