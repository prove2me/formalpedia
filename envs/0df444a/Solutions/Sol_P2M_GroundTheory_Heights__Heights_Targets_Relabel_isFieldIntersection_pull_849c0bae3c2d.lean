-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isFieldIntersection_pull_849c0bae3c2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:19.031928+00:00
-- url     : https://prove2.me/submissions/71418903-2e62-4464-aba7-10974b79dbf9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_snoc_comp_2c85a72d5335
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_cycEval_mapDomain_006092ad837c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_exists_map_eq_b759d115fba2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_comap_map_91dd5e903145
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isProjVarF_map_iff_c536fdc6a750
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isChart_of_map_ff6e6ce7aa6c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ptDeg_map_97ccd73c0d80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ratDiv_map_1d0c077ddfbc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_isRatSection_of_map_55aaddf39d7c

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
theorem _root_.solution {I : IFamily F ι} (hI : IsFieldIntersection I) :
    IsFieldIntersection (pullFamily e h I) := by
  refine ⟨fun V' L i' hV' hi' => ?_, fun V' n L A f' g' hV' hs => ?_⟩
  · obtain ⟨V, rfl⟩ := exists_map_eq e h V'
    show I _ 0 _ = _
    rw [comap_map, ptDeg_map]
    exact hI.1 V _ _ ((isProjVarF_map_iff e h V 0).1 hV') (isChart_of_map e h hi')
  · obtain ⟨V, rfl⟩ := exists_map_eq e h V'
    obtain ⟨f, rfl⟩ := (ringEquiv F e h).surjective f'
    obtain ⟨g, rfl⟩ := (ringEquiv F e h).surjective g'
    show I _ (n + 1) _ = _
    rw [comap_map, snoc_comp e L A,
      hI.2 V n _ (A ∘ e) f g ((isProjVarF_map_iff e h V _).1 hV') (isRatSection_of_map e h hs),
      ratDiv_map, cycEval_mapDomain]
    simp only [pullFamily, comap_map]
end GroundTheory.Heights₂.Heights.Targets.Relabel
