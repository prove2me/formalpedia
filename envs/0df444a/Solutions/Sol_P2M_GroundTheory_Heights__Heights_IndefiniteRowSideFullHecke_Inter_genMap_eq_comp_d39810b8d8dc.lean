-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genMap_eq_comp_d39810b8d8dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:02.2657+00:00
-- url     : https://prove2.me/submissions/aa9bbd8b-3ffa-46bf-a3dd-ecc4df0e9036

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_genericEvaluation_rename_inr_2dfe02c66895

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution [DecidableEq K] (P : Ideal (MRing ι)) {N1 : ℕ} (V : S → Fin N1 → MRing ι) :
    genMap P (fun s j => toFn P (V s j)) = (genericEvaluation P).comp (aeval (genericSubstitution V)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
  rintro ⟨k | u, i⟩
  · simp [genMap, genericSubstitution, genericEvaluation, genPt, toFn]
  · change Fin N1 at i
    simp only [genMap, genericSubstitution, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, aeval_X, map_sum, map_mul, genericEvaluation_rename_inr]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [genericEvaluation]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
