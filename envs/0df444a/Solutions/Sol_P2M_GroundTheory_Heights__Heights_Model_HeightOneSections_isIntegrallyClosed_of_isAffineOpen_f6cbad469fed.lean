-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_isIntegrallyClosed_of_isAffineOpen_f6cbad469fed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:00.597005+00:00
-- url     : https://prove2.me/submissions/dc52cde3-5547-43df-a3df-b22970d9585c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
namespace GroundTheory.Heights₂.Heights.Model.HeightOneSections
theorem _root_.solution (hN : IsNormalScheme X) {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  have hy := fromSpec_mem hV ⟨P, hP.isPrime⟩
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf
    (⟨hV.fromSpec ⟨P, hP.isPrime⟩, hy⟩ : V)
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hV.isLocalization_stalk' ⟨P, hP.isPrime⟩ hy
  have := hN (hV.fromSpec ⟨P, hP.isPrime⟩)
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv
end GroundTheory.Heights₂.Heights.Model.HeightOneSections
