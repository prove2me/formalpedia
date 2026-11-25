-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_quotH_equiv_a468c3a14426
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:44.576013+00:00
-- url     : https://prove2.me/submissions/2e59a142-2a27-4e0c-9708-6d3fa9f0370b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrictQuotX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_support_subset_d90ca596ffab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_mem_twist_ideal_of_not_subset_f0cb625b4a65
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_chartEquiv_mk_22d16b1d6585

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
namespace GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
theorem _root_.solution {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (i : ℕ) :
    Nonempty (SubSystem.quotH L.toSubSystem (L.toSubSystem.twist (idealSys x pp)) i ≃ₗ[S]
      L'.toSubSystem.H i) := by
  refine ⟨Cech.equivHRestr (support_subset hxy) (fun J => chartEquiv h hpy J) ?_ ?_ i⟩
  · intro J J' hJJ' m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    apply Subtype.ext
    have e1 := congrArg Subtype.val
      (chartEquiv_mk h hpy J' (L.toSubSystem.res (liftChart hxy J) (liftChart hxy J') hJJ' z))
    have e2 := congrArg Subtype.val (chartEquiv_mk h hpy J z)
    exact e1.trans e2.symm
  · intro I hI m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_twist_ideal_of_not_subset hpy.le _ I hI z.2)
end GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
