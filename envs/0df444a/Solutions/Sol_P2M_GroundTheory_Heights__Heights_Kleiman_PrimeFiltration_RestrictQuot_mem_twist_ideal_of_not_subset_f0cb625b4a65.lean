-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_RestrictQuot_mem_twist_ideal_of_not_subset_f0cb625b4a65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:51.076825+00:00
-- url     : https://prove2.me/submissions/6ef4c821-ef52-4ca1-9516-882e5d6d450a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrictQuotX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
theorem _root_.solution {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y ≤ pp)
    (F : SubSystem S x Ω) (I : Chart x) (hI : ¬ I.1 ⊆ support y) {z : Ω} (hz : z ∈ F.sub I) :
    z ∈ (F.twist (idealSys x pp)).sub I := by
  obtain ⟨i, hiI, hiy⟩ := Finset.not_subset.mp hI
  have hyi : y i = 0 := by
    by_contra h0; exact hiy ((mem_support y).mpr h0)
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hiI)
  have hXp : (X i : Poly S N) ∈ pp :=
    hpp ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi]))
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hXp, X_mem_monos hiI, isHomogeneous_X S i, isHomogeneous_X S i,
      by rw [aeval_X, div_self hxi]⟩
  exact Submodule.subset_span ⟨1, h1, z, hz, (one_smul _ _).symm⟩
end GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot
