-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPositive_ringKrullDim_primeOfOne_7d3697857068
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:05:36.386803+00:00
-- url     : https://prove2.me/submissions/0b42a274-9d94-4be9-a7f2-f1847ba9f1b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegreePos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedHilbertPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PModulesFromPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRankOfSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive
theorem _root_.solution (y : Fin (N + 1) → Ω) :
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ringKrullDim (Poly k N ⧸ primeOf (S := k) y) := by
  let f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (blockEquiv N)).toRingEquiv
  have hc : primeOfOne (S := k) y = (primeOf (S := k) y).comap f.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have h : primeOf (S := k) y = (primeOfOne (S := k) y).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive
