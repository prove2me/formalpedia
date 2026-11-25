-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_zeroSet_subset_biUnion_minimalPrimes_30b5b55c15ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:41:06.705217+00:00
-- url     : https://prove2.me/submissions/29f23e70-5d2d-4187-94f5-a95271d7359b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetTubeVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSet I ⊆ ⋃ P ∈ I.minimalPrimes, zeroSet P := by
  intro x hx
  have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hle
  exact Set.mem_biUnion hP fun q hq => (RingHom.mem_ker).1 (hPle hq)
end GroundTheory.Heights₂.Heights
