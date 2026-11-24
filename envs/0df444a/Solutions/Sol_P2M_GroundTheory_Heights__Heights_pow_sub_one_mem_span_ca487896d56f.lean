-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_pow_sub_one_mem_span_ca487896d56f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:57.253107+00:00
-- url     : https://prove2.me/submissions/d5262f23-8e39-4880-af08-20e2ef2a3edf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch

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
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (g : MvPolynomial ι R) (k : ℕ) :
    (X none * rename some g) ^ k - 1 ∈
      (Ideal.span {X none * rename some g - 1} : Ideal (MvPolynomial (Option ι) R)) := by
  rw [Ideal.mem_span_singleton]
  simpa using sub_dvd_pow_sub_pow (X none * rename some g : MvPolynomial (Option ι) R) 1 k
end GroundTheory.Heights₂.Heights
