-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_mem_heightOneSpectrum_c3aeab300187
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:25.486848+00:00
-- url     : https://prove2.me/submissions/450b5183-098e-4218-aa95-0fac09c1557d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_exists_prime_natCast_mem_3bd80a14c2c7

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ v.asIdeal := by
  have := v.isPrime
  refine exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal) ?_ (Ideal.absNorm_mem _)
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot
end GroundTheory.Heights₂.Heights.NineStatements
