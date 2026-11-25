-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_primeFrac_1bb1ff15a839
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:01.971693+00:00
-- url     : https://prove2.me/submissions/e0ec2fa0-0e04-4a22-8866-7a91e4bcc9f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound

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
theorem _root_.solution (L : Type) [Field L] [NumberField L] (q : ℕ) :
    Real.log (FractionalIdeal.absNorm (primeFrac L q) : ℝ) = Module.finrank ℚ L * Real.log q := by
  rw [primeFrac, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  push_cast
  rw [Real.log_pow]
end GroundTheory.Heights₂.Heights.NineStatements
