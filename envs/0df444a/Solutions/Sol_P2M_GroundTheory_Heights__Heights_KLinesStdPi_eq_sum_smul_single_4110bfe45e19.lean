-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KLinesStdPi_eq_sum_smul_single_4110bfe45e19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:00:50.311388+00:00
-- url     : https://prove2.me/submissions/98214982-29f5-4544-afd3-5cad60dda61a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesStdPi

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
open NumberField
open GroundTheory.Heights₂.Heights.KLinesStdPi
namespace GroundTheory.Heights₂.Heights.KLinesStdPi
theorem _root_.solution {K : Type*} [Field K] {k : ℕ} (y : Fin k → 𝓞 K) :
    (fun i => algebraMap (𝓞 K) K (y i)) = ∑ j, y j • (Pi.single j 1 : Fin k → K) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, Algebra.smul_def, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
end GroundTheory.Heights₂.Heights.KLinesStdPi
