-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_LocalLatticeBases_kronecker_root_of_unity__f23bb266025f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:24.726215+00:00
-- url     : https://prove2.me/submissions/ef39171f-fa61-40e0-90a6-812ca3acacf9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : KroneckerRootOfUnity := by
  intro K _ _ α hα h0 hle hμ
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ h0 hα hle
  exact hμ α ⟨n, hn, h⟩
end Formalism.HermitianLattices.LocalLatticeBases
