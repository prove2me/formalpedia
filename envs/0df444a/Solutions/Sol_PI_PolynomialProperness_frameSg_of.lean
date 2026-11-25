-- Prove2me | solution 1 for PI.PolynomialProperness.frameSg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:52:24.393507+00:00
-- url     : https://prove2.me/submissions/b3805bcc-e25f-4079-bc3f-38dd4e3c65d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnipotentFixesFrameVector
import Theorems.Thm_PI_PolynomialProperness_sg_frame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hvL, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.1 hn hv hh
  exact ⟨h1, v, hv, hvL, h2⟩
end PI.PolynomialProperness
