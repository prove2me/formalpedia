-- Prove2me | solution 1 for P2M_PI_PolynomialProperness_frameSg__of_34c40b5599d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:02.656752+00:00
-- url     : https://prove2.me/submissions/b5c3be76-0dcd-4e5d-908f-d2fa53d181bd

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
theorem _root_.solution (hU : UMapFrame) (hT : TauMem) (hG : GVGroup) : FrameSg' := by
  intro k r z z' γ hstd σ hσ
  obtain ⟨n0, hn, v, hv, hPv, h, hh, rfl⟩ := hσ
  obtain ⟨h1, h2⟩ := sg_frame hU hT hG hstd.2.2 hn hv hh
  exact ⟨h1, v, hv, hPv, h2⟩
end PI.PolynomialProperness
