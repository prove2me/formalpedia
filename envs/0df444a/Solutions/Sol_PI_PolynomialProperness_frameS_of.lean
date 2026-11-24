-- Prove2me | solution 1 for PI.PolynomialProperness.frameS_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:43:51.607355+00:00
-- url     : https://prove2.me/submissions/d5d6240f-f0aa-426e-8cf6-1027c613bd94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnipotentFixesFrameVector

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
theorem _root_.solution (hU : UMapFrame) (hG : GVGroup) : FrameS := by
  intro k r z hz s hs
  have hs' := hs
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  obtain ⟨hf, hut, -⟩ := (hU k r z hz).1 _ hs'
  exact ⟨(hG k r).1 _ hh.1 _ hm.1, uMap k r z (h * m), hut, hf⟩
end PI.PolynomialProperness
