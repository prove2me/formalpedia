-- Prove2me | solution 1 for PI.LocFramePrimWork.Steps_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:33.813821+00:00
-- url     : https://prove2.me/submissions/1e6845f7-04e9-4846-a10c-327a0325e783

import Definitions.Def_Formalism_PeriodIntegrals_LocFramePrim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
namespace PI.LocFramePrimWork
theorem _root_.solution (h1 : DiffLoc) (h2 : Dual) (h3 : Assemble) : PI.LocFramePrim.Statement := by
  intro F E _ _ _ _ _ v n r Λ Lb e f z hfg hΛ hli hdis hz hprim
  obtain ⟨φ, φz, p1, p2, p3, p4, p5, p6, p7⟩ := h2 F E n r Λ Lb e f z hfg hΛ hli hdis hz hprim
  exact h3 F E v n r Λ Lb e f z (h1 F E v) hΛ hz φ φz p1 p2 p3 p4 p5 p6 p7
end PI.LocFramePrimWork
