-- Prove2me | solution 1 for PIW.AdelClassFin.stCong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:54.533487+00:00
-- url     : https://prove2.me/submissions/58c298ad-506e-49f3-ad9e-725b957befb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IsImgTrans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : StCong := by
  intro I U hU
  obtain ⟨g, hg, hsub⟩ := I.topf_basis U (hU.mem_nhds U.one_mem)
  exact ⟨g, hg, fun x hx => hsub hx⟩
end PIW.AdelClassFin
