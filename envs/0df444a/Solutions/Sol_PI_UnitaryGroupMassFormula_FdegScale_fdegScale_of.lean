-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FdegScale.fdegScale_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:44.297001+00:00
-- url     : https://prove2.me/submissions/26417af9-8800-414d-93df-f59ef7744864

import Definitions.Def_Formalism_PeriodIntegrals_FdegScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeScaling_FdegScaleOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_FdegScale_fdegHC_pos
import Theorems.Thm_PI_UnitaryGroupMassFormula_FdegScale_fdeg_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FdegScale
open PI PI.UpqRep MeasureTheory Finset
open scoped InnerProductSpace
namespace PI.UnitaryGroupMassFormula.FdegScale
theorem _root_.solution (h : PI.HCFdeg) : PI.FdegScale := by
  intro n ε s hs lam hlam
  obtain ⟨c, hc, hC⟩ := h n ε
  refine ⟨c * fdegHC lam / (s : ℝ), div_pos (mul_pos hc (fdegHC_pos hlam)) (by exact_mod_cast hs), ?_⟩
  intro V _ _ σ d hDS hF
  have : CompleteSpace V := hDS.1
  have : Nontrivial V := hDS.2.1
  exact fdeg_smul_eq (muG ε) σ s hs _ d (hC lam V σ hlam hDS) hF
end PI.UnitaryGroupMassFormula.FdegScale
