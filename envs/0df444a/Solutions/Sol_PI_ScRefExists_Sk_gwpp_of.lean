-- Prove2me | solution 1 for PI.ScRefExists.Sk.gwpp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:20:57.365011+00:00
-- url     : https://prove2.me/submissions/ca35ea11-d00d-4615-a332-3a24ff6fd2e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.Sk
namespace PI.ScRefExists.Sk
theorem _root_.solution (h1 : WFrame) (h2 : PPAssemble) : GWpp := by
  intro I p m r k θ e f M hp hm hH
  obtain ⟨_, _, _, hn, hee, hff, hef, hM, hL⟩ := id hH
  have hMp : Nat.Coprime M p :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hM
  obtain ⟨w, wd, hw, horth, hdual, hspan⟩ := h1 I p r k e f M hp hn hee hff hef hMp hL
  exact h2 I p m r k θ e f M w wd hp hm hH hw horth hdual hspan
end PI.ScRefExists.Sk
