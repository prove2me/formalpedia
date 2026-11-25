-- Prove2me | solution 1 for PI.ScRefExists.WF.proj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:14.937741+00:00
-- url     : https://prove2.me/submissions/654957d1-499e-443f-84dd-f7c7537f111d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_ap_smul
import Theorems.Thm_PI_ScRefExists_WF_hG_LA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution (hp : p.Prime) {r : ℕ} {e f : Fin r → Fin I.n → I.E}
    (heA : ∀ a, e a ∈ LA I p) (hfA : ∀ a, f a ∈ LA I p) {y : Fin I.n → I.E} (hy : y ∈ LA I p) :
    proj e f y ∈ LA I p := by
  unfold proj
  refine Submodule.sum_mem _ fun a _ => Submodule.add_mem _ ?_ ?_
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (f a) y, hG_LA hp (hfA a) hy⟩ : Ap I p) (heA a)
    rwa [ap_smul] at h1
  · have h1 := Submodule.smul_mem (LA I p) (⟨hG I (e a) y, hG_LA hp (heA a) hy⟩ : Ap I p) (hfA a)
    rwa [ap_smul] at h1
end PI.ScRefExists.WF
