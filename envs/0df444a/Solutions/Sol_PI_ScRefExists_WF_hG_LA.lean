-- Prove2me | solution 1 for PI.ScRefExists.WF.hG_LA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:16.279553+00:00
-- url     : https://prove2.me/submissions/3eb8f7ad-4873-44de-b353-400a940e3b29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_PI_ScRefExists_WF_hG_L
import Theorems.Thm_PI_ScRefExists_WF_mem_LA_iff
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_left
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_right


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
theorem _root_.solution (hp : p.Prime) {x y : Fin I.n → I.E} (hx : x ∈ LA I p) (hy : y ∈ LA I p) :
    hG I x y ∈ Ap I p := by
  obtain ⟨s, hs, hsx⟩ := (mem_LA_iff hp).1 hx
  obtain ⟨t, ht, hty⟩ := (mem_LA_iff hp).1 hy
  obtain ⟨o, ho⟩ := hG_L hsx hty
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, o, ?_⟩
  rw [hG_smul_left, hG_smul_right, star_natCast] at ho
  rw [show ((o : 𝓞 I.E) : I.E) = algebraMap (𝓞 I.E) I.E o from rfl, ho]; push_cast; ring
end PI.ScRefExists.WF
