-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.clsBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:08.696151+00:00
-- url     : https://prove2.me/submissions/d6a9be83-7453-4402-8028-0b4f71381670

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_cls
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_cls
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_cls_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution : ClsBound := by
  intro n s hs p q R z
  refine ⟨contDiff_cls hs z p q R, fun L => ?_⟩
  obtain ⟨R', hR'⟩ : ∃ R', L.foldr (fun kl g => Dkl kl.1 kl.2 g) (cls s z p q R) = cls s z p q R' := by
    induction L with
    | nil => exact ⟨R, rfl⟩
    | cons kl L ih =>
      obtain ⟨R', h⟩ := ih
      refine ⟨dR s z p q kl.1 kl.2 R', ?_⟩
      rw [List.foldr_cons, h]
      funext y
      exact dirC_cls hs z p q R' y kl.1 kl.2
  rw [hR']
  exact ⟨_, fun y => cls_bound hs z p q R' y⟩
end PositivityTheory.Rg.Sw.WR.B
