-- Prove2me | solution 1 for QmCapCommW.EE_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:06.891003+00:00
-- url     : https://prove2.me/submissions/be535d25-7045-45e1-9e04-f26e908867c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open QmCapCommW
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace QmCapCommW
theorem _root_.solution (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (EE hP hD a b x).1 := by
  unfold Rep at h ⊢
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext0 x.1) g
  exact hC E k r i D a b F (ext0 x.1) hD (fun g' hg' => by rw [extension_by_zero_apply hg']; exact h g' hg') g hg
end QmCapCommW
