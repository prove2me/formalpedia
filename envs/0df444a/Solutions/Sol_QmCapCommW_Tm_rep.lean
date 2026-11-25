-- Prove2me | solution 1 for QmCapCommW.Tm_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:29.24568+00:00
-- url     : https://prove2.me/submissions/22ebc1f9-4f51-4081-8d55-70298b0baf6d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
import Theorems.Thm_QmCapCommW_EE_rep
import Theorems.Thm_QmCapCommW_posL_inj

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
    (h : Rep F x.1) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (EE hP hD) u a b x).1 := by
  have h1 := EE_rep hC hP hD h a b
  unfold Rep at h h1 ⊢
  intro g hg
  by_cases hab : a = b
  · subst hab
    first
      | simp [Formalism.QuantumDeterminants.Top, Formalism.REAL.Tm, Module.algebraMap_end_apply, h g hg, h1 g hg]
      | simp [Formalism.QuantumDeterminants.Top, Tm, Module.algebraMap_end_apply, h g hg, h1 g hg]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    first
      | simp [Formalism.QuantumDeterminants.Top, Formalism.REAL.Tm, hab, hne, h1 g hg]
      | simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h1 g hg]
end QmCapCommW
