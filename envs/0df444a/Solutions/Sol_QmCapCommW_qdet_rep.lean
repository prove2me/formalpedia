-- Prove2me | solution 1 for QmCapCommW.qdet_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:18.283882+00:00
-- url     : https://prove2.me/submissions/719c26c7-8459-40a0-a1b6-bc2ef482f658

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
import Theorems.Thm_QmCapCommW_rep_sum
import Theorems.Thm_QmCapCommW_foldr_rep
import Theorems.Thm_QmCapCommW_qminor_apply

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
theorem _root_.solution (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (u : ℂ) {F : Mx k r → E} {x : SS k r i D E}
    (h : Rep F x.1) : Rep (capL k r i u F) (qdet (EE hP hD) u x).1 := by
  unfold qdet capL
  rw [qminor_apply]
  unfold qminorOp
  have H := rep_sum (fun σ : Equiv.Perm (Fin (mdim k r i)) => (((Equiv.Perm.sign σ : ℤ) : ℂ)))
    (fun σ => foldr_rep hC hP hD (List.ofFn fun q : Fin (mdim k r i) => (u - ((q : ℕ) : ℂ), σ q, q)) h)
  simp only [List.map_ofFn, Function.comp_def, id] at H ⊢
  intro g hg
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  exact H g hg
end QmCapCommW
