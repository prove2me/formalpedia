-- Prove2me | solution 1 for QmCapCommW.foldr_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:48.859662+00:00
-- url     : https://prove2.me/submissions/0820dd89-fbf2-408b-b2db-339bf5a67464

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
import Theorems.Thm_QmCapCommW_Tm_rep

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
theorem _root_.solution (hC : CapCongr) (hP : EabPres) (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    {F : Mx k r → E} {x : SS k r i D E} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons q l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    first
      | rw [Module.End.mul_apply]
      | rw [LinearMap.mul_apply]
    exact Tm_rep hC hP hD ih q.1 q.2.1 q.2.2
end QmCapCommW
