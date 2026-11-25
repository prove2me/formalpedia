-- Prove2me | solution 1 for QmCapCommW.qminor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:13.229107+00:00
-- url     : https://prove2.me/submissions/f686ac89-5504-4611-8cc4-a7e202fc4093

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
theorem _root_.solution (hP : EabPres) (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ)
    (x : SS k r i D E) :
    qminor (EE hP hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (EE hP hD) p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Module.End.mul_apply, List.map_ofFn]
  simp [Function.comp_def, Int.cast_smul_eq_zsmul]
end QmCapCommW
