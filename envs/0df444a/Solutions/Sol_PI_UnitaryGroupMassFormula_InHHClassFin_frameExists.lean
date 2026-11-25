-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.frameExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:04.517716+00:00
-- url     : https://prove2.me/submissions/4bd27680-ec99-4dba-a470-55e8ed745359

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_FrHformSumLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_disj
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_fr_sup
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix Formalism.UG PI.InHHClassFin Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {I : Formalism.MainNotions.S.AutInst} {S : Set (Fin I.n → I.E)}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution : FrameExists := by
  intro I S hS
  classical
  have hc : IsCompl (Submodule.span I.E S) (frW I S) :=
    ⟨fr_disj hS, codisjoint_iff.mpr (fr_sup hS)⟩
  let bS := Module.finBasis I.E (Submodule.span I.E S)
  let bW := Module.finBasis I.E (frW I S)
  let bb := (bS.prod bW).map (Submodule.prodEquivOfIsCompl _ _ hc)
  let e := Pi.basisFun I.E (Fin I.n)
  refine ⟨Frame.mk _ _ (e.toMatrix bb) (bb.toMatrix e) (e.toMatrix_mul_toMatrix_flip bb)
    (bb.toMatrix_mul_toMatrix_flip e) ?_ ?_ ?_⟩
  · intro j
    have hcol : (fun i => e.toMatrix bb i (Sum.inl j)) = (bS j : Fin I.n → I.E) := by
      funext i; simp [bb, e, Basis.toMatrix_apply]
    rw [hcol]; exact (bS j).2
  · intro s hs j
    have h1 : bb.toMatrix e *ᵥ s = bb.repr s := by
      have := e.toMatrix_mulVec_repr bb s
      have he : ⇑(e.repr s) = s := by funext i; simp [e]
      rw [he] at this
      exact this
    rw [h1]
    have hs' : s = Submodule.prodEquivOfIsCompl _ _ hc (⟨s, Submodule.subset_span hs⟩, 0) := by simp
    rw [hs', Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      Basis.prod_repr_inr]
    simp
  · intro s hs j
    have hcol : (fun i => e.toMatrix bb i (Sum.inr j)) = (bW j : Fin I.n → I.E) := by
      funext i; simp [bb, e, Basis.toMatrix_apply]
    rw [hcol]; exact (bW j).2 s hs
end PI.UnitaryGroupMassFormula.InHHClassFin
