-- Prove2me | solution 1 for PI.ScPiBuildW.Asm.build
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:06.052498+00:00
-- url     : https://prove2.me/submissions/3dd68f16-f658-427c-8c52-1c490720e25c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_InnerOfNorm
import Theorems.Thm_PI_ScPiBuildW_Asm_inner_of_norm
import Theorems.Thm_PI_ScPiBuildW_Asm_uMat_one
import Theorems.Thm_PI_ScPiBuildW_Asm_uMat_mul
import Theorems.Thm_PI_ScPiBuildW_Asm_inUJ_uMat
import Theorems.Thm_PI_ScPiBuildW_Asm_cont_uMat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_N
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_inUJ
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_mul
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_M_one
import Theorems.Thm_PI_ScPiBuildW_Rv_locFrame_e
import Theorems.Thm_PI_ScPiBuildW_Rv_locFrame_f
import Theorems.Thm_PI_ScPiBuildW_Rv_locFrame_w
import Theorems.Thm_PI_ScPiBuildW_Rv_locFrame_z
import Theorems.Thm_PI_ScPiBuildW_Tens_continuousOn_tensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_inner_tensOp
import Theorems.Thm_PI_ScPiBuildW_Tens_inner_tensU
import Theorems.Thm_PI_ScPiBuildW_Tens_span_tensU
import Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_mul
import Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_one
import Theorems.Thm_PI_ScPiBuildW_Tens_tensOp_tensU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] PI.ScPiBuildW.Rv.locFrame_e
attribute [local simp] PI.ScPiBuildW.Rv.locFrame_f
attribute [local simp] PI.ScPiBuildW.Rv.locFrame_w
attribute [local simp] PI.ScPiBuildW.Rv.locFrame_z



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped InnerProductSpace
open PI PI.ScPiBuildW PI.ScPiBuildW.Asm
open PI.ScPiExists Formalism.MainNotions.S
namespace PI.ScPiBuildW.Asm
theorem _root_.solution : Build := by
  intro hW I r k e f z lam hn hF hz hlam hw
  classical
  choose w hw using hw
  choose H hHN hHI pl hπ using fun v => hW k (lam v) (hlam v)
  let _ := hHN
  let _ := hHI
  have hHF : ∀ v, FiniteDimensional ℂ (H v) := fun v => (hπ v).2.1
  let L : ∀ v, Loc.LocFrame I.n r k (I.ε v) := fun v => Rv.locFrame I e f z hn hF hz v (w v) (hw v)
  let A : I.Ginf → ∀ v, H v →L[ℂ] H v := fun s v => pl v ((L v).M (uMat (s v)))
  have hA1 : A 1 = fun _ => 1 := by
    funext v
    simp only [A]
    rw [uMat_one, Loc.LocFrame.M_one]
    exact (hπ v).2.2.1.1.1
  refine ⟨{
      Vpi := Tens.TV H
      piU := fun s => Tens.tensOp (A s)
      piU_rep := ?_
      Vloc := H
      piLoc := pl
      piLoc_type := hπ
      wfr := w
      wfr_on := fun v => (hw v).1
      wfr_perp := fun v => (hw v).2
      tensU := Tens.tensU
      tensU_inner := Tens.inner_tensU
      tensU_span := Tens.span_tensU
      tensU_equiv := fun s _ x => Tens.tensOp_tensU (A s) x }⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Tens.tensOp (A 1) = 1
    rw [hA1]
    exact Tens.tensOp_one
  · intro s hs t ht
    show Tens.tensOp (A (s * t)) = Tens.tensOp (A s) * Tens.tensOp (A t)
    rw [← Tens.tensOp_mul]
    congr 1
    funext v
    simp only [A]
    rw [uMat_mul, (L v).M_mul (inUJ_uMat I s v) (hs v) (inUJ_uMat I t v) (ht v)]
    exact (hπ v).2.2.1.1.2 _ ((L v).M_inUJ (inUJ_uMat I s v) (hs v)) _
      ((L v).M_inUJ (inUJ_uMat I t v) (ht v))
  · intro s hs x y
    exact Tens.inner_tensOp (A s) (fun v u u' => inner_of_norm _
      (fun y => (hπ v).2.2.1.2.1 _ ((L v).M_inUJ (inUJ_uMat I s v) (hs v)) y) u u') x y
  · intro s hs
    show Tens.tensOp (A s) = 1
    have : A s = fun _ => 1 := by
      funext v
      simp only [A]
      rw [(L v).M_N (hs v)]
      exact (hπ v).2.2.1.1.1
    rw [this]
    exact Tens.tensOp_one
  · intro x
    refine Tens.continuousOn_tensOp A (Sinf I e z) (fun v y => ?_) x
    have hc : Continuous fun s : I.Ginf => (L v).M (uMat (s v)) := by
      apply continuous_pi
      intro a
      apply continuous_pi
      intro b
      simp only [Loc.LocFrame.M, hJ]
      exact continuous_const.dotProduct
        (continuous_const.matrix_mulVec ((cont_uMat I v).matrix_mulVec continuous_const))
    exact ((hπ v).2.2.1.2.2 y).comp hc.continuousOn
      (fun s hs => (L v).M_inUJ (inUJ_uMat I s v) (hs v))
end PI.ScPiBuildW.Asm
