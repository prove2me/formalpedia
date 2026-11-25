-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.locSplitChi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:23.015804+00:00
-- url     : https://prove2.me/submissions/7e229b5f-9236-4e32-8e37-0ed9795bea75

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sig_sig
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_sig_fix
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_herm_v
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_spl_det_v
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_proj_bijective
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitIso_exists_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (hG : GLChi) : LocSplitChi := by
  intro I v hnf χ hpos hcent _ g
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F _).injective
  obtain ⟨π, hπ⟩ := SplitIso.exists_split (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (spl_sig_sig I) (spl_sig_fix I) I.cm.deg2 two_ne_zero hnf
  have hπ' : ∀ r, π (sigV I v r) = (π r).swap := hπ
  let f : Uv I v →* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    SplitGL.proj (sigV I v) π (I.J.map (inclV I v))
  have hbij : Function.Bijective f :=
    SplitGL.proj_bijective (sigV I v) π hπ' (I.J.map (inclV I v)) (spl_herm_v I v) (spl_det_v I v)
  let e : Uv I v ≃* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) := MulEquiv.ofBijective f hbij
  have key := hG (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.n (χ.comp e.symm.toMonoidHom) (fun g => hpos _) ?_ (e g)
  · have h2 : e.symm (e g) = g := e.symm_apply_apply g
    rw [← h2]; exact key
  · intro d
    show χ (e.symm _) = 1
    apply hcent
    intro t
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact Algebra.commutes _ _
end PI.UnitaryGroupMassFormula.AdIndexEq
