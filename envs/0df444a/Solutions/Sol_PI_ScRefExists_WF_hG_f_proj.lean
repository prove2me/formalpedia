-- Prove2me | solution 1 for PI.ScRefExists.WF.hG_f_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:16.128498+00:00
-- url     : https://prove2.me/submissions/652f61b9-6564-47ad-b09a-47e7c6868d48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_StarMemAp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution {r : ℕ} {e f : Fin r → Fin I.n → I.E} (hf : ∀ a b, hG I (f a) (f b) = 0)
    (hef : ∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) (b : Fin r) (y : Fin I.n → I.E) :
    hG I (f b) (proj e f y) = hG I (f b) y := by
  have hr : ∀ (x : Fin I.n → I.E) (c : Fin r → I.E) (w : Fin r → Fin I.n → I.E),
      hG I x (∑ a, c a • w a) = ∑ a, c a * hG I x (w a) := by
    intro x c w
    unfold hG Formalism.UG.hform
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hadd2 : ∀ x u w : Fin I.n → I.E, hG I x (u + w) = hG I x u + hG I x w := by
    intro x u w
    unfold hG Formalism.UG.hform
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hJ : ∀ i j, starRingEnd I.E (I.J i j) = I.J j i := by
    intro i j
    have := congrFun (congrFun I.J_herm j) i
    simpa [Formalism.UG.cT] using this
  have hsym : ∀ x y, hG I y x = starRingEnd I.E (hG I x y) := by
    intro x y
    unfold hG Formalism.UG.hform
    simp only [map_sum, map_mul, starRingEnd_self_apply, hJ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have h1 : ∀ a, hG I (f b) (e a) = if a = b then 1 else 0 := by
    intro a
    rw [hsym (e a) (f b), hef]
    split_ifs <;> simp
  unfold proj
  rw [Finset.sum_add_distrib, hadd2, hr, hr]
  simp only [hf, h1]
  simp
end PI.ScRefExists.WF
