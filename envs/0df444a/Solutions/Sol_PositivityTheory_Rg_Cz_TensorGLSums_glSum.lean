-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TensorGLSums.glSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:25.495105+00:00
-- url     : https://prove2.me/submissions/af7cf56b-c261-41df-8580-735fbd3d2c9f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TensorGLSums
namespace PositivityTheory.Rg.Cz.TensorGLSums
theorem _root_.solution {R : Type*} [Ring R] {n : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι) (L : Fin n → Fin n → R)
    (e : ι → Fin n → Fin n → R) (hL : GlRel L) (hLe : ∀ p a b c d, Commute (L a b) (e p c d))
    (he : ∀ p q a b c d, e p a b * e q c d - e q c d * e p a b =
      if p = q then (if b = c then e p a d else 0) - (if d = a then e p c b else 0) else 0) :
    GlRel (fun a b => L a b + ∑ p ∈ S, e p a b) := by
  intro a b c d
  have key : ∀ x y u v : R, (x + u) * (y + v) - (y + v) * (x + u) =
      (x * y - y * x) + (x * v - v * x) + (u * y - y * u) + (u * v - v * u) := by
    intros; noncomm_ring
  simp only
  rw [key, hL]
  have h1 : L a b * ∑ p ∈ S, e p c d - (∑ p ∈ S, e p c d) * L a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_right _ _ _ fun p _ => hLe p a b c d).eq
  have h2 : (∑ p ∈ S, e p a b) * L c d - L c d * ∑ p ∈ S, e p a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_left _ _ _ fun p _ => (hLe p c d a b).symm).eq
  have h3 : (∑ p ∈ S, e p a b) * (∑ q ∈ S, e q c d) - (∑ q ∈ S, e q c d) * (∑ p ∈ S, e p a b) =
      ∑ p ∈ S, ((if b = c then e p a d else 0) - (if d = a then e p c b else 0)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := S) (t := S)
      (f := fun q p => e q c d * e p a b), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [he p]
    rw [Finset.sum_ite_eq]
    simp [hp]
  rw [h1, h2, h3]
  split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel
end PositivityTheory.Rg.Cz.TensorGLSums
