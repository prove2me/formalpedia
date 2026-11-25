-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TensorGLSums.omComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:21.881731+00:00
-- url     : https://prove2.me/submissions/6f6a30ee-5392-46f1-98f9-8df2bd7188fb

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
theorem _root_.solution {R : Type*} [Ring R] {n : ℕ} (L e : Fin n → Fin n → R) (hL : GlRel L)
    (hLe : ∀ a b c d, Commute (L a b) (e c d)) (he : ∀ a b c d, e a b * e c d = if b = c then e a d else 0)
    (c d : Fin n) : Commute (∑ a, ∑ b, L a b * e b a) (L c d + e c d) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have hterm : ∀ a b, L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a) =
      ((if b = c then L a d * e b a else 0) - (if d = a then L c b * e b a else 0)) +
      ((if a = c then L a b * e b d else 0) - (if d = b then L a b * e c a else 0)) := by
    intro a b
    have h1 : e b a * L c d = L c d * e b a := ((hLe c d b a).eq).symm
    have h2 : e c d * L a b = L a b * e c d := ((hLe a b c d).eq).symm
    have h3 := hL a b c d
    have e1 := he b a c d
    have e2 := he c d b a
    calc L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)
        = (L a b * L c d - L c d * L a b) * e b a + L a b * (e b a * e c d - e c d * e b a) := by
          have k1 : L a b * e b a * L c d = L a b * L c d * e b a := by rw [mul_assoc, h1, ← mul_assoc]
          have k2 : e c d * (L a b * e b a) = L a b * e c d * e b a := by rw [← mul_assoc, h2]
          rw [mul_add, add_mul, k1, k2]
          noncomm_ring
      _ = _ := by
          rw [h3, e1, e2]
          split_ifs <;> simp [sub_mul, mul_sub]
  have hx : (∑ a, ∑ b, L a b * e b a) * (L c d + e c d) - (L c d + e c d) * (∑ a, ∑ b, L a b * e b a) =
      ∑ a, ∑ b, (L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hx]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if d = a then L c b * e b a else 0)]
  rw [Finset.sum_comm (f := fun a b => if a = c then L a b * e b d else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel
end PositivityTheory.Rg.Cz.TensorGLSums
