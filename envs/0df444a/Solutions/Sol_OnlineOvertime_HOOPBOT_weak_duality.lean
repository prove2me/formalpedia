-- Prove2me | solution 1 for OnlineOvertime.HOOPBOT.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:13.699521+00:00
-- url     : https://prove2.me/submissions/1cd683ae-5bf9-4a02-9f16-0bbe6ca43a47

import Definitions.Def_OnlineOvertime_HOOPBOT_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
open OnlineOvertime.HOOPBOT
open scoped BigOperators

theorem solution {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (y : Fin m → Fin n → Fin T → ℝ) (v : Fin n → Fin T → ℝ)
    (x u : Fin n → Fin T → ℝ) (z : Fin m → ℝ)
    (hP : Feasible I y v) (hD : DualFeasible I x u z) :
    obj I y v ≤ dualObj I x u z := by
  have hy : ∀ j i t, 0 ≤ y j i t := by
    intro j i t
    rcases hP.1 j i t with h|h <;> simp [h]
  have hlocal : ∀ i t, (∑ j, I.c j i * y j i t) - I.d i * v i t ≤
      I.B i t * x i t + I.U i t * u i t + ∑ j, z j * y j i t := by
    intro i t
    have hc : (∑ j, I.c j i * y j i t) ≤
        x i t * (∑ j, I.b j i * y j i t) + ∑ j, z j * y j i t := by
      calc
        _ ≤ ∑ j, (I.b j i * x i t + z j) * y j i t :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hD.1 i t j) (hy j i t))
        _ = _ := by simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]; apply congrArg₂ (·+·) ?_ rfl; apply Finset.sum_congr rfl; intro j _; ring
    have hcap := mul_le_mul_of_nonneg_left (hP.2.2.1 i t) (hD.2.2.1 i t)
    have hd := mul_le_mul_of_nonneg_right (hD.2.1 i t) (hP.2.2.2.2 i t)
    have hu := mul_le_mul_of_nonneg_left (hP.2.2.2.1 i t) (hD.2.2.2.1 i t)
    nlinarith only [hc,hcap,hd,hu]
  have hzsum : (∑ t, ∑ i, ∑ j, z j * y j i t) ≤ ∑ j, z j := by
    calc
      _ = ∑ t, ∑ j, ∑ i, z j * y j i t := by
        apply Finset.sum_congr rfl; intro t _; exact Finset.sum_comm
      _ = ∑ j, ∑ t, ∑ i, z j * y j i t := Finset.sum_comm
      _ = ∑ j, z j * (∑ t, ∑ i, y j i t) := by simp only [Finset.mul_sum]
      _ ≤ ∑ j, z j * 1 := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hP.2.1 j) (hD.2.2.2.2 j))
      _ = _ := by simp
  unfold obj dualObj
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun t _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hlocal i t))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hs ⊢
  linarith only [hs,hzsum]

#print axioms solution

