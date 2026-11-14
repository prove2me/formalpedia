-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.finite_observation_change_measure
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:16:49.047501+00:00
-- url     : https://prove2.me/submissions/0727276f-772e-46b7-a1c3-792ef509a62b

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem solution {X Y : Type} [Fintype X] [Fintype Y]
    (obs : X → Y) (p : X → ℝ) (q : Y → ℝ) (H Good : Y → Y → Prop) (L : ℝ)
    (hL : 0 ≤ L) (hq : ∀ y, 0 ≤ q y)
    (hdensity : ∀ y y', H y y' → Good y y' →
      (∑ x ∈ Finset.univ.filter (fun x => obs x = y), p x) *
      (∑ x ∈ Finset.univ.filter (fun x => obs x = y'), p x) ≤ L * (q y * q y')) :
    (∑ x, ∑ x', if H (obs x) (obs x') ∧ Good (obs x) (obs x') then p x*p x' else 0) ≤
      L * ∑ y, ∑ y', if H y y' then q y*q y' else 0 := by
  classical
  let P : Y → ℝ := fun y => ∑ x ∈ Finset.univ.filter (fun x => obs x = y), p x
  have hone (r : Y → ℝ) : (∑ x, p x * r (obs x)) = ∑ y, P y * r y := by
    rw [← Finset.sum_fiberwise Finset.univ obs (fun x => p x * r (obs x))]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [P]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  let F : Y → Y → ℝ := fun y y' => if H y y' ∧ Good y y' then 1 else 0
  have hrepr : (∑ x, ∑ x', if H (obs x) (obs x') ∧ Good (obs x) (obs x') then p x*p x' else 0) =
      ∑ y, ∑ y', P y * P y' * F y y' := by
    calc
      _ = ∑ x, p x * (∑ x', p x' * F (obs x) (obs x')) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x' hx'
        dsimp [F]
        split_ifs <;> ring
      _ = ∑ x, p x * (∑ y', P y' * F (obs x) y') := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hone]
      _ = ∑ y, P y * (∑ y', P y' * F y y') := hone (fun y => ∑ y', P y' * F y y')
      _ = _ := by simp_rw [Finset.mul_sum,mul_assoc]
  rw [hrepr, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y' hy'
  dsimp [F]
  by_cases h : H y y'
  · by_cases hg : Good y y'
    · simpa [h,hg,P] using hdensity y y' h hg
    · have hh : 0 ≤ L * (q y*q y') := mul_nonneg hL (mul_nonneg (hq y) (hq y'))
      simpa [h,hg] using hh
  · simp [h]
