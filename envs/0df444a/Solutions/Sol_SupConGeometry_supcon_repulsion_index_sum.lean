-- Prove2me | solution 1 for SupConGeometry.supcon_repulsion_index_sum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:45:59.013297+00:00
-- url     : https://prove2.me/submissions/60a8a757-4954-48f9-974a-71e27e62d64e

import Mathlib
import Definitions.Def_SupConGeometry_Basic

open Finset

namespace SupConGeometry

theorem supcon_repulsion_index_sum {N K h : ℕ} (hKh : K ≤ h + 1)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ) (Y : Fin N → Fin K) :
    -(ρ ^ 2) * ∑ y, (labelCount Y y : ℝ) ^ 2 ≤
      ∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
        inner ℝ (Z n) (Z m) ∧
    (∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
        inner ℝ (Z n) (Z m) = -(ρ ^ 2) * ∑ y, (labelCount Y y : ℝ) ^ 2 ↔
      (∑ n, Z n = 0) ∧ ∀ n m : Fin N, Y n = Y m → Z n = Z m) := by
  set S := ∑ n, Z n with hS
  let D : Fin K → ℝ := fun y => ∑ n ∈ univ.filter (fun n => Y n = y),
    ∑ m ∈ univ.filter (fun m => Y m = y), (ρ ^ 2 - inner ℝ (Z n) (Z m))
  have hin : ∀ n m, inner ℝ (Z n) (Z m) ≤ ρ ^ 2 := fun n m => by
    have := real_inner_le_norm (Z n) (Z m)
    rw [hZ, hZ] at this; nlinarith
  have hD0 : ∀ y, 0 ≤ D y := fun y =>
    sum_nonneg fun n _ => sum_nonneg fun m _ => sub_nonneg.2 (hin n m)
  have h1 : ∀ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
      inner ℝ (Z n) (Z m) = ∑ n ∈ univ.filter (fun n => Y n = y), inner ℝ (Z n) S
        - ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m = y),
          inner ℝ (Z n) (Z m) := by
    intro y; rw [← sum_sub_distrib]; refine sum_congr rfl fun n _ => ?_
    rw [hS, inner_sum]
    have := sum_filter_add_sum_filter_not univ (fun m => Y m = y) (fun m => inner ℝ (Z n) (Z m))
    simp only [ne_eq]; linarith
  have h2 : ∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), inner ℝ (Z n) S = ‖S‖ ^ 2 := by
    rw [sum_fiberwise univ Y (fun n => inner ℝ (Z n) S), ← sum_inner, ← hS,
      real_inner_self_eq_norm_sq]
  have h3 : ∀ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m = y),
      inner ℝ (Z n) (Z m) = (labelCount Y y : ℝ) ^ 2 * ρ ^ 2 - D y := by
    intro y
    simp only [D, sum_sub_distrib, sum_const, labelCount, nsmul_eq_mul]
    ring
  have hT : ∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
      inner ℝ (Z n) (Z m) = ‖S‖ ^ 2 - ρ ^ 2 * ∑ y, (labelCount Y y : ℝ) ^ 2 + ∑ y, D y := by
    simp only [h1, h3, sum_sub_distrib, h2, mul_sum]
    rw [show ∑ x, (labelCount Y x : ℝ) ^ 2 * ρ ^ 2 = ∑ x, ρ ^ 2 * (labelCount Y x : ℝ) ^ 2 from
      sum_congr rfl fun _ _ => mul_comm _ _]
    ring
  rw [hT]
  have hDs := sum_nonneg fun y (_ : y ∈ univ) => hD0 y
  refine ⟨by nlinarith [sq_nonneg ‖S‖], ⟨fun heq => ?_, fun ⟨hS0, hc⟩ => ?_⟩⟩
  · have hsum : ‖S‖ ^ 2 + ∑ y, D y = 0 := by linarith
    have hS2 : ‖S‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖S‖]
    have hDz : ∑ y, D y = 0 := by linarith
    refine ⟨by simpa using hS2, fun n m hnm => ?_⟩
    have hy := (sum_eq_zero_iff_of_nonneg fun y _ => hD0 y).1 hDz (Y n) (mem_univ _)
    have hn : n ∈ univ.filter (fun k => Y k = Y n) := by simp
    have hm : m ∈ univ.filter (fun k => Y k = Y n) := by simp [hnm]
    have hy2 := (sum_eq_zero_iff_of_nonneg fun k _ => sum_nonneg fun j _ =>
      sub_nonneg.2 (hin k j)).1 hy n hn
    have hy3 := (sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hin n j)).1 hy2 m hm
    have hsq : ‖Z n - Z m‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hZ, hZ]; linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · have hDz : ∀ y, D y = 0 := fun y => by
      refine sum_eq_zero fun n hn => sum_eq_zero fun m hm => ?_
      simp only [mem_filter, mem_univ, true_and] at hn hm
      rw [← hc n m (hn.trans hm.symm), real_inner_self_eq_norm_sq, hZ]; ring
    simp only [hDz, sum_const_zero, hS0, norm_zero]
    ring

end SupConGeometry
open SupConGeometry Finset in
theorem solution {N K h : ℕ} (hKh : K ≤ h + 1)
    (ρ : ℝ) (hρ : 0 < ρ) (Z : Fin N → Rep h) (hZ : ∀ n, ‖Z n‖ = ρ) (Y : Fin N → Fin K) :
    -(ρ ^ 2) * ∑ y, (labelCount Y y : ℝ) ^ 2 ≤
      ∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
        inner ℝ (Z n) (Z m) ∧
    (∑ y, ∑ n ∈ univ.filter (fun n => Y n = y), ∑ m ∈ univ.filter (fun m => Y m ≠ y),
        inner ℝ (Z n) (Z m) = -(ρ ^ 2) * ∑ y, (labelCount Y y : ℝ) ^ 2 ↔
      (∑ n, Z n = 0) ∧ ∀ n m : Fin N, Y n = Y m → Z n = Z m) :=
  supcon_repulsion_index_sum hKh ρ hρ Z hZ Y
