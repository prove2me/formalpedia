-- Prove2me | solution 1 for VapnikChervonenkis.GrowthFunction.phi_le_pow_add_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:33:56.356138+00:00
-- url     : https://prove2.me/submissions/18240ef0-3d50-4515-a162-9a73ca9c29ec

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi

namespace VapnikChervonenkis.GrowthFunction

theorem aux_vcphi_one (r : ℕ) : Shared.Phi 1 r = r + 1 := by
  induction r with
  | zero => simp [Shared.Phi]
  | succ r ih =>
    rw [Shared.Phi, ih]
    simp [Shared.Phi]

theorem aux_vcphi_pow_ge (r n : ℕ) (hn : 1 ≤ n) : r ^ n + 1 ≤ (r + 1) ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have h := ih hk
      have h' := Nat.mul_le_mul_right (r + 1) h
      have e : (r ^ k + 1) * (r + 1) = r ^ k * r + r ^ k + r + 1 := by ring
      rw [pow_succ, pow_succ]
      omega

theorem aux_vcphi_ineq (r n : ℕ) (hn : 1 ≤ n) :
    r ^ (n + 1) + r ^ n + 1 ≤ (r + 1) ^ (n + 1) := by
  have h := aux_vcphi_pow_ge r n hn
  rw [pow_succ, pow_succ]
  nlinarith

theorem aux_vcphi_main (r : ℕ) : ∀ n, 0 < n → Shared.Phi n r ≤ r ^ n + 1 := by
  induction r with
  | zero =>
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    simp [Shared.Phi]
  | succ r ih =>
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    rcases m with _ | k
    · rw [aux_vcphi_one]; simp
    · show Shared.Phi (k + 1 + 1) (r + 1) ≤ (r + 1) ^ (k + 1 + 1) + 1
      rw [Shared.Phi]
      have h1 : Shared.Phi (k + 1 + 1) r ≤ r ^ (k + 1 + 1) + 1 := ih (k + 1 + 1) (by omega)
      have h2 : Shared.Phi (k + 1) r ≤ r ^ (k + 1) + 1 := ih (k + 1) (by omega)
      have h3 := aux_vcphi_ineq r (k + 1) (by omega)
      omega

end VapnikChervonenkis.GrowthFunction

open VapnikChervonenkis.GrowthFunction
open VapnikChervonenkis

theorem solution (n r : ℕ) (hn : 0 < n) :
    Shared.Phi n r ≤ r ^ n + 1 :=
  aux_vcphi_main r n hn
