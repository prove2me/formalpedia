-- Prove2me | solution 1 for OddPerfectNumber.vieta_phi5_C_nine_ray_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T13:49:43.062129+00:00
-- url     : https://prove2.me/submissions/cb6d528b-85a7-4d91-b506-56db759425d7

import Mathlib
import Definitions.Def_opnRightRay
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_vieta_phi5_other_root
import Theorems.Thm_OddPerfectNumber_opnRightRay_recurrence
import Theorems.Thm_OddPerfectNumber_opnLeftRay_recurrence

open OddPerfectNumber

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000

theorem solution (x y : Nat)
    (hx : 0 < x)
    (hy : 0 < y)
    (heq : x ^ 2 + x + y ^ 2 + y + 1 = 9 * (x * y - 1)) :
    (∃ n : Nat, x = opnRightRay n ∧ y = opnRightRay (n + 1)) ∨
      (∃ n : Nat, y = opnRightRay n ∧ x = opnRightRay (n + 1)) ∨
      (∃ n : Nat, x = opnLeftRay n ∧ y = opnLeftRay (n + 1)) ∨
      (∃ n : Nat, y = opnLeftRay n ∧ x = opnLeftRay (n + 1)) := by
  let Cov : Nat → Nat → Prop := fun a b =>
    (∃ n : Nat, a = opnRightRay n ∧ b = opnRightRay (n + 1)) ∨
      (∃ n : Nat, b = opnRightRay n ∧ a = opnRightRay (n + 1)) ∨
      (∃ n : Nat, a = opnLeftRay n ∧ b = opnLeftRay (n + 1)) ∨
      (∃ n : Nat, b = opnLeftRay n ∧ a = opnLeftRay (n + 1))
  have Cov_symm : ∀ a b : Nat, Cov a b → Cov b a := by
    intro a b h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  -- Recurrence in the index shape used by `Cov`, forward step.
  have R_fwd : ∀ n : Nat,
      9 * opnRightRay (n + 1) - opnRightRay n - 1 = opnRightRay (n + 1 + 1) := by
    intro n
    have h := opnRightRay_recurrence n
    have h2 : n + 2 = n + 1 + 1 := by omega
    rw [h2] at h
    omega
  have L_fwd : ∀ n : Nat,
      9 * opnLeftRay (n + 1) - opnLeftRay n - 1 = opnLeftRay (n + 1 + 1) := by
    intro n
    have h := opnLeftRay_recurrence n
    have h2 : n + 2 = n + 1 + 1 := by omega
    rw [h2] at h
    omega
  -- Recurrence in the index shape used by `Cov`, backward step away from index 0.
  have R_back : ∀ n : Nat, 1 ≤ n →
      9 * opnRightRay n - opnRightRay (n + 1) - 1 = opnRightRay (n - 1) := by
    intro n hn
    have h := opnRightRay_recurrence (n - 1)
    have h1 : n - 1 + 2 = n + 1 := by omega
    have h2 : n - 1 + 1 = n := by omega
    rw [h1, h2] at h
    omega
  have L_back : ∀ n : Nat, 1 ≤ n →
      9 * opnLeftRay n - opnLeftRay (n + 1) - 1 = opnLeftRay (n - 1) := by
    intro n hn
    have h := opnLeftRay_recurrence (n - 1)
    have h1 : n - 1 + 2 = n + 1 := by omega
    have h2 : n - 1 + 1 = n := by omega
    rw [h1, h2] at h
    omega
  -- `v = 9u - z - 1` is the neighbour of `u` opposite to `z` on the orbit.
  have extend : ∀ u z v : Nat, Cov u z → v + z + 1 = 9 * u → Cov u v := by
    intro u z v hcov hvz
    have hv : v = 9 * u - z - 1 := by omega
    rcases hcov with h | h | h | h
    · obtain ⟨n, hun, hzn⟩ := h
      by_cases hn : n = 0
      · subst n
        right
        right
        left
        refine ⟨0, ?_, ?_⟩
        · rw [hun]
          norm_num [opnRightRay, opnLeftRay]
        · rw [hv, hun, hzn]
          norm_num [opnRightRay, opnLeftRay]
      · have hn1 : 1 ≤ n := by omega
        right
        left
        refine ⟨n - 1, ?_, ?_⟩
        · rw [hv, hun, hzn]
          exact R_back n hn1
        · rw [hun]
          congr 1
          omega
    · obtain ⟨n, hzn, hun⟩ := h
      left
      refine ⟨n + 1, ?_, ?_⟩
      · rw [hun]
      · rw [hv, hun, hzn]
        exact R_fwd n
    · obtain ⟨n, hun, hzn⟩ := h
      by_cases hn : n = 0
      · subst n
        left
        refine ⟨0, ?_, ?_⟩
        · rw [hun]
          norm_num [opnRightRay, opnLeftRay]
        · rw [hv, hun, hzn]
          norm_num [opnRightRay, opnLeftRay]
      · have hn1 : 1 ≤ n := by omega
        right
        right
        right
        refine ⟨n - 1, ?_, ?_⟩
        · rw [hv, hun, hzn]
          exact L_back n hn1
        · rw [hun]
          congr 1
          omega
    · obtain ⟨n, hzn, hun⟩ := h
      right
      right
      left
      refine ⟨n + 1, ?_, ?_⟩
      · rw [hun]
      · rw [hv, hun, hzn]
        exact L_fwd n
  -- Finite-regime bounds, reused verbatim from the accepted C in {3,9} classification.
  have base_u_le3 : ∀ u h : Nat,
      0 < u →
      1 ≤ h →
      h ^ 2 * u + 2 * h * u ^ 2 ≤ 2 * h + u ^ 2 + 3 * u + 1 →
      u ≤ 3 := by
    intro u h hu hh hbase
    have hbaseZ :
        (h : Int) ^ 2 * (u : Int) +
            2 * (h : Int) * (u : Int) ^ 2 ≤
          2 * (h : Int) + (u : Int) ^ 2 + 3 * (u : Int) + 1 := by
      exact_mod_cast hbase
    have hhZ : (1 : Int) ≤ h := by exact_mod_cast hh
    have huZ : (0 : Int) < u := by exact_mod_cast hu
    have hdiff :
        0 ≤ ((h : Int) - 1) *
          ((h : Int) * (u : Int) + 2 * (u : Int) ^ 2 + (u : Int) - 2) := by
      have h1 : 0 ≤ (h : Int) - 1 := by omega
      have h2 : 0 ≤
          (h : Int) * (u : Int) + 2 * (u : Int) ^ 2 + (u : Int) - 2 := by
        nlinarith
      exact mul_nonneg h1 h2
    have hid :
        ((h : Int) - 1) *
            ((h : Int) * (u : Int) + 2 * (u : Int) ^ 2 + (u : Int) - 2) =
          (-(u : Int) ^ 2 + 2 * (u : Int) + 3) -
            (-(h : Int) ^ 2 * (u : Int) -
              2 * (h : Int) * (u : Int) ^ 2 +
              2 * (h : Int) + (u : Int) ^ 2 + 3 * (u : Int) + 1) := by
      ring
    have hF : 0 ≤ -(u : Int) ^ 2 + 2 * (u : Int) + 3 := by
      nlinarith [hbaseZ, hdiff, hid]
    by_contra hu4
    have hu4' : 4 ≤ u := by omega
    have hu4Z : (4 : Int) ≤ u := by exact_mod_cast hu4'
    nlinarith [sq_nonneg ((u : Int) - 3)]
  have base_h_le4 : ∀ u h : Nat,
      1 ≤ u →
      u ≤ 3 →
      1 ≤ h →
      h ^ 2 * u + 2 * h * u ^ 2 ≤ 2 * h + u ^ 2 + 3 * u + 1 →
      h ≤ 4 := by
    intro u h hu hu3 hh hbase
    have hu_sq : 1 ≤ u ^ 2 := by nlinarith
    have hmul1 : h ^ 2 ≤ h ^ 2 * u := by
      simpa [Nat.mul_one] using Nat.mul_le_mul_left (h ^ 2) hu
    have hmul2 : 2 * h ≤ 2 * h * u ^ 2 := by
      have htmp := Nat.mul_le_mul_left (2 * h) hu_sq
      simpa [Nat.mul_one, mul_assoc] using htmp
    have hu_sq_le : u ^ 2 ≤ 9 := by nlinarith
    have hu3 : 3 * u ≤ 9 := by nlinarith
    have hh_sq : h ^ 2 ≤ 19 := by nlinarith
    by_contra hh5
    have hh5' : 5 ≤ h := by omega
    have hh_sq25 : 25 ≤ h ^ 2 := by nlinarith
    nlinarith
  let P : Nat → Prop := fun n =>
    ∀ u v : Nat,
      u + v = n →
      0 < u →
      0 < v →
      u ≤ v →
      u ^ 2 + u + v ^ 2 + v + 1 = 9 * (u * v - 1) →
      Cov u v
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro u v huv hu hv huvle huv_eq
        obtain ⟨z, hz, hvz, hzprod, hzeq⟩ :=
          vieta_phi5_other_root u v 9 hu hv huv_eq
        by_cases hzy : z < v
        · have hlt : u + z < n := by omega
          have hsmall : Cov u z := by
            by_cases huz : u ≤ z
            · exact ih (u + z) hlt u z rfl hu hz huz hzeq
            · have hzu : z ≤ u := by omega
              have hsw : z ^ 2 + z + u ^ 2 + u + 1 = 9 * (z * u - 1) := by
                calc
                  z ^ 2 + z + u ^ 2 + u + 1 = u ^ 2 + u + z ^ 2 + z + 1 := by ring
                  _ = 9 * (u * z - 1) := hzeq
                  _ = 9 * (z * u - 1) := by rw [mul_comm u z]
              exact Cov_symm z u (ih (z + u) (by omega) z u rfl hz hu hzu hsw)
          exact extend u z v hsmall hvz
        · have hvz' : v ≤ z := by omega
          by_cases huv0 : u = v
          · subst v
            have hu1 : u ≠ 1 := by
              intro h1
              subst u
              norm_num at huv_eq
            have hu2 : 2 ≤ u := by omega
            have hDdiag : 2 * u ^ 2 + 2 * u + 1 = 9 * (u ^ 2 - 1) := by
              calc
                2 * u ^ 2 + 2 * u + 1 = u ^ 2 + u + u ^ 2 + u + 1 := by ring
                _ = 9 * (u * u - 1) := huv_eq
                _ = 9 * (u ^ 2 - 1) := by rw [pow_two]
            have hu_le3 : u ≤ 3 := by
              have hmul : 3 * (u ^ 2 - 1) ≤ 9 * (u ^ 2 - 1) := by omega
              have hineq : 3 * (u ^ 2 - 1) ≤ 2 * u ^ 2 + 2 * u + 1 := by
                calc
                  3 * (u ^ 2 - 1) ≤ 9 * (u ^ 2 - 1) := hmul
                  _ = 2 * u ^ 2 + 2 * u + 1 := hDdiag.symm
              by_contra hu4
              have hu4' : 4 ≤ u := by omega
              have hu_sq : 4 * u ≤ u ^ 2 := by nlinarith
              have hsub2 : u ^ 2 - 1 + 1 = u ^ 2 := by omega
              nlinarith
            interval_cases u <;> omega
          · have huv_lt : u < v := by omega
            let h : Nat := v - u
            have hh : 1 ≤ h := by
              dsimp [h]
              omega
            have hv_eq : v = u + h := by
              dsimp [h]
              omega
            have hlin : 2 * v + 1 ≤ 9 * u := by omega
            have hmul : (2 * v + 1) * (u * v - 1) ≤ (9 * u) * (u * v - 1) :=
              Nat.mul_le_mul_right (u * v - 1) hlin
            have hDmul : (9 * u) * (u * v - 1) = u * (u ^ 2 + u + v ^ 2 + v + 1) := by
              calc
                (9 * u) * (u * v - 1) = u * (9 * (u * v - 1)) := by ring
                _ = u * (u ^ 2 + u + v ^ 2 + v + 1) := by rw [← huv_eq]
            have hineq : (2 * v + 1) * (u * v - 1) ≤ u * (u ^ 2 + u + v ^ 2 + v + 1) :=
              le_trans hmul (le_of_eq hDmul)
            have hbase : h ^ 2 * u + 2 * h * u ^ 2 ≤ 2 * h + u ^ 2 + 3 * u + 1 := by
              have hsub : u * v - 1 + 1 = u * v := by omega
              have hleft :
                  (2 * v + 1) * (u * v - 1) + (2 * v + 1) =
                    (2 * v + 1) * (u * v) := by
                calc
                  (2 * v + 1) * (u * v - 1) + (2 * v + 1) =
                      (2 * v + 1) * ((u * v - 1) + 1) := by ring
                  _ = (2 * v + 1) * (u * v) := by rw [hsub]
              have hadd :
                  (2 * v + 1) * (u * v) ≤
                    u * (u ^ 2 + u + v ^ 2 + v + 1) + (2 * v + 1) := by
                calc
                  (2 * v + 1) * (u * v) =
                      (2 * v + 1) * (u * v - 1) + (2 * v + 1) := hleft.symm
                  _ ≤ u * (u ^ 2 + u + v ^ 2 + v + 1) + (2 * v + 1) :=
                    Nat.add_le_add_right hineq (2 * v + 1)
              have hpoly :
                  (2 * v + 1) * (u * v) + (2 * h + u ^ 2 + 3 * u + 1) =
                    (u * (u ^ 2 + u + v ^ 2 + v + 1) + (2 * v + 1)) +
                      (h ^ 2 * u + 2 * h * u ^ 2) := by
                rw [hv_eq]
                ring
              have hadd' := Nat.add_le_add_right hadd (h ^ 2 * u + 2 * h * u ^ 2)
              rw [← hpoly] at hadd'
              exact Nat.le_of_add_le_add_left hadd'
            have hu1 : 1 ≤ u := by omega
            have hu_le3 := base_u_le3 u h hu hh hbase
            have hh_le4 := base_h_le4 u h hu1 hu_le3 hh hbase
            have hEq :
                u ^ 2 + u + (u + h) ^ 2 + (u + h) + 1 =
                  9 * (u * (u + h) - 1) := by
              rw [← hv_eq]
              exact huv_eq
            have hu_cases : u = 1 ∨ u = 2 ∨ u = 3 := by omega
            rcases hu_cases with rfl | rfl | rfl
            · interval_cases h
              · left
                refine ⟨0, ?_, ?_⟩
                · norm_num [opnRightRay]
                · rw [hv_eq]
                  norm_num [opnRightRay]
              · omega
              · omega
              · omega
            · interval_cases h <;> omega
            · interval_cases h <;> omega
  have hmain : Cov x y := by
    by_cases hxy : x ≤ y
    · exact hP (x + y) x y rfl hx hy hxy heq
    · have hyx : y ≤ x := by omega
      have hsw : y ^ 2 + y + x ^ 2 + x + 1 = 9 * (y * x - 1) := by
        calc
          y ^ 2 + y + x ^ 2 + x + 1 = x ^ 2 + x + y ^ 2 + y + 1 := by ring
          _ = 9 * (x * y - 1) := heq
          _ = 9 * (y * x - 1) := by rw [mul_comm x y]
      exact Cov_symm y x (hP (x + y) y x (by omega) hy hx hyx hsw)
  exact hmain
