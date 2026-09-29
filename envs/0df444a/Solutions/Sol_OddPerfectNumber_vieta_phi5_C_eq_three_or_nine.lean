-- Prove2me | solution 1 for OddPerfectNumber.vieta_phi5_C_eq_three_or_nine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T08:24:11.791178+00:00
-- url     : https://prove2.me/submissions/cf64b5a4-3eb9-4332-b6eb-7281759df51d

import Mathlib
import Theorems.Thm_OddPerfectNumber_vieta_phi5_other_root

open OddPerfectNumber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

theorem solution (x y C : Nat)
    (hx : 0 < x)
    (hy : 0 < y)
    (heq : x ^ 2 + x + y ^ 2 + y + 1 = C * (x * y - 1)) :
    C = 3 ∨ C = 9 := by
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

  have diag_u_le3 : ∀ u D : Nat,
      2 ≤ u →
      3 ≤ D →
      2 * u ^ 2 + 2 * u + 1 = D * (u ^ 2 - 1) →
      u ≤ 3 := by
    intro u D hu hD hEq
    have hmul : 3 * (u ^ 2 - 1) ≤ D * (u ^ 2 - 1) := by
      exact Nat.mul_le_mul_right (u ^ 2 - 1) hD
    have hineq : 3 * (u ^ 2 - 1) ≤ 2 * u ^ 2 + 2 * u + 1 := by
      calc
        3 * (u ^ 2 - 1) ≤ D * (u ^ 2 - 1) := hmul
        _ = 2 * u ^ 2 + 2 * u + 1 := hEq.symm
    by_contra hu4
    have hu4' : 4 ≤ u := by omega
    have hu_sq : 4 * u ≤ u ^ 2 := by nlinarith
    have hsub : u ^ 2 - 1 + 1 = u ^ 2 := by omega
    nlinarith

  have finite_base : ∀ u h D : Nat,
      1 ≤ u →
      u ≤ 3 →
      1 ≤ h →
      h ≤ 4 →
      u ^ 2 + u + (u + h) ^ 2 + (u + h) + 1 =
        D * (u * (u + h) - 1) →
      D = 3 ∨ D = 9 := by
    intro u h D hu hu3 hh hh4 hEq
    have hu_cases : u = 1 ∨ u = 2 ∨ u = 3 := by omega
    rcases hu_cases with rfl | rfl | rfl <;>
      interval_cases h <;> omega

  let P : Nat → Prop := fun n =>
    ∀ x y C : Nat,
      x + y = n →
      0 < x →
      0 < y →
      x ^ 2 + x + y ^ 2 + y + 1 = C * (x * y - 1) →
      C = 3 ∨ C = 9
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b K habsum ha hb habeq
        have ordered : ∀ (u v D : Nat),
            u + v = n →
            0 < u →
            0 < v →
            u ≤ v →
            u ^ 2 + u + v ^ 2 + v + 1 = D * (u * v - 1) →
            D = 3 ∨ D = 9 := by
          intro u v D huv hu hv huvle hD
          obtain ⟨z, hz, hvz, hvprod, hzeq⟩ :=
            vieta_phi5_other_root u v D hu hv hD
          by_cases hzy : z < v
          · have hlt : u + z < n := by omega
            have hrec : P (u + z) := ih (u + z) hlt
            exact hrec u z D rfl hu hz hzeq
          · have hvz' : v ≤ z := by omega
            by_cases huv_eq : u = v
            · subst v
              have hu1 : u ≠ 1 := by
                intro hu1
                subst u
                norm_num at hD
              have hu2 : 2 ≤ u := by omega
              have hDdiag : 2 * u ^ 2 + 2 * u + 1 = D * (u ^ 2 - 1) := by
                calc
                  2 * u ^ 2 + 2 * u + 1 =
                      u ^ 2 + u + u ^ 2 + u + 1 := by ring
                  _ = D * (u * u - 1) := hD
                  _ = D * (u ^ 2 - 1) := by rw [pow_two]
              have hDthree : 3 ≤ D := by
                have hlin : 2 * u + 1 ≤ D * u := by omega
                nlinarith
              have hu_le3 := diag_u_le3 u D hu2 hDthree hDdiag
              interval_cases u <;> omega
            · have huv_lt : u < v := by omega
              let h : Nat := v - u
              have hh : 1 ≤ h := by
                dsimp [h]
                omega
              have hv_eq : v = u + h := by
                dsimp [h]
                omega
              have hlin : 2 * v + 1 ≤ D * u := by omega
              have hDpos : 0 < u * v - 1 := by
                have hu1 : 1 ≤ u := by omega
                have hv2 : 2 ≤ v := by omega
                nlinarith
              have hmul :
                  (2 * v + 1) * (u * v - 1) ≤
                    (D * u) * (u * v - 1) := by
                exact Nat.mul_le_mul_right (u * v - 1) hlin
              have hDmul :
                  (D * u) * (u * v - 1) =
                    u * (u ^ 2 + u + v ^ 2 + v + 1) := by
                calc
                  (D * u) * (u * v - 1) = u * (D * (u * v - 1)) := by ring
                  _ = u * (u ^ 2 + u + v ^ 2 + v + 1) := by rw [hD]
              have hineq :
                  (2 * v + 1) * (u * v - 1) ≤
                    u * (u ^ 2 + u + v ^ 2 + v + 1) := by
                calc
                  (2 * v + 1) * (u * v - 1) ≤
                      (D * u) * (u * v - 1) := hmul
                  _ = u * (u ^ 2 + u + v ^ 2 + v + 1) := hDmul
              have hbase :
                  h ^ 2 * u + 2 * h * u ^ 2 ≤
                    2 * h + u ^ 2 + 3 * u + 1 := by
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
                    (2 * v + 1) * (u * v) +
                        (2 * h + u ^ 2 + 3 * u + 1) =
                      (u * (u ^ 2 + u + v ^ 2 + v + 1) + (2 * v + 1)) +
                        (h ^ 2 * u + 2 * h * u ^ 2) := by
                  rw [hv_eq]
                  ring
                have hadd' := Nat.add_le_add_right hadd
                    (h ^ 2 * u + 2 * h * u ^ 2)
                rw [← hpoly] at hadd'
                exact Nat.le_of_add_le_add_left hadd'
              have hu1 : 1 ≤ u := by omega
              have hu_le3 := base_u_le3 u h (by omega) hh hbase
              have hh_le4 := base_h_le4 u h hu1 hu_le3 hh hbase
              have hEq :
                  u ^ 2 + u + (u + h) ^ 2 + (u + h) + 1 =
                    D * (u * (u + h) - 1) := by
                rw [← hv_eq]
                exact hD
              exact finite_base u h D hu1 hu_le3 hh hh_le4 hEq
        by_cases hable : a ≤ b
        · exact ordered a b K habsum ha hb hable habeq
        · have hba : b ≤ a := by omega
          have hswap :
              b ^ 2 + b + a ^ 2 + a + 1 = K * (b * a - 1) := by
            calc
              b ^ 2 + b + a ^ 2 + a + 1 =
                  a ^ 2 + a + b ^ 2 + b + 1 := by ring
              _ = K * (a * b - 1) := habeq
              _ = K * (b * a - 1) := by rw [mul_comm a b]
          exact ordered b a K (by omega) hb ha hba hswap
  exact hP (x + y) x y C rfl hx hy heq
