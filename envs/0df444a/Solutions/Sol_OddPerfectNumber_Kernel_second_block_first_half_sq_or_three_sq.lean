-- Prove2me | solution 1 for OddPerfectNumber.Kernel.second_block_first_half_sq_or_three_sq
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:52:20.720326+00:00
-- url     : https://prove2.me/submissions/85c005ad-361b-4858-9e8d-3260eef26879

import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_second_block_gcd_dvd_three

set_option autoImplicit false
set_option linter.unusedVariables false

open OddPerfectNumber.Kernel

lemma p2m_sq_of_even_vals {n : Nat} (hn : n ≠ 0)
    (h : ∀ q : Nat, q.Prime → 2 ∣ n.factorization q) : ∃ z : Nat, n = z ^ 2 := by
  classical
  let f := n.factorization
  have hself : f.prod (fun p k => p ^ k) = n := Nat.prod_factorization_pow_eq_self hn
  have h1 : f.prod (fun p k => p ^ k) = f.prod fun p k => (p ^ (k / 2)) ^ 2 := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpprime : p.Prime := by
      have hmem : p ∈ n.primeFactors := by
        simpa [f, Nat.support_factorization] using hp
      exact Nat.prime_of_mem_primeFactors hmem
    have hdiv : 2 ∣ f p := h p hpprime
    obtain ⟨m, hm⟩ := hdiv
    have hdiv2 : f p / 2 = m := by omega
    calc
      p ^ f p = p ^ (2 * m) := by rw [hm]
      _ = p ^ (m * 2) := by rw [Nat.mul_comm]
      _ = (p ^ m) ^ 2 := Nat.pow_mul p m 2
      _ = (p ^ (f p / 2)) ^ 2 := by rw [hdiv2]
  have h2 : f.prod (fun p k => (p ^ (k / 2)) ^ 2) =
      (f.prod fun p k => p ^ (k / 2)) ^ 2 := by
    rw [Finsupp.prod, Finsupp.prod]
    exact Finset.prod_pow (s := f.support) (f := fun p => p ^ (f p / 2)) (n := 2)
  exact ⟨f.prod fun p k => p ^ (k / 2), by rw [← hself, h1, h2]⟩

lemma p2m_second_mod4 (p : Nat) (hp4 : p % 4 = 1) : (p ^ 2 - p + 1) % 4 = 1 := by
  have hdiv : p = 4 * (p / 4) + p % 4 := (Nat.div_add_mod p 4).symm
  rw [hp4] at hdiv
  set k : Nat := p / 4
  have hp : p = 4 * k + 1 := by simpa [k] using hdiv
  have hge : 4 * k + 1 ≤ (4 * k + 1) ^ 2 := by nlinarith
  have hid : (4 * k + 1) ^ 2 - (4 * k + 1) + 1 = 4 * (4 * k ^ 2 + k) + 1 := by
    zify [hge]
    ring
  rw [hp, hid]
  omega

lemma p2m_not_square_second (p : Nat) (hp : p.Prime) :
    ¬ ∃ z : Nat, p ^ 2 - p + 1 = z ^ 2 := by
  intro ⟨z, hz⟩
  have hpos : 0 < p := hp.pos
  have hle : p ≤ p ^ 2 := by nlinarith
  have hsum : p ^ 2 - p + 1 = (p - 1) ^ 2 + p := by
    have h1 : 1 ≤ p := hpos
    zify [h1, hle]
    ring
  have hlow : (p - 1) ^ 2 < z ^ 2 := by
    have : (p - 1) ^ 2 < p ^ 2 - p + 1 := by
      rw [hsum]
      omega
    rwa [hz] at this
  have hhigh : z ^ 2 < p ^ 2 := by
    have hclose : (p ^ 2 - p + 1) + (p - 1) = p ^ 2 := by
      calc
        (p ^ 2 - p + 1) + (p - 1) = (p ^ 2 - p) + (1 + (p - 1)) := by omega
        _ = (p ^ 2 - p) + p := by
          have : 1 + (p - 1) = p := by omega
          rw [this]
        _ = p ^ 2 := Nat.sub_add_cancel hle
    have hpos1 : 0 < p - 1 := by
      have := hp.two_le
      omega
    have : p ^ 2 - p + 1 < p ^ 2 := by omega
    rwa [hz] at this
  have hzlt : p - 1 < z :=
    (Nat.mul_self_lt_mul_self_iff).1 (by simpa [Nat.pow_two] using hlow)
  have hzl : z < p :=
    (Nat.mul_self_lt_mul_self_iff).1 (by simpa [Nat.pow_two] using hhigh)
  omega

theorem solution (p c y : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) (hc : c.Prime)
    (hy : ((p + 1) / 2) * (p ^ 2 - p + 1) = c * y ^ 2) :
    (∃ z : Nat, (p + 1) / 2 = z ^ 2) ∨ (∃ z : Nat, (p + 1) / 2 = 3 * z ^ 2) := by
  classical
  let A : Nat := (p + 1) / 2
  let B : Nat := p ^ 2 - p + 1
  have hA0 : A ≠ 0 := by
    have : 0 < A := by
      have : 2 ≤ p + 1 := by omega
      simpa [A] using Nat.div_pos this (by decide : 0 < 2)
    exact this.ne'
  have hB0 : B ≠ 0 := by
    have : 0 < B := by simp [B]
    exact this.ne'
  have hy0 : y ≠ 0 := by
    intro hyz
    have : A * B = 0 := by simpa [A, B, hyz] using hy
    exact mul_ne_zero hA0 hB0 this
  have hc0 : c ≠ 0 := hc.ne_zero
  have hg : Nat.gcd A B ∣ 3 := by
    simpa [A, B] using second_block_gcd_dvd_three p hp4
  have hBmod : B % 4 = 1 := by simpa [B] using p2m_second_mod4 p hp4
  have hnotsq : ¬ ∃ z : Nat, B = z ^ 2 := by simpa [B] using p2m_not_square_second p hp
  have hshare (q : Nat) (hq : q.Prime) (hq3 : q ≠ 3) : ¬ (q ∣ A ∧ q ∣ B) := by
    intro ⟨hdA, hdB⟩
    have hqg : q ∣ Nat.gcd A B := Nat.dvd_gcd hdA hdB
    have hq3d : q ∣ 3 := Nat.dvd_trans hqg hg
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq (by decide : (3 : Nat).Prime)).1 hq3d)
  have hvalRHS (q : Nat) :
      (c * y ^ 2).factorization q = c.factorization q + 2 * y.factorization q := by
    rw [Nat.factorization_mul hc0 (pow_ne_zero 2 hy0), Nat.factorization_pow]
    simp [Finsupp.smul_apply, smul_eq_mul]
  have hprod (q : Nat) :
      (A * B).factorization q = c.factorization q + 2 * y.factorization q := by
    have heq : (A * B).factorization q = (c * y ^ 2).factorization q := by
      simpa [A, B] using congrArg (fun n => n.factorization q) hy
    exact heq.trans (hvalRHS q)
  have hsum (q : Nat) :
      A.factorization q + B.factorization q = (A * B).factorization q := by
    rw [Nat.factorization_mul hA0 hB0]
    simp
  have hcval (q : Nat) : c.factorization q = if q = c then 1 else 0 := by
    rw [hc.factorization]
    by_cases hqc : q = c
    · simp [hqc]
    · simp [hqc]
  have hAeven (q : Nat) (hq : q.Prime) (hq3 : q ≠ 3) : 2 ∣ A.factorization q := by
    by_cases hqc : q = c
    · by_cases hdA : q ∣ A
      · exfalso
        have hnotB : ¬ q ∣ B := by
          intro hdB
          exact hshare q hq hq3 ⟨hdA, hdB⟩
        have hBv : B.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hnotB
        have hBeven (r : Nat) (hr : r.Prime) (hr3 : r ≠ 3) : 2 ∣ B.factorization r := by
          by_cases hrc : r = c
          · rw [hrc, ← hqc, hBv]
            exact dvd_zero _
          · have hAr : A.factorization r = 0 ∨ B.factorization r = 0 := by
              by_cases hdAr : r ∣ A
              · right
                have hnot : ¬ r ∣ B := by
                  intro hdBr
                  exact hshare r hr hr3 ⟨hdAr, hdBr⟩
                exact Nat.factorization_eq_zero_of_not_dvd hnot
              · left
                exact Nat.factorization_eq_zero_of_not_dvd hdAr
            have hpr : (A * B).factorization r = 2 * y.factorization r := by
              rw [hprod r, hcval r]
              simp [hrc]
            rw [← hsum r] at hpr
            rcases hAr with hAz | hBz
            · rw [hAz, zero_add] at hpr
              rw [hpr]
              exact dvd_mul_right _ _
            · simp [hBz]
        have he3 : 2 ∣ B.factorization 3 ∨ ¬ 2 ∣ B.factorization 3 := em _
        rcases he3 with he | ho
        · have hall (r : Nat) (hr : r.Prime) : 2 ∣ B.factorization r := by
            by_cases hr3 : r = 3
            · simpa [hr3] using he
            · exact hBeven r hr hr3
          obtain ⟨z, hz⟩ := p2m_sq_of_even_vals hB0 hall
          exact hnotsq ⟨z, hz⟩
        · have h3 : (3 : Nat).Prime := by decide
          have hne : B.factorization 3 ≠ 0 := by
            intro hz
            exact ho (by simp [hz])
          have h3le : 1 ≤ B.factorization 3 := by omega
          have h3dvd : 3 ∣ B := (h3.dvd_iff_one_le_factorization hB0).2 h3le
          have hBsplit : B = 3 * (B / 3) := (Nat.mul_div_cancel' h3dvd).symm
          set S : Nat := B / 3
          have hS0 : S ≠ 0 := by
            intro hS
            have : B = 0 := by simp [hBsplit, S, hS]
            exact hB0 this
          have hSval (r : Nat) (hr : r.Prime) :
              S.factorization r = if r = 3 then B.factorization 3 - 1 else B.factorization r := by
            have hmul := congrArg (fun n => n.factorization r)
              (show 3 * S = B by simpa [S] using hBsplit.symm)
            rw [Nat.factorization_mul (by decide : (3 : Nat) ≠ 0) hS0] at hmul
            have h3r : (3 : Nat).factorization r = if r = 3 then 1 else 0 := by
              rw [h3.factorization]
              by_cases hr3 : r = 3
              · simp [hr3]
              · simp [hr3]
            have hadd : (3 : Nat).factorization r + S.factorization r = B.factorization r := by
              simpa using hmul
            by_cases hr3 : r = 3
            · have h3r' : (3 : Nat).factorization 3 = 1 := by simpa [hr3] using h3r
              have hadd' : (3 : Nat).factorization 3 + S.factorization 3 = B.factorization 3 := by
                simpa [hr3] using hadd
              rw [h3r'] at hadd'
              simp [hr3]
              omega
            · have hadd' : S.factorization r = B.factorization r := by
                rw [h3r] at hadd
                simpa [hr3] using hadd
              simpa [hr3] using hadd'
          have hSeven (r : Nat) (hr : r.Prime) : 2 ∣ S.factorization r := by
            rw [hSval r hr]
            by_cases hr3 : r = 3
            · simp [hr3]
              have hsub : B.factorization 3 - 1 + 1 = B.factorization 3 := by omega
              -- e odd ⇒ e - 1 even
              have : (B.factorization 3) % 2 = 1 := by
                have hnot : ¬ 2 ∣ B.factorization 3 := ho
                omega
              omega
            · simp [hr3]
              exact hBeven r hr hr3
          obtain ⟨z, hz⟩ := p2m_sq_of_even_vals hS0 hSeven
          have hB3 : B = 3 * z ^ 2 := by rw [hBsplit, hz]
          have hzmod : z % 2 = 0 ∨ z % 2 = 1 := by omega
          rcases hzmod with hz0 | hz1
          · have h2z : 2 ∣ z := Nat.dvd_of_mod_eq_zero hz0
            obtain ⟨t, ht⟩ := h2z
            have h4 : 4 ∣ B := by
              rw [hB3, ht]
              refine ⟨3 * t ^ 2, ?_⟩
              ring
            have : B % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
            omega
          · have ht : z = 2 * (z / 2) + 1 := by omega
            have hsqexp : (2 * (z / 2) + 1) ^ 2 = 4 * ((z / 2) * ((z / 2) + 1)) + 1 := by ring
            have hsq : z ^ 2 % 4 = 1 := by
              rw [ht, hsqexp]
              omega
            have hrepr : z ^ 2 = 4 * (z ^ 2 / 4) + 1 := by
              have := (Nat.div_add_mod (z ^ 2) 4).symm
              omega
            have hB4 : B % 4 = 3 := by
              rw [hB3, hrepr]
              omega
            omega
      · exact Nat.dvd_of_mod_eq_zero (by
          have : A.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hdA
          simp [this])
    · have hpr : (A * B).factorization q = 2 * y.factorization q := by
        rw [hprod q, hcval q]
        simp [hqc]
      have hAB : A.factorization q + B.factorization q = 2 * y.factorization q := by
        rw [hsum q, hpr]
      by_cases hdA : q ∣ A
      · have hnotB : ¬ q ∣ B := by
          intro hdB
          exact hshare q hq hq3 ⟨hdA, hdB⟩
        have hBv : B.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hnotB
        rw [hBv, add_zero] at hAB
        rw [hAB]
        exact dvd_mul_right _ _
      · have : A.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hdA
        simp [this]
  have he3 : 2 ∣ A.factorization 3 ∨ ¬ 2 ∣ A.factorization 3 := em _
  rcases he3 with he | ho
  · left
    have hall (q : Nat) (hq : q.Prime) : 2 ∣ A.factorization q := by
      by_cases hq3 : q = 3
      · simpa [hq3] using he
      · exact hAeven q hq hq3
    simpa [A] using p2m_sq_of_even_vals hA0 hall
  · right
    have h3 : (3 : Nat).Prime := by decide
    have hne : A.factorization 3 ≠ 0 := by
      intro hz
      exact ho (by simp [hz])
    have h3le : 1 ≤ A.factorization 3 := by omega
    have h3dvd : 3 ∣ A := (h3.dvd_iff_one_le_factorization hA0).2 h3le
    have hAsplit : A = 3 * (A / 3) := (Nat.mul_div_cancel' h3dvd).symm
    set S : Nat := A / 3
    have hS0 : S ≠ 0 := by
      intro hS
      have : A = 0 := by simp [hAsplit, S, hS]
      exact hA0 this
    have hSval (r : Nat) (hr : r.Prime) :
        S.factorization r = if r = 3 then A.factorization 3 - 1 else A.factorization r := by
      have hmul := congrArg (fun n => n.factorization r)
        (show 3 * S = A by simpa [S] using hAsplit.symm)
      rw [Nat.factorization_mul (by decide : (3 : Nat) ≠ 0) hS0] at hmul
      have h3r : (3 : Nat).factorization r = if r = 3 then 1 else 0 := by
        rw [h3.factorization]
        by_cases hr3 : r = 3
        · simp [hr3]
        · simp [hr3]
      have hadd : (3 : Nat).factorization r + S.factorization r = A.factorization r := by
        simpa using hmul
      by_cases hr3 : r = 3
      · have h3r' : (3 : Nat).factorization 3 = 1 := by simpa [hr3] using h3r
        have hadd' : (3 : Nat).factorization 3 + S.factorization 3 = A.factorization 3 := by
          simpa [hr3] using hadd
        rw [h3r'] at hadd'
        simp [hr3]
        omega
      · have hadd' : S.factorization r = A.factorization r := by
          rw [h3r] at hadd
          simpa [hr3] using hadd
        simpa [hr3] using hadd'
    have hSeven (r : Nat) (hr : r.Prime) : 2 ∣ S.factorization r := by
      rw [hSval r hr]
      by_cases hr3 : r = 3
      · simp [hr3]
        have : A.factorization 3 % 2 = 1 := by
          have : ¬ 2 ∣ A.factorization 3 := ho
          omega
        omega
      · simp [hr3]
        exact hAeven r hr hr3
    obtain ⟨z, hz⟩ := p2m_sq_of_even_vals hS0 hSeven
    refine ⟨z, ?_⟩
    simpa [A, S, hz] using hAsplit
