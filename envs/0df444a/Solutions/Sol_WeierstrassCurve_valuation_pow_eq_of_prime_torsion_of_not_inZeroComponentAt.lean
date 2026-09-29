-- Prove2me | solution 1 for WeierstrassCurve.valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/14a34910-5ff5-5b59-8c9b-a2b4fd8d2a0b

import Mathlib.RingTheory.Valuation.ValuationSubring
import Theorems.Thm_WeierstrassCurve_valuation_discriminant_eq_of_criticalCentre
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_level_eq_of_branch_ne
import Theorems.Thm_WeierstrassCurve_level_add_of_branch_eq
import Theorems.Thm_WeierstrassCurve_level_add_of_branch_ne_of_level_lt
import Theorems.Thm_WeierstrassCurve_level_add_of_antipodal_of_shallow
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_add_of_antipodal
import Theorems.Thm_WeierstrassCurve_level_add_of_inZeroComponentAt
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

section Helpers
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem tl_lt_of_mul_lt_mul_right {a b c : Γ₀} (h : a * c < b * c) : a < b := by
  by_contra hle
  exact absurd h (not_lt.mpr (mul_le_mul' (not_lt.mp hle) le_rfl))

theorem tl_pow_left_inj {a b : Γ₀} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (pow_lt_pow_left₀ hab zero_le' hn))
  · exact hab
  · exact absurd h (ne_of_gt (pow_lt_pow_left₀ hab zero_le' hn))

theorem tl_H1 {F L M N : Γ₀} {j m : ℕ} (hj : M ^ 2 * F ^ (2 * j) = L ^ (2 * m)) (hN : N = M * L) :
    N ^ 2 * F ^ (2 * j) = L ^ (2 * (m + 1)) := by
  rw [hN, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, ← hj, mul_pow]
  simp only [sq, mul_comm, mul_left_comm, mul_assoc]

theorem tl_H2 {F L M : Γ₀} {j m : ℕ} (hj : M ^ 2 * F ^ (2 * j) = L ^ (2 * m)) (hF : F = (M * L) ^ 2) :
    F ^ (2 * j + 1) = L ^ (2 * (m + 1)) := by
  calc F ^ (2 * j + 1) = F ^ (2 * j) * F := pow_succ F (2 * j)
    _ = F ^ (2 * j) * (M * L) ^ 2 := by rw [← hF]
    _ = (M ^ 2 * F ^ (2 * j)) * L ^ 2 := by simp only [sq, mul_comm, mul_left_comm, mul_assoc]
    _ = L ^ (2 * m) * L ^ 2 := by rw [hj]
    _ = L ^ (2 * (m + 1)) := by rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]

theorem tl_H3 {F L M N : Γ₀} {j m : ℕ} (hj : M ^ 2 * F ^ (2 * j) = L ^ (2 * m)) (hN : N * (M * L) = F)
    (hML : M * L ≠ 0) : F ^ (2 * j + 2) = L ^ (2 * (m + 1)) * N ^ 2 := by

  have key : F ^ (2 * j + 2) * (M * L) ^ 2 = L ^ (2 * (m + 1)) * N ^ 2 * (M * L) ^ 2 := by
    calc F ^ (2 * j + 2) * (M * L) ^ 2 = F ^ (2 * j) * F ^ 2 * (M * L) ^ 2 := by rw [pow_add]
      _ = (M ^ 2 * F ^ (2 * j)) * L ^ 2 * (N * (M * L)) ^ 2 := by
          rw [hN]; simp only [sq, mul_comm, mul_left_comm, mul_assoc]
      _ = L ^ (2 * m) * L ^ 2 * (N * (M * L)) ^ 2 := by rw [hj]
      _ = L ^ (2 * (m + 1)) * N ^ 2 * (M * L) ^ 2 := by
          rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
          simp only [sq, mul_comm, mul_left_comm, mul_assoc]
  exact mul_right_cancel₀ (pow_ne_zero 2 hML) key

theorem tl_H4 {F L M N : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 2) = L ^ (2 * m) * M ^ 2) (hN : N * L = M) :
    F ^ (2 * j + 2) = L ^ (2 * (m + 1)) * N ^ 2 := by
  rw [hj, ← hN, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, mul_pow]
  simp only [sq, mul_comm, mul_left_comm, mul_assoc]

theorem tl_H5 {F L M : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 2) = L ^ (2 * m) * M ^ 2) (hM : M = L) :
    F ^ (2 * (j + 1)) = L ^ (2 * (m + 1)) := by
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, hj, hM, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]

theorem tl_H6 {F L M N : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 2) = L ^ (2 * m) * M ^ 2) (hN : N * M = L)
    (hM : M ≠ 0) : N ^ 2 * F ^ (2 * (j + 1)) = L ^ (2 * (m + 1)) := by
  have key : N ^ 2 * F ^ (2 * (j + 1)) * M ^ 2 = L ^ (2 * (m + 1)) * M ^ 2 := by
    calc N ^ 2 * F ^ (2 * (j + 1)) * M ^ 2 = (N * M) ^ 2 * F ^ (2 * j + 2) := by
          rw [show 2 * (j + 1) = 2 * j + 2 by ring, mul_pow]
          simp only [sq, mul_comm, mul_left_comm, mul_assoc]
      _ = L ^ 2 * (L ^ (2 * m) * M ^ 2) := by rw [hN, hj]
      _ = L ^ (2 * (m + 1)) * M ^ 2 := by
          rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
          simp only [sq, mul_comm, mul_left_comm, mul_assoc]
  exact mul_right_cancel₀ (pow_ne_zero 2 hM) key

theorem tl_H7 {F L N : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 1) = L ^ (2 * m)) (hN : (N * L) ^ 2 = F) :
    F ^ (2 * j + 2) = L ^ (2 * (m + 1)) * N ^ 2 := by
  rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, hj, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add,
    ← hN, mul_pow]
  simp only [sq, mul_comm, mul_left_comm, mul_assoc]

theorem tl_S3 {F N P : Γ₀} (hN : N * P = F) (hlt : P ^ 2 < F) (hF : 0 < F) : F < N ^ 2 := by
  have hP0 : 0 < P := by
    rcases eq_or_lt_of_le (zero_le' : (0:Γ₀) ≤ P) with h0 | h0
    · rw [← h0, mul_zero] at hN; rw [hN] at hF; exact absurd hF (lt_irrefl _)
    · exact h0
  have h1 : P * P < N * P := by rw [hN, ← sq]; exact hlt
  have h2 : P < N := tl_lt_of_mul_lt_mul_right h1
  calc F = N * P := hN.symm
    _ < N * N := by
        have hN0 : 0 < N := lt_of_le_of_lt zero_le' h2
        have := mul_lt_mul_of_pos_right h2 hN0
        rwa [mul_comm P N] at this
    _ = N ^ 2 := (sq N).symm

theorem tl_S4 {F L M N : Γ₀} (hN : N * L = M) (hF : F < M ^ 2) (hL1 : L < 1)
    (hML : M < L) : F < N ^ 2 ∧ N < 1 := by
  have hMN : M ≤ N := by
    rw [← hN]
    calc N * L ≤ N * 1 := mul_le_mul' le_rfl (le_of_lt hL1)
      _ = N := mul_one N
  constructor
  · calc F < M ^ 2 := hF
      _ ≤ N ^ 2 := pow_le_pow_left₀ zero_le' hMN 2
  · have : N * L < 1 * L := by rw [hN, one_mul]; exact hML
    exact tl_lt_of_mul_lt_mul_right this

theorem tl_S6 {F L M N : Γ₀} (hN : N * M = L) (hF : F < L ^ 2) (hM1 : M < 1)
    (hLM : L < M) : F < N ^ 2 ∧ N < 1 := by
  have hLN : L ≤ N := by
    rw [← hN]
    calc N * M ≤ N * 1 := mul_le_mul' le_rfl (le_of_lt hM1)
      _ = N := mul_one N
  constructor
  · calc F < L ^ 2 := hF
      _ ≤ N ^ 2 := pow_le_pow_left₀ zero_le' hLN 2
  · have : N * M < 1 * M := by rw [hN, one_mul]; exact hLM
    exact tl_lt_of_mul_lt_mul_right this

theorem tl_S7 {F L N : Γ₀} (hN : (N * L) ^ 2 = F) (hF : F < L ^ 2) (hF0 : 0 < F) (hL1 : L < 1) :
    F < N ^ 2 ∧ N < 1 := by
  have hN1 : N < 1 := by
    have : (N * L) ^ 2 < (1 * L) ^ 2 := by rw [hN, one_mul]; exact hF
    by_contra hle
    have hle' : 1 * L ≤ N * L := mul_le_mul' (not_lt.mp hle) le_rfl
    exact absurd this (not_lt.mpr (pow_le_pow_left₀ zero_le' hle' 2))
  have hN0 : 0 < N := by
    rcases eq_or_lt_of_le (zero_le' : (0:Γ₀) ≤ N) with h0 | h0
    · rw [← h0, zero_mul, zero_pow two_ne_zero] at hN
      rw [← hN] at hF0
      exact absurd hF0 (lt_irrefl _)
    · exact h0
  refine ⟨?_, hN1⟩
  rw [← hN, mul_pow]
  calc N ^ 2 * L ^ 2 < N ^ 2 * 1 := by
        apply mul_lt_mul_of_pos_left _ (pow_pos hN0 2)
        exact pow_lt_one₀ zero_le' hL1 two_ne_zero
    _ = N ^ 2 := mul_one _

end Helpers

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : ℓ • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1) :
    A.valuation (W.Δ : AlgebraicClosure ℚ) < A.valuation (x - x₀) ^ 2 ∧
      ∃ j : ℕ, 1 ≤ j ∧ 2 * j < ℓ ∧
        A.valuation (x - x₀) ^ ℓ = A.valuation (W.Δ : AlgebraicClosure ℚ) ^ j := by

  have _ : q.Prime ∧ (q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄ ∧ A.LiesOverPrime q := ⟨hq, hqΔ, hqc₄, hA⟩

  have hDisc := WeierstrassCurve.valuation_discriminant_eq_of_criticalCentre W A hx₀ hy₀ hFy hFx hnode hbad
  rw [hDisc]

  obtain ⟨vF, hvF⟩ : ∃ g, A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) = g := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ g, A.valuation (x - x₀) = g := ⟨_, rfl⟩
  rw [hvF, hL]
  have hvF1 : vF < 1 := hvF ▸ hbad
  have hL1 : L < 1 := hL ▸ hX
  have hvF0 : 0 < vF := by
    rw [← hvF, ← hDisc]
    apply lt_of_le_of_ne zero_le'
    symm
    rw [Valuation.ne_zero_iff]
    exact_mod_cast hΔ
  have hℓ3 : 3 ≤ ℓ := by
    have := hℓ.two_le
    omega

  have same_same : ∀ {a b c : AlgebraicClosure ℚ}, A.valuation (a - b) < 1 → A.valuation (b - c) < 1 →
      A.valuation (a - c) < 1 := by
    intro a b c h1 h2
    have := Valuation.map_add_lt A.valuation h1 h2
    rwa [show a - b + (b - c) = a - c by ring] at this
  have opp_same : ∀ {a b c : AlgebraicClosure ℚ}, A.valuation (a - b) = 1 → A.valuation (b - c) < 1 →
      A.valuation (a - c) = 1 := by
    intro a b c h1 h2
    have h2' : A.valuation (b - c) < A.valuation (a - b) := by rwa [h1]
    have := Valuation.map_add_eq_of_lt_left A.valuation h2'
    rw [show a - b + (b - c) = a - c by ring] at this
    rw [this, h1]
  have same_opp : ∀ {a b c : AlgebraicClosure ℚ}, A.valuation (a - b) < 1 → A.valuation (b - c) = 1 →
      A.valuation (a - c) = 1 := by
    intro a b c h1 h2
    have h1' : A.valuation (a - b) < A.valuation (b - c) := by rwa [h2]
    have := Valuation.map_add_eq_of_lt_right A.valuation h1'
    rw [show a - b + (b - c) = a - c by ring] at this
    rw [this, h2]
  rcases lt_or_ge vF (L ^ 2) with hsh | hanti
  ·
    have hshR : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x - x₀) ^ 2 := by
      rw [hvF, hL]; exact hsh

    have main : ∀ m : ℕ, 1 ≤ m →
        (W.InZeroComponentAt A (m • Point.some x y h) ∧ ∃ j : ℕ, vF ^ (2 * j) = L ^ (2 * m)) ∨
        (∃ (x' y' : AlgebraicClosure ℚ)
            (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - x₀) < 1 ∧
            vF < A.valuation (x' - x₀) ^ 2 ∧
            A.valuation ((y' - y₀) / (x' - x₀) - (y - y₀) / (x - x₀)) < 1 ∧
            ∃ j : ℕ, A.valuation (x' - x₀) ^ 2 * vF ^ (2 * j) = L ^ (2 * m)) ∨
        (∃ (x' y' : AlgebraicClosure ℚ)
            (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - x₀) < 1 ∧
            vF < A.valuation (x' - x₀) ^ 2 ∧
            A.valuation ((y' - y₀) / (x' - x₀) - (y - y₀) / (x - x₀)) = 1 ∧
            ∃ j : ℕ, vF ^ (2 * j + 2) = L ^ (2 * m) * A.valuation (x' - x₀) ^ 2) ∨
        (∃ (x' y' : AlgebraicClosure ℚ)
            (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - x₀) < 1 ∧
            A.valuation (x' - x₀) ^ 2 ≤ vF ∧
            ∃ j : ℕ, vF ^ (2 * j + 1) = L ^ (2 * m)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>

        refine Or.inr (Or.inl ⟨x, y, h, one_nsmul _, hX, ?_, ?_, 0, ?_⟩)
        · rw [hL]; exact hsh
        · rw [sub_self, Valuation.map_zero]; exact zero_lt_one
        · rw [hL]; simp
      | succ m hm ih =>
        rw [succ_nsmul]
        rcases ih with ⟨hE0, j, hj⟩ | ⟨x', y', h', hmP, hX', hsh', hbr', j, hj⟩ |
            ⟨x', y', h', hmP, hX', hsh', hbr', j, hj⟩ | ⟨x', y', h', hmP, hX', hanti', j, hj⟩
        ·
          obtain ⟨x₃, y₃, h₃, hsum, hX₃, hshcl, -⟩ :=
            WeierstrassCurve.level_add_of_inZeroComponentAt W A hx₀ hy₀ hFy hFx hnode hbad
              (m • Point.some x y h) hE0 h hX
          obtain ⟨hlev₃, hbr₃⟩ := hshcl hshR
          rw [hL] at hlev₃
          refine Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, ?_, hbr₃, j, ?_⟩)
          · rw [hlev₃]; exact hsh
          · rw [hlev₃, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, ← hj]
            simp only [sq, mul_comm, mul_assoc]
        ·
          have hshR' : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
              - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x' - x₀) ^ 2 := by
            rw [hvF]; exact hsh'
          obtain ⟨x₃, y₃, h₃, hsum, hX₃, hci, hcii, hciii⟩ :=
            WeierstrassCurve.level_add_of_branch_eq W A hx₀ hy₀ hFy hFx hnode hbad h' h hX' hX hshR' hshR hbr'
          rw [hvF, hL] at hci hcii hciii
          rw [hmP]
          rcases lt_trichotomy vF ((A.valuation (x' - x₀) * L) ^ 2) with hc | hc | hc
          ·
            obtain ⟨hlev₃, hbr₃⟩ := hci hc
            refine Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, ?_, same_same hbr₃ hbr', j, tl_H1 hj hlev₃⟩)
            rw [hlev₃]; exact hc
          ·
            exact Or.inr (Or.inr (Or.inr ⟨x₃, y₃, h₃, hsum, hX₃, hcii hc, j, tl_H2 hj hc⟩))
          ·
            obtain ⟨hlev₃, hbr₃⟩ := hciii hc
            have hML : A.valuation (x' - x₀) * L ≠ 0 := by
              intro h0
              rw [h0, mul_zero] at hlev₃
              exact absurd hlev₃ (ne_of_gt hvF0).symm
            exact Or.inr (Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, tl_S3 hlev₃ hc hvF0,
              opp_same hbr₃ hbr', j, tl_H3 hj hlev₃ hML⟩))
        ·
          have hshR' : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
              - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < A.valuation (x' - x₀) ^ 2 := by
            rw [hvF]; exact hsh'
          rw [hmP]
          rcases lt_trichotomy (A.valuation (x' - x₀)) L with hc | hc | hc
          ·
            have hcR : A.valuation (x' - x₀) < A.valuation (x - x₀) := by rw [hL]; exact hc
            obtain ⟨x₃, y₃, h₃, hsum, hlev₃, hbr₃⟩ :=
              WeierstrassCurve.level_add_of_branch_ne_of_level_lt W A hx₀ hy₀ hFy hFx hnode hbad
                h' h hX hcR hshR' hbr'
            rw [hL] at hlev₃
            obtain ⟨hsh₃, hX₃⟩ := tl_S4 hlev₃ hsh' hL1 hc
            exact Or.inr (Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, hsh₃, same_opp hbr₃ hbr', j,
              tl_H4 hj hlev₃⟩))
          ·
            have hcR : A.valuation (x' - x₀) = A.valuation (x - x₀) := by rw [hL]; exact hc
            have hE0 := (WeierstrassCurve.inZeroComponentAt_add_of_level_eq_of_branch_ne W A hx₀ hy₀ hFy hFx
              hnode hbad h' h hX' hX hcR hshR' hbr').1
            exact Or.inl ⟨hE0, j + 1, tl_H5 hj hc⟩
          ·
            have hbr'' : A.valuation ((y - y₀) / (x - x₀) - (y' - y₀) / (x' - x₀)) = 1 := by
              rw [Valuation.map_sub_swap]; exact hbr'
            have hcR : A.valuation (x - x₀) < A.valuation (x' - x₀) := by rw [hL]; exact hc
            obtain ⟨x₃, y₃, h₃, hsum, hlev₃, hbr₃⟩ :=
              WeierstrassCurve.level_add_of_branch_ne_of_level_lt W A hx₀ hy₀ hFy hFx hnode hbad
                h h' hX' hcR hshR hbr''
            rw [add_comm] at hsum
            rw [hL] at hlev₃
            have hM0 : A.valuation (x' - x₀) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hc)
            obtain ⟨hsh₃, hX₃⟩ := tl_S6 hlev₃ hsh hX' hc
            exact Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, hsh₃, hbr₃, j + 1, tl_H6 hj hlev₃ hM0⟩)
        ·
          have hantiR : A.valuation (x' - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
              - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
            rw [hvF]; exact hanti'
          rw [hmP]
          obtain ⟨x₃, y₃, h₃, hsum, hlev₃, hbr₃⟩ :=
            WeierstrassCurve.level_add_of_antipodal_of_shallow W A hx₀ hy₀ hFy hFx hnode hbad
              h' h hX' hantiR hX hshR
          rw [hvF, hL] at hlev₃
          obtain ⟨hsh₃, hX₃⟩ := tl_S7 hlev₃ hsh hvF0 hL1
          exact Or.inr (Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, hsh₃, hbr₃, j, tl_H7 hj hlev₃⟩))

    have hfin := main ℓ (by omega)
    rw [htor] at hfin
    rcases hfin with ⟨-, j, hj⟩ | ⟨x', y', h', h0, -⟩ | ⟨x', y', h', h0, -⟩ | ⟨x', y', h', h0, -⟩
    · have hjℓ : vF ^ j = L ^ ℓ := by
        apply tl_pow_left_inj (n := 2) two_ne_zero
        rw [← pow_mul, ← pow_mul, mul_comm j 2, mul_comm ℓ 2, hj]
      refine ⟨hsh, j, ?_, ?_, hjℓ.symm⟩
      ·
        by_contra hj0
        have hj0 : j = 0 := by omega
        rw [hj0, pow_zero] at hjℓ
        exact absurd hjℓ (ne_of_gt (pow_lt_one₀ zero_le' hL1 (by omega)))
      ·
        by_contra hle
        have hle : ℓ ≤ 2 * j := by omega
        have h1 : vF ^ j < (L ^ 2) ^ j := pow_lt_pow_left₀ hsh zero_le' (by omega)
        rw [← pow_mul, hjℓ] at h1
        have h2 : L ^ (2 * j) ≤ L ^ ℓ := pow_le_pow_right_of_le_one' (le_of_lt hL1) hle
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    · exact absurd h0.symm (Point.some_ne_zero h')
    · exact absurd h0.symm (Point.some_ne_zero h')
    · exact absurd h0.symm (Point.some_ne_zero h')
  ·
    exfalso
    have hantiR : A.valuation (x - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
      rw [hvF, hL]; exact hanti
    have alt : ∀ m : ℕ, 1 ≤ m →
        (Odd m → ∃ (x' y' : AlgebraicClosure ℚ)
            (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - x₀) < 1 ∧
            A.valuation (x' - x₀) ^ 2 ≤ A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
              - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))) ∧
        (Even m → W.InZeroComponentAt A (m • Point.some x y h)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        refine ⟨fun _ => ⟨x, y, h, one_nsmul _, hX, hantiR⟩, fun h1 => ?_⟩
        exact absurd h1 (by decide)
      | succ m hm ih =>
        rw [succ_nsmul]
        refine ⟨fun hodd => ?_, fun heven => ?_⟩
        · have hev : Even m := by
            rcases Nat.even_or_odd m with he | ho
            · exact he
            · exact absurd hodd (Nat.not_odd_iff_even.mpr (ho.add_one))
          obtain ⟨x₃, y₃, h₃, hsum, hX₃, -, hanticl⟩ :=
            WeierstrassCurve.level_add_of_inZeroComponentAt W A hx₀ hy₀ hFy hFx hnode hbad
              (m • Point.some x y h) (ih.2 hev) h hX
          exact ⟨x₃, y₃, h₃, hsum, hX₃, hanticl hantiR⟩
        · have hodd : Odd m := by
            rcases Nat.even_or_odd m with he | ho
            · exact absurd heven (Nat.not_even_iff_odd.mpr (he.add_one))
            · exact ho
          obtain ⟨x', y', h', hmP, hX', hanti'⟩ := ih.1 hodd
          rw [hmP]
          exact WeierstrassCurve.inZeroComponentAt_add_of_antipodal W A hx₀ hy₀ hFy hFx hnode hbad
            h' h hX' hanti' hX hantiR
    have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
    obtain ⟨x', y', h', h0, -⟩ := (alt ℓ (by omega)).1 hℓodd
    rw [htor] at h0
    exact absurd h0.symm (Point.some_ne_zero h')

end S_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt
end P2MW
export P2MW.S_WeierstrassCurve_valuation_pow_eq_of_prime_torsion_of_not_inZeroComponentAt (solution)
