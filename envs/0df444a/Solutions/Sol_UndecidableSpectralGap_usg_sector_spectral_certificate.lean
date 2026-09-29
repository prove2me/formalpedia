-- Prove2me | solution 1 for UndecidableSpectralGap.usg_sector_spectral_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T20:35:59.192716+00:00
-- url     : https://prove2.me/submissions/7487cbf0-ac9a-4a1b-bf25-96956eeafbd4

import Theorems.Thm_UndecidableSpectralGap_usg_switch_finite_spectrum
import Theorems.Thm_UndecidableSpectralGap_usg_switch_magnon_density

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ComplexOrder

open UndecidableSpectralGap

theorem solution (u : Nat.Partrec.Code) (ε : ℝ) (hε : 0 < ε) :
    ∃ (d : ℕ) (A A' B C D D' : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
      (Pi : Matrix (Fin d) (Fin d) ℂ) (β : ℚ) (α : ℕ → ℝ),
      -- `β` is a rational number, as small as desired
      0 < β ∧ (β : ℝ) < ε ∧
      -- (i) `A` is diagonal with integer entries
      (∀ i j, i ≠ j → A i j = 0) ∧ (∀ i, ∃ a : ℤ, A i i = (a : ℂ)) ∧
      -- (ii) `A'` is Hermitian with entries in `ℤ + (1/√2) ℤ`
      A'.IsHermitian ∧
        (∀ i j, ∃ a b : ℤ, A' i j = (a : ℂ) + (b : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) ∧
      -- (iii) `B`, `C` have integer entries
      (∀ i j, ∃ a : ℤ, B i j = (a : ℂ)) ∧ (∀ i j, ∃ a : ℤ, C i j = (a : ℂ)) ∧
      -- (iv) `D` is diagonal with integer entries
      (∀ i j, i ≠ j → D i j = 0) ∧ (∀ i, ∃ a : ℤ, D i i = (a : ℂ)) ∧
      -- (v) `D'` is Hermitian with integer entries
      D'.IsHermitian ∧ (∀ i j, ∃ a : ℤ, D' i j = (a : ℂ)) ∧
      -- `Π` is a diagonal projector
      Pi.IsHermitian ∧ (∀ i j, i ≠ j → Pi i j = 0) ∧ Pi * Pi = Pi ∧
      -- `α(n)` is an algebraic number bounded by `2β`
      (∀ n, IsAlgebraic ℚ (α n) ∧ α n ≤ 2 * (β : ℝ)) ∧
      ∀ n : ℕ, ∀ (h1 : Matrix (Fin d) (Fin d) ℂ)
        (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
        h1 = ((α n : ℝ) : ℂ) • Pi →
        hcol = D + ((β : ℝ) : ℂ) • D' →
        hrow = A + ((β : ℝ) : ℂ) •
          (A' + Complex.exp (Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ)) • B
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * ((phi n : ℚ) : ℂ))) • B.conjTranspose
            + Complex.exp (Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ))) • C
            + Complex.exp (-(Complex.I * (Real.pi : ℂ) * (2 : ℂ) ^ (-(phiLen n : ℤ)))) • C.conjTranspose) →
        -- (i) the local interaction strength is bounded by 1
        localInteractionStrength h1 hrow hcol ≤ 1 ∧
        ∃ (E : ℕ → ℝ) (S : ℕ → Set ℝ) (L0 : ℕ),
          (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ L > N,
            ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ S L, |x - s| ≤ δ) ∧
          (∀ L > L0,
            (0 ∈ specReal (latticeHam L d h1 hrow hcol) ∧
             E L ∈ specReal (latticeHam L d h1 hrow hcol) ∧
             ∀ μ ∈ specReal (latticeHam L d h1 hrow hcol), min 0 (E L) ≤ μ) ∧
            (∀ s ∈ S L, E L + s ∈ specReal (latticeHam L d h1 hrow hcol)) ∧
            (1 ≤ E L → eigMultiplicity (latticeHam L d h1 hrow hcol) 0 = 1 ∧
              ∀ μ ∈ specReal (latticeHam L d h1 hrow hcol), μ ≠ 0 → 1 ≤ μ)) ∧
          ((u.eval n).Dom → ∀ L > L0, 1 ≤ E L) ∧
          (¬ (u.eval n).Dom → ∀ L > L0, E L ≤ 0)  := by
  classical
  obtain ⟨β, hβ, hβε⟩ := exists_rat_btwn
    (show (0 : ℝ) < min ε (1 / 2) from lt_min hε (by norm_num))
  have hβq : (0 : ℚ) < β := by exact_mod_cast hβ
  have hβhalf : (β : ℝ) ≤ 1 / 2 := le_trans hβε.le (min_le_right _ _)
  let α : ℕ → ℝ := fun n => if (u.eval n).Dom then (β : ℝ) else -(β : ℝ)
  have hGdiag : ∀ i j, i ≠ j → switchGuard i j = 0 := by
    intro i j hij
    simp [switchGuard, hij]
  have hGint : ∀ i, ∃ z : ℤ, switchGuard i i = (z : ℂ) := by
    intro i
    unfold switchGuard
    split_ifs
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
  have hF : switchExchange.IsHermitian := by
    change switchExchange.conjTranspose = switchExchange
    ext i j
    simp [Matrix.conjTranspose_apply, switchExchange, mul_comm]
  have hFi : ∀ i j, ∃ a b : ℤ,
      switchExchange i j = (a : ℂ) + (b : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) := by
    intro i j
    refine ⟨switchVector i * switchVector j, 0, ?_⟩
    simp [switchExchange]
  have hZ : (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ).IsHermitian := by
    change (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ).conjTranspose = 0
    simp
  have hZi : ∀ i j : Fin 3 × Fin 3, ∃ z : ℤ,
      (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) i j = (z : ℂ) := by
    intro i j
    exact ⟨0, by simp⟩
  have hP : switchProjector.IsHermitian := by
    change switchProjector.conjTranspose = switchProjector
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply, switchProjector]
  have hPdiag : ∀ i j, i ≠ j → switchProjector i j = 0 := by
    intro i j hij
    simp [switchProjector, hij]
  have hPmul : switchProjector * switchProjector = switchProjector := by
    have hdiag : switchProjector = Matrix.diagonal
        (fun i : Fin 3 => if i ≠ 0 then (1 : ℂ) else 0) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [switchProjector, Matrix.diagonal]
      · simp [switchProjector, Matrix.diagonal, hij]
    rw [hdiag, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    dsimp
    split_ifs <;> simp
  have hα : ∀ n, IsAlgebraic ℚ (α n) ∧ α n ≤ 2 * (β : ℝ) := by
    intro n
    dsimp [α]
    split_ifs
    · exact ⟨isAlgebraic_ratCast ℚ β, by linarith⟩
    · exact ⟨(isAlgebraic_ratCast ℚ β).neg, by linarith⟩
  refine ⟨3, switchGuard, switchExchange, 0, 0, switchGuard, 0,
    switchProjector, β, α, hβq, lt_of_lt_of_le hβε (min_le_left _ _),
    hGdiag, hGint, hF, hFi, hZi, hZi, hGdiag, hGint, hZ, hZi,
    hP, hPdiag, hPmul, hα, ?_⟩
  intro n h1 hrow hcol hh1 hhcol hhrow
  have habs : |α n| ≤ (β : ℝ) := by
    dsimp [α]
    split_ifs <;> simp [abs_of_pos hβ]
  have hc : hcol = switchGuard := by simpa using hhcol
  have hr : hrow = switchGuard + ((β : ℝ) : ℂ) • switchExchange := by
    simpa using hhrow
  rw [hh1, hr, hc]
  obtain ⟨hnorm, hspec⟩ := usg_switch_finite_spectrum (β : ℝ) (α n) hβ hβhalf habs
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / (β : ℝ))
  refine ⟨hnorm, (fun L => α n * (L : ℝ) ^ 2),
    (fun L => switchMagnonSpectrum L (β : ℝ)), max 1 M,
    usg_switch_magnon_density (β : ℝ) hβ, ?_, ?_, ?_⟩
  · intro L hL
    have h2 : 2 ≤ L := by have := le_max_left 1 M; omega
    simpa only [switchHam] using hspec L h2
  · intro hh L hL
    have hML : M < L := lt_of_le_of_lt (le_max_right _ _) hL
    have hL1 : (1 : ℝ) ≤ L := by
      have : 1 ≤ L := by have := le_max_left 1 M; omega
      exact_mod_cast this
    have hlarge : 1 / (β : ℝ) < (L : ℝ) := lt_trans hM (by exact_mod_cast hML)
    have hprod : (1 : ℝ) < (L : ℝ) * β := (div_lt_iff₀ hβ).mp hlarge
    have hsq : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    dsimp [α]
    rw [if_pos hh]
    nlinarith [mul_le_mul_of_nonneg_left hsq hβ.le]
  · intro hh L hL
    dsimp [α]
    rw [if_neg hh]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ.le) (sq_nonneg _)
