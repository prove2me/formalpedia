-- Prove2me | solution 1 for UndecidableSpectralGap.usg_spectral_gap_main
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T20:18:56.77018+00:00
-- url     : https://prove2.me/submissions/63d6e316-10b2-443b-b00d-4fbb3362fce4

import Theorems.Thm_UndecidableSpectralGap_usg_sector_spectral_certificate

set_option autoImplicit false
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
        -- (ii) if `UTM` halts on input `n`, the family is gapped with gap at least 1
        ((u.eval n).Dom → GappedWithGap d h1 hrow hcol 1) ∧
        -- (iii) if `UTM` does not halt on input `n`, the family is gapless
        (¬ (u.eval n).Dom → Gapless d h1 hrow hcol)  := by
  classical
  obtain ⟨d, A, A', B, C, D, D', Pi, β, α, hβ, hβε, hA, hAi, hA', hA'i,
    hB, hC, hD, hDi, hD', hD'i, hPi, hPid, hPis, hα, hmodel⟩ :=
    usg_sector_spectral_certificate u ε hε
  refine ⟨d, A, A', B, C, D, D', Pi, β, α, hβ, hβε, hA, hAi, hA', hA'i,
    hB, hC, hD, hDi, hD', hD'i, hPi, hPid, hPis, hα, ?_⟩
  intro n h1 hrow hcol hh1 hhcol hhrow
  obtain ⟨hnorm, E, S, L0, hdense, hspectral, hhalt, hnonhalt⟩ :=
    hmodel n h1 hrow hcol hh1 hhcol hhrow
  have hground : ∀ L > L0,
      gsEnergy (latticeHam L d h1 hrow hcol) = min 0 (E L) := by
    intro L hL
    obtain ⟨⟨hz, he, hlower⟩, _, _⟩ := hspectral L hL
    have hmem : min 0 (E L) ∈ specReal (latticeHam L d h1 hrow hcol) := by
      by_cases h : 0 ≤ E L
      · simpa [min_eq_left h] using hz
      · simpa [min_eq_right (le_of_not_ge h)] using he
    unfold gsEnergy
    exact le_antisymm (csInf_le ⟨min 0 (E L), hlower⟩ hmem)
      (le_csInf ⟨0, hz⟩ hlower)
  refine ⟨hnorm, ?_, ?_⟩
  · intro hhalts
    refine ⟨by norm_num, L0, ?_⟩
    intro L hL
    have he := hhalt hhalts L hL
    have hg : gsEnergy (latticeHam L d h1 hrow hcol) = 0 := by
      rw [hground L hL, min_eq_left (by linarith)]
    obtain ⟨hmult, hgap⟩ := (hspectral L hL).2.2 he
    constructor
    · change eigMultiplicity (latticeHam L d h1 hrow hcol)
        (gsEnergy (latticeHam L d h1 hrow hcol)) = 1
      simpa only [hg] using hmult
    · intro μ hμ hne
      rw [hg] at hne ⊢
      simpa only [zero_add] using hgap μ hμ hne
  · intro hnot
    refine ⟨1, by norm_num, ?_⟩
    intro δ hδ
    obtain ⟨N, hN⟩ := hdense δ hδ
    refine ⟨max L0 N, ?_⟩
    intro L hL x hx
    have hL0 : L0 < L := lt_of_le_of_lt (le_max_left _ _) hL
    have hLN : N < L := lt_of_le_of_lt (le_max_right _ _) hL
    have hg : gsEnergy (latticeHam L d h1 hrow hcol) = E L := by
      rw [hground L hL0, min_eq_right (hnonhalt hnot L hL0)]
    rw [hg] at hx
    have hx' : x - E L ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    obtain ⟨s, hs, hdist⟩ := hN L hLN (x - E L) hx'
    refine ⟨E L + s, (hspectral L hL0).2.1 s hs, ?_⟩
    have heq : x - (E L + s) = x - E L - s := by ring
    simpa only [heq] using hdist
