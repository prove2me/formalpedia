-- Prove2me | solution 1 for UndecidableSpectralGap.usg_diverging_gs_energy
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-14T11:59:58.265398+00:00
-- url     : https://prove2.me/submissions/9885729c-b837-4ffb-a09a-e78cf64bf1a2

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false
open scoped ComplexOrder

open UndecidableSpectralGap

namespace UsgDivergingGsEnergyDisproof

/-- On a `1 × 1` lattice there are no horizontal edges. -/
theorem rowEdges_one_eq_empty : rowEdges 1 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  rintro e he
  simp only [rowEdges, Finset.mem_filter] at he
  have h1 : ((e.2.2 : Fin 1) : ℕ) < 1 := e.2.2.isLt
  omega

/-- On a `1 × 1` lattice there are no vertical edges. -/
theorem colEdges_one_eq_empty : colEdges 1 = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  rintro e he
  simp only [colEdges, Finset.mem_filter] at he
  have h1 : ((e.2.1 : Fin 1) : ℕ) < 1 := e.2.1.isLt
  omega

/-- The `1 × 1` lattice has a single site, so its configurations are just the local levels. -/
def siteEquiv (d : ℕ) : Config 1 d ≃ Fin d where
  toFun c := c (0, 0)
  invFun x := fun _ => x
  left_inv c := by
    funext s
    have hs : s = ((0 : Fin 1), (0 : Fin 1)) := Subsingleton.elim _ _
    rw [hs]
  right_inv _ := rfl

/-- On the `1 × 1` lattice the Hamiltonian is just the on-site term `h₁`, written in the
basis of configurations: there are no nearest-neighbour pairs and exactly one site. -/
theorem latticeHam_one (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    latticeHam 1 d h1 hrow hcol = h1.submatrix (siteEquiv d) (siteEquiv d) := by
  funext c c'
  have huniv : (Finset.univ : Finset (Site 1)) = {((0 : Fin 1), (0 : Fin 1))} := by
    ext p; simp [Subsingleton.elim p ((0 : Fin 1), (0 : Fin 1))]
  simp [latticeHam, rowEdges_one_eq_empty, colEdges_one_eq_empty, huniv, embedOne,
    Matrix.submatrix, siteEquiv]

/-- Reindexing a matrix along a bijection of index types does not change its spectrum. -/
theorem specReal_submatrix (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ) :
    specReal (h1.submatrix (siteEquiv d) (siteEquiv d)) = specReal h1 := by
  have h : h1.submatrix (siteEquiv d) (siteEquiv d)
      = Matrix.reindexAlgEquiv ℂ ℂ (siteEquiv d).symm h1 := by
    simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  ext μ
  simp only [specReal, Set.mem_ofPred_eq, h]
  rw [AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℂ ℂ (siteEquiv d).symm) h1]

/-- Every real point of the spectrum of a matrix is bounded in absolute value by its
operator norm. -/
theorem abs_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {μ : ℝ}
    (hμ : μ ∈ specReal A) : |μ| ≤ opNorm A := by
  have hmem : (μ : ℂ) ∈ spectrum ℂ A := hμ
  rcases isEmpty_or_nonempty n with _ | _
  · rw [spectrum.mem_iff] at hmem
    exact absurd (isUnit_of_subsingleton _) hmem
  · have h2 : (μ : ℂ) ∈ spectrum ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) A) := by
      rw [AlgEquiv.spectrum_eq (Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix n n ℂ ≃⋆ₐ[ℂ] _)]
      exact hmem
    simpa [opNorm] using spectrum.norm_le_norm_of_mem h2

/-- **The key bound.** If the on-site term has operator norm at most `1/2`, then the ground
state energy on the `1 × 1` lattice is at least `-1/2`, whatever the interactions are. -/
theorem neg_half_le_gsEnergy_one (d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hn : opNorm h1 ≤ 1 / 2) :
    -(1 / 2 : ℝ) ≤ gsEnergy (latticeHam 1 d h1 hrow hcol) := by
  rw [latticeHam_one, gsEnergy, specReal_submatrix]
  refine Real.le_sInf (fun x hx => ?_) (by norm_num)
  have habs : |x| ≤ opNorm h1 := abs_le_opNorm h1 hx
  have := abs_le.mp (habs.trans hn)
  linarith [this.1]

/-- **Disproof of Proposition 53 as stated.** Take a code `u` whose evaluation is nowhere
defined and `β = 2`. The non-halting clause would force
`λ₀(H^{Λ(1)}) ≤ -β/2 = -1` on the `1 × 1` lattice. But `Λ(1)` has a single site and no
nearest-neighbour pair, so `H^{Λ(1)}` is (a reindexing of) the on-site term `h₁`, whose
operator norm is at most `1/2`; hence `λ₀(H^{Λ(1)}) ≥ -1/2`. -/
theorem disproof : ¬ (∀ (u : Nat.Partrec.Code) (β : ℚ) (hβ : 0 < β),
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (δ₁ δ₂ : ℕ → ℝ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j)) ∧
        0 < δ₁ n ∧ 0 < δ₂ n) ∧
      ∀ n : ℕ,
        (¬ (u.eval n).Dom → ∀ L : ℕ, 0 < L →
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ -(L : ℝ) * (β : ℝ) / 2) ∧
        ((u.eval n).Dom → ∃ L0 : ℕ, ∀ L ≥ L0,
          (L : ℝ) ^ 2 * δ₂ n - (L : ℝ) * δ₁ n
            ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)))) := by
  intro h
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp Nat.Partrec.none
  obtain ⟨d, h1, hrow, hcol, δ₁, δ₂, hprops, hmain⟩ := h u 2 (by norm_num)
  have hnd : ¬ (u.eval 0).Dom := by rw [hu]; simp
  have hle := (hmain 0).1 hnd 1 Nat.one_pos
  have hnorm : opNorm (h1 0) ≤ 1 / 2 := (hprops 0).2.2.2.1
  have hge := neg_half_le_gsEnergy_one d (h1 0) (hrow 0) (hcol 0) hnorm
  rw [show ((-((1 : ℕ) : ℝ) * ((2 : ℚ) : ℝ) / 2)) = -1 by norm_num] at hle
  linarith

end UsgDivergingGsEnergyDisproof

theorem solution : ¬ (∀ (u : Nat.Partrec.Code) (β : ℚ) (hβ : 0 < β),
    ∃ (d : ℕ) (h1 : ℕ → Matrix (Fin d) (Fin d) ℂ)
      (hrow hcol : ℕ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (δ₁ δ₂ : ℕ → ℝ),
      (∀ n : ℕ,
        (h1 n).IsHermitian ∧ (hrow n).IsHermitian ∧ (hcol n).IsHermitian ∧
        opNorm (h1 n) ≤ 1 / 2 ∧ opNorm (hrow n) ≤ 1 / 2 ∧ opNorm (hcol n) ≤ 1 / 2 ∧
        (∀ i j, IsAlgebraic ℚ ((h1 n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hrow n) i j)) ∧
        (∀ i j, IsAlgebraic ℚ ((hcol n) i j)) ∧
        0 < δ₁ n ∧ 0 < δ₂ n) ∧
      ∀ n : ℕ,
        (¬ (u.eval n).Dom → ∀ L : ℕ, 0 < L →
          gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)) ≤ -(L : ℝ) * (β : ℝ) / 2) ∧
        ((u.eval n).Dom → ∃ L0 : ℕ, ∀ L ≥ L0,
          (L : ℝ) ^ 2 * δ₂ n - (L : ℝ) * δ₁ n
            ≤ gsEnergy (latticeHam L d (h1 n) (hrow n) (hcol n)))) :=
  UsgDivergingGsEnergyDisproof.disproof
