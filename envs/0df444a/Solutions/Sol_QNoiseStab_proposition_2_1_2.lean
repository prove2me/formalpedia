-- Prove2me | solution 2 for QNoiseStab.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:13.943434+00:00
-- url     : https://prove2.me/submissions/e9f05dfe-8401-401b-b09b-0f952af51e7d

import Mathlib

-- Solutions.Proposition21
section
/-! # Extremal row sums of a nonnegative symmetric matrix -/

namespace QNoiseStab

open Matrix
open scoped MatrixOrder

private theorem submission_proof {N : ℕ} (hN : 0 < N) (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M.IsHermitian) (hnn : ∀ i j, 0 ≤ M i j) :
    let hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
    let r : Fin N → ℝ := fun i => ∑ j, M i j
    let lamMax : ℝ := Finset.univ.sup' hne hM.eigenvalues
    (Finset.univ.inf' hne r ≤ lamMax ∧ lamMax ≤ Finset.univ.sup' hne r) ∧
      ∀ c : ℝ, (∀ i, r i = c) → lamMax = c := by
  intro hne r lamMax
  have hmax : IsGreatest (spectrum ℝ M) lamMax := by
    rw [hM.spectrum_real_eq_range_eigenvalues]
    constructor
    · obtain ⟨i, _, hi⟩ := Finset.univ.exists_mem_eq_sup' hne hM.eigenvalues
      exact ⟨i, hi.symm⟩
    · rintro _ ⟨i, rfl⟩
      exact Finset.le_sup' hM.eigenvalues (Finset.mem_univ i)
  have hl : Finset.univ.inf' hne r ≤ lamMax := by
    have hle : M ≤ algebraMap ℝ (Matrix (Fin N) (Fin N) ℝ) lamMax :=
      le_algebraMap_of_spectrum_le (fun _ hx => hmax.2 hx) hM
    have hquad := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg (1 : Fin N → ℝ)
    rw [star_one, sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec,
      one_dotProduct] at hquad
    by_contra! hlt
    refine (not_lt_of_ge hquad) (Finset.sum_neg (fun i _ => ?_) hne)
    have hi := hlt.trans_le (Finset.inf'_le r (Finset.mem_univ i))
    simpa [r, mulVec, dotProduct, sub_neg] using hi
  have hu : lamMax ≤ Finset.univ.sup' hne r := by
    have heig : Module.End.HasEigenvalue M.toLin' lamMax :=
      .of_mem_spectrum (by simpa using hmax.1)
    obtain ⟨i, hi⟩ := eigenvalue_mem_ball heig
    rw [Metric.mem_closedBall, Real.dist_eq] at hi
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnn i _)] at hi
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)] at hi
    have hrow : lamMax ≤ ∑ j, M i j :=
      (sub_le_sub_iff_right (M i i)).mp ((le_abs_self _).trans hi)
    exact hrow.trans (Finset.le_sup' r (Finset.mem_univ i))
  refine ⟨⟨hl, hu⟩, fun c hc => ?_⟩
  exact le_antisymm (hu.trans (Finset.sup'_le _ _ fun i _ => (hc i).le))
    ((Finset.le_inf' _ _ fun i _ => (hc i).ge).trans hl)

end QNoiseStab
end

section
open QNoiseStab

set_option linter.unusedVariables false in
theorem solution :
    ∀ {N : ℕ} (hN : 0 < N) (M : Matrix (Fin N) (Fin N) ℝ)
        (hM : M.IsHermitian) (hnn : ∀ i j, 0 ≤ M i j),
      let hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      let r : Fin N → ℝ := fun i => ∑ j, M i j
      let lamMax : ℝ := Finset.univ.sup' hne hM.eigenvalues
      (Finset.univ.inf' hne r ≤ lamMax ∧ lamMax ≤ Finset.univ.sup' hne r) ∧
        ∀ c : ℝ, (∀ i, r i = c) → lamMax = c :=
  @QNoiseStab.submission_proof

end
