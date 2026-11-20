-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.totally_nonsingular_exists
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:58:33.768241+00:00
-- url     : https://prove2.me/submissions/f77d55e1-0c43-4af8-bafa-3fe4bd729fe8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

theorem AuxTN_minor_ne {n k : ℕ} (rows cols : Fin k ↪ Fin n) :
    ((Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).submatrix
      rows cols).det ≠ 0 := by
  classical
  intro h
  set f : Fin n × Fin n → ℂ := fun p => if ∃ a, rows a = p.1 ∧ cols a = p.2 then 1 else 0
  have h2 := congrArg (MvPolynomial.eval f) h
  rw [RingHom.map_det, map_zero] at h2
  have hM : (MvPolynomial.eval f).mapMatrix
      ((Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).submatrix
        rows cols) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.of_apply,
      MvPolynomial.eval_X, f, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg, if_neg hab]
      rintro ⟨c, hc1, hc2⟩
      exact hab ((rows.injective hc1).symm.trans (cols.injective hc2))
  rw [hM, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem _root_.solution (n : ℕ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, TotallyNonsingular M := by
  classical
  set X : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
    Matrix.of fun i j => MvPolynomial.X (i, j) with hX
  let ι := Σ k : Fin (n + 1), (Fin k ↪ Fin n) × (Fin k ↪ Fin n)
  let p : ι → MvPolynomial (Fin n × Fin n) ℂ := fun s => (X.submatrix s.2.1 s.2.2).det
  have hp : ∀ s, p s ≠ 0 := fun s => AuxTN_minor_ne s.2.1 s.2.2
  have hP : ∏ s, p s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hp s
  obtain ⟨f, hf⟩ : ∃ f : Fin n × Fin n → ℂ, MvPolynomial.eval f (∏ s, p s) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP
    exact MvPolynomial.funext fun x => by simpa using hcon x
  refine ⟨Matrix.of fun i j => f (i, j), fun k rows cols => ?_⟩
  have hk : k < n + 1 := by
    have := Fintype.card_le_of_embedding rows
    simp at this; omega
  have hne : MvPolynomial.eval f (p ⟨⟨k, hk⟩, rows, cols⟩) ≠ 0 := by
    rw [map_prod] at hf
    exact (Finset.prod_ne_zero_iff.mp hf) _ (Finset.mem_univ _)
  simp only [p, RingHom.map_det] at hne
  convert hne using 2
  ext a b
  simp [X]

end QAlgorithms.Papers.Independent.Intake100.P43

end
