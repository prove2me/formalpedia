-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P07.nondegenerate_phaseTest
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:46.88544+00:00
-- url     : https://prove2.me/submissions/7109df24-688c-465a-8f47-fb5c8db378e6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7_trR_conj (U V : Local) (hV : Vᴴ * V = 1) (X : Joint) :
    traceRight (Matrix.kronecker U V * X * (Matrix.kronecker U V)ᴴ) = U * traceRight X * Uᴴ := by
  have hV' : ∀ r2 s2 : Fin 3, ∑ h, V h r2 * star (V h s2) = if s2 = r2 then 1 else 0 := by
    intro r2 s2
    have := congrFun (congrFun hV s2) r2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  ext a b
  simp only [traceRight, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, star_mul', Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s1 _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, s2]; rw [Finset.sum_comm]
  conv_lhs => enter [2, s2, 2, r1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, r1]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  refine Finset.sum_congr rfl fun r2 _ => ?_
  have : ∀ s2, ∑ h, U a r1 * V h r2 * X (r1, r2) (s1, s2) * (star (U b s1) * star (V h s2)) =
      (U a r1 * X (r1, r2) (s1, s2) * star (U b s1)) * ∑ h, V h r2 * star (V h s2) := by
    intro s2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [this, hV', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma X7_trL_conj (U V : Local) (hU : Uᴴ * U = 1) (X : Joint) :
    traceLeft (Matrix.kronecker U V * X * (Matrix.kronecker U V)ᴴ) = V * traceLeft X * Vᴴ := by
  have hU' : ∀ r1 s1 : Fin 3, ∑ h, U h r1 * star (U h s1) = if s1 = r1 then 1 else 0 := by
    intro r1 s1
    have := congrFun (congrFun hU s1) r1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    rw [← this]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  ext a b
  simp only [traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, star_mul', Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, h]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s2 _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, s1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, s1, 2, r1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, s1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, r2]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r2 _ => ?_
  refine Finset.sum_congr rfl fun r1 _ => ?_
  have : ∀ s1, ∑ h, U h r1 * V a r2 * X (r1, r2) (s1, s2) * (star (U h s1) * star (V b s2)) =
      (V a r2 * X (r1, r2) (s1, s2) * star (V b s2)) * ∑ h, U h r1 * star (U h s1) := by
    intro s1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [this, hU', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

def X7_ph (α : Fin 3 → ℝ) : Local := Matrix.diagonal fun i => Complex.exp (Complex.I * (α i : ℂ))

lemma X7_star_exp (t : ℝ) : star (Complex.exp (Complex.I * (t : ℂ))) =
    Complex.exp (-(Complex.I * (t : ℂ))) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

lemma X7_diag_conj (α β : Fin 3 → ℝ) (X : Joint) (i j k l : Fin 3) :
    (Matrix.kronecker (X7_ph α) (X7_ph β) * X * (Matrix.kronecker (X7_ph α) (X7_ph β))ᴴ) (i, j) (k, l) =
      Complex.exp (Complex.I * ((α i - α k + β j - β l : ℝ) : ℂ)) * X (i, j) (k, l) := by
  have hk : Matrix.kronecker (X7_ph α) (X7_ph β) = Matrix.diagonal fun mn : Fin 3 × Fin 3 =>
      Complex.exp (Complex.I * (α mn.1 : ℂ)) * Complex.exp (Complex.I * (β mn.2 : ℂ)) := by
    unfold X7_ph
    exact Matrix.diagonal_kronecker_diagonal _ _
  rw [hk, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, star_mul', X7_star_exp]
  rw [show Complex.I * ((α i - α k + β j - β l : ℝ) : ℂ) =
      Complex.I * (α i : ℂ) + Complex.I * (β j : ℂ) + -(Complex.I * (α k : ℂ)) +
        -(Complex.I * (β l : ℂ)) by push_cast; ring]
  simp only [Complex.exp_add]
  ring

lemma X7_ph_unitary (α : Fin 3 → ℝ) : X7_ph α ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  unfold X7_ph
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply, X7_star_exp, ← Complex.exp_add]
  simp

lemma X7_diag_of_comm (U : Local) (hU : Uᴴ * U = 1) (d : Fin 3 → ℝ)
    (hd : Function.Injective d) (D : Local) (hDd : D = Matrix.diagonal (fun i => (d i : ℂ)))
    (h' : D = U * D * Uᴴ) :
    U = X7_ph (fun i => Complex.arg (U i i)) := by
  have h : U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ = Matrix.diagonal (fun i => (d i : ℂ)) := by
    rw [← hDd]; exact h'.symm
  have hc : U * Matrix.diagonal (fun i => (d i : ℂ)) = Matrix.diagonal (fun i => (d i : ℂ)) * U := by
    calc U * Matrix.diagonal (fun i => (d i : ℂ))
        = U * Matrix.diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by rw [hU, Matrix.mul_one]
      _ = (U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) * U := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hoff : ∀ i k, i ≠ k → U i k = 0 := by
    intro i k hik
    have := congrFun (congrFun hc i) k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have hne : (d k : ℂ) - d i ≠ 0 := by
      rw [sub_ne_zero]
      intro h'
      exact hik (hd (Complex.ofReal_injective h')).symm
    have : ((d k : ℂ) - d i) * U i k = 0 := by linear_combination this
    exact (mul_eq_zero.mp this).resolve_left hne
  have hnorm : ∀ i, ‖U i i‖ = 1 := by
    intro i
    have := congrFun (congrFun hU i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    rw [Finset.sum_eq_single i (fun h _ hhi => by rw [hoff h i hhi, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)] at this
    have h2 : (Complex.normSq (U i i) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def]; exact this
    have h3 : Complex.normSq (U i i) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h3
  ext i k
  unfold X7_ph
  by_cases hik : i = k
  · subst hik
    rw [Matrix.diagonal_apply_eq]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (U i i)]
    rw [hnorm i, Complex.ofReal_one, one_mul, mul_comm]
  · rw [Matrix.diagonal_apply_ne _ hik, hoff i k hik]

lemma X7_unit_facts (U : Matrix.unitaryGroup (Fin 3) ℂ) :
    (U : Local)ᴴ * U = 1 ∧ (U : Local) * (U : Local)ᴴ = 1 := by
  refine ⟨?_, ?_⟩
  · have := (Matrix.mem_unitaryGroup_iff').mp U.2; simpa [Matrix.star_eq_conjTranspose] using this
  · have := (Matrix.mem_unitaryGroup_iff).mp U.2; simpa [Matrix.star_eq_conjTranspose] using this

lemma X7_main (eta zeta : Joint)
    (hA : traceRight eta = Matrix.diagonal (fun i => (ascEigenvalues (traceRight eta) i : ℂ)))
    (hB : traceLeft eta = Matrix.diagonal (fun i => (ascEigenvalues (traceLeft eta) i : ℂ)))
    (hZA : traceRight zeta = traceRight eta) (hZB : traceLeft zeta = traceLeft eta)
    (hsimpleA : Function.Injective (ascEigenvalues (traceRight eta)))
    (hsimpleB : Function.Injective (ascEigenvalues (traceLeft eta))) :
    LU eta zeta ↔ PhaseRelated eta zeta := by
  constructor
  · rintro ⟨U, V, hz⟩
    obtain ⟨hU1, -⟩ := X7_unit_facts U
    obtain ⟨hV1, -⟩ := X7_unit_facts V
    have hR := X7_trR_conj U V hV1 eta
    have hL := X7_trL_conj U V hU1 eta
    rw [← hz, hZA] at hR
    rw [← hz, hZB] at hL
    have hUd := X7_diag_of_comm U hU1 (fun i => ascEigenvalues (traceRight eta) i) hsimpleA _ hA hR
    have hVd := X7_diag_of_comm V hV1 (fun i => ascEigenvalues (traceLeft eta) i) hsimpleB _ hB hL
    obtain ⟨α, hα⟩ : ∃ α, (U : Local) = X7_ph α := ⟨_, hUd⟩
    obtain ⟨β, hβ⟩ : ∃ β, (V : Local) = X7_ph β := ⟨_, hVd⟩
    refine ⟨α, β, fun i j k l => ?_⟩
    rw [hz, hα, hβ, X7_diag_conj]
  · rintro ⟨α, β, h⟩
    refine ⟨⟨X7_ph α, X7_ph_unitary α⟩, ⟨X7_ph β, X7_ph_unitary β⟩, ?_⟩
    ext ⟨i, j⟩ ⟨k, l⟩
    change zeta (i, j) (k, l) = (Matrix.kronecker (X7_ph α) (X7_ph β) * eta *
      (Matrix.kronecker (X7_ph α) (X7_ph β))ᴴ) (i, j) (k, l)
    rw [h, X7_diag_conj]

end QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P07 in
theorem solution (eta zeta : Joint)
    (he : IsDensityMatrix eta) (hz : IsDensityMatrix zeta)
    (hA : traceRight eta = Matrix.diagonal (fun i => (ascEigenvalues (traceRight eta) i : ℂ)))
    (hB : traceLeft eta = Matrix.diagonal (fun i => (ascEigenvalues (traceLeft eta) i : ℂ)))
    (hZA : traceRight zeta = traceRight eta) (hZB : traceLeft zeta = traceLeft eta)
    (hsimpleA : Function.Injective (ascEigenvalues (traceRight eta)))
    (hsimpleB : Function.Injective (ascEigenvalues (traceLeft eta))) :
    LU eta zeta ↔ PhaseRelated eta zeta :=
  X7_main eta zeta hA hB hZA hZB hsimpleA hsimpleB

end
