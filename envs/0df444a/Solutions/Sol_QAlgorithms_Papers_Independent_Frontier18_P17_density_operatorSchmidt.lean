-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.density_operatorSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:14:11.465669+00:00
-- url     : https://prove2.me/submissions/18c37afb-7398-43b9-80ae-c92888033932

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

open QAlgorithms.Papers.Independent.Frontier18.P17

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- rows r_a = u_a^* A -/
lemma g52_rows_gram (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (a b : I) :
    (star ⇑(hH.eigenvectorBasis a) ᵥ* A) ⬝ᵥ star (star ⇑(hH.eigenvectorBasis b) ᵥ* A) =
      (hH.eigenvalues b : ℂ) * (star ⇑(hH.eigenvectorBasis a) ⬝ᵥ ⇑(hH.eigenvectorBasis b)) := by
  rw [Matrix.star_vecMul, star_star, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    hH.mulVec_eigenvectorBasis, dotProduct_smul, Complex.real_smul]

lemma g52_ortho (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (a b : I) :
    star ⇑(hH.eigenvectorBasis a) ⬝ᵥ ⇑(hH.eigenvectorBasis b) = if a = b then 1 else 0 := by
  have h := hH.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at h
  have := h a b
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at this
  exact this

lemma g52_delta (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (i i' : I) :
    ∑ a, (hH.eigenvectorBasis a) i * star ((hH.eigenvectorBasis a) i') = if i = i' then 1 else 0 := by
  have hU' : (hH.eigenvectorUnitary : Matrix I I ℂ) * star (hH.eigenvectorUnitary : Matrix I I ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (hH.eigenvectorUnitary).2
  have := congrFun (congrFun hU' i) i'
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    Matrix.one_apply] using this

lemma g52_decomp (A : Matrix I J ℂ) (hH : (A * Aᴴ).IsHermitian) (i : I) (j : J) :
    A i j = ∑ a, (hH.eigenvectorBasis a) i * (star ⇑(hH.eigenvectorBasis a) ᵥ* A) j := by
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, g52_delta A hH]
  simp

theorem g52_thinSVD (A : Matrix I J ℂ) :
    ∃ (k : ℕ) (s : Fin k → ℝ) (u : Fin k → EuclideanSpace ℂ I) (v : Fin k → EuclideanSpace ℂ J),
      k ≤ min (Fintype.card I) (Fintype.card J) ∧ ThinSVD A s u v := by
  have hP := Matrix.posSemidef_self_mul_conjTranspose A
  set hH := hP.isHermitian with hHdef
  set μ := hH.eigenvalues with hμ
  have hμ0 : ∀ a, 0 ≤ μ a := fun a => hP.eigenvalues_nonneg a
  let r : I → J → ℂ := fun a => star ⇑(hH.eigenvectorBasis a) ᵥ* A
  have hgram : ∀ a b, r a ⬝ᵥ star (r b) = (μ b : ℂ) * (if a = b then 1 else 0) := by
    intro a b; rw [g52_rows_gram A hH a b, g52_ortho A hH a b]
  have hr0 : ∀ a, μ a = 0 → r a = 0 := by
    intro a ha
    have := hgram a a
    rw [ha] at this; simp only [Complex.ofReal_zero, zero_mul] at this
    rw [dotProduct_comm] at this
    exact dotProduct_star_self_eq_zero.mp this
  let S := {a : I // μ a ≠ 0}
  let e := Fintype.equivFin S
  have hpos : ∀ x : S, 0 < μ x.1 := fun x => lt_of_le_of_ne (hμ0 x.1) (Ne.symm x.2)
  let c : S → ℝ := fun x => Real.sqrt (μ x.1)
  have hc : ∀ x, 0 < c x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hcc : ∀ x, c x * c x = μ x.1 := fun x => Real.mul_self_sqrt (hμ0 x.1)
  let u : Fin (Fintype.card S) → EuclideanSpace ℂ I := fun i => hH.eigenvectorBasis (e.symm i).1
  let v : Fin (Fintype.card S) → EuclideanSpace ℂ J := fun i =>
    WithLp.toLp 2 (((c (e.symm i))⁻¹ : ℂ) • star (r (e.symm i).1))
  have hu : Orthonormal ℂ u :=
    hH.eigenvectorBasis.orthonormal.comp _ (fun i j h => e.symm.injective (Subtype.ext h))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [v, WithLp.ofLp_toLp, star_smul, star_star, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [dotProduct_comm, hgram]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, mul_one]
      have h1 := hcc (e.symm i)
      have h2 : (c (e.symm i) : ℂ) ≠ 0 := by exact_mod_cast (hc _).ne'
      rw [← h1]; push_cast
      simp [Complex.star_def, Complex.conj_ofReal]
      field_simp
    · have : (e.symm i).1 ≠ (e.symm j).1 := fun h => hij (e.symm.injective (Subtype.ext h))
      simp [this, hij]
  refine ⟨Fintype.card S, fun i => c (e.symm i), u, v, ?_, hu, hv, fun i => hc _, ?_⟩
  · refine le_min (Fintype.card_subtype_le _) ?_
    have := hv.linearIndependent.fintype_card_le_finrank
    simpa [finrank_euclideanSpace] using this
  · ext a b
    rw [g52_decomp A hH a b, Finset.sum_apply, Finset.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, u, v, WithLp.ofLp_toLp, Pi.smul_apply, Pi.star_apply,
      star_star, smul_eq_mul]
    rw [Equiv.sum_comp e.symm (fun x : S => (c x : ℂ) * ((hH.eigenvectorBasis x.1) a *
      (starRingEnd ℂ) (((c x)⁻¹ : ℂ) * star (r x.1 b))))]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun a => μ a ≠ 0)]
    have hz : ∑ x : {a : I // ¬ μ a ≠ 0}, (hH.eigenvectorBasis x.1) a * r x.1 b = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hr0 x.1 (not_not.mp x.2)]; simp
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h2 : (c x : ℂ) ≠ 0 := by exact_mod_cast (hc x).ne'
    simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.star_def, RingHomCompTriple.comp_apply,
      RingHom.id_apply]
    show _ = (c x : ℂ) * ((hH.eigenvectorBasis x.1) a * (((c x : ℂ))⁻¹ * r x.1 b))
    field_simp
    rfl

end

lemma g52_oc {m n : ℕ} (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (a b) :
    operatorCoefficients rho a b = star (rho (a.1, b.1) (a.2, b.2)) := by
  unfold operatorCoefficients hs
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [res, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, Matrix.kroneckerMap_apply,
    Matrix.kronecker, Matrix.single_apply]
  rw [Finset.sum_eq_single ((a.1, b.1), (a.2, b.2))]
  · simp
  · rintro ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ _ hne
    by_cases h1 : a.1 = p1 <;> by_cases h2 : a.2 = q1 <;> by_cases h3 : b.1 = p2 <;>
      by_cases h4 : b.2 = q2 <;> simp [h1, h2, h3, h4] at hne ⊢
  · simp

open QAlgorithms in
theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (rho : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) :
    ∃ (k : ℕ) (s : Fin k → ℝ)
      (u : Fin k → EuclideanSpace ℂ (Fin m × Fin m))
      (v : Fin k → EuclideanSpace ℂ (Fin n × Fin n)),
      k ≤ min (m*m) (n*n) ∧ ThinSVD (operatorCoefficients rho) s u v ∧
      rho = ∑ i, (s i : ℂ) • Matrix.kronecker
        (unres (WithLp.toLp 2 (fun a => conj (u i a)))) (unres (v i)) := by
  obtain ⟨k, s, u, v, hk, hsvd⟩ := g52_thinSVD (operatorCoefficients rho)
  refine ⟨k, s, u, v, by simpa using hk, hsvd, ?_⟩
  ext ⟨a, b⟩ ⟨a', b'⟩
  have h := congrFun (congrFun hsvd.2.2.2 (a, a')) (b, b')
  rw [g52_oc] at h
  have h' := congrArg star h
  rw [star_star] at h'
  rw [h']
  simp only [Finset.sum_apply, Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    star_sum, star_mul', Matrix.kronecker, Matrix.kroneckerMap_apply, unres, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def, Complex.conj_ofReal]
