-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P26.spectral_permutation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:49:55.158252+00:00
-- url     : https://prove2.me/submissions/868e71c5-5075-47ff-a5dc-27e419d6c499

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26
noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)


open QAlgorithms

lemma g67g_islin {d : ℕ} (a b : Fin d → ℝ) :
    IsLinearMap ℝ (fun S : Matrix (Fin d) (Fin d) ℝ => ∑ j, ∑ i, S j i * (a i * b j)) := by
  constructor
  · intro S T
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  · intro c S
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring

lemma g67g_perm_val {d : ℕ} (a b : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    (∑ j, ∑ i, (σ.permMatrix ℝ) j i * (a i * b j)) = ∑ j, a (σ j) * b j := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

lemma g67g_trace_formula {d : ℕ} (U VA VB : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℝ) :
    ((U * (VA * Matrix.diagonal (fun i => (a i : ℂ)) * VAᴴ) * Uᴴ *
      (VB * Matrix.diagonal (fun i => (b i : ℂ)) * VBᴴ)).trace.re) =
      ∑ j, ∑ i, Complex.normSq ((VBᴴ * U * VA) j i) * (a i * b j) := by
  have h1 : (U * (VA * Matrix.diagonal (fun i => (a i : ℂ)) * VAᴴ) * Uᴴ *
      (VB * Matrix.diagonal (fun i => (b i : ℂ)) * VBᴴ)).trace =
      (Matrix.diagonal (fun i => (a i : ℂ)) * (VBᴴ * U * VA)ᴴ *
        Matrix.diagonal (fun i => (b i : ℂ)) * (VBᴴ * U * VA)).trace := by
    rw [show U * (VA * Matrix.diagonal (fun i => (a i : ℂ)) * VAᴴ) * Uᴴ *
      (VB * Matrix.diagonal (fun i => (b i : ℂ)) * VBᴴ) = (U * VA) *
      (Matrix.diagonal (fun i => (a i : ℂ)) * VAᴴ * Uᴴ * VB * Matrix.diagonal (fun i => (b i : ℂ)) * VBᴴ)
      by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h1]
  generalize VBᴴ * U * VA = W
  have e : ∀ x : ℂ, ∀ p q : ℝ, ((p:ℂ) * star x * (q:ℂ) * x).re = Complex.normSq x * (p * q) := by
    intro x p q
    have : star x * x = (Complex.normSq x : ℂ) := by
      rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [show (p:ℂ) * star x * (q:ℂ) * x = ((p * q : ℝ) : ℂ) * (star x * x) by push_cast; ring, this,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  exact e _ _ _

lemma g67g_ds {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (Matrix.of fun j i => Complex.normSq (W j i)) ∈ doublyStochastic ℝ (Fin d) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun j => ?_, fun i => ?_⟩
  · have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hW) j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Matrix.of_apply, RCLike.star_def]
    rw [Complex.mul_conj, Complex.ofReal_re]
  · have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hW) i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Matrix.of_apply, RCLike.star_def]
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

/-- PDF p.9, Lemma IV.11: permutations depend on both full eigenvalue lists,
chosen before every unitary; PSD operators need not have trace one. -/
theorem solution {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (lambdaA lambdaB : Fin d → ℝ)
    (hEA : HasEigenvalues A lambdaA) (hEB : HasEigenvalues B lambdaB) :
    ∃ piMin piMax : Equiv.Perm (Fin d), ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∑ j, lambdaA (piMin j)*lambdaB j) ≤
        (((U : Matrix (Fin d) (Fin d) ℂ)*A*(U : Matrix (Fin d) (Fin d) ℂ)ᴴ*B).trace.re) ∧
      (((U : Matrix (Fin d) (Fin d) ℂ)*A*(U : Matrix (Fin d) (Fin d) ℂ)ᴴ*B).trace.re) ≤
        ∑ j, lambdaA (piMax j)*lambdaB j := by
  obtain ⟨VA, hVA⟩ := hEA
  obtain ⟨VB, hVB⟩ := hEB
  obtain ⟨piMin, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm (Fin d) => ∑ j, lambdaA (σ j) * lambdaB j) Finset.univ_nonempty
  obtain ⟨piMax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun σ : Equiv.Perm (Fin d) => ∑ j, lambdaA (σ j) * lambdaB j) Finset.univ_nonempty
  refine ⟨piMin, piMax, fun U => ?_⟩
  have hW : (VB : Matrix (Fin d) (Fin d) ℂ)ᴴ * (U : Matrix (Fin d) (Fin d) ℂ) *
      (VA : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    have := (star VB * U * VA).2
    simpa [Matrix.star_eq_conjTranspose] using this
  have hS : _ ∈ (doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ)) := g67g_ds _ hW
  rw [doublyStochastic_eq_convexHull_permMatrix] at hS
  rw [hVA, hVB, g67g_trace_formula]
  have hlin := g67g_islin lambdaA lambdaB
  constructor
  · have hsub := convexHull_min (s := {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)})
      (t := {S | (∑ j, lambdaA (piMin j) * lambdaB j) ≤ ∑ j, ∑ i, S j i * (lambdaA i * lambdaB j)})
      (by rintro _ ⟨σ, rfl⟩; simp only [Set.mem_setOf_eq, g67g_perm_val]; exact hmin σ (Finset.mem_univ _))
      (convex_halfSpace_ge hlin _)
    exact hsub hS
  · have hsub := convexHull_min (s := {σ.permMatrix ℝ | σ : Equiv.Perm (Fin d)})
      (t := {S | (∑ j, ∑ i, S j i * (lambdaA i * lambdaB j)) ≤ ∑ j, lambdaA (piMax j) * lambdaB j})
      (by rintro _ ⟨σ, rfl⟩; simp only [Set.mem_setOf_eq, g67g_perm_val]; exact hmax σ (Finset.mem_univ _))
      (convex_halfSpace_le hlin _)
    exact hsub hS


end
