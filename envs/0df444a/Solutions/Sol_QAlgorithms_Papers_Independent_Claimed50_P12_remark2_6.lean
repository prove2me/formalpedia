-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P12.remark2_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T10:03:13.246732+00:00
-- url     : https://prove2.me/submissions/916c1109-4cf1-4940-b690-4f933eb99acd

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12
noncomputable section
open Filter MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open QAlgorithms.Papers.Independent.Claimed50.P12
open QAlgorithms.Papers.Independent.Information100.P32 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)
open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)
open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)
open Matrix

lemma g68m_mp_mul {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (n : ℕ) :
    matrixPower (A * B) n = matrixPower A n * matrixPower B n := by
  ext x y
  simp only [matrixPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma g68m_mp_star {I : Type*} [Fintype I] (A : Matrix I I ℂ) (n : ℕ) :
    matrixPower (star A) n = star (matrixPower A n) := by
  ext x y
  simp only [matrixPower, Matrix.star_apply, star_prod]

lemma g68m_mp_diag {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℂ) (n : ℕ)
    [DecidableEq (Fin n → I)] :
    matrixPower (diagonal d) n = diagonal (fun x : Fin n → I => ∏ i, d (x i)) := by
  ext x y
  simp only [matrixPower, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h; push Not at h; exact hxy (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma g68m_mp_one {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) [DecidableEq (Fin n → I)] :
    matrixPower (1 : Matrix I I ℂ) n = 1 := by
  rw [← diagonal_one, g68m_mp_diag]; simp

/-- eigenvalues of a unitarily diagonalized Hermitian matrix are diagonal entries -/
lemma g68m_eig_mem {J : Type*} [Fintype J] [DecidableEq J] (A W : Matrix J J ℂ) (δ : J → ℂ)
    (hW : star W * W = 1) (hA : A = W * diagonal δ * star W) (hH : A.IsHermitian) (j : J) :
    ∃ x, ((hH.eigenvalues j : ℝ) : ℂ) = δ x := by
  set v := ⇑(hH.eigenvectorBasis j)
  have hv : A *ᵥ v = (hH.eigenvalues j : ℂ) • v := by
    rw [hH.mulVec_eigenvectorBasis j]
    ext k; simp [v, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hW' : W * star W = 1 := mul_eq_one_comm.mp hW
  set w := star W *ᵥ v
  have hvne : v ≠ 0 := by
    intro h
    have := (hH.eigenvectorBasis).orthonormal.1 j
    have h2 : hH.eigenvectorBasis j = 0 := by
      ext k; exact congrFun h k
    rw [h2] at this; simp at this
  have hwne : w ≠ 0 := by
    intro h
    apply hvne
    have : W *ᵥ w = v := by simp [w, Matrix.mulVec_mulVec, hW']
    rw [← this, h, Matrix.mulVec_zero]
  have hdw : diagonal δ *ᵥ w = (hH.eigenvalues j : ℂ) • w := by
    have : star W * A = diagonal δ * star W := by
      simp only [hA, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    simp only [w]
    rw [Matrix.mulVec_mulVec, ← this, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ 0 := by
    by_contra h; push Not at h; exact hwne (funext h)
  refine ⟨x, ?_⟩
  have := congrFun hdw x
  simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  exact (mul_right_cancel₀ hx this).symm


lemma g68m_count {I : Type*} [Fintype I] [DecidableEq I] (μ : I → ℝ) (n : ℕ) (hn : 0 < n) :
    (Finset.univ.image (fun x : Fin n → I => ∏ i, μ (x i))).card ≤
      (n + 1) ^ (Fintype.card {i // μ i ≠ 0}) := by
  classical
  set g : (Fin n → I) → ℝ := fun x => ∏ i, μ (x i) with hg
  let cnt : (Fin n → I) → I → ℕ := fun x j => (Finset.univ.filter (fun i => x i = j)).card
  have hcnt_le : ∀ x j, cnt x j ≤ n := by
    intro x j
    calc cnt x j ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by simp
  let φ : (Fin n → I) → Option ({i // μ i ≠ 0} → Fin (n + 1)) := fun x =>
    if ∀ i, μ (x i) ≠ 0 then some (fun j => ⟨cnt x j.1, Nat.lt_succ_of_le (hcnt_le x j.1)⟩)
    else none
  have hprod : ∀ x, g x = ∏ j, μ j ^ cnt x j := by
    intro x
    show ∏ i, μ (x i) = _
    rw [← Finset.prod_fiberwise Finset.univ x (fun i => μ (x i))]
    apply Finset.prod_congr rfl
    intro j _
    rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.prod_const]
  have hzero : ∀ x, (∀ i, μ (x i) ≠ 0) → ∀ j, μ j = 0 → cnt x j = 0 := by
    intro x hx j hj
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi; exact hx i (hi ▸ hj)
  have hφ : ∀ x y, φ x = φ y → g x = g y := by
    intro x y hxy
    by_cases hx : ∀ i, μ (x i) ≠ 0 <;> by_cases hy : ∀ i, μ (y i) ≠ 0
    · simp only [φ, if_pos hx, if_pos hy, Option.some.injEq] at hxy
      rw [hprod, hprod]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : μ j = 0
      · rw [hzero x hx j hj, hzero y hy j hj]
      · have := congrFun hxy ⟨j, hj⟩
        simp only [Fin.mk.injEq] at this
        rw [this]
    · simp [φ, if_pos hx, if_neg hy] at hxy
    · simp [φ, if_neg hx, if_pos hy] at hxy
    · push Not at hx hy
      obtain ⟨i, hi⟩ := hx
      obtain ⟨i', hi'⟩ := hy
      rw [hg]
      simp only
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, Finset.prod_eq_zero (Finset.mem_univ i') hi']
  have hne : ∀ x, φ x ≠ some 0 := by
    intro x
    by_cases hx : ∀ i, μ (x i) ≠ 0
    · simp only [φ, if_pos hx, ne_eq, Option.some.injEq]
      intro h
      have := congrFun h ⟨x ⟨0, hn⟩, hx _⟩
      simp only [Pi.zero_apply, Fin.ext_iff, Fin.val_zero] at this
      have h1 : ⟨0, hn⟩ ∈ Finset.univ.filter (fun i => x i = x ⟨0, hn⟩) := by simp
      have := Finset.card_pos.mpr ⟨_, h1⟩
      simp only [cnt] at *
      omega
    · simp [φ, if_neg hx]
  let G : Option ({i // μ i ≠ 0} → Fin (n + 1)) → ℝ := fun o =>
    if h : ∃ x, φ x = o then g h.choose else 0
  have hsurj : Set.SurjOn G (Finset.univ.image φ : Set _) (Finset.univ.image g : Set _) := by
    intro v hv
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hv
    obtain ⟨x, rfl⟩ := hv
    refine ⟨φ x, by simp, ?_⟩
    have h : ∃ y, φ y = φ x := ⟨x, rfl⟩
    simp only [G, dif_pos h]
    exact hφ _ _ h.choose_spec
  calc (Finset.univ.image g).card ≤ (Finset.univ.image φ).card :=
        Finset.card_le_card_of_surjOn G hsurj
    _ ≤ (Finset.univ.erase (some (0 : {i // μ i ≠ 0} → Fin (n + 1)))).card := by
        apply Finset.card_le_card
        intro o ho
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at ho
        obtain ⟨x, rfl⟩ := ho
        simp [hne x]
    _ = (n + 1) ^ (Fintype.card {i // μ i ≠ 0}) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option,
          Fintype.card_fun, Fintype.card_fin]
        simp


theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho : Op I) (hrho : IsDensityMatrix rho) (n : ℕ) (hn : 0 < n) :
    (Finset.univ.image (ascEigenvalues (matrixPower rho n))).card ≤ (n+1)^rho.rank := by
  have hH : rho.IsHermitian := hrho.1.isHermitian
  set μ := hH.eigenvalues
  set U : Matrix I I ℂ := (hH.eigenvectorUnitary : Matrix I I ℂ)
  have hrho_eq : rho = U * diagonal (Complex.ofReal ∘ μ) * star U := by
    simpa using hH.spectral_theorem
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  set W := matrixPower U n
  have hW : star W * W = 1 := by
    rw [← g68m_mp_star, ← g68m_mp_mul, hU, g68m_mp_one]
  have hA : matrixPower rho n = W * diagonal (fun x : Fin n → I => ∏ i, ((μ (x i) : ℝ) : ℂ)) *
      star W := by
    conv_lhs => rw [hrho_eq]
    rw [g68m_mp_mul, g68m_mp_mul, g68m_mp_diag, g68m_mp_star]
    rfl
  have hHA : (matrixPower rho n).IsHermitian := by
    show (matrixPower rho n)ᴴ = matrixPower rho n
    rw [← Matrix.star_eq_conjTranspose, ← g68m_mp_star, Matrix.star_eq_conjTranspose, hH.eq]
  set g : (Fin n → I) → ℝ := fun x => ∏ i, μ (x i)
  have hsub : Finset.univ.image (ascEigenvalues (matrixPower rho n)) ⊆ Finset.univ.image g := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨k, rfl⟩ := hv
    unfold ascEigenvalues
    rw [dif_pos hHA]
    obtain ⟨x, hx⟩ := g68m_eig_mem _ _ _ hW hA hHA
      (Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.rev k))
    refine ⟨x, ?_⟩
    have h2 : hHA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.rev k)) =
        hHA.eigenvalues₀ (Fin.rev k) := by
      simp [Matrix.IsHermitian.eigenvalues]
    rw [h2] at hx
    apply Complex.ofReal_injective
    rw [hx]; simp [g]
  calc (Finset.univ.image (ascEigenvalues (matrixPower rho n))).card
      ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (n + 1) ^ (Fintype.card {i // μ i ≠ 0}) := g68m_count μ n hn
    _ = (n+1)^rho.rank := by rw [hH.rank_eq_card_non_zero_eigs]

end
