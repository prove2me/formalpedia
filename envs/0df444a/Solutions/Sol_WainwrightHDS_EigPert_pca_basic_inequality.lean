-- Prove2me | solution 1 for WainwrightHDS.EigPert.pca_basic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:36:47.27342+00:00
-- url     : https://prove2.me/submissions/58dc1752-cbee-4444-9a65-1f9f049b7dfd

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_gamma
import Definitions.Def_WainwrightHDS_EigPert_IsMaxEigenvector
import Definitions.Def_WainwrightHDS_EigPert_psi

open WainwrightHDS.EigPert

set_option autoImplicit false

section LemmaHelpers

lemma psi_sub_eq {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.IsHermitian)
    (θstar θhat : EuclideanSpace ℝ (Fin d)) :
    psi θstar P (θhat - θstar) =
      inner ℝ θhat (Matrix.toEuclideanLin P θhat) -
      inner ℝ θstar (Matrix.toEuclideanLin P θstar) := by
  dsimp [psi]
  have hsymm : ∀ u v : EuclideanSpace ℝ (Fin d),
      inner ℝ u (Matrix.toEuclideanLin P v) = inner ℝ v (Matrix.toEuclideanLin P u) := by
    intro u v
    have h1 := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP
    rw [← h1 u v, real_inner_comm]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_left]
  rw [hsymm θstar θhat]
  ring

lemma inner_map_eq_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) (eig : ι → ℝ)
    (hT : ∀ i, T (b i) = eig i • b i) (x : E) :
    inner ℝ x (T x) = ∑ i, eig i * (inner ℝ x (b i)) ^ 2 := by
  nth_rw 2 [← b.sum_repr x]
  rw [map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hT, smul_smul, inner_smul_right, OrthonormalBasis.repr_apply_apply]
  rw [real_inner_comm (b i) x]
  ring

lemma inner_θstar_S_θstar {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar) :
    inner ℝ θstar (Matrix.toEuclideanLin S θstar) = gamma S hS.1 0 := by
  obtain ⟨hnorm, heig⟩ := hθstar
  rw [heig, inner_smul_right, real_inner_self_eq_norm_mul_norm, hnorm, mul_one, mul_one]

noncomputable def one_N (n : ℕ) : Fin (Fintype.card (Fin (n + 2))) :=
  Fin.cast (Fintype.card_fin (n + 2)).symm 1

lemma gamma_one_eq {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef) :
    gamma S hS.1 1 = hS.1.eigenvalues₀ (one_N n) := rfl

lemma val_one_N (n : ℕ) : (one_N n).val = 1 := by
  change (1 : Fin (n + 2)).val = 1
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

lemma eig_le_of_ne_zero {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (i : Fin (Fintype.card (Fin (n + 2)))) (hi : i ≠ 0) :
    hS.1.eigenvalues₀ i ≤ gamma S hS.1 1 := by
  rw [gamma_one_eq S hS]
  apply hS.1.eigenvalues₀_antitone
  rw [Fin.le_def, val_one_N]
  have hne : i.val ≠ 0 := by
    intro hc
    exact hi (Fin.ext hc)
  omega

lemma gamma_zero_eq {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef) :
    gamma S hS.1 0 = hS.1.eigenvalues₀ 0 := rfl

noncomputable def eigBasis {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef) :
    OrthonormalBasis (Fin (Fintype.card (Fin (n + 2)))) ℝ (EuclideanSpace ℝ (Fin (n + 2))) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hS.1).eigenvectorBasis finrank_euclideanSpace

lemma apply_eigBasis {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (i : Fin (Fintype.card (Fin (n + 2)))) :
    Matrix.toEuclideanLin S (eigBasis S hS i) = hS.1.eigenvalues₀ i • eigBasis S hS i :=
  LinearMap.IsSymmetric.apply_eigenvectorBasis _ _ i

lemma inner_θstar_b_of_ne_zero {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (i : Fin (Fintype.card (Fin (n + 2)))) (hi : i ≠ 0) :
    inner ℝ θstar (eigBasis S hS i) = 0 := by
  let hT : (Matrix.toEuclideanLin S).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hS.1
  let b := eigBasis S hS
  have hsymm := hT θstar (b i)
  have h1 : Matrix.toEuclideanLin S θstar = gamma S hS.1 0 • θstar := hθstar.2
  have h2 : Matrix.toEuclideanLin S (b i) = hS.1.eigenvalues₀ i • b i := apply_eigBasis S hS i
  rw [h1, h2, real_inner_smul_left, real_inner_smul_right] at hsymm
  have h3 : (gamma S hS.1 0 - hS.1.eigenvalues₀ i) * inner ℝ θstar (b i) = 0 := by
    calc
      (gamma S hS.1 0 - hS.1.eigenvalues₀ i) * inner ℝ θstar (b i)
        = gamma S hS.1 0 * inner ℝ θstar (b i) - hS.1.eigenvalues₀ i * inner ℝ θstar (b i) := by ring
      _ = 0 := by linarith
  have hle := eig_le_of_ne_zero S hS i hi
  have hpos : 0 < gamma S hS.1 0 - hS.1.eigenvalues₀ i := by linarith
  cases mul_eq_zero.mp h3 with
  | inl h => linarith
  | inr h => exact h

lemma θstar_eq_smul_b_zero {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar) :
    θstar = inner ℝ θstar (eigBasis S hS 0) • eigBasis S hS 0 := by
  let b := eigBasis S hS
  have h_repr := b.sum_repr θstar
  have h_zero : ∀ i : Fin (Fintype.card (Fin (n + 2))), i ≠ 0 → b.repr θstar i • b i = 0 := by
    intro i hi
    have h_inner : inner ℝ θstar (b i) = 0 := inner_θstar_b_of_ne_zero S hS hgap θstar hθstar i hi
    have hr : b.repr θstar i = inner ℝ θstar (b i) := by
      rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
    rw [hr, h_inner, zero_smul]
  have h_single : (∑ i, b.repr θstar i • b i) = b.repr θstar 0 • b 0 := by
    apply Finset.sum_eq_single 0
    · intro i _ hi
      exact h_zero i hi
    · intro h0
      exact False.elim (h0 (Finset.mem_univ 0))
  rw [h_single] at h_repr
  have hr0 : b.repr θstar 0 = inner ℝ θstar (b 0) := by
    rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  rw [hr0] at h_repr
  exact h_repr.symm

lemma sq_inner_θstar_b_zero {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar) :
    (inner ℝ θstar (eigBasis S hS 0)) ^ 2 = 1 := by
  let b := eigBasis S hS
  have h_sum := b.sum_sq_inner_left θstar
  have h_norm : ‖θstar‖ ^ 2 = 1 := by
    rw [hθstar.1, one_pow]
  rw [h_norm] at h_sum
  have h_single : (∑ i, (inner ℝ θstar (b i)) ^ 2) = (inner ℝ θstar (b 0)) ^ 2 := by
    apply Finset.sum_eq_single 0
    · intro i _ hi
      have h_zero := inner_θstar_b_of_ne_zero S hS hgap θstar hθstar i hi
      rw [h_zero, zero_pow two_ne_zero]
    · intro h0
      exact False.elim (h0 (Finset.mem_univ 0))
  rw [h_single] at h_sum
  exact h_sum

lemma sq_inner_θhat_θstar_eq {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (θhat : EuclideanSpace ℝ (Fin (n + 2))) :
    (inner ℝ θhat θstar) ^ 2 = (inner ℝ θhat (eigBasis S hS 0)) ^ 2 := by
  let b := eigBasis S hS
  have hθ : θstar = inner ℝ θstar (b 0) • b 0 := θstar_eq_smul_b_zero S hS hgap θstar hθstar
  have hsq := sq_inner_θstar_b_zero S hS hgap θstar hθstar
  nth_rw 1 [hθ]
  rw [inner_smul_right, mul_pow, hsq, one_mul]

lemma inner_θhat_S_θhat_le {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hS : S.PosSemidef)
    (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (θhat : EuclideanSpace ℝ (Fin (n + 2))) (hθhat : ‖θhat‖ = 1) :
    inner ℝ θhat (Matrix.toEuclideanLin S θhat) ≤
      gamma S hS.1 0 * (inner ℝ θhat θstar) ^ 2 +
      gamma S hS.1 1 * (1 - (inner ℝ θhat θstar) ^ 2) := by
  let b := eigBasis S hS
  have h_sum := inner_map_eq_sum b (Matrix.toEuclideanLin S) hS.1.eigenvalues₀ (apply_eigBasis S hS) θhat
  rw [h_sum]
  have h_split : (∑ i : Fin (Fintype.card (Fin (n + 2))), hS.1.eigenvalues₀ i * (inner ℝ θhat (b i)) ^ 2) =
      hS.1.eigenvalues₀ 0 * (inner ℝ θhat (b 0)) ^ 2 +
      ∑ i ∈ Finset.univ.erase 0, hS.1.eigenvalues₀ i * (inner ℝ θhat (b i)) ^ 2 := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ 0)]
    rw [Finset.sum_insert (by simp)]
  rw [h_split]
  have h_le_rest : ∑ i ∈ Finset.univ.erase 0, hS.1.eigenvalues₀ i * (inner ℝ θhat (b i)) ^ 2 ≤
      ∑ i ∈ Finset.univ.erase 0, gamma S hS.1 1 * (inner ℝ θhat (b i)) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi_ne : i ≠ 0 := Finset.ne_of_mem_erase hi
    have h_eig := eig_le_of_ne_zero S hS i hi_ne
    exact mul_le_mul_of_nonneg_right h_eig (sq_nonneg _)
  have h_mul_sum : (∑ i ∈ Finset.univ.erase 0, gamma S hS.1 1 * (inner ℝ θhat (b i)) ^ 2) =
      gamma S hS.1 1 * ∑ i ∈ Finset.univ.erase 0, (inner ℝ θhat (b i)) ^ 2 := by
    rw [Finset.mul_sum]
  have h_sq_sum := b.sum_sq_inner_left θhat
  have h_norm : ‖θhat‖ ^ 2 = 1 := by rw [hθhat, one_pow]
  rw [h_norm] at h_sq_sum
  have h_split_sq : (∑ i : Fin (Fintype.card (Fin (n + 2))), (inner ℝ θhat (b i)) ^ 2) =
      (inner ℝ θhat (b 0)) ^ 2 + ∑ i ∈ Finset.univ.erase 0, (inner ℝ θhat (b i)) ^ 2 := by
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ 0)]
    rw [Finset.sum_insert (by simp)]
  rw [h_split_sq] at h_sq_sum
  have h_rest_eq : (∑ i ∈ Finset.univ.erase 0, (inner ℝ θhat (b i)) ^ 2) = 1 - (inner ℝ θhat (b 0)) ^ 2 := by
    linarith
  have h_sq_eq := sq_inner_θhat_θstar_eq S hS hgap θstar hθstar θhat
  rw [h_mul_sum] at h_le_rest
  rw [h_rest_eq] at h_le_rest
  rw [← h_sq_eq] at h_le_rest
  rw [← h_sq_eq]
  rw [gamma_zero_eq S hS]
  linarith

end LemmaHelpers

open WainwrightHDS.EigPert in
theorem solution {n : ℕ} (S : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (hS : S.PosSemidef) (hgap : 0 < gamma S hS.1 0 - gamma S hS.1 1)
    (θstar : EuclideanSpace ℝ (Fin (n + 2))) (hθstar : IsMaxEigenvector S hS.1 θstar)
    (P : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hP : P.IsHermitian)
    (C : Set (EuclideanSpace ℝ (Fin (n + 2)))) (hC : C ⊆ {v | ‖v‖ = 1})
    (hθstarC : θstar ∈ C) (θhat : EuclideanSpace ℝ (Fin (n + 2))) (hθhatC : θhat ∈ C)
    (hθhat_max : ∀ θ ∈ C, inner ℝ θ (Matrix.toEuclideanLin (S + P) θ) ≤
      inner ℝ θhat (Matrix.toEuclideanLin (S + P) θhat)) :
    (gamma S hS.1 0 - gamma S hS.1 1) * (1 - (inner ℝ θhat θstar) ^ 2) ≤
      |psi θstar P (θhat - θstar)| := by
  have hθhat_norm : ‖θhat‖ = 1 := hC hθhatC
  have hθstar_norm : ‖θstar‖ = 1 := hθstar.1
  have h_S_θstar := inner_θstar_S_θstar S hS θstar hθstar
  have h_S_θhat := inner_θhat_S_θhat_le S hS hgap θstar hθstar θhat hθhat_norm
  have h_diff_S : (gamma S hS.1 0 - gamma S hS.1 1) * (1 - (inner ℝ θhat θstar) ^ 2) ≤
      inner ℝ θstar (Matrix.toEuclideanLin S θstar) - inner ℝ θhat (Matrix.toEuclideanLin S θhat) := by
    rw [h_S_θstar]
    linarith
  have h_lin_add : Matrix.toEuclideanLin (S + P) = Matrix.toEuclideanLin S + Matrix.toEuclideanLin P :=
    map_add Matrix.toEuclideanLin S P
  have h_eval (v : EuclideanSpace ℝ (Fin (n + 2))) :
      inner ℝ v (Matrix.toEuclideanLin (S + P) v) =
      inner ℝ v (Matrix.toEuclideanLin S v) + inner ℝ v (Matrix.toEuclideanLin P v) := by
    rw [h_lin_add, LinearMap.add_apply, inner_add_right]
  have h_max := hθhat_max θstar hθstarC
  rw [h_eval θstar, h_eval θhat] at h_max
  have h_diff_P : inner ℝ θstar (Matrix.toEuclideanLin S θstar) - inner ℝ θhat (Matrix.toEuclideanLin S θhat) ≤
      inner ℝ θhat (Matrix.toEuclideanLin P θhat) - inner ℝ θstar (Matrix.toEuclideanLin P θstar) := by
    linarith
  have h_psi := psi_sub_eq P hP θstar θhat
  rw [← h_psi] at h_diff_P
  have h_abs : psi θstar P (θhat - θstar) ≤ |psi θstar P (θhat - θstar)| := le_abs_self _
  linarith
