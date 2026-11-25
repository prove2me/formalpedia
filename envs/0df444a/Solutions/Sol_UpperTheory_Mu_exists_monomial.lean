-- Prove2me | solution 1 for UpperTheory.Mu.exists_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:27:21.56981+00:00
-- url     : https://prove2.me/submissions/1beb4848-3c3c-4a9d-9751-01676c06733a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial
import Theorems.Thm_UpperTheory_Mu_pow_torsionOrder_eq_one
import Theorems.Thm_UpperTheory_Mu_norm_eq_one_of_star_mul
import Theorems.Thm_GlobalTheory_finrank_mul_abs_norm_rpow_le_sum_sq
import Theorems.Thm_GlobalTheory_one_le_abs_norm_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
namespace UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
private theorem finrank_le_sum_sq_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (GlobalTheory.finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast GlobalTheory.one_le_abs_norm_of_isIntegral hx h0
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow h1 (by positivity))
private theorem exists_single_of_sum_star_mul {n : ℕ} [Star K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (z : Fin n → K) (hz : ∀ i, IsIntegral ℤ (z i)) (h1 : ∑ i, star (z i) * z i = 1) :
    ∃ i, ∀ j, j ≠ i → z j = 0 := by
  have hφ : ∀ φ : K →+* ℂ, ∑ i, ‖φ (z i)‖ ^ 2 = 1 := by
    intro φ
    have h := congrArg φ h1
    rw [map_sum, map_one] at h
    have h2 : ∀ i, φ (star (z i) * z i) = ((‖φ (z i)‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [map_mul, hconj, Complex.conj_mul']
      push_cast
      rfl
    simp_rw [h2] at h
    exact_mod_cast h
  have htot : ∑ i, ∑ φ : K →+* ℂ, ‖φ (z i)‖ ^ 2 = (Module.finrank ℚ K : ℝ) := by
    rw [Finset.sum_comm]
    simp [hφ, Embeddings.card]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    simp [hall] at h1
  refine ⟨i, fun j hji => ?_⟩
  by_contra hj
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ φ : K →+* ℂ, ‖φ (z k)‖ ^ 2 :=
    fun k _ => Finset.sum_nonneg fun _ _ => by positivity
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
    (fun k hk _ => hnn k hk)
  rw [Finset.sum_pair (Ne.symm hji), htot] at hsub
  have := finrank_le_sum_sq_of_isIntegral (hz i) hi
  have := finrank_le_sum_sq_of_isIntegral (hz j) hj
  linarith
end UpperTheory.Mu
end

set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
namespace UpperTheory.Mu
theorem _root_.solution [StarRing K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : gᴴ * g = 1) (hint : ∀ a b, IsIntegral ℤ (g a b)) :
    ∃ (t : Fin n → K) (σ : Equiv.Perm (Fin n)), (∀ b, t b ^ Units.torsionOrder K = 1) ∧
      g = Matrix.of fun a b => if a = σ b then t b else 0 := by
  have hcol : ∀ b, ∑ a, star (g a b) * g a b = 1 := by
    intro b
    have h := congrFun (congrFun hg b) b
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have horth : ∀ b b', b ≠ b' → ∑ a, star (g a b) * g a b' = 0 := by
    intro b b' hbb
    have h := congrFun (congrFun hg b) b'
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne hbb] using h
  choose f hf using fun b => exists_single_of_sum_star_mul hconj (fun a => g a b)
    (fun a => hint a b) (hcol b)
  have hdiag : ∀ b, star (g (f b) b) * g (f b) b = 1 := by
    intro b
    have h := hcol b
    rwa [Finset.sum_eq_single (f b) (fun j _ hj => by simp [hf b j hj]) (by simp)] at h
  have hne : ∀ b, g (f b) b ≠ 0 := by
    intro b h
    have h' := hdiag b
    simp [h] at h'
  have hinj : Function.Injective f := by
    intro b b' hbb
    by_contra hb
    have h := horth b b' hb
    rw [Finset.sum_eq_single (f b) (fun j _ hj => by simp [hf b j hj]) (by simp)] at h
    rcases mul_eq_zero.mp h with h | h
    · exact hne b (star_eq_zero.mp h)
    · rw [hbb] at h
      exact hne b' h
  refine ⟨fun b => g (f b) b, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
    fun b => pow_torsionOrder_eq_one (hint _ _) (norm_eq_one_of_star_mul hconj (hdiag b)), ?_⟩
  ext a b
  simp only [Matrix.of_apply, Equiv.ofBijective_apply]
  split_ifs with h
  · rw [h]
  · exact hf b a h
end UpperTheory.Mu
