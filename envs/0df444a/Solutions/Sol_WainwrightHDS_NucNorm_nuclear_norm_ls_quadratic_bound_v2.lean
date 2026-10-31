-- Prove2me | solution 1 for WainwrightHDS.NucNorm.nuclear_norm_ls_quadratic_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T04:15:58.33023+00:00
-- url     : https://prove2.me/submissions/3e8a4b08-f07d-4d46-bee0-ec6c4400b715
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_projMat
import Definitions.Def_WainwrightHDS_NucNorm_projM
import Definitions.Def_WainwrightHDS_NucNorm_projMperp
import Definitions.Def_WainwrightHDS_NucNorm_projMbarPerp
import Definitions.Def_WainwrightHDS_NucNorm_projMbar
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_WainwrightHDS_NucNorm_obsOp
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_WainwrightHDS_NucNorm_Mspace
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp
import Definitions.Def_WainwrightHDS_NucNorm_Mbar
import Definitions.Def_WainwrightHDS_NucNorm_lsNucObjective
import Definitions.Def_WainwrightHDS_NucNorm_frobSq
import Theorems.Thm_WainwrightHDS_NucNorm_cone_constraint_nuclear
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_le_sqrt_two_r_frob_of_mem_Mbar
import Theorems.Thm_WainwrightHDS_NucNorm_isLUB_traceInner_nucNorm_le_one
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_le
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_smul
import Theorems.Thm_WainwrightHDS_NucNorm_nucNorm_add_of_mem_Mspace_of_mem_MbarPerp
import Theorems.Thm_WainwrightHDS_NucNorm_exists_top_r_singular_subspaces
import Theorems.Thm_WainwrightHDS_NucNorm_quadratic_bound_from_subspace_and_rsc

namespace WainwrightHDS.NucNorm

set_option linter.unusedVariables false

lemma traceInner_comm {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A B = traceInner B A := by
  unfold traceInner
  simp_rw [mul_comm]

lemma traceInner_smul_left {d₁ d₂ : ℕ} (c : ℝ) (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (c • A) B = c * traceInner A B := by
  unfold traceInner
  simp_rw [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

lemma traceInner_sum_left {d₁ d₂ : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d₁) (Fin d₂) ℝ)
    (B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (∑ i ∈ s, A i) B = ∑ i ∈ s, traceInner (A i) B := by
  unfold traceInner
  simp_rw [Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := s)]
  rw [Finset.sum_comm]

lemma traceInner_obsOp {n d₁ d₂ : ℕ} (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ)
    (w : Fin n → ℝ) (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner ((1 / (n : ℝ)) • ∑ i, w i • X i) Δ =
      (1 / (n : ℝ)) * ∑ i, w i * obsOp X Δ i := by
  rw [traceInner_smul_left, traceInner_sum_left]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [traceInner_smul_left]
  dsimp [obsOp]

lemma traceInner_sub_right {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (B - C) = traceInner A B - traceInner A C := by
  unfold traceInner
  simp_rw [Matrix.sub_apply, mul_sub, ← Finset.sum_sub_distrib]

lemma obsOp_sub {n d₁ d₂ : ℕ} (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ)
    (A B : Matrix (Fin d₁) (Fin d₂) ℝ) (i : Fin n) :
    obsOp X (A - B) i = obsOp X A i - obsOp X B i := by
  dsimp [obsOp]
  exact traceInner_sub_right (X i) A B

lemma traceInner_neg_left {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner (-A) B = - traceInner A B := by
  unfold traceInner
  simp_rw [Matrix.neg_apply, neg_mul, ← Finset.sum_neg_distrib]

lemma traceInner_add_right {d₁ d₂ : ℕ} (A B C : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner A (B + C) = traceInner A B + traceInner A C := by
  unfold traceInner
  simp_rw [Matrix.add_apply, mul_add, ← Finset.sum_add_distrib]

lemma opNorm2_neg {d₁ d₂ : ℕ} (G : Matrix (Fin d₁) (Fin d₂) ℝ) :
    opNorm2 (-G) = opNorm2 G := by
  dsimp [opNorm2]
  rw [map_neg Matrix.toEuclideanLin, map_neg LinearMap.toContinuousLinearMap, norm_neg]

lemma nucNorm_nonneg {d₁ d₂ : ℕ} (M : Matrix (Fin d₁) (Fin d₂) ℝ) :
    0 ≤ nucNorm M := by
  dsimp [nucNorm, singVal]
  exact Finset.sum_nonneg (fun j _ => LinearMap.singularValues_nonneg _ _)

lemma frobSq_nonneg {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma traceInner_le_opNorm2_mul_nucNorm {d₁ d₂ : ℕ} (M N : Matrix (Fin d₁) (Fin d₂) ℝ) :
    traceInner M N ≤ opNorm2 N * nucNorm M := by
  have hlub := isLUB_traceInner_nucNorm_le_one N
  have hub := hlub.1
  by_cases hpos : 0 < nucNorm M
  · have h_le_one : nucNorm ((nucNorm M)⁻¹ • M) ≤ 1 := by
      rw [nucNorm_smul, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
    have h_mem : traceInner ((nucNorm M)⁻¹ • M) N ∈ {t : ℝ | ∃ M' : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M' ≤ 1 ∧ t = traceInner M' N} :=
      ⟨(nucNorm M)⁻¹ • M, h_le_one, rfl⟩
    have h_bound := hub h_mem
    rw [traceInner_smul_left] at h_bound
    have h_mul := mul_le_mul_of_nonneg_right h_bound (le_of_lt hpos)
    have h_cancel : (nucNorm M)⁻¹ * traceInner M N * nucNorm M = traceInner M N := by
      calc (nucNorm M)⁻¹ * traceInner M N * nucNorm M
        _ = traceInner M N * ((nucNorm M)⁻¹ * nucNorm M) := by ring
        _ = traceInner M N * 1 := by rw [inv_mul_cancel₀ (ne_of_gt hpos)]
        _ = traceInner M N := mul_one _
    rwa [h_cancel] at h_mul
  · have hzero : nucNorm M = 0 := by
      have : 0 ≤ nucNorm M := nucNorm_nonneg M
      linarith
    rw [hzero, mul_zero]
    by_contra! h_gt
    let c := (opNorm2 N + 1) / traceInner M N
    have hc_pos : 0 < c := div_pos (by
      have : 0 ≤ opNorm2 N := norm_nonneg _
      linarith) h_gt
    have hc_bound : nucNorm (c • M) ≤ 1 := by
      rw [nucNorm_smul, abs_of_pos hc_pos, hzero, mul_zero]
      linarith
    have h_mem : traceInner (c • M) N ∈ {t : ℝ | ∃ M' : Matrix (Fin d₁) (Fin d₂) ℝ, nucNorm M' ≤ 1 ∧ t = traceInner M' N} :=
      ⟨c • M, hc_bound, rfl⟩
    have h_ub := hub h_mem
    rw [traceInner_smul_left] at h_ub
    dsimp [c] at h_ub
    rw [div_mul_cancel₀ (opNorm2 N + 1) (ne_of_gt h_gt)] at h_ub
    linarith

lemma ls_basic_inequality {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (lam : ℝ) (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ) :
    1 / (2 * (n : ℝ)) * ∑ i, (obsOp X (Θhat - Θstar) i) ^ 2 ≤
      traceInner ((1 / (n : ℝ)) • ∑ i, w i • X i) (Θhat - Θstar) +
        lam * (nucNorm Θstar - nucNorm Θhat) := by
  have hmin_star := hmin Θstar
  dsimp [lsNucObjective] at hmin_star
  set Δ := Θhat - Θstar
  have hy_star : ∀ i, y i - obsOp X Θstar i = w i := by
    intro i
    rw [hy i]
    ring
  have hy_hat : ∀ i, y i - obsOp X Θhat i = w i - obsOp X Δ i := by
    intro i
    rw [hy i, obsOp_sub]
    ring
  have h_sq_diff : ∀ i, (y i - obsOp X Θhat i) ^ 2 - (y i - obsOp X Θstar i) ^ 2 =
      (obsOp X Δ i) ^ 2 - 2 * w i * obsOp X Δ i := by
    intro i
    rw [hy_hat i, hy_star i]
    ring
  have h_sum_diff : ∑ i, (y i - obsOp X Θhat i) ^ 2 =
      ∑ i, (y i - obsOp X Θstar i) ^ 2 + ∑ i, ((obsOp X Δ i) ^ 2 - 2 * w i * obsOp X Δ i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    linarith [h_sq_diff i]
  rw [h_sum_diff] at hmin_star
  have h_split : ∑ i, ((obsOp X Δ i) ^ 2 - 2 * w i * obsOp X Δ i) =
      (∑ i, (obsOp X Δ i) ^ 2) - 2 * ∑ i, w i * obsOp X Δ i := by
    rw [Finset.sum_sub_distrib]
    congr 1
    have h_two : (∑ i, 2 * w i * obsOp X Δ i) = 2 * ∑ i, w i * obsOp X Δ i := by
      simp_rw [mul_assoc]
      exact (Finset.mul_sum Finset.univ (fun i => w i * obsOp X Δ i) 2).symm
    exact h_two
  rw [h_split] at hmin_star
  have h_trace := traceInner_obsOp X w Δ
  have h_n_cancel : 1 / (2 * (n : ℝ)) * (2 * ∑ i, w i * obsOp X Δ i) =
      traceInner ((1 / (n : ℝ)) • ∑ i, w i • X i) Δ := by
    rw [h_trace]
    ring
  have h_alg : 1 / (2 * (n : ℝ)) * (∑ i, (y i - obsOp X Θstar i) ^ 2 +
      ((∑ i, (obsOp X Δ i) ^ 2) - 2 * ∑ i, w i * obsOp X Δ i)) =
      1 / (2 * (n : ℝ)) * ∑ i, (y i - obsOp X Θstar i) ^ 2 +
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 -
      1 / (2 * (n : ℝ)) * (2 * ∑ i, w i * obsOp X Δ i) := by ring
  rw [h_alg, h_n_cancel] at hmin_star
  linarith

lemma projMbar_add_projMbarPerp {d₁ d₂ : ℕ}
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁))) (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂)))
    (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    projMbar U V Δ + projMbarPerp U V Δ = Δ := by
  dsimp [projMbar]
  abel

/-- **Intermediate quadratic inequality in the proof of Proposition 10.6 (Wainwright §10.2.2, p. 320).**
Under restricted strong convexity (10.17) and the dual-norm event `|||(1/n) ∑ᵢ wᵢ Xᵢ|||₂ ≤ λₙ/2`,
choosing `(𝕌, 𝕍)` to be the top-`r` left and right singular subspaces of `Θ*` and combining the
nuclear-norm cone constraint (10.15) with `Ψ(𝕄̄(𝕌, 𝕍)) ≤ √(2r)` and `128 c₀ (d₁ + d₂) r ≤ κ n`
yields the quadratic inequality in `|||Θ̂ − Θ*|||_F`:
`κ |||Θ̂ − Θ*|||_F² ≤ (3/2) λₙ √(2r) |||Θ̂ − Θ*|||_F + λₙ ∑_{j=r+1}^{d'} σ_j(Θ*) + 16 c₀ ((d₁+d₂)/n) [∑_{j=r+1}^{d'} σ_j(Θ*)]²`. -/
theorem nuclear_norm_ls_quadratic_bound_v2 {n d₁ d₂ : ℕ}
    (X : Fin n → Matrix (Fin d₁) (Fin d₂) ℝ) (Θstar : Matrix (Fin d₁) (Fin d₂) ℝ)
    (w y : Fin n → ℝ) (hy : ∀ i, y i = obsOp X Θstar i + w i)
    (κ c₀ lam : ℝ) (hκ : 0 < κ) (hc₀ : 0 < c₀) (hlam : 0 < lam)
    (hRSC : ∀ Δ : Matrix (Fin d₁) (Fin d₂) ℝ,
      1 / (2 * (n : ℝ)) * ∑ i, (obsOp X Δ i) ^ 2 ≥
        κ / 2 * frobSq Δ - c₀ * (((d₁ : ℝ) + d₂) / n) * nucNorm Δ ^ 2)
    (hG : opNorm2 ((1 / (n : ℝ)) • ∑ i, w i • X i) ≤ lam / 2)
    (Θhat : Matrix (Fin d₁) (Fin d₂) ℝ)
    (hmin : ∀ Θ : Matrix (Fin d₁) (Fin d₂) ℝ, lsNucObjective X y lam Θhat ≤ lsNucObjective X y lam Θ)
    (r : ℕ) (hr₁ : 1 ≤ r) (hrd : r ≤ min d₁ d₂)
    (hrκ : 128 * c₀ * ((d₁ : ℝ) + d₂) * r ≤ κ * n) :
    κ * frobSq (Θhat - Θstar) ≤
      3 / 2 * lam * Real.sqrt (2 * r) * Real.sqrt (frobSq (Θhat - Θstar)) +
        lam * (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) +
        16 * c₀ * ((d₁ : ℝ) + d₂) / n *
          (∑ j ∈ Finset.Ico r (min d₁ d₂), singVal j Θstar) ^ 2 := by
  -- Obtain top-r singular subspaces (U, V)
  obtain ⟨U, V, hU, hV, h_tail, h_mem, h_frob_proj⟩ :=
    exists_top_r_singular_subspaces Θstar r hr₁ hrd
  set Δ := Θhat - Θstar
  have h_mbar_nuc := nucNorm_le_sqrt_two_r_frob_of_mem_Mbar U V r hU hV (projMbar U V Δ) (h_mem Δ)
  have h_frob_le : Real.sqrt (frobSq (projMbar U V Δ)) ≤ Real.sqrt (frobSq Δ) :=
    Real.sqrt_le_sqrt (h_frob_proj Δ)
  have h_mbar_bound : nucNorm (projMbar U V Δ) ≤ Real.sqrt (2 * (r : ℝ)) * Real.sqrt (frobSq Δ) := by
    refine le_trans h_mbar_nuc ?_
    refine mul_le_mul_of_nonneg_left h_frob_le (Real.sqrt_nonneg _)
  exact quadratic_bound_from_subspace_and_rsc X Θstar w y hy κ c₀ lam hκ hc₀ hlam
    hRSC hG Θhat hmin r hr₁ hrd hrκ U V hU hV h_tail h_mbar_bound

abbrev solution := @nuclear_norm_ls_quadratic_bound_v2

end WainwrightHDS.NucNorm

abbrev solution := @WainwrightHDS.NucNorm.nuclear_norm_ls_quadratic_bound_v2
