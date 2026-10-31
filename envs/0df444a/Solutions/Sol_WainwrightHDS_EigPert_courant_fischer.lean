-- Prove2me | solution 1 for WainwrightHDS.EigPert.courant_fischer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T02:26:25.636751+00:00
-- url     : https://prove2.me/submissions/00ce74cb-1d36-43a6-83ae-d53767081f77

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_gamma

namespace WainwrightHDS.EigPert

theorem courant_fischer {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsHermitian)
    (j : Fin d) (hj : 1 ≤ j.val) :
    IsLeast
      {c : ℝ | ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V = j.val ∧
        IsGreatest ((fun u => inner ℝ u (Matrix.toEuclideanLin Q u)) ''
          {u | u ∈ Vᗮ ∧ ‖u‖ = 1}) c}
      (gamma Q hQ j) := by
  have _ := hj
  let hTQ := Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin d) := finrank_euclideanSpace
  let bQ := hTQ.eigenvectorBasis hn
  let j0 : Fin (Fintype.card (Fin d)) := Fin.cast (Fintype.card_fin d).symm j
  have h_gammaQ : hTQ.eigenvalues hn j0 = gamma Q hQ j := rfl
  have h_repr_T : ∀ (u : EuclideanSpace ℝ (Fin d)) (i : Fin (Fintype.card (Fin d))),
      (bQ.repr (Matrix.toEuclideanLin Q u)).ofLp i = hTQ.eigenvalues hn i * (bQ.repr u).ofLp i := by
    intro u i
    exact hTQ.eigenvectorBasis_apply_self_apply hn u i
  have h_inner_Q : ∀ u : EuclideanSpace ℝ (Fin d),
      inner ℝ u (Matrix.toEuclideanLin Q u) =
        ∑ i, hTQ.eigenvalues hn i * (bQ.repr u).ofLp i ^ 2 := by
    intro u
    rw [← bQ.repr.inner_map_map, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_repr_T u i, Real.inner_apply]
    ring
  have h_norm_repr : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      (∑ i, (bQ.repr u).ofLp i ^ 2) = 1 := by
    intro u hu
    have h1 : ‖bQ.repr u‖ ^ 2 = 1 := by
      rw [LinearIsometryEquiv.norm_map, hu, one_pow]
    rw [PiLp.norm_sq_eq_of_L2] at h1
    have h_simp : (∑ i, ‖(bQ.repr u).ofLp i‖ ^ 2) = ∑ i, (bQ.repr u).ofLp i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_simp] at h1
    exact h1
  constructor
  · -- Part 1: gamma Q hQ j ∈ S
    dsimp
    let V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
      Submodule.span ℝ (Set.range (fun (i : Finset.Iio j0) => bQ i.val))
    use V
    have hli : LinearIndependent ℝ bQ := bQ.orthonormal.linearIndependent
    have hli_v : LinearIndependent ℝ (fun (i : Finset.Iio j0) => bQ i.val) :=
      hli.comp Subtype.val Subtype.val_injective
    have hdim : Module.finrank ℝ V = j.val := by
      rw [finrank_span_eq_card hli_v, Fintype.card_coe, Fin.card_Iio]
      rfl
    refine ⟨hdim, ?_⟩
    have hu0_orth : bQ j0 ∈ Vᗮ := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨⟨i, hi⟩, rfl⟩
        rw [Finset.mem_Iio] at hi
        have hne : i ≠ j0 := ne_of_lt hi
        exact bQ.orthonormal.2 hne
      | zero => rw [inner_zero_left]
      | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
      | smul c x hx ih => rw [inner_smul_left, ih, mul_zero]
    have hu0_norm : ‖bQ j0‖ = 1 := bQ.orthonormal.1 j0
    have hu0_inner : inner ℝ (bQ j0) (Matrix.toEuclideanLin Q (bQ j0)) = gamma Q hQ j := by
      have h_ev : Matrix.toEuclideanLin Q (bQ j0) = (gamma Q hQ j) • bQ j0 :=
        hTQ.apply_eigenvectorBasis hn j0
      rw [h_ev, inner_smul_right, real_inner_self_eq_norm_sq, hu0_norm, one_pow, mul_one]
    refine ⟨⟨bQ j0, ⟨hu0_orth, hu0_norm⟩, hu0_inner⟩, ?_⟩
    rintro c ⟨u, ⟨hu_orth, hu_norm⟩, rfl⟩
    dsimp only
    have hu_zero : ∀ i < j0, (bQ.repr u).ofLp i = 0 := by
      intro i hi
      rw [OrthonormalBasis.repr_apply_apply]
      rw [Submodule.mem_orthogonal] at hu_orth
      have hmem : bQ i ∈ V := Submodule.subset_span ⟨⟨i, Finset.mem_Iio.mpr hi⟩, rfl⟩
      exact hu_orth (bQ i) hmem
    have h_le : (∑ i, hTQ.eigenvalues hn i * (bQ.repr u).ofLp i ^ 2) ≤
        ∑ i, hTQ.eigenvalues hn j0 * (bQ.repr u).ofLp i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i < j0
      · rw [hu_zero i hi]
        simp
      · have hj0_le : j0 ≤ i := not_lt.mp hi
        have h_anti := hTQ.eigenvalues_antitone hn hj0_le
        have : 0 ≤ (bQ.repr u).ofLp i ^ 2 := sq_nonneg _
        nlinarith
    have h_sum : (∑ i, hTQ.eigenvalues hn j0 * (bQ.repr u).ofLp i ^ 2) =
        hTQ.eigenvalues hn j0 * ∑ i, (bQ.repr u).ofLp i ^ 2 := by
      rw [← Finset.mul_sum]
    rw [h_inner_Q u]
    refine h_le.trans ?_
    rw [h_sum, h_norm_repr u hu_norm, mul_one, h_gammaQ]
  · -- Part 2: gamma Q hQ j is a lower bound for S
    intro c hc
    dsimp at hc
    rcases hc with ⟨V, hV_dim, hV_great⟩
    let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
      Submodule.span ℝ (Set.range (fun (i : Finset.Iic j0) => bQ i.val))
    have hli : LinearIndependent ℝ bQ := bQ.orthonormal.linearIndependent
    have hli_w : LinearIndependent ℝ (fun (i : Finset.Iic j0) => bQ i.val) :=
      hli.comp Subtype.val Subtype.val_injective
    have hdim_W : Module.finrank ℝ W = j.val + 1 := by
      rw [finrank_span_eq_card hli_w, Fintype.card_coe, Fin.card_Iic]
      rfl
    have h_dim_total : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    have hdim_Vorth : Module.finrank ℝ ↥Vᗮ = d - j.val := by
      have := Submodule.finrank_add_finrank_orthogonal V
      rw [h_dim_total, hV_dim] at this
      omega
    have hsum : Module.finrank ℝ ↥(W ⊔ Vᗮ) + Module.finrank ℝ ↥(W ⊓ Vᗮ) = (j.val + 1) + (d - j.val) := by
      rw [Submodule.finrank_sup_add_finrank_inf_eq, hdim_W, hdim_Vorth]
    have hle : Module.finrank ℝ ↥(W ⊔ Vᗮ) ≤ d := by
      have := Submodule.finrank_le (W ⊔ Vᗮ)
      rw [h_dim_total] at this
      exact this
    have hj_lt : j.val < d := j.isLt
    have h_pos : 0 < Module.finrank ℝ ↥(W ⊓ Vᗮ) := by omega
    have h_ne_bot : (W ⊓ Vᗮ) ≠ ⊥ := by
      intro hbot
      rw [hbot] at h_pos
      simp at h_pos
    rcases Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot with ⟨v, hv_mem, hv_ne⟩
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    let u : EuclideanSpace ℝ (Fin d) := ‖v‖⁻¹ • v
    have hu_norm : ‖u‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hv_norm_pos)]
    have hu_W : u ∈ W := Submodule.smul_mem W _ (Submodule.mem_inf.mp hv_mem).1
    have hu_Vorth : u ∈ Vᗮ := Submodule.smul_mem (Vᗮ) _ (Submodule.mem_inf.mp hv_mem).2
    have hu_zero_all : ∀ w ∈ W, ∀ i, j0 < i → (bQ.repr w).ofLp i = 0 := by
      intro w hw i hi
      rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
      induction hw using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨⟨k, hk⟩, rfl⟩
        rw [Finset.mem_Iic] at hk
        have hne : k ≠ i := ne_of_lt (lt_of_le_of_lt hk hi)
        exact bQ.orthonormal.2 hne
      | zero => rw [inner_zero_left]
      | add x y hx hy ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
      | smul a x hx ih => rw [inner_smul_left, ih, mul_zero]
    have hu_zero : ∀ i, j0 < i → (bQ.repr u).ofLp i = 0 := hu_zero_all u hu_W
    have h_le : (∑ i, hTQ.eigenvalues hn j0 * (bQ.repr u).ofLp i ^ 2) ≤
        ∑ i, hTQ.eigenvalues hn i * (bQ.repr u).ofLp i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ≤ j0
      · have h_anti := hTQ.eigenvalues_antitone hn hi
        have : 0 ≤ (bQ.repr u).ofLp i ^ 2 := sq_nonneg _
        nlinarith
      · have hi_gt : j0 < i := lt_of_not_ge hi
        rw [hu_zero i hi_gt]
        simp
    have h_sum : (∑ i, hTQ.eigenvalues hn j0 * (bQ.repr u).ofLp i ^ 2) =
        hTQ.eigenvalues hn j0 * ∑ i, (bQ.repr u).ofLp i ^ 2 := by
      rw [← Finset.mul_sum]
    have h_gamma_le_inner : gamma Q hQ j ≤ inner ℝ u (Matrix.toEuclideanLin Q u) := by
      rw [h_inner_Q u, ← h_gammaQ, ← mul_one (hTQ.eigenvalues hn j0), ← h_norm_repr u hu_norm, ← h_sum]
      exact h_le
    have hu_in_image : inner ℝ u (Matrix.toEuclideanLin Q u) ∈
        (fun u => inner ℝ u (Matrix.toEuclideanLin Q u)) '' {u | u ∈ Vᗮ ∧ ‖u‖ = 1} :=
      ⟨u, ⟨hu_Vorth, hu_norm⟩, rfl⟩
    have h_inner_le_c : inner ℝ u (Matrix.toEuclideanLin Q u) ≤ c :=
      hV_great.2 hu_in_image
    exact h_gamma_le_inner.trans h_inner_le_c

abbrev solution := @courant_fischer

end WainwrightHDS.EigPert

abbrev solution := @WainwrightHDS.EigPert.courant_fischer
