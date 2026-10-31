-- Prove2me | solution 1 for WainwrightHDS.EigPert.weyl_eigenvalue_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:13:13.713146+00:00
-- url     : https://prove2.me/submissions/788448d5-56ec-446f-9e85-80481de52e1e

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2
import Definitions.Def_WainwrightHDS_EigPert_gamma
import Theorems.Thm_WainwrightHDS_EigPert_courant_fischer

open WainwrightHDS.EigPert Matrix

lemma inner_R_le_inner_Q_add {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    inner ℝ u (Matrix.toEuclideanLin R u) ≤ inner ℝ u (Matrix.toEuclideanLin Q u) + opNorm2 (Q - R) := by
  have hlin : Matrix.toEuclideanLin (R - Q) u = Matrix.toEuclideanLin R u - Matrix.toEuclideanLin Q u := by
    rw [map_sub, LinearMap.sub_apply]
  have hinner : inner ℝ u (Matrix.toEuclideanLin R u) - inner ℝ u (Matrix.toEuclideanLin Q u) =
      inner ℝ u (Matrix.toEuclideanLin (R - Q) u) := by
    rw [← inner_sub_right, ← hlin]
  have hle1 : inner ℝ u (Matrix.toEuclideanLin (R - Q) u) ≤ ‖Matrix.toEuclideanLin (R - Q) u‖ := by
    have := real_inner_le_norm u (Matrix.toEuclideanLin (R - Q) u)
    rwa [hu, one_mul] at this
  have hle2 : ‖Matrix.toEuclideanLin (R - Q) u‖ ≤ opNorm2 (R - Q) := by
    have := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (R - Q)) u
    change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (R - Q) u‖ ≤ _ at this
    rwa [hu, mul_one] at this
  have hsymm : opNorm2 (R - Q) = opNorm2 (Q - R) := by
    have hneg : R - Q = - (Q - R) := (neg_sub Q R).symm
    rw [hneg]
    dsimp [opNorm2]
    rw [map_neg, norm_neg]
  linarith

lemma gamma_sub_le_of_zero {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) (j : Fin d) (hj : j.val = 0) :
    gamma R hR j - gamma Q hQ j ≤ opNorm2 (Q - R) := by
  let hTR := isSymmetric_toEuclideanLin_iff.mpr hR
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Fintype.card (Fin d) := finrank_euclideanSpace
  let i0 : Fin (Fintype.card (Fin d)) := Fin.cast (Fintype.card_fin d).symm j
  let u0 := (hTR.eigenvectorBasis hn) i0
  have hu0 : ‖u0‖ = 1 := (hTR.eigenvectorBasis hn).orthonormal.1 i0
  have h_inner_R : inner ℝ u0 (toEuclideanLin R u0) = gamma R hR j := by
    have h_ev : toEuclideanLin R u0 = (gamma R hR j) • u0 := hTR.apply_eigenvectorBasis hn i0
    rw [h_ev, inner_smul_right, real_inner_self_eq_norm_sq, hu0, one_pow, mul_one]
  have h_le_add : inner ℝ u0 (toEuclideanLin R u0) ≤ inner ℝ u0 (toEuclideanLin Q u0) + opNorm2 (Q - R) :=
    inner_R_le_inner_Q_add Q R u0 hu0
  let hTQ := isSymmetric_toEuclideanLin_iff.mpr hQ
  let bQ := hTQ.eigenvectorBasis hn
  have h_inner_Q : inner ℝ u0 (toEuclideanLin Q u0) = inner ℝ (bQ.repr u0) (bQ.repr (toEuclideanLin Q u0)) := by
    rw [bQ.repr.inner_map_map]
  have h_repr_T : ∀ i, (bQ.repr (toEuclideanLin Q u0)).ofLp i = hTQ.eigenvalues hn i * (bQ.repr u0).ofLp i := by
    intro i
    exact hTQ.eigenvectorBasis_apply_self_apply hn u0 i
  have h_euc_inner : inner ℝ (bQ.repr u0) (bQ.repr (toEuclideanLin Q u0)) =
      ∑ i, hTQ.eigenvalues hn i * (bQ.repr u0).ofLp i ^ 2 := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_repr_T i, Real.inner_apply]
    ring
  have h_le : (∑ i, hTQ.eigenvalues hn i * (bQ.repr u0).ofLp i ^ 2) ≤
      ∑ i, hTQ.eigenvalues hn i0 * (bQ.repr u0).ofLp i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi0_le : i0 ≤ i := by
      change (Fin.cast (Fintype.card_fin d).symm j).val ≤ i.val
      rw [Fin.val_cast, hj]
      exact Nat.zero_le i.val
    have h_anti := hTQ.eigenvalues_antitone hn hi0_le
    have : 0 ≤ (bQ.repr u0).ofLp i ^ 2 := sq_nonneg _
    nlinarith
  have h_sum : (∑ i, hTQ.eigenvalues hn i0 * (bQ.repr u0).ofLp i ^ 2) =
      hTQ.eigenvalues hn i0 * ∑ i, (bQ.repr u0).ofLp i ^ 2 := by
    rw [← Finset.mul_sum]
  have h_norm : (∑ i, (bQ.repr u0).ofLp i ^ 2) = 1 := by
    have h_norm_repr : ‖bQ.repr u0‖ ^ 2 = 1 := by
      rw [LinearIsometryEquiv.norm_map, hu0, one_pow]
    rw [PiLp.norm_sq_eq_of_L2] at h_norm_repr
    have h_simp : (∑ i, ‖(bQ.repr u0).ofLp i‖ ^ 2) = ∑ i, (bQ.repr u0).ofLp i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_simp] at h_norm_repr
    exact h_norm_repr
  have h_gammaQ : hTQ.eigenvalues hn i0 = gamma Q hQ j := rfl
  have h_inner_Q_le : inner ℝ u0 (toEuclideanLin Q u0) ≤ gamma Q hQ j := by
    rw [h_inner_Q, h_euc_inner]
    refine h_le.trans ?_
    rw [h_sum, h_norm, mul_one, h_gammaQ]
  linarith

lemma gamma_sub_le_of_pos {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) (j : Fin d) (hj : 1 ≤ j.val) :
    gamma R hR j - gamma Q hQ j ≤ opNorm2 (Q - R) := by
  have hcfQ := (courant_fischer Q hQ j hj).1
  rcases hcfQ with ⟨V, hV, hQ_greatest⟩
  let S := {u : EuclideanSpace ℝ (Fin d) | u ∈ Vᗮ ∧ ‖u‖ = 1}
  rcases hQ_greatest.1 with ⟨u0, hu0_S, -⟩
  have hS_nonempty : S.Nonempty := ⟨u0, hu0_S⟩
  have hS_compact : IsCompact S := by
    have hs : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := isCompact_sphere 0 1
    have hc : IsClosed (Vᗮ : Set (EuclideanSpace ℝ (Fin d))) := Submodule.closed_of_finiteDimensional Vᗮ
    have h_eq : S = (Vᗮ : Set (EuclideanSpace ℝ (Fin d))) ∩ Metric.sphere 0 1 := by
      ext u
      dsimp [S]
      simp
    rw [h_eq]
    exact IsCompact.inter_left hs hc
  have hfR_cont : Continuous (fun u : EuclideanSpace ℝ (Fin d) => inner ℝ u (Matrix.toEuclideanLin R u)) := by
    have heq : (fun u : EuclideanSpace ℝ (Fin d) => inner ℝ u (Matrix.toEuclideanLin R u)) =
        (fun u => inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) R u)) := rfl
    rw [heq]
    exact continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) R).continuous
  have h_image_compact : IsCompact ((fun u => inner ℝ u (Matrix.toEuclideanLin R u)) '' S) :=
    hS_compact.image hfR_cont
  have h_image_nonempty : ((fun u => inner ℝ u (Matrix.toEuclideanLin R u)) '' S).Nonempty :=
    hS_nonempty.image _
  obtain ⟨c_R, hc_R_greatest⟩ := IsCompact.exists_isGreatest h_image_compact h_image_nonempty
  have hc_R_mem : c_R ∈ {c : ℝ | ∃ V' : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V' = j.val ∧
      IsGreatest ((fun u => inner ℝ u (Matrix.toEuclideanLin R u)) '' {u | u ∈ V'ᗮ ∧ ‖u‖ = 1}) c} :=
    ⟨V, hV, hc_R_greatest⟩
  have hR_le_cR : gamma R hR j ≤ c_R := (courant_fischer R hR j hj).2 hc_R_mem
  obtain ⟨u_R, hu_R_S, hu_R_eq⟩ := hc_R_greatest.1
  have hu_R_norm : ‖u_R‖ = 1 := hu_R_S.2
  have hu_R_inner_le : inner ℝ u_R (Matrix.toEuclideanLin R u_R) ≤
      inner ℝ u_R (Matrix.toEuclideanLin Q u_R) + opNorm2 (Q - R) :=
    inner_R_le_inner_Q_add Q R u_R hu_R_norm
  have hu_R_Q_le : inner ℝ u_R (Matrix.toEuclideanLin Q u_R) ≤ gamma Q hQ j := by
    have : inner ℝ u_R (Matrix.toEuclideanLin Q u_R) ∈ (fun u => inner ℝ u (Matrix.toEuclideanLin Q u)) '' S :=
      ⟨u_R, hu_R_S, rfl⟩
    exact hQ_greatest.2 this
  linarith

lemma gamma_sub_le {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) (j : Fin d) :
    gamma R hR j - gamma Q hQ j ≤ opNorm2 (Q - R) := by
  rcases Nat.eq_zero_or_pos j.val with hj | hj
  · exact gamma_sub_le_of_zero Q R hQ hR j hj
  · exact gamma_sub_le_of_pos Q R hQ hR j hj

theorem solution {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) :
    ∀ j : Fin d, |gamma Q hQ j - gamma R hR j| ≤ opNorm2 (Q - R) := by
  intro j
  rw [abs_sub_le_iff]
  constructor
  · have h1 := gamma_sub_le R Q hR hQ j
    have hsymm : opNorm2 (R - Q) = opNorm2 (Q - R) := by
      have hneg : R - Q = - (Q - R) := (neg_sub Q R).symm
      rw [hneg]
      dsimp [opNorm2]
      rw [map_neg, norm_neg]
    rwa [hsymm] at h1
  · exact gamma_sub_le Q R hQ hR j
