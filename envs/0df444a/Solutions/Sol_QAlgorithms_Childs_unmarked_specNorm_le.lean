-- Prove2me | solution 1 for QAlgorithms.Childs.unmarked_specNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:16:41.808495+00:00
-- url     : https://prove2.me/submissions/2f14cb34-65a9-4917-b599-d99d99e9a743

import Definitions.Def_QAlgorithms_Defs_Walk
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open QAlgorithms Matrix
open scoped BigOperators RealInnerProductSpace Norms.L2Operator

private lemma sum_extension {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (f : {i // p i} → ℝ) :
    (∑ i, if hi : p i then f ⟨i, hi⟩ else 0) = ∑ i, f i := by
  exact Finset.sum_congr_set {i | p i} _ f
    (by intro i hi; exact dif_pos hi)
    (by intro i hi; exact dif_neg hi)

private lemma herm_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, |hA.eigenvalues i| ≤ c) : specNorm A ≤ c := by
  change ‖A‖ ≤ c
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).mpr fun i => by simpa using h i

private lemma spectral_coords {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (w : EuclideanSpace ℝ ι) (i : ι) :
    hA.eigenvectorBasis.repr (A.toEuclideanLin w) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr w i := by
  rw [hA.eigenvectorBasis.repr_apply_apply, hA.eigenvectorBasis.repr_apply_apply]
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [← hs]
  have he : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply PiLp.ext
    intro k
    exact congrFun (hA.mulVec_eigenvectorBasis i) k
  rw [he, real_inner_smul_left]

private lemma spectral_quad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (w : EuclideanSpace ℝ ι) :
    ⟪w, A.toEuclideanLin w⟫ =
      ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr w i) ^ 2 := by
  rw [← hA.eigenvectorBasis.repr.inner_map_map]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, spectral_coords]
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option maxHeartbeats 1600000 in
theorem solution {N : ℕ} (hN : 2 ≤ N) (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : IsColumnStochastic P) (hsymm : P.IsHermitian) (M : Finset (Fin N)) (δ ϵ : ℝ)
    (hδ : 0 < δ) (hϵ : 0 < ϵ)
    (hgap : (Finset.univ.filter fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|).card ≤ 1)
    (hM : ϵ * (N : ℝ) ≤ (M.card : ℝ)) :
    specNorm (unmarkedSubmatrix P M) ≤ 1 - δ * ϵ := by
  classical
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have hd : δ ≤ 1 := by
    by_contra! hd
    have he : (Finset.univ.filter fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|) =
        Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact lt_of_lt_of_le (by linarith) (abs_nonneg _)
    rw [he, Finset.card_univ, Fintype.card_fin] at hgap
    omega
  have hmcard : M.card ≤ N := by simpa using M.card_le_univ
  have heps : ϵ ≤ 1 := by
    have : (M.card : ℝ) ≤ N := by exact_mod_cast hmcard
    nlinarith only [hM, this, hNr]
  have hc : 0 ≤ 1 - δ * ϵ := by
    have hh := mul_le_mul_of_nonneg_left heps hδ.le
    nlinarith only [hh, hd]
  let b := hsymm.eigenvectorBasis
  let T := P.toEuclideanLin
  let u : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun _ => 1)
  have hu : T u = u := by
    apply PiLp.ext
    intro j
    change (∑ k, P j k * 1) = 1
    simp only [mul_one]
    convert hP.2 j using 1
    apply Finset.sum_congr rfl
    intro k _
    exact hsymm.eq.symm |> fun hh => by simpa using congrFun (congrFun hh j) k
  have hun : ‖u‖ ^ 2 = (N : ℝ) := by
    simp [u, PiLp.norm_sq_eq_of_L2]
  have hunz : u ≠ 0 := by
    intro hz
    rw [hz] at hun
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hun
    linarith
  obtain ⟨i₀, hi₀⟩ : ∃ i, b.repr u i ≠ 0 := by
    by_contra! h
    apply hunz
    apply b.repr.injective
    ext i
    simpa using h i
  have hcoord (i) : hsymm.eigenvalues i * b.repr u i = b.repr u i := by
    rw [← spectral_coords P hsymm u i]
    exact congrArg (fun w => b.repr w i) hu
  have hlam : hsymm.eigenvalues i₀ = 1 := by
    have := hcoord i₀
    rcases mul_eq_zero.mp (show (hsymm.eigenvalues i₀ - 1) * b.repr u i₀ = 0 by nlinarith) with h | h
    · linarith
    · exact (hi₀ h).elim
  have hother (i) (hi : i ≠ i₀) : |hsymm.eigenvalues i| ≤ 1 - δ := by
    by_contra! hh
    have hmem : i₀ ∈ Finset.univ.filter (fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|) := by
      simp [hlam, hδ]
    have hmem' : i ∈ Finset.univ.filter (fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|) := by
      simp [hh]
    have hsub : ({i, i₀} : Finset (Fin N)) ⊆
        Finset.univ.filter (fun i : Fin N => 1 - δ < |hsymm.eigenvalues i|) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hmem'
      · exact hmem
    have htwo := Finset.card_le_card hsub
    rw [Finset.card_pair hi] at htwo
    omega
  have hzero (i) (hi : i ≠ i₀) : b.repr u i = 0 := by
    have hb := hother i hi
    have hh := hcoord i
    have hl : hsymm.eigenvalues i < 1 := lt_of_le_of_lt (le_trans (le_abs_self _) hb) (by linarith)
    have he : (hsymm.eigenvalues i - 1) * b.repr u i = 0 := by
      nlinarith only [hh]
    rcases mul_eq_zero.mp he with he | he
    · linarith only [he, hl]
    · exact he
  have hut : (b.repr u i₀) ^ 2 = (N : ℝ) := by
    have hn := b.sum_sq_inner_right u
    simp only [← b.repr_apply_apply] at hn
    rw [← hun, ← hn]
    symm
    apply Finset.sum_eq_single i₀
    · intro i _ hi
      rw [hzero i hi]; simp
    · simp
  have hpair (w : EuclideanSpace ℝ (Fin N)) :
      ⟪u, w⟫ = b.repr u i₀ * b.repr w i₀ := by
    rw [← b.repr.inner_map_map]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_eq_single i₀ (by intro i _ hi; rw [hzero i hi]; simp) (by simp)]
    ring
  have hquad (w : EuclideanSpace ℝ (Fin N)) :
      |⟪w, T w⟫| ≤ (1 - δ) * ‖w‖ ^ 2 + δ * (b.repr w i₀) ^ 2 := by
    rw [spectral_quad P hsymm w]
    calc
      |∑ i, hsymm.eigenvalues i * (b.repr w i) ^ 2| ≤
          ∑ i, |hsymm.eigenvalues i * (b.repr w i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ((1 - δ) * (b.repr w i) ^ 2 +
          if i = i₀ then δ * (b.repr w i₀) ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg (b.repr w i))]
        by_cases hi : i = i₀
        · subst i
          simp only [hlam, abs_one, one_mul, ↓reduceIte]
          ring_nf; rfl
        · simp only [hi, ↓reduceIte, add_zero]
          exact mul_le_mul_of_nonneg_right (hother i hi) (sq_nonneg _)
      _ = (1 - δ) * ‖w‖ ^ 2 + δ * (b.repr w i₀) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [show ∑ i, (b.repr w i) ^ 2 = ‖w‖ ^ 2 by
          simpa only [b.repr_apply_apply] using b.sum_sq_inner_right w]
  let U := {v : Fin N // v ∉ M}
  let A := unmarkedSubmatrix P M
  have hA : A.IsHermitian := hsymm.submatrix Subtype.val
  apply herm_norm_bound A hA _ hc
  intro i
  let v := hA.eigenvectorBasis i
  let w : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2
    (fun j => if hj : j ∉ M then v ⟨j, hj⟩ else 0)
  have hwn : ‖w‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [w, Real.norm_eq_abs, sq_abs]
    have heq : (∑ j : Fin N, (if hj : j ∉ M then v ⟨j, hj⟩ else 0) ^ 2) =
        ∑ j : U, v j ^ 2 := by
      simp_rw [dite_pow, zero_pow (by decide : 2 ≠ 0)]
      exact sum_extension (fun j => j ∉ M) (fun j => v j ^ 2)
    rw [heq]
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : U => ℝ) v
    simp only [Real.norm_eq_abs, sq_abs] at hn
    rw [← hn]
    simp [v, hA.eigenvectorBasis.orthonormal.1]
  have hwq : ⟪w, T w⟫ = hA.eigenvalues i := by
    change (∑ j : Fin N, (T w) j * w j) = _
    have hTw (j : U) : (T w) j = (A.toEuclideanLin v) j := by
      change (∑ k : Fin N, P j k * w k) = ∑ k : U, A j k * v k
      simp only [w, mul_dite, mul_zero]
      exact sum_extension (fun k : Fin N => k ∉ M) (fun k => P j k * v k)
    have hsplit : (∑ j : Fin N, (T w) j * w j) =
        ∑ j : U, (A.toEuclideanLin v) j * v j := by
      simp only [w, mul_dite, mul_zero]
      rw [sum_extension (fun k : Fin N => k ∉ M) (fun k => (T w) k * v k)]
      apply Finset.sum_congr rfl
      intro j _
      rw [← hTw]
    rw [hsplit]
    change ⟪v, A.toEuclideanLin v⟫ = _
    have hev : A.toEuclideanLin v = hA.eigenvalues i • v := by
      apply PiLp.ext
      intro j
      exact congrFun (hA.mulVec_eigenvectorBasis i) j
    rw [hev, inner_smul_right, real_inner_self_eq_norm_sq]
    simp [v, hA.eigenvectorBasis.orthonormal.1]
  have hcs : ⟪u, w⟫ ^ 2 ≤ ((N : ℝ) - M.card) := by
    let z : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun j => if j ∉ M then 1 else 0)
    have hip : ⟪u, w⟫ = ⟪z, w⟫ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∉ M <;> simp [u, z, w, hj]
    have hzn : ‖z‖ ^ 2 = (N : ℝ) - M.card := by
      simp only [z, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
      simp only [apply_ite abs, abs_one, abs_zero, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      have hf : (Finset.univ.filter fun j : Fin N => j ∉ M) = Finset.univ \ M := by ext; simp
      rw [hf, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub hmcard]
    have hh := real_inner_mul_inner_self_le z w
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hzn, hwn] at hh
    rw [hip]
    nlinarith only [hh]
  have hweight : (b.repr w i₀) ^ 2 ≤ 1 - ϵ := by
    rw [hpair] at hcs
    rw [mul_pow, hut] at hcs
    apply (mul_le_mul_iff_right₀ hNr).mp
    nlinarith only [hcs, hM]
  have hh := hquad w
  rw [hwq, hwn] at hh
  nlinarith only [hh, mul_le_mul_of_nonneg_left hweight (le_of_lt hδ)]
