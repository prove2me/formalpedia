-- Prove2me | solution 1 for StochQuasiNewton.SQN.lbfgs_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:39:55.112969+00:00
-- url     : https://prove2.me/submissions/c1aa3251-a43b-485a-be21-3ff61eb1bd6f

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS

open scoped RealInnerProductSpace Matrix
open StochQuasiNewton.SQN

private theorem hessian_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → ℝ) (hF : ContDiff ℝ 2 F) (x : E) :
    (fderiv ℝ (gradient F) x).toLinearMap.IsSymmetric := by
  have hG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have he := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp x
    (hG x).hasFDerivAt
  change HasFDerivAt ((InnerProductSpace.toDual ℝ E) ∘ gradient F) _ x at he
  rw [toDual_comp_gradient] at he
  intro u v
  have hs := ((hF.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)).eq u v
  rw [he.fderiv] at hs
  change ⟪fderiv ℝ (gradient F) x u,v⟫ = ⟪fderiv ℝ (gradient F) x v,u⟫ at hs
  exact hs.trans (real_inner_comm _ _)

private theorem spectral_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ s, s ≠ 0 → a*‖s‖^2 < ⟪A s,s⟫ ∧ ⟪A s,s⟫ < b*‖s‖^2)
    (s : E) (hs : s ≠ 0) : a ≤ ‖A s‖^2/⟪A s,s⟫ ∧ ‖A s‖^2/⟪A s,s⟫ ≤ b := by
  let e := hA.eigenvalues (n := Module.finrank ℝ E) rfl
  let v := hA.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have hev : ∀ i, A (v i) = e i • v i := hA.apply_eigenvectorBasis rfl
  have he : ∀ i, a < e i ∧ e i < b := by
    intro i
    have hvne : v i ≠ 0 := by
      intro hz
      have hh := v.norm_eq_one i
      rw [hz,norm_zero] at hh
      norm_num at hh
    have hh := hbounds (v i) hvne
    simpa [hev, real_inner_smul_left, real_inner_self_eq_norm_sq, v.norm_eq_one] using hh
  have hi : ∀ i, ⟪v i,A s⟫ = e i*⟪v i,s⟫ := by
    intro i
    rw [← hA, hev, real_inner_smul_left]
  have hn : ‖A s‖^2 = ∑ i, (e i*⟪v i,s⟫)^2 := by
    rw [← v.sum_sq_inner_right]
    simp_rw [hi]
  have hid : ⟪A s,s⟫ = ∑ i, e i*⟪v i,s⟫^2 := by
    rw [← v.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (v i) (A s), hi]
    ring
  have hd : 0 < ⟪A s,s⟫ := lt_trans (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hs))) (hbounds s hs).1
  constructor
  · apply (le_div_iff₀ hd).mpr
    rw [hn,hid,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hmul := mul_nonneg (show 0 ≤ e i from (ha.trans (he i).1).le) (sub_nonneg.mpr (he i).1.le)
    have hh := mul_nonneg hmul (sq_nonneg ⟪v i,s⟫)
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    rw [hn,hid,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hmul := mul_nonneg (show 0 ≤ e i from (ha.trans (he i).1).le) (sub_nonneg.mpr (he i).2.le)
    have hh := mul_nonneg hmul (sq_nonneg ⟪v i,s⟫)
    nlinarith

private theorem curvature_pair_bounds_local {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (bH : ℕ)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (SH : Finset (Fin N)) (hSH : SH.card = bH) (wbar s y : EuclideanSpace ℝ (Fin n))
    (hs : s ≠ 0) (hy : y = subsampledHessian f SH wbar s) :
    (lam * ‖s‖ ^ 2 ≤ ⟪y, s⟫ ∧ ⟪y, s⟫ ≤ Lam * ‖s‖ ^ 2) ∧
      (lam ≤ ‖y‖ ^ 2 / ⟪y, s⟫ ∧ ‖y‖ ^ 2 / ⟪y, s⟫ ≤ Lam) := by
  subst y
  have hh := hHess SH hSH wbar
  refine ⟨⟨(hh s hs).1.le,(hh s hs).2.le⟩,?_⟩
  apply spectral_ratio (subsampledHessian f SH wbar).toLinearMap ?_ lam Lam hlam hh s hs
  intro u v
  simp only [subsampledHessian, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hessian_symmetric (f i) (hf i) wbar u v

private theorem direct_psd {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (s y : EuclideanSpace ℝ (Fin n)) (hy : 0 < ⟪y,s⟫) : (bfgsDirectUpdate s y B).PosSemidef := by
  let S := Matrix.vecMulVec s.ofLp s.ofLp
  let δ := dotProduct s.ofLp (B.mulVec s.ofLp)
  let r := 1/δ
  have hS : S.PosSemidef := by simpa [S] using Matrix.posSemidef_vecMulVec_self_star s.ofLp
  have hY : (Matrix.vecMulVec y.ofLp y.ofLp).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star y.ofLp
  have hlast : ((1/⟪y,s⟫) • Matrix.vecMulVec y.ofLp y.ofLp).PosSemidef := hY.smul (by positivity)
  have hmain : (B-r • (B*S*B)).PosSemidef := by
    by_cases hd : δ = 0
    · simpa [r,hd] using hB
    let C : Matrix (Fin n) (Fin n) ℝ := 1-r • (S*B)
    have hCH : Cᴴ = 1-r • (B*S) := by
      simp only [C,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul,
        star_trivial,Matrix.conjTranspose_mul,hB.isHermitian.eq,hS.isHermitian.eq]
    have hSBS : S*B*S = δ • S := by
      dsimp [S,δ]
      rw [Matrix.vecMulVec_mul,Matrix.vecMulVec_mul_vecMulVec,← Matrix.dotProduct_mulVec,
        Matrix.vecMulVec_smul]
    have hquad : B*S*B*S*B = δ • (B*S*B) := by
      calc
        B*S*B*S*B = B*(S*B*S)*B := by noncomm_ring
        _ = δ • (B*S*B) := by rw [hSBS]; simp [smul_mul_assoc,mul_smul_comm]
    have he : Cᴴ*B*C = B-r • (B*S*B) := by
      rw [hCH]
      dsimp [C]
      simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
        smul_mul_assoc,mul_smul_comm,smul_smul]
      simp only [← Matrix.mul_assoc]
      rw [hquad]
      simp only [smul_smul]
      have hr : r*δ = 1 := by dsimp [r]; field_simp
      simp [hr]
    rw [← he]
    exact hB.conjTranspose_mul_mul_same C
  exact hmain.add hlast

private theorem direct_trace {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosSemidef)
    (s y : EuclideanSpace ℝ (Fin n)) :
    Matrix.trace (bfgsDirectUpdate s y B) ≤ Matrix.trace B + ‖y‖^2/⟪y,s⟫ := by
  have hδ : 0 ≤ dotProduct s.ofLp (B.mulVec s.ofLp) := by
    simpa using hB.dotProduct_mulVec_nonneg s.ofLp
  have hS : (Matrix.vecMulVec s.ofLp s.ofLp).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star s.ofLp
  have hBSB : (B*Matrix.vecMulVec s.ofLp s.ofLp*B).PosSemidef := by
    simpa only [hB.isHermitian.eq] using hS.mul_mul_conjTranspose_same B
  have hr := (hBSB.smul (one_div_nonneg.mpr hδ)).trace_nonneg
  have hnorm : dotProduct y.ofLp y.ofLp = ‖y‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using real_inner_self_eq_norm_sq y
  simp only [bfgsDirectUpdate,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,
    Matrix.trace_vecMulVec,smul_eq_mul,hnorm]
  simp only [Matrix.trace_smul,smul_eq_mul] at hr
  simp only [div_eq_mul_inv,one_mul] at hr ⊢
  nlinarith

theorem solution {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (bH : ℕ)
    (hbH : 1 ≤ bH)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (M t : ℕ) (hM : 1 ≤ M) (ht : 1 ≤ t) (s y : ℕ → EuclideanSpace ℝ (Fin n))
    (hpairs : ∀ j, t - min t M < j → j ≤ t →
      s j ≠ 0 ∧ ∃ (SH : Finset (Fin N)) (wbar : EuclideanSpace ℝ (Fin n)),
        SH.card = bH ∧ y j = subsampledHessian f SH wbar (s j)) :
    Matrix.trace (lbfgsDirectStage M t s y (min t M)) ≤
      Matrix.trace (lbfgsDirectStage M t s y 0) + (min t M : ℝ)*Lam := by
  have hmpos : 0 < min t M := by omega
  have hp : ∀ j, t-min t M < j → j ≤ t → 0 < ⟪y j,s j⟫ ∧ ‖y j‖^2/⟪y j,s j⟫ ≤ Lam := by
    intro j hj hjt
    obtain ⟨hs,SH,w,hSH,hy⟩ := hpairs j hj hjt
    have hc := curvature_pair_bounds_local f hf lam Lam hlam hLam bH hHess SH hSH w (s j) (y j) hs hy
    exact ⟨lt_of_lt_of_le (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hs))) hc.1.1,hc.2.2⟩
  have hp0 := (hp t (by omega) le_rfl).1
  have hB0 : (lbfgsDirectStage M t s y 0).PosSemidef := by
    dsimp [lbfgsDirectStage]
    apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
    apply div_nonneg
    · exact real_inner_self_nonneg
    · simpa only [real_inner_comm] using hp0.le
  have hall : ∀ i, i ≤ min t M → (lbfgsDirectStage M t s y i).PosSemidef ∧
      Matrix.trace (lbfgsDirectStage M t s y i) ≤ Matrix.trace (lbfgsDirectStage M t s y 0)+(i:ℝ)*Lam := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hB0,by simp⟩
    | succ i ih =>
      intro hi
      obtain ⟨hpsd,htrace⟩ := ih (by omega)
      let j := t-min t M+1+i
      have hj : t-min t M < j := by dsimp [j]; omega
      have hjt : j ≤ t := by dsimp [j]; omega
      have hcurv := hp j hj hjt
      change (bfgsDirectUpdate (s j) (y j) (lbfgsDirectStage M t s y i)).PosSemidef ∧ _
      refine ⟨direct_psd _ hpsd _ _ hcurv.1,?_⟩
      have hh := direct_trace (lbfgsDirectStage M t s y i) hpsd (s j) (y j)
      change Matrix.trace (bfgsDirectUpdate (s j) (y j) (lbfgsDirectStage M t s y i)) ≤ _
      push_cast
      linarith [hcurv.2]
  simpa only [Nat.cast_min] using (hall (min t M) le_rfl).2
