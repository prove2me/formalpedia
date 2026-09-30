-- Prove2me | solution 1 for StochQuasiNewton.SQN.hessian_approx_eigenvalue_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:55:58.192028+00:00
-- url     : https://prove2.me/submissions/e9d92008-657b-4d06-ab67-4c118e5ea670

import Definitions.Def_StochQuasiNewton_SQN_Algorithm
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

private noncomputable def quad {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : ℝ := dotProduct v.ofLp (H.mulVec v.ofLp)

private theorem inv_quad {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (s y v : EuclideanSpace ℝ (Fin n)) :
    quad (bfgsInverseUpdate s y H) v =
      quad H (v - (⟪s,v⟫/⟪y,s⟫) • y) + ⟪s,v⟫^2/⟪y,s⟫ := by
  let r := 1/⟪y,s⟫
  let A : Matrix (Fin n) (Fin n) ℝ := 1-r • Matrix.vecMulVec s.ofLp y.ofLp
  let D : Matrix (Fin n) (Fin n) ℝ := 1-r • Matrix.vecMulVec y.ofLp s.ofLp
  let w := v - (⟪s,v⟫/⟪y,s⟫) • y
  have hleft : Matrix.vecMul v.ofLp A = w.ofLp := by
    simp only [A,Matrix.vecMul_sub,Matrix.vecMul_one,Matrix.vecMul_smul,Matrix.vecMul_vecMulVec]
    simp [w,r,EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm,div_eq_mul_inv,smul_smul,mul_comm]
  have hright : D.mulVec v.ofLp = w.ofLp := by
    simp only [D,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,Matrix.vecMulVec_mulVec]
    simp [w,r,EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm,div_eq_mul_inv,smul_smul,mul_comm]
  change dotProduct v.ofLp ((A*H*D+r • Matrix.vecMulVec s.ofLp s.ofLp).mulVec v.ofLp) = _
  rw [Matrix.add_mulVec,dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,hleft,hright]
  congr 1
  simp only [Matrix.smul_mulVec,Matrix.vecMulVec_mulVec,dotProduct_smul]
  simp [r,EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm,smul_eq_mul]
  ring

private theorem norm_sum_sq {E : Type*} [NormedAddCommGroup E] (x z : E) :
    ‖x+z‖^2 ≤ 2*‖x‖^2+2*‖z‖^2 := by
  have ht := norm_add_le x z
  nlinarith [norm_nonneg (x+z),norm_nonneg x,norm_nonneg z,sq_nonneg (‖x‖-‖z‖)]

private theorem inverse_bounds_step {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (s y : EuclideanSpace ℝ (Fin n)) (lam Lam K C : ℝ)
    (hlam : 0 < lam) (hLam : 0 < Lam) (hK : 1 ≤ K) (hLK : Lam ≤ K)
    (hC : 2 ≤ C) (hC' : 2+2*Lam/lam+1/lam ≤ C)
    (hcurv : 0 < ⟪y,s⟫) (hs : lam*‖s‖^2 ≤ ⟪y,s⟫) (hy : ‖y‖^2 ≤ Lam*⟪y,s⟫)
    (hH : ∀ v, ‖v‖^2 ≤ K*quad H v ∧ quad H v ≤ K*‖v‖^2) :
    ∀ v, ‖v‖^2 ≤ (C*K)*quad (bfgsInverseUpdate s y H) v ∧
      quad (bfgsInverseUpdate s y H) v ≤ (C*K)*‖v‖^2 := by
  intro v
  let σ := ⟪y,s⟫
  let r := ⟪s,v⟫
  let z := (r/σ) • y
  let w := v-z
  let R := r^2/σ
  have hσ : 0 < σ := hcurv
  have hKpos : 0 < K := by linarith
  have hR : 0 ≤ R := div_nonneg (sq_nonneg _) hσ.le
  have hcs : r^2 ≤ ‖s‖^2*‖v‖^2 := by
    have hc := abs_real_inner_le_norm s v
    have hh := sq_le_sq₀ (abs_nonneg ⟪s,v⟫) (mul_nonneg (norm_nonneg s) (norm_nonneg v)) |>.mpr hc
    simpa [r,sq_abs,mul_pow] using hh
  have hRbound : R ≤ ‖v‖^2/lam := by
    apply (le_div_iff₀ hlam).mpr
    dsimp [R]
    rw [div_mul_eq_mul_div,div_le_iff₀ hσ]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖v‖),mul_le_mul_of_nonneg_left hcs hlam.le]
  have hz : ‖z‖^2 ≤ Lam*R := by
    have he : ‖z‖^2 = (r/σ)^2*‖y‖^2 := by simp only [z,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [he]
    calc
      _ ≤ (r/σ)^2*(Lam*σ) := mul_le_mul_of_nonneg_left hy (sq_nonneg _)
      _ = Lam*R := by dsimp [R]; field_simp <;> ring
  have hw : ‖w‖^2 ≤ (2+2*Lam/lam)*‖v‖^2 := by
    have hh := norm_sum_sq v (-z)
    simp only [norm_neg,← sub_eq_add_neg] at hh
    have hmul := mul_le_mul_of_nonneg_left hRbound (by positivity : 0 ≤ Lam)
    dsimp [w]
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith
  have hvw : ‖v‖^2 ≤ 2*‖w‖^2+2*Lam*R := by
    have hh := norm_sum_sq w z
    have he : w+z=v := by dsimp [w]; abel
    rw [he] at hh
    linarith
  have hq := hH w
  have hqnonneg : 0 ≤ quad H w := by nlinarith [sq_nonneg ‖w‖]
  have he : quad (bfgsInverseUpdate s y H) v = quad H w + R := inv_quad H s y v
  rw [he]
  constructor
  · have hl : ‖v‖^2 ≤ 2*K*(quad H w+R) := by
      nlinarith [mul_le_mul_of_nonneg_right hLK hR]
    nlinarith [mul_le_mul_of_nonneg_right hC (mul_nonneg hKpos.le (add_nonneg hqnonneg hR))]
  · have hup := mul_le_mul_of_nonneg_left hw hKpos.le
    have hrk : R ≤ K*(‖v‖^2/lam) := le_trans hRbound (le_mul_of_one_le_left (by positivity) hK)
    have hcc := mul_le_mul_of_nonneg_right hC' (mul_nonneg hKpos.le (sq_nonneg ‖v‖))
    simp only [div_eq_mul_inv] at hup hrk hcc
    nlinarith

private theorem inverse_psd {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosSemidef)
    (s y : EuclideanSpace ℝ (Fin n)) (hy : 0 < ⟪y,s⟫) : (bfgsInverseUpdate s y H).PosSemidef := by
  let A : Matrix (Fin n) (Fin n) ℝ := 1-(1/⟪y,s⟫) • Matrix.vecMulVec s.ofLp y.ofLp
  have hs : (Matrix.vecMulVec s.ofLp s.ofLp).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star s.ofLp
  convert (hH.mul_mul_conjTranspose_same A).add (hs.smul (one_div_nonneg.mpr hy.le)) using 1
  simp [bfgsInverseUpdate,A,Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_vecMulVec]

private theorem quad_scalar {n : ℕ} (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    quad (a • (1 : Matrix (Fin n) (Fin n) ℝ)) v = a*‖v‖^2 := by
  have hn : dotProduct v.ofLp v.ofLp = ‖v‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using real_inner_self_eq_norm_sq v
  simp [quad,Matrix.smul_mulVec,dotProduct_smul,hn]

private theorem strict_matrix_bounds {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosSemidef) (K : ℝ) (hK : 0 < K)
    (hb : ∀ v, ‖v‖^2 ≤ K*quad H v ∧ quad H v ≤ K*‖v‖^2) :
    (H - (1/(2*K)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
    ((2*K) • (1 : Matrix (Fin n) (Fin n) ℝ)-H).PosDef := by
  have hId (a : ℝ) : (a • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  constructor
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos (hH.isHermitian.sub (hId _))
    intro v hv
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hx : x ≠ 0 := by simpa [x] using hv
    have hp : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    have hh := (hb x).1
    have hn : dotProduct v v = ‖x‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using real_inner_self_eq_norm_sq x
    have he : K*((1/(2*K))*‖x‖^2) = ‖x‖^2/2 := by field_simp <;> ring
    simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,
      Matrix.one_mulVec,dotProduct_smul,smul_eq_mul,hn]
    change 0 < quad H x - (1/(2*K))*‖x‖^2
    nlinarith
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos ((hId _).sub hH.isHermitian)
    intro v hv
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hx : x ≠ 0 := by simpa [x] using hv
    have hp : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    have hh := (hb x).2
    have hn : dotProduct v v = ‖x‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using real_inner_self_eq_norm_sq x
    simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,
      Matrix.one_mulVec,dotProduct_smul,smul_eq_mul,hn]
    change 0 < (2*K)*‖x‖^2-quad H x
    nlinarith

private theorem memory_bounds {n : ℕ} (lam Lam C : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hC2 : 2 ≤ C) (hLC : Lam ≤ C) (hlC : 1/lam ≤ C)
    (hCrec : 2+2*Lam/lam+1/lam ≤ C) (M t : ℕ) (hM : 1 ≤ M) (ht : 1 ≤ t)
    (s y : ℕ → EuclideanSpace ℝ (Fin n))
    (hp : ∀ j, t-min t M < j → j ≤ t →
      0 < ⟪y j,s j⟫ ∧ lam*‖s j‖^2 ≤ ⟪y j,s j⟫ ∧
        lam ≤ ‖y j‖^2/⟪y j,s j⟫ ∧ ‖y j‖^2/⟪y j,s j⟫ ≤ Lam) :
    (lbfgsMatrix M t s y - (1/(2*C^(M+1))) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
    ((2*C^(M+1)) • (1 : Matrix (Fin n) (Fin n) ℝ)-lbfgsMatrix M t s y).PosDef := by
  have hC : 0 < C := by linarith
  have hCone : 1 ≤ C := by linarith
  have hc0 := hp t (by omega) le_rfl
  have hy0 : y t ≠ 0 := by intro he; simp [he] at hc0
  have hypos : 0 < ‖y t‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy0)
  let a := ⟪y t,s t⟫/‖y t‖^2
  have hapos : 0 < a := div_pos hc0.1 hypos
  have ha1 : 1 ≤ C*a := by
    dsimp [a]
    rw [← mul_div_assoc,le_div_iff₀ hypos]
    have hh := (div_le_iff₀ hc0.1).mp hc0.2.2.2
    nlinarith [mul_le_mul_of_nonneg_right hLC hc0.1.le]
  have ha2 : a ≤ C := by
    apply le_trans (b := 1/lam) ?_ hlC
    dsimp [a]
    rw [div_le_div_iff₀ hypos hlam]
    have hh := (le_div_iff₀ hc0.1).mp hc0.2.2.1
    nlinarith
  have hB0 : (lbfgsInverseStage M t s y 0).PosSemidef := by
    dsimp [lbfgsInverseStage]
    apply Matrix.PosSemidef.smul Matrix.PosSemidef.one
    exact div_nonneg (by simpa only [real_inner_comm] using hc0.1.le) real_inner_self_nonneg
  have hpow : ∀ i : ℕ, C ≤ C^(i+1) := by
    intro i
    simpa using pow_le_pow_right₀ hCone (show 1 ≤ i+1 by omega)
  have hall : ∀ i, i ≤ min t M → (lbfgsInverseStage M t s y i).PosSemidef ∧
      ∀ v, ‖v‖^2 ≤ C^(i+1)*quad (lbfgsInverseStage M t s y i) v ∧
        quad (lbfgsInverseStage M t s y i) v ≤ C^(i+1)*‖v‖^2 := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨hB0,?_⟩
      intro v
      have he : quad (lbfgsInverseStage M t s y 0) v = a*‖v‖^2 := by
        simp only [lbfgsInverseStage,quad_scalar,real_inner_self_eq_norm_sq]
        congr 2
        exact real_inner_comm _ _
      rw [he]
      simp only [zero_add,pow_one]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖v‖)]
      · exact mul_le_mul_of_nonneg_right ha2 (sq_nonneg ‖v‖)
    | succ i ih =>
      intro hi
      obtain ⟨hpsd,hbound⟩ := ih (by omega)
      let j := t-min t M+1+i
      have hj : t-min t M < j := by dsimp [j]; omega
      have hjt : j ≤ t := by dsimp [j]; omega
      have hc := hp j hj hjt
      refine ⟨inverse_psd _ hpsd _ _ hc.1,?_⟩
      have hh := inverse_bounds_step (lbfgsInverseStage M t s y i) (s j) (y j) lam Lam
        (C^(i+1)) C hlam hLam (le_trans hCone (hpow i)) (le_trans hLC (hpow i)) hC2 hCrec
        hc.1 hc.2.1 ((div_le_iff₀ hc.1).mp hc.2.2.2) hbound
      intro v
      simpa only [lbfgsInverseStage, Nat.succ_eq_add_one,pow_succ',j] using hh v
  obtain ⟨hpsd,hbound⟩ := hall (min t M) le_rfl
  apply strict_matrix_bounds _ hpsd (C^(M+1)) (pow_pos hC _)
  intro v
  have hh := hbound v
  have hpowle : C^(min t M+1) ≤ C^(M+1) := pow_le_pow_right₀ hCone (by omega)
  have hqpos : 0 ≤ quad (lbfgsInverseStage M t s y (min t M)) v := by
    simpa only [quad,star_trivial] using hpsd.dotProduct_mulVec_nonneg v.ofLp
  exact ⟨le_trans hh.1 (mul_le_mul_of_nonneg_right hpowle hqpos),
    le_trans hh.2 (mul_le_mul_of_nonneg_right hpowle (sq_nonneg ‖v‖))⟩

theorem solution {n N : ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (M L bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w)) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      ∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ t, (SH t).card = bH) →
        ∀ t, 1 ≤ t → (∀ j, 1 ≤ j → j ≤ t → sqnPairS f M L α w1 S SH j ≠ 0) →
          (sqnHessianApprox f M L α w1 S SH t - μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) - sqnHessianApprox f M L α w1 S SH t).PosDef := by
  let C := 3+Lam+2*Lam/lam+1/lam
  have hq1 : 0 ≤ 2*Lam/lam := by positivity
  have hq2 : 0 < 1/lam := by positivity
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  have hLC : Lam ≤ C := by dsimp [C]; linarith
  have hlC : 1/lam ≤ C := by dsimp [C]; linarith
  have hCrec : 2+2*Lam/lam+1/lam ≤ C := by dsimp [C]; linarith
  have hC : 0 < C := by linarith
  have hCone : 1 ≤ C := by linarith
  have hK : 1 ≤ C^(M+1) := one_le_pow₀ hCone
  refine ⟨1/(2*C^(M+1)),2*C^(M+1),by positivity,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2*C^(M+1))).mpr
    nlinarith
  · intro α w1 S SH hSH t ht hs
    apply memory_bounds lam Lam C hlam hLam hC2 hLC hlC hCrec M t hM ht
      (sqnPairS f M L α w1 S SH) (sqnPairY f M L α w1 S SH)
    intro j hj hjt
    have hsj := hs j (by omega) hjt
    have hc := curvature_pair_bounds_local f hf lam Lam hlam hLam bH hHess (SH j) (hSH j)
      (blockAverage L (sqnHistory f M L α w1 S SH ((j+1)*L)) j)
      (sqnPairS f M L α w1 S SH j) (sqnPairY f M L α w1 S SH j) hsj rfl
    exact ⟨lt_of_lt_of_le (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hsj))) hc.1.1,hc.1.1,hc.2⟩
