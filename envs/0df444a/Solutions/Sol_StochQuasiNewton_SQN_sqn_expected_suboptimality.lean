-- Prove2me | solution 1 for StochQuasiNewton.SQN.sqn_expected_suboptimality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:08:02.846285+00:00
-- url     : https://prove2.me/submissions/c8727876-a715-47e4-882c-62aa018ce7a7

import Definitions.Def_StochQuasiNewton_SQN_Algorithm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Definitions.Def_StochQuasiNewton_SQN_LBFGS
import Mathlib.Algebra.Order.BigOperators.Expect
import Definitions.Def_StochQuasiNewton_SQN_NewtonLike
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Chebyshev


open StochQuasiNewton.SQN
namespace SQNHistory
variable {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (M L : ℕ)
  (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N))

theorem stable {m r j : ℕ} (hmr : m ≤ r) (hj : j ≤ m+1) :
    sqnHistory f M L α w1 S SH r j = sqnHistory f M L α w1 S SH m j := by
  induction r,hmr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    simp only [sqnHistory,if_neg (show j ≠ r+2 by omega)]
    exact ih

theorem initial : sqnIterate f M L α w1 S SH 1 = w1 := by simp [sqnIterate,sqnHistory]

theorem step (k : ℕ) (hk : 1 ≤ k) :
    sqnIterate f M L α w1 S SH (k+1) = sqnIterate f M L α w1 S SH k -
      α k • Matrix.toEuclideanLin (sqnAppliedMatrix f M L α w1 S SH k)
        (miniBatchGrad f (S k) (sqnIterate f M L α w1 S SH k)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [sqnIterate,sqnHistory,sqnAppliedMatrix]

theorem blockAverage_congr {t : ℕ} {h g : ℕ → EuclideanSpace ℝ (Fin n)}
    (he : ∀ j, j ≤ (t+1)*L → h j=g j) : blockAverage L h t=blockAverage L g t := by
  unfold blockAverage
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact he j (Finset.mem_Icc.mp hj).2

theorem corrS_congr {t : ℕ} {h g : ℕ → EuclideanSpace ℝ (Fin n)}
    (he : ∀ j, j ≤ (t+1)*L → h j=g j) : corrS L h t=corrS L g t := by
  unfold corrS
  rw [blockAverage_congr L he,blockAverage_congr L (t := t-1) (fun j hj => he j (by nlinarith [Nat.sub_le t 1]))]

theorem lbfgs_congr {t : ℕ} {s y s' y' : ℕ → EuclideanSpace ℝ (Fin n)}
    (hs : ∀ j, j ≤ t → s j=s' j) (hy : ∀ j, j ≤ t → y j=y' j) :
    lbfgsMatrix M t s y=lbfgsMatrix M t s' y' := by
  suffices ∀ i, i ≤ min t M → lbfgsInverseStage M t s y i=lbfgsInverseStage M t s' y' i by
    exact this _ le_rfl
  intro i hi
  induction i with
  | zero => simp only [lbfgsInverseStage,hs t le_rfl,hy t le_rfl]
  | succ i ih =>
    rw [lbfgsInverseStage,lbfgsInverseStage,ih (by omega),hs _ (by omega),hy _ (by omega)]

theorem stepMatrix_congr_SH {SH' : ℕ → Finset (Fin N)} {h : ℕ → EuclideanSpace ℝ (Fin n)}
    {k : ℕ} (he : ∀ j, j ≤ k-1 → SH j=SH' j) :
    stepMatrix f M L SH h k=stepMatrix f M L SH' h k := by
  unfold stepMatrix
  split
  · rfl
  · apply lbfgs_congr M (fun _ _ => rfl)
    intro j hj
    have hjk : j ≤ k-1 := le_trans hj (le_trans (Nat.sub_le _ _) (Nat.div_le_self _ _))
    simp only [corrY,he j hjk]

theorem history_congr {S' SH' : ℕ → Finset (Fin N)} {m : ℕ}
    (hs : ∀ j, j ≤ m → S j=S' j) (hh : ∀ j, j ≤ m → SH j=SH' j) :
    sqnHistory f M L α w1 S SH m = sqnHistory f M L α w1 S' SH' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := ih (fun j hj => hs j (by omega)) (fun j hj => hh j (by omega))
    funext j
    simp only [sqnHistory,hm]
    rw [hs (m+1) (by omega)]
    rw [stepMatrix_congr_SH f M L SH (fun j hj => hh j (by omega))]

theorem iterate_congr {S' SH' : ℕ → Finset (Fin N)} {k : ℕ} (hk : 1 ≤ k)
    (hs : ∀ j, j < k → S j=S' j) (hh : ∀ j, j < k → SH j=SH' j) :
    sqnIterate f M L α w1 S SH k=sqnIterate f M L α w1 S' SH' k := by
  unfold sqnIterate
  rw [history_congr f M L α w1 S SH (fun j hj => hs j (by omega)) (fun j hj => hh j (by omega))]

theorem applied_congr {S' SH' : ℕ → Finset (Fin N)} {k : ℕ} (hk : 1 ≤ k)
    (hs : ∀ j, j < k → S j=S' j) (hh : ∀ j, j < k → SH j=SH' j) :
    sqnAppliedMatrix f M L α w1 S SH k=sqnAppliedMatrix f M L α w1 S' SH' k := by
  unfold sqnAppliedMatrix
  rw [history_congr f M L α w1 S SH (fun j hj => hs j (by omega)) (fun j hj => hh j (by omega))]
  exact stepMatrix_congr_SH f M L SH (fun j hj => hh j (by omega))

theorem correction_stable {t k : ℕ} (htk : (t+1)*L ≤ k-1) :
    corrS L (sqnHistory f M L α w1 S SH (k-1)) t = sqnPairS f M L α w1 S SH t := by
  unfold sqnPairS
  apply corrS_congr L
  intro j hj
  exact stable f M L α w1 S SH htk (by omega)
end SQNHistory
namespace SQNUniform

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
end SQNUniform
namespace SQNUniform
open scoped RealInnerProductSpace Matrix
open StochQuasiNewton.SQN

theorem applied_bounds {n N : ℕ}
    (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam) (M L bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hHess : ∀ SH : Finset (Fin N), SH.card=bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w)) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      ∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ j, (SH j).card=bH) → (∀ j, 1 ≤ j → sqnPairS f M L α w1 S SH j ≠ 0) →
        ∀ k, 1 ≤ k →
          (sqnAppliedMatrix f M L α w1 S SH k-μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ)-sqnAppliedMatrix f M L α w1 S SH k).PosDef := by
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
  · intro α w1 S SH hSH hs k hk
    unfold sqnAppliedMatrix stepMatrix
    split
    · apply strict_matrix_bounds 1 Matrix.PosSemidef.one (C^(M+1)) (by positivity)
      intro v
      have he : quad (1 : Matrix (Fin n) (Fin n) ℝ) v=‖v‖^2 := by
        simpa using quad_scalar (n := n) 1 v
      rw [he]
      constructor <;> nlinarith [sq_nonneg ‖v‖]
    · rename_i hlate
      let t := (k-1)/L-1
      have ht : 1 ≤ t := by dsimp [t]; omega
      have htk : (t+1)*L ≤ k-1 := by
        have he : t+1=(k-1)/L := by dsimp [t]; omega
        rw [he]
        exact Nat.div_mul_le_self _ _
      apply memory_bounds lam Lam C hlam hLam hC2 hLC hlC hCrec M t hM ht
      intro j hj hjt
      have hjk : (j+1)*L ≤ k-1 := le_trans (Nat.mul_le_mul_right L (by omega)) htk
      have hsj : corrS L (sqnHistory f M L α w1 S SH (k-1)) j ≠ 0 := by
        rw [SQNHistory.correction_stable f M L α w1 S SH hjk]
        exact hs j (by omega)
      have hc := curvature_pair_bounds_local f hf lam Lam hlam hLam bH hHess (SH j) (hSH j)
        (blockAverage L (sqnHistory f M L α w1 S SH (k-1)) j)
        (corrS L (sqnHistory f M L α w1 S SH (k-1)) j)
        (corrY f L SH (sqnHistory f M L α w1 S SH (k-1)) j) hsj rfl
      exact ⟨lt_of_lt_of_le (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hsj))) hc.1.1,hc.1.1,hc.2⟩
end SQNUniform


open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter
namespace SQNProof

theorem quadratic_lower {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F w + ⟪gradient F w, v-w⟫ + lam / 2 * ‖v-w‖^2 ≤ F v := by
  let d := v-w
  let q : ℝ → ℝ := fun t => F (w+t • d) - lam/2*t^2*‖d‖^2
  let q' : ℝ → ℝ := fun t => ⟪gradient F (w+t • d), d⟫ - lam*t*‖d‖^2
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w+s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add w
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    have hchain := (hdF (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← inner_gradient_left] at hchain
    convert! hchain.sub (((hasDerivAt_id t).pow 2).const_mul (lam/2) |>.mul_const (‖d‖^2)) using 1 <;>
      dsimp only [q, q', id_eq] <;> ring
  have hq' : ∀ t, HasDerivAt q'
      (⟪fderiv ℝ (gradient F) (w+t • d) d, d⟫-lam*‖d‖^2) t := by
    intro t
    have hchain := (hdG (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert! (hchain.inner ℝ (hasDerivAt_const t d)).sub
      (((hasDerivAt_id t).const_mul lam).mul_const (‖d‖^2)) using 1 <;> simp [q']
  have hmono : Monotone q' := monotone_of_hasDerivAt_nonneg hq' (by
    intro t
    by_cases hd : d = 0
    · simp [hd]
    · exact sub_nonneg.mpr (hHess (w+t • d) d hd).le)
  have hconv : ConvexOn ℝ Set.univ q :=
    (show Monotone (deriv q) from fun x y hxy => by
      rw [(hq x).deriv, (hq y).deriv]; exact hmono hxy).monotoneOn (interior Set.univ) |>.convexOn_of_deriv
      convex_univ (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
  have hh := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0:ℝ)<1) (hq 0)
  simp [q, q', slope_def_field, d] at hh
  rw [inner_gradient_left, map_sub]
  linarith

theorem spectral_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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


end SQNProof

namespace SQNProof
open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter

theorem quadratic_upper {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (Lam : ℝ)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      ⟪fderiv ℝ (gradient F) w v, v⟫ < Lam * ‖v‖ ^ 2)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F v ≤ F w + ⟪gradient F w, v-w⟫ + Lam / 2 * ‖v-w‖^2 := by
  let d := v-w
  let q : ℝ → ℝ := fun t => Lam/2*t^2*‖d‖^2-F (w+t • d)
  let q' : ℝ → ℝ := fun t => Lam*t*‖d‖^2-⟪gradient F (w+t • d), d⟫
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w+s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add w
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    have hchain := (hdF (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← inner_gradient_left] at hchain
    convert! (((hasDerivAt_id t).pow 2).const_mul (Lam/2) |>.mul_const (‖d‖^2)).sub hchain using 1 <;>
      dsimp only [q, q', id_eq] <;> ring
  have hq' : ∀ t, HasDerivAt q'
      (Lam*‖d‖^2-⟪fderiv ℝ (gradient F) (w+t • d) d, d⟫) t := by
    intro t
    have hchain := (hdG (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert! (((hasDerivAt_id t).const_mul Lam).mul_const (‖d‖^2)).sub
      (hchain.inner ℝ (hasDerivAt_const t d)) using 1 <;> simp [q']
  have hmono : Monotone q' := monotone_of_hasDerivAt_nonneg hq' (by
    intro t
    by_cases hd : d=0
    · simp [hd]
    · exact sub_nonneg.mpr (hHess (w+t • d) d hd).le)
  have hconv : ConvexOn ℝ Set.univ q :=
    (show Monotone (deriv q) from fun x y hxy => by
      rw [(hq x).deriv, (hq y).deriv]; exact hmono hxy).monotoneOn (interior Set.univ) |>.convexOn_of_deriv
      convex_univ (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
  have hh := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) (hq 0)
  simp [q,q',slope_def_field,d] at hh
  rw [inner_gradient_left,map_sub]
  linarith

theorem objective_lower {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ) (hlam : 0 < lam)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F w - 1/(2*lam)*‖gradient F w‖^2 ≤ F v := by
  have hq := quadratic_lower F hF lam hHess w v
  have hs := sq_nonneg ‖gradient F w + lam • (v-w)‖
  rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hs
  have he : -(1/(2*lam)*‖gradient F w‖^2) ≤
      ⟪gradient F w,v-w⟫+lam/2*‖v-w‖^2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2*lam by positivity)).mp
    field_simp
    nlinarith
  linarith

theorem matrix_bounds {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hl : (H-a • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (hu : (b • (1 : Matrix (Fin n) (Fin n) ℝ)-H).PosDef) :
    (H.toEuclideanLin.IsSymmetric) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ ⟪H.toEuclideanLin v,v⟫) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖H.toEuclideanLin v‖ ≤ b*‖v‖ := by
  have hId (c : ℝ) : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  have hH : H.IsHermitian := by
    simpa only [sub_add_cancel] using hl.isHermitian.add (hId a)
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hstrict (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
      a*‖v‖^2 < ⟪H.toEuclideanLin v,v⟫ ∧ ⟪H.toEuclideanLin v,v⟫ < b*‖v‖^2 := by
    have hv' : v.ofLp ≠ 0 := by simpa using hv
    have h1 := hl.dotProduct_mulVec_pos hv'
    have h2 := hu.dotProduct_mulVec_pos hv'
    have hn : dotProduct v.ofLp v.ofLp = ‖v‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using real_inner_self_eq_norm_sq v
    have he : ⟪H.toEuclideanLin v,v⟫ = dotProduct v.ofLp (H.mulVec v.ofLp) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,Matrix.ofLp_toEuclideanLin_apply]
    simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,
      Matrix.one_mulVec,dotProduct_smul,smul_eq_mul,hn] at h1 h2
    rw [he]
    exact ⟨sub_pos.mp h1,sub_pos.mp h2⟩
  refine ⟨hsym,?_,?_⟩
  · intro v
    by_cases hv : v=0
    · simp [hv]
    · exact (hstrict v hv).1.le
  · intro v
    by_cases hv : v=0
    · simp [hv]
    have hr := (spectral_ratio H.toEuclideanLin hsym a b ha hstrict v hv).2
    have hp : 0 < ⟪H.toEuclideanLin v,v⟫ :=
      lt_trans (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hstrict v hv).1
    have hs := (div_le_iff₀ hp).mp hr
    have hq := mul_le_mul_of_nonneg_left (hstrict v hv).2.le (ha.le.trans hab)
    have hb : 0 ≤ b*‖v‖ := mul_nonneg (ha.le.trans hab) (norm_nonneg _)
    nlinarith [norm_nonneg (H.toEuclideanLin v)]
end SQNProof

namespace SQNProof
open scoped RealInnerProductSpace BigOperators
open StochQuasiNewton.SQN

theorem deterministic_descent {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hLam : 0 < Lam)
    (hHess : ∀ z, StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) z))
    (A : Matrix (Fin n) (Fin n) ℝ) (μ₁ μ₂ a : ℝ) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (ha : 0 < a)
    (hAl : (A-μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (hAu : (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ)-A).PosDef)
    (x g : EuclideanSpace ℝ (Fin n)) :
    F (x-a • A.toEuclideanLin g) ≤ F x-a*⟪A.toEuclideanLin (gradient F x),g⟫+
      Lam/2*(a*μ₂)^2*‖g‖^2 := by
  have hb := matrix_bounds A μ₁ μ₂ hμ₁ hμ hAl hAu
  have ht := quadratic_upper F hF Lam (fun z v hv => (hHess z v hv).2) x (x-a • A.toEuclideanLin g)
  have hd : x-a • A.toEuclideanLin g-x = -(a • A.toEuclideanLin g) := by abel
  rw [hd,inner_neg_right,real_inner_smul_right,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos ha] at ht
  rw [← hb.1] at ht
  have hn := hb.2.2 g
  have hns : ‖A.toEuclideanLin g‖^2 ≤ μ₂^2*‖g‖^2 := by
    have hp := mul_nonneg (hμ₁.le.trans hμ) (norm_nonneg g)
    nlinarith [norm_nonneg (A.toEuclideanLin g)]
  have hm := mul_le_mul_of_nonneg_left hns (show 0 ≤ Lam/2*a^2 by positivity)
  nlinarith

theorem expected_inner {n : ℕ} {I : Type*} (T : Finset I)
    (v : EuclideanSpace ℝ (Fin n)) (g : I → EuclideanSpace ℝ (Fin n)) :
    T.expect (fun i => ⟪v,g i⟫) = ⟪v,(1/(T.card:ℝ)) • ∑ i ∈ T, g i⟫ := by
  rw [Finset.expect_eq_sum_div_card,real_inner_smul_right,inner_sum]
  ring

theorem averaged_descent {n : ℕ} {I : Type*} (T : Finset I) (hT : T.Nonempty)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hHess : ∀ z, StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) z))
    (A : Matrix (Fin n) (Fin n) ℝ) (μ₁ μ₂ a γ : ℝ) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (ha : 0 < a)
    (hAl : (A-μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (hAu : (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ)-A).PosDef)
    (x wstar : EuclideanSpace ℝ (Fin n)) (g : I → EuclideanSpace ℝ (Fin n))
    (hmean : (1/(T.card:ℝ)) • ∑ i ∈ T, g i = gradient F x)
    (hsq : T.expect (fun i => ‖g i‖^2) ≤ γ^2) :
    T.expect (fun i => F (x-a • A.toEuclideanLin (g i))-F wstar) ≤
      (1-2*a*μ₁*lam)*(F x-F wstar)+Lam/2*(a*μ₂)^2*γ^2 := by
  have hp := Finset.expect_le_expect (s := T) (fun i hi =>
    sub_le_sub_right (deterministic_descent F hF lam Lam hLam hHess A μ₁ μ₂ a hμ₁ hμ ha hAl hAu x (g i)) (F wstar))
  have he : T.expect (fun i => F x-a*⟪A.toEuclideanLin (gradient F x),g i⟫+
      Lam/2*(a*μ₂)^2*‖g i‖^2-F wstar) =
      F x-a*⟪A.toEuclideanLin (gradient F x),gradient F x⟫+
        Lam/2*(a*μ₂)^2*T.expect (fun i => ‖g i‖^2)-F wstar := by
    rw [Finset.expect_sub_distrib,Finset.expect_add_distrib,Finset.expect_sub_distrib]
    rw [Finset.expect_const hT,Finset.expect_const hT,← Finset.mul_expect,← Finset.mul_expect]
    rw [expected_inner,hmean]
  rw [he] at hp
  have hnoise := mul_le_mul_of_nonneg_left hsq (show 0 ≤ Lam/2*(a*μ₂)^2 by positivity)
  have hquad := (matrix_bounds A μ₁ μ₂ hμ₁ hμ hAl hAu).2.1 (gradient F x)
  have hgrad : 2*lam*(F x-F wstar) ≤ ‖gradient F x‖^2 := by
    have hl := objective_lower F hF lam hlam (fun z v hv => (hHess z v hv).1) x wstar
    have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*lam by positivity)
    field_simp at hh
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left hquad ha.le
  have hgap := mul_le_mul_of_nonneg_left hgrad (mul_nonneg ha.le hμ₁.le)
  nlinarith
end SQNProof


open scoped BigOperators
open StochQuasiNewton.SQN
namespace SQNAverage

noncomputable def hist {A : Type*} (T : Finset A) (k : ℕ) : Finset (Fin k → A) :=
  Fintype.piFinset (fun _ => T)

theorem hist_nonempty {A : Type*} (T : Finset A) (hT : T.Nonempty) (k : ℕ) : (hist T k).Nonempty := by
  obtain ⟨a,ha⟩ := hT
  exact ⟨fun _ => a,by simpa [hist] using (show ∀ i : Fin k, a ∈ T from fun _ => ha)⟩

theorem hist_snoc {A : Type*} (T : Finset A) (k : ℕ) (g : (Fin (k+1) → A) → ℝ) :
    (hist T (k+1)).expect g = T.expect (fun a => (hist T k).expect (fun σ => g (Fin.snoc σ a))) := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (k+1) => A)
  calc
    (hist T (k+1)).expect g = (T ×ˢ hist T k).expect (fun p => g (Fin.snoc p.2 p.1)) := by
      symm
      apply Finset.expect_equiv e
      · intro p
        simp only [Finset.mem_product,hist,Fintype.mem_piFinset]
        change (p.1 ∈ T ∧ ∀ i : Fin k, p.2 i ∈ T) ↔ ∀ i : Fin (k+1), Fin.snoc (α := fun _ : Fin (k+1) => A) p.2 p.1 i ∈ T
        rw [Fin.forall_fin_succ']
        simp [and_comm]
      · intro p hp
        rfl
    _ = _ := Finset.expect_product _ _ _

theorem sample_eq_expect (N b bH k : ℕ)
    (Φ : (ℕ → Finset (Fin N)) → (ℕ → Finset (Fin N)) → ℝ) :
    sampleExpectation N b bH k Φ =
      (hist (Finset.powersetCard b (Finset.univ : Finset (Fin N))) k).expect (fun σ =>
        (hist (Finset.powersetCard bH (Finset.univ : Finset (Fin N))) k).expect (fun τ =>
          Φ (extendSamples σ) (extendSamples τ))) := by
  simp only [sampleExpectation,hist,Finset.expect_eq_sum_div_card]
  rw [← Finset.sum_div]
  rw [div_div]
  congr 1
  ring

theorem extend_snoc_prefix {N k : ℕ} (σ : Fin k → Finset (Fin N)) (a : Finset (Fin N))
    (j : ℕ) (hj : j < k) : extendSamples (Fin.snoc σ a) j = extendSamples σ j := by
  simp only [extendSamples,dif_pos (show j < k+1 by omega),dif_pos hj]
  change Fin.snoc (α := fun _ : Fin (k+1) => Finset (Fin N)) σ a (Fin.castSucc ⟨j,hj⟩) = _
  exact Fin.snoc_castSucc (α := fun _ : Fin (k+1) => Finset (Fin N)) a σ ⟨j,hj⟩

theorem extend_snoc_last {N k : ℕ} (σ : Fin k → Finset (Fin N)) (a : Finset (Fin N)) :
    extendSamples (Fin.snoc σ a) k = a := by
  simp only [extendSamples,dif_pos (Nat.lt_succ_self k)]
  change Fin.snoc (α := fun _ : Fin (k+1) => Finset (Fin N)) σ a (Fin.last k) = a
  simp

noncomputable def fill {N k : ℕ} (σ : Fin k → Finset (Fin N)) (a : Finset (Fin N)) : ℕ → Finset (Fin N) :=
  fun j => if h : j < k then σ ⟨j,h⟩ else a

theorem fill_prefix {N k : ℕ} (σ : Fin k → Finset (Fin N)) (a : Finset (Fin N))
    (j : ℕ) (hj : j < k) : extendSamples σ j = fill σ a j := by simp [extendSamples,fill,hj]

theorem fill_card {N k b : ℕ} (σ : Fin k → Finset (Fin N)) (a : Finset (Fin N))
    (ha : a.card=b) (hs : σ ∈ hist (Finset.powersetCard b (Finset.univ : Finset (Fin N))) k) :
    ∀ j, (fill σ a j).card=b := by
  intro j
  unfold fill
  split
  · exact (Finset.mem_powersetCard.mp ((Fintype.mem_piFinset.mp hs) _)).2
  · exact ha
end SQNAverage

namespace SQNAverage

theorem hist_double_snoc {A B : Type*} (T : Finset A) (U : Finset B) (k : ℕ)
    (Φ : (Fin (k+1) → A) → (Fin (k+1) → B) → ℝ) :
    (hist T (k+1)).expect (fun σ => (hist U (k+1)).expect (fun τ => Φ σ τ)) =
      (hist T k).expect (fun σ => (hist U k).expect (fun τ =>
        T.expect (fun a => U.expect (fun b => Φ (Fin.snoc σ a) (Fin.snoc τ b))))) := by
  simp_rw [hist_snoc]
  rw [Finset.expect_comm T (hist T k)]
  apply Finset.expect_congr rfl
  intro σ hσ
  simp_rw [Finset.expect_comm U (hist U k)]
  exact Finset.expect_comm T (hist U k) _

theorem hist_double_recurrence {A B : Type*} (T : Finset A) (U : Finset B)
    (hT : T.Nonempty) (hU : U.Nonempty) (k : ℕ)
    (Φ : ∀ k : ℕ,(Fin k → A) → (Fin k → B) → ℝ) (c d : ℝ)
    (hstep : ∀ σ ∈ hist T k,∀ τ ∈ hist U k,
      T.expect (fun a => U.expect (fun b => Φ (k+1) (Fin.snoc σ a) (Fin.snoc τ b))) ≤ c*Φ k σ τ+d) :
    (hist T (k+1)).expect (fun σ => (hist U (k+1)).expect (fun τ => Φ (k+1) σ τ)) ≤
      c*(hist T k).expect (fun σ => (hist U k).expect (fun τ => Φ k σ τ))+d := by
  rw [hist_double_snoc]
  calc
    _ ≤ (hist T k).expect (fun σ => (hist U k).expect (fun τ => c*Φ k σ τ+d)) :=
      Finset.expect_le_expect fun σ hσ => Finset.expect_le_expect fun τ hτ => hstep σ hσ τ hτ
    _ = _ := by
      simp only [Finset.expect_add_distrib,← Finset.mul_expect,
        Finset.expect_const (hist_nonempty U hU k),Finset.expect_const (hist_nonempty T hT k)]

theorem sample_nonneg (N b bH k : ℕ)
    (Φ : (ℕ → Finset (Fin N)) → (ℕ → Finset (Fin N)) → ℝ) (hΦ : ∀ σ τ,0 ≤ Φ σ τ) :
    0 ≤ sampleExpectation N b bH k Φ := by
  rw [sample_eq_expect]
  exact Finset.expect_nonneg fun σ hσ => Finset.expect_nonneg fun τ hτ => hΦ _ _

theorem sample_const (N b bH k : ℕ) (hb : b ≤ N) (hbH : bH ≤ N) (c : ℝ) :
    sampleExpectation N b bH k (fun _ _ => c)=c := by
  have hT : (Finset.powersetCard b (Finset.univ : Finset (Fin N))).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using hb)
  have hU : (Finset.powersetCard bH (Finset.univ : Finset (Fin N))).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using hbH)
  rw [sample_eq_expect]
  simp only [Finset.expect_const (hist_nonempty _ hU k),Finset.expect_const (hist_nonempty _ hT k)]

end SQNAverage


open scoped RealInnerProductSpace
open StochQuasiNewton.SQN

namespace CSQN

lemma subset_card_pos {N b : ℕ} (hbN : b ≤ N) :
    0 < ((Finset.univ : Finset (Fin N)).powersetCard b).card := by
  simpa using Nat.choose_pos hbN

lemma subset_count {N b : ℕ} (hb : 1 ≤ b) (i : Fin N) :
    (((Finset.univ : Finset (Fin N)).powersetCard b).filter (fun S => i ∈ S)).card =
      (N-1).choose (b-1) := by
  simpa using Finset.card_filter_powersetCard_subset ({i} : Finset (Fin N))
    Finset.univ b (Finset.subset_univ _) (by simpa)

lemma sum_subsets {N b : ℕ} (hb : 1 ≤ b) {E : Type*} [AddCommMonoid E]
    (v : Fin N → E) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b, ∑ i ∈ S, v i =
      (N-1).choose (b-1) • ∑ i, v i := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b,
          ∑ i : Fin N, if i ∈ S then v i else 0 := by
      simp only [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ i : Fin N, ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b,
          if i ∈ S then v i else 0 := Finset.sum_comm
    _ = ∑ i : Fin N, (N-1).choose (b-1) • v i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, subset_count hb]
    _ = _ := Finset.sum_nsmul _ _ _

lemma subset_mean {N b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (v : Fin N → E) :
    (1 / (((Finset.univ : Finset (Fin N)).powersetCard b).card : ℝ)) •
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b,
        (1 / (S.card : ℝ)) • ∑ i ∈ S, v i =
      (1 / (N : ℝ)) • ∑ i, v i := by
  classical
  have hN : 0 < N := lt_of_lt_of_le (by omega) hbN
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc0 : (N.choose b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hbN))
  have hcount : (N : ℝ) * ((N-1).choose (b-1) : ℝ) = (N.choose b : ℝ) * (b : ℝ) := by
    have hh := Nat.add_one_mul_choose_eq (N-1) (b-1)
    rw [Nat.sub_add_cancel hN, Nat.sub_add_cancel hb] at hh
    exact_mod_cast hh
  have he : ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b,
        (1 / (S.card : ℝ)) • ∑ i ∈ S, v i =
      (1 / (b : ℝ)) • ((N-1).choose (b-1) • ∑ i, v i) := by
    rw [← sum_subsets hb, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [he, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  congr 1
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  field_simp
  nlinarith

lemma norm_mean_sq_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset ι) (v : ι → E) :
    ‖(1 / (S.card : ℝ)) • ∑ i ∈ S, v i‖^2 ≤
      (1 / (S.card : ℝ)) * ∑ i ∈ S, ‖v i‖^2 := by
  have hn : ‖∑ i ∈ S, v i‖ ≤ ∑ i ∈ S, ‖v i‖ := norm_sum_le S v
  calc
    _ = (‖∑ i ∈ S, v i‖ / (S.card : ℝ)) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      congr 1
      ring
    _ ≤ ((∑ i ∈ S, ‖v i‖) / (S.card : ℝ)) ^ 2 := by
      gcongr
    _ ≤ (∑ i ∈ S, ‖v i‖^2) / (S.card : ℝ) := sum_div_card_sq_le_sum_sq_div_card
    _ = _ := by ring

lemma subset_mean_norm_sq_le {N b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : Fin N → E) :
    (1 / (((Finset.univ : Finset (Fin N)).powersetCard b).card : ℝ)) *
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b,
        ‖(1 / (S.card : ℝ)) • ∑ i ∈ S, v i‖^2 ≤
      (1 / (N : ℝ)) * ∑ i, ‖v i‖^2 := by
  calc
    _ ≤ (1 / (((Finset.univ : Finset (Fin N)).powersetCard b).card : ℝ)) *
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b,
        (1 / (S.card : ℝ)) * ∑ i ∈ S, ‖v i‖^2 := by
      gcongr with S hS
      exact norm_mean_sq_le S v
    _ = _ := subset_mean hb hbN (fun i => ‖v i‖^2)

end CSQN


open scoped RealInnerProductSpace
open StochQuasiNewton.SQN

namespace CSQN

lemma objective_contDiff {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (objective f) :=
  contDiff_const.mul (ContDiff.sum fun i _ => hf i)

lemma objective_gradient {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (w : EuclideanSpace ℝ (Fin n)) :
    gradient (objective f) w = (1 / (N : ℝ)) • ∑ i, gradient (f i) w := by
  have hd := ((HasFDerivAt.fun_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    (hf i w).hasFDerivAt).const_mul (1 / (N : ℝ))).fderiv
  unfold gradient
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => (1 / (N : ℝ)) * ∑ i, f i y) w) = _
  rw [hd]
  simp

lemma gradient_differentiable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
    (hfder.differentiable (by norm_num))

lemma objective_hessian {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (gradient (objective f)) w =
      (1 / (N : ℝ)) • ∑ i, fderiv ℝ (gradient (f i)) w := by
  have hg : gradient (objective f) = fun y => (1 / (N : ℝ)) • ∑ i, gradient (f i) y :=
    funext (objective_gradient f (fun i => (hf i).differentiable (by norm_num)))
  rw [hg, fderiv_fun_const_smul (Differentiable.fun_sum
    (fun i _ => gradient_differentiable (f i) (hf i)) w),
    fderiv_fun_sum (fun i _ => gradient_differentiable (f i) (hf i) w)]

lemma minibatch_mean {n N b : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (hb : 1 ≤ b) (hbN : b ≤ N)
    (w : EuclideanSpace ℝ (Fin n)) :
    (1 / (((Finset.univ : Finset (Fin N)).powersetCard b).card : ℝ)) •
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b, miniBatchGrad f S w =
      gradient (objective f) w := by
  rw [objective_gradient f hf]
  exact subset_mean hb hbN (fun i => gradient (f i) w)

lemma minibatch_second_moment {n N b : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : 1 ≤ b) (hbN : b ≤ N) (w : EuclideanSpace ℝ (Fin n)) :
    (1 / (((Finset.univ : Finset (Fin N)).powersetCard b).card : ℝ)) *
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard b, ‖miniBatchGrad f S w‖^2 ≤
      (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) w‖^2 :=
  subset_mean_norm_sq_le hb hbN (fun i => gradient (f i) w)

lemma hessian_mean {n N bH : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (w : EuclideanSpace ℝ (Fin n)) :
    (1 / (((Finset.univ : Finset (Fin N)).powersetCard bH).card : ℝ)) •
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard bH, subsampledHessian f S w =
      fderiv ℝ (gradient (objective f)) w := by
  rw [objective_hessian f hf]
  exact subset_mean hbH hbHN (fun i => fderiv ℝ (gradient (f i)) w)

lemma mean_bounds {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (a b : ℝ) (v : ι → ℝ)
    (h : ∀ i ∈ S, a < v i ∧ v i < b) :
    a < (1 / (S.card : ℝ)) * ∑ i ∈ S, v i ∧
      (1 / (S.card : ℝ)) * ∑ i ∈ S, v i < b := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hlo := Finset.sum_lt_sum_of_nonempty hS (fun i hi => (h i hi).1)
  have hhi := Finset.sum_lt_sum_of_nonempty hS (fun i hi => (h i hi).2)
  simp only [Finset.sum_const, nsmul_eq_mul] at hlo hhi
  constructor
  · rw [one_div_mul_eq_div, lt_div_iff₀ hcard]
    nlinarith
  · rw [one_div_mul_eq_div, div_lt_iff₀ hcard]
    nlinarith

lemma objective_hessian_bounds {n N bH : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (hHess : ∀ S : Finset (Fin N), S.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f S w))
    (w : EuclideanSpace ℝ (Fin n)) :
    StrictLoewnerBounds lam Lam (fderiv ℝ (gradient (objective f)) w) := by
  intro v hv
  have hid := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
    ⟪A v,v⟫) (hessian_mean f hf hbH hbHN w)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    real_inner_smul_left, sum_inner] at hid
  rw [← hid]
  exact mean_bounds _ (Finset.card_pos.mp (subset_card_pos hbHN)) _ _ _
    (fun S hS => hHess S (Finset.mem_powersetCard.mp hS).2 w v hv)


lemma minibatch_expect {n N b : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (hb : 1 ≤ b) (hbN : b ≤ N)
    (w : EuclideanSpace ℝ (Fin n)) :
    ((Finset.univ : Finset (Fin N)).powersetCard b).expect (fun S => miniBatchGrad f S w) =
      gradient (objective f) w := by
  rw [Finset.expect, ← NNRat.cast_smul_eq_nnqsmul ℝ]
  simpa only [NNRat.cast_inv, NNRat.cast_natCast, one_div] using minibatch_mean f hf hb hbN w

lemma minibatch_expect_sq {n N b : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hb : 1 ≤ b) (hbN : b ≤ N) (w : EuclideanSpace ℝ (Fin n)) :
    ((Finset.univ : Finset (Fin N)).powersetCard b).expect (fun S => ‖miniBatchGrad f S w‖^2) ≤
      (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) w‖^2 := by
  rw [Finset.expect_eq_sum_div_card]
  simpa only [one_div_mul_eq_div] using minibatch_second_moment f hb hbN w

end CSQN

namespace SQNProof
open StochQuasiNewton.SQN
open MeasureTheory Filter

theorem scalar_rate (φ : ℕ → ℝ) (c B Q : ℝ) (hc : 1 < c) (hB : 0 ≤ B)
    (hQ : B ≤ (c-1)*Q) (hQ2 : 2*B ≤ Q) (hinit : φ 1 ≤ Q)
    (hφ : ∀ k, 1 ≤ k → 0 ≤ φ k)
    (hrec : ∀ k, 1 ≤ k → φ (k+1) ≤ (1-c/k)*φ k+B/(k:ℝ)^2) :
    ∀ k, 1 ≤ k → φ k ≤ Q/k := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ2
  intro k hk
  induction k,hk using Nat.le_induction with
  | base => simpa using hinit
  | succ k hk ih =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkp : (0 : ℝ) < k := by positivity
    have hksp : (0 : ℝ) < k+1 := by positivity
    have hkn : (k : ℝ) ≠ 0 := ne_of_gt hkp
    have hksn : (k : ℝ)+1 ≠ 0 := ne_of_gt hksp
    rw [Nat.cast_add,Nat.cast_one]
    by_cases hsign : 0 ≤ 1-c/k
    · have hmul := mul_le_mul_of_nonneg_left ih hsign
      have he : Q/((k:ℝ)+1)-((1-c/k)*(Q/k)+B/(k:ℝ)^2) =
          (((c-1)*Q-B)*((k:ℝ)+1)+Q)/((k:ℝ)^2*((k:ℝ)+1)) := by
        field_simp
        ring
      have hnum : 0 ≤ ((c-1)*Q-B)*((k:ℝ)+1)+Q := by positivity
      have hnon := div_nonneg hnum (show 0 ≤ (k:ℝ)^2*((k:ℝ)+1) by positivity)
      rw [← he] at hnon
      linarith [hrec k hk]
    · have hmul : (1-c/k)*φ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) (hφ k hk)
      have hquot : B/(k:ℝ)^2 ≤ Q/((k:ℝ)+1) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hkp) hksp).mpr
        have hsq : (k:ℝ)+1 ≤ 2*(k:ℝ)^2 := by nlinarith
        have h1 := mul_le_mul_of_nonneg_left hsq hB
        have h2 := mul_le_mul_of_nonneg_right hQ2 (sq_nonneg (k:ℝ))
        nlinarith
      linarith [hrec k hk]
end SQNProof

namespace SQNFinal
open StochQuasiNewton.SQN SQNAverage
open scoped BigOperators

theorem next {n N k : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (M L : ℕ) (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n))
    (σ τ : Fin k → Finset (Fin N)) (a b : Finset (Fin N)) (hk : 1 ≤ k) :
    sqnIterate f M L α w1 (extendSamples (Fin.snoc σ a)) (extendSamples (Fin.snoc τ b)) (k+1) =
      sqnIterate f M L α w1 (extendSamples σ) (extendSamples τ) k -
        α k • (sqnAppliedMatrix f M L α w1 (extendSamples σ) (extendSamples τ) k).toEuclideanLin
          (miniBatchGrad f a (sqnIterate f M L α w1 (extendSamples σ) (extendSamples τ) k)) := by
  rw [SQNHistory.step f M L α w1 _ _ k hk]
  rw [SQNHistory.iterate_congr f M L α w1 _ _ hk
    (extend_snoc_prefix σ a) (extend_snoc_prefix τ b)]
  rw [SQNHistory.applied_congr f M L α w1 _ _ hk
    (extend_snoc_prefix σ a) (extend_snoc_prefix τ b),extend_snoc_last]

theorem recurrence {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (M L b bH : ℕ) (hb : 1 ≤ b) (hbN : b ≤ N) (hbH : 1 ≤ bH) (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (μ₁ μ₂ γ : ℝ) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂)
    (α : ℕ → ℝ) (w1 wstar : EuclideanSpace ℝ (Fin n))
    (hA : ∀ S SH : ℕ → Finset (Fin N), (∀ j, (S j).card = b) → (∀ j, (SH j).card = bH) →
      ∀ k, 1 ≤ k →
        (sqnAppliedMatrix f M L α w1 S SH k-μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
        (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ)-sqnAppliedMatrix f M L α w1 S SH k).PosDef)
    (hg : ∀ S SH : ℕ → Finset (Fin N), (∀ j, (S j).card = b) → (∀ j, (SH j).card = bH) →
      ∀ k, 1 ≤ k → (1/(N:ℝ))*∑ i, ‖gradient (f i) (sqnIterate f M L α w1 S SH k)‖^2 ≤ γ^2)
    (k : ℕ) (hk : 1 ≤ k) (hα : 0 < α k) :
    sampleExpectation N b bH (k+1) (fun S SH => objective f (sqnIterate f M L α w1 S SH (k+1))-objective f wstar) ≤
      (1-2*α k*μ₁*lam)*sampleExpectation N b bH k (fun S SH => objective f (sqnIterate f M L α w1 S SH k)-objective f wstar)+
        Lam/2*(α k*μ₂)^2*γ^2 := by
  classical
  let T := (Finset.univ : Finset (Fin N)).powersetCard b
  let U := (Finset.univ : Finset (Fin N)).powersetCard bH
  have hT : T.Nonempty := Finset.card_pos.mp (CSQN.subset_card_pos hbN)
  have hU : U.Nonempty := Finset.card_pos.mp (CSQN.subset_card_pos hbHN)
  obtain ⟨a0,ha0⟩ := hT
  obtain ⟨b0,hb0⟩ := hU
  have hT : T.Nonempty := ⟨a0,ha0⟩
  have hU : U.Nonempty := ⟨b0,hb0⟩
  have ha0c : a0.card=b := (Finset.mem_powersetCard.mp ha0).2
  have hb0c : b0.card=bH := (Finset.mem_powersetCard.mp hb0).2
  simp only [sample_eq_expect]
  apply hist_double_recurrence T U hT hU k
    (fun j σ τ => objective f (sqnIterate f M L α w1 (extendSamples σ) (extendSamples τ) j)-objective f wstar)
  intro σ hσ τ hτ
  have hS := fill_card σ a0 ha0c hσ
  have hSH := fill_card τ b0 hb0c hτ
  have hw := SQNHistory.iterate_congr f M L α w1 (extendSamples σ) (extendSamples τ) hk
    (fill_prefix σ a0) (fill_prefix τ b0)
  have hm := SQNHistory.applied_congr f M L α w1 (extendSamples σ) (extendSamples τ) hk
    (fill_prefix σ a0) (fill_prefix τ b0)
  have hbounds := hA (fill σ a0) (fill τ b0) hS hSH k hk
  rw [← hm] at hbounds
  have hsq := hg (fill σ a0) (fill τ b0) hS hSH k hk
  rw [← hw] at hsq
  simp_rw [next f M L α w1 σ τ _ _ hk]
  simp only [Finset.expect_const hU]
  apply SQNProof.averaged_descent T hT (objective f) (CSQN.objective_contDiff f hf)
    lam Lam hlam hLam (CSQN.objective_hessian_bounds f hf lam Lam hbH hbHN hHess)
    _ μ₁ μ₂ (α k) γ hμ₁ hμ hα hbounds.1 hbounds.2 _ wstar
  · exact CSQN.minibatch_mean f (fun i => (hf i).differentiable (by norm_num)) hb hbN _
  · exact (CSQN.minibatch_expect_sq f hb hbN _).trans hsq

end SQNFinal


open StochQuasiNewton.SQN
theorem solution {n N : ℕ} (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (M L b bH : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) (hb : 1 ≤ b) (hbN : b ≤ N) (hbH : 1 ≤ bH)
    (hbHN : bH ≤ N)
    (hHess : ∀ SH : Finset (Fin N), SH.card = bH → ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (subsampledHessian f SH w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn (objective f) Set.univ wstar) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ μ₁ ≤ μ₂ ∧
      (∀ (α : ℕ → ℝ) (w1 : EuclideanSpace ℝ (Fin n)) (S SH : ℕ → Finset (Fin N)),
        (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
        (∀ t, 1 ≤ t → sqnPairS f M L α w1 S SH t ≠ 0) →
        ∀ k, 1 ≤ k →
          (sqnAppliedMatrix f M L α w1 S SH k -
              μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
          (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) -
              sqnAppliedMatrix f M L α w1 S SH k).PosDef) ∧
      (∀ (β γ : ℝ) (w1 : EuclideanSpace ℝ (Fin n)), 1 / (2 * μ₁ * lam) < β →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ t, 1 ≤ t → sqnPairS f M L (fun k => β / k) w1 S SH t ≠ 0) →
        (∀ S SH : ℕ → Finset (Fin N), (∀ k, (S k).card = b) → (∀ t, (SH t).card = bH) →
          ∀ k, 1 ≤ k →
            (1 / (N : ℝ)) * ∑ i, ‖gradient (f i) (sqnIterate f M L (fun k => β / k) w1 S SH k)‖ ^ 2
              ≤ γ ^ 2) →
        ∀ k, 1 ≤ k →
          sampleExpectation N b bH k (fun S SH =>
              objective f (sqnIterate f M L (fun k => β / k) w1 S SH k) - objective f wstar) ≤
            rateConstant Lam lam μ₁ μ₂ β γ (objective f w1 - objective f wstar) / k) := by
  classical
  obtain ⟨μ₁,μ₂,hμ₁,hμ,hA⟩ := SQNUniform.applied_bounds f hf lam Lam hlam hLam M L bH hM hL hHess
  refine ⟨μ₁,μ₂,hμ₁,hμ,?_,?_⟩
  · intro α w1 S SH hS hSH hs k hk
    exact hA α w1 S SH hSH hs k hk
  · intro β γ w1 hβ hs hg
    have hd : 0 < 2*μ₁*lam := by positivity
    have hβpos : 0 < β := lt_trans (one_div_pos.mpr hd) hβ
    have hα (k : ℕ) (hk : 1 ≤ k) : 0 < β/(k:ℝ) := by
      have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      exact div_pos hβpos hkp
    let φ : ℕ → ℝ := fun k => sampleExpectation N b bH k (fun S SH =>
      objective f (sqnIterate f M L (fun j => β/j) w1 S SH k)-objective f wstar)
    let c := 2*μ₁*lam*β
    let B := Lam/2*(β*μ₂)^2*γ^2
    let Q := rateConstant Lam lam μ₁ μ₂ β γ (objective f w1-objective f wstar)
    have hc : 1 < c := by
      have hh := (div_lt_iff₀ hd).mp hβ
      dsimp [c]
      nlinarith
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hQ2 : 2*B ≤ Q := by
      have hh : Lam*μ₂^2*β^2*γ^2 ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
      convert! hh using 1 <;> dsimp [B] <;> ring
    have hQ : B ≤ (c-1)*Q := by
      have hh : Lam*μ₂^2*β^2*γ^2/(2*(2*μ₁*lam*β-1)) ≤ Q :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have he : B/(c-1)=Lam*μ₂^2*β^2*γ^2/(2*(2*μ₁*lam*β-1)) := by
        dsimp [B,c]
        field_simp
      rw [← he] at hh
      have ht := (div_le_iff₀ (sub_pos.mpr hc)).mp hh
      simpa only [mul_comm] using ht
    have hinit : φ 1 ≤ Q := by
      dsimp [φ]
      simp only [SQNHistory.initial,SQNAverage.sample_const N b bH 1 hbN hbHN]
      exact le_max_right _ _
    have hφ : ∀ k, 1 ≤ k → 0 ≤ φ k := by
      intro k hk
      exact SQNAverage.sample_nonneg N b bH k _ (fun S SH => sub_nonneg.mpr (hwstar (Set.mem_univ _)))
    have hrec : ∀ k, 1 ≤ k → φ (k+1) ≤ (1-c/(k:ℝ))*φ k+B/(k:ℝ)^2 := by
      intro k hk
      have hh := SQNFinal.recurrence f hf lam Lam hlam hLam M L b bH hb hbN hbH hbHN hHess
        μ₁ μ₂ γ hμ₁ hμ (fun j => β/j) w1 wstar
        (fun S SH hS hSH => hA _ w1 S SH hSH (hs S SH hS hSH)) hg k hk (hα k hk)
      convert! hh using 1 <;> dsimp [φ,c,B] <;> simp only [div_pow,div_eq_mul_inv] <;> ring
    exact SQNProof.scalar_rate φ c B Q hc hB hQ hQ2 hinit hφ hrec
