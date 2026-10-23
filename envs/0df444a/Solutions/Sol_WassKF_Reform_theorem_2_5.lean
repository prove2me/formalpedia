-- Prove2me | solution 1 for WassKF.Reform.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T20:46:04.172459+00:00
-- url     : https://prove2.me/submissions/ea1d15f0-43d2-45cf-b17c-a91a09d5ac8d

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective
import Definitions.Def_WassersteinDRO_Shrinkage_sdpValue
import Definitions.Def_WassersteinDRO_Shrinkage_affineEstimator
import Definitions.Def_WassKF_Reform_GaussianBall
import Definitions.Def_WassKF_Reform_expectedLoss
import Definitions.Def_WassKF_Reform_minimaxValue
import Definitions.Def_WassKF_Reform_maximinValue

open MeasureTheory ProbabilityTheory
open Matrix MeasureTheory ProbabilityTheory WassersteinDRO.Shrinkage

namespace WassersteinKalmanProof

abbrev Joint (n m : ℕ) := Fin n ⊕ Fin m
abbrev Cov (n m : ℕ) := Matrix (Joint n m) (Joint n m) ℝ
abbrev State (n m : ℕ) := EuclideanSpace ℝ (Joint n m)
noncomputable def slope {n m : ℕ} (S : Cov n m) : Matrix (Fin n) (Fin m) ℝ :=
  S.toBlocks₁₂ * S.toBlocks₂₂⁻¹
noncomputable def residual {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Joint n m) ℝ := Matrix.fromCols 1 (-G)
noncomputable def riskMatrix {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℝ) : Cov n m :=
  (residual G).transpose * residual G
noncomputable def estimator {n m : ℕ} (μ : State n m) (S : Cov n m) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) :=
  affineEstimator S.toBlocks₁₂ S.toBlocks₂₂
    ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
    ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))
noncomputable def bures {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sig S : Matrix ι ι ℝ) : ℝ :=
  (S + Sig - (2 : ℝ) • psdSqrt (psdSqrt Sig * S * psdSqrt Sig)).trace
noncomputable def transportMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sig S : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (psdSqrt Sig)⁻¹ * psdSqrt (psdSqrt Sig * S * psdSqrt Sig) * (psdSqrt Sig)⁻¹
noncomputable def dualMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (γ : ℝ) : Matrix ι ι ℝ :=
  γ ^ 2 • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹ - γ • (1 : Matrix ι ι ℝ)
noncomputable def dualValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ℝ) (Sig D : Matrix ι ι ℝ) (γ : ℝ) : ℝ :=
  γ * ρ ^ 2 + (dualMatrix D γ * Sig).trace

end WassersteinKalmanProof

open Matrix WassersteinDRO.Shrinkage
open scoped BigOperators MatrixOrder

namespace WassersteinKalmanProof

section Square
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem psd_transpose {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : A.transpose = A := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq

theorem pd_mul_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')

theorem pd_inv_mul {A : Matrix ι ι ℝ} (hA : A.PosDef) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')

theorem sqrt_facts (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    (psdSqrt A).PosSemidef ∧ psdSqrt A * psdSqrt A = A := by
  have hex : ∃ B : Matrix ι ι ℝ, B.PosSemidef ∧ B * B = A :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef,
      CFC.sqrt_mul_sqrt_self A hA.nonneg⟩
  simpa only [psdSqrt, dif_pos hex] using hex.choose_spec

theorem sqrt_unique (A B : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hBB : B * B = A) : psdSqrt A = B := by
  have hR := sqrt_facts A hA
  exact (CFC.sqrt_eq_iff A (psdSqrt A) hA.nonneg hR.1.nonneg).2 hR.2 |>.symm.trans
    ((CFC.sqrt_eq_iff A B hA.nonneg hB.nonneg).2 hBB)

theorem sqrt_posDef (A : Matrix ι ι ℝ) (hA : A.PosDef) : (psdSqrt A).PosDef := by
  have hR := sqrt_facts A hA.posSemidef
  apply hR.1.posDef_iff_det_ne_zero.mpr
  intro hz
  have hd := congrArg Matrix.det hR.2
  rw [Matrix.det_mul, hz, zero_mul] at hd
  exact hA.det_pos.ne' hd.symm

theorem sqrt_transpose (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    (psdSqrt A).transpose = psdSqrt A := psd_transpose (sqrt_facts A hA).1

theorem sqrt_self_square (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    psdSqrt (A * A) = A := by
  apply sqrt_unique _ _
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hA] using
      Matrix.posSemidef_conjTranspose_mul_self A
  · exact hA
  · rfl

theorem psd_trace_mul {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have h := (hA.mul_mul_conjTranspose_same (psdSqrt B)).trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, sqrt_transpose B hB,
    Matrix.trace_mul_cycle, (sqrt_facts B hB).2] at h
  simpa only [Matrix.trace_mul_comm B A] using h

theorem trace_sqrt_variational (A H : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hH : H.PosDef) :
    2 * (psdSqrt A).trace ≤ H.trace + (H⁻¹ * A).trace := by
  let X := psdSqrt A
  have hX : X.PosSemidef := (sqrt_facts A hA).1
  have hXX : X * X = A := (sqrt_facts A hA).2
  have hn := (hH.inv.posSemidef.conjTranspose_mul_mul_same (H - X)).trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
    psd_transpose hH.posSemidef, psd_transpose hX] at hn
  have he : (H - X) * H⁻¹ * (H - X) = H - X - X + X * H⁻¹ * X := by
    calc
      _ = H * H⁻¹ * H - H * H⁻¹ * X - X * H⁻¹ * H + X * H⁻¹ * X := by
        noncomm_ring
      _ = _ := by
        rw [pd_mul_inv hH, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc X H⁻¹ H,
          pd_inv_mul hH, Matrix.mul_one]
  rw [he, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_cycle, hXX] at hn
  rw [Matrix.trace_mul_comm A H⁻¹] at hn
  dsimp [X] at hn
  linarith

theorem spectral_real (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
    Function.id_comp] using hA.spectral_theorem

theorem unitary_real_left (U : Matrix.unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ).transpose * U = 1 := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self U

theorem unitary_real_right (U : Matrix.unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ).transpose = 1 := by
  have h := Unitary.coe_mul_star_self U
  change (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ).conjTranspose = 1 at h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

theorem least_eigenvalue_facts (A : Matrix ι ι ℝ) (hA : A.PosDef) (σ : ℝ)
    (hσ : IsLeast (Set.range hA.isHermitian.eigenvalues) σ) :
    0 < σ ∧ (A - σ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  obtain ⟨i, hi⟩ := hσ.1
  refine ⟨hi ▸ hA.eigenvalues_pos i, ?_⟩
  let U : Matrix.unitaryGroup ι ℝ := hA.isHermitian.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun j => hA.isHermitian.eigenvalues j - σ)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun j => sub_nonneg.mpr (hσ.2 ⟨j, rfl⟩)
  have he : Matrix.diagonal (fun j => hA.isHermitian.eigenvalues j - σ) =
      Matrix.diagonal hA.isHermitian.eigenvalues - σ • (1 : Matrix ι ι ℝ) := by
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.diagonal, hjk]
  have h := hd.mul_mul_conjTranspose_same (U : Matrix ι ι ℝ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, he, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, unitary_real_right,
    ← spectral_real A hA.isHermitian] at h
  exact h

omit [Fintype ι] in
theorem pd_of_lower {A : Matrix ι ι ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hA : (A - σ • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hpos := Matrix.PosDef.posSemidef_add hA ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul hσ)
  simpa only [sub_add_cancel] using hpos

theorem continuousAt_inv_pd (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    ContinuousAt (fun B : Matrix ι ι ℝ => B⁻¹) A := by
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hA.det_pos.ne')

omit [DecidableEq ι] in
theorem isClosed_psd : IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  have h1 : IsClosed {A : Matrix ι ι ℝ | A.IsHermitian} :=
    isClosed_eq (by fun_prop) continuous_id
  have h2 : IsClosed {A : Matrix ι ι ℝ | ∀ x : ι → ℝ, 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    have hc : IsClosed (⋂ x : ι → ℝ,
        {A : Matrix ι ι ℝ | 0 ≤ star x ⬝ᵥ (A *ᵥ x)}) :=
      isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)
    simpa only [Set.iInter_ofPred] using hc
  simp_rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  exact h1.inter h2

end Square

section Rectangular
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem trace_square_entries (A : Matrix ι κ ℝ) :
    (A * A.transpose).trace = ∑ i, ∑ j, (A i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem trace_congruence_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (B : Matrix κ ι ℝ) : 0 ≤ (B * A * B.transpose).trace := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hA.mul_mul_conjTranspose_same B).trace_nonneg

end Rectangular

end WassersteinKalmanProof

open Matrix WassersteinDRO.Shrinkage
open scoped BigOperators MatrixOrder

namespace WassersteinKalmanProof

section Square
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem transport_facts (Sig S : Matrix ι ι ℝ) (hSig : Sig.PosDef) (hS : S.PosSemidef) :
    (transportMap Sig S).PosSemidef ∧
    transportMap Sig S * Sig * (transportMap Sig S).transpose = S ∧
    ((transportMap Sig S - 1) * Sig * (transportMap Sig S - 1).transpose).trace =
      bures Sig S := by
  let R := psdSqrt Sig
  let U := psdSqrt (R * S * R)
  have hR : R.PosDef := sqrt_posDef Sig hSig
  have hRR : R * R = Sig := (sqrt_facts Sig hSig.posSemidef).2
  have hRSR : (R * S * R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hR.posSemidef] using
      hS.mul_mul_conjTranspose_same R
  have hU : U.PosSemidef := (sqrt_facts _ hRSR).1
  have hUU : U * U = R * S * R := (sqrt_facts _ hRSR).2
  have hT : (transportMap Sig S).PosSemidef := by
    simpa only [transportMap, Matrix.conjTranspose_eq_transpose_of_trivial,
      psd_transpose hR.inv.posSemidef] using hU.conjTranspose_mul_mul_same R⁻¹
  have hin : R⁻¹ * Sig * R⁻¹ = 1 := by
    rw [← hRR]
    simp only [Matrix.mul_assoc, pd_mul_inv hR, Matrix.mul_one, pd_inv_mul hR]
  have hcov : transportMap Sig S * Sig * (transportMap Sig S).transpose = S := by
    rw [psd_transpose hT]
    change (R⁻¹ * U * R⁻¹) * Sig * (R⁻¹ * U * R⁻¹) = S
    calc
      _ = R⁻¹ * U * (R⁻¹ * Sig * R⁻¹) * U * R⁻¹ := by noncomm_ring
      _ = R⁻¹ * (U * U) * R⁻¹ := by rw [hin]; noncomm_ring
      _ = S := by
        rw [hUU]
        simp only [Matrix.mul_assoc, pd_mul_inv hR, Matrix.mul_one]
        rw [← Matrix.mul_assoc, pd_inv_mul hR, Matrix.one_mul]
  have htrace : (transportMap Sig S * Sig).trace = U.trace := by
    change (R⁻¹ * U * R⁻¹ * Sig).trace = U.trace
    rw [← hRR]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc R⁻¹ R R, pd_inv_mul hR, Matrix.one_mul]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, pd_mul_inv hR, Matrix.one_mul]
  refine ⟨hT, hcov, ?_⟩
  rw [Matrix.transpose_sub, Matrix.transpose_one, psd_transpose hT]
  have he : (transportMap Sig S - 1) * Sig * (transportMap Sig S - 1) =
      transportMap Sig S * Sig * transportMap Sig S - transportMap Sig S * Sig -
        Sig * transportMap Sig S + Sig := by noncomm_ring
  have hcov' := hcov
  rw [psd_transpose hT] at hcov'
  rw [he, hcov']
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm Sig (transportMap Sig S), htrace]
  simp only [bures, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  dsimp [U, R]
  ring

theorem transport_converse (Sig T : Matrix ι ι ℝ) (hSig : Sig.PosDef)
    (hT : T.PosSemidef) :
    bures Sig (T * Sig * T) = ((T - 1) * Sig * (T - 1)).trace := by
  let R := psdSqrt Sig
  have hR : R.PosSemidef := (sqrt_facts Sig hSig.posSemidef).1
  have hRR : R * R = Sig := (sqrt_facts Sig hSig.posSemidef).2
  have hRTR : (R * T * R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hR] using
      hT.mul_mul_conjTranspose_same R
  have he : R * (T * Sig * T) * R = (R * T * R) * (R * T * R) := by
    rw [← hRR]
    noncomm_ring
  have hsqrt : psdSqrt (R * (T * Sig * T) * R) = R * T * R := by
    rw [he, sqrt_self_square _ hRTR]
  have htr : (R * T * R).trace = (T * Sig).trace := by
    rw [Matrix.trace_mul_cycle, hRR, Matrix.trace_mul_comm]
  unfold bures
  change (T * Sig * T + Sig - (2 : ℝ) • psdSqrt (R * (T * Sig * T) * R)).trace = _
  rw [hsqrt, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, htr]
  have hx : (T - 1) * Sig * (T - 1) = T * Sig * T - T * Sig - Sig * T + Sig := by
    noncomm_ring
  rw [hx, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm Sig T]
  simp only [smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem pd_convex_combination (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B).PosDef := by
  by_cases hz : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [hz, hb1, zero_smul, one_smul, zero_add] using hB
  · exact (hA.smul (lt_of_le_of_ne ha (Ne.symm hz))).add_posSemidef (hB.posSemidef.smul hb)

theorem trace_sqrt_concave (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (psdSqrt A).trace + b * (psdSqrt B).trace ≤
      (psdSqrt (a • A + b • B)).trace := by
  let C := a • A + b • B
  let H := psdSqrt C
  have hC : C.PosDef := pd_convex_combination A B hA hB a b ha hb hab
  have hH : H.PosDef := sqrt_posDef C hC
  have h1 := mul_le_mul_of_nonneg_left (trace_sqrt_variational A H hA.posSemidef hH) ha
  have h2 := mul_le_mul_of_nonneg_left (trace_sqrt_variational B H hB.posSemidef hH) hb
  have hHC : H⁻¹ * C = H := by
    rw [← (sqrt_facts C hC.posSemidef).2]
    change H⁻¹ * (H * H) = H
    rw [← Matrix.mul_assoc, pd_inv_mul hH, Matrix.one_mul]
  have he : a * (H⁻¹ * A).trace + b * (H⁻¹ * B).trace = H.trace := by
    calc
      _ = (H⁻¹ * C).trace := by
        simp only [C, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
          Matrix.trace_smul, smul_eq_mul]
      _ = _ := congrArg Matrix.trace hHC
  have heH : a * H.trace + b * H.trace = H.trace := by
    rw [← add_mul, hab, one_mul]
  change a * (psdSqrt A).trace + b * (psdSqrt B).trace ≤ H.trace
  nlinarith

end Square


open scoped Matrix.Norms.Elementwise

section FeasibleGeometry
variable {n m : ℕ}

theorem feasible_nonempty (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    (sdpFeasibleSet ρ Sig σ).Nonempty := by
  have _ := hρ
  refine ⟨Sig, hSig.posSemidef, hSig.posSemidef.submatrix Sum.inl,
    hSig.posSemidef.submatrix Sum.inr, ?_, (least_eigenvalue_facts Sig hSig σ hσ).2⟩
  have h := transport_converse Sig 1 hSig Matrix.PosSemidef.one
  simp only [Matrix.one_mul, Matrix.mul_one, sub_self, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.trace_zero] at h
  change bures Sig Sig ≤ ρ ^ 2
  rw [h]
  positivity

def transportDomain (Sig : Cov n m) (ρ σ : ℝ) : Set (Cov n m) :=
  {T | T.PosSemidef ∧ (T * Sig * T - σ • 1).PosSemidef ∧
    ((T - 1) * Sig * (T - 1)).trace ≤ ρ ^ 2}

theorem transportDomain_closed (Sig : Cov n m) (ρ σ : ℝ) :
    IsClosed (transportDomain Sig ρ σ) := by
  have hc : Continuous (fun T : Cov n m => T * Sig * T - σ • 1) := by fun_prop
  have ht : Continuous (fun T : Cov n m => ((T - 1) * Sig * (T - 1)).trace) := by
    simp only [Matrix.trace, Matrix.diag]
    fun_prop
  exact isClosed_psd.inter ((isClosed_psd.preimage hc).inter
    (isClosed_le ht continuous_const))

theorem transportDomain_bounded (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ σ : ℝ) (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    Bornology.IsBounded (transportDomain Sig ρ σ) := by
  obtain ⟨hspos, hslow⟩ := least_eigenvalue_facts Sig hSig σ hσ
  have hq : 0 ≤ ρ ^ 2 / σ := div_nonneg (sq_nonneg _) hspos.le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2 + ρ ^ 2 / σ, ?_⟩
  intro T hT
  let A := T - 1
  have hAt : A.transpose = A := by
    simp only [A, Matrix.transpose_sub, Matrix.transpose_one, psd_transpose hT.1]
  have hcost : (A * Sig * A.transpose).trace ≤ ρ ^ 2 := by
    rw [hAt]
    exact hT.2.2
  have hlo := trace_congruence_nonneg hslow A
  have he : A * (Sig - σ • 1) * A.transpose =
      A * Sig * A.transpose - σ • (A * A.transpose) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  rw [he, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hlo
  have hs : σ * ∑ i, ∑ j, (A i j)^2 ≤ ρ ^ 2 := by
    rw [← trace_square_entries]
    linarith
  have heach (i j : Joint n m) : (A i j)^2 ≤ ρ ^ 2 / σ := by
    have h1 : (A i j)^2 ≤ ∑ k, (A i k)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
    have h2 : (∑ k, (A i k)^2) ≤ ∑ l, ∑ k, (A l k)^2 :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg (A l k)))
        (Finset.mem_univ i)
    apply (le_div_iff₀ hspos).mpr
    nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [Real.norm_eq_abs]
  have ha : |A i j| ≤ 1 + ρ ^ 2 / σ := by
    apply abs_le.mpr
    constructor <;> nlinarith [heach i j, sq_nonneg (A i j - 1), sq_nonneg (A i j + 1)]
  have hi : |(1 : Cov n m) i j| ≤ 1 := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  calc
    |T i j| = |A i j + (1 : Cov n m) i j| := by simp [A]
    _ ≤ |A i j| + |(1 : Cov n m) i j| := abs_add_le _ _
    _ ≤ 2 + ρ ^ 2 / σ := by linarith

theorem transportDomain_image (Sig : Cov n m) (hSig : Sig.PosDef) (ρ σ : ℝ) :
    (fun T : Cov n m => T * Sig * T) '' transportDomain Sig ρ σ =
      sdpFeasibleSet ρ Sig σ := by
  ext S
  constructor
  · rintro ⟨T, hT, rfl⟩
    have hS : (T * Sig * T).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hT.1] using
        hSig.posSemidef.mul_mul_conjTranspose_same T
    refine ⟨hS, hS.submatrix Sum.inl, hS.submatrix Sum.inr, ?_, hT.2.1⟩
    change bures Sig (T * Sig * T) ≤ ρ ^ 2
    rw [transport_converse Sig T hSig hT.1]
    exact hT.2.2
  · intro hS
    obtain ⟨hT, hcov, hcost⟩ := transport_facts Sig S hSig hS.1
    rw [psd_transpose hT] at hcov
    refine ⟨transportMap Sig S, ⟨hT, ?_, ?_⟩, hcov⟩
    · rw [hcov]
      exact hS.2.2.2.2
    · rw [Matrix.transpose_sub, Matrix.transpose_one, psd_transpose hT] at hcost
      rw [hcost]
      exact hS.2.2.2.1

theorem feasible_isCompact (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    IsCompact (sdpFeasibleSet ρ Sig σ) := by
  have _ := hρ
  have hK : IsCompact (transportDomain Sig ρ σ) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨transportDomain_closed Sig ρ σ, transportDomain_bounded Sig hSig ρ σ hσ⟩
  rw [← transportDomain_image Sig hSig ρ σ]
  exact hK.image (by fun_prop)

theorem feasible_convex (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    Convex ℝ (sdpFeasibleSet ρ Sig σ) := by
  have _ := hρ
  intro A hA B hB a b ha hb hab
  have hspos := (least_eigenvalue_facts Sig hSig σ hσ).1
  have hAP : A.PosDef := pd_of_lower hspos hA.2.2.2.2
  have hBP : B.PosDef := pd_of_lower hspos hB.2.2.2.2
  have hP : (a • A + b • B).PosSemidef := (hA.1.smul ha).add (hB.1.smul hb)
  refine ⟨hP, hP.submatrix Sum.inl, hP.submatrix Sum.inr, ?_, ?_⟩
  · let R := psdSqrt Sig
    have hR : R.PosDef := sqrt_posDef Sig hSig
    have hinj : Function.Injective (Matrix.mulVec R) := by
      intro x y hxy
      have h := congrArg (fun z => R⁻¹ *ᵥ z) hxy
      simpa only [Matrix.mulVec_mulVec, pd_inv_mul hR, Matrix.one_mulVec] using h
    have hRA : (R * A * R).PosDef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hR.posSemidef]
        using hAP.conjTranspose_mul_mul_same hinj
    have hRB : (R * B * R).PosDef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hR.posSemidef]
        using hBP.conjTranspose_mul_mul_same hinj
    have hc := trace_sqrt_concave (R * A * R) (R * B * R) hRA hRB a b ha hb hab
    have he : R * (a • A + b • B) * R = a • (R * A * R) + b • (R * B * R) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hca := mul_le_mul_of_nonneg_left hA.2.2.2.1 ha
    have hcb := mul_le_mul_of_nonneg_left hB.2.2.2.1 hb
    change bures Sig (a • A + b • B) ≤ ρ ^ 2
    simp only [bures, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    change a * A.trace + b * B.trace + Sig.trace -
      2 * (psdSqrt (R * (a • A + b • B) * R)).trace ≤ ρ ^ 2
    rw [he]
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] at hca hcb
    change a * (A.trace + Sig.trace - 2 * (psdSqrt (R * A * R)).trace) ≤ a * ρ^2 at hca
    change b * (B.trace + Sig.trace - 2 * (psdSqrt (R * B * R)).trace) ≤ b * ρ^2 at hcb
    have heSig : a * Sig.trace + b * Sig.trace = Sig.trace := by
      rw [← add_mul, hab, one_mul]
    have herho : a * ρ^2 + b * ρ^2 = ρ^2 := by
      rw [← add_mul, hab, one_mul]
    linarith
  · have h := (hA.2.2.2.2.smul ha).add (hB.2.2.2.2.smul hb)
    have he : a • (A - σ • (1 : Cov n m)) + b • (B - σ • (1 : Cov n m)) =
        (a • A + b • B) - σ • (1 : Cov n m) := by
      calc
        _ = a • A + b • B - (a + b) • (σ • (1 : Cov n m)) := by module
        _ = _ := by rw [hab, one_smul]
    rwa [he] at h

end FeasibleGeometry

end WassersteinKalmanProof

open Matrix WassersteinDRO.Shrinkage
open scoped BigOperators

namespace WassersteinKalmanProof

section Blocks
variable {n m : ℕ}

theorem feasible_posDef (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ σ : ℝ) (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ) : S.PosDef :=
  pd_of_lower (least_eigenvalue_facts Sig hSig σ hσ).1 hS.2.2.2.2

theorem schur_observation_posDef (S : Cov n m) (hS : S.PosDef) :
    S.toBlocks₂₂.PosDef := hS.submatrix Sum.inr_injective

theorem schur_cross_transpose (S : Cov n m) (hS : S.PosSemidef) :
    S.toBlocks₁₂.transpose = S.toBlocks₂₁ := by
  ext i j
  exact congrFun (congrFun (psd_transpose hS) (Sum.inr i)) (Sum.inl j)

theorem slope_mul (S : Cov n m) (hS : S.PosDef) :
    slope S * S.toBlocks₂₂ = S.toBlocks₁₂ := by
  rw [slope, Matrix.mul_assoc, pd_inv_mul (schur_observation_posDef S hS), Matrix.mul_one]

theorem mul_slope_transpose (S : Cov n m) (hS : S.PosDef) :
    S.toBlocks₂₂ * (slope S).transpose = S.toBlocks₂₁ := by
  have h := congrArg Matrix.transpose (slope_mul S hS)
  rwa [Matrix.transpose_mul, psd_transpose (schur_observation_posDef S hS).posSemidef,
    schur_cross_transpose S hS.posSemidef] at h

theorem residual_mul (S : Cov n m) (G : Matrix (Fin n) (Fin m) ℝ) :
    residual G * S = Matrix.fromCols
      (S.toBlocks₁₁ - G * S.toBlocks₂₁) (S.toBlocks₁₂ - G * S.toBlocks₂₂) := by
  unfold residual
  nth_rw 1 [← Matrix.fromBlocks_toBlocks S]
  simp only [Matrix.fromCols_mul_fromBlocks, Matrix.one_mul, Matrix.neg_mul, sub_eq_add_neg]

theorem residual_covariance (S : Cov n m) (G : Matrix (Fin n) (Fin m) ℝ) :
    residual G * S * (residual G).transpose =
      S.toBlocks₁₁ - G * S.toBlocks₂₁ - S.toBlocks₁₂ * G.transpose +
        G * S.toBlocks₂₂ * G.transpose := by
  rw [residual_mul]
  simp only [residual, Matrix.transpose_fromCols, Matrix.transpose_one,
    Matrix.transpose_neg, Matrix.fromCols_mul_fromRows, Matrix.mul_one,
    Matrix.mul_neg, Matrix.sub_mul]
  abel

theorem schur_residual_matrix (S : Cov n m) (hS : S.PosDef) :
    residual (slope S) * S * (residual (slope S)).transpose =
      S.toBlocks₁₁ - S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ * S.toBlocks₂₁ := by
  rw [residual_covariance, slope_mul S hS]
  simp only [sub_add_cancel, slope]

theorem schur_residual_trace (S : Cov n m) (hS : S.PosDef) :
    (residual (slope S) * S * (residual (slope S)).transpose).trace = sdpObjective S := by
  rw [schur_residual_matrix S hS]
  rfl

theorem schur_residual_observation (S : Cov n m) (hS : S.PosDef)
    (i : Fin n) (j : Fin m) :
    (residual (slope S) * S) i (Sum.inr j) = 0 := by
  rw [residual_mul, slope_mul S hS]
  simp

theorem schur_nonneg (S : Cov n m) (hS : S.PosDef) : 0 ≤ sdpObjective S := by
  rw [← schur_residual_trace S hS]
  exact trace_congruence_nonneg hS.posSemidef _

theorem schur_completion (S : Cov n m) (hS : S.PosDef)
    (G : Matrix (Fin n) (Fin m) ℝ) :
    residual G * S * (residual G).transpose =
      residual (slope S) * S * (residual (slope S)).transpose +
        (G - slope S) * S.toBlocks₂₂ * (G - slope S).transpose := by
  rw [residual_covariance S G, residual_covariance S (slope S)]
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
  rw [slope_mul S hS, Matrix.mul_assoc G S.toBlocks₂₂ (slope S).transpose,
    mul_slope_transpose S hS]
  have hbal : slope S * S.toBlocks₂₁ = S.toBlocks₁₂ * (slope S).transpose := by
    rw [← mul_slope_transpose S hS, ← Matrix.mul_assoc, slope_mul S hS]
  rw [hbal]
  abel

theorem riskMatrix_psd (G : Matrix (Fin n) (Fin m) ℝ) : (riskMatrix G).PosSemidef := by
  simpa only [riskMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (residual G)

theorem riskMatrix_trace (S : Cov n m) (G : Matrix (Fin n) (Fin m) ℝ) :
    (riskMatrix G * S).trace = (residual G * S * (residual G).transpose).trace := by
  unfold riskMatrix
  exact (Matrix.trace_mul_cycle (residual G) S (residual G).transpose).symm

theorem continuousOn_sdpObjective (K : Set (Cov n m)) (hK : ∀ S ∈ K, S.PosDef) :
    ContinuousOn sdpObjective K := by
  intro S hS
  have hc11 : Continuous (fun T : Cov n m => T.toBlocks₁₁) := by
    unfold Matrix.toBlocks₁₁
    fun_prop
  have hc12 : Continuous (fun T : Cov n m => T.toBlocks₁₂) := by
    unfold Matrix.toBlocks₁₂
    fun_prop
  have hc21 : Continuous (fun T : Cov n m => T.toBlocks₂₁) := by
    unfold Matrix.toBlocks₂₁
    fun_prop
  have hc22 : Continuous (fun T : Cov n m => T.toBlocks₂₂) := by
    unfold Matrix.toBlocks₂₂
    fun_prop
  have hi : ContinuousWithinAt (fun T : Cov n m => T.toBlocks₂₂⁻¹) K S :=
    (continuousAt_inv_pd S.toBlocks₂₂ (schur_observation_posDef S (hK S hS))).comp_continuousWithinAt
      hc22.continuousWithinAt
  have hout : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ ×
      (Matrix (Fin n) (Fin m) ℝ × (Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin n) ℝ)) =>
      (p.1 - p.2.1 * p.2.2.1 * p.2.2.2).trace) := by fun_prop
  exact hout.continuousAt.comp_continuousWithinAt
    (hc11.continuousWithinAt.prodMk (hc12.continuousWithinAt.prodMk
      (hi.prodMk hc21.continuousWithinAt)))

end Blocks

end WassersteinKalmanProof

open scoped BigOperators
open Set

namespace WassersteinKalmanProof

section FiniteScalar
variable {ι : Type*} [Fintype ι]

noncomputable def scalarCost (a d : ι → ℝ) (γ : ℝ) : ℝ := ∑ i, a i * (d i / (γ - d i)) ^ 2

theorem scalar_cost_bound (a d : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L γ : ℝ) (hd : ∀ i, d i ≤ L) (hγ : L < γ) :
    scalarCost a d γ ≤ (∑ i, a i * (d i) ^ 2) / (γ - L) ^ 2 := by
  unfold scalarCost
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hp : 0 < γ - L := sub_pos.mpr hγ
  have hi : γ - L ≤ γ - d i := by linarith [hd i]
  rw [div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (mul_nonneg (ha i) (sq_nonneg _))
    (sq_pos_of_pos hp) (sq_le_sq₀ hp.le (hp.le.trans hi) |>.2 hi)

theorem scalar_cost_root (a d : ι → ℝ) (ha : ∀ i, 0 < a i)
    (_hd : ∀ i, 0 ≤ d i) (hpos : ∃ i, 0 < d i) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ γ : ℝ, (∀ i, d i < γ) ∧ scalarCost a d γ = ρ ^ 2 := by
  classical
  obtain ⟨j, hj⟩ := hpos
  let : Nonempty ι := ⟨j⟩
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hmax' : ∀ k, d k ≤ d i := fun k => hmax k (Finset.mem_univ k)
  have hi : 0 < d i := hj.trans_le (hmax' j)
  let q : ℝ := a i * (d i) ^ 2
  have hq : 0 < q := mul_pos (ha i) (sq_pos_of_pos hi)
  let δ : ℝ := q / (1 + ρ ^ 2 + q)
  have hden : 0 < 1 + ρ ^ 2 + q := by positivity
  have hδ : 0 < δ := div_pos hq hden
  have hδ1 : δ < 1 := (div_lt_one hden).2 (by nlinarith [sq_nonneg ρ])
  have hδρ : δ * ρ ^ 2 < q := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_nonneg q]
  have hlow : ρ ^ 2 < scalarCost a d (d i + δ) := by
    have hterm : ρ ^ 2 < a i * (d i / (d i + δ - d i)) ^ 2 := by
      rw [show d i + δ - d i = δ by ring, div_pow, ← mul_div_assoc]
      apply (lt_div_iff₀ (sq_pos_of_pos hδ)).2
      have hsq : δ ^ 2 ≤ δ := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg ρ)
      dsimp [q] at hδρ
      nlinarith
    unfold scalarCost
    exact hterm.trans_le (Finset.single_le_sum
      (fun k _ => mul_nonneg (ha k).le (sq_nonneg (d k / (d i + δ - d k)))) (Finset.mem_univ i))
  let C : ℝ := ∑ k, a k * (d k) ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => mul_nonneg (ha k).le (sq_nonneg _)
  let b : ℝ := δ + 1 + (C + 1) / ρ ^ 2
  have hr2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hb1 : 1 < b := by
    dsimp [b]
    have : 0 ≤ (C + 1) / ρ ^ 2 := by positivity
    linarith
  have hb : 0 < b := zero_lt_one.trans hb1
  have hbr : C < b * ρ ^ 2 := by
    have he : ((C + 1) / ρ ^ 2) * ρ ^ 2 = C + 1 := div_mul_cancel₀ _ hr2.ne'
    dsimp [b]
    nlinarith [mul_pos hδ hr2]
  have hhigh : scalarCost a d (d i + b) < ρ ^ 2 := by
    have hbound := scalar_cost_bound a d (fun k => (ha k).le) (d i) (d i + b)
      hmax' (by linarith)
    have hdenb : d i + b - d i = b := by ring
    rw [hdenb] at hbound
    apply hbound.trans_lt
    apply (div_lt_iff₀ (sq_pos_of_pos hb)).2
    have hsq : b < b ^ 2 := by nlinarith
    have hh := mul_lt_mul_of_pos_right hsq hr2
    dsimp [C] at hbr
    nlinarith
  have hab : d i + δ ≤ d i + b := by
    dsimp [b]
    have : 0 ≤ (C + 1) / ρ ^ 2 := by positivity
    linarith
  have hc : ContinuousOn (scalarCost a d) (Icc (d i + δ) (d i + b)) := by
    unfold scalarCost
    apply continuousOn_finsetSum
    intro k _
    apply continuousOn_const.mul
    apply ContinuousOn.pow
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro x hx
    have : d k < x := lt_of_le_of_lt (hmax' k) (lt_of_lt_of_le (by linarith) hx.1)
    exact (sub_pos.mpr this).ne'
  obtain ⟨γ, hγ, he⟩ := intermediate_value_Icc' hab hc ⟨hhigh.le, hlow.le⟩
  exact ⟨γ, fun k => lt_of_le_of_lt (hmax' k)
    (lt_of_lt_of_le (by linarith) hγ.1), he⟩

theorem scalar_resolvent_error_small (a d : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hd : ∀ i, 0 ≤ d i) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ (∀ i, d i < γ) ∧
      (∑ i, a i * (d i) ^ 2 / (γ - d i)) < ε := by
  classical
  let L : ℝ := ∑ i, d i
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => hd i
  have hdi : ∀ i, d i ≤ L := fun i =>
    Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  let C : ℝ := ∑ i, a i * (d i) ^ 2
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (sq_nonneg _)
  let γ := L + 1 + C / ε
  have hγL : L < γ := by
    dsimp [γ]
    have : 0 ≤ C / ε := by positivity
    linarith
  refine ⟨γ, hL.trans_lt hγL, fun i => (hdi i).trans_lt hγL, ?_⟩
  calc
    _ ≤ ∑ i, a i * (d i) ^ 2 / (γ - L) := by
      apply Finset.sum_le_sum
      intro i _
      exact div_le_div_of_nonneg_left (mul_nonneg (ha i) (sq_nonneg _))
        (sub_pos.mpr hγL) (by linarith [hdi i])
    _ = C / (γ - L) := by rw [Finset.sum_div]
    _ < ε := by
      apply (div_lt_iff₀ (sub_pos.mpr hγL)).2
      have he : C / ε * ε = C := div_mul_cancel₀ _ hε.ne'
      dsimp [γ]
      nlinarith

end FiniteScalar

end WassersteinKalmanProof

open Matrix WassersteinDRO.Shrinkage
open scoped BigOperators

namespace WassersteinKalmanProof

section Spectral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def spectralDiag (U : Matrix.unitaryGroup ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  (U : Matrix ι ι ℝ) * Matrix.diagonal d * (U : Matrix ι ι ℝ).transpose

theorem spectralDiag_const (U : Matrix.unitaryGroup ι ℝ) (c : ℝ) :
    spectralDiag U (fun _ => c) = c • (1 : Matrix ι ι ℝ) := by
  have h : Matrix.diagonal (fun _ : ι => c) = c • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [spectralDiag, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, unitary_real_right]

theorem spectralDiag_sub (U : Matrix.unitaryGroup ι ℝ) (a b : ι → ℝ) :
    spectralDiag U (fun i => a i - b i) = spectralDiag U a - spectralDiag U b := by
  unfold spectralDiag
  rw [← Matrix.diagonal_sub a b, Matrix.mul_sub, Matrix.sub_mul]


theorem spectralDiag_smul (U : Matrix.unitaryGroup ι ℝ) (c : ℝ) (a : ι → ℝ) :
    spectralDiag U (fun i => c * a i) = c • spectralDiag U a := by
  change spectralDiag U (c • a) = _
  simp only [spectralDiag, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem spectralDiag_mul (U : Matrix.unitaryGroup ι ℝ) (a b : ι → ℝ) :
    spectralDiag U a * spectralDiag U b = spectralDiag U (fun i => a i * b i) := by
  unfold spectralDiag
  calc
    _ = (U : Matrix ι ι ℝ) * Matrix.diagonal a *
        ((U : Matrix ι ι ℝ).transpose * U) * Matrix.diagonal b *
        (U : Matrix ι ι ℝ).transpose := by noncomm_ring
    _ = _ := by rw [unitary_real_left, Matrix.mul_one, Matrix.mul_assoc _ (Matrix.diagonal a),
      Matrix.diagonal_mul_diagonal]

theorem spectralDiag_psd (U : Matrix.unitaryGroup ι ℝ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (spectralDiag U a).PosSemidef := by
  simpa only [spectralDiag, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.diagonal ha).mul_mul_conjTranspose_same (U : Matrix ι ι ℝ)

theorem spectralDiag_pd (U : Matrix.unitaryGroup ι ℝ) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    (spectralDiag U a).PosDef := by
  have hu : IsUnit (U : Matrix ι ι ℝ) := Unitary.isUnit_coe
  have h := hu.posDef_star_right_conjugate_iff.mpr (Matrix.PosDef.diagonal ha)
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    spectralDiag] using h

theorem spectralDiag_inv (U : Matrix.unitaryGroup ι ℝ) (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    (spectralDiag U a)⁻¹ = spectralDiag U (fun i => (a i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [spectralDiag_mul]
  simp only [mul_inv_cancel₀ (ha _), spectralDiag_const, one_smul]

theorem spectralDiag_trace (U : Matrix.unitaryGroup ι ℝ) (a : ι → ℝ)
    (Sig : Matrix ι ι ℝ) :
    (spectralDiag U a * Sig).trace =
      ∑ i, a i * ((U : Matrix ι ι ℝ).transpose * Sig * U) i i := by
  unfold spectralDiag
  calc
    _ = ((U : Matrix ι ι ℝ) * (Matrix.diagonal a *
        ((U : Matrix ι ι ℝ).transpose * Sig))).trace := by congr 1; noncomm_ring
    _ = (Matrix.diagonal a * ((U : Matrix ι ι ℝ).transpose * Sig) * U).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Matrix.diagonal a * ((U : Matrix ι ι ℝ).transpose * Sig * U)).trace := by
      rw [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

theorem spectral_weights_pos (U : Matrix.unitaryGroup ι ℝ)
    (Sig : Matrix ι ι ℝ) (hSig : Sig.PosDef) (i : ι) :
    0 < ((U : Matrix ι ι ℝ).transpose * Sig * U) i i := by
  have hu : IsUnit (U : Matrix ι ι ℝ) := Unitary.isUnit_coe
  have h := hu.posDef_star_left_conjugate_iff.mpr hSig
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    h.diag_pos (i := i)

theorem positive_eigenvalue_of_ne_zero (D : Matrix ι ι ℝ) (hD : D.PosSemidef) (hne : D ≠ 0) :
    ∃ i, 0 < hD.isHermitian.eigenvalues i := by
  by_contra hn
  push Not at hn
  have hz : hD.isHermitian.eigenvalues = 0 := by
    funext i
    exact le_antisymm (hn i) (hD.eigenvalues_nonneg i)
  apply hne
  rw [spectral_real D hD.isHermitian, hz]
  simp

noncomputable def resolvent (D : Matrix ι ι ℝ) (γ : ℝ) : Matrix ι ι ℝ :=
  γ • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹

theorem resolvent_spectral (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (γ : ℝ) (hγ : ∀ i, hD.isHermitian.eigenvalues i < γ) :
    (γ • (1 : Matrix ι ι ℝ) - D).PosDef ∧
    resolvent D γ = spectralDiag hD.isHermitian.eigenvectorUnitary
      (fun i => γ / (γ - hD.isHermitian.eigenvalues i)) ∧
    dualMatrix D γ = spectralDiag hD.isHermitian.eigenvectorUnitary
      (fun i => γ ^ 2 / (γ - hD.isHermitian.eigenvalues i) - γ) := by
  let U := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  have he : γ • (1 : Matrix ι ι ℝ) - D = spectralDiag U (fun i => γ - d i) := by
    rw [spectralDiag_sub, spectralDiag_const]
    congr 1
    exact spectral_real D hD.isHermitian
  have hp : (γ • (1 : Matrix ι ι ℝ) - D).PosDef := by
    rw [he]
    exact spectralDiag_pd U _ fun i => sub_pos.mpr (hγ i)
  have hin := spectralDiag_inv U (fun i => γ - d i) (fun i => (sub_pos.mpr (hγ i)).ne')
  refine ⟨hp, ?_, ?_⟩
  · rw [resolvent, he, hin, ← spectralDiag_smul]
    simp only [div_eq_mul_inv, U, d]
  · rw [dualMatrix, he, hin, ← spectralDiag_smul, ← spectralDiag_const U γ,
      ← spectralDiag_sub]
    simp only [div_eq_mul_inv, U, d]

theorem resolvent_psd_lower (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (γ : ℝ) (_hγ0 : 0 < γ) (hγ : ∀ i, hD.isHermitian.eigenvalues i < γ) :
    (resolvent D γ).PosSemidef ∧ (resolvent D γ * resolvent D γ - 1).PosSemidef := by
  obtain ⟨_, he, _⟩ := resolvent_spectral D hD γ hγ
  have ht : ∀ i, 1 ≤ γ / (γ - hD.isHermitian.eigenvalues i) := by
    intro i
    apply (le_div_iff₀ (sub_pos.mpr (hγ i))).2
    nlinarith [hD.eigenvalues_nonneg i]
  refine ⟨?_, ?_⟩
  · rw [he]
    exact spectralDiag_psd _ _ fun i => le_trans (by norm_num) (ht i)
  · rw [he, spectralDiag_mul, ← one_smul ℝ (1 : Matrix ι ι ℝ),
      ← spectralDiag_const hD.isHermitian.eigenvectorUnitary 1, ← spectralDiag_sub]
    apply spectralDiag_psd
    intro i
    nlinarith [ht i]

theorem resolvent_covariance_lower (Sig D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (σ γ : ℝ) (hσ : 0 ≤ σ) (hSig : (Sig - σ • (1 : Matrix ι ι ℝ)).PosSemidef)
    (hγ0 : 0 < γ) (hγ : ∀ i, hD.isHermitian.eigenvalues i < γ) :
    (resolvent D γ * Sig * resolvent D γ - σ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  let T := resolvent D γ
  obtain ⟨hT, hTT⟩ := resolvent_psd_lower D hD γ hγ0 hγ
  have hT' : T.PosSemidef := hT
  have hp : (T * (Sig - σ • 1) * T).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hT'] using
      hSig.mul_mul_conjTranspose_same T
  have he : T * Sig * T - σ • 1 = T * (Sig - σ • 1) * T + σ • (T * T - 1) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, smul_sub]
    abel
  rw [he]
  exact hp.add (hTT.smul hσ)

theorem spectralDiag_quadratic_trace (U : Matrix.unitaryGroup ι ℝ) (t : ι → ℝ)
    (Sig : Matrix ι ι ℝ) :
    (spectralDiag U t * Sig * spectralDiag U t).trace =
      ∑ i, (t i) ^ 2 * ((U : Matrix ι ι ℝ).transpose * Sig * U) i i := by
  rw [Matrix.trace_mul_cycle, spectralDiag_mul, spectralDiag_trace]
  simp only [pow_two]

theorem spectralDiag_sandwich_trace (U : Matrix.unitaryGroup ι ℝ) (d t : ι → ℝ)
    (Sig : Matrix ι ι ℝ) :
    (spectralDiag U d * (spectralDiag U t * Sig * spectralDiag U t)).trace =
      ∑ i, d i * (t i) ^ 2 * ((U : Matrix ι ι ℝ).transpose * Sig * U) i i := by
  calc
    _ = (spectralDiag U d * spectralDiag U t * Sig * spectralDiag U t).trace := by
      congr 1
      noncomm_ring
    _ = (spectralDiag U t * (spectralDiag U d * spectralDiag U t) * Sig).trace :=
      Matrix.trace_mul_cycle _ _ _
    _ = _ := by
      rw [spectralDiag_mul, spectralDiag_mul, spectralDiag_trace]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem resolvent_cost (Sig D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (γ : ℝ) (hγ : ∀ i, hD.isHermitian.eigenvalues i < γ) :
    ((resolvent D γ - 1) * Sig * (resolvent D γ - 1)).trace =
      scalarCost (fun i => ((hD.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ).transpose *
        Sig * hD.isHermitian.eigenvectorUnitary) i i) hD.isHermitian.eigenvalues γ := by
  let U := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  have he := (resolvent_spectral D hD γ hγ).2.1
  have hdiff : resolvent D γ - 1 = spectralDiag U (fun i => d i / (γ - d i)) := by
    rw [he, ← one_smul ℝ (1 : Matrix ι ι ℝ), ← spectralDiag_const U 1,
      ← spectralDiag_sub]
    congr 1
    funext i
    dsimp [d]
    field_simp [(sub_pos.mpr (hγ i)).ne']
    ring
  rw [hdiff, spectralDiag_quadratic_trace]
  unfold scalarCost
  apply Finset.sum_congr rfl
  intro i _
  dsimp [U, d]
  ring

theorem resolvent_dual_identity (ρ : ℝ) (Sig D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (γ : ℝ) (hγ : ∀ i, hD.isHermitian.eigenvalues i < γ) :
    dualValue ρ Sig D γ - (D * (resolvent D γ * Sig * resolvent D γ)).trace =
      γ * (ρ ^ 2 - scalarCost
        (fun i => ((hD.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ).transpose *
          Sig * hD.isHermitian.eigenvectorUnitary) i i) hD.isHermitian.eigenvalues γ) := by
  let U := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  let a := fun i => ((U : Matrix ι ι ℝ).transpose * Sig * U) i i
  have hspec : D = spectralDiag U d := spectral_real D hD.isHermitian
  obtain ⟨_, ht, hb⟩ := resolvent_spectral D hD γ hγ
  have htr : (D * (resolvent D γ * Sig * resolvent D γ)).trace =
      ∑ i, d i * (γ / (γ - d i)) ^ 2 * a i := by
    calc
      _ = (spectralDiag U d * (spectralDiag U (fun i => γ / (γ - d i)) * Sig *
          spectralDiag U (fun i => γ / (γ - d i)))).trace := by rw [← hspec, ← ht]
      _ = _ := spectralDiag_sandwich_trace U d _ Sig
  have hbtr : (dualMatrix D γ * Sig).trace =
      ∑ i, (γ ^ 2 / (γ - d i) - γ) * a i := by
    rw [hb, spectralDiag_trace]
  have hs : (∑ i, (γ ^ 2 / (γ - d i) - γ) * a i) -
      (∑ i, d i * (γ / (γ - d i)) ^ 2 * a i) =
      -γ * scalarCost a d γ := by
    rw [← Finset.sum_sub_distrib]
    unfold scalarCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hn : γ - d i ≠ 0 := (sub_pos.mpr (hγ i)).ne'
    field_simp [hn]
    ring
  unfold dualValue
  rw [htr, hbtr]
  change γ * ρ ^ 2 + _ - _ = γ * (ρ ^ 2 - scalarCost a d γ)
  linarith

theorem resolvent_zero_radius_error (Sig D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (γ : ℝ) (hγ : ∀ i, hD.isHermitian.eigenvalues i < γ) :
    dualValue 0 Sig D γ - (D * Sig).trace =
      ∑ i, (((hD.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ).transpose * Sig *
        hD.isHermitian.eigenvectorUnitary) i i) * (hD.isHermitian.eigenvalues i) ^ 2 /
          (γ - hD.isHermitian.eigenvalues i) := by
  let U := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  have hs : D = spectralDiag U d := spectral_real D hD.isHermitian
  have hb := (resolvent_spectral D hD γ hγ).2.2
  unfold dualValue
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  have htr : (D * Sig).trace = ∑ i, d i * ((U : Matrix ι ι ℝ).transpose * Sig * U) i i := by
    calc
      _ = (spectralDiag U d * Sig).trace := congrArg (fun A => (A * Sig).trace) hs
      _ = _ := spectralDiag_trace U d Sig
  rw [hb, spectralDiag_trace, htr, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [U, d]
  field_simp [(sub_pos.mpr (hγ i)).ne']
  ring

end Spectral

end WassersteinKalmanProof

open Matrix WassersteinDRO.Shrinkage Filter Set
open scoped BigOperators Topology

namespace WassersteinKalmanProof

variable {n m : ℕ}

theorem feasible_maximizer (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    ∃ S ∈ sdpFeasibleSet ρ Sig σ, IsMaxOn sdpObjective (sdpFeasibleSet ρ Sig σ) S := by
  exact (feasible_isCompact Sig hSig ρ hρ σ hσ).exists_isMaxOn
    (feasible_nonempty Sig hSig ρ hρ σ hσ)
    (continuousOn_sdpObjective _ fun S hS => feasible_posDef Sig hSig ρ σ hσ S hS)

theorem schur_fixed_upper (S : Cov n m) (hS : S.PosDef)
    (G : Matrix (Fin n) (Fin m) ℝ) :
    sdpObjective S ≤ (riskMatrix G * S).trace := by
  rw [riskMatrix_trace, schur_completion S hS G, Matrix.trace_add,
    schur_residual_trace S hS]
  exact le_add_of_nonneg_right (trace_congruence_nonneg
    (schur_observation_posDef S hS).posSemidef (G - slope S))

theorem continuousAt_slope (S : Cov n m) (hS : S.PosDef) : ContinuousAt slope S := by
  have h12 : Continuous (fun V : Cov n m => V.toBlocks₁₂) := by
    change Continuous (fun V : Cov n m => fun i j => V (Sum.inl i) (Sum.inr j))
    fun_prop
  have h22 : Continuous (fun V : Cov n m => V.toBlocks₂₂) := by
    change Continuous (fun V : Cov n m => fun i j => V (Sum.inr i) (Sum.inr j))
    fun_prop
  have hi := (continuousAt_inv_pd S.toBlocks₂₂ (schur_observation_posDef S hS)).comp h22.continuousAt
  have hm : Continuous (fun p : Matrix (Fin n) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ =>
      p.1 * p.2) := by fun_prop
  exact hm.continuousAt.comp (h12.continuousAt.prodMk hi)

theorem continuous_riskMatrix : Continuous (@riskMatrix n m) := by
  have hr : Continuous (@residual n m) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    cases j with
    | inl j => exact continuous_const
    | inr j => change Continuous (fun G : Matrix (Fin n) (Fin m) ℝ => -G i j); fun_prop
  exact hr.matrix_transpose.matrix_mul hr

theorem schur_support (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ)
    (hmax : IsMaxOn sdpObjective (sdpFeasibleSet ρ Sig σ) S)
    (V : Cov n m) (hV : V ∈ sdpFeasibleSet ρ Sig σ) :
    (riskMatrix (slope S) * V).trace ≤ sdpObjective S := by
  let Δ := V - S
  have hSP := feasible_posDef Sig hSig ρ σ hσ S hS
  have hfeas : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → S + t • Δ ∈ sdpFeasibleSet ρ Sig σ := by
    intro t ht ht1
    have he : S + t • Δ = (1 - t) • S + t • V := by dsimp [Δ]; module
    rw [he]
    exact feasible_convex Sig hSig ρ hρ σ hσ hS hV (sub_nonneg.mpr ht1) ht (by ring)
  have hineq : ∀ t : ℝ, 0 < t → t < 1 →
      (riskMatrix (slope (S + t • Δ)) * Δ).trace ≤ 0 := by
    intro t ht ht1
    have htK := hfeas t ht.le ht1.le
    have htP := feasible_posDef Sig hSig ρ σ hσ _ htK
    have hm := (hmax htK).trans (schur_fixed_upper S hSP (slope (S + t • Δ)))
    rw [← schur_residual_trace _ htP, ← riskMatrix_trace,
      Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul] at hm
    simp only [smul_eq_mul] at hm
    by_contra hn
    have hp := mul_pos ht (lt_of_not_ge hn)
    linarith
  have hc : ContinuousAt (fun t : ℝ =>
      (riskMatrix (slope (S + t • Δ)) * Δ).trace) 0 := by
    have hpath : Continuous (fun t : ℝ => S + t • Δ) := by fun_prop
    have hslope : ContinuousAt slope (S + (0 : ℝ) • Δ) := by
      simpa only [zero_smul, add_zero] using continuousAt_slope S hSP
    have hg := hslope.comp (f := fun t : ℝ => S + t • Δ) (hpath.continuousAt (x := 0))
    have hf : Continuous (fun G : Matrix (Fin n) (Fin m) ℝ => (riskMatrix G * Δ).trace) :=
      (continuous_riskMatrix.matrix_mul continuous_const).matrix_trace
    exact hf.continuousAt.comp hg
  have hnonpos : (riskMatrix (slope S) * Δ).trace ≤ 0 := by
    have hl := hc.tendsto.mono_left (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
    simp only [zero_smul, add_zero] at hl
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left] with t ht ht1
    exact hineq t ht ht1
  dsimp [Δ] at hnonpos
  rw [Matrix.mul_sub, Matrix.trace_sub, riskMatrix_trace S (slope S),
    schur_residual_trace S hSP] at hnonpos
  linarith

theorem zero_dualMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ℝ) (hγ : 0 < γ) : dualMatrix (0 : Matrix ι ι ℝ) γ = 0 := by
  have hi : (γ • (1 : Matrix ι ι ℝ))⁻¹ = γ⁻¹ • (1 : Matrix ι ι ℝ) := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [mul_inv_cancel₀ hγ.ne', one_smul]
  unfold dualMatrix
  rw [sub_zero, hi, smul_smul]
  have he : γ ^ 2 * γ⁻¹ = γ := by field_simp
  rw [he, sub_self]

theorem support_approx_dual (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ)
    (D : Cov n m) (hD : D.PosSemidef) (f : ℝ) (hf : 0 ≤ f)
    (hsupport : ∀ V ∈ sdpFeasibleSet ρ Sig σ, (D * V).trace ≤ f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ (γ • (1 : Cov n m) - D).PosDef ∧
      dualValue ρ Sig D γ < f + ε := by
  by_cases hDz : D = 0
  · subst D
    let γ := ε / (2 * (ρ ^ 2 + 1))
    have hden : 0 < 2 * (ρ ^ 2 + 1) := by positivity
    have hγ : 0 < γ := div_pos hε hden
    refine ⟨γ, hγ, ?_, ?_⟩
    · simpa only [sub_zero] using (Matrix.PosDef.one (n := Joint n m) (R := ℝ)).smul hγ
    · unfold dualValue
      rw [zero_dualMatrix γ hγ, Matrix.zero_mul, Matrix.trace_zero, add_zero]
      have hb : γ * ρ ^ 2 < ε := by
        dsimp [γ]
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith [sq_nonneg ρ]
      linarith
  let U := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  let a := fun i => ((U : Cov n m).transpose * Sig * U) i i
  have ha : ∀ i, 0 < a i := spectral_weights_pos U Sig hSig
  have hd : ∀ i, 0 ≤ d i := hD.eigenvalues_nonneg
  have hpos : ∃ i, 0 < d i := positive_eigenvalue_of_ne_zero D hD hDz
  by_cases hr : ρ = 0
  · subst ρ
    obtain ⟨γ, hγ0, hγ, herr⟩ := scalar_resolvent_error_small a d (fun i => (ha i).le) hd ε hε
    have hSigK : Sig ∈ sdpFeasibleSet 0 Sig σ := by
      refine ⟨hSig.posSemidef, hSig.posSemidef.submatrix Sum.inl,
        hSig.posSemidef.submatrix Sum.inr, ?_, (least_eigenvalue_facts Sig hSig σ hσ).2⟩
      have he := transport_converse Sig 1 hSig Matrix.PosSemidef.one
      simp only [Matrix.one_mul, Matrix.mul_one, sub_self, Matrix.zero_mul,
        Matrix.mul_zero, Matrix.trace_zero] at he
      change bures Sig Sig ≤ 0 ^ 2
      rw [he]
      norm_num
    refine ⟨γ, hγ0, (resolvent_spectral D hD γ hγ).1, ?_⟩
    have he := resolvent_zero_radius_error Sig D hD γ hγ
    have hs := hsupport Sig hSigK
    change (∑ i, a i * (d i) ^ 2 / (γ - d i)) < ε at herr
    change dualValue 0 Sig D γ - (D * Sig).trace =
      ∑ i, a i * (d i) ^ 2 / (γ - d i) at he
    linarith
  · have hrpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hr)
    obtain ⟨γ, hγ, hcost⟩ := scalar_cost_root a d ha hd hpos ρ hrpos
    obtain ⟨i, hi⟩ := hpos
    have hγ0 : 0 < γ := hi.trans (hγ i)
    let T := resolvent D γ
    have hT := (resolvent_psd_lower D hD γ hγ0 hγ).1
    have hTP : (T * Sig * T).PosSemidef := by
      have hT' : T.PosSemidef := hT
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, psd_transpose hT'] using
        hSig.posSemidef.mul_mul_conjTranspose_same T
    have hVK : T * Sig * T ∈ sdpFeasibleSet ρ Sig σ := by
      refine ⟨hTP, hTP.submatrix Sum.inl, hTP.submatrix Sum.inr, ?_, ?_⟩
      · change bures Sig (T * Sig * T) ≤ ρ ^ 2
        rw [transport_converse Sig T hSig hT, resolvent_cost Sig D hD γ hγ]
        exact hcost.le
      · exact resolvent_covariance_lower Sig D hD σ γ
          (least_eigenvalue_facts Sig hSig σ hσ).1.le
          (least_eigenvalue_facts Sig hSig σ hσ).2 hγ0 hγ
    have he := resolvent_dual_identity ρ Sig D hD γ hγ
    change dualValue ρ Sig D γ - (D * (T * Sig * T)).trace =
      γ * (ρ ^ 2 - scalarCost a d γ) at he
    rw [hcost, sub_self, mul_zero] at he
    have hs := hsupport (T * Sig * T) hVK
    exact ⟨γ, hγ0, (resolvent_spectral D hD γ hγ).1, by linarith⟩

theorem saddle_approx_dual (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ)
    (hmax : IsMaxOn sdpObjective (sdpFeasibleSet ρ Sig σ) S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ (γ • (1 : Cov n m) - riskMatrix (slope S)).PosDef ∧
      dualValue ρ Sig (riskMatrix (slope S)) γ < sdpObjective S + ε :=
  support_approx_dual Sig hSig ρ hρ σ hσ (riskMatrix (slope S)) (riskMatrix_psd _)
    (sdpObjective S) (schur_nonneg S (feasible_posDef Sig hSig ρ σ hσ S hS))
    (schur_support Sig hSig ρ hρ σ hσ S hS hmax) ε hε

end WassersteinKalmanProof

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace WassersteinKalmanProof

noncomputable section

variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

def gaussLin (A : Matrix κ ι ℝ) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (Matrix.toLpLin 2 2 A).toContinuousLinearMap

omit [DecidableEq κ] in
@[simp] theorem gaussLin_apply (A : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) (i : κ) :
    gaussLin A x i = ∑ j, A i j * x j := rfl

@[simp] theorem gaussLin_one (x : EuclideanSpace ℝ ι) : gaussLin (1 : Matrix ι ι ℝ) x = x := by
  ext i
  simp [gaussLin_apply, Matrix.one_apply]

omit [DecidableEq κ] in
@[simp] theorem gaussLin_sub (A B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    gaussLin (A - B) x = gaussLin A x - gaussLin B x := by
  ext i
  simp [gaussLin_apply, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq κ] in
@[simp] theorem gaussLin_smul (a : ℝ) (A : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    gaussLin (a • A) x = a • gaussLin A x := by
  ext i
  simp [gaussLin_apply, Finset.mul_sum, mul_assoc]

omit [DecidableEq τ] in
theorem gaussLin_mul (A : Matrix τ κ ℝ) (B : Matrix κ ι ℝ) :
    gaussLin (A * B) = (gaussLin A).comp (gaussLin B) := by
  ext x i
  simp only [gaussLin_apply, ContinuousLinearMap.comp_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [DecidableEq κ] in
theorem gaussLin_inner (A : Matrix κ ι ℝ) (x : EuclideanSpace ℝ κ)
    (y : EuclideanSpace ℝ ι) :
    inner ℝ x (gaussLin A y) = x ⬝ᵥ A *ᵥ y := by
  simp [PiLp.inner_apply, dotProduct, mulVec, mul_comm]

theorem gaussLin_adjoint (A : Matrix κ ι ℝ) :
    (gaussLin A).adjoint = gaussLin Aᵀ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, gaussLin_apply,
    transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def gaussQuad (B : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) : ℝ := z ⬝ᵥ B *ᵥ z

omit [DecidableEq ι] in
theorem gaussQuad_sum (B : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) :
    gaussQuad B z = ∑ i, ∑ j, B i j * z i * z j := by
  simp only [gaussQuad, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq ι] in
@[fun_prop] theorem gaussQuad_continuous (B : Matrix ι ι ℝ) : Continuous (gaussQuad B) := by
  have heq : gaussQuad B = fun z => ∑ i, ∑ j, B i j * z i * z j := funext (gaussQuad_sum B)
  rw [heq]
  fun_prop

theorem gaussLin_norm_sq (A : Matrix κ ι ℝ) (z : EuclideanSpace ℝ ι) :
    ‖gaussLin A z‖ ^ 2 = gaussQuad (Aᵀ * A) z := by
  rw [← real_inner_self_eq_norm_sq, gaussQuad, ← gaussLin_inner,
    gaussLin_mul, ContinuousLinearMap.comp_apply, ← gaussLin_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem gaussian_center_memLp (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    MemLp (fun z => z - μ) 2 (multivariateGaussian μ S) :=
  IsGaussian.memLp_two_id.sub (memLp_const μ)

theorem gaussian_coord_memLp (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (i : ι) :
    MemLp (fun z => z i - μ i) 2 (multivariateGaussian μ S) := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (gaussian_center_memLp μ S)
  change MemLp (fun z => (z - μ) i) 2 (multivariateGaussian μ S) at h
  simpa only [PiLp.sub_apply] using h

theorem gaussian_center_mean (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    ∫ z, z - μ ∂multivariateGaussian μ S = 0 := by
  rw [integral_sub (f := fun z : EuclideanSpace ℝ ι => z)
    (g := fun _ => μ) IsGaussian.integrable_id (integrable_const _),
    integral_id_multivariateGaussian, integral_const]
  simp

theorem gaussian_coord_moment (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) (i j : ι) :
    (∫ z, (z i - μ i) * (z j - μ j) ∂multivariateGaussian μ S) = S i j := by
  have h := covarianceBilin_apply (μ := multivariateGaussian μ S)
    IsGaussian.memLp_two_id (EuclideanSpace.basisFun ι ℝ i)
    (EuclideanSpace.basisFun ι ℝ j)
  simpa [integral_id_multivariateGaussian', covarianceBilin_multivariateGaussian hS,
    PiLp.inner_apply, dotProduct, mulVec] using h.symm

theorem gaussian_quad_integrable (μ : EuclideanSpace ℝ ι) (S B : Matrix ι ι ℝ) :
    Integrable (fun z => gaussQuad B (z - μ)) (multivariateGaussian μ S) := by
  simp_rw [gaussQuad_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := (gaussian_coord_memLp μ S i).integrable_mul (gaussian_coord_memLp μ S j)
  simpa only [Pi.mul_apply, PiLp.sub_apply, mul_assoc] using h.const_mul (B i j)

theorem gaussian_quad_mean (μ : EuclideanSpace ℝ ι) (S B : Matrix ι ι ℝ)
    (hS : S.PosSemidef) :
    (∫ z, gaussQuad B (z - μ) ∂multivariateGaussian μ S) = (B * S).trace := by
  have hi (i j : ι) : Integrable (fun z => B i j * (z i - μ i) * (z j - μ j))
      (multivariateGaussian μ S) := by
    simpa only [Pi.mul_apply, mul_assoc] using
      ((gaussian_coord_memLp μ S i).integrable_mul
        (gaussian_coord_memLp μ S j)).const_mul (B i j)
  simp_rw [gaussQuad_sum, PiLp.sub_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), mul_assoc, integral_const_mul,
    gaussian_coord_moment μ S hS]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : S j i = S i j := by simpa only [star_trivial] using hS.isHermitian.apply i j
  rw [hs]

theorem gaussian_linear_sq_integrable (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (A : Matrix κ ι ℝ) :
    Integrable (fun z => ‖gaussLin A (z - μ)‖ ^ 2) (multivariateGaussian μ S) := by
  simpa only [gaussLin_norm_sq] using gaussian_quad_integrable μ S (Aᵀ * A)

theorem gaussian_linear_sq_mean (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) (A : Matrix κ ι ℝ) :
    (∫ z, ‖gaussLin A (z - μ)‖ ^ 2 ∂multivariateGaussian μ S) = (A * S * Aᵀ).trace := by
  simp_rw [gaussLin_norm_sq]
  rw [gaussian_quad_mean μ S _ hS, Matrix.mul_assoc, Matrix.trace_mul_comm]

theorem gaussian_affine_map (μ : EuclideanSpace ℝ ι) (ν : EuclideanSpace ℝ κ)
    (S : Matrix ι ι ℝ) (T : Matrix κ κ ℝ) (A : Matrix κ ι ℝ)
    (hS : S.PosSemidef) (hT : T.PosSemidef) (hcov : A * S * Aᵀ = T) :
    (multivariateGaussian μ S).map (fun z => ν + gaussLin A (z - μ)) =
      multivariateGaussian ν T := by
  have heq : (fun z => ν + gaussLin A (z - μ)) =
      (fun z => (ν - gaussLin A μ) + z) ∘ gaussLin A := by
    funext z
    simp only [Function.comp_apply, map_sub]
    abel
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop)]
  apply IsGaussian.ext
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp only [id_eq]
    rw [integral_add (f := fun _ => ν - gaussLin A μ) (g := fun z => z) (integrable_const _)
      IsGaussian.integrable_id, integral_const,
      (gaussLin A).integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian]
    simp
  · rw [covarianceBilin_map_const_add]
    ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hT,
      ← gaussLin_inner, ← gaussLin_inner, ← hcov,
      gaussLin_mul, gaussLin_mul]
    simp only [ContinuousLinearMap.comp_apply, ← gaussLin_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

def signal {n m : ℕ} (z : State n m) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => z (Sum.inl i))

def observation {n m : ℕ} (z : State n m) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => z (Sum.inr i))

@[fun_prop] theorem signal_continuous {n m : ℕ} : Continuous (signal : State n m → _) := by
  unfold signal
  fun_prop

@[fun_prop] theorem observation_continuous {n m : ℕ} :
    Continuous (observation : State n m → _) := by
  unfold observation
  fun_prop

theorem estimator_eq {n m : ℕ} (μ : State n m) (S : Cov n m)
    (y : EuclideanSpace ℝ (Fin m)) :
    estimator μ S y = gaussLin (slope S) (y - observation μ) + signal μ := by
  unfold estimator WassersteinDRO.Shrinkage.affineEstimator
  congr 1
  ext i
  change (S.toBlocks₁₂ *ᵥ (S.toBlocks₂₂⁻¹ *ᵥ (y - observation μ))) i =
    ((S.toBlocks₁₂ * S.toBlocks₂₂⁻¹) *ᵥ (y - observation μ)) i
  rw [Matrix.mulVec_mulVec]

theorem estimator_measurable {n m : ℕ} (μ : State n m) (S : Cov n m) :
    Measurable (estimator μ S) := by
  have heq : estimator μ S = fun y => gaussLin (slope S) (y - observation μ) + signal μ :=
    funext (estimator_eq μ S)
  rw [heq]
  fun_prop

theorem residual_apply {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℝ) (z : State n m) :
    gaussLin (residual G) z = signal z - gaussLin G (observation z) := by
  ext i
  simp [gaussLin_apply, residual, signal, observation, Fintype.sum_sum_type, sub_eq_add_neg, Matrix.one_apply]

theorem residual_error {n m : ℕ} (μ : State n m) (S : Cov n m) (z : State n m) :
    signal z - estimator μ S (observation z) =
      gaussLin (residual (slope S)) (z - μ) := by
  rw [estimator_eq, residual_apply]
  have hs : signal (z - μ) = signal z - signal μ := by ext; rfl
  have ho : observation (z - μ) = observation z - observation μ := by ext; rfl
  rw [hs, ho]
  abel

theorem estimationLoss_eq {n m : ℕ} (μ : State n m) (S : Cov n m) (z : State n m) :
    WassersteinDRO.Shrinkage.estimationLoss (estimator μ S) z =
      ‖gaussLin (residual (slope S)) (z - μ)‖ ^ 2 := by
  change ‖signal z - estimator μ S (observation z)‖ ^ 2 = _
  rw [residual_error]

end

end WassersteinKalmanProof

open MeasureTheory ProbabilityTheory Matrix WassersteinDRO.Shrinkage
open scoped BigOperators

namespace WassersteinKalmanProof

noncomputable section

theorem gaussian_mem_ball {n m : ℕ} (μ : State n m) (Sig : Cov n m)
    (hSig : Sig.PosDef) (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ) :
    multivariateGaussian μ S ∈ WassKF.Reform.GaussianBall μ Sig ρ := by
  have hs := hS.1
  obtain ⟨_, hcov, hcost⟩ := transport_facts Sig S hSig hs
  let T := transportMap Sig S
  let F : State n m → State n m := fun z => μ + gaussLin T (z - μ)
  let π := (multivariateGaussian μ Sig).map (fun z => (F z, z))
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hpair : Measurable (fun z : State n m => (F z, z)) := by fun_prop
  have hmarg : π.map Prod.fst = multivariateGaussian μ S ∧
      π.map Prod.snd = multivariateGaussian μ Sig := by
    constructor
    · dsimp [π]
      rw [Measure.map_map measurable_fst hpair]
      exact gaussian_affine_map μ μ Sig S T hSig.posSemidef hs hcov
    · dsimp [π]
      rw [Measure.map_map measurable_snd hpair]
      exact Measure.map_id
  have hdiff (z : State n m) : F z - z = gaussLin (T - 1) (z - μ) := by
    simp only [F, gaussLin_sub, gaussLin_one]
    abel
  have hπcost : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) =
      ENNReal.ofReal (bures Sig S) := by
    dsimp [π]
    rw [lintegral_map (f := fun z : State n m × State n m =>
      ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ))) (by fun_prop) hpair]
    simp only [Real.rpow_two, hdiff]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (gaussian_linear_sq_integrable μ Sig (T - 1))
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
      gaussian_linear_sq_mean μ Sig hSig.posSemidef (T - 1)]
    exact congrArg ENNReal.ofReal hcost
  refine ⟨μ, S, hs, rfl, ?_⟩
  unfold wassersteinDistance
  have hi : (⨅ (ν : Measure (State n m × State n m))
      (_ : ν.map Prod.fst = multivariateGaussian μ S ∧
        ν.map Prod.snd = multivariateGaussian μ Sig),
      ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂ν) ≤
      ENNReal.ofReal (ρ ^ 2) := by
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π :=
        iInf_le_of_le π (iInf_le_of_le hmarg le_rfl)
      _ = ENNReal.ofReal (bures Sig S) := hπcost
      _ ≤ ENNReal.ofReal (ρ ^ 2) := ENNReal.ofReal_le_ofReal hS.2.2.2.1
  have hp := ENNReal.rpow_le_rpow hi (by norm_num : 0 ≤ (1 / (2 : ℝ)))
  rw [ENNReal.ofReal_pow hρ, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul] at hp
  norm_num at hp ⊢
  exact hp

end

end WassersteinKalmanProof

open MeasureTheory ProbabilityTheory Matrix WassersteinDRO.Shrinkage
open scoped BigOperators

namespace WassersteinKalmanProof

noncomputable section

variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

omit [DecidableEq κ] in
theorem gaussian_linear_covariance (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) (A : Matrix κ ι ℝ) (B : Matrix τ ι ℝ)
    (a : EuclideanSpace ℝ κ) (b : EuclideanSpace ℝ τ) :
    covariance (fun z => inner ℝ a (gaussLin A z))
      (fun z => inner ℝ b (gaussLin B z)) (multivariateGaussian μ S) =
      inner ℝ a (gaussLin (A * S * Bᵀ) b) := by
  have ha : (fun z => inner ℝ a (gaussLin A z)) =
      fun z => inner ℝ ((gaussLin A).adjoint a) z := by
    funext z
    exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  have hb : (fun z => inner ℝ b (gaussLin B z)) =
      fun z => inner ℝ ((gaussLin B).adjoint b) z := by
    funext z
    exact (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  rw [ha, hb, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_multivariateGaussian hS, ← gaussLin_inner,
    ContinuousLinearMap.adjoint_inner_left, gaussLin_adjoint]
  rw [gaussLin_mul, gaussLin_mul]
  rfl

def observationMatrix (n m : ℕ) : Matrix (Fin m) (Joint n m) ℝ :=
  Matrix.fromCols 0 1

theorem observationMatrix_apply {n m : ℕ} (z : State n m) :
    gaussLin (observationMatrix n m) z = observation z := by
  ext i
  simp [gaussLin_apply, observationMatrix, observation, Fintype.sum_sum_type, Matrix.one_apply]

theorem residual_independent {n m : ℕ} (μ : State n m) (S : Cov n m)
    (hS : S.PosDef) :
    IndepFun (fun z => gaussLin (residual (slope S)) (z - μ)) observation
      (multivariateGaussian μ S) := by
  let C := residual (slope S)
  let O := observationMatrix n m
  have hzero : C * S * Oᵀ = 0 := by
    ext i j
    simpa [Matrix.mul_apply, O, observationMatrix, Fintype.sum_sum_type, Matrix.one_apply] using
      schur_residual_observation S hS i j
  have hjoint : HasGaussianLaw (fun z => (gaussLin C z, gaussLin O z))
      (multivariateGaussian μ S) := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.prod_apply] using
      (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian μ S)).map
        ((gaussLin C).prod (gaussLin O))
  have hi : IndepFun (gaussLin C) (gaussLin O) (multivariateGaussian μ S) := by
    apply hjoint.indepFun_of_covariance_inner
    intro a b
    rw [gaussian_linear_covariance μ S hS.posSemidef C O a b, hzero]
    have hz : gaussLin (0 : Matrix (Fin n) (Fin m) ℝ) b = 0 := by
      ext j
      simp [gaussLin_apply]
    rw [hz, inner_zero_right]
  have h := hi.comp (measurable_id.sub_const (gaussLin C μ)) measurable_id
  simpa only [C, O, Function.comp_def, id_eq, map_sub, observationMatrix_apply] using h

theorem gaussian_shifted_residual_lintegral {n m : ℕ} (μ : State n m) (S : Cov n m)
    (hS : S.PosDef) (a : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ r, ENNReal.ofReal (‖r + a‖ ^ 2)
      ∂(multivariateGaussian μ S).map
        (fun z => gaussLin (residual (slope S)) (z - μ))) =
      ENNReal.ofReal (sdpObjective S + ‖a‖ ^ 2) := by
  let R : State n m → EuclideanSpace ℝ (Fin n) :=
    fun z => gaussLin (residual (slope S)) (z - μ)
  have hR : MemLp R 2 (multivariateGaussian μ S) :=
    (gaussLin (residual (slope S))).comp_memLp' (gaussian_center_memLp μ S)
  have hRi := hR.integrable (by norm_num)
  have hmean : ∫ z, R z ∂multivariateGaussian μ S = 0 := by
    dsimp [R]
    rw [(gaussLin (residual (slope S))).integral_comp_comm
      ((gaussian_center_memLp μ S).integrable (by norm_num)), gaussian_center_mean, map_zero]
  have hnorm : Integrable (fun z => ‖R z‖ ^ 2) (multivariateGaussian μ S) :=
    hR.integrable_norm_pow'
  have hshift : Integrable (fun z => ‖R z + a‖ ^ 2) (multivariateGaussian μ S) :=
    (hR.add (memLp_const a)).integrable_norm_pow'
  have hpoint (z : State n m) :
      ‖R z + a‖ ^ 2 = (‖R z‖ ^ 2 + 2 * inner ℝ a (R z)) + ‖a‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm a (R z)]
  rw [lintegral_map (by fun_prop) (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal hshift
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  congr 1
  simp_rw [hpoint]
  have hcross : Integrable (fun z => 2 * inner ℝ a (R z))
      (multivariateGaussian μ S) := (hRi.const_inner a).const_mul 2
  have hsum : Integrable (fun z => ‖R z‖ ^ 2 + 2 * inner ℝ a (R z))
      (multivariateGaussian μ S) := hnorm.add hcross
  rw [integral_add hsum (integrable_const _),
    integral_add hnorm ((hRi.const_inner a).const_mul 2), integral_const_mul,
    integral_inner hRi a, hmean, inner_zero_right, mul_zero, add_zero, integral_const]
  rw [gaussian_linear_sq_mean μ S hS.posSemidef, schur_residual_trace S hS]
  simp

theorem gaussian_risk_affine {n m : ℕ} (μ : State n m) (S : Cov n m)
    (hS : S.PosDef) :
    WassKF.Reform.expectedLoss (estimator μ S) (multivariateGaussian μ S) =
      ENNReal.ofReal (sdpObjective S) := by
  unfold WassKF.Reform.expectedLoss
  simp_rw [estimationLoss_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (gaussian_linear_sq_integrable μ S (residual (slope S)))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    gaussian_linear_sq_mean μ S hS.posSemidef, schur_residual_trace S hS]

theorem gaussian_risk_lower {n m : ℕ} (μ : State n m) (S : Cov n m)
    (hS : S.PosDef) (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hψ : Measurable ψ) :
    ENNReal.ofReal (sdpObjective S) ≤
      WassKF.Reform.expectedLoss ψ (multivariateGaussian μ S) := by
  let P := multivariateGaussian μ S
  let R : State n m → EuclideanSpace ℝ (Fin n) :=
    fun z => gaussLin (residual (slope S)) (z - μ)
  let F : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ENNReal :=
    fun p => ENNReal.ofReal (‖p.1 + (estimator μ S p.2 - ψ p.2)‖ ^ 2)
  have hR : Measurable R := by dsimp [R]; fun_prop
  have hO : Measurable (observation : State n m → _) := by fun_prop
  have hF : Measurable F := by
    dsimp [F]
    exact (measurable_fst.add
      (((estimator_measurable μ S).comp measurable_snd).sub
        (hψ.comp measurable_snd))).norm.pow_const 2 |>.ennreal_ofReal
  have hprod : P.map (fun z => (R z, observation z)) =
      (P.map R).prod (P.map observation) :=
    (residual_independent μ S hS).map_prod_eq_prod_map_map hR.aemeasurable hO.aemeasurable
  let : IsProbabilityMeasure (P.map observation) := P.isProbabilityMeasure_map hO.aemeasurable
  have hinner (y : EuclideanSpace ℝ (Fin m)) :
      ENNReal.ofReal (sdpObjective S) ≤ ∫⁻ r, F (r, y) ∂P.map R := by
    change ENNReal.ofReal (sdpObjective S) ≤
      ∫⁻ r, ENNReal.ofReal (‖r + (estimator μ S y - ψ y)‖ ^ 2) ∂P.map R
    rw [gaussian_shifted_residual_lintegral μ S hS]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))
  calc
    ENNReal.ofReal (sdpObjective S) =
        ∫⁻ _ : EuclideanSpace ℝ (Fin m), ENNReal.ofReal (sdpObjective S)
          ∂P.map observation := by simp
    _ ≤ ∫⁻ y, ∫⁻ r, F (r, y) ∂P.map R ∂P.map observation := lintegral_mono hinner
    _ = ∫⁻ p, F p ∂(P.map R).prod (P.map observation) :=
      (lintegral_prod_symm _ hF.aemeasurable).symm
    _ = ∫⁻ z, F (R z, observation z) ∂P := by
      rw [← hprod, lintegral_map hF (hR.prodMk hO)]
    _ = WassKF.Reform.expectedLoss ψ P := by
      apply lintegral_congr
      intro z
      dsimp [F, WassKF.Reform.expectedLoss, WassersteinDRO.Shrinkage.estimationLoss]
      congr 3
      change R z + (estimator μ S (observation z) - ψ (observation z)) =
        signal z - ψ (observation z)
      rw [show R z = signal z - estimator μ S (observation z) from
        (residual_error μ S z).symm]
      abel

end

end WassersteinKalmanProof

open MeasureTheory ProbabilityTheory Matrix WassersteinDRO.Shrinkage
open scoped BigOperators

namespace WassersteinKalmanProof

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem quadratic_completion (C : Matrix κ ι ℝ) (γ : ℝ)
    (hH : (γ • (1 : Matrix ι ι ℝ) - Cᵀ * C).PosDef)
    (x y : EuclideanSpace ℝ ι) :
    ‖gaussLin C x‖ ^ 2 ≤ γ * ‖x - y‖ ^ 2 + gaussQuad (dualMatrix (Cᵀ * C) γ) y := by
  let H : Matrix ι ι ℝ := γ • 1 - Cᵀ * C
  let v := γ • gaussLin H⁻¹ y
  have hi : H * H⁻¹ = 1 :=
    Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  have hv : gaussLin H v = γ • y := by
    dsimp [v]
    rw [map_smul, ← ContinuousLinearMap.comp_apply, ← gaussLin_mul, hi, gaussLin_one]
  have hs : Hᵀ = H := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.isHermitian.eq
  have hsym : inner ℝ v (gaussLin H x) = inner ℝ (gaussLin H v) x := by
    rw [← ContinuousLinearMap.adjoint_inner_left, gaussLin_adjoint, hs]
  have hp : 0 ≤ inner ℝ (x - v) (gaussLin H (x - v)) := by
    rw [gaussLin_inner]
    simpa using hH.posSemidef.dotProduct_mulVec_nonneg (x - v)
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym, hv] at hp
  have hx : inner ℝ x (gaussLin H x) = γ * ‖x‖ ^ 2 - ‖gaussLin C x‖ ^ 2 := by
    dsimp [H]
    rw [gaussLin_sub, gaussLin_smul, gaussLin_one, inner_sub_right,
      inner_smul_right, real_inner_self_eq_norm_sq, gaussLin_norm_sq]
    rw [gaussQuad, gaussLin_inner]
  have hb : gaussQuad (dualMatrix (Cᵀ * C) γ) y =
      γ ^ 2 * inner ℝ y (gaussLin H⁻¹ y) - γ * ‖y‖ ^ 2 := by
    rw [gaussQuad, ← gaussLin_inner]
    simp only [dualMatrix, gaussLin_sub, gaussLin_smul, gaussLin_one,
      inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    rfl
  rw [hx] at hp
  dsimp [v] at hp
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real] at hp
  rw [real_inner_comm x y, real_inner_comm y (gaussLin H⁻¹ y)] at hp
  rw [norm_sub_sq_real, hb]
  nlinarith

theorem dual_quadratic_nonneg (C : Matrix κ ι ℝ) (γ : ℝ)
    (hH : (γ • (1 : Matrix ι ι ℝ) - Cᵀ * C).PosDef)
    (y : EuclideanSpace ℝ ι) : 0 ≤ gaussQuad (dualMatrix (Cᵀ * C) γ) y := by
  have h := quadratic_completion C γ hH y y
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at h
  exact (sq_nonneg _).trans h

theorem coupling_loss_bound {n m : ℕ} (μ : State n m) (Sig S : Cov n m)
    (hSig : Sig.PosDef) (γ : ℝ) (hγ : 0 < γ)
    (hD : (γ • (1 : Cov n m) - riskMatrix (slope S)).PosDef)
    (Q : Measure (State n m)) (π : Measure (State n m × State n m))
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = multivariateGaussian μ Sig) :
    WassKF.Reform.expectedLoss (estimator μ S) Q ≤
      ENNReal.ofReal γ * (∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π) +
        ENNReal.ofReal ((dualMatrix (riskMatrix (slope S)) γ * Sig).trace) := by
  let C := residual (slope S)
  let B := dualMatrix (riskMatrix (slope S)) γ
  have hB (z : State n m) : 0 ≤ gaussQuad B z := dual_quadratic_nonneg C γ hD z
  have hpoint (p : State n m × State n m) :
      ENNReal.ofReal (‖gaussLin C (p.1 - μ)‖ ^ 2) ≤
        ENNReal.ofReal γ * ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) +
          ENNReal.ofReal (gaussQuad B (p.2 - μ)) := by
    rw [← ENNReal.ofReal_mul hγ.le, ← ENNReal.ofReal_add
      (mul_nonneg hγ.le (sq_nonneg _)) (hB _)]
    apply ENNReal.ofReal_le_ofReal
    have h := quadratic_completion C γ hD (p.1 - μ) (p.2 - μ)
    convert h using 1
    congr 2
    abel
  have hsecond : (∫⁻ p : State n m × State n m,
      ENNReal.ofReal (gaussQuad B (p.2 - μ)) ∂π) =
      ENNReal.ofReal ((B * Sig).trace) := by
    rw [← lintegral_map (f := fun z : State n m => ENNReal.ofReal (gaussQuad B (z - μ)))
      (by fun_prop) measurable_snd, hπ.2,
      ← ofReal_integral_eq_lintegral_ofReal (gaussian_quad_integrable μ Sig B)
        (Filter.Eventually.of_forall (fun z => hB (z - μ))),
      gaussian_quad_mean μ Sig B hSig.posSemidef]
  unfold WassKF.Reform.expectedLoss
  rw [← hπ.1, lintegral_map (by simp_rw [estimationLoss_eq]; fun_prop) measurable_fst]
  simp_rw [estimationLoss_eq]
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal γ * ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) +
        ENNReal.ofReal (gaussQuad B (p.2 - μ)) ∂π := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop), hsecond]

theorem transport_upper {n m : ℕ} (μ : State n m) (Sig S : Cov n m)
    (hSig : Sig.PosDef) (ρ : ℝ) (hρ : 0 ≤ ρ) (γ : ℝ) (hγ : 0 < γ)
    (hD : (γ • (1 : Cov n m) - riskMatrix (slope S)).PosDef)
    (Q : Measure (State n m)) (hQ : Q ∈ WassKF.Reform.GaussianBall μ Sig ρ) :
    WassKF.Reform.expectedLoss (estimator μ S) Q ≤
      ENNReal.ofReal (dualValue ρ Sig (riskMatrix (slope S)) γ) := by
  let B := dualMatrix (riskMatrix (slope S)) γ
  let cost : ENNReal := ⨅ (π : Measure (State n m × State n m))
    (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = multivariateGaussian μ Sig),
      ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π
  have hcost : cost ≤ ENNReal.ofReal (ρ ^ 2) := by
    obtain ⟨_, _, _, _, hball⟩ := hQ
    have hb : cost ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ρ := by
      simpa only [wassersteinDistance, Real.rpow_two] using hball
    have hh := ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 2)
    rw [← ENNReal.rpow_mul] at hh
    norm_num only [show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.rpow_two] at hh
    simpa only [ENNReal.ofReal_pow hρ] using hh
  have hbound : WassKF.Reform.expectedLoss (estimator μ S) Q ≤
      ENNReal.ofReal γ * cost + ENNReal.ofReal ((B * Sig).trace) := by
    dsimp [cost]
    rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hγ) ENNReal.ofReal_ne_top,
      ENNReal.iInf_add]
    refine le_iInf fun π => ?_
    rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hγ) ENNReal.ofReal_ne_top,
      ENNReal.iInf_add]
    exact le_iInf fun hπ => coupling_loss_bound μ Sig S hSig γ hγ hD Q π hπ
  have htrace : 0 ≤ (B * Sig).trace := by
    rw [← gaussian_quad_mean μ Sig B hSig.posSemidef]
    exact integral_nonneg fun z => dual_quadratic_nonneg (residual (slope S)) γ hD (z - μ)
  calc
    _ ≤ ENNReal.ofReal γ * cost + ENNReal.ofReal ((B * Sig).trace) := hbound
    _ ≤ ENNReal.ofReal γ * ENNReal.ofReal (ρ ^ 2) +
        ENNReal.ofReal ((B * Sig).trace) := by gcongr
    _ = ENNReal.ofReal (dualValue ρ Sig (riskMatrix (slope S)) γ) := by
      rw [← ENNReal.ofReal_mul hγ.le, ← ENNReal.ofReal_add
        (mul_nonneg hγ.le (sq_nonneg ρ)) htrace]
      rfl

end

end WassersteinKalmanProof

open Matrix MeasureTheory ProbabilityTheory WassersteinDRO.Shrinkage WassKF.Reform
open scoped BigOperators

namespace WassersteinKalmanProof

variable {n m : ℕ}

theorem affine_worst_bound (μ : State n m) (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ)
    (hmax : IsMaxOn sdpObjective (sdpFeasibleSet ρ Sig σ) S) :
    (⨆ (Q : Measure (State n m)) (_ : Q ∈ GaussianBall μ Sig ρ),
      expectedLoss (estimator μ S) Q) ≤ ENNReal.ofReal (sdpObjective S) := by
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεR : (0 : ℝ) < ε := hε
  obtain ⟨γ, hγ, hD, hb⟩ := saddle_approx_dual Sig hSig ρ hρ σ hσ S hS hmax ε hεR
  have hu := transport_upper μ Sig S hSig ρ hρ γ hγ hD Q hQ
  have hf := schur_nonneg S (feasible_posDef Sig hSig ρ σ hσ S hS)
  calc
    expectedLoss (estimator μ S) Q ≤ ENNReal.ofReal (dualValue ρ Sig (riskMatrix (slope S)) γ) := hu
    _ ≤ ENNReal.ofReal (sdpObjective S + ε) := ENNReal.ofReal_le_ofReal hb.le
    _ = ENNReal.ofReal (sdpObjective S) + ε := by
      rw [ENNReal.ofReal_add hf ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

theorem minimax_weak_duality (μ : State n m) (Sig : Cov n m) (ρ : ℝ) :
    maximinValue μ Sig ρ ≤ minimaxValue μ Sig ρ := by
  unfold maximinValue minimaxValue
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  apply le_iInf
  intro ψ
  apply le_iInf
  intro hψ
  calc
    _ ≤ expectedLoss ψ Q := iInf_le_of_le ψ (iInf_le_of_le hψ le_rfl)
    _ ≤ _ := by
      apply le_iSup_of_le Q
      exact le_iSup (fun _ : Q ∈ GaussianBall μ Sig ρ => expectedLoss ψ Q) hQ

theorem saddle_values (μ : State n m) (Sig : Cov n m) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ)
    (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ)
    (hmax : IsMaxOn sdpObjective (sdpFeasibleSet ρ Sig σ) S) :
    minimaxValue μ Sig ρ = ENNReal.ofReal (sdpObjective S) ∧
    maximinValue μ Sig ρ = ENNReal.ofReal (sdpObjective S) ∧
    (⨆ (Q : Measure (State n m)) (_ : Q ∈ GaussianBall μ Sig ρ),
      expectedLoss (estimator μ S) Q) = ENNReal.ofReal (sdpObjective S) ∧
    (⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
      expectedLoss ψ (multivariateGaussian μ S)) = ENNReal.ofReal (sdpObjective S) := by
  have hSP := feasible_posDef Sig hSig ρ σ hσ S hS
  have hQ := gaussian_mem_ball μ Sig hSig ρ hρ σ S hS
  have hψ := estimator_measurable μ S
  have he := gaussian_risk_affine μ S hSP
  have hlo : ENNReal.ofReal (sdpObjective S) ≤
      ⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
        expectedLoss ψ (multivariateGaussian μ S) := by
    exact le_iInf fun ψ => le_iInf fun hm => gaussian_risk_lower μ S hSP ψ hm
  have hi : (⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
      expectedLoss ψ (multivariateGaussian μ S)) = ENNReal.ofReal (sdpObjective S) := by
    exact le_antisymm (iInf_le_of_le (estimator μ S) (iInf_le_of_le hψ he.le)) hlo
  have hlmax : ENNReal.ofReal (sdpObjective S) ≤ maximinValue μ Sig ρ := by
    unfold maximinValue
    exact le_iSup_of_le (multivariateGaussian μ S) (le_iSup_of_le hQ hi.ge)
  have hup := affine_worst_bound μ Sig hSig ρ hρ σ hσ S hS hmax
  have humin : minimaxValue μ Sig ρ ≤ ENNReal.ofReal (sdpObjective S) := by
    unfold minimaxValue
    exact iInf_le_of_le (estimator μ S) (iInf_le_of_le hψ hup)
  have hmm := minimax_weak_duality μ Sig ρ
  refine ⟨le_antisymm humin (hlmax.trans hmm), le_antisymm (hmm.trans humin) hlmax, ?_, hi⟩
  exact le_antisymm hup
    (le_iSup_of_le (multivariateGaussian μ S) (le_iSup_of_le hQ he.ge))

theorem sdpValue_at_max (Sig : Cov n m) (ρ σ : ℝ)
    (S : Cov n m) (hS : S ∈ sdpFeasibleSet ρ Sig σ)
    (hmax : IsMaxOn sdpObjective (sdpFeasibleSet ρ Sig σ) S) :
    sdpValue ρ Sig σ = (sdpObjective S : EReal) := by
  unfold sdpValue
  apply le_antisymm
  · exact iSup_le fun V => iSup_le fun hV => EReal.coe_le_coe_iff.mpr (hmax hV)
  · exact le_iSup_of_le S (le_iSup_of_le hS le_rfl)

end WassersteinKalmanProof

open WassersteinKalmanProof

namespace WassKF.Reform

/-- Theorem 2.5 (Tractable reformulation), Shafieezadeh-Abadeh et al., arXiv:1809.08830v3, p. 3.
Let `ℙ = 𝒩_d(μ, Sig)` with `Sig ≻ 0`, `ρ ≥ 0`, and `σ = λ_min(Sig)`. Then
1. the optimal value of the minimax problem (2) over the ambiguity set (3) equals the optimal value
   of program (5), `sup Tr[S_xx − S_xy S_yy⁻¹ S_yx]` over `sdpFeasibleSet ρ Sig σ`;
2. for every optimal solution `S⋆` of (5), the affine estimator
   `ψ⋆(y) = S⋆_xy (S⋆_yy)⁻¹ (y − μ_y) + μ_x` is measurable and attains the outer infimum of (2);
3. for the same `S⋆`, `Q⋆ = 𝒩_d(μ, S⋆)` lies in the ambiguity set and attains the outer supremum
   of nature's problem `sup_{Q ∈ 𝒫} inf_{ψ ∈ ℒ} E^Q[‖x − ψ(y)‖²]` (it is the least favorable prior).
Here `μ_x = (μ_i)_{i ∈ inl}` and `μ_y = (μ_j)_{j ∈ inr}`. -/
theorem theorem_2_5 {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ) (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    ((minimaxValue μ Sig ρ : ENNReal) : EReal) = WassersteinDRO.Shrinkage.sdpValue ρ Sig σ ∧
    ∀ Sstar ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sig σ,
      IsMaxOn WassersteinDRO.Shrinkage.sdpObjective
          (WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sig σ) Sstar →
        (Measurable (WassersteinDRO.Shrinkage.affineEstimator Sstar.toBlocks₁₂ Sstar.toBlocks₂₂
            ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
            ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))) ∧
          (⨆ (Q : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) (_ : Q ∈ GaussianBall μ Sig ρ),
              expectedLoss (WassersteinDRO.Shrinkage.affineEstimator Sstar.toBlocks₁₂
                Sstar.toBlocks₂₂
                ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
                ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))) Q) =
            minimaxValue μ Sig ρ) ∧
        (multivariateGaussian μ Sstar ∈ GaussianBall μ Sig ρ ∧
          (⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
              expectedLoss ψ (multivariateGaussian μ Sstar)) =
            maximinValue μ Sig ρ) := by
  obtain ⟨S, hS, hmax⟩ := feasible_maximizer Sig hSig ρ hρ σ hσ
  have hv := saddle_values μ Sig hSig ρ hρ σ hσ S hS hmax
  constructor
  · rw [hv.1, sdpValue_at_max Sig ρ σ S hS hmax, EReal.coe_ennreal_ofReal]
    rw [max_eq_left (schur_nonneg S (feasible_posDef Sig hSig ρ σ hσ S hS))]
  · intro Sstar hSstar hMstar
    have hvstar := saddle_values μ Sig hSig ρ hρ σ hσ Sstar hSstar hMstar
    refine ⟨⟨estimator_measurable μ Sstar, ?_⟩,
      gaussian_mem_ball μ Sig hSig ρ hρ σ Sstar hSstar, ?_⟩
    · exact hvstar.2.2.1.trans hvstar.1.symm
    · exact hvstar.2.2.2.trans hvstar.2.1.symm

end WassKF.Reform

open WassKF.Reform

theorem solution {n m : ℕ} (μ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (Sig : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (hSig : Sig.PosDef)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (σ : ℝ) (hσ : IsLeast (Set.range hSig.isHermitian.eigenvalues) σ) :
    ((minimaxValue μ Sig ρ : ENNReal) : EReal) = WassersteinDRO.Shrinkage.sdpValue ρ Sig σ ∧
    ∀ Sstar ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sig σ,
      IsMaxOn WassersteinDRO.Shrinkage.sdpObjective
          (WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sig σ) Sstar →
        (Measurable (WassersteinDRO.Shrinkage.affineEstimator Sstar.toBlocks₁₂ Sstar.toBlocks₂₂
            ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
            ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))) ∧
          (⨆ (Q : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) (_ : Q ∈ GaussianBall μ Sig ρ),
              expectedLoss (WassersteinDRO.Shrinkage.affineEstimator Sstar.toBlocks₁₂
                Sstar.toBlocks₂₂
                ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => μ (Sum.inl i)))
                ((EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => μ (Sum.inr j)))) Q) =
            minimaxValue μ Sig ρ) ∧
        (multivariateGaussian μ Sstar ∈ GaussianBall μ Sig ρ ∧
          (⨅ (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (_ : Measurable ψ),
              expectedLoss ψ (multivariateGaussian μ Sstar)) =
            maximinValue μ Sig ρ) := by
  exact WassKF.Reform.theorem_2_5 μ Sig hSig ρ hρ σ hσ
