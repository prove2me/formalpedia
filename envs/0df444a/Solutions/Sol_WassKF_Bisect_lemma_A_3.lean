-- Prove2me | solution 1 for WassKF.Bisect.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T05:09:07.651412+00:00
-- url     : https://prove2.me/submissions/b74cf55d-a04c-4095-94ea-bfb5aad2c691

/-
Kalman bisection interval, 23 October 2026.
Original result: Soroosh Shafieezadeh-Abadeh, Viet Anh Nguyen, Daniel Kuhn and
Peyman Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering,
arXiv:1809.08830v3 (1 October 2018), Lemma A.3, equation (A.7), p.13.
Inspected PDF SHA256 d0bec3d6b0335573310beadb723366d71e09fc89732424eb632bfc92d1c0f91e.
mikedeng1 supplied the platform model and target, including explicit unit
normalization of the eigenvector. Statement confirmation is not proof review.
The lower endpoint follows from a unit-vector Rayleigh/trace inequality and
the resolvent eigenvector identity. The upper endpoint uses commuting positive
matrix products to bound the positive resolvent error and its square, followed
by a positive weighted-trace bound. Scalar square-root algebra closes both.
The proof was informed by vebis's accepted dual-upper-bound formalization
(target 8d2a683b-e529-435f-b61e-e86776afd15e, submission
d95c213f-df06-4207-8509-2a4b1c9fa0a6, SHA256
ec921d0d5200ed0a9ff1faa11d5a62b77ae0476e5fb6a3768acc6a355b9bd4c3),
which demonstrates the Mathlib positive-square-root and commuting-positive-
product techniques. No platform theorem body or open assumption is imported.
Lean/Mathlib contributors supply matrix order, functional calculus, inverse,
finite Cauchy-Schwarz and scalar-order foundations.
Alexander Richard Towell directed the research and verification standards;
OpenAI Codex constructed and checked this formalization. No mathematical
novelty or independent human proof review is claimed.
-/
import Mathlib
import Definitions.Def_WassKF_Bisect_hFun

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder
set_option autoImplicit false

namespace KalmanResearch

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rayleigh_le_trace (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (v : ι → ℝ) (hv : v ⬝ᵥ v = 1) : v ⬝ᵥ (A *ᵥ v) ≤ A.trace := by
  let R : Matrix ι ι ℝ := CFC.sqrt A
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have hRT : Rᵀ = R := by simpa using hR.isHermitian.eq
  have hRRA : Rᵀ * R = A := by rw [hRT,hRR]
  have hsq : ∑ j, v j ^ 2 = 1 := by simpa [dotProduct,pow_two] using hv
  calc
    v ⬝ᵥ (A *ᵥ v) = ∑ i, (∑ j, R i j * v j) ^ 2 := by
      rw [← hRRA, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      simp [dotProduct, mulVec, pow_two]
    _ ≤ ∑ i, (∑ j, R i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (R * Rᵀ).trace := by
      rw [hsq]
      simp [Matrix.trace, Matrix.mul_apply, pow_two]
    _ = A.trace := by rw [Matrix.trace_mul_comm,hRRA]

lemma gap_pos (D : Matrix ι ι ℝ) (lam γ : ℝ) (v : ι → ℝ)
    (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1)
    (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef) : 0 < γ-lam := by
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv1
  have h := hγ.dotProduct_mulVec_pos hv0
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, dotProduct_sub,
    dotProduct_smul, hv1] using h

lemma eigenvalue_nonneg (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (lam : ℝ) (v : ι → ℝ) (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1) :
    0 ≤ lam := by
  simpa [hv, dotProduct_smul, hv1] using hD.dotProduct_mulVec_nonneg v

lemma resolvent_eigenvector (D : Matrix ι ι ℝ) (lam γ : ℝ) (v : ι → ℝ)
    (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1)
    (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef) :
    (γ • (1 : Matrix ι ι ℝ) - D)⁻¹ *ᵥ v = (γ-lam)⁻¹ • v := by
  let A := γ • (1 : Matrix ι ι ℝ) - D
  have hgap := gap_pos D lam γ v hv hv1 hγ
  have hAv : A *ᵥ v = (γ-lam) • v := by
    simp [A, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, sub_smul]
  have hInvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A
    ((Matrix.isUnit_iff_isUnit_det A).mp hγ.isUnit)
  have he : (γ-lam) • (A⁻¹ *ᵥ v) = v := by
    rw [← Matrix.mulVec_smul, ← hAv, Matrix.mulVec_mulVec, hInvA, Matrix.one_mulVec]
  change A⁻¹ *ᵥ v = _
  calc
    A⁻¹ *ᵥ v = (γ-lam)⁻¹ • ((γ-lam) • (A⁻¹ *ᵥ v)) := by
      simp [smul_smul,hgap.ne']
    _ = _ := by rw [he]

lemma transport_eigenvector (D : Matrix ι ι ℝ) (lam γ : ℝ) (v : ι → ℝ)
    (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1)
    (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef) :
    (1 - γ • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹) *ᵥ v =
      (-(lam / (γ-lam))) • v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    resolvent_eigenvector D lam γ v hv hv1 hγ, smul_smul]
  have hgap := gap_pos D lam γ v hv hv1 hγ
  have he : 1-γ*(γ-lam)⁻¹ = -(lam/(γ-lam)) := by field_simp; ring
  calc
    v - (γ * (γ-lam)⁻¹) • v = (1-γ*(γ-lam)⁻¹) • v := by rw [sub_smul,one_smul]
    _ = _ := by rw [he]

end KalmanResearch

#print axioms KalmanResearch.rayleigh_le_trace
#print axioms KalmanResearch.transport_eigenvector

namespace KalmanResearch
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_eigenvalue_bound (Sigma B : Matrix ι ι ℝ) (hSigma : Sigma.PosSemidef)
    (hBT : Bᵀ = B) (v : ι → ℝ) (hv1 : v ⬝ᵥ v = 1)
    (β : ℝ) (hv : B *ᵥ v = β • v) :
    β^2 * (v ⬝ᵥ (Sigma *ᵥ v)) ≤ (Sigma * B^2).trace := by
  have hc : (Bᵀ * Sigma * B).PosSemidef := by
    simpa using hSigma.conjTranspose_mul_mul_same B
  have h := rayleigh_le_trace (Bᵀ * Sigma * B) hc v hv1
  have he : v ⬝ᵥ ((Bᵀ * Sigma * B) *ᵥ v) = β^2 * (v ⬝ᵥ (Sigma *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      vecMul_transpose, hv, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [he] at h
  convert h using 1
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm Bᵀ, hBT, Matrix.mul_assoc, pow_two]

lemma lower_endpoint (Sigma D : Matrix ι ι ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hSigma : Sigma.PosSemidef) (hD : D.PosSemidef)
    (lam : ℝ) (v : ι → ℝ) (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1)
    (γ : ℝ) (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef)
    (hroot : WassKF.Bisect.hFun Sigma D ρ γ = 0) :
    lam * (1 + Real.sqrt (v ⬝ᵥ (Sigma *ᵥ v)) / ρ) ≤ γ := by
  let A := γ • (1 : Matrix ι ι ℝ) - D
  let B := (1 : Matrix ι ι ℝ) - γ • A⁻¹
  have hAT : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hγ.isHermitian.eq
  have hBT : Bᵀ = B := by simp [B, Matrix.transpose_nonsing_inv, hAT]
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hgap := gap_pos D lam γ v hv hv1 hγ
  have hl := eigenvalue_nonneg D hD lam v hv hv1
  have ha : 0 ≤ v ⬝ᵥ (Sigma *ᵥ v) := by simpa using hSigma.dotProduct_mulVec_nonneg v
  have heig : B *ᵥ v = (-(lam/(γ-lam))) • v :=
    transport_eigenvector D lam γ v hv hv1 hγ
  have hlow := weighted_eigenvalue_bound Sigma B hSigma hBT v hv1 _ heig
  have htrace : (Sigma * B^2).trace = ρ^2 := by
    unfold WassKF.Bisect.hFun at hroot
    rw [hSigT] at hroot
    change ρ^2 - (Sigma * B^2).trace = 0 at hroot
    linarith
  rw [htrace, neg_sq] at hlow
  have hm := mul_le_mul_of_nonneg_right hlow (sq_nonneg (γ-lam))
  have hcancel : (lam/(γ-lam))^2 * (v ⬝ᵥ (Sigma *ᵥ v)) * (γ-lam)^2 =
      lam^2 * (v ⬝ᵥ (Sigma *ᵥ v)) := by field_simp
  rw [hcancel] at hm
  have hsq : (lam * Real.sqrt (v ⬝ᵥ (Sigma *ᵥ v)))^2 ≤ (ρ*(γ-lam))^2 := by
    rw [mul_pow, Real.sq_sqrt ha, mul_pow]
    exact hm
  have hle := (sq_le_sq₀ (mul_nonneg hl (Real.sqrt_nonneg _))
    (mul_nonneg hρ.le hgap.le)).mp hsq
  have hdiv : lam * Real.sqrt (v ⬝ᵥ (Sigma *ᵥ v)) / ρ ≤ γ-lam := by
    apply (div_le_iff₀ hρ).mpr
    nlinarith [hle]
  calc
    _ = lam + lam * Real.sqrt (v ⬝ᵥ (Sigma *ᵥ v)) / ρ := by ring
    _ ≤ γ := by linarith

end KalmanResearch
#print axioms KalmanResearch.lower_endpoint

namespace KalmanResearch
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inv_scalar (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : Matrix ι ι ℝ))⁻¹ = c⁻¹ • (1 : Matrix ι ι ℝ) := by
  apply Matrix.inv_eq_right_inv
  simp [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hc]

lemma positive_resolvent_bounds (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (lam γ : ℝ) (hlam : 0 ≤ lam) (hgap : 0 < γ-lam)
    (hDupper : (lam • (1 : Matrix ι ι ℝ) - D).PosSemidef)
    (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef) :
    let B := γ • (γ • (1 : Matrix ι ι ℝ) - D)⁻¹ - 1
    B.PosSemidef ∧ ((lam/(γ-lam)) • (1 : Matrix ι ι ℝ) - B).PosSemidef := by
  let A := γ • (1 : Matrix ι ι ℝ) - D
  let B := γ • A⁻¹ - 1
  have hγpos : 0 < γ := by linarith
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hia : A⁻¹*A=1 := Matrix.nonsing_inv_mul A hu
  have hai : A*A⁻¹=1 := Matrix.mul_nonsing_inv A hu
  have hi : A⁻¹.PosSemidef := hγ.posSemidef.inv
  have hcomm (c : ℝ) : Commute A⁻¹ (A-c • (1 : Matrix ι ι ℝ)) := by
    change A⁻¹*(A-c • 1)=(A-c • 1)*A⁻¹
    simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,Matrix.one_mul,hia,hai]
  have hcomm' (c : ℝ) : Commute A⁻¹ (c • (1 : Matrix ι ι ℝ)-A) := by
    change A⁻¹*(c • 1-A)=(c • 1-A)*A⁻¹
    simp only [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,Matrix.one_mul,hia,hai]
  have hup : (γ • (1 : Matrix ι ι ℝ)-A).PosSemidef := by simpa [A] using hD
  have hlo : (A-(γ-lam) • (1 : Matrix ι ι ℝ)).PosSemidef := by
    have he : A-(γ-lam) • (1 : Matrix ι ι ℝ) = lam • 1-D := by
      dsimp [A]
      rw [sub_smul]
      abel
    rw [he]
    exact hDupper
  have hB : B.PosSemidef := by
    have ht := Matrix.nonneg_iff_posSemidef.mp
      (Commute.mul_nonneg hi.nonneg hup.nonneg (hcomm' γ))
    simpa only [mul_sub,Matrix.mul_smul,Matrix.mul_one,hia] using ht
  have ht := Matrix.nonneg_iff_posSemidef.mp
    (Commute.mul_nonneg hi.nonneg hlo.nonneg (hcomm (γ-lam)))
  have ht' : ((1 : Matrix ι ι ℝ)-(γ-lam) • A⁻¹).PosSemidef := by
    simpa only [mul_sub,hia,Matrix.mul_smul,Matrix.mul_one] using ht
  have hs := ht'.smul (div_nonneg hγpos.le hgap.le)
  rw [smul_sub,smul_smul,div_mul_cancel₀ γ hgap.ne'] at hs
  have he : γ/(γ-lam) = lam/(γ-lam)+1 := by field_simp; ring
  have heB : (lam/(γ-lam)) • (1 : Matrix ι ι ℝ)-B =
      (γ/(γ-lam)) • 1-γ • A⁻¹ := by
    dsimp [B]
    rw [he,add_smul,one_smul]
    abel
  exact ⟨hB,heB ▸ hs⟩

lemma square_bound (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (β : ℝ) (hβ : 0 ≤ β)
    (hcap : (β • (1 : Matrix ι ι ℝ) - B).PosSemidef) :
    (β^2 • (1 : Matrix ι ι ℝ) - B^2).PosSemidef := by
  have hp : (β • (1 : Matrix ι ι ℝ) + B).PosSemidef :=
    (Matrix.PosSemidef.one.smul hβ).add hB
  have hc : Commute (β • (1 : Matrix ι ι ℝ) - B) (β • (1 : Matrix ι ι ℝ) + B) := by
    change (β • (1 : Matrix ι ι ℝ) - B) * (β • 1 + B) =
      (β • 1 + B) * (β • 1 - B)
    simp only [sub_mul,mul_sub,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.mul_one,Matrix.one_mul]
    abel
  have ht := Matrix.nonneg_iff_posSemidef.mp
    (Commute.mul_nonneg hcap.nonneg hp.nonneg hc)
  have he : (β • (1 : Matrix ι ι ℝ)-B)*(β • 1+B) = β^2 • 1-B^2 := by
    simp only [sub_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.mul_one,Matrix.one_mul,smul_smul,pow_two]
    abel
  rw [he] at ht
  exact ht

lemma trace_mul_nonneg (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A*B).trace := by
  let R : Matrix ι ι ℝ := CFC.sqrt A
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hRR : R*R=A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hRT : Rᵀ=R := by simpa using hR.isHermitian.eq
  have hpos : (R*B*R).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial,hRT] using hB.conjTranspose_mul_mul_same R
  have he : (R*B*R).trace = (A*B).trace := by
    rw [Matrix.trace_mul_comm (R*B) R, ← Matrix.mul_assoc, hRR]
  rw [← he]
  exact hpos.trace_nonneg

lemma weighted_square_upper (Sigma B : Matrix ι ι ℝ) (hSigma : Sigma.PosSemidef)
    (hB : B.PosSemidef) (β : ℝ) (hβ : 0 ≤ β)
    (hcap : (β • (1 : Matrix ι ι ℝ) - B).PosSemidef) :
    (Sigma*B^2).trace ≤ β^2 * Sigma.trace := by
  have h := trace_mul_nonneg Sigma (β^2 • (1 : Matrix ι ι ℝ) - B^2)
    hSigma (square_bound B hB β hβ hcap)
  simpa only [Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,
    Matrix.trace_smul,smul_eq_mul,sub_nonneg] using h

end KalmanResearch
#print axioms KalmanResearch.weighted_square_upper
#print axioms KalmanResearch.positive_resolvent_bounds

namespace KalmanResearch
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma upper_endpoint (Sigma D : Matrix ι ι ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hSigma : Sigma.PosSemidef) (hD : D.PosSemidef)
    (lam : ℝ) (v : ι → ℝ) (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1)
    (hDupper : (lam • (1 : Matrix ι ι ℝ) - D).PosSemidef)
    (γ : ℝ) (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef)
    (hroot : WassKF.Bisect.hFun Sigma D ρ γ = 0) :
    γ ≤ lam * (1 + Real.sqrt Sigma.trace / ρ) := by
  let A := γ • (1 : Matrix ι ι ℝ) - D
  let B := γ • A⁻¹ - 1
  have hgap := gap_pos D lam γ v hv hv1 hγ
  have hl := eigenvalue_nonneg D hD lam v hv hv1
  have ht := hSigma.trace_nonneg
  have hβ : 0 ≤ lam/(γ-lam) := div_nonneg hl hgap.le
  obtain ⟨hB,hcap⟩ := positive_resolvent_bounds D hD lam γ hl hgap hDupper hγ
  have hbound := weighted_square_upper Sigma B hSigma hB (lam/(γ-lam)) hβ hcap
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hneg : (1 : Matrix ι ι ℝ) - γ • A⁻¹ = -B := by dsimp [B]; abel
  have htrace : (Sigma*B^2).trace = ρ^2 := by
    unfold WassKF.Bisect.hFun at hroot
    change ρ^2 - (Sigmaᵀ * (1-γ • A⁻¹)^2).trace = 0 at hroot
    rw [hSigT,hneg,neg_sq] at hroot
    linarith
  rw [htrace] at hbound
  have hm := mul_le_mul_of_nonneg_right hbound (sq_nonneg (γ-lam))
  have hcancel : (lam/(γ-lam))^2 * Sigma.trace * (γ-lam)^2 = lam^2 * Sigma.trace := by
    field_simp
  rw [hcancel] at hm
  have hsq : (ρ*(γ-lam))^2 ≤ (lam*Real.sqrt Sigma.trace)^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt ht]
    exact hm
  have hle := (sq_le_sq₀ (mul_nonneg hρ.le hgap.le)
    (mul_nonneg hl (Real.sqrt_nonneg _))).mp hsq
  have hdiv : γ-lam ≤ lam*Real.sqrt Sigma.trace/ρ := by
    apply (le_div_iff₀ hρ).mpr
    nlinarith [hle]
  calc
    γ ≤ lam+lam*Real.sqrt Sigma.trace/ρ := by linarith
    _ = _ := by ring

end KalmanResearch

theorem solution {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef) (hD0 : D ≠ 0)
    (lam1 : ℝ) (v₁ : Fin n ⊕ Fin m → ℝ)
    (hlam : (lam1 • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosSemidef)
    (hv : D *ᵥ v₁ = lam1 • v₁) (hv1 : v₁ ⬝ᵥ v₁ = 1)
    (γstar : ℝ)
    (hγstar : (γstar • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hroot : WassKF.Bisect.hFun Sigma D ρ γstar = 0) :
    lam1 * (1 + Real.sqrt (v₁ ⬝ᵥ (Sigma *ᵥ v₁)) / ρ) ≤ γstar ∧
      γstar ≤ lam1 * (1 + Real.sqrt Sigma.trace / ρ) := by
  exact ⟨KalmanResearch.lower_endpoint Sigma D ρ hρ hSigma.posSemidef hD
    lam1 v₁ hv hv1 γstar hγstar hroot,
    KalmanResearch.upper_endpoint Sigma D ρ hρ hSigma.posSemidef hD
    lam1 v₁ hv hv1 hlam γstar hγstar hroot⟩

#print axioms solution
