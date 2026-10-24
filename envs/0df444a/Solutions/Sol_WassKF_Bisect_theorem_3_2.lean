-- Prove2me | solution 1 for WassKF.Bisect.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T08:56:55.901907+00:00
-- url     : https://prove2.me/submissions/b1ac76f0-7e56-4613-a742-153d6aab3fb4

/-
Kalman Algorithm1: full soundness and termination,23October2026.
Exact corrected platform Theorem3.2, including the no-dyadic-root hypothesis.
New continuity and shrinking-bracket arguments complete termination; the earlier
checked soundness and credited accepted proof bodies are retained below.
Original mathematics: Shafieezadeh-Abadeh, Nguyen, Kuhn and Mohajerin Esfahani,
Wasserstein Distributionally Robust Kalman Filtering,arXiv1809.08830v3,
Theorem3.2/Algorithm1 pp.5-6 and AppendixA.3 p.13.
Alexander Richard Towell(queelius), substantial OpenAI Codex assistance.
Reuses actual accepted vebis proofs: feasibility submission
f9f7d9c1-e37a-4376-84e7-7d98bb4cdfea,
SHA2560860378c0527ccfefac5b35056069d9f2c1d047cf37f7b0e5fabfe31af4071e9;
dual-bound submission d95c213f-df06-4207-8509-2a4b1c9fa0a6,
SHA256ec921d0d5200ed0a9ff1faa11d5a62b77ae0476e5fb6a3768acc6a355b9bd4c3.
Also reuses queelius's accepted interval proof and locally verified algorithm
invariants, with their original source and vebis methodological credit retained
in the companion record. mikedeng1 supplied the platform model. Lean/Mathlib
provide matrix order, square roots, inverse, topology and finite-dimensional
algebra foundations. No mathematical novelty or human proof review claimed.
-/
import Mathlib
import Definitions.Def_WassKF_Bisect_Delta
import Definitions.Def_WassKF_Bisect_Lgamma
import Definitions.Def_WassKF_Bisect_algorithm1
import Definitions.Def_WassKF_Bisect_gradF
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet


namespace AcceptedInterval
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

end AcceptedInterval

namespace LocalInvariants
open Matrix
set_option autoImplicit false
namespace KalmanAlgorithm
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma bracket_bounds (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (h : WassKF.Bisect.gammaMin Sigma ρ lam v ≤ WassKF.Bisect.gammaMax Sigma ρ lam)
    (k : ℕ) :
    WassKF.Bisect.gammaMin Sigma ρ lam v ≤ (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 ∧
    (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 ≤ (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 ∧
    (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 ≤ WassKF.Bisect.gammaMax Sigma ρ lam := by
  induction k with
  | zero => simpa [WassKF.Bisect.bisectState] using h
  | succ k ih =>
    simp only [WassKF.Bisect.bisectState]
    split <;> dsimp <;> constructor
    all_goals first | linarith [ih.1, ih.2.1, ih.2.2] | constructor <;> linarith [ih.1, ih.2.1, ih.2.2]

lemma trial_bounds (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (h : WassKF.Bisect.gammaMin Sigma ρ lam v ≤ WassKF.Bisect.gammaMax Sigma ρ lam)
    (k : ℕ) :
    WassKF.Bisect.gammaMin Sigma ρ lam v ≤ WassKF.Bisect.bisectGamma Sigma D ρ lam v k ∧
    WassKF.Bisect.bisectGamma Sigma D ρ lam v k ≤ WassKF.Bisect.gammaMax Sigma ρ lam := by
  have hb := bracket_bounds Sigma D ρ lam v h k
  unfold WassKF.Bisect.bisectGamma
  constructor <;> linarith [hb.1, hb.2.1, hb.2.2]

lemma bracket_width (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ) (k : ℕ) :
    (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 -
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 =
      (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k := by
  induction k with
  | zero => simp [WassKF.Bisect.bisectState]
  | succ k ih =>
    simp only [WassKF.Bisect.bisectState]
    split <;> dsimp
    all_goals rw [pow_succ, div_mul_eq_div_div, ← ih]; ring

lemma bracket_grid (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ) (k : ℕ) :
    ∃ j : ℕ, j < 2^k ∧
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 =
        WassKF.Bisect.gammaMin Sigma ρ lam v + j *
          (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k ∧
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 =
        WassKF.Bisect.gammaMin Sigma ρ lam v + (j+1 : ℕ) *
          (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k := by
  induction k with
  | zero => refine ⟨0, by norm_num, ?_, ?_⟩ <;> simp [WassKF.Bisect.bisectState]
  | succ k ih =>
    obtain ⟨j, hj, hlo, hup⟩ := ih
    simp only [WassKF.Bisect.bisectState]
    split
    · refine ⟨2*j+1, ?_, ?_, ?_⟩
      · rw [pow_succ]; omega
      · dsimp; rw [hlo, hup]; push_cast; rw [pow_succ]; ring
      · dsimp; rw [hup]; push_cast; rw [pow_succ]; ring
    · refine ⟨2*j, ?_, ?_, ?_⟩
      · rw [pow_succ]; omega
      · dsimp; rw [hlo]; push_cast; rw [pow_succ]; ring
      · dsimp; rw [hlo, hup]; push_cast; rw [pow_succ]; ring

lemma trial_grid (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ) (k : ℕ) :
    ∃ j : ℕ, 0 < j ∧ j ≤ 2^(k+1) ∧
      WassKF.Bisect.bisectGamma Sigma D ρ lam v k =
        WassKF.Bisect.gammaMin Sigma ρ lam v + j *
          (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^(k+1) := by
  obtain ⟨j, hj, hlo, hup⟩ := bracket_grid Sigma D ρ lam v k
  refine ⟨2*j+1, by omega, ?_, ?_⟩
  · rw [pow_succ]; omega
  · unfold WassKF.Bisect.bisectGamma
    rw [hlo, hup]; push_cast; rw [pow_succ]; ring

lemma trial_not_root (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (hgrid : ∀ (k j : ℕ), 0 < j → j ≤ 2^k →
      WassKF.Bisect.hFun Sigma D ρ
        (WassKF.Bisect.gammaMin Sigma ρ lam v + j *
          (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k) ≠ 0)
    (k : ℕ) : WassKF.Bisect.hFun Sigma D ρ (WassKF.Bisect.bisectGamma Sigma D ρ lam v k) ≠ 0 := by
  obtain ⟨j, hj0, hj, he⟩ := trial_grid Sigma D ρ lam v k
  rw [he]
  exact hgrid (k+1) j hj0 hj

lemma trial_posDef (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (horder : WassKF.Bisect.gammaMin Sigma ρ lam v ≤ WassKF.Bisect.gammaMax Sigma ρ lam)
    (hstrict : lam < WassKF.Bisect.gammaMin Sigma ρ lam v)
    (hD : (lam • (1 : Matrix ι ι ℝ) - D).PosSemidef) (k : ℕ) :
    (WassKF.Bisect.bisectGamma Sigma D ρ lam v k • (1 : Matrix ι ι ℝ) - D).PosDef := by
  have hb := (trial_bounds Sigma D ρ lam v horder k).1
  have hp : 0 < WassKF.Bisect.bisectGamma Sigma D ρ lam v k - lam := by linarith
  have hh := ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul hp).add_posSemidef hD
  convert hh using 1
  simp only [sub_smul]
  abel

end KalmanAlgorithm
#print axioms KalmanAlgorithm.bracket_bounds
#print axioms KalmanAlgorithm.bracket_width
#print axioms KalmanAlgorithm.bracket_grid
#print axioms KalmanAlgorithm.trial_not_root

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ) (k : ℕ) :
    (WassKF.Bisect.gammaMin Sigma ρ lam v ≤ WassKF.Bisect.gammaMax Sigma ρ lam →
      WassKF.Bisect.gammaMin Sigma ρ lam v ≤ (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 ∧
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 ≤ (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 ∧
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 ≤ WassKF.Bisect.gammaMax Sigma ρ lam) ∧
    ((WassKF.Bisect.bisectState Sigma D ρ lam v k).2 - (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 =
      (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k) ∧
    (∃ j : ℕ, j < 2^k ∧
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).1 = WassKF.Bisect.gammaMin Sigma ρ lam v + j *
        (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k ∧
      (WassKF.Bisect.bisectState Sigma D ρ lam v k).2 = WassKF.Bisect.gammaMin Sigma ρ lam v + (j+1 : ℕ) *
        (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^k) ∧
    ((∀ (l j : ℕ), 0 < j → j ≤ 2^l → WassKF.Bisect.hFun Sigma D ρ
      (WassKF.Bisect.gammaMin Sigma ρ lam v + j *
        (WassKF.Bisect.gammaMax Sigma ρ lam - WassKF.Bisect.gammaMin Sigma ρ lam v) / 2^l) ≠ 0) →
      WassKF.Bisect.hFun Sigma D ρ (WassKF.Bisect.bisectGamma Sigma D ρ lam v k) ≠ 0) ∧
    (WassKF.Bisect.gammaMin Sigma ρ lam v ≤ WassKF.Bisect.gammaMax Sigma ρ lam →
      lam < WassKF.Bisect.gammaMin Sigma ρ lam v →
      (lam • (1 : Matrix ι ι ℝ) - D).PosSemidef →
      (WassKF.Bisect.bisectGamma Sigma D ρ lam v k • (1 : Matrix ι ι ℝ) - D).PosDef) := by
  exact ⟨fun h => KalmanAlgorithm.bracket_bounds Sigma D ρ lam v h k,
    KalmanAlgorithm.bracket_width Sigma D ρ lam v k,
    KalmanAlgorithm.bracket_grid Sigma D ρ lam v k,
    fun h => KalmanAlgorithm.trial_not_root Sigma D ρ lam v h k,
    fun h hs hD => KalmanAlgorithm.trial_posDef Sigma D ρ lam v h hs hD k⟩
#print axioms solution

end LocalInvariants

namespace AcceptedFeasibility
set_option autoImplicit false

open Matrix

section psd
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma psd_exists_sqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : ∃ S : Matrix n n ℝ, S.PosSemidef ∧ S * S = A := by
  have h0 : (0 : Matrix n n ℝ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  exact ⟨CFC.sqrt A, Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A),
    CFC.sqrt_mul_sqrt_self A h0⟩

lemma psd_unique {n : Type*} [Fintype n] [DecidableEq n] (B B' : Matrix n n ℝ)
    (hB : B.PosSemidef) (hB' : B'.PosSemidef) (h : B' * B' = B * B) : B' = B := by
  have hB0 : (0 : Matrix n n ℝ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  have hB0' : (0 : Matrix n n ℝ) ≤ B' := Matrix.nonneg_iff_posSemidef.mpr hB'
  exact (CFC.mul_self_eq_mul_self_iff B' B hB0' hB0).mp h

lemma psd_commute_mul {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℝ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : X * Y = Y * X) : (X * Y).PosSemidef := by
  have hX0 : (0 : Matrix n n ℝ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  have hY0 : (0 : Matrix n n ℝ) ≤ Y := Matrix.nonneg_iff_posSemidef.mpr hY
  exact Matrix.nonneg_iff_posSemidef.mp (Commute.mul_nonneg hX0 hY0 h)

end psd

lemma psdSqrt_unique {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hB : B.PosSemidef) (hBB : B * B = A) :
    WassersteinDRO.Shrinkage.psdSqrt A = B := by
  classical
  unfold WassersteinDRO.Shrinkage.psdSqrt
  have hex : ∃ B' : Matrix n n ℝ, B'.PosSemidef ∧ B' * B' = A := ⟨B, hB, hBB⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact psd_unique B _ hB h1 (by rw [h2, hBB])

open WassKF.Bisect

theorem solution {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ σ γ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (hh : 0 < hFun Sigma D ρ γ) :
    Lgamma Sigma D γ ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ := by
  classical
  unfold hFun at hh
  unfold Lgamma
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hDT : Dᵀ = D := by simpa using hD.isHermitian.eq
  obtain ⟨A, hAdef⟩ : ∃ A, A = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D := ⟨_, rfl⟩
  rw [← hAdef] at hγ hh ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = A⁻¹ := ⟨_, rfl⟩
  rw [← ha] at hh ⊢
  have hAT : Aᵀ = A := by rw [hAdef]; simp [hDT]
  have hAu : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hAa : A * a = 1 := by rw [ha]; exact Matrix.mul_nonsing_inv _ hAu
  have haA : a * A = 1 := by rw [ha]; exact Matrix.nonsing_inv_mul _ hAu
  have haT : aᵀ = a := by rw [ha, Matrix.transpose_nonsing_inv, hAT]
  have hapd : a.PosDef := by rw [ha]; exact hγ.inv
  have hDA : D = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A := by
    rw [hAdef, sub_sub_cancel]
  -- σ ≥ 0
  have hσpos : 0 ≤ σ := by
    obtain ⟨v, hv, hvσ⟩ := hσ_eig
    have h1 := hSigma.dotProduct_mulVec_pos hv
    rw [hvσ] at h1
    simp only [star_trivial, dotProduct_smul, smul_eq_mul] at h1
    have h2 : 0 < v ⬝ᵥ v := by
      by_contra hneg
      have : v ⬝ᵥ v = 0 := le_antisymm (not_lt.mp hneg) (dotProduct_self_star_nonneg v)
      exact hv ((dotProduct_self_eq_zero).mp this)
    by_contra hneg
    have : σ * (v ⬝ᵥ v) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) h2
    linarith
  -- empty case / γ ≥ 0
  rcases isEmpty_or_nonempty (Fin n ⊕ Fin m) with hE | hNE
  · -- everything is trivial
    have hsub : ∀ M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ, M = 0 := fun M =>
      Subsingleton.elim _ _
    have hsubB : ∀ M : Matrix (Fin n) (Fin n) ℝ, M = 0 := fun M => by
      have : IsEmpty (Fin n) := ⟨fun i => hE.false (Sum.inl i)⟩
      exact Subsingleton.elim _ _
    have hsubC : ∀ M : Matrix (Fin m) (Fin m) ℝ, M = 0 := fun M => by
      have : IsEmpty (Fin m) := ⟨fun i => hE.false (Sum.inr i)⟩
      exact Subsingleton.elim _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hsub (γ ^ 2 • (a * Sigma * a))]; exact Matrix.PosSemidef.zero
    · have := hsubB (Matrix.toBlocks₁₁ (γ ^ 2 • (a * Sigma * a)))
      rw [this]; exact Matrix.PosSemidef.zero
    · have := hsubC (Matrix.toBlocks₂₂ (γ ^ 2 • (a * Sigma * a)))
      rw [this]; exact Matrix.PosSemidef.zero
    · simp [Matrix.trace, Finset.univ_eq_empty]; positivity
    · rw [hsub (γ ^ 2 • (a * Sigma * a) - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ))]
      exact Matrix.PosSemidef.zero
  have hγ0 : 0 ≤ γ := by
    obtain ⟨i⟩ := hNE
    have h1 := hγ.diag_pos (i := i)
    have h2 := hD.diag_nonneg (i := i)
    rw [hAdef] at h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    linarith
  -- the matrix L
  have hLpsd : (γ ^ 2 • (a * Sigma * a)).PosSemidef := by
    have := hSigma.posSemidef.conjTranspose_mul_mul_same a
    have h2 : aᴴ = a := by simpa using haT
    rw [h2] at this
    exact this.smul (sq_nonneg γ)
  -- square root of Sigma
  obtain ⟨Sq, hSq, hSqSq⟩ := psd_exists_sqrt Sigma hSigma.posSemidef
  have hSqT : Sqᵀ = Sq := by simpa using hSq.isHermitian.eq
  have hpsdSq : WassersteinDRO.Shrinkage.psdSqrt Sigma = Sq := psdSqrt_unique _ _ hSq hSqSq
  -- Y
  have hYpsd : (γ • (Sq * a * Sq)).PosSemidef := by
    have := hapd.posSemidef.conjTranspose_mul_mul_same Sq
    have h2 : Sqᴴ = Sq := by simpa using hSqT
    rw [h2] at this
    exact this.smul hγ0
  have hYY : (γ • (Sq * a * Sq)) * (γ • (Sq * a * Sq)) =
      WassersteinDRO.Shrinkage.psdSqrt Sigma * (γ ^ 2 • (a * Sigma * a)) *
        WassersteinDRO.Shrinkage.psdSqrt Sigma := by
    rw [hpsdSq]
    conv_rhs => rw [← hSqSq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
    congr 1
    simp only [Matrix.mul_assoc]
  have hsqrtW : WassersteinDRO.Shrinkage.psdSqrt
      (WassersteinDRO.Shrinkage.psdSqrt Sigma * (γ ^ 2 • (a * Sigma * a)) *
        WassersteinDRO.Shrinkage.psdSqrt Sigma) = γ • (Sq * a * Sq) :=
    psdSqrt_unique _ _ hYpsd hYY
  refine ⟨hLpsd, hLpsd.submatrix Sum.inl, hLpsd.submatrix Sum.inr, ?_, ?_⟩
  · rw [hsqrtW]
    have hY1 : (Sq * a * Sq).trace = (a * Sigma).trace := by
      calc (Sq * a * Sq).trace = (Sq * (a * Sq)).trace := by rw [Matrix.mul_assoc]
        _ = ((a * Sq) * Sq).trace := Matrix.trace_mul_comm _ _
        _ = (a * Sigma).trace := by rw [Matrix.mul_assoc, hSqSq]
    have hL1 : (γ ^ 2 • (a * Sigma * a)).trace = γ ^ 2 * (Sigma * (a * a)).trace := by
      rw [Matrix.trace_smul, smul_eq_mul]
      congr 1
      calc (a * Sigma * a).trace = (a * (Sigma * a)).trace := by rw [Matrix.mul_assoc]
        _ = ((Sigma * a) * a).trace := Matrix.trace_mul_comm _ _
        _ = (Sigma * (a * a)).trace := by rw [Matrix.mul_assoc]
    have hsq : ((1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - γ • a) ^ 2 =
        1 - (2 * γ) • a + (γ ^ 2) • (a * a) := by
      simp only [sq, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      module
    rw [hSigT, hsq] at hh
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hh
    have hS2 : (Sigma * a).trace = (a * Sigma).trace := Matrix.trace_mul_comm _ _
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hY1, hL1]
    rw [hS2] at hh
    nlinarith [hh]
  · -- L - σ I ⪰ 0
    have hE : (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)).PosSemidef := by
      apply psd_commute_mul _ _ hD
      · have h1 : ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) =
            γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) + A := by
          rw [hAdef]; module
        rw [h1]
        exact ((Matrix.PosSemidef.one).smul hγ0).add hγ.posSemidef
      · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.one_mul]
    have hE2 : D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D) =
        γ ^ 2 • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A * A := by
      rw [hAdef]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, smul_smul]
      module
    have haEa : a * (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)) * a =
        γ ^ 2 • (a * a) - 1 := by
      rw [hE2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      have : a * (A * A) * a = 1 := by
        calc a * (A * A) * a = (a * A) * (A * a) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [haA, hAa, Matrix.one_mul]
      rw [this]
    have h2 : aᴴ = a := by simpa using haT
    have hP1 : (a * (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)) * a).PosSemidef := by
      have := hσ.conjTranspose_mul_mul_same a
      rwa [h2] at this
    have hP2 : (a * (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)) * a).PosSemidef := by
      have := hE.conjTranspose_mul_mul_same a
      rwa [h2] at this
    have hsplit : γ ^ 2 • (a * Sigma * a) - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) =
        γ ^ 2 • (a * (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)) * a) +
          σ • (a * (D * ((2 * γ) • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)) * a) := by
      rw [haEa]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
      module
    rw [hsplit]
    exact (hP1.smul (sq_nonneg γ)).add (hP2.smul hσpos)

end AcceptedFeasibility

namespace AcceptedDual
set_option autoImplicit false

open Matrix

section psd
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma psd_exists_sqrt {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.PosSemidef) : ∃ S : Matrix n n ℝ, S.PosSemidef ∧ S * S = A := by
  have h0 : (0 : Matrix n n ℝ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  exact ⟨CFC.sqrt A, Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A),
    CFC.sqrt_mul_sqrt_self A h0⟩

lemma psd_unique {n : Type*} [Fintype n] [DecidableEq n] (B B' : Matrix n n ℝ)
    (hB : B.PosSemidef) (hB' : B'.PosSemidef) (h : B' * B' = B * B) : B' = B := by
  have hB0 : (0 : Matrix n n ℝ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  have hB0' : (0 : Matrix n n ℝ) ≤ B' := Matrix.nonneg_iff_posSemidef.mpr hB'
  exact (CFC.mul_self_eq_mul_self_iff B' B hB0' hB0).mp h

lemma psd_commute_mul {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℝ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : X * Y = Y * X) : (X * Y).PosSemidef := by
  have hX0 : (0 : Matrix n n ℝ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  have hY0 : (0 : Matrix n n ℝ) ≤ Y := Matrix.nonneg_iff_posSemidef.mpr hY
  exact Matrix.nonneg_iff_posSemidef.mp (Commute.mul_nonneg hX0 hY0 h)

end psd

lemma psdSqrt_unique {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hB : B.PosSemidef) (hBB : B * B = A) :
    WassersteinDRO.Shrinkage.psdSqrt A = B := by
  classical
  unfold WassersteinDRO.Shrinkage.psdSqrt
  have hex : ∃ B' : Matrix n n ℝ, B'.PosSemidef ∧ B' * B' = A := ⟨B, hB, hBB⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact psd_unique B _ hB h1 (by rw [h2, hBB])


lemma psdSqrt_spec {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ)
    (hW : W.PosSemidef) :
    (WassersteinDRO.Shrinkage.psdSqrt W).PosSemidef ∧
      WassersteinDRO.Shrinkage.psdSqrt W * WassersteinDRO.Shrinkage.psdSqrt W = W := by
  classical
  obtain ⟨B, hB, hBB⟩ := psd_exists_sqrt W hW
  have : WassersteinDRO.Shrinkage.psdSqrt W = B := psdSqrt_unique W B hB hBB
  rw [this]; exact ⟨hB, hBB⟩

theorem solution {n m : ℕ} (Sigma D : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : (γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D).PosDef)
    (L' : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (hL' : L' ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ) :
    (L'ᵀ * D).trace ≤
      γ * (ρ ^ 2 - Sigma.trace) +
        γ ^ 2 * (((γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D)⁻¹)ᵀ * Sigma).trace := by
  classical
  obtain ⟨hX, -, -, htr, -⟩ := hL'
  have hSigT : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hDT : Dᵀ = D := by simpa using hD.isHermitian.eq
  have hXT : L'ᵀ = L' := by simpa using hX.isHermitian.eq
  rcases isEmpty_or_nonempty (Fin n ⊕ Fin m) with hE | hNE
  · have hz : ∀ M : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ, M.trace = 0 := fun M => by
      simp [Matrix.trace, Finset.univ_eq_empty]
    simp only [hz, mul_zero, sub_zero, add_zero]
    exact mul_nonneg hγ0 (sq_nonneg ρ)
  obtain ⟨A, hAdef⟩ : ∃ A, A = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - D := ⟨_, rfl⟩
  rw [← hAdef] at hγ ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = A⁻¹ := ⟨_, rfl⟩
  rw [← ha]
  have hγpos : 0 < γ := by
    obtain ⟨i⟩ := hNE
    have h1 := hγ.diag_pos (i := i)
    have h2 := hD.diag_nonneg (i := i)
    rw [hAdef] at h1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
    linarith
  have hAT : Aᵀ = A := by rw [hAdef]; simp [hDT]
  have hAu : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hAa : A * a = 1 := by rw [ha]; exact Matrix.mul_nonsing_inv _ hAu
  have haA : a * A = 1 := by rw [ha]; exact Matrix.nonsing_inv_mul _ hAu
  have haT : aᵀ = a := by rw [ha, Matrix.transpose_nonsing_inv, hAT]
  have hDA : D = γ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - A := by
    rw [hAdef, sub_sub_cancel]
  -- square root of Sigma
  obtain ⟨R, hR, hRR⟩ := psd_exists_sqrt Sigma hSigma.posSemidef
  have hRT : Rᵀ = R := by simpa using hR.isHermitian.eq
  have hpsdR : WassersteinDRO.Shrinkage.psdSqrt Sigma = R := psdSqrt_unique _ _ hR hRR
  have hRu : IsUnit R.det := by
    have h1 : IsUnit (R * R).det := by
      rw [hRR]; exact (isUnit_iff_isUnit_det _).mp hSigma.isUnit
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  obtain ⟨Ri, hRi⟩ : ∃ Ri, Ri = R⁻¹ := ⟨_, rfl⟩
  have hRRi : R * Ri = 1 := by rw [hRi]; exact Matrix.mul_nonsing_inv _ hRu
  have hRiR : Ri * R = 1 := by rw [hRi]; exact Matrix.nonsing_inv_mul _ hRu
  have hRiT : Riᵀ = Ri := by rw [hRi, Matrix.transpose_nonsing_inv, hRT]
  -- Y
  have hWpsd : (R * L' * R).PosSemidef := by
    have := hX.conjTranspose_mul_mul_same R
    have h2 : Rᴴ = R := by simpa using hRT
    rw [h2] at this
    exact this
  obtain ⟨hYpsd, hYY⟩ := psdSqrt_spec _ hWpsd
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = WassersteinDRO.Shrinkage.psdSqrt (R * L' * R) := ⟨_, rfl⟩
  rw [← hYdef] at hYpsd hYY
  rw [hpsdR, ← hYdef] at htr
  have hYT : Yᵀ = Y := by simpa using hYpsd.isHermitian.eq
  -- P and Q
  obtain ⟨P, hPdef⟩ : ∃ P, P = γ • (R * a * R) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = γ⁻¹ • (Ri * A * Ri) := ⟨_, rfl⟩
  have hγne : γ ≠ 0 := hγpos.ne'
  have hPQ : P * Q = 1 := by
    rw [hPdef, hQdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hγne, one_smul]
    calc R * a * R * (Ri * A * Ri) = R * a * (R * Ri) * A * Ri := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hRRi, Matrix.mul_one]
        calc R * a * A * Ri = R * (a * A) * Ri := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [haA, Matrix.mul_one, hRRi]
  have hQP : Q * P = 1 := by
    rw [hPdef, hQdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hγne, one_smul]
    calc Ri * A * Ri * (R * a * R) = Ri * A * (Ri * R) * a * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hRiR, Matrix.mul_one]
        calc Ri * A * a * R = Ri * (A * a) * R := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hAa, Matrix.mul_one, hRiR]
  have hQpsd : Q.PosSemidef := by
    have := hγ.posSemidef.conjTranspose_mul_mul_same Ri
    have h2 : Riᴴ = Ri := by simpa using hRiT
    rw [h2] at this
    rw [hQdef]
    exact this.smul (inv_nonneg.mpr hγ0)
  have hPT : Pᵀ = P := by
    rw [hPdef, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, hRT, haT,
      Matrix.mul_assoc]
  have hkey : 0 ≤ ((P - Y) * Q * (P - Y)).trace := by
    have := hQpsd.conjTranspose_mul_mul_same (P - Y)
    have h2 : (P - Y)ᴴ = P - Y := by simp [Matrix.conjTranspose_eq_transpose_of_trivial, hPT, hYT]
    rw [h2] at this
    exact this.trace_nonneg
  have hexp : (P - Y) * Q * (P - Y) = P - Y - Y + Y * Q * Y := by
    have e1 : P * Q * P = P := by rw [hPQ, Matrix.one_mul]
    have e2 : P * Q * Y = Y := by rw [hPQ, Matrix.one_mul]
    have e3 : Y * Q * P = Y := by rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, e1, e2, e3]
    abel
  have htrP : P.trace = γ * (a * Sigma).trace := by
    rw [hPdef, Matrix.trace_smul, smul_eq_mul]
    congr 1
    calc (R * a * R).trace = (R * (a * R)).trace := by rw [Matrix.mul_assoc]
      _ = ((a * R) * R).trace := Matrix.trace_mul_comm _ _
      _ = (a * Sigma).trace := by rw [Matrix.mul_assoc, hRR]
  have htrYQY : (Y * Q * Y).trace = γ⁻¹ * (A * L').trace := by
    calc (Y * Q * Y).trace = (Q * (Y * Y)).trace := by
          calc (Y * Q * Y).trace = (Y * (Q * Y)).trace := by rw [Matrix.mul_assoc]
            _ = ((Q * Y) * Y).trace := Matrix.trace_mul_comm _ _
            _ = (Q * (Y * Y)).trace := by rw [Matrix.mul_assoc]
      _ = (Q * (R * L' * R)).trace := by rw [hYY]
      _ = γ⁻¹ * (A * L').trace := by
          rw [hQdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
          congr 1
          calc (Ri * A * Ri * (R * L' * R)).trace = (Ri * (A * L') * R).trace := by
                rw [show Ri * A * Ri * (R * L' * R) = Ri * A * (Ri * R) * L' * R by
                  simp only [Matrix.mul_assoc], hRiR, Matrix.mul_one]
                simp only [Matrix.mul_assoc]
            _ = (Ri * ((A * L') * R)).trace := by rw [Matrix.mul_assoc]
            _ = (((A * L') * R) * Ri).trace := Matrix.trace_mul_comm _ _
            _ = (A * L').trace := by rw [Matrix.mul_assoc, hRRi, Matrix.mul_one]
  rw [hexp] at hkey
  simp only [Matrix.trace_add, Matrix.trace_sub, htrP, htrYQY] at hkey
  -- the inequality 2γ tr Y ≤ γ² tr(aΣ) + tr(A L')
  have h2 : 2 * γ * Y.trace ≤ γ ^ 2 * (a * Sigma).trace + (A * L').trace := by
    have := mul_nonneg hγpos.le hkey
    have e : γ * (γ * (a * Sigma).trace - Y.trace - Y.trace + γ⁻¹ * (A * L').trace) =
        γ ^ 2 * (a * Sigma).trace - 2 * γ * Y.trace + (A * L').trace := by
      field_simp
      ring
    linarith
  -- trace condition
  have htr' : L'.trace + Sigma.trace - 2 * Y.trace ≤ ρ ^ 2 := by
    simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at htr
    linarith
  have hZ : (aᵀ * Sigma).trace = (a * Sigma).trace := by rw [haT]
  have hLD : (L'ᵀ * D).trace = γ * L'.trace - (A * L').trace := by
    rw [hXT, hDA, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, Matrix.trace_mul_comm]
  rw [hZ, hLD]
  nlinarith [mul_le_mul_of_nonneg_left htr' hγ0, h2]

end AcceptedDual

open Matrix WassKF.Bisect
namespace KalmanSoundness
open scoped Matrix.Norms.L2Operator MatrixOrder

lemma grad_posSemidef {n m : ℕ} (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) :
    (gradF S).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma grad_diag {n m : ℕ} (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (i : Fin n) :
    gradF S (Sum.inl i) (Sum.inl i) = 1 := by
  simp [gradF, Matrix.mul_apply, Matrix.transpose_apply, Matrix.fromCols, Matrix.one_apply]

lemma top_eigenvalue_ge_one {n m : ℕ} (hn : 0 < n)
    (S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (lam : ℝ)
    (hlam : (lam • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - gradF S).PosSemidef) :
    1 ≤ lam := by
  have h := hlam.diag_nonneg (i := Sum.inl (⟨0,hn⟩ : Fin n))
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    grad_diag] at h
  linarith

lemma initial_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Sigma : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hSigma : Sigma.PosDef) (hv : v ⬝ᵥ v = 1) :
    lam < gammaMin Sigma ρ lam v ∧ gammaMin Sigma ρ lam v ≤ gammaMax Sigma ρ lam := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  have hquad : 0 < v ⬝ᵥ (Sigma *ᵥ v) := by simpa using hSigma.dotProduct_mulVec_pos hv0
  have hsqrt : 0 < Real.sqrt (v ⬝ᵥ (Sigma *ᵥ v)) := Real.sqrt_pos.mpr hquad
  have hbound := AcceptedInterval.KalmanResearch.rayleigh_le_trace Sigma hSigma.posSemidef v hv
  constructor
  · unfold gammaMin
    have hd := div_pos hsqrt hρ
    nlinarith [mul_pos hlam hd]
  · unfold gammaMin gammaMax
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hbound) hρ.le)) hlam.le

end KalmanSoundness

/-- The full soundness conjunct of Theorem3.2, under exactly its root hypotheses.
Termination is not asserted by this local supporting theorem. -/
theorem checked_soundness {n m : ℕ} (hn : 0 < n)
    (Sigma S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (ρ ε σ lam1 : ℝ)
    (v₁ : Fin n ⊕ Fin m → ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (hSigma : Sigma.PosDef) (hS : S.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (hlam : (lam1 • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - gradF S).PosSemidef)
    (hv : gradF S *ᵥ v₁ = lam1 • v₁) (hv1 : v₁ ⬝ᵥ v₁ = 1) :
    ∀ k : ℕ, bisectStops Sigma (gradF S) ρ ε lam1 v₁ k →
      bisectOutput Sigma (gradF S) ρ lam1 v₁ k ∈
          WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ ∧
        ∀ L' ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ,
          (L'ᵀ * gradF S).trace ≤
            ((bisectOutput Sigma (gradF S) ρ lam1 v₁ k)ᵀ * gradF S).trace + ε := by
  have hD := KalmanSoundness.grad_posSemidef S
  have hl : 0 < lam1 := lt_of_lt_of_le zero_lt_one (KalmanSoundness.top_eigenvalue_ge_one hn S lam1 hlam)
  obtain ⟨hstrict,horder⟩ := KalmanSoundness.initial_bounds Sigma ρ lam1 v₁ hρ hl hSigma hv1
  intro k hstop
  have hγ := LocalInvariants.KalmanAlgorithm.trial_posDef Sigma (gradF S) ρ lam1 v₁ horder hstrict hlam k
  have hb := (LocalInvariants.KalmanAlgorithm.trial_bounds Sigma (gradF S) ρ lam1 v₁ horder k).1
  have hγ0 : 0 ≤ bisectGamma Sigma (gradF S) ρ lam1 v₁ k := by linarith
  constructor
  · exact AcceptedFeasibility.solution Sigma (gradF S) ρ σ _ hρ hSigma hD hσ hσ_eig hγ hstop.1
  · intro L' hL'
    have hdual := AcceptedDual.solution Sigma (gradF S) ρ σ hρ hSigma hD hσ hσ_eig
      (bisectGamma Sigma (gradF S) ρ lam1 v₁ k) hγ0 hγ L' hL'
    have hgap := hstop.2
    unfold Delta at hgap
    unfold bisectOutput
    linarith

#print axioms checked_soundness

namespace KalmanAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gap_identity (Sigma D : Matrix ι ι ℝ) (ρ γ : ℝ) (hSigma : Sigma.PosSemidef)
    (hγ : (γ • (1 : Matrix ι ι ℝ) - D).PosDef) :
    Delta Sigma D ρ γ = γ * hFun Sigma D ρ γ := by
  let A := γ • (1 : Matrix ι ι ℝ) - D
  let a := A⁻¹
  change A.PosDef at hγ
  have hAT : Aᵀ = A := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hγ.isHermitian.eq
  have haT : aᵀ = a := by simp [a,Matrix.transpose_nonsing_inv,hAT]
  have hST : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  have hAu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hγ.isUnit
  have haA : a*A=1 := Matrix.nonsing_inv_mul A hAu
  have hDA : D = γ • (1 : Matrix ι ι ℝ) - A := by simp [A]
  have hada : a*D*a = γ • (a*a)-a := by
    rw [hDA,mul_sub,sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,haA,Matrix.one_mul]
  have hcyc : (a*Sigma*a*D).trace = (Sigma*(a*D*a)).trace := by
    calc
      _ = (a*(Sigma*a*D)).trace := by simp only [Matrix.mul_assoc]
      _ = ((Sigma*a*D)*a).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have hLt : (Lgamma Sigma D γ)ᵀ = Lgamma Sigma D γ := by
    unfold Lgamma
    change (γ^2 • (a*Sigma*a))ᵀ = γ^2 • (a*Sigma*a)
    simp [Matrix.transpose_mul,haT,hST,Matrix.mul_assoc]
  have hLD : ((Lgamma Sigma D γ)ᵀ * D).trace =
      γ^2 * (γ * (Sigma*(a*a)).trace - (Sigma*a).trace) := by
    rw [hLt]
    unfold Lgamma
    change ((γ^2 • (a*Sigma*a))*D).trace = _
    rw [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,hcyc,hada,
      Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul]
  have hsq : ((1 : Matrix ι ι ℝ)-γ • a)^2 =
      1-(2*γ) • a + γ^2 • (a*a) := by
    simp only [pow_two,mul_sub,sub_mul,Matrix.one_mul,Matrix.mul_one,
      Matrix.smul_mul,Matrix.mul_smul]
    module
  unfold Delta hFun
  change γ*(ρ^2-Sigma.trace)-((Lgamma Sigma D γ)ᵀ*D).trace+
    γ^2*(aᵀ*Sigma).trace = γ*(ρ^2-(Sigmaᵀ*(1-γ • a)^2).trace)
  rw [hLD,haT,hST,hsq,Matrix.mul_add,Matrix.mul_sub,Matrix.mul_one,
    Matrix.mul_smul,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_sub,
    Matrix.trace_smul,Matrix.trace_smul,smul_eq_mul,smul_eq_mul,Matrix.trace_mul_comm a Sigma]
  ring

end KalmanAnalytic
#print axioms KalmanAnalytic.gap_identity

namespace KalmanAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma resolvent_posDef (D : Matrix ι ι ℝ) (lam γ : ℝ)
    (hu : (lam • (1 : Matrix ι ι ℝ) - D).PosSemidef) (hg : lam < γ) :
    (γ • (1 : Matrix ι ι ℝ) - D).PosDef := by
  have h := ((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul (sub_pos.mpr hg)).add_posSemidef hu
  convert h using 1
  rw [sub_smul]
  abel

lemma initial_signs (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (hu : (lam • (1 : Matrix ι ι ℝ) - D).PosSemidef)
    (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1) :
    hFun Sigma D ρ (gammaMin Sigma ρ lam v) ≤ 0 ∧
      0 ≤ hFun Sigma D ρ (gammaMax Sigma ρ lam) := by
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv1
  have hq : 0 < v ⬝ᵥ (Sigma *ᵥ v) := by simpa using hSigma.dotProduct_mulVec_pos hv0
  have htr : 0 < Sigma.trace := hq.trans_le
    (AcceptedInterval.KalmanResearch.rayleigh_le_trace Sigma hSigma.posSemidef v hv1)
  have hST : Sigmaᵀ = Sigma := by simpa using hSigma.isHermitian.eq
  obtain ⟨hstrict,horder⟩ := KalmanSoundness.initial_bounds Sigma ρ lam v hρ hlam hSigma hv1
  have hlPD := resolvent_posDef D lam (gammaMin Sigma ρ lam v) hu hstrict
  have huPD := resolvent_posDef D lam (gammaMax Sigma ρ lam) hu (hstrict.trans_le horder)
  have hratio (a : ℝ) (ha : 0 < a) :
      (lam/(lam*(1+Real.sqrt a/ρ)-lam))^2*a = ρ^2 := by
    have he : lam/(lam*(1+Real.sqrt a/ρ)-lam) = ρ/Real.sqrt a := by
      have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
      field_simp [hs,hlam.ne',hρ.ne']
      <;> ring
    rw [he,div_pow,Real.sq_sqrt ha.le,div_mul_cancel₀ _ ha.ne']
  constructor
  · let γ := gammaMin Sigma ρ lam v
    let B := (1 : Matrix ι ι ℝ)-γ • (γ • (1 : Matrix ι ι ℝ)-D)⁻¹
    have hBT : Bᵀ = B := by
      have hAT : (γ • (1 : Matrix ι ι ℝ)-D)ᵀ = γ • (1 : Matrix ι ι ℝ)-D := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hlPD.isHermitian.eq
      simp [B,Matrix.transpose_nonsing_inv,hAT]
    have heig := AcceptedInterval.KalmanResearch.transport_eigenvector D lam γ v hv hv1 hlPD
    have hlow := AcceptedInterval.KalmanResearch.weighted_eigenvalue_bound Sigma B hSigma.posSemidef hBT v hv1
      (-(lam/(γ-lam))) heig
    rw [neg_sq] at hlow
    have he : (lam/(γ-lam))^2*(v ⬝ᵥ (Sigma *ᵥ v)) = ρ^2 := hratio _ hq
    rw [he] at hlow
    unfold hFun
    rw [hST]
    exact sub_nonpos.mpr hlow
  · let γ := gammaMax Sigma ρ lam
    let B := γ • (γ • (1 : Matrix ι ι ℝ)-D)⁻¹-1
    have hgap : 0 < γ-lam := sub_pos.mpr (hstrict.trans_le horder)
    obtain ⟨hB,hcap⟩ := AcceptedInterval.KalmanResearch.positive_resolvent_bounds D hD lam γ hlam.le hgap hu huPD
    have hup := AcceptedInterval.KalmanResearch.weighted_square_upper Sigma B hSigma.posSemidef hB
      (lam/(γ-lam)) (div_nonneg hlam.le hgap.le) hcap
    have he : (lam/(γ-lam))^2*Sigma.trace = ρ^2 := hratio _ htr
    rw [he] at hup
    have hneg : (1 : Matrix ι ι ℝ)-γ • (γ • (1 : Matrix ι ι ℝ)-D)⁻¹ = -B := by dsimp [B]; abel
    unfold hFun
    change 0 ≤ ρ^2-(Sigmaᵀ*((1 : Matrix ι ι ℝ)-γ • (γ • (1 : Matrix ι ι ℝ)-D)⁻¹)^2).trace
    rw [hST,hneg,neg_sq]
    exact sub_nonneg.mpr hup

end KalmanAnalytic
#print axioms KalmanAnalytic.initial_signs

open Matrix WassKF.Bisect
namespace KalmanAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 800000 in
lemma hFun_continuousAt (Sigma D : Matrix ι ι ℝ) (ρ γ : ℝ)
    (hγ : (γ • (1 : Matrix ι ι ℝ)-D).PosDef) :
    ContinuousAt (hFun Sigma D ρ) γ := by
  let A := γ • (1 : Matrix ι ι ℝ)-D
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hγ.isUnit
  have hdet : ContinuousAt Ring.inverse A.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp hu)
  have hmat : Continuous (fun t : ℝ => t • (1 : Matrix ι ι ℝ)-D) :=
    (continuous_id.smul continuous_const).sub continuous_const
  have hi : ContinuousAt (fun t : ℝ => (t • (1 : Matrix ι ι ℝ)-D)⁻¹) γ :=
    (continuousAt_matrix_inv A hdet).comp hmat.continuousAt
  have hh : ContinuousAt (fun t : ℝ => (1 : Matrix ι ι ℝ)-t • (t • (1 : Matrix ι ι ℝ)-D)⁻¹) γ :=
    continuousAt_const.sub (continuousAt_id.smul hi)
  have hm : ContinuousAt (fun t : ℝ => Sigmaᵀ * ((1 : Matrix ι ι ℝ)-t • (t • (1 : Matrix ι ι ℝ)-D)⁻¹)^2) γ :=
    continuousAt_const.mul (hh.pow 2)
  have ht : Continuous (fun M : Matrix ι ι ℝ => M.trace) := continuous_id.matrix_trace
  unfold hFun
  exact continuousAt_const.sub (ht.continuousAt.comp hm)
end KalmanAnalytic
#print axioms KalmanAnalytic.hFun_continuousAt

open Matrix WassKF.Bisect Filter
open scoped Topology
namespace KalmanTermination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open LocalInvariants.KalmanAlgorithm

lemma lower_mono (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (horder : gammaMin Sigma ρ lam v ≤ gammaMax Sigma ρ lam) :
    Monotone (fun k => (bisectState Sigma D ρ lam v k).1) := by
  apply monotone_nat_of_le_succ
  intro k
  have hb := bracket_bounds Sigma D ρ lam v horder k
  simp only [bisectState]
  split <;> dsimp <;> linarith [hb.2.1]

lemma bracket_signs (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (hl : hFun Sigma D ρ (gammaMin Sigma ρ lam v) ≤ 0)
    (hu : 0 < hFun Sigma D ρ (gammaMax Sigma ρ lam))
    (hnz : ∀ k, hFun Sigma D ρ (bisectGamma Sigma D ρ lam v k) ≠ 0) (k : ℕ) :
    hFun Sigma D ρ (bisectState Sigma D ρ lam v k).1 ≤ 0 ∧
      0 < hFun Sigma D ρ (bisectState Sigma D ρ lam v k).2 := by
  induction k with
  | zero => exact ⟨hl,hu⟩
  | succ k ih =>
    simp only [bisectState]
    split
    · rename_i h; exact ⟨h.le,ih.2⟩
    · rename_i h
      exact ⟨ih.1,lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hnz k))⟩

lemma limits (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (horder : gammaMin Sigma ρ lam v ≤ gammaMax Sigma ρ lam) :
    ∃ c ∈ Set.Icc (gammaMin Sigma ρ lam v) (gammaMax Sigma ρ lam),
      Tendsto (fun k => (bisectState Sigma D ρ lam v k).1) atTop (𝓝 c) ∧
      Tendsto (fun k => (bisectState Sigma D ρ lam v k).2) atTop (𝓝 c) ∧
      Tendsto (bisectGamma Sigma D ρ lam v) atTop (𝓝 c) := by
  let l := fun k => (bisectState Sigma D ρ lam v k).1
  let u := fun k => (bisectState Sigma D ρ lam v k).2
  have hb : BddAbove (Set.range l) := by
    refine ⟨gammaMax Sigma ρ lam,?_⟩
    rintro x ⟨k,rfl⟩
    exact (bracket_bounds Sigma D ρ lam v horder k).2.1.trans
      (bracket_bounds Sigma D ρ lam v horder k).2.2
  let c := ⨆ k, l k
  have hl : Tendsto l atTop (𝓝 c) := tendsto_atTop_ciSup (lower_mono Sigma D ρ lam v horder) hb
  have hc : c ∈ Set.Icc (gammaMin Sigma ρ lam v) (gammaMax Sigma ρ lam) := by
    constructor
    · exact le_ciSup hb 0
    · exact ciSup_le (fun k => (bracket_bounds Sigma D ρ lam v horder k).2.1.trans
        (bracket_bounds Sigma D ρ lam v horder k).2.2)
  have hw : Tendsto (fun k : ℕ => (gammaMax Sigma ρ lam-gammaMin Sigma ρ lam v)/(2:ℝ)^k) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
      (by norm_num : (2:ℝ)⁻¹ < 1)).const_mul (gammaMax Sigma ρ lam-gammaMin Sigma ρ lam v)
    simpa only [div_eq_mul_inv,inv_pow,mul_zero] using hp
  have hu : Tendsto u atTop (𝓝 c) := by
    have hh := hl.add hw
    simp only [add_zero] at hh
    convert hh using 1
    funext k
    have h := bracket_width Sigma D ρ lam v k
    dsimp [l,u]
    linarith
  refine ⟨c,hc,hl,hu,?_⟩
  have hh := (hu.add hl).div_const 2
  convert hh using 1 <;> first | rfl | congr 1 <;> ring

lemma positive_late (Sigma D : Matrix ι ι ℝ) (ρ lam : ℝ) (v : ι → ℝ)
    (c : ℝ)
    (hu : Tendsto (fun k => (bisectState Sigma D ρ lam v k).2) atTop (𝓝 c))
    (hroot : hFun Sigma D ρ c = 0)
    (hpos : ∀ k, 0 < hFun Sigma D ρ (bisectState Sigma D ρ lam v k).2)
    (hnz : ∀ k, hFun Sigma D ρ (bisectGamma Sigma D ρ lam v k) ≠ 0) :
    ∀ N : ℕ, ∃ k, N ≤ k ∧ 0 < hFun Sigma D ρ (bisectGamma Sigma D ρ lam v k) := by
  intro N
  by_contra h
  push_neg at h
  have hneg (k : ℕ) (hk : N ≤ k) : hFun Sigma D ρ (bisectGamma Sigma D ρ lam v k) < 0 :=
    lt_of_le_of_ne (h k hk) (hnz k)
  have hconst (j : ℕ) : (bisectState Sigma D ρ lam v (N+j)).2 = (bisectState Sigma D ρ lam v N).2 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.add_succ,bisectState]
      have ht := hneg (N+j) (by omega)
      unfold bisectGamma at ht
      simp only [if_pos ht]
      exact ih
  have heq : (fun k => (bisectState Sigma D ρ lam v k).2) =ᶠ[atTop]
      (fun _ => (bisectState Sigma D ρ lam v N).2) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hconst j
  have hc : c = (bisectState Sigma D ρ lam v N).2 :=
    tendsto_nhds_unique hu (tendsto_const_nhds.congr' heq.symm)
  have hp := hpos N
  rw [← hc,hroot] at hp
  exact (lt_irrefl 0) hp

lemma terminates (Sigma D : Matrix ι ι ℝ) (ρ ε lam : ℝ) (v : ι → ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (hlam : 0 < lam) (hSigma : Sigma.PosDef) (hD : D.PosSemidef)
    (huD : (lam • (1 : Matrix ι ι ℝ)-D).PosSemidef)
    (hv : D *ᵥ v = lam • v) (hv1 : v ⬝ᵥ v = 1)
    (hgrid : ∀ k j : ℕ, 0 < j → j ≤ 2^k →
      hFun Sigma D ρ (gammaMin Sigma ρ lam v + (j:ℝ)*(gammaMax Sigma ρ lam-gammaMin Sigma ρ lam v)/2^k) ≠ 0) :
    ∃ k, bisectStops Sigma D ρ ε lam v k := by
  obtain ⟨hstrict,horder⟩ := KalmanSoundness.initial_bounds Sigma ρ lam v hρ hlam hSigma hv1
  obtain ⟨hlo,hhi⟩ := KalmanAnalytic.initial_signs Sigma D ρ lam v hρ hlam hSigma hD huD hv hv1
  have hupper_ne : hFun Sigma D ρ (gammaMax Sigma ρ lam) ≠ 0 := by
    simpa using hgrid 0 1 (by omega) (by norm_num)
  have hupper : 0 < hFun Sigma D ρ (gammaMax Sigma ρ lam) := lt_of_le_of_ne hhi hupper_ne.symm
  have hnz := trial_not_root Sigma D ρ lam v hgrid
  have hsign := bracket_signs Sigma D ρ lam v hlo hupper hnz
  obtain ⟨c,hc,hl,hu,hγ⟩ := limits Sigma D ρ lam v horder
  have hcPD := KalmanAnalytic.resolvent_posDef D lam c huD (hstrict.trans_le hc.1)
  have hcont := KalmanAnalytic.hFun_continuousAt Sigma D ρ c hcPD
  have hroot : hFun Sigma D ρ c = 0 := by
    apply le_antisymm
    · exact le_of_tendsto' (hcont.tendsto.comp hl) (fun k => (hsign k).1)
    · exact ge_of_tendsto' (hcont.tendsto.comp hu) (fun k => (hsign k).2.le)
  have hgap : Tendsto (fun k => Delta Sigma D ρ (bisectGamma Sigma D ρ lam v k)) atTop (𝓝 0) := by
    have hh := hγ.mul (hcont.tendsto.comp hγ)
    rw [hroot,mul_zero] at hh
    convert hh using 1
    funext k
    exact KalmanAnalytic.gap_identity Sigma D ρ _ hSigma.posSemidef
      (trial_posDef Sigma D ρ lam v horder hstrict huD k)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hgap.eventually (gt_mem_nhds hε))
  obtain ⟨k,hk,hpos⟩ := positive_late Sigma D ρ lam v c hu hroot (fun k => (hsign k).2) hnz N
  exact ⟨k,hpos,hN k hk⟩

end KalmanTermination
#print axioms KalmanTermination.limits
#print axioms KalmanTermination.positive_late
#print axioms KalmanTermination.terminates

/-- Full corrected platform Theorem3.2. -/
theorem solution : ∀ {n m : ℕ},
  OfNat.ofNat 0 < n →
    ∀ (Sigma S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (ρ ε σ lam1 : ℝ) (v₁ : Fin n ⊕ Fin m → ℝ),
      OfNat.ofNat 0 < ρ →
        OfNat.ofNat 0 < ε →
          Sigma.PosDef →
            S.PosSemidef →
              (Sigma - σ • OfNat.ofNat 1).PosSemidef →
                (∃ (v : Fin n ⊕ Fin m → ℝ), v ≠ OfNat.ofNat 0 ∧ Sigma *ᵥ v = σ • v) →
                  (lam1 • OfNat.ofNat 1 - WassKF.Bisect.gradF S).PosSemidef →
                    WassKF.Bisect.gradF S *ᵥ v₁ = lam1 • v₁ →
                      v₁ ⬝ᵥ v₁ = OfNat.ofNat 1 →
                        (∀ (k : ℕ),
                            WassKF.Bisect.bisectStops Sigma (WassKF.Bisect.gradF S) ρ ε lam1 v₁ k →
                              WassKF.Bisect.bisectOutput Sigma (WassKF.Bisect.gradF S) ρ lam1 v₁ k ∈
                                  WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ ∧
                                ∀ L' ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ,
                                  (L'ᵀ * WassKF.Bisect.gradF S).trace ≤
                                    ((WassKF.Bisect.bisectOutput Sigma (WassKF.Bisect.gradF S) ρ lam1 v₁ k)ᵀ *
                                          WassKF.Bisect.gradF S).trace +
                                      ε) ∧
                          ((∀ (k j : ℕ),
                              OfNat.ofNat 0 < j →
                                j ≤ OfNat.ofNat 2 ^ k →
                                  WassKF.Bisect.hFun Sigma (WassKF.Bisect.gradF S) ρ
                                      (WassKF.Bisect.gammaMin Sigma ρ lam1 v₁ +
                                        j.cast *
                                            (WassKF.Bisect.gammaMax Sigma ρ lam1 -
                                              WassKF.Bisect.gammaMin Sigma ρ lam1 v₁) /
                                          OfNat.ofNat 2 ^ k) ≠
                                    OfNat.ofNat 0) →
                            ∃ (k : ℕ), WassKF.Bisect.bisectStops Sigma (WassKF.Bisect.gradF S) ρ ε lam1 v₁ k) := by
  intro n m hn Sigma S ρ ε σ lam1 v₁ hρ hε hSigma hS hσ hσ_eig hlam hv hv1
  constructor
  · exact checked_soundness hn Sigma S ρ ε σ lam1 v₁ hρ hε hSigma hS hσ hσ_eig hlam hv hv1
  · intro hgrid
    have hl : 0 < lam1 := lt_of_lt_of_le zero_lt_one
      (KalmanSoundness.top_eigenvalue_ge_one hn S lam1 hlam)
    exact KalmanTermination.terminates Sigma (gradF S) ρ ε lam1 v₁ hρ hε hl hSigma
      (KalmanSoundness.grad_posSemidef S) hlam hv hv1 hgrid
#print axioms solution
