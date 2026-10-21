-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P01.finiteAncillaTomography
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:38:54.229762+00:00
-- url     : https://prove2.me/submissions/81733873-5c9c-459b-bcd1-4f73032c67f0

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01
noncomputable section

theorem G64B.pi_exp {I : Type*} [Fintype I] [DecidableEq I] (v : Fin 2 → Matrix I I ℂ) (a : Fin 2) :
    NormedSpace.exp v a = NormedSpace.exp (v a) := by
  let _ : NormedRing (Matrix I I ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix I I ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix I I ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix I I ℂ) := FiniteDimensional.complete ℂ _
  exact Pi.coe_exp v a


open Filter MeasureTheory Set

open scoped BigOperators ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology ENNReal

open QAlgorithms.Papers.Independent.Next46.P01
open scoped Matrix

namespace G64B

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exp_conj2 (P Q A : Matrix I I ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    NormedSpace.exp (P * A * Q) = P * NormedSpace.exp A * Q := by
  have hQ : Q = P⁻¹ := (Matrix.inv_eq_right_inv hPQ).symm
  have hU : IsUnit P := ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
  rw [hQ]; exact Matrix.exp_conj P A hU

theorem exp_add_smul (L : Matrix I I ℂ) (a b : ℂ) :
    NormedSpace.exp (a • L) * NormedSpace.exp (b • L) = NormedSpace.exp ((a + b) • L) := by
  rw [add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl L).smul_left a).smul_right b

theorem exp_inv_smul (L : Matrix I I ℂ) (a : ℂ) :
    NormedSpace.exp (a • L) * NormedSpace.exp ((-a) • L) = 1 := by
  rw [exp_add_smul]; simp [NormedSpace.exp_zero]

theorem exp_inv_smul' (L : Matrix I I ℂ) (a : ℂ) :
    NormedSpace.exp ((-a) • L) * NormedSpace.exp (a • L) = 1 := by
  rw [exp_add_smul]; simp [NormedSpace.exp_zero]

theorem exp_ct (L : Matrix I I ℂ) (hL : L.IsHermitian) (a : ℂ) :
    (NormedSpace.exp (a • L))ᴴ = NormedSpace.exp ((starRingEnd ℂ a) • L) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hL.eq]; rfl

theorem cfc_conj (u : Matrix.unitaryGroup I ℂ)
    (f : ℝ → ℝ) (A : Matrix I I ℂ) :
    cfc f ((u : Matrix I I ℂ) * A * (u : Matrix I I ℂ)ᴴ) =
      (u : Matrix I I ℂ) * cfc f A * (u : Matrix I I ℂ)ᴴ := by
  by_cases hA : IsSelfAdjoint A
  · let φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) u
    have hφ : Continuous φ :=
      (φ.toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional
    have hφa : IsSelfAdjoint (φ A) := by
      simp only [φ, Unitary.conjStarAlgAut_apply]
      exact hA.conjugate _
    have := StarAlgHomClass.map_cfc φ f A ((Matrix.finite_real_spectrum).continuousOn _) hφ hA hφa
    simpa [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using this.symm
  · have h2 : ¬ IsSelfAdjoint ((u : Matrix I I ℂ) * A * (u : Matrix I I ℂ)ᴴ) := by
      intro h
      apply hA
      have h3 := h.conjugate ((u : Matrix I I ℂ)ᴴ)
      have hu : (u : Matrix I I ℂ)ᴴ * (u : Matrix I I ℂ) = 1 := Unitary.star_mul_self_of_mem u.2
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h3
      have : (u : Matrix I I ℂ)ᴴ * ((u : Matrix I I ℂ) * A * (u : Matrix I I ℂ)ᴴ) *
          (u : Matrix I I ℂ) = A := by
        rw [show (u : Matrix I I ℂ)ᴴ * ((u : Matrix I I ℂ) * A * (u : Matrix I I ℂ)ᴴ) *
          (u : Matrix I I ℂ) = ((u : Matrix I I ℂ)ᴴ * (u : Matrix I I ℂ)) * A *
            ((u : Matrix I I ℂ)ᴴ * (u : Matrix I I ℂ)) by simp only [Matrix.mul_assoc]]
        rw [hu, Matrix.one_mul, Matrix.mul_one]
      rwa [this] at h3
    rw [cfc_apply_of_not_predicate _ h2, cfc_apply_of_not_predicate _ hA]
    simp

/-- W = exp(i s H) is unitary. -/
theorem expH_ct (H : Matrix I I ℂ) (hH : H.IsHermitian) (s : ℝ) :
    (NormedSpace.exp ((Complex.I * (s : ℂ)) • H))ᴴ =
      NormedSpace.exp ((-(Complex.I * (s : ℂ))) • H) := by
  rw [exp_ct H hH]; congr 2; simp [Complex.conj_ofReal]

theorem traceLeft_block (X Y : Fin 2 → Matrix I I ℂ) (nu : Matrix I I ℂ)
    (rho : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    QAlgorithms.traceLeft (Matrix.blockDiagonal X * Matrix.kronecker nu rho *
      Matrix.blockDiagonal Y) a b = rho a b * (X a * nu * Y b).trace := by
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.trace,
    Matrix.diag, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end G64B

open G64B in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (H omega nu : Matrix I I ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (hH : H.IsHermitian) (homega : QAlgorithms.IsDensityMatrix omega)
    (hfaithful : omega.PosDef) (hnu : QAlgorithms.IsDensityMatrix nu)
    (hrho : QAlgorithms.IsDensityMatrix rho) (hcoherence : rho 0 1 ≠ 0)
    (t : ℝ) (alpha : ℂ) (himaginary : alpha.re = 0) :
    QAlgorithms.traceLeft
      (finiteDensityAt (finiteAncillaHamiltonian H omega alpha)
        (Matrix.kronecker nu rho) t) =
      ancillaReadout rho (finiteAncillaFunctional H omega nu t alpha) := by
  set L := cfc Real.log omega with hLdef
  have hL : L.IsHermitian := (cfc_predicate Real.log omega : IsSelfAdjoint L)
  let E : ℂ → Matrix I I ℂ := fun c => NormedSpace.exp (c • L)
  let c : Fin 2 → ℂ := fun a => alpha / 2 * ancillaSigmaZ a a
  have hK1 : (alpha / 2) • Matrix.kronecker L ancillaSigmaZ =
      Matrix.blockDiagonal (fun a => c a • L) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [c, Matrix.kronecker, Matrix.blockDiagonal_apply, ancillaSigmaZ]
  have hK2 : (-alpha / 2) • Matrix.kronecker L ancillaSigmaZ =
      Matrix.blockDiagonal (fun a => (-c a) • L) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    fin_cases a <;> fin_cases b <;>
      simp [c, Matrix.kronecker, Matrix.blockDiagonal_apply, ancillaSigmaZ] <;> ring
  have hH1 : Matrix.kronecker H (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.blockDiagonal (fun _ => H) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.kronecker, Matrix.blockDiagonal_apply, Matrix.one_apply]
  have hHa : finiteAncillaHamiltonian H omega alpha =
      Matrix.blockDiagonal (fun a => E (c a) * H * E (-c a)) := by
    simp only [finiteAncillaHamiltonian]
    rw [hK1, hK2, hH1, Matrix.exp_blockDiagonal, Matrix.exp_blockDiagonal,
      ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
    congr 1
    funext a
    rw [pi_exp, pi_exp]
  have hexpb : ∀ z : ℂ, NormedSpace.exp (z • finiteAncillaHamiltonian H omega alpha) =
      Matrix.blockDiagonal (fun a => E (c a) * NormedSpace.exp (z • H) * E (-c a)) := by
    intro z
    rw [hHa, ← Matrix.blockDiagonal_smul, Matrix.exp_blockDiagonal]
    congr 1
    funext a
    rw [pi_exp]
    simp only [Pi.smul_apply]
    rw [show z • (E (c a) * H * E (-c a)) = E (c a) * (z • H) * E (-c a) by simp]
    exact exp_conj2 _ _ _ (exp_inv_smul L (c a)) (exp_inv_smul' L (c a))
  set W := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) with hW
  set W' := NormedSpace.exp ((Complex.I * (t : ℂ)) • H) with hW'
  have hWW' : W * W' = 1 := by
    rw [hW, hW', neg_mul]; exact exp_inv_smul' H _
  have hW'W : W' * W = 1 := by
    rw [hW, hW', neg_mul]; exact exp_inv_smul H _
  have hW'ct : W'ᴴ = W := by rw [hW', expH_ct H hH t, hW, neg_mul]
  have hWct : Wᴴ = W' := by rw [← hW'ct, Matrix.conjTranspose_conjTranspose]
  have hEE : ∀ x y : ℂ, E x * E y = E (x + y) := fun x y => exp_add_smul L x y
  have hE0 : E 0 = 1 := by simp [E, NormedSpace.exp_zero]
  have hEct : ∀ x : ℂ, (E x)ᴴ = E (starRingEnd ℂ x) := fun x => exp_ct L hL x
  have hconj : starRingEnd ℂ alpha = -alpha := by
    apply Complex.ext <;> simp [himaginary]
  have hD : finiteDensityAt H omega (-t) = W' * omega * W'ᴴ := by
    rw [hW'ct]; simp only [finiteDensityAt, hW, hW']; push_cast; ring_nf
  have hFP : finitePower (finiteDensityAt H omega (-t)) alpha = W' * E alpha * W := by
    have hu : W' ∈ Matrix.unitaryGroup I ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hW'ct]; exact hW'W
    have := cfc_conj ⟨W', hu⟩ Real.log omega
    simp only at this
    rw [finitePower, hD, this, hW'ct, ← hLdef]
    rw [show alpha • (W' * L * W) = W' * (alpha • L) * W by simp]
    exact exp_conj2 _ _ _ hW'W hWW'
  have hF : finiteAncillaFunctional H omega nu t alpha =
      (nu * E (-alpha / 2) * (W' * E alpha * W) * E (-alpha / 2)).trace := by
    rw [finiteAncillaFunctional, hFP]; rfl
  have hnuct : nuᴴ = nu := hnu.1.1
  have key : ∀ a b : Fin 2,
      ((E (c a) * NormedSpace.exp ((-Complex.I * (t : ℂ)) • H) * E (-c a)) * nu *
        (E (c b) * NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * E (-c b))).trace =
      (nu * (E (c b) * W' * (E (-c b) * E (c a)) * W * E (-c a))).trace := by
    intro a b
    have gen : ∀ X N Y : Matrix I I ℂ, (X * N * Y).trace = (N * (Y * X)).trace := by
      intro X N Y
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [← hW, ← hW', gen]
    simp only [Matrix.mul_assoc]
  have hc0 : c 0 = alpha / 2 := by simp [c, ancillaSigmaZ]
  have hc1 : c 1 = -alpha / 2 := by simp [c, ancillaSigmaZ]; ring
  simp only [finiteDensityAt]
  rw [hexpb, hexpb]
  ext a b
  rw [traceLeft_block, key]
  have hconjF : starRingEnd ℂ (finiteAncillaFunctional H omega nu t alpha) =
      (nu * (E (alpha / 2) * W' * E (-alpha) * W * E (alpha / 2))).trace := by
    rw [hF, show ∀ A : Matrix I I ℂ, starRingEnd ℂ A.trace = (Aᴴ).trace from
      fun A => (Matrix.trace_conjTranspose A).symm]
    simp only [Matrix.conjTranspose_mul, hEct, hW'ct, hWct, hnuct, map_neg, map_div₀, hconj,
      map_ofNat, neg_div, neg_neg]
    rw [Matrix.trace_mul_comm nu]
    simp only [Matrix.mul_assoc]
  have e1 : -(-alpha / 2) + alpha / 2 = alpha := by ring
  have e2 : -(alpha / 2) = -alpha / 2 := by ring
  have e3 : -(alpha / 2) + -alpha / 2 = -alpha := by ring
  have e4 : -(-alpha / 2) = alpha / 2 := by ring
  fin_cases a <;> fin_cases b
  · simp only [ancillaReadout]
    simp
    rw [hEE, neg_add_cancel, hE0, Matrix.mul_one, Matrix.mul_assoc (E _) W' W, hW'W,
      Matrix.mul_one, hEE, add_neg_cancel, hE0, Matrix.mul_one, hnu.2, mul_one]
  · simp [ancillaReadout]
    rw [hF, hEE, hc0, hc1, e1, e2, mul_comm]
    congr 1
    simp only [Matrix.mul_assoc]
  · simp [ancillaReadout]
    rw [hconjF, hEE, hc0, hc1, e3, e4, mul_comm]
  · simp only [ancillaReadout]
    simp
    rw [hEE, neg_add_cancel, hE0, Matrix.mul_one, Matrix.mul_assoc (E _) W' W, hW'W,
      Matrix.mul_one, hEE, add_neg_cancel, hE0, Matrix.mul_one, hnu.2, mul_one]

end
