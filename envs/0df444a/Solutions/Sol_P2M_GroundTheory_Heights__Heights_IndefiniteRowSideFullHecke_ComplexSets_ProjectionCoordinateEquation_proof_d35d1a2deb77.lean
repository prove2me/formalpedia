-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProjectionCoordinateEquation_proof_d35d1a2deb77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:47.690398+00:00
-- url     : https://prove2.me/submissions/86221950-42db-4300-aec3-a1a38edcb16c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionCoordinateEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionCoordinateEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_aeval_cons_eq_eval__finSuccEquiv_b773e260af41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_finSuccEquiv_pderiv_zero_1571138ea42c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_algHom_aeval_eq_eval_e9fd7e8da1f5
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ProjectionCoordinateEquation
theorem _root_.solution : ProjectionCoordinateEquation.Statement := by
  intro n k J A O hV hO hOne hcov j
  have := hV.isPrime
  set B := MvPolynomial (Fin n) ℂ ⧸ J
  let π := Ideal.Quotient.mkₐ ℂ J
  let y : Fin k → B := fun i => π (∑ l, C (A i l) * X l)
  let z : B := π (X j)
  let φ : MvPolynomial (Fin k) ℂ →+* B := (aeval y).toRingHom

  have hev : ∀ x ∈ zeroLocus J, ∃ e : B →ₐ[ℂ] ℂ, (∀ i, e (y i) = (A *ᵥ x) i) ∧ e z = x j := by
    intro x hx
    let e : B →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ J (aeval x) (fun q hq =>
      (RingHom.congr_fun (coe_aeval_eq_eval x) q).trans (hx q hq))
    have he : ∀ q, e (π q) = aeval x q := fun q => rfl
    refine ⟨e, fun i => ?_, ?_⟩
    · rw [he]
      simp [Matrix.mulVec, dotProduct]
    · rw [he, aeval_X]

  have hind : AlgebraicIndependent ℂ y := by
    rw [algebraicIndependent_iff]
    intro F hF
    obtain ⟨y₀, hy₀⟩ := hOne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
    refine funext_set (fun i => Metric.ball (y₀ i) ε)
      (fun i => infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hε)) fun v hv => ?_
    have hvO : v ∈ O := hball (by rw [ball_pi _ hε]; exact hv)
    obtain ⟨x, hx, rfl⟩ := hcov v hvO
    obtain ⟨e, hey, -⟩ := hev x hx
    have := algHom_aeval_eq_eval e y F
    rw [hF, map_zero] at this
    simp only [hey] at this
    rw [map_zero, ← this]

  have : Algebra.FiniteType ℂ B := inferInstance
  have htr := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℂ (A := B)
  rw [hV.dim] at htr
  have hle : Algebra.trdeg ℂ B ≤ k := by
    rw [← Cardinal.toENat_le_natCast]
    exact le_of_eq (by exact_mod_cast htr.symm)
  have hdep : ∀ b : B, ∃ p : Polynomial (MvPolynomial (Fin k) ℂ), p ≠ 0 ∧ p.eval₂ φ b = 0 := by
    intro b
    have hni : ¬ AlgebraicIndependent ℂ (Fin.cons b y : Fin (k + 1) → B) := by
      intro h
      have := h.cardinalMk_le_trdeg.trans hle
      rw [Cardinal.mk_fin, Nat.cast_le] at this
      omega
    rw [algebraicIndependent_iff] at hni
    push Not at hni
    obtain ⟨R, hR, hR0⟩ := hni
    refine ⟨finSuccEquiv ℂ k R, fun h => hR0 ((finSuccEquiv ℂ k).injective (by rw [h, map_zero])), ?_⟩
    rw [← aeval_cons_eq_eval₂_finSuccEquiv, hR]

  have hex : ∃ d, ∃ p : Polynomial (MvPolynomial (Fin k) ℂ), p ≠ 0 ∧ p.natDegree = d ∧ p.eval₂ φ z = 0 := by
    obtain ⟨p, hp, hpz⟩ := hdep z
    exact ⟨_, p, hp, rfl, hpz⟩
  classical
  obtain ⟨P, hP0, hPd, hPz⟩ := Nat.find_spec hex
  have hmin := fun d (hd : d < Nat.find hex) => Nat.find_min hex hd
  have hdeg : P.natDegree ≠ 0 := by
    intro h0
    rw [Polynomial.natDegree_eq_zero] at h0
    obtain ⟨c, rfl⟩ := h0
    rw [Polynomial.eval₂_C] at hPz
    have hc : c = 0 := (algebraicIndependent_iff.mp hind) c hPz
    exact hP0 (by rw [hc, map_zero])
  have hP'0 : Polynomial.derivative P ≠ 0 := fun h =>
    hdeg (Polynomial.derivative_eq_zero.mp h)
  set w := (Polynomial.derivative P).eval₂ φ z with hw
  have hw0 : w ≠ 0 := by
    intro h
    refine hmin _ ?_ ⟨_, hP'0, rfl, h⟩
    rw [← hPd]
    exact Polynomial.natDegree_derivative_lt hdeg

  obtain ⟨r, hr0, hrw⟩ := hdep w
  obtain ⟨q, hrq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr0 0
  rw [map_zero, sub_zero, Polynomial.X_dvd_iff] at hq
  rw [map_zero, sub_zero] at hrq
  have hqw : q.eval₂ φ w = 0 := by
    rw [hrq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hrw
    exact (mul_eq_zero.mp hrw).resolve_left (pow_ne_zero _ hw0)
  rw [← Polynomial.divX_mul_X_add q, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at hqw
  refine ⟨(finSuccEquiv ℂ k).symm P, q.coeff 0, hq, fun x hx => ?_, fun x hx hD => ?_⟩
  · obtain ⟨e, hey, hez⟩ := hev x hx
    have h1 := algHom_aeval_eq_eval e (Fin.cons z y : Fin (k + 1) → B) ((finSuccEquiv ℂ k).symm P)
    rw [aeval_cons_eq_eval₂_finSuccEquiv, AlgEquiv.apply_symm_apply] at h1
    have h2 : (fun i => e ((Fin.cons z y : Fin (k + 1) → B) i)) = Fin.cons (x j) (A *ᵥ x) := by
      funext i
      cases i using Fin.cases with
      | zero => simpa using hez
      | succ i => simpa using hey i
    rw [← h2, ← h1]
    exact hPz.symm ▸ map_zero e
  · obtain ⟨e, hey, hez⟩ := hev x hx
    have h1 := algHom_aeval_eq_eval e (Fin.cons z y : Fin (k + 1) → B)
      (pderiv 0 ((finSuccEquiv ℂ k).symm P))
    rw [aeval_cons_eq_eval₂_finSuccEquiv, finSuccEquiv_pderiv_zero, AlgEquiv.apply_symm_apply] at h1
    have h2 : (fun i => e ((Fin.cons z y : Fin (k + 1) → B) i)) = Fin.cons (x j) (A *ᵥ x) := by
      funext i
      cases i using Fin.cases with
      | zero => simpa using hez
      | succ i => simpa using hey i
    rw [← h2, ← h1]
    intro hwx
    change e w = 0 at hwx
    apply hD
    have h3 := algHom_aeval_eq_eval e y (q.coeff 0)
    have h4 : φ (q.coeff 0) = -((q.divX.eval₂ φ w) * w) := eq_neg_of_add_eq_zero_right hqw
    change e (φ (q.coeff 0)) = _ at h3
    rw [h4, map_neg, map_mul, hwx, mul_zero, neg_zero] at h3
    simp only [hey] at h3
    exact h3.symm
end ProjectionCoordinateEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
