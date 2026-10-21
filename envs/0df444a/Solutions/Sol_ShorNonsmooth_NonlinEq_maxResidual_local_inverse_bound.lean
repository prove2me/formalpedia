-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.maxResidual_local_inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:51:14.347847+00:00
-- url     : https://prove2.me/submissions/62b87d98-c9a6-4692-89d3-9cecfc282b06

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ShorNonsmooth.NonlinEq

theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hroot : ∀ i, ψ i xstar = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U)
    (hJ : (jacobianMatrix ψ xstar).det ≠ 0) :
    ∃ V ∈ nhds xstar, ∃ C > 0, ∀ x ∈ V,
      ‖x - xstar‖ ≤ C * maxResidual ψ x := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun d i => fderiv ℝ (ψ i) xstar d
      map_add' := by
        intro a b
        ext i
        simp
      map_smul' := by
        intro c a
        ext i
        simp }
  have hzero : ∀ d, T d = 0 → d = 0 := by
    intro d hd
    have hcoords : ∀ i, fderiv ℝ (ψ i) xstar d = 0 := by
      intro i
      exact congrFun hd i
    let v : Fin n → ℝ := fun j => d j
    have hsum : ∑ j, d j • EuclideanSpace.single j 1 = d := by
      simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr d
    have hJv : (jacobianMatrix ψ xstar).mulVec v = 0 := by
      funext i
      calc
        (jacobianMatrix ψ xstar).mulVec v i
            = ∑ j, fderiv ℝ (ψ i) xstar (EuclideanSpace.single j 1) * d j := by
                simp [v, jacobianMatrix, Matrix.mulVec, dotProduct, mul_comm]
        _ = ∑ j, fderiv ℝ (ψ i) xstar (d j • EuclideanSpace.single j 1) := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [map_smul, mul_comm]
        _ = fderiv ℝ (ψ i) xstar (∑ j, d j • EuclideanSpace.single j 1) := by
                rw [map_sum]
        _ = fderiv ℝ (ψ i) xstar d := by rw [hsum]
        _ = 0 := hcoords i
    have hv : v = 0 :=
      Matrix.mulVec_injective_of_det_ne_zero hJ (by simpa using hJv)
    simpa [v, hv] using hsum.symm
  have hTinj : Function.Injective T := by
    intro d e hde
    exact sub_eq_zero.mp (hzero (d - e) (by simpa [map_sub, hde]))
  obtain ⟨K, hKpos, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz T).mp hTinj
  let Kℝ : ℝ := K
  have hKℝpos : 0 < Kℝ := by exact_mod_cast hKpos
  let ε : ℝ := 1 / (2 * Kℝ)
  have hεpos : 0 < ε := by positivity
  have hxstarU : xstar ∈ U := mem_of_mem_nhds hU
  have hsmall : ∀ i, ∀ᶠ x in nhds xstar,
      ‖ψ i x - fderiv ℝ (ψ i) xstar (x - xstar)‖ ≤ ε * ‖x - xstar‖ := by
    intro i
    have hdiff : DifferentiableAt ℝ (ψ i) xstar :=
      ((hψ i).contDiffAt hU).differentiableAt_one
    have hlittle := hdiff.hasFDerivAt.isLittleO
    convert hlittle.def hεpos using 1
    ext x
    simp [hroot i]
  have hsmall_all : ∀ᶠ x in nhds xstar, ∀ i,
      ‖ψ i x - fderiv ℝ (ψ i) xstar (x - xstar)‖ ≤ ε * ‖x - xstar‖ := by
    exact Filter.eventually_all.mpr hsmall
  rcases (Filter.eventually_iff_exists_mem).mp hsmall_all with ⟨V, hV, hVbound⟩
  refine ⟨V, hV, 2 * Kℝ, by positivity, ?_⟩
  intro x hx
  let d := x - xstar
  have hmax_nonneg : 0 ≤ maxResidual ψ x := by
    unfold maxResidual
    exact Real.iSup_nonneg (fun i => abs_nonneg _)
  have hTbound : ‖T d‖ ≤ maxResidual ψ x + ε * ‖d‖ := by
    rw [pi_norm_le_iff_of_nonneg
      (add_nonneg hmax_nonneg (mul_nonneg hεpos.le (norm_nonneg _)))]
    intro i
    have hi := hVbound x hx i
    have hcorr : ‖ψ i x‖ ≤ maxResidual ψ x := by
      simpa [maxResidual, abs_of_nonneg (norm_nonneg _)] using
        (Finite.le_ciSup (fun j => |ψ j x|) i)
    calc
      ‖T d i‖ = ‖fderiv ℝ (ψ i) xstar d‖ := rfl
      _ ≤ ‖ψ i x - fderiv ℝ (ψ i) xstar d‖ + ‖ψ i x‖ := by
            have h := (abs_le.mp (abs_norm_sub_norm_le
              (fderiv ℝ (ψ i) xstar d) (ψ i x))).2
            rw [norm_sub_rev (fderiv ℝ (ψ i) xstar d) (ψ i x)] at h
            linarith [norm_nonneg (ψ i x)]
      _ ≤ ε * ‖d‖ + maxResidual ψ x := add_le_add hi hcorr
      _ = maxResidual ψ x + ε * ‖d‖ := by ring
  have hanti0 : ‖d‖ ≤ Kℝ * ‖T d‖ := by
    simpa [Kℝ, d, dist_eq_norm] using hanti.le_mul_dist d 0
  have hmul : Kℝ * (maxResidual ψ x + ε * ‖d‖) = Kℝ * maxResidual ψ x + ‖d‖ / 2 := by
    simp [ε, hKℝpos.ne']
    field_simp [hKℝpos.ne']
  have hhalf : ‖d‖ / 2 ≤ Kℝ * maxResidual ψ x := by
    have := hanti0.trans (mul_le_mul_of_nonneg_left hTbound hKℝpos.le)
    linarith
  have hfinal : ‖d‖ ≤ 2 * Kℝ * maxResidual ψ x := by
    nlinarith
  simpa [d] using hfinal
