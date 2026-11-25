-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_exists_point_of_evalYT_eq_zero_7a5ea48e4f32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:51.909593+00:00
-- url     : https://prove2.me/submissions/5a4c8509-60d0-442a-9ee6-0fde2e9db9a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen

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
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin d → MvPolynomial (Fin n) ℂ) (hfin : ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).Finite)
    (L : MvPolynomial (Fin n) ℂ) (μ : Polynomial (MvPolynomial (Fin d) ℂ))
    (hdvd : ∀ F, Polynomial.eval₂ ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom
      (Ideal.Quotient.mk J L) F = 0 → μ ∣ F)
    {y : Fin d → ℂ} {t : ℂ} (hyt : evalYT μ y t = 0) :
    ∃ z ∈ zeroLocus J, (fun i => eval z (p i)) = y ∧ eval z L = t := by
  classical
  set f := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom with hf
  let g : Polynomial (MvPolynomial (Fin d) ℂ) →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    Polynomial.eval₂RingHom f (Ideal.Quotient.mk J L)
  let e : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := Polynomial.eval₂RingHom (MvPolynomial.eval y) t
  have he : Function.Surjective e := fun c => ⟨Polynomial.C (MvPolynomial.C c), by simp [e]⟩
  have hPmax : (RingHom.ker e).IsMaximal := RingHom.ker_isMaximal_of_surjective e he
  have hgC : g.comp Polynomial.C = f := RingHom.ext fun a => by simp [g]
  have hfint : f.IsIntegral := RingHom.IsIntegral.of_finite hfin
  have hgint : g.IsIntegral := RingHom.IsIntegral.tower_top Polynomial.C g (hgC ▸ hfint)
  let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := g.toAlgebra
  have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨hgint⟩
  have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker e := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    obtain ⟨H, rfl⟩ := hdvd F hF
    have hμ : e μ = 0 := by simpa [e, evalYT, Polynomial.eval_map] using hyt
    rw [map_mul, hμ, zero_mul]
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker e) hker
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have key : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval z q = 0 := by
    intro q hq
    have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
    rw [hz, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval] at hq'
    exact hq'
  have key2 : ∀ F, e F = 0 → g F ∈ Q := by
    intro F hF
    have hF' : F ∈ Q.comap (algebraMap _ _) := by rw [hQP]; exact hF
    exact hF'
  refine ⟨z, fun q hq => key q ?_, ?_, ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]
    exact Q.zero_mem
  · funext i
    have h1 := key2 (Polynomial.C (X i - C (y i))) (by simp [e])
    have h2 : g (Polynomial.C (X i - C (y i))) = Ideal.Quotient.mk J (p i - C (y i)) := by
      simp [g, f]
      rfl
    rw [h2] at h1
    have h3 := key _ h1
    simpa [sub_eq_zero] using h3
  · have h1 := key2 (Polynomial.X - Polynomial.C (C t)) (by simp [e])
    have h2 : g (Polynomial.X - Polynomial.C (C t)) = Ideal.Quotient.mk J (L - C t) := by
      simp [g, f]
      rfl
    rw [h2] at h1
    have h3 := key _ h1
    simpa [sub_eq_zero] using h3
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen
