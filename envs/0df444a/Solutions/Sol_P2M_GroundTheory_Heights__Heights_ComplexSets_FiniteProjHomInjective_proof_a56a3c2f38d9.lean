-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjHomInjective_proof_a56a3c2f38d9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:21.172214+00:00
-- url     : https://prove2.me/submissions/bdf96890-482f-4cf6-a550-dcb7ff47b304

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ringKrullDim_mvPolynomial_complex_a419de08b2fb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.ComplexSets
namespace FiniteProjHomInjective
theorem _root_.solution : FiniteProjHomInjective.Statement := by
  intro n d J A _ hdim hfin
  set f : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J := (projHom J A).toRingHom with hf
  have hinj : Function.Injective f := by
    by_contra hni
    rw [injective_iff_map_eq_zero] at hni
    push Not at hni
    obtain ⟨p, hp0, hp⟩ := hni
    let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toAlgebra
    have hint : f.IsIntegral := hfin.to_isIntegral

    let g : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ J) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin d) ℂ) (Ideal.span {p}) := fun q =>
      ⟨PrimeSpectrum.comap f q, by
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
          Set.singleton_subset_iff]
        show f p ∈ q.asIdeal
        rw [hp0]; exact q.asIdeal.zero_mem⟩
    have hg : StrictMono g := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap _ _) < q₂.asIdeal.comap (algebraMap _ _)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩ (hint x)
    have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
        ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ Ideal.span {p}) := by
      rw [ringKrullDim_quotient (Ideal.span {p})]
      exact Order.krullDim_le_of_strictMono g hg
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hp)
    rw [ringKrullDim_mvPolynomial_complex] at h2
    rw [hdim] at h1
    have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := le_trans (by gcongr) h2
    have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
    have h5 : d + 1 ≤ d := by exact_mod_cast h4
    omega
  exact fun a b h => hinj h
end FiniteProjHomInjective
end GroundTheory.Heights₂.Heights.ComplexSets
