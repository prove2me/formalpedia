-- Prove2me | solution 1 for P2M_DedekindZeta_Theta_traceForm_int_iff_eEmb__mem_dualLattice_db62551e6e8f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:26.92485+00:00
-- url     : https://prove2.me/submissions/8a406c5c-b620-45d5-881c-eaa38d15c950

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_traceForm_mixedEmbedding
import Theorems.Thm_DedekindZeta_Theta_traceForm_mixedEmbedding_int_iff_mem_dualIdeal
import Theorems.Thm_P2M_DedekindZeta_Theta_eEmb__mem_idealLattice_iff_6d901df151c6
import Theorems.Thm_DedekindZeta_Theta_traceForm_sub_left
import Theorems.Thm_DedekindZeta_Theta_traceForm_natCast_mul
import Theorems.Thm_DedekindZeta_Theta_traceForm_eq_zero_of_forall_integralBasis

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (η : mixedSpace K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ, traceForm K η a = (k : ℝ)) ↔
      eEmbℝ K η ∈ idealLattice K (dualIdeal K 𝔞) := by
  rw [eEmbℝ_mem_idealLattice_iff]
  constructor
  · intro h
    classical
    -- A nonzero rational integer `m ∈ 𝔞` (the absolute norm), so that
    -- `m · (integral basis) ⊆ 𝔞` and we can extract rational pairings.
    set m : ℕ := Ideal.absNorm 𝔞 with hm
    have hm0 : (m : ℝ) ≠ 0 := by
      have : 𝔞 ≠ ⊥ := hne
      exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr this
    have hmem : (m : 𝓞 K) ∈ 𝔞 := Ideal.absNorm_mem 𝔞
    -- Rationality: `T(η, integralBasis i) = algebraMap (q i)` for `q i ∈ ℚ`.
    have hq : ∀ i, ∃ q : ℚ, traceForm K η (integralBasis K i) = algebraMap ℚ ℝ q := by
      intro i
      have hmemf : ((m : K) * integralBasis K i) ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
        have he : ((m : K) * integralBasis K i)
            = algebraMap (𝓞 K) K ((m : 𝓞 K) * RingOfIntegers.basis K i) := by
          rw [map_mul, integralBasis_apply, map_natCast]
        rw [he]
        exact FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰
          (Ideal.mul_mem_right (RingOfIntegers.basis K i) 𝔞 hmem)
      obtain ⟨k, hk⟩ := h _ hmemf
      refine ⟨(k : ℚ) / (m : ℚ), ?_⟩
      rw [traceForm_natCast_mul] at hk
      have : traceForm K η (integralBasis K i) = (k : ℝ) / (m : ℝ) := by
        field_simp at hk ⊢; linarith [hk]
      rw [this, map_div₀, map_intCast, map_natCast]
    choose q hqeq using hq
    -- Construct `b ∈ K` with the prescribed pairings via the trace-dual basis.
    set b : K := ∑ i, q i • (integralBasis K).traceDual i with hb
    have htr : ∀ j, Algebra.trace ℚ K (b * integralBasis K j) = q j := by
      intro j
      rw [hb, Finset.sum_mul, map_sum]
      have : ∀ i, Algebra.trace ℚ K ((q i • (integralBasis K).traceDual i) * integralBasis K j)
          = q i • (if j = i then (1 : ℚ) else 0) := by
        intro i
        rw [smul_mul_assoc, map_smul, (integralBasis K).trace_traceDual_mul]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j q]
      simp
    -- `mixedEmbedding K b` and `η` have equal trace pairings against the basis.
    have hpair : ∀ j, traceForm K (mixedEmbedding K b) (integralBasis K j)
        = traceForm K η (integralBasis K j) := by
      intro j
      rw [traceForm_mixedEmbedding, ← Algebra.traceForm_apply, Algebra.traceForm_apply,
        htr j, hqeq j]
    -- Nondegeneracy forces `mixedEmbedding K b = η`.
    have hbη : mixedEmbedding K b = η := by
      have := traceForm_eq_zero_of_forall_integralBasis K (mixedEmbedding K b - η)
        (fun j => by rw [traceForm_sub_left, hpair j, sub_self])
      rwa [sub_eq_zero] at this
    refine ⟨b, ?_, hbη⟩
    -- `b ∈ dualIdeal K 𝔞` from the integrality hypothesis transported through `hbη`.
    refine (traceForm_mixedEmbedding_int_iff_mem_dualIdeal K 𝔞 hne b).mp ?_
    intro a ha
    rw [hbη]
    exact h a ha
  · rintro ⟨b, hb, rfl⟩
    exact (traceForm_mixedEmbedding_int_iff_mem_dualIdeal K 𝔞 hne b).mpr hb
end DedekindZeta.Theta
