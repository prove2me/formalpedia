-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.idem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:23.136751+00:00
-- url     : https://prove2.me/submissions/e76c08e5-ebd5-43d6-ba35-e22bbe64f53c

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_WeilRepresentations_ZariskiDensity_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by
  by_contra hne
  have hne1 : Ideal.span {1 - f} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    apply hne
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    exact htop.mul_left_eq_zero.1 h0
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne1
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (H ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)
  let e : K ≃ₐ[K] H ⧸ M := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb
  let x : H →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)
  have h1 : Ideal.Quotient.mk M f = 1 := by
    have hmem : 1 - f ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : Ideal.Quotient.mk M (1 - f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  have hx1 : x f = 1 := by
    change e.symm (Ideal.Quotient.mkₐ K M f) = 1
    rw [Ideal.Quotient.mkₐ_eq_mk, h1, map_one]
  have hx := h x
  rw [hx1] at hx
  exact one_ne_zero hx
end PositivityTheory.PrwZar.Qi
