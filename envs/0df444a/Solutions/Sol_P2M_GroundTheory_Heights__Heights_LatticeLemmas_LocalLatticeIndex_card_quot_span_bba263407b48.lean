-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_card_quot_span_bba263407b48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:02:53.554349+00:00
-- url     : https://prove2.me/submissions/7a0ec57d-e337-4972-8ed0-c382b585a894

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf
import Theorems.Thm_GroundTheory_Global_natCard_residueField_adicCompletionIntegers
import Theorems.Thm_GroundTheory_Global_normalizedAbv_of_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace LocalLatticeIndex
theorem _root_.solution {a : v.adicCompletionIntegers K} (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a}) : ℝ) =
      ‖(a : v.adicCompletion K)‖⁻¹ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hne : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ≠ ⊥ := by
    rw [hϖ.maximalIdeal_eq, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  have hcard : Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {(u : v.adicCompletionIntegers K) * ϖ ^ n}) = Ideal.absNorm v.asIdeal ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne,
      Submodule.cardQuot_apply, ← GroundTheory.Global.natCard_residueField_adicCompletionIntegers v]
    rfl
  have hϖn : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
    GroundTheory.Global.normalizedAbv_of_irreducible v hϖ
  rw [hcard, Nat.cast_pow]
  push_cast
  rw [norm_mul, norm_pow, LocalLatticeIndex.norm_unit, hϖn, one_mul, inv_pow, inv_inv]
end LocalLatticeIndex
end GroundTheory.Heights₂.Heights.LatticeLemmas
