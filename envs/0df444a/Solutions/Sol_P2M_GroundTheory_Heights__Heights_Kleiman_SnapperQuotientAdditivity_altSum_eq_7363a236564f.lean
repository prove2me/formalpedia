-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_altSum_eq_7363a236564f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:18.186575+00:00
-- url     : https://prove2.me/submissions/d8d1210d-38d1-495c-84a7-c4b3295055cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
theorem _root_.solution {k : Type u} [Field k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, FiniteDimensional k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, FiniteDimensional k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, FiniteDimensional k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (h0 : Function.Injective (f 0)) (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i)) (hδf : ∀ i, Function.Exact (δ i) (f (i + 1))) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) =
      (-1 : ℤ) ^ M * Module.finrank k (LinearMap.range (δ M)) := by
  have hB : ∀ i, (Module.finrank k (B i) : ℤ) =
      Module.finrank k (LinearMap.range (f i)) + Module.finrank k (LinearMap.range (g i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (g i), LinearMap.exact_iff.1 (hfg i)]
    push_cast; ring
  have hC : ∀ i, (Module.finrank k (C i) : ℤ) =
      Module.finrank k (LinearMap.range (g i)) + Module.finrank k (LinearMap.range (δ i)) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (δ i), LinearMap.exact_iff.1 (hgδ i)]
    push_cast; ring
  have hA : ∀ i, (Module.finrank k (A (i + 1)) : ℤ) =
      Module.finrank k (LinearMap.range (δ i)) + Module.finrank k (LinearMap.range (f (i + 1))) := by
    intro i
    rw [← LinearMap.finrank_range_add_finrank_ker (f (i + 1)), LinearMap.exact_iff.1 (hδf i)]
    push_cast; ring
  have hA0 : (Module.finrank k (A 0) : ℤ) = Module.finrank k (LinearMap.range (f 0)) := by
    rw [← LinearMap.finrank_range_add_finrank_ker (f 0), LinearMap.ker_eq_bot.2 h0, finrank_bot]
    simp
  induction M with
  | zero => rw [Finset.sum_range_one, hA0, hB 0, hC 0]; ring
  | succ M ih => rw [Finset.sum_range_succ, ih, hA M, hB (M + 1), hC (M + 1)]; ring
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
