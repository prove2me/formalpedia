-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.kunf.setIntegral_fd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:52.38819+00:00
-- url     : https://prove2.me/submissions/47a9ddfc-f170-46fe-b53b-d75c9bfca51b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] {lam : Measure V} [lam.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ]
  {𝓖 : Set V}
omit [SecondCountableTopology V]
namespace PositivityTheory.SiegelWeilFormula.kunf
theorem _root_.solution (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (g : V → ℂ)
    (hg : ∀ (ν : Λ) β, g (β + ν) = g β) (β₀ : V) (c : ℂ) (hc : c ≠ 1) (hβ₀ : ∀ β, g (β + β₀) = c * g β) :
    ∫ β in 𝓖, g β ∂lam = 0 := by
  have h1 : IsAddFundamentalDomain Λ ((-β₀) +ᵥ 𝓖) lam := h𝓖.vadd_of_comm (-β₀)
  have h2 : ∫ β in 𝓖, g β ∂lam = ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam := by
    rw [← (measurePreserving_vadd β₀ lam).setIntegral_image_emb (measurableEmbedding_const_vadd β₀)]
    congr 1
    rw [Set.image_vadd, vadd_vadd, add_neg_cancel, zero_vadd]
  have h3 : ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam = c * ∫ β in 𝓖, g β ∂lam := by
    have e : (fun x => g (β₀ +ᵥ x)) = fun x => c * g x := funext fun x => by
      rw [vadd_eq_add, add_comm, hβ₀]
    rw [e, h1.setIntegral_eq h𝓖 (fun ν x => by rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hg]),
      integral_const_mul]
  have h4 : (1 - c) * ∫ β in 𝓖, g β ∂lam = 0 := by
    rw [sub_mul, one_mul, ← h3, ← h2, sub_self]
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hc))
end PositivityTheory.SiegelWeilFormula.kunf
