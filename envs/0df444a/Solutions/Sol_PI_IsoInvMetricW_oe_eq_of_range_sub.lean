-- Prove2me | solution 1 for PI.IsoInvMetricW.oe_eq_of_range_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:36.793841+00:00
-- url     : https://prove2.me/submissions/d015a4dc-469c-4688-91f5-a3736f39e3de

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution {h N : ℕ} (I J : Fin h ↪o Fin N) (hs : ∀ i, ∃ k, J k = I i) :
    I = J := by
  classical
  have h1 : Finset.univ.image I ⊆ Finset.univ.image J := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact hs i
  have h2 : Finset.univ.image I = Finset.univ.image J :=
    Finset.eq_of_subset_of_card_le h1 (by
      rw [Finset.card_image_of_injective _ J.injective,
        Finset.card_image_of_injective _ I.injective])
  apply OrderEmbedding.range_inj.mp
  have := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h2
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using this
end PI.IsoInvMetricW
