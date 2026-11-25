-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:25:53.281185+00:00
-- url     : https://prove2.me/submissions/06ee7d9b-ae6b-497f-9910-dba7b2d2fe46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_pack
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PackingSeparation_sep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_card_CP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
theorem _root_.solution (R : ℝ) (hR : 0 ≤ R) :
    {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E) := by
  set T := {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}
  have hT : T.Finite := by
    have h := Embeddings.finite_of_norm_le E ℂ R
    refine (h.preimage (Set.injOn_of_injective RingOfIntegers.coe_injective)).subset ?_
    intro α hα
    exact ⟨α.isIntegral_coe, hα⟩
  refine ⟨hT, ?_⟩
  let p : 𝓞 E → (CP E → ℂ) := fun α w => w.1.embedding (α : E)
  have hpinj : Function.Injective p := by
    intro α β h
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have := congrFun h ⟨w0, IsTotallyComplex.isComplex w0⟩
    exact RingOfIntegers.coe_injective (w0.embedding.injective this)
  have hd : finrank ℝ (CP E → ℂ) = 2 * fdeg E := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, (card_CP (E := E)).1, mul_comm]
  have hcard : T.ncard = (hT.toFinset.image p).card := by
    rw [Finset.card_image_of_injective _ hpinj, Set.ncard_eq_toFinset_card _ hT]
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have : Nonempty (CP E) := ⟨⟨w0, IsTotallyComplex.isComplex w0⟩⟩
  rw [hcard, ← hd]
  refine pack volume _ R hR ?_ ?_
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hq
    rw [Set.Finite.mem_toFinset] at hα
    exact (pi_norm_le_iff_of_nonneg hR).mpr fun w => hα _
  · intro q hq q' hq' hne
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hq'
    have hαβ : α - β ≠ 0 := sub_ne_zero.mpr fun h => hne (by rw [h])
    obtain ⟨w, hw⟩ := sep (α - β) hαβ
    calc (1 : ℝ) ≤ ‖w.1.embedding ((α - β : 𝓞 E) : E)‖ := hw
      _ = ‖(p α - p β) w‖ := by simp [p]
      _ ≤ ‖p α - p β‖ := norm_le_pi_norm _ w
end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
