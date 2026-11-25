-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pu_pow_37879c7c4c96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:41.561578+00:00
-- url     : https://prove2.me/submissions/14f39921-44ab-4c76-bc43-fde88d02c2e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution {K : ℕ} (f c : Fin K → Ω) (hf : ∀ l, f l ∈ chartRing ℤ x i)
    (hc : ∀ l, c l ∈ chartRing ℤ x i) (hs : ∑ l, c l * f l = 1) (T : ℕ) :
    ∃ d : Fin K → Ω, (∀ l, d l ∈ chartRing ℤ x i) ∧ ∑ l, d l * f l ^ T = 1 := by
  let F : Fin K → chartRing ℤ x i := fun l => ⟨f l, hf l⟩
  have h1 : Ideal.span (Set.range F) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, Subtype.ext ?_⟩
    simpa [F] using hs
  have h2 := Ideal.span_pow_eq_top _ h1 T
  rw [← Set.range_comp] at h2
  have h3 : (1 : chartRing ℤ x i) ∈ Ideal.span (Set.range ((fun y => y ^ T) ∘ F)) := by
    rw [h2]; trivial
  obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.1 h3
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [F] using this
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
