-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumOfFiltration_eventually_mixedDiff_sum_b0957ba4a222
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:44.397995+00:00
-- url     : https://prove2.me/submissions/1bb218a7-8886-4eb9-afaa-47c50e9f9b9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumOfFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration
theorem _root_.solution (h1 : MixedDiffLinear.Statement)
    (h3 : EventualValueFacts.Statement) {K : Type} {n : ℕ} (bs : Fin n → K → ℤ)
    {α : Type*} (h : α → (K → ℤ) → ℤ) (s : α → K → ℤ) :
    ∀ l : List α, (∀ p ∈ l, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (h p) m = c) →
      ∀ᶠ m in Filter.atTop,
        mixedDiff bs (fun m => (l.map fun p => h p (m - s p)).sum) m =
          (l.map fun p => eventualValue (mixedDiff bs (h p))).sum := by
  intro l
  induction l with
  | nil =>
    intro _
    have h0 : (fun m : K → ℤ => (([] : List α).map fun p => h p (m - s p)).sum) = 0 := by
      funext m
      simp
    have hz : mixedDiff bs (0 : (K → ℤ) → ℤ) = 0 := by
      have := (h1 K n bs 0 0 0 0 0).2.1
      simpa using this
    refine Filter.Eventually.of_forall fun m => ?_
    rw [h0, hz]
    simp
  | cons p l ih =>
    intro hl
    obtain ⟨c, hc⟩ := hl p List.mem_cons_self
    have hsplit : (fun m : K → ℤ => ((p :: l).map fun q => h q (m - s q)).sum) =
        shiftFn (s p) (h p) + fun m => (l.map fun q => h q (m - s q)).sum := by
      funext m
      simp [shiftFn]
    have hev := (h3 K _ c (s p)).1 hc
    have hsh := (h3 K _ c (s p)).2 hc
    filter_upwards [ih fun q hq => hl q (List.mem_cons_of_mem p hq), hsh] with m hm hm'
    rw [hsplit, (h1 K n bs (shiftFn (s p) (h p)) (fun m => (l.map fun q => h q (m - s q)).sum)
      0 (s p) 0).1, (h1 K n bs (h p) 0 0 (s p) 0).2.2.1]
    simp only [Pi.add_apply, List.map_cons, List.sum_cons]
    rw [hm', hm, hev]
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumOfFiltration
