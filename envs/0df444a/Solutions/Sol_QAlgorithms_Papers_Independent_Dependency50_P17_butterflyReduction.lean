-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P17.butterflyReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:48:20.281023+00:00
-- url     : https://prove2.me/submissions/e288c9a8-8310-4429-93a0-b87573b38e16

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.10–11, Appendix A and Figure 5: three COMP invocations, at v3,v5,v6.
u is v3's decoded sum, t5,t6 its forwarded copies, and s1,s2 the negative side
messages used at v5,v6. Outputs v5 and v6 recover b and a. The seven error events
include all three COMP decoders and the forwarding/side links. The signs follow
the displayed reconstruction equations in Figure 5; characteristic two is not assumed. -/
theorem solution {F Omega : Type*} [Field F] [Fintype F]
    [MeasurableSpace F] [MeasurableSingletonClass F] [MeasurableSpace Omega]
    {ell : ℕ} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (a b u t5 t6 s1 s2 v5 v6 : Omega → (Fin ell → F))
    (ha : Measurable a) (hb : Measurable b) (hu : Measurable u)
    (ht5 : Measurable t5) (ht6 : Measurable t6)
    (hs1 : Measurable s1) (hs2 : Measurable s2)
    (hv5 : Measurable v5) (hv6 : Measurable v6)
    (hmsg : UniformMessagePair mu a b) :
    (∀ w, u w = a w + b w → t5 w = u w → t6 w = u w →
      s1 w = -a w → s2 w = -b w →
      v5 w = t5 w + s1 w → v6 w = t6 w + s2 w →
      v5 w = b w ∧ v6 w = a w) ∧
    mu {w | v5 w ≠ b w ∨ v6 w ≠ a w} ≤
      mu {w | u w ≠ a w + b w} + mu {w | t5 w ≠ u w} + mu {w | t6 w ≠ u w} +
        mu {w | s1 w ≠ -a w} + mu {w | s2 w ≠ -b w} +
        mu {w | v5 w ≠ t5 w + s1 w} + mu {w | v6 w ≠ t6 w + s2 w}
    := by
  refine ⟨fun w h1 h2 h3 h4 h5 h6 h7 => ?_, ?_⟩
  · rw [h6, h7, h2, h3, h4, h5, h1]
    constructor <;> abel
  · calc mu {w | v5 w ≠ b w ∨ v6 w ≠ a w}
        ≤ mu ({w | u w ≠ a w + b w} ∪ {w | t5 w ≠ u w} ∪ {w | t6 w ≠ u w} ∪
            {w | s1 w ≠ -a w} ∪ {w | s2 w ≠ -b w} ∪
            {w | v5 w ≠ t5 w + s1 w} ∪ {w | v6 w ≠ t6 w + s2 w}) := by
          apply measure_mono
          intro w hw
          by_contra hc
          simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
          obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
          have hv5 : v5 w = b w := by rw [h6, h2, h4, h1]; abel
          have hv6 : v6 w = a w := by rw [h7, h3, h5, h1]; abel
          simp only [Set.mem_ofPred_eq, hv5, hv6, ne_eq, not_true_eq_false, or_self] at hw
      _ ≤ _ := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _


end

