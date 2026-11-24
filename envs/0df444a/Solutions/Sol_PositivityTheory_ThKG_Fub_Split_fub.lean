-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.Split.fub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:27.627879+00:00
-- url     : https://prove2.me/submissions/73068727-6dc9-4703-b403-0e238d10008b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {S A B : Subgroup G} {p q : G →* G}
namespace PositivityTheory.ThKG.Fub
namespace Split
theorem _root_.solution (h : Split S A B p q) (μ : Measure S) (α : Measure A) (β : Measure B) [μ.IsHaarMeasure] [α.IsHaarMeasure]
    [β.IsHaarMeasure] : ∃ c : ℝ≥0, c ≠ 0 ∧
      (∀ f g : G → ℂ, Integrable (fun a : A => f a) α → Integrable (fun b : B => g b) β →
        Integrable (fun x : S => f (p x) * g (q x)) μ ∧
          ∫ x : S, f (p x) * g (q x) ∂μ = c * ((∫ a : A, f a ∂α) * ∫ b : B, g b ∂β)) ∧
      ∀ U : Set G, MeasurableSet U → (∀ g ∈ S, g ∈ U ↔ p g ∈ U ∧ q g ∈ U) →
        μ {x | x.1 ∈ U} = c * (α {x | x.1 ∈ U} * β {x | x.1 ∈ U}) := by
  haveI : LocallyCompactSpace A := h.cA.locallyCompactSpace
  haveI : LocallyCompactSpace B := h.cB.locallyCompactSpace
  haveI : LocallyCompactSpace S := h.cS.locallyCompactSpace
  have hm : (μ.map h.e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ h.e
  set c := Measure.haarScalarFactor (μ.map h.e) (α.prod β) with hc
  have he : μ.map h.e = c • α.prod β := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have hme : MeasurableEmbedding h.e := h.e.toHomeomorph.measurableEmbedding
  refine ⟨c, hc0, fun f g hf hg => ?_, fun U hU hh => ?_⟩
  · have h1 : Integrable (fun x : A × B => f x.1 * g x.2) (μ.map h.e) := by
      rw [he]; exact (hf.mul_prod hg).smul_measure_nnreal
    refine ⟨(hme.integrable_map_iff.1 h1 :), ?_⟩
    have h2 := hme.integral_map (μ := μ) (fun x : A × B => f x.1 * g x.2)
    rw [he, integral_smul_nnreal_measure, integral_prod_mul (fun a : A => f a) (fun b : B => g b)] at h2
    refine Eq.trans ?_ (h2.symm.trans ?_)
    · rfl
    · simp [NNReal.smul_def]
  · have h2 : {x : S | x.1 ∈ U} = h.e ⁻¹' ({x : A | x.1 ∈ U} ×ˢ {x : B | x.1 ∈ U}) := Set.ext fun x => hh _ x.2
    rw [h2, ← hme.map_apply, he, Measure.smul_apply, Measure.prod_prod]
    rfl
end Split
end PositivityTheory.ThKG.Fub
