-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:36.472922+00:00
-- url     : https://prove2.me/submissions/e74498bd-dded-45cb-89da-74acabbc7624

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
variable {R : Type} [CommRing R]
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution {S S' : Subgroup G} (h : S = S') (mS : MeasurableSpace S) (hm : mS = borel S) (x : @Measure S mS) :
    ∃ x' : Measure S', (@Measure.IsHaarMeasure _ _ _ mS x → x'.IsHaarMeasure) ∧
      (∀ U : Set G, x' {y | y.1 ∈ U} = x {y | y.1 ∈ U}) ∧ ∀ f : G → ℂ,
        (Integrable (fun y : S' => f y) x' ↔ @Integrable _ _ _ _ mS (fun y : S => f y) x) ∧
          ∫ y : S', f y ∂x' = @integral _ _ _ _ mS x fun y : S => f y := by
  subst h
  have : mS = Subtype.instMeasurableSpace := hm.trans (@BorelSpace.measurable_eq S _ Subtype.instMeasurableSpace (Subtype.borelSpace _)).symm
  subst this
  exact ⟨x, id, fun _ => rfl, fun _ => ⟨Iff.rfl, rfl⟩⟩
end PositivityTheory.ThKG.Fub
