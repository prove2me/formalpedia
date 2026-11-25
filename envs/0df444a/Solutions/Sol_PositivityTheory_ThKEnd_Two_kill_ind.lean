-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.kill_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:47.665707+00:00
-- url     : https://prove2.me/submissions/f91a51b1-e5a7-45c6-ac53-dba6ece3eee2

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Dat_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution (hC : Cusp Γ n a) (hn : Continuous n) (hl : ‖l‖ < 1) (P : (G → ℂ) → (G → ℂ) → Prop)
    (h0 : ∀ φ c, Dat Γ n a lam l φ c → (∃ M, ∀ g, ‖φ g‖ ≤ M) → P φ c)
    (h1 : ∀ φ c, Dat Γ n a lam l φ c → (∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ P (conv μ η φ) (conv μ η c)) → P φ c)
    (m : ℕ) : ∀ φ c, Dat Γ n a lam l φ c → Gr a m φ → P φ c := by
  induction m with
  | zero =>
    intro φ c h hm
    obtain ⟨Ω, hΩ, hs⟩ := hC.siegel
    obtain ⟨C, hCC⟩ := hm Ω hΩ
    refine h0 φ c h ⟨C, fun g => ?_⟩
    obtain ⟨γ, a1, k, κ, a2, a3⟩ := hs g
    simpa [← a3, h.inv γ a1] using hCC k κ a2
  | succ m ih =>
    intro φ c h hm
    refine h1 φ c h fun V hV => ?_
    obtain ⟨η, a1, a2⟩ := h.step μ hC hn hl hm hV
    exact ⟨η, a1, ih _ _ (h.conv μ hC hn a1) a2⟩
end PositivityTheory.ThKEnd.Two
