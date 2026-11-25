-- Prove2me | solution 1 for PI.VolStabW.DiscreteGroups.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:47.461401+00:00
-- url     : https://prove2.me/submissions/7f44911e-d2e7-46b5-a6e7-67c63f89b16a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabW PI.VolStabW.Glue
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]
namespace PI.VolStabW.DiscreteGroups
theorem _root_.solution (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by
  haveI : LocallyCompactSpace O := hO.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice O
  have h : ∀ k, ∃ g : C(V, ℝ), EqOn g 1 (Subtype.val '' E k) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Subtype.val '' interior (E (k + 1)) ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun k =>
    exists_continuousMap_one_of_isCompact_subset_isOpen ((E.isCompact k).image continuous_subtype_val)
      (hO.isOpenMap_subtype_val _ isOpen_interior) (image_mono (E.subset_interior_succ k))
  choose g hg1 hgc hgs hg01 using h
  have hsubO : ∀ k, tsupport (g k) ⊆ O :=
    fun k => (hgs k).trans (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  have hmono : ∀ x, Monotone fun k => g k x := by
    intro x
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases hx : x ∈ tsupport (g k)
    · obtain ⟨u, hu, rfl⟩ := hgs k hx
      rw [hg1 (k + 1) ⟨u, interior_subset hu, rfl⟩]
      exact (hg01 k _).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact (hg01 (k + 1) x).1
  refine ⟨fun k => g k, fun k => ⟨(g k).continuous, hgc k, hsubO k⟩, fun k x => hg01 k x, hmono,
    fun x => ?_⟩
  by_cases hx : x ∈ O
  · obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
    rw [indicator_of_mem hx]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      have := ENNReal.ofReal_le_ofReal (hg01 k x).2
      simpa using this
    · refine le_iSup_of_le n ?_
      have h1 : g n x = 1 := hg1 n ⟨⟨x, hx⟩, hn, rfl⟩
      show (1 : V → ℝ≥0∞) x ≤ ENNReal.ofReal (g n x)
      rw [h1]
      simp
  · rw [indicator_of_notMem hx]
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsubO _ h))]
end PI.VolStabW.DiscreteGroups
