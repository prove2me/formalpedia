-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.sncInducedAtlas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:46.428409+00:00
-- url     : https://prove2.me/submissions/f8807647-6f57-4ea0-8899-ff3921d1c1ea

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_SNCAtlas
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_isClosed_divisorComponent
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_slice_trans
import Theorems.Thm_ReciprocityTheory_AnForm_M_SimpleNormalCrossingSliceCharts_slice_holo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Topology Filter Set
open scoped ContDiff
noncomputable section
open SimpleNormalCrossingSliceCharts
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : SNCInducedAtlasStatement := by
  unfold SNCInducedAtlasStatement
  intro e X _ _ _ A L s r m W _ _ h k
  have hK : IsCompact (W k) := (isClosed_divisorComponent A L s m W h k).isCompact
  unfold IsSNC at h
  choose ψ hψ using h
  have h' : ∀ x, ∃ σ : Fin r → Option (Fin (e + 1)),
      ∀ k', W k' ∩ (ψ x).source = {y ∈ (ψ x).source | ∃ i, σ k' = some i ∧ (ψ x) y i = 0} := by
    intro x
    obtain ⟨-, -, -, σ, -, hW, -⟩ := hψ x
    exact ⟨σ, hW⟩
  choose σ hσ using h'
  have hι : ∀ x : W k, ∃ i, σ x.1 k = some i := by
    intro x
    have hm : (x : X) ∈ W k ∩ (ψ x.1).source := ⟨x.2, (hψ x.1).2.1⟩
    rw [hσ x.1 k] at hm
    obtain ⟨i, hi, -⟩ := hm.2
    exact ⟨i, hi⟩
  choose ι hι using hι
  have hS : ∀ x : W k, ∀ y ∈ (ψ x.1).source, y ∈ W k ↔ (ψ x.1) y (ι x) = 0 := by
    intro x y hy
    constructor
    · intro hyW
      have hm : y ∈ W k ∩ (ψ x.1).source := ⟨hyW, hy⟩
      rw [hσ x.1 k] at hm
      obtain ⟨i', hi', h0⟩ := hm.2
      rw [hι x, Option.some.injEq] at hi'
      rw [hi']
      exact h0
    · intro h0
      have hm : y ∈ {y ∈ (ψ x.1).source | ∃ i', σ x.1 k = some i' ∧ (ψ x.1) y i' = 0} :=
        ⟨hy, ι x, hι x, h0⟩
      rw [← hσ x.1 k] at hm
      exact hm.1
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : W k => (ψ x.1).source)
    (fun x => (ψ x.1).open_source) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, (hψ y).2.1⟩)
  refine ⟨{ n := t.card
            chart := fun j => sliceChart (ψ (t.equivFin.symm j).1.1) (ι (t.equivFin.symm j).1) (W k)
              (hS (t.equivFin.symm j).1) (t.equivFin.symm j).1
            cover := ?_
            holo := fun j j' => slice_trans A (W k) (hS (t.equivFin.symm j).1)
              (hS (t.equivFin.symm j').1) (t.equivFin.symm j).1 (t.equivFin.symm j').1
              (hψ (t.equivFin.symm j).1.1).1 (hψ (t.equivFin.symm j').1.1).1 }, ?_⟩
  · intro y
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht y.2)
    refine ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    show (y : X) ∈ (ψ (t.equivFin.symm (t.equivFin ⟨x, hxt⟩)).1.1).source
    rw [Equiv.symm_apply_apply]
    exact hyx
  · unfold HoloMap
    refine ⟨continuous_subtype_val, fun j k' => ?_⟩
    exact slice_holo A (W k) (hS (t.equivFin.symm j).1) (t.equivFin.symm j).1
      (hψ (t.equivFin.symm j).1.1).1 k'
end ReciprocityTheory.AnForm.M
