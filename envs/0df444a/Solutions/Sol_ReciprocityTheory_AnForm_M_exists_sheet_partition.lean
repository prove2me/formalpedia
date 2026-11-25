-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.exists_sheet_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:06.044977+00:00
-- url     : https://prove2.me/submissions/6f153991-1661-45dd-9f77-a7c62a6b6a78

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_secondCountable
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_sheets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace Y] [T2Space Y] [CompactSpace X] [T2Space X]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} (hh : HoloMap B A h) {d : ℕ}
    {S : Set X} (hd : IsDegreeOff A B h d S) [MeasurableSpace X] [BorelSpace X] [Nonempty X] :
    ∃ (E V : ℕ → Set X) (k : ℕ → Fin A.n) (W : ℕ → Fin d → Set Y) (j : ℕ → Fin d → Fin B.n),
      (∀ m, MeasurableSet (E m)) ∧ Pairwise (Function.onFun Disjoint E) ∧
      (⋃ m, E m) = Sᶜ ∧ (∀ m, E m ⊆ V m) ∧
      ∀ m, IsOpen (V m) ∧ V m ⊆ (A.chart (k m)).source ∧ (∀ i, IsOpen (W m i)) ∧
        Pairwise (Function.onFun Disjoint (W m)) ∧ h ⁻¹' V m = ⋃ i, W m i ∧
        ∀ i, Set.BijOn h (W m i) (V m) ∧ W m i ⊆ (B.chart (j m i)).source := by
  classical
  haveI := dI_secondCountable A
  have hSc : (Sᶜ).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
    have h2 := hd.2.1
    rw [hne, interior_univ] at h2
    exact Set.univ_nonempty.ne_empty h2
  choose V0 hV0o hxV0 hV0S k0 hk0 W0 j0 hW0 hdis0 hpre0 hsh0 using
    fun x : ↥(Sᶜ) => dI_sheets hh hd (x : X) x.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V0 hV0o
  have hTne : T.Nonempty := by
    obtain ⟨x0, hx0⟩ := hSc
    have hx : (x0 : X) ∈ ⋃ i ∈ T, V0 i := by
      rw [hTU]; exact Set.mem_iUnion.2 ⟨⟨x0, hx0⟩, hxV0 _⟩
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, -⟩ := hx
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  subst hf
  rw [Set.biUnion_range] at hTU
  refine ⟨disjointed (fun m => V0 (f m)), fun m => V0 (f m), fun m => k0 (f m),
    fun m => W0 (f m), fun m => j0 (f m), ?_, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.disjointed (fun n => (hV0o (f n)).measurableSet)
  · exact disjoint_disjointed _
  · rw [iUnion_disjointed]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hx
      exact fun hxS => Set.disjoint_left.1 (hV0S (f m)) hm hxS
    · intro x hx
      have hx' : x ∈ ⋃ i, V0 i := Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV0 _⟩
      rw [← hTU] at hx'
      exact hx'
  · intro m
    first
      | exact disjointed_subset _ m
      | exact disjointed_le _ m
      | exact disjointed_subset m
  · intro m
    exact ⟨hV0o _, hk0 _, hW0 _, hdis0 _, hpre0 _, hsh0 _⟩
end ReciprocityTheory.AnForm.M
