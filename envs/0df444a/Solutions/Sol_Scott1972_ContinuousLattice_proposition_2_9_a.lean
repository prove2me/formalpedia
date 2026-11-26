-- Prove2me | solution 1 for Scott1972.ContinuousLattice.proposition_2_9_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:30:15.89353+00:00
-- url     : https://prove2.me/submissions/52cc3ff5-4ddd-42ba-9196-2925005d8207

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_sSup_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
namespace Scott1972.ContinuousLattice
theorem _root_.solution {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, IsContinuousLattice (E i)) : IsContinuousLattice (∀ i, E i) := by
  classical
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  rw [Pi.le_def]
  intro i
  rw [← (hE i).sSup_wayBelow (y i)]
  apply sSup_le
  intro a ha
  set e : (∀ j, E j) := Function.update (⊥ : ∀ j, E j) i a with he
  have hei : e i = a := by rw [he]; exact Function.update_self i a _
  have hcyl : e ≪ y := by
    obtain ⟨U, hU, hyiU, hUsub⟩ := ha
    refine ⟨{z : ∀ j, E j | z i ∈ U}, ?_, hyiU, ?_⟩
    · refine ⟨fun z w hzw hz => hU.1 (hzw i) hz, fun S hSne hSdir hmem => ?_⟩
      rw [Set.mem_setOf_eq, sSup_apply_eq_sSup_image] at hmem
      have hdir' : DirectedOn (· ≤ ·) (Function.eval i '' S) := by
        rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
        obtain ⟨h, hhS, hfh, hgh⟩ := hSdir f hf g hg
        exact ⟨Function.eval i h, ⟨h, hhS, rfl⟩, hfh i, hgh i⟩
      obtain ⟨t, htimg, htU⟩ := hU.2 (hSne.image _) hdir' hmem
      obtain ⟨f, hfS, rfl⟩ := htimg
      exact ⟨f, hfS, htU⟩
    · intro z hz
      rw [Set.mem_Ici, Pi.le_def]
      intro j
      rcases eq_or_ne j i with rfl | hji
      · rw [hei]; exact Set.mem_Ici.1 (hUsub hz)
      · rw [he, Function.update_of_ne hji]; exact bot_le
  have hle : e i ≤ b i := (hb hcyl) i
  rw [hei] at hle
  exact hle
end Scott1972.ContinuousLattice
