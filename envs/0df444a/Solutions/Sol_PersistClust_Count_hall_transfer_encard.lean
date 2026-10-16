-- Prove2me | solution 1 for PersistClust.Count.hall_transfer_encard
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-16T04:15:53.134429+00:00
-- url     : https://prove2.me/submissions/03524536-38ed-4c79-8f4c-cf740cf521b8

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Hall's inequality transfers along injective relabellings with matching neighbourhoods. -/
theorem solution {A B C T : Type} (vA : A → C) (vB : B → C)
    (hA : Function.Injective vA) (hB : Function.Injective vB)
    (GA : A → Set T) (GB : B → Set T) (sA : Set A) (sB : Set B)
    (himg : vA '' sA = vB '' sB) (hG : ∀ a b, vA a = vB b → GA a = GB b)
    (h : sB.encard ≤ (⋃ b ∈ sB, GB b).encard) :
    sA.encard ≤ (⋃ a ∈ sA, GA a).encard := by
  have h1 : sA.encard = sB.encard := by
    rw [← hA.encard_image, ← hB.encard_image, himg]
  have h2 : (⋃ a ∈ sA, GA a) = ⋃ b ∈ sB, GB b := by
    ext t
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨a, ha, ht⟩
      obtain ⟨b, hb, hba⟩ : vA a ∈ vB '' sB := himg ▸ ⟨a, ha, rfl⟩
      exact ⟨b, hb, (hG a b hba.symm) ▸ ht⟩
    · rintro ⟨b, hb, ht⟩
      obtain ⟨a, ha, hab⟩ : vB b ∈ vA '' sA := himg ▸ ⟨b, hb, rfl⟩
      exact ⟨a, ha, (hG a b hab).symm ▸ ht⟩
  rw [h1, h2]
  exact h
