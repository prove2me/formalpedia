-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.bijective_H_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:14.855876+00:00
-- url     : https://prove2.me/submissions/448a1c8b-341b-410a-b92b-5cf941e5c1d1

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
import Theorems.Thm_ReciprocityTheory_Coh_admissibility_holds
import Theorems.Thm_ReciprocityTheory_Coh_lES_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B C : TRep ℤ G}
    {i : Pair A B} {q : Pair B C} (h : admitted i q) (n : ℕ) (h1 : Subsingleton (A.H n))
    (h2 : Subsingleton (A.H (n + 1))) : Bijective (q.hom.H n) := by
  have hs := admissibility_holds ℤ G _ _ _ _ _ h
  obtain ⟨⟨δ, -, hl⟩, -⟩ := lES_holds ℤ _ _ _ _ _ hs
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hl.exB n x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (hl.exC n y).1 (Subsingleton.elim _ _)
end ReciprocityTheory.DiscreteGroups.LocalClassField
