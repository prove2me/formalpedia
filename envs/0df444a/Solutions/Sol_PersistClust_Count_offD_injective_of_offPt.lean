-- Prove2me | solution 1 for PersistClust.Count.offD_injective_of_offPt
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T13:24:34.664795+00:00
-- url     : https://prove2.me/submissions/7d060008-03d5-4b52-beed-1dc9f19e0ced

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

/-- Copy-record injectivity: two offD copy-records with equal offPt
projections are equal, so offPt-injectivity of a family of copy-records
F implies injectivity of F itself. -/
theorem solution {D : EReal × EReal → ℕ∞} {A : Type*}
    (F : A → offD D) (h : Function.Injective (fun a => offPt (F a))) : Function.Injective F :=
  fun a₁ a₂ heq => h (congrArg offPt heq)
