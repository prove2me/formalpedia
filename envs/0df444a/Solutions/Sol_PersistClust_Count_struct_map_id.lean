-- Prove2me | solution 1 for PersistClust.Count.struct_map_id
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T09:55:42.537479+00:00
-- url     : https://prove2.me/submissions/4260fef3-b35e-44ae-8283-428b263e0ac7

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem solution {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (t : ℝ) (C : comps stage J t) :
    structMap hLaw le_rfl C = C :=
  Subtype.ext (compRep_spec stage J t C).2
