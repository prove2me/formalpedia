-- Prove2me | solution 1 for PersistClust.Count.enat_add_sub_cancel_left
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T10:03:18.12597+00:00
-- url     : https://prove2.me/submissions/b633a082-bebb-4316-a374-c0c0e8d6f2c6

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

theorem solution {a b : ℕ∞} (hfin : a ≠ ⊤) : (a + b) - a = b := by
  cases a with
  | top => exact absurd rfl hfin
  | coe m =>
      cases b with
      | top => simp
      | coe n => exact_mod_cast Nat.add_sub_cancel_left m n
