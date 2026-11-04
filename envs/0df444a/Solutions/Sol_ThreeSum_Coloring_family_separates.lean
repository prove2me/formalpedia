-- Prove2me | solution 1 for ThreeSum.Coloring.family_separates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:35.372385+00:00
-- url     : https://prove2.me/submissions/902381b6-5d67-4ddb-9062-f763a88edceb

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
import Theorems.Thm_ThreeSum_Coloring_exists_separating_parameter
import Theorems.Thm_ThreeSum_Coloring_indexWord_injective

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ c ∈ family n, c i = 0 ∧ c j = 1 ∧ c k = 2 := by
  obtain ⟨p, hp⟩ := exists_separating_parameter
    (fun h => hij (indexWord_injective n h)) (fun h => hik (indexWord_injective n h))
    (fun h => hjk (indexWord_injective n h))
  exact ⟨colorIndex p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hp⟩
end ThreeSum.Coloring
