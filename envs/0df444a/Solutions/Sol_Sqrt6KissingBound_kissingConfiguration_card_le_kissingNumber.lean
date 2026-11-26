-- Prove2me | solution 1 for Sqrt6KissingBound.kissingConfiguration_card_le_kissingNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:39:31.029855+00:00
-- url     : https://prove2.me/submissions/1322b421-2295-4944-a198-44cc35341b34

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_realizableKissingCard_le_kissingNumber

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n)
    (X : Finset (EuclideanSpace ℝ (Fin n)))
    (hX : IsKissingConfiguration X) :
    X.card ≤ kissingNumber n :=
  realizableKissingCard_le_kissingNumber hn ⟨X, hX, rfl⟩
end Sqrt6KissingBound
