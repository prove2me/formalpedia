-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.mem_spH_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:00.709055+00:00
-- url     : https://prove2.me/submissions/fa835887-e67c-40fa-9aee-6183423b723c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spH_exists_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hN : N ∈ spH g)
    (h : N * M = 1) : M ∈ spH g := by

  obtain ⟨y, hy, hyN⟩ := spH_exists_inv hN
  have h1 : M = y := by
    calc M = (y * N) * M := by rw [hyN, one_mul]
      _ = y * (N * M) := mul_assoc _ _ _
      _ = y := by rw [h, mul_one]
  rw [h1]
  exact hy
end ReciprocityTheory.ChartRestriction.G.Key.Chi
