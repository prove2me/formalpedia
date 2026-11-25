-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.card_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:16:07.308871+00:00
-- url     : https://prove2.me/submissions/c15b1d42-bac2-4aaa-8e0f-c37f80398e14

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (D e : ℕ) :
    Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D := by
  rw [Nat.card_congr (degreeLeEquivAntidiag D e), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    show D + 1 + e - 1 = D + e by omega, ← Nat.choose_symm_add, add_comm]
end ReciprocityTheory.MultiplicativeHeights
