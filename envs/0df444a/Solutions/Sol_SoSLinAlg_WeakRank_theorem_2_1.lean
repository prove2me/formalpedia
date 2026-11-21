-- Prove2me | solution 1 for SoSLinAlg.WeakRank.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:00:47.032409+00:00
-- url     : https://prove2.me/submissions/db635562-4cfb-4f41-84f4-02bc2c5f6d3e

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank
import Theorems.Thm_SoSLinAlg_WeakRank_upper_bound_sec_4_1
import Theorems.Thm_SoSLinAlg_WeakRank_proposition_1_10
import Theorems.Thm_SoSLinAlg_WeakRank_lower_bound_identity_sec_4_3

section
namespace SoSLinAlg.WeakRank

theorem chk_theorem_2_1 {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    SoSRefutable (WRank r A) (2 * r + 2) ∧
      ∀ D : ℕ, D ≤ 2 * r + 1 → ¬ SoSRefutable (WRank r A) D :=
  ⟨SoSLinAlg.WeakRank.upper_bound_sec_4_1 hr hrn A hA,
   fun D hD href =>
    SoSLinAlg.WeakRank.lower_bound_identity_sec_4_3 hr hrn D hD
      ((SoSLinAlg.WeakRank.proposition_1_10 hr hrn A hA D).1 href)⟩

end SoSLinAlg.WeakRank
end

theorem solution : type_of% @SoSLinAlg.WeakRank.chk_theorem_2_1 := @SoSLinAlg.WeakRank.chk_theorem_2_1
