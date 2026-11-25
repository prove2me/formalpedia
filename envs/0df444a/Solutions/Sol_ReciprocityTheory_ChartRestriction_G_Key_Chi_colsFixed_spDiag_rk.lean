-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.colsFixed_spDiag_rk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:22.961136+00:00
-- url     : https://prove2.me/submissions/1ed54fb9-0f3c-48a3-a9ff-6434a21eadc8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenCol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_inv_val

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
theorem _root_.solution {k : ℕ} {u v : Fin g → ℤ} (h : v ⬝ᵥ u = 0)
    (hu : ∀ i : Fin g, (i : ℕ) < k → u i = 0) (hv : ∀ i : Fin g, (i : ℕ) < k → v i = 0) :
    ColsFixed k (spDiag (rkU u v h)) := by
  intro i hi
  simp only [spDiag, rkU_val, rkU_inv_val]
  refine ⟨fun r => ?_, fun r => ?_⟩ <;> rcases r with r | r <;>
    simp [Matrix.vecMulVec_apply, hu i hi, hv i hi, Matrix.one_apply, eq_comm]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
