-- Prove2me | solution 1 for P2M_GlobalTheory_BK_Descent_Y__le_Y_23b05d78c6fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:58:35.639035+00:00
-- url     : https://prove2.me/submissions/a9755b78-b612-4c67-9f46-fd8d551085c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Descent_act_X_pow_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
omit [NeZero e]
namespace GlobalTheory.BK.Descent
theorem _root_.solution (η : ℕ) : Δ.Y' η ≤ Δ.Y η := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨(P.EM η).smul_mem (uIn (A O K) ^ e) hy.1,
    fun g => (Δ.act_X_pow_smul g y).trans (congrArg _ (hy.2 g))⟩
end GlobalTheory.BK.Descent
