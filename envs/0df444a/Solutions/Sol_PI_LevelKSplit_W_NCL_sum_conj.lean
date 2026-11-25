-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.sum_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:48:46.173717+00:00
-- url     : https://prove2.me/submissions/b3dc7e20-2065-410a-8d5a-cd17b51a8cf3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (σ : A →+* A) (U W : Fin r → Fin r → A) (α β : Fin r → A)
    (h : ∀ b c, ∑ a, σ (U a b) * W a c = if b = c then 1 else 0) :
    ∑ a, σ (∑ b, U a b * α b) * ∑ c, W a c * β c = ∑ b, σ (α b) * β b := by
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ c, ∑ a, ∑ b, σ (U a b) * σ (α b) * (W a c * β c)
      = ∑ c, ∑ b, (∑ a, σ (U a b) * W a c) * (σ (α b) * β c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ b, σ (α b) * β b := by
        rw [Finset.sum_comm]
        simp [h]
end PI.LevelKSplit.W.NCL
