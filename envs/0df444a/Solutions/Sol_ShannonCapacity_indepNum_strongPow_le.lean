-- Prove2me | solution 1 for ShannonCapacity.indepNum_strongPow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:19:47.728059+00:00
-- url     : https://prove2.me/submissions/105b7801-7585-4b92-865f-830025295470

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}
namespace ShannonCapacity
theorem _root_.solution [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) (k : ℕ) :
    ((strongPow G k).indepNum : ℝ) ≤ t ^ k :=
  LovaszTheta.indepNum_strongPow_le G hu hc ht0 ht k
end ShannonCapacity
