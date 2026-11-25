-- Prove2me | solution 1 for ShannonCapacity.indepNum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:19:36.086998+00:00
-- url     : https://prove2.me/submissions/69b2cb8e-ad04-42a2-8851-072096f0ef6e

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}
namespace ShannonCapacity
theorem _root_.solution [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) :
    (G.indepNum : ℝ) ≤ t :=
  LovaszTheta.indepNum_le G hu hc ht0 ht
end ShannonCapacity
