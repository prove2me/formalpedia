-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.lev_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:23.622831+00:00
-- url     : https://prove2.me/submissions/8f7f5559-b436-4582-bc89-a521c3d3aad8

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
open PositivityTheory.Mix.PlaneOK
variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h
omit h
namespace PositivityTheory.Mix.PlaneOK
theorem _root_.solution (t s : R) (v) : lev c J ε x y t s *ᵥ v = v + ((t - 1) * bf c J v y) • x + ((s - 1) * ε * bf c J v x) • y := by
  have vm : ∀ p q w : Fin n → R, vecMulVec p q *ᵥ w = (q ⬝ᵥ w) • p := by
    intro p q w
    ext i
    simp only [vecMulVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [lev, add_mulVec, one_mulVec, smul_mulVec, vm, smul_smul]
  rw [dotProduct_comm (J *ᵥ fun i => c (y i)) v, dotProduct_comm (J *ᵥ fun i => c (x i)) v]
  rfl
end PositivityTheory.Mix.PlaneOK
