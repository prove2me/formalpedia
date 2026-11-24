-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.cols_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:27.304692+00:00
-- url     : https://prove2.me/submissions/facfa737-c1ff-425d-a8ac-ad86cdad8b07

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
omit [DecidableEq d] [DecidableEq e]
namespace PositivityTheory.ThKG.Tow.Levi
theorem _root_.solution {m : Matrix d d R} {g : Matrix e e R} {b : Matrix e (Fin 2) R} {a : Matrix (Fin 2) e R}
    {s : Matrix (Fin 2) (Fin 2) R} (h : m * fr ι x y = fr ι x y * fromBlocks g b a s) :
    m * ι = ι * g + of (fun i j => ![x i, y i] j) * a ∧
      m *ᵥ x = ι *ᵥ (fun j => b j 0) + s 0 0 • x + s 1 0 • y ∧ m *ᵥ y = ι *ᵥ (fun j => b j 1) + s 0 1 • x + s 1 1 • y := by
  rw [fr, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff] at h
  refine ⟨h.1, funext fun i => ?_, funext fun i => ?_⟩
  · have := congrFun (congrFun h.2 i) 0
    simpa [mul_apply, mulVec, dotProduct, add_assoc, mul_comm] using this
  · have := congrFun (congrFun h.2 i) 1
    simpa [mul_apply, mulVec, dotProduct, add_assoc, mul_comm] using this
end PositivityTheory.ThKG.Tow.Levi
