-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.exists_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:25.752976+00:00
-- url     : https://prove2.me/submissions/76b7723f-a191-4948-8572-58fd552b6af3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_levi_element_fixes_first_vector
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_y
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_i
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_mul
import Theorems.Thm_PositivityTheory_Mix_PlaneOK_lev_unit

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
namespace PositivityTheory.Mix.PlaneOK
theorem _root_.solution (t : Rˣ) : ∃ m : GL (Fin n) R, m.1ᵀ * J * m.1.map c = J ∧ m.1 *ᵥ x = t.1 • x ∧ m.1 *ᵥ y = c (t⁻¹).1 • y ∧
    ∀ z, m.1 *ᵥ (ι *ᵥ z) = ι *ᵥ z := by
  have hc1 : c (t⁻¹ : Rˣ).1 * c t.1 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hc2 : c t.1 * c (t⁻¹ : Rˣ).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨lev c J ε x y t.1 (c (t⁻¹ : Rˣ).1), lev c J ε x y (t⁻¹ : Rˣ).1 (c t.1),
    h.lev_mul (Units.mul_inv t) hc1, h.lev_mul (Units.inv_mul t) hc2⟩, ?_, h.levi_element_fixes_first_vector _ _, h.lev_y _ _, fun z => h.lev_i _ _ z⟩
  apply h.lev_unit
  rw [h.cc, Units.mul_inv]
end PositivityTheory.Mix.PlaneOK
