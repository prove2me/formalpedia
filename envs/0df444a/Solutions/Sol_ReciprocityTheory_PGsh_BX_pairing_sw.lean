-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pairing_sw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:54:32.826301+00:00
-- url     : https://prove2.me/submissions/f3e7f040-4305-4470-a48b-0f601ff20f63

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_swap_castSnd
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_nsmul2
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_nsmul1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_zero1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_sw_zero2
import Theorems.Thm_ReciprocityTheory_PGsh_BX_swap_castFst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ) (h : B.IsPairing N x y z) :
    B.IsPairing N y x z⁻¹ := by
  have swap_castFst : ∀ {a b c : B.G R} (e : a = b) (v : B.P R a c), B.sw (B.tr1 e v) = B.tr2 e (B.sw v) := by
    intro a b c e v
    subst e
    rfl
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  refine ⟨hy, hx, B.sw u, l₂, l₁, ?_, ?_, inv_div l₁ l₂⟩
  · rw [← B.sw_nsmul2, ← B.swap_castSnd, e₂, B.sw_smul, B.sw_zero2]
  · rw [← B.sw_nsmul1, ← swap_castFst, e₁, B.sw_smul, B.sw_zero1]
end ReciprocityTheory.PGsh.BX
