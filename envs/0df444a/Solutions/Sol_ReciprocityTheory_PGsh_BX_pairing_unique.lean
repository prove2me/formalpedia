-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pairing_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:04:26.851071+00:00
-- url     : https://prove2.me/submissions/7579104e-78c7-4f08-ad88-7e79e1c9ca2e

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_smul


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
theorem _root_.solution (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x y z') : z = z' := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  obtain ⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩ := h'

  obtain ⟨c, hc, -⟩ := B.trans u u'
  subst hc
  have inj : ∀ {a b : B.G R} (v : B.P R a b) (l l' : (R : Type u)ˣ), B.smul l v = B.smul l' v → l = l' :=
    fun v l l' h => (B.trans v (B.smul l v)).unique rfl h.symm
  rw [B.nsmul1_smul, B.castFst_smul, e₁, ← B.mul_smul] at f₁
  rw [B.nsmul2_smul, B.castSnd_smul, e₂, ← B.mul_smul] at f₂
  rw [← inj _ _ _ f₁, ← inj _ _ _ f₂]
  exact (mul_div_mul_left_eq_div _ _ _).symm
end ReciprocityTheory.PGsh.BX
