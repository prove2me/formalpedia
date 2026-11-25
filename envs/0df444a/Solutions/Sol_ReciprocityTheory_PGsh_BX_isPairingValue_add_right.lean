-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isPairingValue_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:43.775381+00:00
-- url     : https://prove2.me/submissions/ae16bec9-1768-46ad-b291-423bc090bcad

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_eq_iff
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_addSnd
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreSnd_nsmul_mk
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmulFst_addSnd


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
theorem _root_.solution (N : ℕ) (x y y' : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x y' z') : B.IsPairing N x (y + y') (z * z') := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  obtain ⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩ := h'
  have hyy : N • (y + y') = 0 := by rw [nsmul_add, hy, hy', add_zero]
  have hsm : ∀ (c : (R : Type u)ˣ) {a b : B.G R} (e : a = b) (v : B.P R x a) (v' : B.P R x b), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b e v v' hv
    subst e
    rw [eq_of_heq hv]
  refine ⟨hx, hyy, B.add2 u u', l₁ * m₁, l₂ * m₂, ?_, ?_, div_mul_div_comm _ _ _ _⟩
  · rw [B.nsmulFst_addSnd, B.castFst_addSnd, e₁, f₁, B.addSnd_smul, B.zeroFst_addSnd]
  ·
    have hS : (⟨N • (y + y'), B.nsmul2 (B.add2 u u') N⟩ : B.S2 R x) =
        ⟨N • y + N • y', B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)⟩ := by
      rw [← B.fibreSnd_nsmul_mk]
      show N • (B.S2mk u + B.S2mk u') = _
      rw [smul_add, B.fibreSnd_nsmul_mk, B.fibreSnd_nsmul_mk]
      rfl
    have e₂' := (B.castSnd_eq_iff hy _ _).1 e₂
    have f₂' := (B.castSnd_eq_iff hy' _ _).1 f₂
    rw [B.castSnd_eq_iff, hS]
    have ee : B.S2mk (B.nsmul2 u N) = B.S2mk (B.smul l₂ (B.zero2 x)) := e₂'
    have ff : B.S2mk (B.nsmul2 u' N) = B.S2mk (B.smul m₂ (B.zero2 x)) := f₂'
    show B.S2mk (B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)) = B.S2mk (B.smul (l₂ * m₂) (B.zero2 x))
    have step : B.S2mk (B.add2 (B.nsmul2 u N) (B.nsmul2 u' N)) = B.S2mk (B.nsmul2 u N) + B.S2mk (B.nsmul2 u' N) := rfl
    have step2 : B.S2mk (B.smul l₂ (B.zero2 x)) + B.S2mk (B.smul m₂ (B.zero2 x)) =
        B.S2mk (B.add2 (B.smul l₂ (B.zero2 x)) (B.smul m₂ (B.zero2 x))) := rfl
    rw [step, ee, ff, step2, B.addSnd_smul]
    exact Sigma.ext (add_zero 0) (hsm _ (add_zero 0) _ _ (B.zeroSnd_add (B.zero2 x)))
end ReciprocityTheory.PGsh.BX
