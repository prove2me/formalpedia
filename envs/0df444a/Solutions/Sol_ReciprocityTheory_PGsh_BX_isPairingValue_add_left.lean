-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.isPairingValue_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:51.873307+00:00
-- url     : https://prove2.me/submissions/fbf3ca33-4440-466a-a3b2-ae3506325693

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_eq_iff
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_addFst
import Theorems.Thm_ReciprocityTheory_PGsh_BX_fibreFst_nsmul_mk


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
theorem _root_.solution (N : ℕ) (x x' y : B.G R) (z z' : (R : Type u)ˣ) (h : B.IsPairing N x y z)
    (h' : B.IsPairing N x' y z') : B.IsPairing N (x + x') y (z * z') := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  obtain ⟨hx', hy', u', m₁, m₂, f₁, f₂, rfl⟩ := h'
  have hxx : N • (x + x') = 0 := by rw [nsmul_add, hx, hx', add_zero]
  have hsm : ∀ (c : (R : Type u)ˣ) {a b : B.G R} (e : a = b) (v : B.P R a y) (v' : B.P R b y), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b e v v' hv
    subst e
    rw [eq_of_heq hv]
  refine ⟨hxx, hy, B.add1 u u', l₁ * m₁, l₂ * m₂, ?_, ?_, div_mul_div_comm _ _ _ _⟩
  ·
    have hS : (⟨N • (x + x'), B.nsmul1 (B.add1 u u') N⟩ : B.S1 R y) =
        ⟨N • x + N • x', B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)⟩ := by
      rw [← B.fibreFst_nsmul_mk]
      show N • (B.S1mk u + B.S1mk u') = _
      rw [smul_add, B.fibreFst_nsmul_mk, B.fibreFst_nsmul_mk]
      rfl
    have e₁' := (B.castFst_eq_iff hx _ _).1 e₁
    have f₁' := (B.castFst_eq_iff hx' _ _).1 f₁
    rw [B.castFst_eq_iff, hS]
    have ee : B.S1mk (B.nsmul1 u N) = B.S1mk (B.smul l₁ (B.zero1 y)) := e₁'
    have ff : B.S1mk (B.nsmul1 u' N) = B.S1mk (B.smul m₁ (B.zero1 y)) := f₁'
    show B.S1mk (B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)) = B.S1mk (B.smul (l₁ * m₁) (B.zero1 y))
    have step : B.S1mk (B.add1 (B.nsmul1 u N) (B.nsmul1 u' N)) = B.S1mk (B.nsmul1 u N) + B.S1mk (B.nsmul1 u' N) := rfl
    have step2 : B.S1mk (B.smul l₁ (B.zero1 y)) + B.S1mk (B.smul m₁ (B.zero1 y)) =
        B.S1mk (B.add1 (B.smul l₁ (B.zero1 y)) (B.smul m₁ (B.zero1 y))) := rfl
    rw [step, ee, ff, step2, B.addFst_smul]
    exact Sigma.ext (add_zero 0) (hsm _ (add_zero 0) _ _ (B.zeroFst_add (B.zero1 y)))
  · rw [B.nsmulSnd_addFst, B.castSnd_addFst, e₂, f₂, B.addFst_smul, B.zeroSnd_addFst]
end ReciprocityTheory.PGsh.BX
