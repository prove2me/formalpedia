-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.det_ne_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:24.381225+00:00
-- url     : https://prove2.me/submissions/fe3d9540-7310-4371-8f40-27fabc174e68

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (c : R) (hc : c ≠ 0)
    (h : ∀ w : Fin s → R, c • w ∈ Submodule.span R (Set.range fun i => fun a => A a i)) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hvA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have key : ∀ u ∈ Submodule.span R (Set.range fun i => fun a => A a i), v ⬝ᵥ u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact congrFun hvA i
    | zero => simp
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
  have h1 := key _ (h (Pi.single j 1))
  simp [hc] at h1
  exact hj h1
end ReciprocityTheory.PGsh.Up
