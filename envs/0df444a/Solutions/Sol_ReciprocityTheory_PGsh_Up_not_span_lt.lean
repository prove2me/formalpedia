-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.not_span_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:06.864341+00:00
-- url     : https://prove2.me/submissions/f7627600-0e22-4084-8ffe-bc5b633202d6

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
import Theorems.Thm_ReciprocityTheory_PGsh_Up_det_ne_of_span
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
theorem _root_.solution {s : ℕ} (B : Matrix (Fin (s + 1)) (Fin s) R) (c : R) (hc : c ≠ 0)
    (h : ∀ w : Fin (s + 1) → R, c • w ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    False := by
  classical
  let A : Matrix (Fin (s + 1)) (Fin (s + 1)) R :=
    Matrix.of fun a i => Fin.snoc (α := fun _ => R) (B a) (0 : R) i
  have hA : A.det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last s)
    intro a
    simp [A]
  refine det_ne_of_span A c hc ?_ hA
  intro w
  refine Submodule.span_mono ?_ (h w)
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castSucc i, ?_⟩
  funext a
  simp [A]
end ReciprocityTheory.PGsh.Up
