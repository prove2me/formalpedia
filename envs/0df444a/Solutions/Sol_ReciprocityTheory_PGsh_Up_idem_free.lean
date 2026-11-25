-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.idem_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:51.651126+00:00
-- url     : https://prove2.me/submissions/1f7bc80c-7465-4047-930c-92b3f8ac91c9

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
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
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (P : Matrix (Fin g) (Fin g) R)
    (hP : P * P = P) : ∃ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R)) := by
  classical
  set f := Matrix.mulVecLin P with hf
  have hff : ∀ x, f (f x) = f x := by
    intro x
    simp only [hf, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  have hsplit : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    apply Subtype.ext
    first
    | exact hff y
    | simp [hff]
  haveI : Module.Projective R (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict hsplit
  haveI : Module.Free R (LinearMap.range f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_flat_of_localRing
    | infer_instance
  exact ⟨Module.finrank R (LinearMap.range f), ⟨(Module.finBasis R (LinearMap.range f)).equivFun⟩⟩
end ReciprocityTheory.PGsh.Up
