-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.unramifiedCokernelLowerBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:03.233983+00:00
-- url     : https://prove2.me/submissions/ee906645-d049-4784-9fa4-1aac6f515aa7

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Theorems.Thm_ReciprocityTheory_PGsh_Up_span_mk_top
import Theorems.Thm_ReciprocityTheory_PGsh_Up_vp_rpow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_up_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU7 : UnramifiedCokernelLengthStatement) (hEx : LenExStatement) (hKG : KilledGenStatement)
    (hIG : IdemGenStatement) : UnramifiedCokernelLowerBoundStatement := by
  unfold UnramifiedCokernelLowerBoundStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U i V1 hV1
  have hidem : U.εL (U.cj i) * U.εL (U.cj i) = U.εL (U.cj i) := by
    rw [U.εL_orth, if_pos rfl]
  obtain ⟨y, hy⟩ := hIG R g (U.r (U.cj i)) (U.εL (U.cj i)) hidem (U.rank (U.cj i))
  obtain ⟨V2, hV2⟩ := hEx C v R hS.integers g H.Ht (U.εL (U.cj i)) (U.εT i)
  have hkill := up_kill hS H U i
  have hgen : ∃ y' : Fin (U.r (U.cj i)) → cokE H.Ht U.εT U.εL (U.cj i) i,
      Submodule.span R (Set.range y') = ⊤ :=
    ⟨fun k => Submodule.Quotient.mk (y k), span_mk_top _ y hy⟩
  have h1 := hKG C v R hS.integers (cokE H.Ht U.εT U.εL (U.cj i) i) V2 (U.r (U.cj i)) cp hV2
    hgen hkill
  have h2 := hU7 p g C v R O σ cp hp2 hS H U i V1 V2 hV1 hV2
  have h3 := vp_rpow hS (U.r (U.cj i))
  have hx : (0 : ℝ) < (v (algebraMap R C (p : R)) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 hS.p_ne)
  have hsplit : ((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i =
      (U.r (U.cj i) : ℝ) / (p - 1) + ((U.r i : ℝ) / (p - 1) - frobSum U i) := by ring
  rw [hsplit, Real.rpow_add hx, h2, h3]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
  exact_mod_cast h1
end ReciprocityTheory.PGsh.Up
