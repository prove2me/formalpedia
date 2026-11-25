-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ED.finrank_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:28:23.941989+00:00
-- url     : https://prove2.me/submissions/f60106f1-bb75-4d9e-9eec-736ae71dedd1

import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_free_fin
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_fg_range
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_isLocal_of_integers
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
open ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.ED
theorem _root_.solution (hv : v.Integers R) {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (P : Fin m → Matrix α α R) (horth : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) :
    ∑ i, Module.finrank R (LinearMap.range (Matrix.mulVecLin (P i))) = Fintype.card α := by
  classical
  haveI := isLocal_of_integers hv
  have hfr := fun i => free_fin hv _ (fg_range (P i))
  haveI : ∀ i, Module.Free R (LinearMap.range (Matrix.mulVecLin (P i))) := fun i => (hfr i).1
  haveI : ∀ i, Module.Finite R (LinearMap.range (Matrix.mulVecLin (P i))) := fun i => (hfr i).2
  have hPP : ∀ i j (w : α → R), P i *ᵥ (P j *ᵥ w) = if i = j then P i *ᵥ w else 0 := by
    intro i j w
    rw [Matrix.mulVec_mulVec, horth]
    split_ifs <;> simp
  have hs : ∀ w : α → R, ∑ i, P i *ᵥ w = w := fun w => by
    rw [← show (∑ i, P i) *ᵥ w = ∑ i, P i *ᵥ w from map_sum (Matrix.mulVec.addMonoidHomLeft w) P Finset.univ,
      hsum, Matrix.one_mulVec]

  let e : (α → R) ≃ₗ[R] ((i : Fin m) → LinearMap.range (Matrix.mulVecLin (P i))) :=
    { toFun := fun w i => ⟨P i *ᵥ w, w, rfl⟩
      map_add' := fun w w' => by
        funext i
        apply Subtype.ext
        simp [Matrix.mulVec_add]
      map_smul' := fun c w => by
        funext i
        apply Subtype.ext
        simp [Matrix.mulVec_smul]
      invFun := fun f => ∑ i, (f i : α → R)
      left_inv := fun w => hs w
      right_inv := fun f => by
        funext i
        apply Subtype.ext
        show P i *ᵥ ∑ j, (f j : α → R) = f i
        rw [show P i *ᵥ ∑ j, (f j : α → R) = ∑ j, P i *ᵥ (f j : α → R) from
          map_sum (Matrix.mulVecLin (P i)) _ _]
        have hj : ∀ j, P i *ᵥ (f j : α → R) = if i = j then (f i : α → R) else 0 := by
          intro j
          obtain ⟨y, hy⟩ := (f j).2
          rw [← hy, Matrix.mulVecLin_apply, hPP]
          split_ifs with h
          · subst h
            exact hy
          · rfl
        rw [Finset.sum_congr rfl (fun j _ => hj j)]
        simp }
  rw [← Module.finrank_pi_fintype R, ← e.finrank_eq, Module.finrank_fintype_fun_eq_card]
end ReciprocityTheory.PGsh.Up.ED
