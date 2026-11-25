-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:07.745075+00:00
-- url     : https://prove2.me/submissions/348e9ab9-4f74-4e55-9ecc-e13dd2fe5619

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_mem_u_5833aa7027d5
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_finrank_u_edc412419c4e
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInnerR_apply_d6ec03973d4a
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_sum_right_e2ea2b48ebbe
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_E_E_d7a9c5da1e23
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_place_eq_e9555ed74f33

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
variable {ι : Type*} [Fintype ι]
variable (F : OrthoFrame)
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution (τ : Fin F.f) : Fintype.card {l // F.place l = τ} = F.r ^ 2 := by
  classical
  let toC : indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) →ₗ[ℝ] ({l // F.place l = τ} → ℝ) :=
    { toFun := fun X l => tInner (F.E l τ) X
      map_add' := fun X Y => by
        funext l; simp only [Submodule.coe_add, Pi.add_apply, ← tInnerR_apply, map_add]
      map_smul' := fun c X => by
        funext l
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, ← tInnerR_apply, map_smul] }
  let e : indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ) ≃ₗ[ℝ] ({l // F.place l = τ} → ℝ) :=
    { toC with
      invFun := fun c => ⟨∑ l : {l // F.place l = τ}, c l • F.E l τ,
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (E_mem_u F l τ)⟩
      left_inv := fun X => Subtype.ext (sum_place_eq F X.2)
      right_inv := fun c => by
        funext k
        change tInner (F.E k τ) (∑ l : {l // F.place l = τ}, c l • F.E l τ) = c k
        rw [tInner_sum_right, Finset.sum_eq_single k]
        · rw [tInner_E_E F k.2, if_pos rfl, mul_one]
        · intro l _ hl
          rw [tInner_E_E F k.2, if_neg (fun h => hl (Subtype.ext h).symm), mul_zero]
        · simp }
  have h := e.finrank_eq
  rw [finrank_u, F.sig, Module.finrank_fintype_fun_eq_card] at h
  exact h.symm
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
