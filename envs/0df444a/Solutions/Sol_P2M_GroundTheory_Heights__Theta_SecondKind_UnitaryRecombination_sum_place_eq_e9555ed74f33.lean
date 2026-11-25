-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_sum_place_eq_e9555ed74f33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:50.72218+00:00
-- url     : https://prove2.me/submissions/749cc0f9-5063-4df9-9e43-45d378ecbb09

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_hsInner_eq_1ad3b1c0ab1b
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_io_coords_bb82a2b1c0fb
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_tInner_zero_right_fae129d07542

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
theorem _root_.solution {τ : Fin F.f} {X : Matrix (Fin (F.p τ) ⊕ Fin (F.q τ)) (Fin (F.p τ) ⊕ Fin (F.q τ)) ℂ}
    (hX : X ∈ indefiniteUnitaryLieAlgebra (F.p τ) (F.q τ)) :
    ∑ l : {l // F.place l = τ}, tInner (F.E l τ) X • F.E l τ = X := by
  classical
  set Xs : MatProd F.p F.q := Pi.single τ X with hXs
  have hmem : Xs ∈ lieProd F.p F.q := by
    rw [lieProd, Submodule.mem_pi]
    intro τ' _
    by_cases h : τ' = τ
    · subst h; simpa [hXs] using hX
    · simp [hXs, h]
  have hc : ∀ l, coords F Xs l = tInner (F.E l τ) X := by
    intro l
    rw [coords, hsInner_eq, Finset.sum_eq_single τ]
    · simp [hXs]
    · intro τ' _ h; simp [hXs, h, tInner_zero_right]
    · simp
  have h := congrFun (io_coords F hmem) τ
  simp only [OrthoFrame.io, Finset.sum_apply, Pi.smul_apply, hc] at h
  rw [hXs, Pi.single_eq_same] at h
  have hz : ∑ l : {l // ¬ F.place l = τ}, tInner (F.E l τ) X • F.E (l : Fin F.dim) τ = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [E_apply_of_ne F (fun h' => l.2 h'.symm), smul_zero]
  calc ∑ l : {l // F.place l = τ}, tInner (F.E l τ) X • F.E l τ
      = ∑ l, tInner (F.E l τ) X • F.E l τ := by
        rw [← Fintype.sum_subtype_add_sum_subtype (fun l => F.place l = τ), hz, add_zero]
    _ = X := h
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
