-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_fam_eq_famExt_551d8170ff5e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:34.04184+00:00
-- url     : https://prove2.me/submissions/773cad5e-c64c-404d-94ed-f4d78d0dcef4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_hermZpow_47ad9a4aea08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_basis_49b303483717
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_update_lamLine_f39d8c36c733

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) (T : Finset (Fin (n + 1))) (t : Fin (n + 1) → Fin 2) :
    I P (n + 1) (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) =
      famExt I P (n + 1) ![X, A] (fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (t j) 1) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  induction T using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.notMem_empty, if_false]
    exact (famExt_basis ![X, A] t).symm
  | insert a T ha ih =>
    have hins : ∀ {β : Type} (y : β) (F : Fin 2 → β),
        (fun j => if j ∈ insert a T then y else F (t j)) =
          Function.update (fun j => if j ∈ T then y else F (t j)) a y := by
      intro β y F
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp
      · simp [h]
    have hupd : ∀ {β : Type} (y : β) (F : Fin 2 → β) (i : Fin 2),
        Function.update (fun j => if j ∈ T then y else F (t j)) a (F i) =
          fun j => if j ∈ T then y else F (Function.update t a i j) := by
      intro β y F i
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp [ha]
      · simp [Function.update_of_ne h]
    have hL : ∀ j, IsSmoothHerm ((fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) j) := by
      intro j
      dsimp only
      split_ifs
      · exact isSmoothHerm_tensor (isSmoothHerm_tensor hA hA) (isSmoothHerm_hermZpow hX _)
      · exact hsm (t j)
    have eL : (fun j => if j ∈ insert a T then lamLine A X c else ![X, A] (t j)) =
        Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a (lamLine A X c) :=
      hins _ _
    have eV : (fun j => if j ∈ insert a T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) =
        Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a
          ![-(c : ℝ), 2] :=
      hins (![-(c : ℝ), 2] : Fin 2 → ℝ) fun i => Pi.single i 1
    have hA1 : Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a A =
        fun j => if j ∈ T then lamLine A X c else ![X, A] (Function.update t a 1 j) :=
      hupd _ ![X, A] 1
    have hX0 : Function.update (fun j => if j ∈ T then lamLine A X c else ![X, A] (t j)) a X =
        fun j => if j ∈ T then lamLine A X c else ![X, A] (Function.update t a 0 j) :=
      hupd _ ![X, A] 0
    have hV1 : Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 1 1) = fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (Function.update t a 1 j) 1 :=
      hupd (![-(c : ℝ), 2] : Fin 2 → ℝ) (fun i => Pi.single i 1) 1
    have hV0 : Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 0 1) = fun j => if j ∈ T then ![-(c : ℝ), 2] else Pi.single (Function.update t a 0 j) 1 :=
      hupd (![-(c : ℝ), 2] : Fin 2 → ℝ) (fun i => Pi.single i 1) 0
    have hw : (![-(c : ℝ), 2] : Fin 2 → ℝ) = (2 : ℝ) • Pi.single 1 1 + (-(c : ℝ)) • Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp
    rw [eL, eV, fam_update_lamLine hI hP _ hL a hA hX c, hA1, hX0, ih, ih,
      congrArg (Function.update (fun j => if j ∈ T then (![-(c : ℝ), 2] : Fin 2 → ℝ) else Pi.single (t j) 1) a) hw, MultilinearMap.map_update_add, MultilinearMap.map_update_smul,
      MultilinearMap.map_update_smul, hV1, hV0, smul_eq_mul, smul_eq_mul]
    ring
end GroundTheory.Heights₂.Heights.Inter
