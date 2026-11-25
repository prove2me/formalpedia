-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_fam_update_lamLine_f39d8c36c733
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:55.367688+00:00
-- url     : https://prove2.me/submissions/7de46b8f-515e-463c-9e68-1faac646b96d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_hermZpow_47ad9a4aea08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_be457e2d980a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_update_eq_snoc_8276b4e1bae1

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
theorem _root_.solution (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) :
    I P (n + 1) (Function.update L a (lamLine A X c)) =
      2 * I P (n + 1) (Function.update L a A) - c * I P (n + 1) (Function.update L a X) := by
  unfold lamLine
  have hAA := isSmoothHerm_tensor hA hA
  have hXc := isSmoothHerm_hermZpow hX (-c)
  have hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i) :=
    fun i => hL _
  rw [fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAA hXc), fam_update_eq_snoc hI hP L hL a hA,
    fam_update_eq_snoc hI hP L hL a hX]
  have h₁ := hI.2.1 P n (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) _ _ hP hR hAA hXc
  have h₂ := hI.2.1 P n (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) _ _ hP hR hA hA
  have h₃ := fam_snoc_zpow hI hP (fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) hR hX (-c)
  rw [h₁, h₂, h₃]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.Inter
