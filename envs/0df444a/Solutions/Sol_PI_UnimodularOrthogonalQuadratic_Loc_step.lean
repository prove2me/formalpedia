-- Prove2me | solution 1 for PI.UnimodularOrthogonalQuadratic.Loc.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:42.964289+00:00
-- url     : https://prove2.me/submissions/0e820a86-d6de-43fd-a279-d4028b11841f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_LocalOrthogonalMatrixOddPrime
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_q_smul
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_star_eq_of_herm
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_q_fixed
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_cong_apply_self
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_herm_cong
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_cong
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_updateRow_zero
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_elim
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_row0
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_of_first_row_single
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_det_blk
import Theorems.Thm_PI_UnimodularOrthogonalQuadratic_Loc_blk_cong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnimodularOrthogonalQuadratic PI.UnimodularOrthogonalQuadratic.Loc
open Matrix
variable {S : Type} [CommRing S] [StarRing S]
namespace PI.UnimodularOrthogonalQuadratic.Loc
theorem _root_.solution (hL : LocHyp S) {n : ℕ}
    (IH : ∀ H : Matrix (Fin n) (Fin n) S, Hᴴ = H → IsUnit H.det →
      ∃ P : Matrix (Fin n) (Fin n) S, IsUnit P.det ∧ P * H * Pᴴ = 1)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) S} (hH : Hᴴ = H) (hdet : IsUnit H.det)
    {v : Fin (n + 1) → S} (hv : v 0 = 1) (hq : IsUnit (q H v)) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) S, IsUnit P.det ∧ P * H * Pᴴ = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, w * q H v = 1 := ⟨_, hq.val_inv_mul⟩
  have hqs : star (q H v) = q H v := q_fixed hH v
  have hws : star w = w := by
    have h1 : star w * q H v = 1 := by rw [← hqs, ← star_mul', hw, star_one]
    linear_combination w * h1 - (star w) * hw
  obtain ⟨u, hu⟩ := hL.norm w hws (isUnit_iff_exists_inv.mpr ⟨_, hw⟩)
  have huq : u * star u * q H v = 1 := by rw [hu, hw]
  have hu1 : IsUnit u := isUnit_iff_exists_inv.mpr ⟨star u * q H v, by rw [← mul_assoc, huq]⟩
  set P1 : Matrix (Fin (n + 1)) (Fin (n + 1)) S := updateRow 1 0 (u • v) with hP1
  have hP1d : IsUnit P1.det := by
    rw [hP1, det_updateRow_zero]
    simpa [hv] using hu1
  set H1 := P1 * H * P1ᴴ with hH1def
  have hH1 : H1ᴴ = H1 := herm_cong P1 hH
  have hH1d : IsUnit H1.det := det_cong hP1d hdet
  have hH100 : H1 0 0 = 1 := by
    rw [hH1def, cong_apply_self, hP1, updateRow_self, q_smul, huq]
  have hEd : IsUnit (elim H1).det := by rw [det_elim]; exact isUnit_one
  set H2 := elim H1 * H1 * (elim H1)ᴴ with hH2def
  have hH2 : H2ᴴ = H2 := herm_cong _ hH1
  have hH2d : IsUnit H2.det := det_cong hEd hH1d
  have hrow : ∀ b, H2 0 b = if b = 0 then 1 else 0 := row0 hH1 hH100
  have hcol : ∀ a, H2 a 0 = if a = 0 then 1 else 0 := fun a => by
    rw [← star_eq_of_herm hH2 0 a, hrow]
    split_ifs <;> simp
  have hH3 : (H2.submatrix Fin.succ Fin.succ)ᴴ = H2.submatrix Fin.succ Fin.succ := by
    rw [conjTranspose_submatrix, hH2]
  have hH3d : IsUnit (H2.submatrix Fin.succ Fin.succ).det := by
    rw [← det_of_first_row_single H2 hrow]
    exact hH2d
  obtain ⟨P3, hP3d, hP3⟩ := IH _ hH3 hH3d
  refine ⟨blk P3 * elim H1 * P1, ?_, ?_⟩
  · rw [det_mul, det_mul, det_blk]
    exact (hP3d.mul hEd).mul hP1d
  · have : blk P3 * elim H1 * P1 * H * (blk P3 * elim H1 * P1)ᴴ = blk P3 * H2 * (blk P3)ᴴ := by
      simp only [hH2def, hH1def, conjTranspose_mul, Matrix.mul_assoc]
    rw [this]
    exact blk_cong hrow hcol hP3
end PI.UnimodularOrthogonalQuadratic.Loc
