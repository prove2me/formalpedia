-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointLine_irreducible_pairing_1c55fbb0a974
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:30.1367+00:00
-- url     : https://prove2.me/submissions/b834f25c-2e2b-4e1f-a8a9-1b99d48b0951

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_coeff_pairing_f4de1af45484
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_exists_ne_zero_98697fadef41

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointLine
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointLine
theorem _root_.solution {y : Fin n → ℂ} (hy : y ≠ 0) : Irreducible (pairing y) := by
  obtain ⟨a, ha⟩ := exists_ne_zero hy
  have hne : pairing y ≠ 0 := fun h => ha (by rw [← coeff_pairing y a, h, coeff_zero])
  have hhom : (pairing y).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
  refine irreducible_of_totalDegree_eq_one (hhom.totalDegree hne) fun c hc => ?_
  have h := hc (Finsupp.single ((0 : Fin 1), a) 1)
  rw [coeff_pairing] at h
  exact isUnit_iff_ne_zero.mpr (by rintro rfl; exact ha (zero_dvd_iff.mp h))
end GroundTheory.Heights₂.Heights.PointLine
