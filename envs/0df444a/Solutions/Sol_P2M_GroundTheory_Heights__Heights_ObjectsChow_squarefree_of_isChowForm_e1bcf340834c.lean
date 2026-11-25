-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_squarefree_of_isChowForm_e1bcf340834c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:24.988717+00:00
-- url     : https://prove2.me/submissions/bcc9dd8e-3222-46b5-a175-5d5706aa76c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsHomogeneousOfIsMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) : Squarefree f := by
  rintro x ⟨h, rfl⟩
  have hxh : x * x * h ∣ x * h := by
    refine (hf.2 (x * h)).1 fun u hu => ?_
    have h0 := (hf.2 (x * x * h)).2 dvd_rfl u hu
    simp only [map_mul] at h0 ⊢
    have h2 : aeval u x * aeval u h * (aeval u x * aeval u h) = 0 := by
      calc _ = aeval u x * aeval u x * aeval u h * aeval u h := by ring
        _ = 0 := by rw [h0, zero_mul]
    exact mul_self_eq_zero.mp h2
  have hne : x * h ≠ 0 := fun h0 => hf.1 (by rw [mul_assoc, h0, mul_zero])
  have h1 : x * (x * h) ∣ 1 * (x * h) := by rwa [one_mul, ← mul_assoc]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).mp h1)
end GroundTheory.Heights₂.Heights.ObjectsChow
