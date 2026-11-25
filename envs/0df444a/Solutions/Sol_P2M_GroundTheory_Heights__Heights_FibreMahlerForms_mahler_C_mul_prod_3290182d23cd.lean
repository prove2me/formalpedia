-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_mahler_C_mul_prod_3290182d23cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:34.548973+00:00
-- url     : https://prove2.me/submissions/6085184a-d935-4baf-9dd0-54b88b6ca054

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahlerMul_d866b4823dac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_02c18ff6a9ea


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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {d : ℕ}
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution {ι : Type*} (s : Finset ι) (L : ι → MvPolynomial (Fin 1 × Fin d) ℂ)
    (hL : ∀ q, L q ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    mahler (HermNorm.std d) 1 (C a * ∏ q ∈ s, L q) =
      Real.log ‖a‖ + ∑ q ∈ s, mahler (HermNorm.std d) 1 (L q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one, mahler_C, Finset.sum_empty, add_zero]
  | insert q s hq ih =>
    have hne : (C a * ∏ q ∈ s, L q : MvPolynomial (Fin 1 × Fin d) ℂ) ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr ha) (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q)
    rw [Finset.prod_insert hq, mul_left_comm, mahlerMul d 1 _ _ _ (hL q) hne, ih,
      Finset.sum_insert hq]
    ring
end GroundTheory.Heights₂.Heights.FibreMahlerForms
