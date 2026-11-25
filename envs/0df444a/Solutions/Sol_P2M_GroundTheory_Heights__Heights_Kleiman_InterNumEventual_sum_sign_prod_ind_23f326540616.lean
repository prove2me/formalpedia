-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_sum_sign_prod_ind_23f326540616
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:45:19.729911+00:00
-- url     : https://prove2.me/submissions/bce3a543-efdd-49fa-8087-08ab563be271

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumEventual
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual
namespace GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual
theorem _root_.solution {n : ℕ} (e : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, ((ind T i : ℕ) : ℚ) ^ e i =
      ∏ i, (1 - (0 : ℚ) ^ e i) := by
  have h1 : ∏ i, (1 - (0 : ℚ) ^ e i) = ∏ i ∈ Finset.univ, (1 + -(0 : ℚ) ^ e i) := by
    simp only [sub_eq_add_neg]
  rw [h1, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, one_mul, Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin,
    ← Finset.prod_mul_prod_compl T, Finset.compl_eq_univ_sdiff]
  congr 1
  rw [Finset.prod_eq_one (fun i hi => by simp [ind, hi]), one_mul]
  exact Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_sdiff] at hi
    simp [ind, hi.2]
end GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual
