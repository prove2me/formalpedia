-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.det_gram_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:31.296211+00:00
-- url     : https://prove2.me/submissions/9aa7fe14-3927-47fc-b463-44ca486ccaab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_gram_mat__78f14edbfb72

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {N L : ℕ} (Z : Fin L → Fin N → ℂ) (T : Matrix (Fin L) (Fin L) ℂ) (hT : T.BlockTriangular id) :
    (Matrix.of fun a b => star (∑ j, T j a • Z j) ⬝ᵥ ∑ j, T j b • Z j).det =
      (star (∏ j, T j j) * ∏ j, T j j) * (Matrix.of fun a b => star (Z a) ⬝ᵥ Z b).det := by
  rw [gram_mat' (fun a => ∑ j, T j a • Z j) ((Matrix.of fun p a => Z a p) * T) (fun p a => by
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _),
    gram_mat' Z (Matrix.of fun p a => Z a p) (fun p a => rfl), conjTranspose_mul]
  rw [show Tᴴ * (Matrix.of fun p a => Z a p)ᴴ * ((Matrix.of fun p a => Z a p) * T) =
      Tᴴ * ((Matrix.of fun p a => Z a p)ᴴ * (Matrix.of fun p a => Z a p)) * T by simp only [Matrix.mul_assoc]]
  rw [det_mul, det_mul, det_conjTranspose, det_of_upperTriangular hT]; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
