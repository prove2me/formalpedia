-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.det_gram_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:08.532718+00:00
-- url     : https://prove2.me/submissions/cfea56b4-d6e1-4786-9e9b-263cbba5102d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_gram_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (w u : Fin m → EuclideanSpace ℂ (Fin n)) (τ : Matrix (Fin m) (Fin m) ℂ)
    (hu : Orthonormal ℂ u) (hτ : τ.BlockTriangular id) (hw : ∀ a, w a = ∑ b, τ b a • u b) :
    (gram w).det = ((∏ j, ‖τ j j‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : gram u = 1 := by
    ext i j; simp [gram, orthonormal_iff_ite.1 hu, Matrix.one_apply]
  have hg : gram w = τᴴ * τ := by
    rw [show w = fun a => ∑ b, τ b a • u b from funext hw, gram_comb, h1, Matrix.mul_one]
  rw [hg, det_mul, det_conjTranspose, det_of_isUpperTriangular hτ]
  rw [show star (∏ j, τ j j) = ∏ j, star (τ j j) by
    simpa using map_prod (starRingEnd ℂ) (fun j => τ j j) Finset.univ]
  rw [← Finset.prod_mul_distrib, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← starRingEnd_apply, Complex.conj_mul']; push_cast; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
