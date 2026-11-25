-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GSB.ga_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:29.574655+00:00
-- url     : https://prove2.me/submissions/9cadbce4-8bce-4ba4-b79b-4ca81826f7d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GSB_gram_det_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GSB_gram_re_det_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GSB_linA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GSB_gram_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_det_gram_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_ga_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_gram_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_gs_fac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_norm_mulVec_le


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB
theorem _root_.solution (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by
  rw [ga_eq, ga_eq]
  set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef
  have hAw : (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) =
      fun a => linA A (w a) := by
    funext a; rw [linA_apply]
  rw [hAw]
  by_cases hw : LinearIndependent ℂ w
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac w hw
    have h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b) := by
      funext a; rw [hwe a, map_sum]; simp only [map_smul]
    have hgw : (GS.gram w).det = (τᴴ).det * τ.det := by
      rw [show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]
    have hv : ∀ b, ‖linA A (u b)‖ ≤ gN A := by
      intro b
      have := norm_mulVec_le A (WithLp.ofLp (u b))
      rw [WithLp.toLp_ofLp, hu.1 b, mul_one] at this
      rw [linA_apply]; exact this
    have hle := gram_re_det_le (fun b => linA A (u b)) (gN A) hv
    have hX := det_gram_of w u τ hu hτ hwe
    rw [h1, gram_comb, det_mul, det_mul]
    have e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det =
        (GS.gram w).det * (GS.gram fun b => linA A (u b)).det := by rw [hgw]; ring
    rw [e1, hX, Complex.re_ofReal_mul]
    have hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    rw [Complex.ofReal_re, mul_comm]
    exact mul_le_mul_of_nonneg_right hle hnn
  · have hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a)) := fun h => hw (h.of_comp (linA A))
    rw [gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
