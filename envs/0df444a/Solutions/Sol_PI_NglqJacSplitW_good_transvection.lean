-- Prove2me | solution 1 for PI.NglqJacSplitW.good_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:56.961345+00:00
-- url     : https://prove2.me/submissions/4d79c4b5-5ace-4742-97e6-3433f2f1f118

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_FactorOneOfDiscrete
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianTransvectionSplitting_GoodTransvection
import Theorems.Thm_PI_NglqJacSplitW_chiM_mul
import Theorems.Thm_PI_NglqJacSplitW_chiM_one
import Theorems.Thm_PI_NglqJacSplitW_chiM_congr
import Theorems.Thm_PI_NglqJacSplitW_chiM_pos
import Theorems.Thm_PI_NglqJacSplitW_good_one
import Theorems.Thm_PI_NglqJacSplitW_transvection_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal
open PI PI.NglqJacSplitW
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.NglqJacSplitW
theorem _root_.solution (i j : ι) (hij : i ≠ j) (c : F) : Good (transvection i j c) := by
  have hT : ∀ c : F, IsUnit (transvection i j c).det := fun c => by
    rw [Matrix.det_transvection_of_ne (i := i) (j := j) hij c]
    exact isUnit_one
  have h1u : IsUnit (1 : Matrix ι ι F).det := by
    rw [det_one]
    exact isUnit_one
  have hdd : ∀ c : F, (diagonal (Function.update (1 : ι → F) i c)).det = c := fun c => by
    rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hDu : ∀ c : F, c ≠ 0 → IsUnit (diagonal (Function.update (1 : ι → F) i c)).det := fun c hc => by
    rw [hdd]
    exact isUnit_iff_ne_zero.mpr hc
  have hmod1 : modF F 1 = 1 := by
    have := good_one h1u
    rw [chiM_one, det_one] at this
    simpa using this.symm
  have hconst : ∀ c : F, c ≠ 0 →
      chiM (transvection i j c) (hT c) = chiM (transvection i j 1) (hT 1) := by
    intro c hc
    have hDD : diagonal (Function.update (1 : ι → F) i c) * diagonal (Function.update (1 : ι → F) i c⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk
        simp [hc]
      · simp [Function.update_of_ne hk]
    have hprod : chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) * chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc)) = 1 := by
      rw [← chiM_mul _ _ _ _ (by rw [hDD]; exact h1u), chiM_congr hDD _ h1u, chiM_one]
    have hu1 : IsUnit (diagonal (Function.update (1 : ι → F) i c) * transvection i j 1).det := by
      rw [det_mul]
      exact (hDu c hc).mul (hT 1)
    have hu2 : IsUnit (diagonal (Function.update (1 : ι → F) i c) * transvection i j 1 * diagonal (Function.update (1 : ι → F) i c⁻¹)).det := by
      rw [← transvection_conj hij hc]
      exact hT c
    rw [chiM_congr (transvection_conj hij hc) (hT c) hu2,
      chiM_mul _ _ hu1 (hDu _ (inv_ne_zero hc)) hu2, chiM_mul _ _ (hDu c hc) (hT 1) hu1]
    calc chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) * chiM (transvection i j 1) (hT 1) *
          chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc))
        = chiM (transvection i j 1) (hT 1) * (chiM (diagonal (Function.update (1 : ι → F) i c)) (hDu c hc) *
          chiM (diagonal (Function.update (1 : ι → F) i c⁻¹)) (hDu _ (inv_ne_zero hc))) := by ring
      _ = chiM (transvection i j 1) (hT 1) := by rw [hprod, mul_one]
  have hc1 : chiM (transvection i j c) (hT c) = 1 := by
    by_cases hc : c = 0
    · subst hc
      rw [chiM_congr (Matrix.transvection_zero (i := i) (j := j)) (hT 0) h1u, chiM_one]
    · have hsq : chiM (transvection i j c) (hT c) * chiM (transvection i j c) (hT c) =
          chiM (transvection i j (c + c)) (hT (c + c)) := by
        rw [← chiM_mul _ _ (hT c) (hT c)
          (by rw [Matrix.transvection_mul_transvection_same (i := i) (j := j) hij]; exact hT _)]
        exact chiM_congr (Matrix.transvection_mul_transvection_same (i := i) (j := j) hij c c) _ _
      have hx0 := (chiM_pos _ (hT c)).ne'
      by_cases h2 : c + c = 0
      · have h0 : chiM (transvection i j (c + c)) (hT (c + c)) = 1 := by
          rw [chiM_congr (show transvection i j (c + c) = 1 by rw [h2, Matrix.transvection_zero])
            (hT (c + c)) h1u, chiM_one]
        rw [h0] at hsq
        exact (pow_left_inj₀ (chiM_pos _ (hT c)).le zero_le_one two_ne_zero).mp (by rw [sq, hsq, one_pow])
      · rw [hconst (c + c) h2, ← hconst c hc] at hsq
        exact mul_left_cancel₀ hx0 (hsq.trans (mul_one _).symm)
  intro h
  rw [chiM_congr rfl h (hT c), hc1, Matrix.det_transvection_of_ne (i := i) (j := j) hij c, hmod1]
  simp
end PI.NglqJacSplitW
