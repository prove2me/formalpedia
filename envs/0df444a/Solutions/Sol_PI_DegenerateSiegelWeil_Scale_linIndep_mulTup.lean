-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.linIndep_mulTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:54.41205+00:00
-- url     : https://prove2.me/submissions/171290df-d2f1-4350-b4dc-0ef66ca7e771

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_mulTup_apply_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix
variable {K : Type} [CommRing K] {n M : ℕ}
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (D : (Matrix (Fin n) (Fin n) K)ˣ) {X : Fin n → Fin M → K}
    (hX : LinearIndependent K X) : LinearIndependent K (mulTup (D : Matrix (Fin n) (Fin n) K) X) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro c hc
  have key : ∑ j, c j • mulTup (D : Matrix (Fin n) (Fin n) K) X j =
      ∑ k, Matrix.mulVec (D : Matrix (Fin n) (Fin n) K) c k • X k := by
    simp only [mulTup_apply_eq_sum, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have h0 : Matrix.mulVec (D : Matrix (Fin n) (Fin n) K) c = 0 := funext (hX _ (key ▸ hc))
  have hc0 : c = 0 := by
    have h1 := congrArg (Matrix.mulVec ((D⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K)) h0
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  intro j
  rw [hc0]
  rfl
end PI.DegenerateSiegelWeil.Scale
