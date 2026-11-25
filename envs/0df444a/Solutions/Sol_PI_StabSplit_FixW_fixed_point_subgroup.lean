-- Prove2me | solution 1 for PI.StabSplit.FixW.fixed_point_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:34:46.817818+00:00
-- url     : https://prove2.me/submissions/ddb51e9e-997c-4a0d-bc99-1e6ed5224dda

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_FixSub
import Theorems.Thm_PI_StabSplit_FixW_mulVec_bvec
import Theorems.Thm_PI_StabSplit_FixW_fix_col
import Theorems.Thm_PI_StabSplit_FixW_uOf_UW
import Theorems.Thm_PI_StabSplit_FixW_uOf_yv
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.FixW
namespace PI.StabSplit.FixW
theorem _root_.solution : FixSub := by
  intro k r z hz g hg
  have hu := uOf_UW hz hg
  have hH : (Hpk k r).det ≠ 0 := by
    have h2 := congrArg Matrix.det (Hpk_sq k r)
    rw [det_mul, det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have hdet : IsUnit (uOf k r g).det := by
    have h := congrArg Matrix.det hu.1
    rw [det_mul, det_mul, det_conjTranspose] at h
    refine isUnit_iff_ne_zero.mpr (fun h0 => hH ?_)
    rw [← h, h0, mul_zero]
  refine ⟨uOf k r g, hu, (uOf k r g)⁻¹ * g, ?_, ?_⟩
  · have hm : (uOf k r g)⁻¹ * g ∈ UH (Hpk k r) := by
      have hinv := (uHGroup (2 * r + k + 1) (Hpk k r) (isUnit_iff_ne_zero.mpr hH)).2
      exact hinv.1 _ (hinv.2 _ hu.1).2 _ hg.1
    refine ⟨hm, fun a i hi => ?_, fun i j h1 h2 h3 => ?_⟩
    · have e : (eI k r a).val < r := by simp [eI]
      have hy := congrFun (uOf_yv hg (eI k r a) (by omega)) i
      have hc : ((uOf k r g)⁻¹ * g) i (eI k r a) = yv k r g (eI k r a) i := by
        rw [← congrFun (mulVec_bvec ((uOf k r g)⁻¹ * g) (eI k r a)) i, ← mulVec_mulVec,
          mulVec_bvec g, ← uOf_yv hg (eI k r a) (by omega), mulVec_mulVec,
          nonsing_inv_mul _ hdet, one_mulVec]
      rw [hc]; simp only [yv]
      by_cases hir : i.val < r
      · rw [if_pos hir, fix_col hg _ e i]
      · rw [if_neg hir]
    · have hc : ((uOf k r g)⁻¹ * g) i j = yv k r g j i := by
        rw [← congrFun (mulVec_bvec ((uOf k r g)⁻¹ * g) j) i, ← mulVec_mulVec,
          mulVec_bvec g, ← uOf_yv hg j h2, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
      rw [hc]; simp only [yv, if_neg (show ¬ i.val < r by omega)]
  · rw [← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]
end PI.StabSplit.FixW
