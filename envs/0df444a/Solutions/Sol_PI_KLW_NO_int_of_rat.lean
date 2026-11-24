-- Prove2me | solution 1 for PI.KLW.NO.int_of_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:07.834268+00:00
-- url     : https://prove2.me/submissions/07ce222a-c323-45d7-9354-fa3aaf407924

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_mem_O_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] (q : ℚ)
    (h : (q : K) ∈ (algebraMap (𝓞 K) K).range) : ∃ m : ℤ, q = m := by
  have h1 : IsIntegral ℤ (algebraMap ℚ K q) := by
    rw [eq_ratCast]; exact mem_O_iff.1 h
  rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at h1
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact ⟨m, by rw [← hm]; simp⟩
end PI.KLW.NO
