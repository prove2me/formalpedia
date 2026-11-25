-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rootDiscr_pow_eq_sqrt_discr_9399e9c24fe2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:49.952035+00:00
-- url     : https://prove2.me/submissions/3f78b34c-313b-4d19-9438-876bdf71004e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    rootDiscriminant K ^ InfinitePlace.nrComplexPlaces K = Real.sqrt |(discr K : ℝ)| := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h1
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (InfinitePlace.nrComplexPlaces K : ℝ) := by
    exact_mod_cast h1.symm
  have hc : (InfinitePlace.nrComplexPlaces K : ℝ) ≠ 0 := by
    have : 0 < InfinitePlace.nrComplexPlaces K := by omega
    exact_mod_cast this.ne'
  unfold rootDiscriminant
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hn, Real.sqrt_eq_rpow]
  congr 1
  field_simp
end Formalism.MainNotions.BridgeLemma₂
