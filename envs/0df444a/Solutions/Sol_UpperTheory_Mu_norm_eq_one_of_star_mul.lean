-- Prove2me | solution 1 for UpperTheory.Mu.norm_eq_one_of_star_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:47.175972+00:00
-- url     : https://prove2.me/submissions/f2db4de9-75b4-4317-98fd-d882f968b6ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
namespace UpperTheory.Mu
theorem _root_.solution [Star K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    {z : K} (h1 : star z * z = 1) (φ : K →+* ℂ) : ‖φ z‖ = 1 := by
  have h3 := congrArg φ h1
  rw [map_mul, hconj, map_one, Complex.conj_mul'] at h3
  have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
end UpperTheory.Mu
