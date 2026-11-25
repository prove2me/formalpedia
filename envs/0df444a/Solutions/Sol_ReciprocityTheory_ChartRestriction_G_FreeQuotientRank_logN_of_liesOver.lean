-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.logN_of_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:45.210023+00:00
-- url     : https://prove2.me/submissions/bfb63d9b-d66b-425a-b259-c7cf92d696ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K₁)} {la : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w la) : logN w = (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * logN la := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨by rw [Ideal.under_def]; exact h.symm⟩
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal la.asIdeal la.isPrime la.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  simp only [logN, hn, Nat.cast_pow, Real.log_pow]
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
