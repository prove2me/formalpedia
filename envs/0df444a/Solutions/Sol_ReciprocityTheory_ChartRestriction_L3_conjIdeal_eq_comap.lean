-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.conjIdeal_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:19.741872+00:00
-- url     : https://prove2.me/submissions/52dc60fd-487a-4707-b092-4e847f4f6008

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsSqAbsNormOfInert
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_conjO_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  apply le_antisymm
  · rw [Formalism.HermitianLatticesTheory.conjIdeal, Ideal.span_le]
    rintro r ⟨s, hs, h⟩
    show conjO K r ∈ P
    have hrs : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      exact (congrArg star h).trans (star_star _)
    rw [hrs]
    exact hs
  · intro r hr
    rw [Formalism.HermitianLatticesTheory.conjIdeal]
    apply Ideal.subset_span
    refine ⟨conjO K r, hr, ?_⟩
    show (r : K) = star ((conjO K r : 𝓞 K) : K)
    rw [conjO_coe, star_star]
end ReciprocityTheory.ChartRestriction.L3
