-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.int_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:47:11.195564+00:00
-- url     : https://prove2.me/submissions/62909a7b-8f09-43f4-af04-a36aa0c61aa1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution (x : K) (h : ∀ w : FinitePlace K, w x ≤ 1) : ∃ y : 𝓞 K, (y : K) = x := by
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v.valuation K x ≤ 1 := by
    intro v
    have h1 := h (FinitePlace.mk v)
    first
      | (rw [FinitePlace.mk_apply, FinitePlace.norm_def] at h1
         have he : (1 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
           have h2 : Ideal.absNorm v.asIdeal ≠ 0 := by
             rw [Ne, Ideal.absNorm_eq_zero_iff]
             exact v.ne_bot
           have h3 : Ideal.absNorm v.asIdeal ≠ 1 := by
             rw [Ne, Ideal.absNorm_eq_one_iff]
             exact v.isPrime.ne_top
           have h4 : 1 < Ideal.absNorm v.asIdeal := by omega
           exact_mod_cast h4
         have h5 : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
           first
             | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
             | exact v.valuedAdicCompletion_eq_valuation' x
             | exact FinitePlace.valuation_embedding v x
             | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v x
             | rfl
         rw [h5] at h1
         exact (WithZeroMulInt.toNNReal_le_one_iff he).mp (by exact_mod_cast h1))
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x hv
  exact ⟨y, hy⟩
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
