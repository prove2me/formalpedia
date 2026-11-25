-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity.gaussAbs_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:41:34.847808+00:00
-- url     : https://prove2.me/submissions/f78554d7-d9dc-4afe-aba5-bcd3ee9716e2

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
open MvPolynomial ReciprocityTheory.MultiplicativeHeights NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
theorem _root_.solution {σ : Type*} (la : HeightOneSpectrum (𝓞 K)) (x : MvPolynomial σ (𝓞 K))
    (hx : x ∉ Ideal.map (C : 𝓞 K →+* MvPolynomial σ (𝓞 K)) la.asIdeal) :
    gaussAbs (FinitePlace.mk la) (MvPolynomial.map (algebraMap (𝓞 K) K) x) = 1 := by
  classical
  rw [MvPolynomial.mem_map_C_iff] at hx
  push_neg at hx
  obtain ⟨s0, hs0⟩ := hx
  have hw : ∀ a : 𝓞 K, FinitePlace.mk la (algebraMap (𝓞 K) K a) ≤ 1 := fun a => by
    rw [FinitePlace.mk_apply]
    exact FinitePlace.norm_le_one K la a
  have hw1 : FinitePlace.mk la (algebraMap (𝓞 K) K (x.coeff s0)) = 1 := by
    rw [FinitePlace.mk_apply]
    exact (FinitePlace.norm_eq_one_iff_notMem K la _).2 hs0
  have hmem : s0 ∈ (MvPolynomial.map (algebraMap (𝓞 K) K) x).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
    intro h0
    rw [h0, map_zero] at hw1
    exact zero_ne_one hw1
  unfold gaussAbs
  apply le_antisymm
  · have h1 : ((MvPolynomial.map (algebraMap (𝓞 K) K) x).support.sup fun s =>
        (FinitePlace.mk la ((MvPolynomial.map (algebraMap (𝓞 K) K) x).coeff s)).toNNReal) ≤ 1 := by
      apply Finset.sup_le
      intro s _
      rw [MvPolynomial.coeff_map]
      exact Real.toNNReal_le_one.2 (hw _)
    exact_mod_cast h1
  · have h1 : (1 : NNReal) ≤ ((MvPolynomial.map (algebraMap (𝓞 K) K) x).support.sup fun s =>
        (FinitePlace.mk la ((MvPolynomial.map (algebraMap (𝓞 K) K) x).coeff s)).toNNReal) := by
      refine Finset.le_sup_of_le hmem ?_
      rw [MvPolynomial.coeff_map, hw1, Real.toNNReal_one]
    exact_mod_cast h1
end ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
