-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:57:42.292042+00:00
-- url     : https://prove2.me/submissions/218ef6e0-8cf5-434c-aedf-3b252ac2f387

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
private lemma place_nonneg_lemma_3 (w : FinitePlace K) (x : K) : 0 ≤ w x := by
  first
    | positivity
    | exact AbsoluteValue.nonneg _ _
    | exact w.1.nonneg _
    | exact norm_nonneg _
    | simp
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) (w : FinitePlace K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) =
      ⨆ i : G₀.support, w ((G₀.coeff i : 𝓞 K) : K) := by
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := by
    first
      | exact RingOfIntegers.coe_injective
      | exact IsFractionRing.injective (𝓞 K) K
      | exact FaithfulSMul.algebraMap_injective (𝓞 K) K
  obtain ⟨s0, hs0⟩ := MvPolynomial.ne_zero_iff.mp h
  have hs0' : s0 ∈ G₀.support := MvPolynomial.mem_support_iff.mpr hs0
  have hbdd : BddAbove (Set.range fun i : G₀.support => w ((G₀.coeff i : 𝓞 K) : K)) :=
    (Set.finite_range _).bddAbove
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [MvPolynomial.support_map_of_injective _ hinj]
  simp_rw [MvPolynomial.coeff_map]
  apply le_antisymm
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup G₀.support ⟨s0, hs0'⟩
      (fun s => (w (algebraMap (𝓞 K) K (G₀.coeff s))).toNNReal)
    rw [heq, Real.coe_toNNReal _ (place_nonneg_lemma_3 w _)]
    exact le_ciSup hbdd ⟨i, hi⟩
  · haveI : Nonempty G₀.support := ⟨⟨s0, hs0'⟩⟩
    apply ciSup_le
    rintro ⟨i, hi⟩
    have hle := Finset.le_sup (f := fun s => (w (algebraMap (𝓞 K) K (G₀.coeff s))).toNNReal) hi
    calc w ((G₀.coeff i : 𝓞 K) : K) = ((w (algebraMap (𝓞 K) K (G₀.coeff i))).toNNReal : ℝ) :=
          (Real.coe_toNNReal _ (place_nonneg_lemma_3 w _)).symm
      _ ≤ _ := NNReal.coe_le_coe.mpr hle
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
