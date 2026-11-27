-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_mulSupport_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:38:46.027521+00:00
-- url     : https://prove2.me/submissions/c2d4f399-593c-4dbd-ad4a-36691042ea8e

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
private lemma gaussAbs_of_lemma {κ : Type*} (F : MvPolynomial κ K) (hF : F ≠ 0) (w : FinitePlace K)
    (hw : ∀ s ∈ F.support, w (F.coeff s) = 1) : ReciprocityTheory.MultiplicativeHeights.gaussAbs w F = 1 := by
  have hle : (F.support.sup fun s => (w (F.coeff s)).toNNReal) ≤ 1 :=
    Finset.sup_le fun s hs => by rw [hw s hs]; simp
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
  have hs' : s ∈ F.support := MvPolynomial.mem_support_iff.mpr hs
  have hge : (1 : NNReal) ≤ F.support.sup fun s => (w (F.coeff s)).toNNReal := by
    have h1 := Finset.le_sup (f := fun s => (w (F.coeff s)).toNNReal) hs'
    rw [hw s hs'] at h1
    simpa using h1
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [le_antisymm hle hge]
  simp
private lemma gaussAbs_cover_lemma_2 {κ : Type*} (F : MvPolynomial κ K) (hF : F ≠ 0) :
    (⋃ s ∈ (F.support : Set (κ →₀ ℕ)), Function.mulSupport fun w : FinitePlace K => w (F.coeff s)).Finite ∧
    ∀ w : FinitePlace K, w ∉ (⋃ s ∈ (F.support : Set (κ →₀ ℕ)),
      Function.mulSupport fun w : FinitePlace K => w (F.coeff s)) → ReciprocityTheory.MultiplicativeHeights.gaussAbs w F = 1 := by
  refine ⟨Set.Finite.biUnion F.support.finite_toSet fun s hs =>
    FinitePlace.mulSupport_finite (MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hs)), ?_⟩
  intro w hw
  apply gaussAbs_of_lemma F hF w
  intro s hs
  by_contra hne
  exact hw (Set.mem_biUnion (Finset.mem_coe.mpr hs) (Function.mem_mulSupport.mpr hne))
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type*} (F : MvPolynomial κ K) (hF : F ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K => ReciprocityTheory.MultiplicativeHeights.gaussAbs w F).Finite := by
  obtain ⟨hfin, hone⟩ := gaussAbs_cover_lemma_2 F hF
  refine hfin.subset ?_
  intro w hw
  by_contra hne
  exact (Function.mem_mulSupport.mp hw) (hone w hne)
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
