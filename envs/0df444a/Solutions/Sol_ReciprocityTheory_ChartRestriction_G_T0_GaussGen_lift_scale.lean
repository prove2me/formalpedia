-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.lift_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:35:12.506031+00:00
-- url     : https://prove2.me/submissions/50e9e123-f55c-41d2-9b8f-bd57b0e0d5cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_Pimg_succAbove
import Theorems.Thm_BlockPoly_translEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace GaussGen
open MvPolynomial NumberField BlockPoly
section Img
variable {Ω : Type} [Field Ω] {D N : ℕ}
private theorem diag_cS_Pimg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (b : Fin (D + 1)) (μ : Ω)
    (t : TVar D N) :
    diag (cS b μ) (Pimg j₀ x t) = C (if t.1 = b then μ else 1) * Pimg j₀ x t := by
  obtain ⟨i, j⟩ := t
  have hC : ∀ a : Ω, diag (cS (N := N) b μ) (C a) = C a := fun a => by simp [diag]
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
  · rw [Pimg_self]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, diag_X]
      rfl
    · rw [if_neg hi, map_neg, map_sum, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, diag_X, hC, mul_assoc]
      rfl
  · rw [Pimg_succAbove, diag_X]
    rfl
end Img
section Stab
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
end Stab
end GaussGen
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.GaussGen
theorem _root_.solution {K : Type} [Field K] [CharZero K] [Algebra K Ω] (j₀ : Fin (N + 1))
    (x : Fin N → Ω) (b : Fin (D + 1)) (t : TVar D N) :
    diag (cS b (2 : Ω)) (Pimg j₀ x t) = aeval (Pimg j₀ x) (diag (cb b (2 : K)) (X t)) := by
  rw [diag_cS_Pimg, diag_X, map_mul, aeval_X, aeval_C]
  congr 1
  obtain ⟨i, j⟩ := t
  show C (if i = b then (2 : Ω) else 1) = algebraMap K _ (if i = b then (2 : K) else 1)
  split_ifs
  · rw [MvPolynomial.algebraMap_apply]
    congr 1
    exact (map_ofNat (algebraMap K Ω) 2).symm
  · simp
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
