-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.formal_log_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:27:09.907295+00:00
-- url     : https://prove2.me/submissions/0bfea624-168b-4109-b6d6-b55c9a55027b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germComp1_germComp1_eq_substitute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_germCompOne_identityPoint_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_formal_exp_law
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_composition_identity_point_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_add_at
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_addition_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
open Formalism.FG.SolveVAux
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : LogUniqueSt := by
  intro k _ _ d G ℓ ℓ' h0 h1 hadd h0' h1' hadd'
  classical
  obtain ⟨ε, ⟨hε0, -, hεL, hLε⟩, htr⟩ := formal_exp_law k d G ℓ h0 h1 hadd
  have hp2 : ∀ (l : Fin 2) (i : Fin d), constantCoeff (pt k (n := 2) d l i) = 0 := fun l i => cc_pt l i
  have hsum0 : ∀ i, constantCoeff ((pt k (n := 2) d 0 + pt k (n := 2) d 1) i) = 0 := fun i => by simp [pt]
  have hεp : ∀ (l : Fin 2) i, constantCoeff (comp1 ε (pt k (n := 2) d l) i) = 0 := fun l i =>
    cc_comp1 ε _ hε0 (hp2 l) i

  have hA : addOf G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) =
      comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) := by
    have hAc : ∀ i, constantCoeff (addOf G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) i) = 0 :=
      fun i => cc_ev _ (fun j i => by fin_cases j <;> exact hεp _ i) (G.const i)
    have e : comp1 ℓ (addOf G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1))) =
        pt k (n := 2) d 0 + pt k (n := 2) d 1 := htr
    have e2 := congrArg (comp1 ε) e
    rw [germComp1_germComp1_eq_substitute ε ℓ _ h0 hAc, hεL, germCompOne_identityPoint_left _ hAc] at e2
    exact e2
  set δ := comp1 ℓ' ε with hδ
  have hδ0 : ∀ i, constantCoeff (δ i) = 0 := fun i => cc_comp1 ℓ' ε h0' hε0 i
  have hδadd : comp1 δ (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 δ (pt k (n := 2) d 0) + comp1 δ (pt k (n := 2) d 1) := by
    rw [hδ, ← germComp1_germComp1_eq_substitute ℓ' ε _ hε0 hsum0, ← germComp1_germComp1_eq_substitute ℓ' ε _ hε0 (hp2 0), ← germComp1_germComp1_eq_substitute ℓ' ε _ hε0 (hp2 1), ← hA]
    exact add_at G ℓ' hadd' _ _ (hεp 0) (hεp 1)
  have hdε : dLin ε = 1 := by
    have := dLin_comp1 ℓ ε hε0
    rw [hLε, h1, _root_.one_mul] at this
    rw [← this]
    refine Matrix.ext fun i j => ?_
    simp only [dLin, pt, Matrix.one_apply, coeff_X, Finsupp.single_left_inj one_ne_zero, Prod.mk.injEq, true_and]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hdδ : dLin δ = 1 := by rw [hδ, dLin_comp1 ℓ' ε hε0, h1', hdε, _root_.one_mul]
  have hδid : δ = pt k d 0 := by
    funext i
    ext e
    rcases eq_or_ne e.degree 1 with he | he
    · obtain ⟨⟨j0, j⟩, rfl⟩ := degree_eq_one e he
      have hj0 : j0 = 0 := Subsingleton.elim _ _
      subst hj0
      have := congrFun (congrFun hdδ i) j
      simp only [dLin, Matrix.one_apply] at this
      rw [this]
      simp only [pt, coeff_X, Finsupp.single_left_inj one_ne_zero, Prod.mk.injEq, true_and]
      by_cases h : i = j
      · simp [h]
      · simp [h, Ne.symm h]
    · rw [addition_linear k d (δ i) (congrFun hδadd i) e he]
      simp only [pt, coeff_X]
      rw [if_neg]
      rintro rfl
      exact he (Finsupp.degree_single _ _)
  calc ℓ = comp1 (pt k d 0) ℓ := (germCompOne_identityPoint_left ℓ h0).symm
    _ = comp1 (comp1 ℓ' ε) ℓ := by rw [← hδ, hδid]
    _ = comp1 ℓ' (comp1 ε ℓ) := (germComp1_germComp1_eq_substitute ℓ' ε ℓ hε0 h0).symm
    _ = ℓ' := by rw [hεL, composition_identity_point_right]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
