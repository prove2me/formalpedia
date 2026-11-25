-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sphereMean_sub_archimedean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:43.567098+00:00
-- url     : https://prove2.me/submissions/604257d9-c59f-4e26-b721-ba294b29799a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightDivMultihomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubArchimedean
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eval_indep_of_first_block
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_logInt_tail
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_mpTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (a b : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hma : IsMultiHomogeneous m a) (hmb : IsMultiHomogeneous m b)
    (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg a) -
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg b) = d.mSgP sg a b := by
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  have hmp := hint_mpTail d.D (d.N + 1) hn
  have key : ∀ q : KTp K d.D d.N, q ≠ 0 → IsMultiHomogeneous m q →
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg q) =
        ∫ w, Real.log ‖d.evT sg 0 (d.tOf w) q‖ ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) ∧
      Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
    intro q hq0 hq
    have hq0' : MvPolynomial.map sg q ≠ 0 := fun h =>
      hq0 (MvPolynomial.map_injective _ sg.injective (by rw [h, map_zero]))
    have hq' : IsMultiHomogeneous m (MvPolynomial.map sg q) :=
      fun s hs => hq s (MvPolynomial.support_map_subset _ _ hs)
    have hI := hint_logInt_tail hn hq0' hq' hm0 0
    have heq : ∀ w, d.evT sg 0 (d.tOf w) q =
        MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg q) := by
      intro w
      rw [MvPolynomial.eval_map]
      rfl
    have hI' : Integrable (fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
        (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
      simp only [heq]
      exact hI
    refine ⟨?_, hI'⟩
    have hpt : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere (d.D + 1) (d.N + 1),
        Real.log ‖MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q)‖ =
          Real.log ‖d.evT sg 0 (d.tOf (fun i : Fin d.D => z i.succ)) q‖ := by
      intro z
      have h1 : MvPolynomial.eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (MvPolynomial.map sg q) =
          d.evT sg (fun j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z 0) j)
            (d.tOf (fun i : Fin d.D => z i.succ)) q := by
        rw [MvPolynomial.eval_map]
        unfold evT
        congr 1
        funext v
        rcases v with ⟨b, j⟩
        cases b using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [h1, d.eval_indep_of_first_block q m hm0 hq sg]
    unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp only [hpt]
    have h2 := MeasureTheory.integral_map (μ := ReciprocityTheory.MultiplicativeHeights.blockSphereProb (d.D + 1) (d.N + 1))
      hmp.measurable.aemeasurable (f := fun w => Real.log ‖d.evT sg 0 (d.tOf w) q‖)
      (by rw [hmp.map_eq]; exact hI'.aestronglyMeasurable)
    rw [hmp.map_eq] at h2
    exact h2.symm
  obtain ⟨ha1, ha2⟩ := key a ha hma
  obtain ⟨hb1, hb2⟩ := key b hb hmb
  rw [ha1, hb1, ← integral_sub ha2 hb2]
  rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
