-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sphereMean_substituted_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:17:17.589884+00:00
-- url     : https://prove2.me/submissions/0770af8b-edfb-49af-a1ce-630becec1947

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintLogFinprod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubstitutedEqIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eval_substituted_shift_invariant
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isProbabilityMeasure_sphereProb
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
open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (x : Fin (d.N + 1) → K) (F : KTp K d.D d.N) (sg : K →+* ℂ) :
    blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) =
      ∫ z, Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F))‖
        ∂(blockSphereProb d.D (d.N + 1)) := by
  have hpt : ∀ z : BlockSphere (d.D + 1) (d.N + 1),
      MvPolynomial.eval (blockPoint z) (MvPolynomial.map sg (d.translatedForm x F)) =
        MvPolynomial.eval (hintPt 0 (Fin.tail z)) (MvPolynomial.map sg (d.translatedForm x F)) := by
    intro z
    rw [← eval_substituted_shift_invariant d x F sg (spherePoint (z 0)) (Fin.tail z)]
    refine congrArg (fun y => MvPolynomial.eval y (MvPolynomial.map sg (d.translatedForm x F)))
      (funext fun v => ?_)
    obtain ⟨a, b⟩ := v
    cases a using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have key : ∀ g : (Fin d.D → UnitSphereC (d.N + 1)) → ℝ,
      ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) =
        ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
    intro g
    haveI hpr : IsProbabilityMeasure (sphereProb (d.N + 1)) :=
      ReciprocityTheory.MultiplicativeHeights.isProbabilityMeasure_sphereProb (Nat.succ_pos _)
    haveI hfin : IsFiniteMeasure (sphereProb (d.N + 1)) :=
      ⟨by rw [MeasureTheory.measure_univ]; exact ENNReal.one_lt_top⟩
    haveI hsf : SigmaFinite (sphereProb (d.N + 1)) :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite _ _ _ hfin
    haveI hsf' : ∀ i : Fin (d.D + 1), SigmaFinite ((fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) i) :=
      fun _ => hsf
    have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
      (fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) 0
    calc ∫ z, g (Fin.tail z) ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1))
        = ∫ z, (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
            (MeasurableEquiv.piFinSuccAbove (fun _ => UnitSphereC (d.N + 1)) 0 z)
            ∂(Measure.pi fun _ : Fin (d.D + 1) => sphereProb (d.N + 1)) := by
          congr 1
      _ = ∫ p, g p.2 ∂((sphereProb (d.N + 1)).prod
            (Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1))) :=
          hmp.integral_comp' (fun p : UnitSphereC (d.N + 1) × (Fin d.D → UnitSphereC (d.N + 1)) => g p.2)
      _ = ∫ w, g w ∂(Measure.pi fun _ : Fin d.D => sphereProb (d.N + 1)) := by
          rw [MeasureTheory.integral_fun_snd]
          simp
  unfold blockSphereMean blockSphereProb
  simp_rw [hpt]
  exact key (fun w => Real.log ‖MvPolynomial.eval (hintPt 0 w) (MvPolynomial.map sg (d.translatedForm x F))‖)
end ReciprocityTheory.ChartRestriction.G.T0.Data
