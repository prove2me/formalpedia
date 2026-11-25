-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.blockPoint_eq_evT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:14.196891+00:00
-- url     : https://prove2.me/submissions/67af9281-10ed-4af3-aeaf-a8f2cc55e1d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (sg : K →+* ℂ) (z : BlockSphere (d.D + 1) (d.N + 1)) (q : KTp K d.D d.N) :
    eval (blockPoint z) (MvPolynomial.map sg q) =
      d.evT sg (spherePoint (z 0)) (d.tOf ((ReciprocityTheory.MultiplicativeHeights.lh0Split d.D (d.N + 1) z).2)) q := by
  rw [MvPolynomial.eval_map]
  unfold Data.evT
  congr 1
  funext v
  obtain ⟨i, j⟩ := v
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    show spherePoint (z i.succ) j = spherePoint (z (Fin.succAbove 0 i)) j
    rw [Fin.succAbove_zero]
end ReciprocityTheory.ChartRestriction.G.T0.Data
