-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.map_evW_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:50.565176+00:00
-- url     : https://prove2.me/submissions/2afcaa00-6e93-4568-b142-15a08e7d2bd4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffEvWMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
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



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (Q : MvPolynomial (UXVar d.D d.N) (𝓞 K)) :
    MvPolynomial.map (Pi.evalRingHom A c) (evW (R := 𝓞 K) (D := d.D) d.w Q) = d.evc c (mapK Q) := by
  haveI := hd.towerO c
  have key : (MvPolynomial.map (Pi.evalRingHom A c)).comp
      (evW (R := 𝓞 K) (D := d.D) d.w).toRingHom =
      (d.evc c).toRingHom.comp (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evW, Data.evc,
        MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_apply]
      congr 1
    · intro v
      cases v <;> simp [evW, Data.evc]
  exact RingHom.congr_fun key Q
end ReciprocityTheory.ChartRestriction.G.T0.Data
