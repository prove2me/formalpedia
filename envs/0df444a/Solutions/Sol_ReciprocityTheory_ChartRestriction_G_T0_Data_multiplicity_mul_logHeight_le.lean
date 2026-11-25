-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.multiplicity_mul_logHeight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:16.37187+00:00
-- url     : https://prove2.me/submissions/b0f582f0-1d10-491d-90d7-38486dc3f393

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_lr_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_logHeight_generator_lower_bound
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Ep_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Ep_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_nonneg
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    (d.Ep h c p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) ≤
      d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) +
        d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) *
          (d.nP h c (d.n1 • d.wde) (d.et c) p * d.dg (d.gen p)) := by
  by_cases hg : ∃ w, w ∈ d.GoodP c p
  · have hL := d.logHeight_generator_lower_bound hd h c hp hg
    have hE0 : (0 : ℝ) ≤ d.Ep h c p := by exact_mod_cast d.Ep_nonneg hd h c hp
    have hE := d.Ep_le hd h hF1d c hp
    have hn0 : (0 : ℝ) ≤ d.nP h c (d.n1 • d.wde) (d.et c) p := by
      exact_mod_cast d.nP_nonneg hd h c hp _ _ fun v hv => hd.ord_nonneg_et c v hv
    have hi : (0 : ℝ) ≤ d.cc / d.i := div_nonneg hd.cc_nonneg (Nat.cast_nonneg _)
    have hE' : (d.Ep h c p : ℝ) ≤ d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p := by
      have : d.cc / (2 * d.i) = (d.cc / d.i) / 2 := by ring
      rw [this] at hE; nlinarith
    have hlr := d.lr_nonneg
    have hX : (0 : ℝ) ≤ d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by positivity
    set r := d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) - d.Ep h c p
    have hr0 : 0 ≤ r := by linarith
    have hrle : r ≤ d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) := by linarith
    have k1 : -(r * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)) ≤ r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) := by
      nlinarith
    have k2 : r * (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
        d.cc / d.i * (d.nP h c (d.n1 • d.wde) (d.et c) p : ℝ) *
          (d.D * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) :=
      mul_le_mul_of_nonneg_right hrle hX
    have : (d.Ep h c p : ℝ) = d.cc / d.i * d.nP h c (d.n1 • d.wde) (d.et c) p - r := by ring
    rw [this]
    nlinarith
  · push_neg at hg
    have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
    have e1 : d.Ep h c p = 0 := by unfold Ep; rw [hG]; simp
    have e2 : d.nP h c (d.n1 • d.wde) (d.et c) p = 0 := by unfold nP; rw [hG]; simp
    rw [e1, e2]; simp
end ReciprocityTheory.ChartRestriction.G.T0.Data
