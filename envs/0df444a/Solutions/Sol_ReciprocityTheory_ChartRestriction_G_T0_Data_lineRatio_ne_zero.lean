-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.lineRatio_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:24.533026+00:00
-- url     : https://prove2.me/submissions/a90c8a17-7ba0-4cb5-9b9b-7ced0b88eef6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_self_height

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) : d.rationalBaseRow c ≠ 0 := by
  have hr1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := ratio_self_height (hd.w_base c)
  have e : d.rationalBaseRow c = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (MvPolynomial.X (Sum.inl ()) + ∑ k, MvPolynomial.X (Sum.inr ((0 : Fin (d.D + 1)), k)) *
        MvPolynomial.C (ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c))) := by
    unfold rationalBaseRow sH sHom
    rw [Fin.sum_univ_succAbove _ (d.jc c)]
    simp only [MvPolynomial.aeval_X, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, if_true, hr1, map_one, mul_one, map_add, map_sum, map_mul]
    congr 1
  rw [e]
  intro h0
  have hinj := IsFractionRing.injective (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
  rw [← map_zero (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N))] at h0
  have h1 := congrArg (MvPolynomial.coeff (Finsupp.single (Sum.inl ()) 1)) (hinj h0)
  simp [MvPolynomial.coeff_X', MvPolynomial.coeff_sum, MvPolynomial.coeff_X_mul', Finsupp.single_eq_single_iff] at h1
end ReciprocityTheory.ChartRestriction.G.T0.Data
