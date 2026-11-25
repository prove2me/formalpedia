-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.ratio_line_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:34.518327+00:00
-- url     : https://prove2.me/submissions/eed9859d-b60a-485b-8a0c-9d91c4446b9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_eq_of_eq_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eq_ratio_smul_on_line

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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0) :
    d.rationalBaseRow c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) *
      ∑ j, d.sH c (MvPolynomial.X (0, j)) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) := by
  have hjc := hd.w_base c
  have hmul : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) =
      ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) * ratio (Ω := Ω c) (d.w j c) (d.w j0 c) := by
    intro j
    have h1 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j c) (hd.w_mem j0 c) hj0
    have h2 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j0 c) (hd.w_mem (d.jc c) c) hjc
    apply ratio_eq_of_eq_smul hjc
    calc d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w j0 c) • d.w j0 c := h1
      _ = ratio (Ω := Ω c) (d.w j c) (d.w j0 c) • (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c) := by
          rw [← h2]
      _ = _ := by rw [smul_smul, mul_comm]
  unfold rationalBaseRow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hmul j, map_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
