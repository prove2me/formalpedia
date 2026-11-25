-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.w0rat_eq_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:22:40.028682+00:00
-- url     : https://prove2.me/submissions/7f2629a4-c854-400a-a787-2f84d8917c4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sImg_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sImg_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sH_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) :
    d.rationalBaseRow c = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (X (Sum.inl ()) + ∑ k, X (Sum.inr ((0 : Fin (d.D + 1)), k)) * C (d.x c k)) := by
  have hb := hd.w_base c
  have key : ∀ (a b : Ω c) (g : A c), g ≠ 0 → a • g = b • g → a = b := by
    intro a b g hg hab
    by_contra hne
    apply hg
    have h1 : (a - b) • g = 0 := by rw [sub_smul, hab, sub_self]
    have h2 : (a - b)⁻¹ • ((a - b) • g) = g := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    rw [← h2, h1, smul_zero]
  have hr1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by
    have hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c := ⟨1, (one_smul _ _).symm⟩
    unfold ratio
    rw [dif_pos hex]
    exact (key _ _ _ hb ((one_smul _ _).trans hex.choose_spec)).symm
  unfold Data.rationalBaseRow
  rw [Fin.sum_univ_succAbove _ (d.jc c), hr1, map_one, mul_one]
  simp only [sH_X, sImg_succAbove, sImg_base, map_add, map_sum, map_mul]
  congr 1
end ReciprocityTheory.ChartRestriction.G.T0.Data
