-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.good_valuation_balance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:06:47.818695+00:00
-- url     : https://prove2.me/submissions/c15d1ce1-5b59-4555-9970-3a8894fb968b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_eq_of_eq_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_self_height
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eq_ratio_smul_on_line
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ratio_line_expansion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_PlaceTrivialOrPositive


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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.GoodP c p) :
    WithTop.untopD 0 (w (d.rationalBaseRow c)) + d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = 0 := by
  obtain ⟨hwO, a, ha, hwa⟩ := hw
  rcases d.PlaceTrivialOrPositive hd h c p hp w hwO with htriv | ⟨hAdm, -, j0, hj0, hmin, hY⟩
  · exact absurd (htriv a ha) hwa
  have hjc := hd.w_base c
  have hsm : ∀ j, d.w j c ≠ 0 → ((d.ord c (d.Wres c w) d.wL (d.w j c) : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) + (d.ord c (d.Wres c w) d.wL (d.w j0 c) : WithTop ℤ) := by
    intro j hj
    have hl := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j c) (hd.w_mem j0 c) hj0
    have hr0 : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hl; exact hj hl
    conv_lhs => rw [hl]
    exact hd.ord_smul c _ hAdm _ (hd.w_mem j0 c) hj0 hr0
  have hge : ∀ j, d.w j c ≠ 0 →
      d.ord c (d.Wres c w) d.wL (d.w j0 c) ≤ d.ord c (d.Wres c w) d.wL (d.w j c) := by
    intro j hj
    have h1 : ((d.ord c (d.Wres c w) d.wL (d.w j0 c) : ℤ) : WithTop ℤ) ≤
        (d.ord c (d.Wres c w) d.wL (d.w j c) : WithTop ℤ) := by
      rw [hsm j hj]; exact le_add_of_nonneg_left (hmin j)
    exact_mod_cast h1
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c)) =
      d.ord c (d.Wres c w) d.wL (d.w j0 c) := by
    haveI : Nonempty {j // d.w j c ≠ 0} := ⟨(⟨j0, hj0⟩ : {j // d.w j c ≠ 0})⟩
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · exact le_ciInf fun j => hge j.1 j.2
  have hl1 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j0 c) (hd.w_mem (d.jc c) c) hjc
  have hl2 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem (d.jc c) c) (hd.w_mem j0 c) hj0
  have hprod : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) * ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c) = 1 := by
    have e : d.w j0 c = (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) * ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c)) • d.w j0 c := by
      rw [← smul_smul, ← hl2, ← hl1]
    rw [← ratio_eq_of_eq_smul (Ω := Ω c) hj0 e, ratio_self_height (Ω := Ω c) hj0]
  have hr1ne : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 := fun h0 => by rw [h0, zero_smul] at hl1; exact hj0 hl1
  have hr2ne : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c) ≠ 0 := fun h0 => by rw [h0, zero_smul] at hl2; exact hjc hl2
  obtain ⟨m1, hm1⟩ := WithTop.ne_top_iff_exists.1
    (show d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) ≠ ⊤ from fun h0 => hr1ne ((AddValuation.top_iff _).1 h0))
  obtain ⟨m2, hm2⟩ := WithTop.ne_top_iff_exists.1
    (show d.Wres c w (ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c)) ≠ ⊤ from fun h0 => hr2ne ((AddValuation.top_iff _).1 h0))
  have hsum : ((m1 + m2 : ℤ) : WithTop ℤ) = 0 := by
    rw [WithTop.coe_add, hm1, hm2, ← AddValuation.map_mul, hprod, AddValuation.map_one]
  have hsum' : m1 + m2 = 0 := by exact_mod_cast hsum
  have hjcv := hsm (d.jc c) hjc
  rw [← hm2] at hjcv
  have hjcv' : d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) = m2 + d.ord c (d.Wres c w) d.wL (d.w j0 c) := by
    exact_mod_cast hjcv
  rw [d.ratio_line_expansion hd c j0 hj0, AddValuation.map_mul, hY, add_zero]
  change WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))) + d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = 0
  rw [← hm1, WithTop.untopD_coe]
  unfold ordMM
  rw [hinf, hjcv']
  omega
end ReciprocityTheory.ChartRestriction.G.T0.Data
