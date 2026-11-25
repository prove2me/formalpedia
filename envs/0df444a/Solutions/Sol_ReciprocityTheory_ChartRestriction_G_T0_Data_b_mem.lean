-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.b_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:36:21.675471+00:00
-- url     : https://prove2.me/submissions/681cd4e2-f374-48eb-b867-015c8186ba80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_admissible_over_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_ratio_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (la : HeightOneSpectrum (𝓞 K)) (k : Fin d.del) (c : ι)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.PlOver la c) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := (d.admissible_over_prime hd h la c w hw).1
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0
end ReciprocityTheory.ChartRestriction.G.T0.Data
