-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.aG_frame_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:43.639111+00:00
-- url     : https://prove2.me/submissions/cb1384fb-7bf3-4bf0-bd04-503826905e14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AGFrameNonneg
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_use__fb60b9f90987
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_eq_ratio_smul_on_line
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_key_degree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_eq_of_eq_smul
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) : 0 ≤ d.aG h d.wF hd.a4.choose := by
  classical
  have hespec := hd.a4.choose_spec
  unfold aG
  refine Finset.sum_nonneg fun c _ => ?_
  have hec : hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hespec.1 c
  have hk : ∃ k, d.thp (hd.sel k) c ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨q, hq, p, hp⟩ := hespec.2.2 (fun _ => 1)
    have e1 := hp c
    simp only [mul_one] at e1
    apply hq c
    rw [e1]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hno k, ratio_eq_of_eq_smul hec.2 (zero_smul (Ω c) (hd.a4.choose c)).symm, map_zero, mul_zero]
  obtain ⟨k, hk⟩ := hk
  have htm : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  have hr := eq_ratio_smul_on_line d (hd := hd) htm hec.1 hec.2
  have hr0 : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) ≠ 0 := by
    intro h0
    apply hk
    rw [hr, h0, zero_smul]
  have hthpmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  have hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v d.wF (d.thp (hd.sel k) c) :=
    fun v hv => hd.ord_nonneg_Thp c v hv _ hthpmem hk
  have x2 := d.good_primes_properties hd h c
  have hsplit : ∀ p ∈ d.HtOne, d.nP h c d.wF (d.thp (hd.sel k) c) p =
      d.nP h c d.wF (hd.a4.choose c) p +
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) *
          WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c))) := by
    intro p hp
    have e2 := d.nP_smul hd h c hec.1 hec.2 hr0 hp
    rw [← hr] at e2
    exact e2
  have hkey := d.key_degree hd h c _ hr0
  have hfe := x2.2.2.1 _ _ hec.1 hec.2
  have hfm := d.use₈ hd h c _ hr0
  have eq1 : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ)) =
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c d.wF (hd.a4.choose c) p * (d.dg (d.gen p) : ℤ)) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          (d.fze h c w : ℤ) *
            WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c)))) *
          (d.dg (d.gen p) : ℤ) := by
    rw [← finsum_mem_add_distrib' ?_ ?_]
    · exact finsum_mem_congr rfl fun p hp => by rw [hsplit p hp, add_mul]
    · refine hfe.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
    · refine hfm.subset ?_
      rintro p ⟨hp, hne⟩
      exact ⟨hp, fun h0 => hne (by simp [h0])⟩
  have hnn : 0 ≤ ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.nP h c d.wF (d.thp (hd.sel k) c) p * (d.dg (d.gen p) : ℤ) :=
    finsum_nonneg fun p => finsum_nonneg fun hp =>
      mul_nonneg (d.nP_nonneg hd h c hp _ _ hord) (Nat.cast_nonneg _)
  rw [eq1, hkey, add_zero] at hnn
  exact hnn
end ReciprocityTheory.ChartRestriction.G.T0.Data
