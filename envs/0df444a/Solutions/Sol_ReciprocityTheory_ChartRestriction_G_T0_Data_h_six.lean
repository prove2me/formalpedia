-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.h_six
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:45:51.094835+00:00
-- url     : https://prove2.me/submissions/d392506b-fb0b-4a60-af24-ea6f865c7b90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumLeOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HSix
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Ep_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Ep_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Ep_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aG_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aG_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aG_sb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aG_wx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fsum_le_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_factorization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_pow_mem_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_thp_ne
import Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_T0_Data_wx_mem_c320beb591cc62f2
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c) (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (d.aG h d.wL (d.wx x) : ℝ) ≤ 4 / 3 * d.del ∧
    0 ≤ d.aG h (d.n1 • d.wde) d.et ∧ d.aG h (d.n1 • d.wde) d.et ≤ d.n1 * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h ((2 : ℕ) • d.G1) d.ta1 ∧ d.aG h ((2 : ℕ) • d.G1) d.ta1 ≤ 2 * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h d.wF ta' ∧ d.aG h d.wF ta' ≤ (d.D + 4) * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h d.G2 d.ta2 ∧ d.aG h d.G2 d.ta2 ≤ (d.D + 4) * d.aG h d.wL (d.wx x) := by
  set sb : ∀ c, A c := fun c => d.w (d.jc c) c with hsbdef
  have hsb : ∀ c, sb c ∈ 𝒜 c d.wL ∧ sb c ≠ 0 := fun c => ⟨hd.w_mem _ c, hd.w_base c⟩
  have hwx : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
  have het : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde) ∧ d.et c ≠ 0 := fun c => ⟨hd.et_mem c, hd.et_ne c⟩
  have hta1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 := fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
  have hta2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
  rw [d.aG_wx hd h x hx]
  set aL := d.aG h d.wL sb with haL
  have hde0 : 0 ≤ d.aG h (d.n1 • d.wde) d.et := d.aG_nonneg hd h _ _ fun c v hv => hd.ord_nonneg_et c v hv
  have hG10 : 0 ≤ d.aG h ((2 : ℕ) • d.G1) d.ta1 := d.aG_nonneg hd h _ _ fun c v hv => hd.ordDoubleFirstSection_nonneg c v hv
  have hG20 : 0 ≤ d.aG h d.G2 d.ta2 := d.aG_nonneg hd h _ _ fun c v hv => hd.ordSecondSectionNonneg c v hv
  have hF0 : 0 ≤ d.aG h d.wF ta' := by
    choose k hk using d.thp_ne hd
    have hth : ∀ c, d.thp (k c) c ∈ 𝒜 c d.wF ∧ d.thp (k c) c ≠ 0 := fun c => ⟨hd.thp_mem _ c, hk c⟩
    rw [(d.norm_factorization hd h).2.1 d.wF ta' (fun c => d.thp (k c) c) hta' hth]
    refine d.aG_nonneg hd h _ _ fun c v hv => hd.ord_nonneg_Thp c v hv (d.thp (k c)) ?_ (hk c)
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨k c, rfl⟩

  obtain ⟨a, ha⟩ : ∃ a, d.n1 = a + 1 := ⟨d.n1 - 1, by
    have : 1 ≤ d.n1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := hd.i_ge; omega)
      (by have := hd.g_zero_ge_ask_sum; omega))
    omega⟩
  have hadd1 : (2 * d.n1 : ℤ) * aL = d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.aG h (d.n1 • d.wde) d.et := by
    have hW : (2 * a + 1 + 1) • d.wL = (a + 1) • ((2 : ℕ) • d.G1) + (1 + 1) • (d.n1 • d.wde) := by
      unfold G1; rw [ha]; simp only [smul_sub, ← mul_nsmul]
      rw [show (2 * a + 1 + 1) = (a + 1) * 2 by ring, show (1 + 1) * (a + 1) = (a + 1) * 2 by ring]
      abel
    have m1 := d.pow_mem_ne hd hsb (2 * a + 1)
    have m2 := d.pow_mem_ne hd hta1 a
    have m3 := d.pow_mem_ne hd het 1
    have m23 : ∀ c, (d.ta1 ^ (a + 1) * d.et ^ (1 + 1)) c ∈ 𝒜 c ((a + 1) • ((2 : ℕ) • d.G1) + (1 + 1) • (d.n1 • d.wde)) ∧
        (d.ta1 ^ (a + 1) * d.et ^ (1 + 1)) c ≠ 0 := fun c => by
      haveI := hd.graded c
      exact ⟨SetLike.mul_mem_graded (m2 c).1 (m3 c).1, hd.mul_ne_zero c (m2 c).1 (m3 c).1 (m2 c).2 (m3 c).2⟩
    have m1' : ∀ c, (sb ^ (2 * a + 1 + 1)) c ∈ 𝒜 c ((a + 1) • ((2 : ℕ) • d.G1) + (1 + 1) • (d.n1 • d.wde)) ∧
        (sb ^ (2 * a + 1 + 1)) c ≠ 0 := fun c => by rw [← hW]; exact m1 c
    have e1 := (d.norm_factorization hd h).2.1 _ _ _ m1' m23
    rw [(d.norm_factorization hd h).2.2 _ _ _ _ m2 m3, d.aG_pow hd h hta1, d.aG_pow hd h het, ← hW,
      d.aG_pow hd h hsb] at e1
    rw [← haL] at e1
    have hn : (d.n1 : ℤ) = a + 1 := by rw [ha]; push_cast; ring
    rw [hn]; push_cast at e1 ⊢; linarith
  have hadd2 : ((d.D : ℤ) + 4) * aL = d.aG h d.wF ta' + d.aG h d.G2 d.ta2 := by
    have hW : (d.D + 3 + 1) • d.wL = d.wF + d.G2 := by
      unfold G2; rw [add_sub_cancel]
    have m1 := d.pow_mem_ne hd hsb (d.D + 3)
    have m23 : ∀ c, (ta' * d.ta2) c ∈ 𝒜 c (d.wF + d.G2) ∧ (ta' * d.ta2) c ≠ 0 := fun c => by
      haveI := hd.graded c
      exact ⟨SetLike.mul_mem_graded (hta' c).1 (hta2 c).1,
        hd.mul_ne_zero c (hta' c).1 (hta2 c).1 (hta' c).2 (hta2 c).2⟩
    have m1' : ∀ c, (sb ^ (d.D + 3 + 1)) c ∈ 𝒜 c (d.wF + d.G2) ∧ (sb ^ (d.D + 3 + 1)) c ≠ 0 :=
      fun c => by rw [← hW]; exact m1 c
    have e1 := (d.norm_factorization hd h).2.1 _ _ _ m1' m23
    rw [(d.norm_factorization hd h).2.2 _ _ _ _ hta' hta2, ← hW, d.aG_pow hd h hsb] at e1
    rw [← haL] at e1
    push_cast at e1; linarith

  have hEsum0 : 0 ≤ ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.Ep h c p * (d.dg (d.gen p) : ℤ) :=
    Finset.sum_nonneg fun c _ => finsum_nonneg fun p => finsum_nonneg fun hp =>
      mul_nonneg (d.Ep_nonneg hd h c hp) (Nat.cast_nonneg _)
  have hE : ((∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.Ep h c p * (d.dg (d.gen p) : ℤ) : ℤ) : ℝ) ≤
      d.cc / (2 * d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
    unfold aG
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    refine fsum_le_of _ _ _ ((d.Ep_ne hd h c _ (hsb c).1 (hsb c).2).subset fun p ⟨hp, hs⟩ =>
        ⟨hp, fun h0 => hs (by simp [h0])⟩)
      (((d.good_primes_properties hd h c).2.2.1 _ _ (het c).1 (het c).2).subset fun p ⟨hp, hs⟩ =>
        ⟨hp, fun h0 => hs (by simp [h0])⟩) _ fun p hp => ?_
    have e := d.Ep_le hd h hF1d c hp
    have hdg : (0 : ℝ) ≤ d.dg (d.gen p) := Nat.cast_nonneg _
    push_cast
    calc (d.Ep h c p : ℝ) * d.dg (d.gen p)
        ≤ (d.cc / (2 * d.i) * d.nP h c (d.n1 • d.wde) (d.et c) p) * d.dg (d.gen p) :=
          mul_le_mul_of_nonneg_right e hdg
      _ = _ := by ring
  have haLeq := d.aG_sb hd h
  rw [← haL] at haLeq
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1 : (d.n1 : ℝ) = d.i * d.g0 := by unfold n1; push_cast; ring
  have hcc := hd.cc_nonneg
  have hccg0 := hd.ccg0
  have haL0 : (0 : ℝ) ≤ aL := by rw [haLeq]; exact_mod_cast (by positivity : (0:ℤ) ≤ d.del + _ )
  have e3 : (d.aG h (d.n1 • d.wde) d.et : ℝ) ≤ d.n1 * aL := by
    have : (2 * d.n1 : ℝ) * aL = d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.aG h (d.n1 • d.wde) d.et := by
      exact_mod_cast hadd1
    have h2 : (0 : ℝ) ≤ d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 :=
      mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hG10)
    linarith
  refine ⟨?_, hde0, ?_, hG10, ?_, hF0, ?_, hG20, ?_⟩
  · have k1 : d.cc / (2 * d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) ≤ d.cc / (2 * d.i) * (d.n1 * aL) :=
      mul_le_mul_of_nonneg_left e3 (by positivity)
    have k2 : d.cc / (2 * d.i) * (d.n1 * aL) = d.cc * d.g0 * aL / 2 := by
      rw [hn1]; field_simp
    have k3 : d.cc * d.g0 * (aL : ℝ) ≤ 1 / 2 * aL := mul_le_mul_of_nonneg_right hccg0 haL0
    have k4 : (aL : ℝ) = d.del + ((∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.Ep h c p * (d.dg (d.gen p) : ℤ) : ℤ) : ℝ) := by rw [haLeq]; push_cast; ring
    linarith
  · have : (2 * d.n1 : ℤ) * aL = d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.aG h (d.n1 • d.wde) d.et := hadd1
    nlinarith [Int.natCast_nonneg d.n1]
  · have h1 : (1 : ℤ) ≤ d.n1 := by rw [ha]; push_cast; omega
    nlinarith
  · linarith
  · linarith
end ReciprocityTheory.ChartRestriction.G.T0.Data
