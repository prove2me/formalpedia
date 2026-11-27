-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.la_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:15:31.05285+00:00
-- url     : https://prove2.me/submissions/3e86e7cf-ff95-49b2-9b88-229691d3728f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HFour
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogNormNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntegralLeOfAeLeAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CardEmbPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_ordMM_fin
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Nla_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aNla_supp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_la_fin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    (∑ᶠ la, d.NlaG h d.wL f la * logNorm la) ≤ (∑ᶠ la, d.NlaMM h f la * logNorm la) +
      d.del * (∑ᶠ la, d.nu la * logNorm la) +
      d.cc / d.i * (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) := by
  have hln : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la :=
    fun la => Real.log_natCast_nonneg _

  have finG : ∀ (G : WT) (ta : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (Function.support (fun la => d.NlaG h G ta la * logNorm la)).Finite := by
    intro G ta hta
    have h1 : (Function.support (d.NlaG h G ta)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ord c v G (ta c)) (hd.a3' c (hta c).1 (hta c).2)) ?_
      exact d.aNla_supp hd h (fun c v g => d.ord c v G g) ta
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finMM : (Function.support (fun la => d.NlaMM h f la * logNorm la)).Finite := by
    have h1 : (Function.support (d.NlaMM h f)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ordMM c v (f c)) ?_) ?_
      · refine (d.ordMM_fin hd c (f c) (hf c).1 (hf c).2).subset ?_
        rintro v ⟨hv, hne⟩
        exact ⟨hv, Int.cast_ne_zero.mpr hne⟩
      · exact d.aNla_supp hd h (fun c v g => d.ordMM c v g) f
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finNu : (Function.support (fun la => d.nu la * logNorm la)).Finite :=
    hH1.2.1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finL := finG d.wL f hf
  have finE := finG (d.n1 • d.wde) d.et (fun c => ⟨hd.et_mem c, hd.et_ne c⟩)
  have finAll := finMM.union (finNu.union finE)

  have key : ∑ᶠ la, d.NlaG h d.wL f la * logNorm la ≤
      ∑ᶠ la, (d.NlaMM h f la * logNorm la + d.del * (d.nu la * logNorm la) +
        d.cc / d.i * (d.NlaG h (d.n1 • d.wde) d.et la * logNorm la)) := by
    refine finsum_le_finsum' finL (finAll.subset fun x hx => ?_) fun la => ?_
    · by_contra hn
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
      apply hx
      simp [hn.1, hn.2.1, hn.2.2]
    · have := mul_le_mul_of_nonneg_right (d.Nla_le hd h hH1 f la) (hln la)
      exact this.trans_eq (by ring)
  refine key.trans_eq ?_
  rw [finsum_add_distrib, finsum_add_distrib, mul_finsum, mul_finsum]
  all_goals
    refine finAll.subset fun x hx => ?_
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hx
    simp [hn.1, hn.2.1, hn.2.2]
end ReciprocityTheory.ChartRestriction.G.T0.Data
