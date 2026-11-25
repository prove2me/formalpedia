-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finsum_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:22.167047+00:00
-- url     : https://prove2.me/submissions/f2743034-1767-447b-88a1-358f0ad3deee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_liesOver_iff_under
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_logN_of_liesOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution (F : HeightOneSpectrum (𝓞 K₁) → ℝ) (hF : (Function.support F).Finite) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K),
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la =
      ∑ᶠ w, F w * logN w := by
  classical
  set S := hF.toFinset
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S.image under
  have hinner : ∀ la : HeightOneSpectrum (𝓞 K),
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1 =
        ∑ w ∈ S.filter (fun w => under (K := K) w = la),
          (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w := by
    intro la
    rw [finsum_eq_sum_of_support_subset _ (s := S.subtype (fun w => LiesOver w la)) ?_,
      Finset.sum_subtype_eq_sum_filter
        (fun w : HeightOneSpectrum (𝓞 K₁) => (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w)]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext w; simp [liesOver_iff_under]
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      exact hw (by simp [h0])
  have hsupp : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) ⊆ T := by
    intro la hla
    rw [Function.mem_support, hinner] at hla
    obtain ⟨w, hw, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hla
    rw [Finset.mem_filter] at hw
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw.1, hw.2⟩)
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := T) (fun la hla => hsupp (by
      intro h; apply hla; simp [h])),
    finsum_eq_sum_of_support_subset _ (s := S) (fun w hw => by
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, S]
      intro h; apply hw; simp [h])]
  simp_rw [hinner, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := under)
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [logN_of_liesOver ((liesOver_iff_under w la).mpr hw.2)]
  ring
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
