-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.exists_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:31.846324+00:00
-- url     : https://prove2.me/submissions/cf924797-2c5c-4e18-9995-206bf0982e62

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
import Theorems.Thm_GroundTheory_Automorphic_eq_sum_indicator_coset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply

set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
namespace PositivityTheory.RgUd.T2.HaarDistr
theorem _root_.solution (K : OpenSubgroup G) (hKc : IsCompact (K : Set G)) (f : SB G)
    (hK : ∀ g, ∀ k ∈ K, (f : G → ℂ) (g * k) = (f : G → ℂ) g) :
    ∃ s : ℂ, ∀ Φ : SB G →ₗ[ℂ] ℂ, (∀ (g : G) (α : SB G), Φ (transl g α) = Φ α) →
      Φ f = s * Φ (ind K hKc) := by
  classical
  have hf : HasCompactSupport (f : G → ℂ) := f.2.2
  set t := (finite_image_mk_tsupport K hf).toFinset with ht
  have key : f = ∑ x ∈ t, ((f : G → ℂ) x.out) • transl x.out (ind K hKc) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    refine (eq_sum_indicator_coset K hf hK).trans (Finset.sum_congr rfl fun x _ => ?_)
    funext y
    show (x.out • (K : Set G)).indicator (fun _ => (f : G → ℂ) x.out) y =
      (f : G → ℂ) x.out * (K : Set G).indicator (fun _ => (1 : ℂ)) (x.out⁻¹ • y)
    by_cases hy : y ∈ x.out • (K : Set G)
    · have hy' : x.out⁻¹ • y ∈ (K : Set G) := Set.mem_smul_set_iff_inv_smul_mem.1 hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy', mul_one]
    · have hy' : x.out⁻¹ • y ∉ (K : Set G) := fun h => hy (Set.mem_smul_set_iff_inv_smul_mem.2 h)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy', mul_zero]
  refine ⟨∑ x ∈ t, (f : G → ℂ) x.out, fun Φ hΦ => ?_⟩
  conv_lhs => rw [key]
  rw [_root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, hΦ, smul_eq_mul]
end PositivityTheory.RgUd.T2.HaarDistr
