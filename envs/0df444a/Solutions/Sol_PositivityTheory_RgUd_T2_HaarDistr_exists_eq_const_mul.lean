-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.exists_eq_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:38.73152+00:00
-- url     : https://prove2.me/submissions/cf2d7685-3570-4678-8464-e9c4e2831af4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_exists_sum_eq
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_right
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset

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
theorem _root_.solution (Φ Ψ : SB G →ₗ[ℂ] ℂ)
    (hΦ : ∀ (g : G) (α : SB G), Φ (transl g α) = Φ α)
    (hΨ : ∀ (g : G) (α : SB G), Ψ (transl g α) = Ψ α)
    (h0 : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), Ψ (ind K hK) ≠ 0) :
    ∃ c : ℂ, ∀ α : SB G, Φ α = c * Ψ α := by
  obtain ⟨K₀, hK₀, -⟩ := exists_openSubgroup_isCompact_subset (G := G) (Filter.univ_mem)
  refine ⟨Φ (ind K₀ hK₀) / Ψ (ind K₀ hK₀), fun α => ?_⟩
  obtain ⟨K₁, -, hK₁⟩ := exists_forall_mul_right (R := ℂ) (show (α : G → ℂ) ∈
    locallyConstantCompactSupport G ℂ ℂ from α.2)
  have hKc : IsCompact ((K₁ ⊓ K₀ : OpenSubgroup G) : Set G) :=
    hK₀.of_isClosed_subset (K₁ ⊓ K₀).isClosed fun x hx => (OpenSubgroup.mem_inf.1 hx).2
  obtain ⟨s, hs⟩ := exists_sum_eq (K₁ ⊓ K₀) hKc α
    (fun g k hk => hK₁ g k (OpenSubgroup.mem_inf.1 hk).1)
  obtain ⟨r, hr⟩ := exists_sum_eq (K₁ ⊓ K₀) hKc (ind K₀ hK₀) (fun g k hk => by
    have hk' : k ∈ K₀ := (OpenSubgroup.mem_inf.1 hk).2
    change (K₀ : Set G).indicator (fun _ => (1 : ℂ)) (g * k) =
      (K₀ : Set G).indicator (fun _ => (1 : ℂ)) g
    by_cases hg : g ∈ (K₀ : Set G)
    · have : g * k ∈ (K₀ : Set G) := K₀.mul_mem hg hk'
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem this]
    · have : g * k ∉ (K₀ : Set G) := fun h => hg (by
        simpa using K₀.mul_mem h (K₀.inv_mem hk'))
      rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem this])
  have a1 := hs Φ hΦ
  have a2 := hs Ψ hΨ
  have b1 := hr Φ hΦ
  have b2 := hr Ψ hΨ
  have hne := h0 _ hK₀
  have hne' := h0 _ hKc
  have hrne : r ≠ 0 := by
    rintro rfl
    exact hne (by simpa using b2)
  rw [a1, a2, b1, b2]
  field_simp
end PositivityTheory.RgUd.T2.HaarDistr
