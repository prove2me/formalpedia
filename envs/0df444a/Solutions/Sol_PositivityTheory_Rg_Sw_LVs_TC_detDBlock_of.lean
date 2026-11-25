-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.detDBlock_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:32.725583+00:00
-- url     : https://prove2.me/submissions/afcd4746-7a63-458c-87ea-d2202a4e0bfe

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_lhs_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rhs_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (hA : IterAffine) (hS : IterSymm) (hN : IterNested) : DetDBlock := by
  intro m j c c' ψ Ω hΩ h0 hψ
  rw [lhs_eq hA j c c' ψ Ω hΩ h0 hψ, rhs_eq hA hS hN j ψ Ω hΩ h0 hψ]
  congr 1
  rw [← Finset.sum_filter, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => piP j p.1 p.2) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro r
    by_cases hr : r ∈ blkA (n := m) j
    · rw [piP, Equiv.Perm.subtypeCongr.left_apply _ _ hr]
      exact iff_of_true hr (p.1 ⟨r, hr⟩).2
    · rw [piP, Equiv.Perm.subtypeCongr.right_apply _ _ hr]
      exact iff_of_false hr ((eBq j).permCongr p.2 ⟨r, hr⟩).2
  · rintro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h
    simp only at h
    refine Prod.ext (Equiv.ext fun ⟨x, hx⟩ => Subtype.ext ?_) (Equiv.ext fun ⟨x, hx⟩ => ?_)
    · have h1 := DFunLike.congr_fun h x
      rwa [piP, piP, Equiv.Perm.subtypeCongr.left_apply _ _ hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx] at h1
    · have hx' : x ∉ blkA (n := m) j := by simpa [blkB] using hx
      have h1 := DFunLike.congr_fun h x
      rw [piP, piP, Equiv.Perm.subtypeCongr.right_apply _ _ hx', Equiv.Perm.subtypeCongr.right_apply _ _ hx'] at h1
      have he : (eBq j).symm ⟨x, hx'⟩ = ⟨x, hx⟩ := rfl
      have h2 := Subtype.ext h1
      rw [Equiv.permCongr_apply, Equiv.permCongr_apply, he] at h2
      exact (eBq j).injective h2
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨(σ.subtypePerm (fun x => (hσ x).symm), (eBq j).symm.permCongr
      (σ.subtypePerm (p := fun x => x ∉ blkA (n := m) j) (fun x => not_congr (hσ x).symm))), by simp, ?_⟩
    ext x
    by_cases hx : x ∈ blkA (n := m) j
    · simp only [piP]
      rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      rfl
    · simp only [piP]
      rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      rfl
  · intro p _
    simp only [piP, Equiv.Perm.sign_subtypeCongr, Equiv.Perm.sign_permCongr, Units.val_mul, Int.cast_mul]
    congr
    exact Subsingleton.elim _ _
end PositivityTheory.Rg.Sw.LVs.TC
