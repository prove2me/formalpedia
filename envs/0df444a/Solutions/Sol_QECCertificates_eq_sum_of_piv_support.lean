-- Prove2me | solution 1 for QECCertificates.eq_sum_of_piv_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:14.860528+00:00
-- url     : https://prove2.me/submissions/aee898e1-19c6-420b-ad69-57819cc5279e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_IsReduced_pivot_inj


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {z : Vec n}
    (hz : ∀ i, (∀ ri ∈ D, ri.2 ≠ i) → z i = 0) :
    ∀ m, z m = ∑ rl ∈ D.toFinset, (if rl.2 = m then z rl.2 else 0) := by
  intro m
  by_cases hm : ∃ rl ∈ D, rl.2 = m
  · obtain ⟨rl, hrl, rfl⟩ := hm
    have hsingle : ∑ b ∈ D.toFinset, (if b.2 = rl.2 then z b.2 else 0) = z rl.2 := by
      have h := Finset.sum_eq_single (s := D.toFinset)
        (f := fun b => if b.2 = rl.2 then z b.2 else 0) rl
        (fun b hb hne => by
          rw [if_neg]
          intro hcon
          exact hne (hD.pivot_inj b (List.mem_toFinset.mp hb) rl hrl hcon))
        (fun hnot => absurd (List.mem_toFinset.mpr hrl) hnot)
      rwa [if_pos rfl] at h
    rw [hsingle]
  · have hz0 : z m = 0 := hz m (fun ri hri hcon => hm ⟨ri, hri, hcon⟩)
    have hsum0 : ∑ b ∈ D.toFinset, (if b.2 = m then z b.2 else 0) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [if_neg]
      intro hcon
      exact hm ⟨b, List.mem_toFinset.mp hb, hcon⟩
    rw [hz0, hsum0]
end QECCertificates
