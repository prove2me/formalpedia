-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_flatW__52449b1b4fd3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:55:42.737571+00:00
-- url     : https://prove2.me/submissions/1289864b-8b20-4261-8374-5c7fc13f46ab

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_MulIterateRootEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_ZmodTrichotomy
import Theorems.Thm_ReciprocityTheory_PGsh_flat_of_ann
import Theorems.Thm_ReciprocityTheory_PGsh_mem_span_p_iff
import Theorems.Thm_ReciprocityTheory_PGsh_p_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh
theorem _root_.solution : FlatW'Statement p O := by
  intro pflat _
  set T : WittVector p (PreTilt O p) := teichmuller p pflat with hT
  set I : Ideal (WittVector p (PreTilt O p)) := span {(p : WittVector p (PreTilt O p)) ^ 2, T} with hI
  have hpc : ((p : ℕ) : WittVector p (PreTilt O p) ⧸ I) = Ideal.Quotient.mk I (p : WittVector p (PreTilt O p)) :=
    (map_natCast _ p).symm
  have hTI : Ideal.Quotient.mk I T = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (subset_span (by simp))
  have hann : ∀ x : WittVector p (PreTilt O p) ⧸ I, (p : WittVector p (PreTilt O p) ⧸ I) * x = 0 →
      ∃ y, x = (p : WittVector p (PreTilt O p) ⧸ I) * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hpc, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, mem_span_pair] at hx
    obtain ⟨c, d, hcd⟩ := hx
    have hd : d - teichmuller p (d.coeff 0) ∈ span {(p : WittVector p (PreTilt O p))} := by
      rw [mem_span_p_iff]
      have : constantCoeff (d - teichmuller p (d.coeff 0)) = 0 := by
        rw [map_sub, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero, sub_self]
      exact this
    obtain ⟨e, he⟩ := mem_span_singleton'.1 hd
    have h1 : teichmuller p (d.coeff 0) * T = (a - c * p - e * T) * p := by
      have hd' : d = teichmuller p (d.coeff 0) + e * p := by rw [he]; ring
      rw [hd'] at hcd
      linear_combination hcd
    have h2 : teichmuller p (d.coeff 0) * T = 0 := by
      have hm : teichmuller p (d.coeff 0) * T ∈ span {(p : WittVector p (PreTilt O p))} :=
        mem_span_singleton'.2 ⟨_, h1.symm⟩
      rw [mem_span_p_iff, mul_coeff_zero, hT, teichmuller_coeff_zero, teichmuller_coeff_zero] at hm
      rw [hT, ← map_mul, hm, teichmuller_zero]
    have h3 : a = c * p + e * T := by
      have := p_mul_eq_zero _ (h1.symm.trans h2)
      linear_combination this
    refine ⟨Ideal.Quotient.mk I c, ?_⟩
    rw [hpc, h3, map_add, map_mul, map_mul, hTI]
    ring
  refine ⟨?_, ?_, hann, ?_⟩
  · apply le_antisymm
    · rw [span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mem_span_pair.2 ⟨1, 2 * p - T, by ring⟩, subset_span (by simp)⟩
    · rw [span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨mem_span_pair.2 ⟨1, T - 2 * p, by ring⟩, subset_span (by simp)⟩
  · rw [hpc, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact subset_span (by simp)
  · intro _
    apply flat_of_ann
    intro m hm
    rw [Algebra.smul_def, map_natCast] at hm
    obtain ⟨y, hy⟩ := hann m hm
    exact ⟨y, by rw [Algebra.smul_def, map_natCast]; exact hy⟩
end ReciprocityTheory.PGsh
