-- Prove2me | solution 1 for SemigroupBetti.GenData.toricKer_le_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:12.315568+00:00
-- url     : https://prove2.me/submissions/b6528521-131d-4a21-8517-e2a4e6305204

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_mono_coe
public import Theorems.Thm_SemigroupBetti_GenData_mono_sub_mem_span
public import Theorems.Thm_SemigroupBetti_GenData_nu_root
public import Theorems.Thm_SemigroupBetti_GenData_coeff_sum_eq_zero

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution : G.toricKer K ≤ Ideal.span (G.binomGens K : Set _) := by
  intro f hf
  set J := Ideal.span (G.binomGens K : Set (MvPolynomial (Fin 4) K))
  have hsplit : f = ∑ s ∈ f.support, C (f.coeff s) * (mono K s - mono K (G.root (G.nu s))) +
      ∑ s ∈ f.support, C (f.coeff s) * mono K (G.root (G.nu s)) := by
    rw [← sum_add_distrib]
    simp_rw [← mul_add, sub_add_cancel, mono_coe, C_mul_monomial, mul_one]
    exact f.as_sum
  have hzero : ∑ s ∈ f.support, C (f.coeff s) * mono K (G.root (G.nu s)) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Fin 4 →₀ ℕ => G.nu s)
      (t := f.support.image (fun s : Fin 4 →₀ ℕ => G.nu s)) (fun s hs => mem_image_of_mem _ hs)]
    refine Finset.sum_eq_zero fun d _ => ?_
    have : ∀ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => G.nu ⇑s = d),
        C (f.coeff s) * mono K (G.root (G.nu s)) = C (f.coeff s) * mono K (G.root d) := by
      intro s hs; rw [(mem_filter.1 hs).2]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum, G.coeff_sum_eq_zero K hf d,
      map_zero, zero_mul]
  rw [hsplit, hzero, add_zero]
  exact J.sum_mem fun s _ => J.mul_mem_left _
    (G.mono_sub_mem_span K (G.nu s) s _ rfl (G.nu_root s))
end SemigroupBetti.GenData
