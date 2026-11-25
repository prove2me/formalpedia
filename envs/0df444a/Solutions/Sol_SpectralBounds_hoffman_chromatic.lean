-- Prove2me | solution 1 for SpectralBounds.hoffman_chromatic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:36:54.910433+00:00
-- url     : https://prove2.me/submissions/8ecc9323-b512-4640-9c9a-8a70a0806bec

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_exists_unit_eigenvector_iSup
public import Theorems.Thm_SpectralBounds_quadForm_eq_zero_of_indep
public import Theorems.Thm_SpectralBounds_hoffman_key
public import Theorems.Thm_SpectralBounds_iInf_eigenvalues_le_neg_one

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
namespace SpectralBounds
theorem _root_.solution (hE : G.edgeSet.Nonempty) {c : ℕ} (hc : G.Colorable c) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ c := by
  obtain ⟨C⟩ := hc
  obtain ⟨x, hx, hxx⟩ := exists_unit_eigenvector_iSup hA
  set lam := ⨆ i, hA.eigenvalues i
  set mu := ⨅ i, hA.eigenvalues i
  have hmu : mu ≤ -1 := iInf_eigenvalues_le_neg_one G hA hE
  set z : Fin c → V → ℝ := fun j v => if C v = j then x v else 0
  have hzz : ∀ j, z j ⬝ᵥ z j = z j ⬝ᵥ x := fun j => by
    simp only [z, dotProduct]
    refine sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  have hz0 : ∀ j, 0 ≤ z j ⬝ᵥ x := fun j => by
    rw [← hzz]
    exact sum_nonneg fun v _ => mul_self_nonneg _
  have hclass : ∀ j, (lam - mu) * (z j ⬝ᵥ x) ≤ -mu := fun j => by
    have hind : z j ⬝ᵥ (G.adjMatrix ℝ *ᵥ z j) = 0 := by
      refine quadForm_eq_zero_of_indep G _ fun u v huv => ?_
      by_contra hne
      push Not at hne
      simp only [z, ne_eq, ite_eq_right_iff, not_forall] at hne
      exact C.valid huv (hne.1.1.trans hne.2.1.symm)
    have h := hoffman_key G hA x (z j) lam (z j ⬝ᵥ x) hx hind
    rw [hzz, hxx] at h
    rcases (hz0 j).lt_or_eq with hs | hs
    · nlinarith
    · rw [← hs]; linarith
  have hsum : ∑ j, z j ⬝ᵥ x = 1 := by
    rw [← hxx]
    simp only [z, dotProduct, ite_mul, zero_mul]
    rw [sum_comm]
    simp
  have htot : lam - mu ≤ -(c * mu) := by
    have := sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin c))) => hclass j
    rw [← mul_sum, hsum] at this
    simpa using this
  have hneg : mu < 0 := by linarith
  have h1 : 1 - (c : ℝ) ≤ lam / mu := by
    rw [le_div_iff_of_neg hneg]
    linarith
  linarith
end SpectralBounds
