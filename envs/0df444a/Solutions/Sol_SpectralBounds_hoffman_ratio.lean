-- Prove2me | solution 1 for SpectralBounds.hoffman_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:37:04.72312+00:00
-- url     : https://prove2.me/submissions/0596302e-43fe-4d54-b40e-3cbf1c08a24a

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_quadForm_eq_zero_of_indep
public import Theorems.Thm_SpectralBounds_hoffman_key
public import Theorems.Thm_SpectralBounds_iInf_eigenvalues_nonpos

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
namespace SpectralBounds
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree k) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) :
    (#s : ℝ) ≤ Fintype.card V * (-(⨅ i, hA.eigenvalues i)) / (k - ⨅ i, hA.eigenvalues i) := by
  set mu := ⨅ i, hA.eigenvalues i
  have hmu : mu ≤ 0 := iInf_eigenvalues_nonpos G hA
  set x : V → ℝ := fun _ => 1
  set z : V → ℝ := fun v => if v ∈ s then 1 else 0
  set n : ℝ := (Fintype.card V : ℝ)
  set a : ℝ := (#s : ℝ)
  have hn : 0 < n := by simp only [n]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hx : G.adjMatrix ℝ *ᵥ x = (k : ℝ) • x := by
    ext v
    simp [x, hreg v]
  have hind : z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0 := by
    refine quadForm_eq_zero_of_indep G _ fun u v huv => ?_
    by_contra hne
    push Not at hne
    simp only [z, ne_eq, ite_eq_right_iff, not_forall] at hne
    exact hs hne.1.1 hne.2.1 huv.ne huv
  have hzz : z ⬝ᵥ z = a := by simp [z, a, dotProduct]
  have hzx : z ⬝ᵥ x = a := by simp [z, x, a, dotProduct]
  have hxx : x ⬝ᵥ x = n := by simp [x, n, dotProduct]
  have h := hoffman_key G hA x z k (a / n) hx hind
  rw [hzz, hzx, hxx] at h
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - mu := by linarith
  rw [le_div_iff₀ hden]
  have ht : a / n * n = a := div_mul_cancel₀ a hn.ne'
  set t := a / n
  have ha : 0 ≤ a := by positivity
  have h' : mu * (t * n) * (1 - t) ≤ -(k * t ^ 2 * n) := by
    have : a = t * n := ht.symm
    rw [this] at h
    nlinarith
  rcases ha.lt_or_eq with hapos | ha0
  · have htpos : 0 < t := by positivity
    have h2 : mu * (1 - t) ≤ -(k * t) := by
      have h3 : t * n * (mu * (1 - t)) ≤ t * n * (-(k * t)) := by nlinarith
      exact le_of_mul_le_mul_left h3 (by positivity)
    rw [← ht]
    nlinarith
  · rw [← ha0]
    nlinarith
end SpectralBounds
