-- Prove2me | solution 1 for SteinitzExchange.Extension.two_swap_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:03:27.084615+00:00
-- url     : https://prove2.me/submissions/846b3aad-f991-4678-bc76-df0f22665724

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

theorem aux_tsb_chi_apply {V : Type*} [DecidableEq V] (u w : V) :
    chi u w = if w = u then 1 else 0 := by
  unfold chi
  rw [Pi.single_apply]

theorem aux_tsb_chi_nonneg {V : Type*} [DecidableEq V] (u w : V) : 0 ≤ chi u w := by
  rw [aux_tsb_chi_apply]; split_ifs <;> norm_num

theorem aux_tsb_chi_sum {V : Type*} [Fintype V] [DecidableEq V] (u : V) :
    ∑ w, chi u w = 1 := by
  unfold chi
  exact Fintype.sum_pi_single' u 1

theorem aux_tsb_pairing {V : Type*} [Fintype V] (p : V → ℝ) (a b c d : V → ℤ)
    (h : a + b = c + d) :
    pairing p (toReal a) + pairing p (toReal b) = pairing p (toReal c) + pairing p (toReal d) := by
  unfold pairing toReal
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hw := congrFun h w
  simp only [Pi.add_apply] at hw
  rw [← mul_add, ← mul_add]
  congr 1
  exact_mod_cast hw

theorem aux_tsb_perturb {V : Type*} [Fintype V] (ω : (V → ℤ) → ℝ) (p : V → ℝ)
    (a b c d : V → ℤ) (h : a + b = c + d) (hω : ω a + ω b ≤ ω c + ω d) :
    perturb ω p a + perturb ω p b ≤ perturb ω p c + perturb ω p d := by
  unfold perturb
  have := aux_tsb_pairing p a b c d h
  linarith

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hloc : SatisfiesEXCLoc B ω) (x : V → ℤ) (hx : x ∈ B) (u₀ u₁ v₀ v₁ : V)
    (hy : x - chi u₀ - chi u₁ + chi v₀ + chi v₁ ∈ B)
    (h00 : u₀ ≠ v₀) (h01 : u₀ ≠ v₁) (h10 : u₁ ≠ v₀) (h11 : u₁ ≠ v₁) (p : V → ℝ) :
    let y := x - chi u₀ - chi u₁ + chi v₀ + chi v₁
    let π : V → V → ℝ := fun u v => perturb ω p (x - chi u + chi v) - perturb ω p x
    (x - chi u₀ + chi v₀ ∈ B ∧ x - chi u₁ + chi v₁ ∈ B ∧
        perturb ω p y - perturb ω p x ≤ π u₀ v₀ + π u₁ v₁) ∨
      (x - chi u₀ + chi v₁ ∈ B ∧ x - chi u₁ + chi v₀ ∈ B ∧
        perturb ω p y - perturb ω p x ≤ π u₀ v₁ + π u₁ v₀) := by
  intro y π
  have hyB : y ∈ B := hy
  have hd : ∀ w, (x - y) w = chi u₀ w + chi u₁ w - chi v₀ w - chi v₁ w := by
    intro w
    simp only [y, Pi.sub_apply, Pi.add_apply]
    ring
  have habs : ∀ w, |x w - y w| = chi u₀ w + chi u₁ w + chi v₀ w + chi v₁ w := by
    intro w
    have := hd w
    rw [Pi.sub_apply] at this
    rw [this]
    simp only [aux_tsb_chi_apply]
    split_ifs <;> simp_all
  have hnorm : ∑ w, |x w - y w| = 4 := by
    simp only [habs, Finset.sum_add_distrib, aux_tsb_chi_sum]
    norm_num
  obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := hloc x hx y hyB hnorm
  have hu' : u = u₀ ∨ u = u₁ := by
    by_contra hne
    push Not at hne
    rw [hd u] at hu
    simp only [aux_tsb_chi_apply, if_neg hne.1, if_neg hne.2] at hu
    have := aux_tsb_chi_nonneg v₀ u
    have := aux_tsb_chi_nonneg v₁ u
    simp only [aux_tsb_chi_apply] at *
    linarith
  have hv' : v = v₀ ∨ v = v₁ := by
    by_contra hne
    push Not at hne
    rw [hd v] at hv
    simp only [aux_tsb_chi_apply, if_neg hne.1, if_neg hne.2] at hv
    have := aux_tsb_chi_nonneg u₀ v
    have := aux_tsb_chi_nonneg u₁ v
    simp only [aux_tsb_chi_apply] at *
    linarith
  rcases hu' with hu | hu <;> rcases hv' with hv | hv <;> rw [hu, hv] at h1 h2 h3
  · have hyeq : y + chi u₀ - chi v₀ = x - chi u₁ + chi v₁ := by
      simp only [y]; abel
    rw [hyeq] at h2 h3
    left
    refine ⟨h1, h2, ?_⟩
    have key := aux_tsb_perturb ω p x y (x - chi u₀ + chi v₀) (x - chi u₁ + chi v₁)
      (by simp only [y]; abel) h3
    simp only [π]
    linarith
  · have hyeq : y + chi u₀ - chi v₁ = x - chi u₁ + chi v₀ := by
      simp only [y]; abel
    rw [hyeq] at h2 h3
    right
    refine ⟨h1, h2, ?_⟩
    have key := aux_tsb_perturb ω p x y (x - chi u₀ + chi v₁) (x - chi u₁ + chi v₀)
      (by simp only [y]; abel) h3
    simp only [π]
    linarith
  · have hyeq : y + chi u₁ - chi v₀ = x - chi u₀ + chi v₁ := by
      simp only [y]; abel
    rw [hyeq] at h2 h3
    right
    refine ⟨h2, h1, ?_⟩
    have key := aux_tsb_perturb ω p x y (x - chi u₁ + chi v₀) (x - chi u₀ + chi v₁)
      (by simp only [y]; abel) h3
    simp only [π]
    linarith
  · have hyeq : y + chi u₁ - chi v₁ = x - chi u₀ + chi v₀ := by
      simp only [y]; abel
    rw [hyeq] at h2 h3
    left
    refine ⟨h2, h1, ?_⟩
    have key := aux_tsb_perturb ω p x y (x - chi u₁ + chi v₁) (x - chi u₀ + chi v₀)
      (by simp only [y]; abel) h3
    simp only [π]
    linarith
