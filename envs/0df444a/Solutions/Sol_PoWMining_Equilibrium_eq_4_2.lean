-- Prove2me | solution 1 for PoWMining.Equilibrium.eq_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:35:19.726242+00:00
-- url     : https://prove2.me/submissions/3435c28c-7209-4e01-9edc-176ea9a34701

import Mathlib
import Definitions.Def_PoWMining_Equilibrium_Setting
set_option autoImplicit false
open PoWMining.Equilibrium

theorem solution {N : ℕ} (P : Params N) (hP : P.Standing) (h : Fin N → ℝ)
    (hh : IsMiningEq P h) (i : Fin N) (hi : 0 < h i) :
    P.R / aggH h * (1 - h i / aggH h) = P.c i + P.γ * h i := by
  obtain ⟨hnn, hnash⟩ := hh
  set S : ℝ := ∑ j ∈ Finset.univ \ {i}, h j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => hnn j)
  have hH : aggH h = h i + S := by
    unfold aggH
    rw [hS, Finset.sdiff_singleton_eq_erase, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hagg : ∀ x : ℝ, aggH (Function.update h i x) = x + S := by
    intro x
    unfold aggH
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  set ψ : ℝ → ℝ := fun x => x / (x + S) * P.R - P.c i * x - P.γ / 2 * x ^ 2 with hψ
  have hloc : IsLocalMax ψ (h i) := by
    filter_upwards [Ioi_mem_nhds hi] with x hx
    have hx0 : 0 < x := hx
    have h1 : payoff P (Function.update h i x) i = ψ x := by
      unfold payoff
      rw [hagg x, if_neg (by positivity)]
      simp only [Function.update_self, hψ]
    have h2 : payoff P h i = ψ (h i) := by
      unfold payoff
      rw [hH, if_neg (by positivity)]
      try simp only [hψ]
    have : payoff P (Function.update h i x) i ≤ payoff P h i := hnash i x hx0.le
    rw [h1, h2] at this
    exact this
  have hpos : 0 < h i + S := by positivity
  have hd : HasDerivAt ψ (P.R * S / (h i + S) ^ 2 - P.c i - P.γ * h i) (h i) := by
    have h1 := (hasDerivAt_id' (h i)).div ((hasDerivAt_id' (h i)).add_const S) hpos.ne'
    have h2 := (h1.mul_const P.R).sub ((hasDerivAt_id' (h i)).const_mul (P.c i))
    have h3 := h2.sub ((hasDerivAt_pow 2 (h i)).const_mul (P.γ / 2))
    refine h3.congr_deriv ?_
    field_simp
    ring
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [hH]
  have hne : h i + S ≠ 0 := hpos.ne'
  have e : P.R / (h i + S) * (1 - h i / (h i + S)) = P.R * S / (h i + S) ^ 2 := by
    field_simp
    ring
  rw [e]
  linarith
