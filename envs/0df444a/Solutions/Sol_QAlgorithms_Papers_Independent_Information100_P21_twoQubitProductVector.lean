-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.twoQubitProductVector
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:47:37.170122+00:00
-- url     : https://prove2.me/submissions/a1ef5707-4976-446c-8b9c-5d95d979a1bd

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Information100.P21

lemma tqpv_key (u : Fin 2 × Fin 2 → ℂ) (h : u (0,0) * u (1,1) = u (0,1) * u (1,0))
    (i j i0 j0 : Fin 2) : u (i,j) * u (i0,j0) = u (i,j0) * u (i0,j) := by
  fin_cases i <;> fin_cases j <;> fin_cases i0 <;> fin_cases j0 <;> simp <;>
    first | ring1 | linear_combination h | linear_combination -h

lemma tqpv_rank1 (u : Fin 2 × Fin 2 → ℂ) (h : u (0,0) * u (1,1) = u (0,1) * u (1,0))
    (hu : u ≠ 0) : ∃ e f : Fin 2 → ℂ, ∀ i j, u (i,j) = e i * f j := by
  obtain ⟨⟨i0, j0⟩, hp⟩ : ∃ p, u p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu (funext hcon)
  refine ⟨fun i => u (i, j0), fun j => u (i0, j) / u (i0, j0), fun i j => ?_⟩
  have := tqpv_key u h i j i0 j0
  field_simp
  linear_combination this

theorem solution (V : Submodule ℂ (Vec QQ)) (h : 2 ≤ Module.finrank ℂ V) :
    ∃ e f : Vec (Fin 2), tensor e f ∈ V ∧ tensor e f ≠ 0 := by
  have h1 : 1 < Module.finrank ℂ V := by omega
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
    have : 0 < Module.finrank ℂ V := by omega
    exact Module.finrank_pos_iff_exists_ne_zero.mp this
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h1 hx
  have hli := LinearIndependent.pair_iff.mp hxy
  set v : Vec QQ := (x : Vec QQ) with hv
  set w : Vec QQ := (y : Vec QQ) with hw
  have hvV : v ∈ V := x.2
  have hwV : w ∈ V := y.2
  have hnz : ∀ s t : ℂ, s • v + t • w = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    apply hli
    apply Subtype.ext
    simpa using hst
  let g : Vec QQ → ℂ := fun z => z (0,0) * z (1,1) - z (0,1) * z (1,0)
  let A := g v
  let C := g w
  let B : ℂ := v (0,0) * w (1,1) + w (0,0) * v (1,1) - v (0,1) * w (1,0) - w (0,1) * v (1,0)
  have hg : ∀ s t : ℂ, g (s • v + t • w) = A * s * s + B * s * t + C * t * t := by
    intro s t
    simp only [g, A, B, C, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  obtain ⟨s, t, hst, hz⟩ : ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ A * s * s + B * s * t + C * t * t = 0 := by
    by_cases hA : A = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA]⟩
    · obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (discrim A B C)
      obtain ⟨s, hs⟩ := exists_quadratic_eq_zero hA ⟨d, hd⟩
      exact ⟨s, 1, Or.inr one_ne_zero, by linear_combination hs⟩
  set u : Vec QQ := s • v + t • w with hu
  have huV : u ∈ V := V.add_mem (V.smul_mem s hvV) (V.smul_mem t hwV)
  have hu0 : u ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := hnz s t h0
    rcases hst with h | h <;> contradiction
  have hdet : u (0,0) * u (1,1) = u (0,1) * u (1,0) := by
    have := hg s t
    rw [hz] at this
    simp only [g] at this
    rw [← hu] at this
    linear_combination this
  obtain ⟨e, f, hef⟩ := tqpv_rank1 (fun p => u p) hdet (by
    intro h0
    apply hu0
    ext p
    exact congrFun h0 p)
  have heq : tensor (WithLp.toLp 2 e : Vec (Fin 2)) (WithLp.toLp 2 f : Vec (Fin 2)) = u := by
    ext p
    obtain ⟨i, j⟩ := p
    simp [tensor, hef i j]
  exact ⟨WithLp.toLp 2 e, WithLp.toLp 2 f, by rw [heq]; exact huV, by rw [heq]; exact hu0⟩
