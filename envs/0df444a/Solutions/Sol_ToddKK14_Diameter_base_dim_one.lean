-- Prove2me | solution 1 for ToddKK14.Diameter.base_dim_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:02:25.483293+00:00
-- url     : https://prove2.me/submissions/af92a76b-10a5-4413-a270-6247b9960b87

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

set_option autoImplicit false

namespace ToddKK14.Diameter

open Hirsch

lemma line_param (u v x : EuclideanSpace ℝ (Fin 1)) (huv : u ≠ v) :
    ∃ t : ℝ, x = u + t • (v - u) := by
  have hc : (v - u) 0 ≠ 0 := by
    intro h
    apply huv
    have : v - u = 0 := by
      ext i
      fin_cases i
      simpa using h
    exact (sub_eq_zero.1 this).symm
  refine ⟨(x - u) 0 / (v - u) 0, ?_⟩
  ext i
  fin_cases i
  simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  simp

lemma base_dim_one' (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 1)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) 1 := by
  intro u hu v hv
  by_cases huv : u = v
  · subst huv
    exact ⟨fun _ => u, rfl, rfl, fun i _ => Or.inl rfl⟩
  · set P := Hpoly a b with hP
    have hsub : P ⊆ segment ℝ u v := by
      intro x hx
      obtain ⟨t, rfl⟩ := line_param u v x huv
      have ht1 : t ≤ 1 := by
        by_contra h
        push_neg at h
        have ht0 : 0 < t := by linarith
        have := hv.2 hu.1 hx (by
          refine ⟨1 - 1 / t, 1 / t, ?_, div_pos one_pos ht0, by ring, ?_⟩
          · have : 1 / t < 1 := by rw [div_lt_one ht0]; exact h
            linarith
          · have : (1 / t) • (t • (v - u)) = v - u := by
              rw [smul_smul, one_div, inv_mul_cancel₀ ht0.ne', one_smul]
            calc (1 - 1 / t) • u + (1 / t) • (u + t • (v - u))
                = u + (1 / t) • (t • (v - u)) := by
                  rw [smul_add, sub_smul, one_smul]; abel
              _ = v := by rw [this]; abel)
        exact huv this
      have ht0 : 0 ≤ t := by
        by_contra h
        push_neg at h
        have h1 : (1 - t) ≠ 0 := by linarith
        have := hu.2 hx hv.1 (by
          refine ⟨1 / (1 - t), -t / (1 - t), div_pos one_pos (by linarith), ?_, ?_, ?_⟩
          · apply div_pos (by linarith) (by linarith)
          · field_simp; ring
          · ext i
            fin_cases i
            simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
            field_simp
            ring)
        have h2 : t • (v - u) = 0 := by
          have := congrArg (fun z => z - u) this
          simpa using this
        rcases smul_eq_zero.1 h2 with h3 | h3
        · linarith
        · exact huv (sub_eq_zero.1 h3).symm
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      rw [sub_smul, one_smul, smul_sub]; abel
    have hseg : segment ℝ u v ⊆ P := by
      -- segment lies in P since u, v ∈ P and P is convex
      have hconv : Convex ℝ P := by
        intro x hx y hy p q hp hq hpq i
        have h1 := hx i
        have h2 := hy i
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_add_right, inner_smul_right]
        have e : p * b i + q * b i = b i := by rw [← add_mul, hpq, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left h1 hp, mul_le_mul_of_nonneg_left h2 hq]
      exact hconv.segment_subset hu.1 hv.1
    have hPeq : P = segment ℝ u v := Set.Subset.antisymm hsub hseg
    refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    right
    refine ⟨huv, ?_⟩
    simp only [if_true, one_ne_zero, zero_add, if_false]
    rw [← hPeq]
    exact IsExtreme.refl ℝ P

end ToddKK14.Diameter

theorem solution (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin 1)) (b : Fin n → ℝ) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) 1 :=
  ToddKK14.Diameter.base_dim_one' n a b
