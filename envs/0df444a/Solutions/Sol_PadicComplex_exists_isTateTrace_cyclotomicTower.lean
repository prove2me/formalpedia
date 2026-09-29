-- Prove2me | solution 1 for PadicComplex.exists_isTateTrace_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/786d0522-b721-57c6-bc0d-9bcbb7d67370

import Mathlib
import Definitions.Def_PadicComplex_TateTrace
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicComplex_exists_isTateTrace_of_norm_sum_pow_apply_le
import Theorems.Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup
import Theorems.Thm_PadicAlgCl_norm_sum_pow_apply_le_of_mem_cyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_isTateTrace_cyclotomicTower

set_option autoImplicit false

noncomputable section

namespace TCT

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

def F (n : ℕ) : IntermediateField ℚ_[p] Ω := PadicAlgCl.cyclotomicTower p (n + 2)

lemma F_mono : Monotone (F p) := fun _ _ h =>
  PadicAlgCl.cyclotomicTower_mono p (Nat.add_le_add_right h 2)

lemma finrank_F (n : ℕ) : Module.finrank ℚ_[p] (F p n) = (p - 1) * p ^ (n + 1) := by
  have h := (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).1 (n + 2) (by omega)
  exact h

lemma finiteDimensional_F (n : ℕ) : FiniteDimensional ℚ_[p] (F p n) := by
  apply Module.finite_of_finrank_pos
  rw [finrank_F]
  have hp : p.Prime := Fact.out
  have : 0 < p - 1 := by have := hp.one_lt; omega
  exact Nat.mul_pos this (pow_pos hp.pos _)

lemma stable (n : ℕ) (σ : Γ) (y : Ω) (hy : y ∈ F p n) : σ y ∈ F p n := by
  unfold F PadicAlgCl.cyclotomicTower at hy ⊢
  set S : Set Ω := {ζ : Ω | ζ ^ p ^ (n + 2) = 1} with hS
  have hmap : (IntermediateField.adjoin ℚ_[p] S).map (σ : Ω →ₐ[ℚ_[p]] Ω) ≤
      IntermediateField.adjoin ℚ_[p] S := by
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨ζ, hζ, rfl⟩
    show (σ : Ω →ₐ[ℚ_[p]] Ω) ζ ^ p ^ (n + 2) = 1
    rw [← map_pow, (hζ : ζ ^ p ^ (n + 2) = 1), map_one]
  exact hmap ⟨y, hy, rfl⟩

lemma hdeg (m n : ℕ) (h : n = m + 1) :
    Module.finrank ℚ_[p] (F p n) = p * Module.finrank ℚ_[p] (F p m) := by
  subst h
  rw [finrank_F, finrank_F]
  ring

lemma hcyc (m : ℕ) (σ : Γ) (hσ : σ ∈ (F p m).fixingSubgroup) (hσ' : σ ∉ (F p (m + 1)).fixingSubgroup) :
    σ ^ p ∈ (F p (m + 1)).fixingSubgroup ∧ σ ^ p ∉ (F p (m + 2)).fixingSubgroup :=
  (PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup p).2 m σ hσ hσ'

def c (m : ℕ) : ℝ := (p : ℝ) ^ (1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)))

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma exponent_nonneg (m : ℕ) : (0 : ℝ) ≤ 1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)) := by
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_p p; linarith
  have h2 : (0 : ℝ) < (p : ℝ) ^ (m + 1) := pow_pos (p_pos p) _
  positivity

lemma one_le_c (m : ℕ) : 1 ≤ c p m := Real.one_le_rpow (one_lt_p p).le (exponent_nonneg p m)

lemma sum_exponent_le (n : ℕ) :
    ∑ m ∈ Finset.range n, 1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_p p; linarith
  have hp0 : (0 : ℝ) < p := p_pos p
  set x : ℝ := (p : ℝ)⁻¹ with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x < 1 := by rw [hx]; exact inv_lt_one_of_one_lt₀ (one_lt_p p)

  have hterm : ∀ m, 1 / (((p : ℝ) - 1) * (p : ℝ) ^ (m + 1)) = ((p : ℝ) - 1)⁻¹ * (x * x ^ m) := by
    intro m
    rw [hx, ← pow_succ', inv_pow]
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

  have hgeom : ∑ m ∈ Finset.range n, x ^ m ≤ (1 - x)⁻¹ := by
    have h := geom_sum_eq hx1.ne n
    rw [h]
    have h1 : 0 < 1 - x := by linarith
    have h2 : (x ^ n - 1) / (x - 1) = (1 - x ^ n) / (1 - x) := by
      have hx1' : x - 1 ≠ 0 := by linarith
      have h1' : 1 - x ≠ 0 := by linarith
      field_simp
      ring
    rw [h2, inv_eq_one_div, div_le_div_iff_of_pos_right h1]
    linarith [pow_nonneg hx0 n]
  have hkey : ((p : ℝ) - 1)⁻¹ * (x * ∑ m ∈ Finset.range n, x ^ m) ≤ ((p : ℝ) - 1)⁻¹ * (x * (1 - x)⁻¹) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeom hx0) (by positivity)
  refine hkey.trans (le_of_eq ?_)
  rw [hx]
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hpx : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [hpx]
  field_simp

lemma prod_c_le (n : ℕ) : ∏ m ∈ Finset.range n, c p m ≤ (p : ℝ) ^ (1 / ((p : ℝ) - 1) ^ 2) := by
  unfold c
  rw [← Real.rpow_sum_of_pos (p_pos p)]
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le (sum_exponent_le p n)

lemma htr (m : ℕ) (σ : Γ) (hσ : σ ∈ (F p m).fixingSubgroup) (hσ' : σ ∉ (F p (m + 1)).fixingSubgroup)
    (y : Ω) (hy : y ∈ F p (m + 1)) :
    ‖∑ i ∈ Finset.range p, (σ ^ i) y‖ ≤ ‖(p : ℚ_[p])‖ * c p m * ‖y‖ :=
  PadicAlgCl.norm_sum_pow_apply_le_of_mem_cyclotomicTower p m σ hσ hσ' y hy

theorem main : ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∃ R : ℂ_[p] → ℂ_[p],
    PadicComplex.IsTateTrace p (fun n => PadicAlgCl.cyclotomicTower p (n + 2)) m d R :=
  PadicComplex.exists_isTateTrace_of_norm_sum_pow_apply_le p (F p) (F_mono p)
    (finiteDimensional_F p) (fun m σ _ y hy => stable p m σ y hy) (hdeg p) (hcyc p)
    (c p) ((p : ℝ) ^ (1 / ((p : ℝ) - 1) ^ 2)) (one_le_c p) (prod_c_le p) (htr p)

end TCT

end

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ d : ℝ, 0 < d ∧ ∀ m : ℕ, ∃ R : ℂ_[p] → ℂ_[p],
      PadicComplex.IsTateTrace p (fun n => PadicAlgCl.cyclotomicTower p (n + 2)) m d R :=
  TCT.main p

end S_PadicComplex_exists_isTateTrace_cyclotomicTower
end P2MW
export P2MW.S_PadicComplex_exists_isTateTrace_cyclotomicTower (solution)
