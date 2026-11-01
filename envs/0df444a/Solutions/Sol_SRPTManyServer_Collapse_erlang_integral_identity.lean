-- Prove2me | solution 1 for SRPTManyServer.Collapse.erlang_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:55:20.85741+00:00
-- url     : https://prove2.me/submissions/45561b85-23cf-4e35-8ee9-fee8ff640359

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang

open MeasureTheory Set Real

lemma srpt_int_pow_exp (k : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-t) = (Nat.factorial k : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (k:ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

lemma srpt_intble_pow_exp (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-t)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (k:ℝ) + 1) (by positivity)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  ring

lemma srpt_int_expand (r : ℝ) (hr : 0 < r) (C : ℕ) :
    ∫ t in Ioi (0:ℝ), (1 + t / r) ^ C * Real.exp (-t) =
      ∑ m ∈ Finset.range (C + 1), (Nat.choose C m : ℝ) / r ^ m * (Nat.factorial m : ℝ) := by
  have hexp : ∀ t : ℝ, (1 + t / r) ^ C * Real.exp (-t) =
      ∑ m ∈ Finset.range (C + 1), ((Nat.choose C m : ℝ) / r ^ m) * (t ^ m * Real.exp (-t)) := by
    intro t
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [div_pow]; field_simp; ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [integral_const_mul, srpt_int_pow_exp]
  · intro m _
    exact (srpt_intble_pow_exp m).const_mul _

theorem solution :
    (∀ (r : ℝ), 0 < r → ∀ C : ℕ,
      KellyStochasticNetworks.erlang r C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / r) ^ C * Real.exp (-t))⁻¹) ∧
    (∀ C : ℕ, 1 ≤ C →
      KellyStochasticNetworks.erlang (C : ℝ) C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / (C : ℝ)) ^ C * Real.exp (-t))⁻¹) := by
  have main : ∀ (r : ℝ), 0 < r → ∀ C : ℕ,
      KellyStochasticNetworks.erlang r C =
        (∫ t in Set.Ioi (0 : ℝ), (1 + t / r) ^ C * Real.exp (-t))⁻¹ := by
    intro r hr C
    rw [srpt_int_expand r hr C, KellyStochasticNetworks.erlang]
    have key : (∑ m ∈ Finset.range (C + 1), (Nat.choose C m : ℝ) / r ^ m * (Nat.factorial m : ℝ))
        * (r ^ C / (Nat.factorial C : ℝ)) =
        ∑ j ∈ Finset.range (C + 1), r ^ j / (Nat.factorial j : ℝ) := by
      rw [Finset.sum_mul]
      conv_rhs => rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hmC : m ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hsub : C + 1 - 1 - m = C - m := by omega
      rw [hsub]
      have hfac := Nat.choose_mul_factorial_mul_factorial hmC
      have hfac' : (Nat.choose C m : ℝ) * (Nat.factorial m : ℝ) * (Nat.factorial (C - m) : ℝ)
          = (Nat.factorial C : ℝ) := by exact_mod_cast hfac
      have hrC : r ^ C = r ^ m * r ^ (C - m) := by rw [← pow_add]; congr 1; omega
      have h1 : (Nat.factorial C : ℝ) ≠ 0 := by positivity
      have h2 : (Nat.factorial (C - m) : ℝ) ≠ 0 := by positivity
      have h3 : r ^ m ≠ 0 := by positivity
      have h4 : (Nat.choose C m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmC).ne'
      rw [hrC, ← hfac']
      field_simp
    have hpos : 0 < r ^ C / (Nat.factorial C : ℝ) := by positivity
    rw [← key]
    have hI : (∑ m ∈ Finset.range (C + 1), (Nat.choose C m : ℝ) / r ^ m * (Nat.factorial m : ℝ))
        ≠ 0 := by
      apply ne_of_gt
      refine Finset.sum_pos' (fun m _ => by positivity) ⟨0, by simp, by simp⟩
    field_simp
  refine ⟨main, fun C hC => main (C : ℝ) (by exact_mod_cast hC) C⟩
