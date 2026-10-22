-- Prove2me | solution 1 for PriceQualityService.Oligopoly.eq_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:31.700184+00:00
-- url     : https://prove2.me/submissions/13d567a8-fb20-4c78-b950-f46eb5b79b8b

import Mathlib
import Definitions.Def_PriceQualityService_Joint_Model
import Definitions.Def_PriceQualityService_Oligopoly_Model
set_option autoImplicit false
open Finset PriceQualityService.Oligopoly

theorem solution {N : ℕ} (α a b c s p q t : Fin N → ℝ) (i : Fin N) (r : ℝ) :
    r * (1 + ∑ j ∈ univ.erase i, PriceQualityService.Joint.attraction α s p q t j) =
        (PriceQualityService.Joint.markup a b c p q t i - r) * PriceQualityService.Joint.attraction α s p q t i ↔
      r = firmProfit α a b c s p q t i := by
  have hpos : ∀ j, 0 < PriceQualityService.Joint.attraction α s p q t j :=
    fun j => Real.exp_pos _
  set S' := ∑ j ∈ univ.erase i, PriceQualityService.Joint.attraction α s p q t j with hS'
  set ai := PriceQualityService.Joint.attraction α s p q t i with hai
  set m := PriceQualityService.Joint.markup a b c p q t i with hm
  have hS'nn : 0 ≤ S' := Finset.sum_nonneg fun j _ => (hpos j).le
  have hsum : ∑ j, PriceQualityService.Joint.attraction α s p q t j = ai + S' := by
    rw [← Finset.add_sum_erase univ _ (Finset.mem_univ i)]
  have hd : 0 < 1 + (ai + S') := by have := hpos i; linarith
  have hprof : firmProfit α a b c s p q t i = m * (ai / (1 + (ai + S'))) := by
    unfold firmProfit PriceQualityService.Joint.choiceProb
    rw [hsum]
  rw [hprof]
  constructor
  · intro h
    field_simp
    nlinarith [h]
  · intro h
    rw [h]
    field_simp
    ring
