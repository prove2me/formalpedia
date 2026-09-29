-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.irreducible_pair_intersection_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:50:31.368143+00:00
-- url     : https://prove2.me/submissions/993e6f04-7f95-483c-afae-db89e063d3d9

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_curry_isPrimitive_of_irreducible_positive_natDegree
import Theorems.Thm_PachDeZeeuw_Algebraic_curry_isRelPrime_of_nonassociated_irreducibles
import Theorems.Thm_PachDeZeeuw_Algebraic_primitive_nonvertical_pair_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_zeroCurry_nonvertical_pair_intersection_bound
import Theorems.Thm_PachDeZeeuw_Algebraic_zeroCurry_zeroCurry_pair_intersection_bound

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {d₁ : ℕ} {d₂ : ℕ} (h k : MvPolynomial (Fin 2) ℝ)
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁)
    (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k) :
    (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
      (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤
        (d₁ + d₂ + 1) ^ 4 := by
  have htarget_mul : d₁ * d₂ ≤ (d₁ + d₂ + 1) ^ 4 := by
    have hle : d₁ * d₂ ≤ (d₁ + d₂ + 1) ^ 2 := by
      have hd1 : d₁ ≤ d₁ + d₂ + 1 := by omega
      have hd2 : d₂ ≤ d₁ + d₂ + 1 := by omega
      calc
        d₁ * d₂ ≤ (d₁ + d₂ + 1) * d₂ := Nat.mul_le_mul_right _ hd1
        _ ≤ (d₁ + d₂ + 1) * (d₁ + d₂ + 1) := Nat.mul_le_mul_left _ hd2
        _ = (d₁ + d₂ + 1) ^ 2 := by simp [pow_two]
    have hpos : 0 < (d₁ + d₂ + 1) ^ 2 := by
      have hbase : 0 < d₁ + d₂ + 1 := by omega
      exact Nat.pow_pos hbase
    have hsq : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 4 := by
      have hle2 : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 2 * (d₁ + d₂ + 1) ^ 2 := by
        exact Nat.le_mul_of_pos_right _ hpos
      simp [pow_succ] at hle2 ⊢
    exact le_trans hle hsq
  have htarget_prim :
      ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂ ≤ (d₁ + d₂ + 1) ^ 4 := by
    -- Write `t = d₁ + d₂` and bound each factor by a power of `t + 1`.
    have hmax : max d₁ d₂ ≤ d₁ + d₂ + 1 :=
      max_le (by omega) (by omega)
    have hfac : (d₁ + d₂) ^ 2 + 1 ≤ (d₁ + d₂ + 1) ^ 3 := by
      have h2 : (d₁ + d₂) ^ 2 + 1 ≤ (d₁ + d₂ + 1) ^ 2 := by
        have : (d₁ + d₂ + 1) ^ 2 = (d₁ + d₂) ^ 2 + (2 * (d₁ + d₂) + 1) := by ring
        omega
      have h3 : (d₁ + d₂ + 1) ^ 2 ≤ (d₁ + d₂ + 1) ^ 3 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact le_trans h2 h3
    calc
      ((d₁ + d₂) ^ 2 + 1) * max d₁ d₂
          ≤ (d₁ + d₂ + 1) ^ 3 * (d₁ + d₂ + 1) := Nat.mul_le_mul hfac hmax
      _ = (d₁ + d₂ + 1) ^ 4 := by ring
  by_cases hdeg0 : (Curry0 h).natDegree = 0
  · by_cases kdeg0 : (Curry0 k).natDegree = 0
    · exact zeroCurry_zeroCurry_pair_intersection_bound h k hh hk hnot hdeg0 kdeg0
    · have kpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero kdeg0
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound h k hh hk hdeg kdeg hnot hdeg0 kpos
      exact ⟨hbound.1, le_trans hbound.2 htarget_mul⟩
  · have hpos : 0 < (Curry0 h).natDegree := Nat.pos_of_ne_zero hdeg0
    by_cases kdeg0 : (Curry0 k).natDegree = 0
    · have hnot' : ¬ Associated k h := by
        intro hAssoc
        exact hnot hAssoc.symm
      have hbound :=
        zeroCurry_nonvertical_pair_intersection_bound k h hk hh kdeg hdeg hnot' kdeg0 hpos
      have hbound' :
          (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧
            (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).ncard ≤ d₁ * d₂ := by
        simpa [Set.inter_comm, Nat.mul_comm] using hbound
      exact ⟨hbound'.1, le_trans hbound'.2 htarget_mul⟩
    · have kpos : 0 < (Curry0 k).natDegree := Nat.pos_of_ne_zero kdeg0
      have hprim : (Curry0 h).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree h hh hpos
      have kprim : (Curry0 k).IsPrimitive :=
        curry_isPrimitive_of_irreducible_positive_natDegree k hk kpos
      have hrel : IsRelPrime (Curry0 h) (Curry0 k) :=
        curry_isRelPrime_of_nonassociated_irreducibles h k hh hk hnot
      have hbound :=
        primitive_nonvertical_pair_intersection_bound h k hdeg kdeg hprim kprim hpos kpos hrel
      exact ⟨hbound.1, le_trans hbound.2 htarget_prim⟩
