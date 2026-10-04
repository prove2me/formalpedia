-- Prove2me | solution 1 for StarShapedRisk.Representation.theorem1_inf_convolution
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T06:18:28.43508+00:00
-- url     : https://prove2.me/submissions/0f0eb4e9-838f-47e8-9727-8638c89c5b70

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet
import Definitions.Def_StarShapedRisk_Representation_Aggregation

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace StarShapedRisk.Representation
open StarShapedRisk.Representation

theorem sr_star_small {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hs : IsStarShaped 𝒳 ρ) (X : 𝒳.carrier) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ρ (t • X) ≤ t * ρ X := by
  have hh := hs (t • X) t⁻¹ ((one_lt_inv₀ ht0).mpr ht1)
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm


theorem sr_risk_const {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) (m : ℝ) : ρ (𝒳.const m)=m := by
  have he : (0 : 𝒳.carrier)-𝒳.const (-m)=𝒳.const m := by ext ω; simp [PositionSpace.const]
  have hh := hρ.2.1 0 (-m)
  have hn : ρ 0=0 := hρ.2.2
  rw [he,hn] at hh
  simpa using hh

theorem sr_shifts_bounds {Ω : Type*} (𝒳 : PositionSpace Ω) (A : Set 𝒳.carrier)
    (hA : IsAcceptanceSet 𝒳 A) (X : 𝒳.carrier) :
    {m : ℝ | X-𝒳.const m ∈ A}.Nonempty ∧ BddBelow {m : ℝ | X-𝒳.const m ∈ A} := by
  obtain ⟨C,hC⟩ := 𝒳.bounded X X.property
  obtain ⟨m,hm⟩ := hA.1.nonempty
  constructor
  · refine ⟨C-m,hA.2 (𝒳.const m) hm (X-𝒳.const (C-m)) ?_⟩
    intro ω
    change X.val ω-(C-m) ≤ m
    have := (abs_le.mp (hC ω)).2
    linarith
  · refine ⟨-C,?_⟩
    intro m hm
    have hac : 𝒳.const (-C-m) ∈ A := hA.2 _ hm _ (by
      intro ω
      change -C-m ≤ X.val ω-m
      have := (abs_le.mp (hC ω)).1
      linarith)
    have hh := hA.1.1 hac
    change -C-m ≤ 0 at hh
    linarith


end StarShapedRisk.Representation

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical
namespace StarShapedRisk.Representation
variable {Ω : Type*} (𝒳 : PositionSpace Ω) {n : ℕ}

def sr_shift (k : Fin n) (Y : Fin n → 𝒳.carrier) (V : 𝒳.carrier) : Fin n → 𝒳.carrier :=
  fun i => Y i + if i = k then V else 0

lemma sr_shift_sum (k : Fin n) (Y : Fin n → 𝒳.carrier) (V : 𝒳.carrier) :
    ∑ i, sr_shift 𝒳 k Y V i = (∑ i, Y i) + V := by
  simp [sr_shift, Finset.sum_add_distrib]

lemma sr_shift_cost (ρ : Fin n → 𝒳.carrier → ℝ) (k : Fin n)
    (Y : Fin n → 𝒳.carrier) (V : 𝒳.carrier) :
    ∑ i, ρ i (sr_shift 𝒳 k Y V i) = (∑ i, ρ i (Y i)) - ρ k (Y k) + ρ k (Y k + V) := by
  have he : ∑ i ∈ Finset.univ.erase k, ρ i (sr_shift 𝒳 k Y V i) =
      ∑ i ∈ Finset.univ.erase k, ρ i (Y i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [sr_shift, (Finset.mem_erase.mp hi).1]
  rw [← Finset.add_sum_erase Finset.univ (fun i => ρ i (sr_shift 𝒳 k Y V i)) (Finset.mem_univ k),
    ← Finset.add_sum_erase Finset.univ (fun i => ρ i (Y i)) (Finset.mem_univ k), he]
  simp [sr_shift, add_comm]

def sr_costs (ρ : Fin n → 𝒳.carrier → ℝ) (X : 𝒳.carrier) : Set ℝ :=
  {s | ∃ Y : Fin n → 𝒳.carrier, ∑ i, Y i = X ∧ s = ∑ i, ρ i (Y i)}

lemma sr_costs_bounds (hn : 0 < n) (ρ : Fin n → 𝒳.carrier → ℝ)
    (hρ : ∀ i, IsRiskMeasure 𝒳 (ρ i)) (hN : NormalityCondition 𝒳 ρ) (X : 𝒳.carrier) :
    (sr_costs 𝒳 ρ X).Nonempty ∧ BddBelow (sr_costs 𝒳 ρ X) := by
  let k : Fin n := ⟨0, hn⟩
  constructor
  · refine ⟨∑ i, ρ i (sr_shift 𝒳 k (fun _ => 0) X i), sr_shift 𝒳 k (fun _ => 0) X, ?_, rfl⟩
    simp [sr_shift_sum]
  · obtain ⟨C, hC⟩ := 𝒳.bounded X X.property
    refine ⟨-C, ?_⟩
    rintro s ⟨Y, hY, rfl⟩
    have hZ : ∑ i, sr_shift 𝒳 k Y (-X) i = 0 := by rw [sr_shift_sum, hY]; simp
    have hh := hN _ hZ
    rw [sr_shift_cost] at hh
    have hc : ρ k (Y k - X) ≤ ρ k (Y k) + C := by
      have hm := (hρ k).1 (Y k - 𝒳.const (-C)) (Y k - X) (fun ω => by
        change (Y k).val ω - X.val ω ≤ (Y k).val ω - (-C)
        linarith [(abs_le.mp (hC ω)).1])
      rw [(hρ k).2.1] at hm
      simpa using hm
    change 0 ≤ (∑ i, ρ i (Y i)) - ρ k (Y k) + ρ k (Y k - X) at hh
    linarith

end StarShapedRisk.Representation

open StarShapedRisk.Representation
theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω) {n : ℕ} (hn : 0 < n)
    (ρ : Fin n → 𝒳.carrier → ℝ) (hρ : ∀ i, IsStarShapedRiskMeasure 𝒳 (ρ i))
    (h10 : NormalityCondition 𝒳 ρ) :
    IsStarShapedRiskMeasure 𝒳 (infConvolution 𝒳 ρ) := by
  have hr (i : Fin n) := (hρ i).1
  have hb := sr_costs_bounds 𝒳 hn ρ hr h10
  let k : Fin n := ⟨0, hn⟩
  change (IsMonotone 𝒳 (infConvolution 𝒳 ρ) ∧ IsTranslationInvariant 𝒳 (infConvolution 𝒳 ρ) ∧
    IsNormalized 𝒳 (infConvolution 𝒳 ρ)) ∧ IsStarShaped 𝒳 (infConvolution 𝒳 ρ)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro X Y hYX
    apply le_csInf (hb X).1
    rintro s ⟨Z, hZ, rfl⟩
    have hz : ∑ i, sr_shift 𝒳 k Z (Y - X) i = Y := by rw [sr_shift_sum, hZ]; abel
    have hi := csInf_le (hb Y).2 (show (∑ i, ρ i (sr_shift 𝒳 k Z (Y-X) i)) ∈ sr_costs 𝒳 ρ Y from ⟨_, hz, rfl⟩)
    have hm := (hr k).1 (Z k) (Z k + (Y-X)) (fun ω => by
      change (Z k).val ω + (Y.val ω - X.val ω) ≤ (Z k).val ω
      linarith [hYX ω])
    rw [sr_shift_cost] at hi
    change infConvolution 𝒳 ρ Y ≤ (∑ i, ρ i (Z i)) - ρ k (Z k) + ρ k (Z k + (Y-X)) at hi
    linarith
  · intro X m
    have hl : infConvolution 𝒳 ρ X - m ≤ infConvolution 𝒳 ρ (X - 𝒳.const m) := by
      apply le_csInf (hb _).1
      rintro s ⟨Z, hZ, rfl⟩
      have hz : ∑ i, sr_shift 𝒳 k Z (𝒳.const m) i = X := by rw [sr_shift_sum, hZ]; abel
      have hi := csInf_le (hb X).2 (show (∑ i, ρ i (sr_shift 𝒳 k Z (𝒳.const m) i)) ∈ sr_costs 𝒳 ρ X from ⟨_, hz, rfl⟩)
      rw [sr_shift_cost] at hi
      have he : Z k + 𝒳.const m = Z k - 𝒳.const (-m) := by ext ω; simp [PositionSpace.const]
      rw [he, (hr k).2.1] at hi
      change infConvolution 𝒳 ρ X ≤ _ at hi
      linarith
    have hu : infConvolution 𝒳 ρ (X - 𝒳.const m) + m ≤ infConvolution 𝒳 ρ X := by
      apply le_csInf (hb X).1
      rintro s ⟨Z, hZ, rfl⟩
      have hz : ∑ i, sr_shift 𝒳 k Z (-𝒳.const m) i = X - 𝒳.const m := by rw [sr_shift_sum, hZ]; abel
      have hi := csInf_le (hb _).2 (show (∑ i, ρ i (sr_shift 𝒳 k Z (-𝒳.const m) i)) ∈ sr_costs 𝒳 ρ (X-𝒳.const m) from ⟨_, hz, rfl⟩)
      rw [sr_shift_cost] at hi
      change infConvolution 𝒳 ρ (X-𝒳.const m) ≤ (∑ i, ρ i (Z i)) - ρ k (Z k) + ρ k (Z k-𝒳.const m) at hi
      rw [(hr k).2.1] at hi
      linarith
    linarith
  · apply le_antisymm
    · apply csInf_le (hb 0).2
      exact ⟨fun _ => 0, by simp, by
        have hz : ∀ i, ρ i 0 = 0 := fun i => (hr i).2.2
        simp only [hz, Finset.sum_const_zero]⟩
    · apply le_csInf (hb 0).1
      rintro s ⟨Z, hZ, rfl⟩
      exact h10 Z hZ
  · intro X t ht
    have ht0 : 0 < t := by linarith
    apply le_csInf (hb (t • X)).1
    rintro s ⟨Z, hZ, rfl⟩
    let Y : Fin n → 𝒳.carrier := fun i => t⁻¹ • Z i
    have hY : ∑ i, Y i = X := by
      dsimp [Y]; rw [← Finset.smul_sum, hZ, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    have hi := csInf_le (hb X).2 (show (∑ i, ρ i (Y i)) ∈ sr_costs 𝒳 ρ X from ⟨Y, hY, rfl⟩)
    change infConvolution 𝒳 ρ X ≤ (∑ i, ρ i (Y i)) at hi
    have hh : t * (∑ i, ρ i (Y i)) ≤ ∑ i, ρ i (Z i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hi := (hρ i).2 (Y i) t ht
      simpa [Y, smul_smul, mul_inv_cancel₀ ht0.ne'] using hi
    exact (mul_le_mul_of_nonneg_left hi ht0.le).trans hh


#check solution
#print axioms solution
