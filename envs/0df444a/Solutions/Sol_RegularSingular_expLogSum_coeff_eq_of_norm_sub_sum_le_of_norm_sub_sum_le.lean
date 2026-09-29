-- Prove2me | solution 1 for RegularSingular.expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bb8dd9be-4654-567d-a780-8edabb8236c5

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le

set_option autoImplicit false

open Finset

namespace RegularSingular
namespace UnionUniqAux

theorem sum_fiber_eq_of_injective {ι : Type*} [Fintype ι] [DecidableEq (ℂ × ℕ)] (f : ι → ℂ × ℕ)
    (hf : Function.Injective f) (c : ι → ℂ) (i₀ : ι) :
    ∑ i ∈ univ.filter (fun i => f i = f i₀), c i = c i₀ := by
  refine Finset.sum_eq_single_of_mem i₀ (by simp) fun i hi hne => ?_
  exact absurd (hf (Finset.mem_filter.1 hi).2) hne

theorem sum_fiber_eq_zero_of_not_mem {ι : Type*} [Fintype ι] [DecidableEq (ℂ × ℕ)] (f : ι → ℂ × ℕ)
    (c : ι → ℂ) (p : ℂ × ℕ) (hp : ∀ i, f i ≠ p) :
    ∑ i ∈ univ.filter (fun i => f i = p), c i = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (Finset.mem_filter.1 hi).2 (hp i)

theorem sum_eq_sum_fiber {ι : Type*} [Fintype ι] [DecidableEq (ℂ × ℕ)] (f : ι → ℂ × ℕ) (P : Finset (ℂ × ℕ))
    (hP : ∀ i, f i ∈ P) (c : ι → ℂ) (w : ℂ × ℕ → ℂ) :
    ∑ i, c i * w (f i) = ∑ p ∈ P, (∑ i ∈ univ.filter (fun i => f i = p), c i) * w p := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := P) (g := f) (fun i _ => hP i)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

end RegularSingular.UnionUniqAux

open RegularSingular.UnionUniqAux in
theorem solution
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (e₁ : ι₁ → ℂ) (n₁ : ι₁ → ℕ) (h₁ : Function.Injective fun i => (e₁ i, n₁ i))
    (e₂ : ι₂ → ℂ) (n₂ : ι₂ → ℕ) (h₂ : Function.Injective fun k => (e₂ k, n₂ k))
    (c₁ : ι₁ → ℂ) (c₂ : ι₂ → ℂ) (θ : ℝ) (F : ℝ → ℂ)
    (hF₁ : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)‖ ≤ K * y ^ θ)
    (hF₂ : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k)‖ ≤ K * y ^ θ) :
    (∀ i k, e₁ i = e₂ k → n₁ i = n₂ k → (e₁ i).re < θ → c₁ i = c₂ k) ∧
    (∀ i, (e₁ i).re < θ → (∀ k, (e₂ k, n₂ k) ≠ (e₁ i, n₁ i)) → c₁ i = 0) ∧
    (∀ k, (e₂ k).re < θ → (∀ i, (e₁ i, n₁ i) ≠ (e₂ k, n₂ k)) → c₂ k = 0) := by
  classical
  obtain ⟨K₁, hK₁⟩ := hF₁
  obtain ⟨K₂, hK₂⟩ := hF₂
  set f₁ : ι₁ → ℂ × ℕ := fun i => (e₁ i, n₁ i) with hf₁
  set f₂ : ι₂ → ℂ × ℕ := fun k => (e₂ k, n₂ k) with hf₂
  set P : Finset (ℂ × ℕ) := univ.image f₁ ∪ univ.image f₂ with hP
  have hP₁ : ∀ i, f₁ i ∈ P := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hP₂ : ∀ k, f₂ k ∈ P := fun k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

  set dcoef : ℂ × ℕ → ℂ := fun p =>
    (∑ i ∈ univ.filter (fun i => f₁ i = p), c₁ i) - ∑ k ∈ univ.filter (fun k => f₂ k = p), c₂ k with hd
  set w : ℝ → ℂ × ℕ → ℂ := fun y p => (y : ℂ) ^ p.1 * (Real.log y : ℂ) ^ p.2 with hw
  have hdiff : ∀ y : ℝ, (∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)) -
      ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k) = ∑ p : ↥P, dcoef p.1 * w y p.1 := by
    intro y
    have h1 : ∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i) = ∑ i, c₁ i * w y (f₁ i) := rfl
    have h2 : ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k) = ∑ k, c₂ k * w y (f₂ k) := rfl
    rw [h1, h2, sum_eq_sum_fiber f₁ P hP₁ c₁ (w y), sum_eq_sum_fiber f₂ P hP₂ c₂ (w y), ← Finset.sum_sub_distrib,
      ← Finset.sum_coe_sort P]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hd]; ring

  have hinjP : Function.Injective fun p : ↥P => ((p.1.1 : ℂ), (p.1.2 : ℕ)) := by
    intro p q h; exact Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have key := LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    (ι := ↥P) (fun p => p.1.1) (fun p => p.1.2) (fun p => dcoef p.1) hinjP θ
    (fun y => (∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)) -
      ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k)) (fun _ => 0)
    (fun y _ _ => by beta_reduce; rw [add_zero, hdiff])
    ⟨0, fun y hy _ => by simp⟩
    ⟨K₁ + K₂, fun y hy0 hy1 => by
      beta_reduce
      have hA := hK₁ y hy0 hy1
      have hB := hK₂ y hy0 hy1
      have : (∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)) -
          ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k) =
          (F y - ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k)) -
            (F y - ∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)) := by ring
      rw [this]
      calc _ ≤ ‖F y - ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k)‖ +
            ‖F y - ∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)‖ := norm_sub_le _ _
        _ ≤ K₂ * y ^ θ + K₁ * y ^ θ := add_le_add hB hA
        _ = (K₁ + K₂) * y ^ θ := by ring⟩
  have hzero : ∀ p : ↥P, (p.1.1).re < θ → dcoef p.1 = 0 := fun p hp => key p hp
  refine ⟨fun i k he hn hre => ?_, fun i hre habs => ?_, fun k hre habs => ?_⟩
  · have h := hzero ⟨f₁ i, hP₁ i⟩ hre
    have hfk : f₂ k = f₁ i := Prod.ext he.symm hn.symm
    simp only [hd] at h
    rw [sum_fiber_eq_of_injective f₁ h₁ c₁ i, ← hfk, sum_fiber_eq_of_injective f₂ h₂ c₂ k] at h
    exact sub_eq_zero.1 h
  · have h := hzero ⟨f₁ i, hP₁ i⟩ hre
    simp only [hd] at h
    rw [sum_fiber_eq_of_injective f₁ h₁ c₁ i, sum_fiber_eq_zero_of_not_mem f₂ c₂ (f₁ i) habs, sub_zero] at h
    exact h
  · have h := hzero ⟨f₂ k, hP₂ k⟩ hre
    simp only [hd] at h
    rw [sum_fiber_eq_of_injective f₂ h₂ c₂ k, sum_fiber_eq_zero_of_not_mem f₁ c₁ (f₂ k) habs, zero_sub,
      neg_eq_zero] at h
    exact h

end S_RegularSingular_expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le
end P2MW
export P2MW.S_RegularSingular_expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le (solution)
