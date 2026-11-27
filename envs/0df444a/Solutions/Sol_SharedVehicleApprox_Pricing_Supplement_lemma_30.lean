-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.lemma_30
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:55.737895+00:00
-- url     : https://prove2.me/submissions/2408d25d-2b1e-4389-9b41-9f8eea4dd4e3

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Lemma 30, p. 39 (corrected: the routing of `r̃` is strongly connected unless `q̃ = 0`, and
`q̃ ≠ 0` unless the total reward rate at each origin is nonnegative): the infinite-unit objective of the redirection policy
`r̃` of Algorithm 8, with every customer served when a unit is available, is at least the relaxation
value `Ôbj(q̃, r̃)`. -/
theorem solution {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I c : Fin n → Fin n → ℝ) (qt : Fin n → ℝ) (zt rt : Fin n → Fin n → ℝ)
    (hopt : IsAlg8Optimal φ I c qt zt) (hrt : rt = noPriceRedirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ∨ qt = 0)
    (hsign : qt ≠ 0 ∨ ∀ i, 0 ≤ ∑ j, φ i j * I i j)
    (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i)
    (htr : IsTraffic (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ρ) :
    alg8Obj φ I c qt zt ≤ noPriceObjInf φ I c rt ρ := by
      obtain ⟨⟨hq, hz, hcirc, hcap⟩, hoptim⟩ := hopt
      subst hrt
      have hq' : ∀ i, 0 ≤ qt i ∧ qt i ≤ 1 := fun i => hq i i
      set F : Fin n → ℝ := fun j => ∑ i, φ i j * qt i with hF
      have hF0 : ∀ j, 0 ≤ F j := fun j => sum_nonneg fun i _ => mul_nonneg (hφ i j) (hq' i).1
      have hcap' : ∀ i, ∑ k, zt i k ≤ F i := fun i => hcap i
      set r := noPriceRedirectProb φ qt zt with hr
      have hrdef : ∀ j k, r j k = zt j k / F j := fun j k => rfl
      have hr0 : ∀ j k, 0 ≤ r j k := fun j k => by rw [hrdef]; exact div_nonneg (hz j k) (hF0 j)
      have hR1 : ∀ j, ∑ k, r j k ≤ 1 := by
        intro j
        simp only [hrdef, ← Finset.sum_div]
        rcases (hF0 j).eq_or_lt with h | h
        · rw [← h, div_zero]; norm_num
        · rw [div_le_one h]; exact hcap' j
      have hzr : ∀ j k, zt j k = r j k * F j := by
        intro j k
        rw [hrdef]
        by_cases h : F j = 0
        · have hle := hcap' j
          rw [h] at hle
          have : zt j k = 0 :=
            le_antisymm ((single_le_sum (fun l _ => hz j l) (mem_univ k)).trans hle) (hz j k)
          rw [this, h]; simp
        · rw [div_mul_cancel₀ _ h]
      set D := inducedDemand φ (fun _ _ => 1) r with hD
      have hDdef : ∀ i j, D i j = φ i j * (1 - ∑ k, r j k) + ∑ k, φ i k * r k j := by
        intro i j; simp [hD, inducedDemand]
      have hD0 : ∀ i j, 0 ≤ D i j := by
        intro i j; rw [hDdef]
        exact add_nonneg (mul_nonneg (hφ i j) (by linarith [hR1 j]))
          (sum_nonneg fun k _ => mul_nonneg (hφ i k) (hr0 k j))
      have hDrow : ∀ i, ∑ k, D i k = ∑ k, φ i k := by
        intro i
        simp only [hDdef, sum_add_distrib, mul_sub, mul_one, sum_sub_distrib, mul_sum]
        rw [Finset.sum_comm (f := fun k l => φ i l * r l k)]
        ring
      have htq : ∀ i, ∑ j, qt j * D j i = qt i * ∑ k, D i k := by
        intro i
        have e1 : ∑ j, qt j * D j i = F i * (1 - ∑ k, r i k) + ∑ k, F k * r k i := by
          simp only [hDdef, hF, mul_add, sum_add_distrib, mul_sum, sum_mul]
          congr 1
          · exact sum_congr rfl fun j _ => by ring
          · rw [sum_comm]; exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
        have e2 : F i * ∑ k, r i k = ∑ k, zt i k := by
          rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [hzr]; ring
        have e3 : ∑ k, F k * r k i = ∑ k, zt k i :=
          sum_congr rfl fun k _ => by rw [hzr]; ring
        have hc := hcirc i
        simp only [sum_add_distrib, ← sum_mul] at hc
        rw [hDrow, e1, mul_sub, mul_one, e2, e3, mul_comm (qt i)]
        have : ∑ k, φ k i * qt k = F i := rfl
        rw [this] at hc
        linarith
      have hcz : ∑ j, ∑ k, c j k * zt j k = ∑ i, qt i * ∑ j, φ i j * ∑ k, r j k * c j k := by
        calc ∑ j, ∑ k, c j k * zt j k = ∑ j, F j * ∑ k, r j k * c j k := by
              refine sum_congr rfl fun j _ => ?_
              rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [hzr]; ring
          _ = ∑ j, ∑ i, qt i * (φ i j * ∑ k, r j k * c j k) := by
              refine sum_congr rfl fun j _ => ?_
              simp only [hF, sum_mul]; exact sum_congr rfl fun i _ => by ring
          _ = _ := by
              rw [sum_comm]; exact sum_congr rfl fun i _ => by rw [mul_sum]
      have hV : alg8Obj φ I c qt zt = ∑ i, qt i * ∑ j, φ i j * (I i j - ∑ k, r j k * c j k) := by
        have : alg8Obj φ I c qt zt = ∑ i, ∑ j, φ i j * qt i * I i j - ∑ i, ∑ j, c i j * zt i j := by
          unfold alg8Obj; simp only [sum_sub_distrib]
        rw [this, hcz, ← sum_sub_distrib]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by ring
      have hX : noPriceObjInf φ I c r ρ = ∑ i, ρ i / rmax ρ * ∑ j, φ i j * (I i j - ∑ k, r j k * c j k) := rfl
      have hV0 : 0 ≤ alg8Obj φ I c qt zt := by
        have hfeas : IsAlg8Feasible φ (fun _ => 0) (fun _ _ => 0) :=
          ⟨fun i j => ⟨le_refl _, zero_le_one⟩, fun i j => le_refl _, fun i => by simp, fun i => by simp⟩
        have := hoptim _ _ hfeas
        simpa [alg8Obj] using this
      obtain ⟨istar, -, hstar⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin n)) ρ
      have hMdef : rmax ρ = ρ istar := hstar
      have hM : 0 < rmax ρ := hMdef ▸ hρ istar
      rw [hX, hV] at *
      set B : Fin n → ℝ := fun i => ∑ j, φ i j * (I i j - ∑ k, r j k * c j k) with hB
      by_cases hq0 : qt = 0
      · have hq0' : ∀ i, qt i = 0 := fun i => congrFun hq0 i
        have hs := hsign.resolve_left (not_not.2 hq0)
        have hrz : ∀ j k, r j k = 0 := by
          intro j k; rw [hrdef]
          have : F j = 0 := by simp [hF, hq0']
          rw [this, div_zero]
        have hB0 : ∀ i, 0 ≤ B i := by
          intro i; simp only [hB, hrz, zero_mul, sum_const_zero, sub_zero]; exact hs i
        simp only [hq0', zero_mul, sum_const_zero]
        exact sum_nonneg fun i _ => mul_nonneg (div_nonneg (hρ i).le hM.le) (hB0 i)
      · have hconn' := hconn.resolve_right hq0
        obtain ⟨i0, -, hi0⟩ := exists_min_image univ (fun i => qt i / ρ i) univ_nonempty
        set t := qt i0 / ρ i0 with ht
        have hw0 : ∀ i, 0 ≤ qt i - t * ρ i := fun i => by
          have := hi0 i (mem_univ _)
          rw [le_div_iff₀ (hρ i)] at this; linarith
        have hwtr : ∀ i, ∑ j, (qt j - t * ρ j) * D j i = (qt i - t * ρ i) * ∑ k, D i k := by
          intro i
          have h1 := htq i
          have h2 := htr i
          simp only [mul_one] at h2
          have h3 : ∑ j, t * ρ j * D j i = t * ∑ j, ρ j * D j i := by
            rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
          simp only [sub_mul, sum_sub_distrib]
          rw [h1, h3, h2]; ring
        have hprop : ∀ a b, (a ≠ b ∧ 0 < D a b * 1) → qt b - t * ρ b = 0 → qt a - t * ρ a = 0 := by
          intro a b ⟨_, hab⟩ hb
          have hsum := hwtr b
          rw [hb, zero_mul] at hsum
          have := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw0 j) (hD0 j b))).1 hsum a
            (mem_univ a)
          rw [mul_one] at hab
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        have hall : ∀ a, qt a = t * ρ a := by
          intro a
          have hpath := hconn' a i0
          suffices qt a - t * ρ a = 0 by linarith
          induction hpath using Relation.ReflTransGen.head_induction_on with
          | refl => rw [ht]; field_simp [(hρ i0).ne']; ring
          | head hab _ ih => exact hprop _ _ hab ih
        have ht0 : 0 ≤ t := div_nonneg (hq' i0).1 (hρ i0).le
        have htpos : 0 < t := by
          rcases ht0.eq_or_lt with h | h
          · exfalso; apply hq0; funext i; rw [hall i, ← h, zero_mul]; rfl
          · exact h
        have htM : t * rmax ρ ≤ 1 := by rw [hMdef, ← hall istar]; exact (hq' istar).2
        have hVS : ∑ i, qt i * B i = t * ∑ i, ρ i * B i := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [hall i]; ring
        have hXS : ∑ i, ρ i / rmax ρ * B i = (∑ i, ρ i * B i) / rmax ρ := by
          rw [sum_div]; exact sum_congr rfl fun i _ => by ring
        have hV0' : 0 ≤ t * ∑ i, ρ i * B i := by rw [← hVS]; exact hV0
        rw [hVS, hXS]
        have hS : 0 ≤ ∑ i, ρ i * B i := (mul_nonneg_iff_of_pos_left htpos).1 hV0'
        rw [le_div_iff₀ hM]
        nlinarith [mul_le_mul_of_nonneg_right htM hS]
