-- Prove2me | solution 1 for PriceCapacities.LowerBound.lemma_10_5
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:23:13.602236+00:00
-- url     : https://prove2.me/submissions/08ea8454-418c-409a-b972-ed3ed65090c9

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
import Definitions.Def_PriceCapacities_LowerBound_CapacitatedCoreset
import Definitions.Def_PriceCapacities_LowerBound_DualCost

set_option autoImplicit false

open PriceCapacities
open PriceCapacities.LowerBound

private theorem exists_assignment {X : Type*} {k : ℕ} (S : WeightedSet X) (h : Fin k → ℝ)
    (hh : IsFeasibleLoad (totalWeight S) h) : ∃ a : X → Fin k → ℝ, IsLoadAssignment S h a := by
  have total : totalWeight S = ∑ x ∈ S.support, (S x : ℝ) := by simp [totalWeight, wsum]
  let a (x : X) (i : Fin k) := (S x : ℝ) * (h i / totalWeight S)
  have nonneg : 0 ≤ totalWeight S := by
    rw [total]
    exact Finset.sum_nonneg fun _ _ => NNReal.zero_le_coe
  refine ⟨a, fun x i => mul_nonneg NNReal.zero_le_coe (div_nonneg (hh.1 i) nonneg), ?_, ?_⟩
  · intro x hx
    dsimp [a]
    rw [← Finset.mul_sum, ← Finset.sum_div, hh.2, div_self, mul_one]
    intro hzero
    have hw := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => NNReal.zero_le_coe (q := S y))).1
      (total.symm.trans hzero) x hx
    exact (Finsupp.mem_support_iff.mp hx) (by exact_mod_cast hw)
  · intro i
    dsimp [a]
    rw [← Finset.sum_mul, ← total]
    by_cases hzero : totalWeight S = 0
    · rw [hzero, zero_mul]
      exact ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hh.1 j)).1
        (hh.2.trans hzero) i (Finset.mem_univ i)).symm
    · field_simp

private noncomputable def dotLoad {k : ℕ} (β h : Fin k → ℝ) : ℝ := ∑ i, β i * h i

private noncomputable def priceScaled {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (z scale : ℝ) (C : Fin k → X) (β : Fin k → ℝ) (x : X) : ℝ :=
  ⨅ i : Fin k, (scale * dist x (C i) ^ z + β i)

private theorem price_le {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (z scale : ℝ) (C : Fin k → X) (β : Fin k → ℝ) (x : X) (i : Fin k) :
    priceScaled z scale C β x ≤ scale * dist x (C i) ^ z + β i :=
  ciInf_le (Set.finite_range _).bddBelow i

private theorem price_min {X : Type*} [PseudoMetricSpace X] {k : ℕ} [Nonempty (Fin k)]
    (z scale : ℝ) (C : Fin k → X) (β : Fin k → ℝ) (x : X) :
    ∃ i : Fin k, priceScaled z scale C β x = scale * dist x (C i) ^ z + β i := by
  let f (i : Fin k) := scale * dist x (C i) ^ z + β i
  obtain ⟨i, _, h⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨i, le_antisymm (price_le z scale C β x i) (le_ciInf fun j => h j (Finset.mem_univ j))⟩

private theorem priced_expansion {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (z scale : ℝ) (S : WeightedSet X) (C : Fin k → X) (β h : Fin k → ℝ)
    (a : X → Fin k → ℝ) (ha : IsLoadAssignment S h a) :
    scale * assignmentCost z S C a + dotLoad β h =
      ∑ x ∈ S.support, ∑ i, a x i * (scale * dist x (C i) ^ z + β i) := by
  have hload : dotLoad β h = ∑ x ∈ S.support, ∑ i, a x i * β i := by
    unfold dotLoad
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha.2.2 i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hload]
  simp only [assignmentCost, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem priced_assignment_lower {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (z scale : ℝ) (S : WeightedSet X) (C : Fin k → X) (β h : Fin k → ℝ)
    (a : X → Fin k → ℝ) (ha : IsLoadAssignment S h a) :
    wsum S (priceScaled z scale C β) ≤ scale * assignmentCost z S C a + dotLoad β h := by
  rw [priced_expansion z scale S C β h a ha]
  unfold wsum
  refine Finset.sum_le_sum fun x hx => ?_
  rw [← ha.2.1 x hx, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (price_le z scale C β x i) (ha.1 x i)

private theorem priced_load_lower {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (z scale : ℝ) (hscale : 0 < scale) (S : WeightedSet X) (C : Fin k → X) (β h : Fin k → ℝ)
    (hh : IsFeasibleLoad (totalWeight S) h) :
    wsum S (priceScaled z scale C β) ≤ scale * capCost z S C h + dotLoad β h := by
  have hw : (wsum S (priceScaled z scale C β) - dotLoad β h) / scale ≤ capCost z S C h := by
    obtain ⟨a, ha⟩ := exists_assignment S h hh
    unfold capCost
    refine le_csInf ⟨_, a, ha, rfl⟩ ?_
    rintro _ ⟨b, hb, rfl⟩
    apply (div_le_iff₀ hscale).2
    have h' := priced_assignment_lower z scale S C β h b hb
    linarith
  have hw' := (div_le_iff₀ hscale).1 hw
  linarith

private theorem priced_greedy {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (z scale : ℝ) (S : WeightedSet X) (C : Fin k → X) (β : Fin k → ℝ)
    (winner : X → Fin k)
    (hwin : ∀ x, priceScaled z scale C β x = scale * dist x (C (winner x)) ^ z + β (winner x)) :
    ∃ h : Fin k → ℝ, IsFeasibleLoad (totalWeight S) h ∧
      capCost z S C h ≤ wsum S (fun x => dist x (C (winner x)) ^ z) ∧
      wsum S (priceScaled z scale C β) =
        scale * wsum S (fun x => dist x (C (winner x)) ^ z) + dotLoad β h := by
  classical
  let a (x : X) (i : Fin k) : ℝ := if i = winner x then S x else 0
  let h (i : Fin k) := ∑ x ∈ S.support, a x i
  have hn (x : X) (i : Fin k) : 0 ≤ a x i := by dsimp [a]; split <;> positivity
  have hr (x : X) : ∑ i, a x i = (S x : ℝ) := by simp [a]
  have hh : IsFeasibleLoad (totalWeight S) h := by
    refine ⟨fun i => Finset.sum_nonneg fun x _ => hn x i, ?_⟩
    dsimp [h]
    rw [Finset.sum_comm]
    simp only [hr, totalWeight, wsum, mul_one]
  have ha : IsLoadAssignment S h a := ⟨hn, fun x _ => hr x, fun _ => rfl⟩
  have hcost : assignmentCost z S C a = wsum S (fun x => dist x (C (winner x)) ^ z) := by
    simp [assignmentCost, wsum, a]
  refine ⟨h, hh, ?_, ?_⟩
  · rw [← hcost]
    exact csInf_le ⟨0, by
      rintro _ ⟨b, hb, rfl⟩
      exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ =>
        mul_nonneg (hb.1 x i) (Real.rpow_nonneg dist_nonneg _)⟩ ⟨a, ha, rfl⟩
  · rw [← hcost, priced_expansion z scale S C β h a ha]
    unfold wsum
    apply Finset.sum_congr rfl
    intro x _
    rw [hwin]
    simp [a]

theorem solution (d k z : ℕ) (hz : 1 ≤ z) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
    (P Q : WeightedSet (EuclideanSpace ℝ (Fin d)))
    (hQ : IsCapacitatedCoreset k (z : ℝ) ε P Q)
    (C : Fin k → EuclideanSpace ℝ (Fin d)) (β : Fin k → ℝ)
    (σ : EuclideanSpace ℝ (Fin d) → Fin k)
    (hσ : ∀ p ∈ P.support, ∀ i : Fin k,
      (1 - ε) * dist p (C (σ p)) ^ (z : ℝ) + β (σ p) ≤ (1 - ε) * dist p (C i) ^ (z : ℝ) + β i) :
    |wsum Q (pricedCost (z : ℝ) C β) - wsum P (pricedCost (z : ℝ) C β)|
      ≤ ε * wsum P (fun p => dist p (C (σ p)) ^ (z : ℝ)) := by
  by_cases hk : k = 0
  · subst k
    exact (σ 0).elim0
  let X := EuclideanSpace ℝ (Fin d)
  let _ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
  let ρ : ℝ := 1 - ε
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let W (S : WeightedSet X) (r : ℝ) := wsum S (priceScaled (z : ℝ) r C β)
  let D (S : WeightedSet X) (τ : X → Fin k) := wsum S (fun x => dist x (C (τ x)) ^ (z : ℝ))
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (price_min (z : ℝ) 1 C β)
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice (price_min (z : ℝ) 1 C β)
  obtain ⟨hP, hPfeas, hPcap, hPprice⟩ := priced_greedy (z : ℝ) 1 P C β f hf
  obtain ⟨hQ', hQfeas, hQcap, hQprice⟩ := priced_greedy (z : ℝ) 1 Q C β g hg
  have hD : D P f ≤ D P σ := by
    unfold D wsum
    apply Finset.sum_le_sum
    intro x hx
    apply mul_le_mul_of_nonneg_left _ NNReal.zero_le_coe
    have h₁ := price_le (z : ℝ) 1 C β x (σ x)
    rw [hf x] at h₁
    have h₂ := hσ x hx (f x)
    apply (mul_le_mul_iff_right₀ hε0).mp
    linarith
  have hdisc : W P 1 - W P ρ ≤ ε * D P σ := by
    unfold W D wsum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hMin : priceScaled (z : ℝ) ρ C β x = ρ * dist x (C (σ x)) ^ (z : ℝ) + β (σ x) :=
      le_antisymm (price_le (z : ℝ) ρ C β x (σ x)) (le_ciInf (hσ x hx))
    have h1 := price_le (z : ℝ) 1 C β x (σ x)
    rw [← mul_sub]
    have h := mul_le_mul_of_nonneg_left (show priceScaled (z : ℝ) 1 C β x - priceScaled (z : ℝ) ρ C β x ≤
      ε * dist x (C (σ x)) ^ (z : ℝ) by rw [hMin]; dsimp [ρ]; linarith) (NNReal.zero_le_coe (q := P x))
    convert h using 1 <;> ring
  have upper : W Q 1 - W P 1 ≤ ε * D P σ := by
    have hcoreset := (abs_le.mp (hQ.2 C hP hPfeas)).2
    have hQbound := priced_load_lower (z : ℝ) 1 (by norm_num) Q C β hP (hQ.1.symm ▸ hPfeas)
    change W Q 1 ≤ 1 * capCost (z : ℝ) Q C hP + dotLoad β hP at hQbound
    change W P 1 = 1 * D P f + dotLoad β hP at hPprice
    have hεcap := mul_le_mul_of_nonneg_left (hPcap.trans hD) hε0.le
    linarith
  have lower : W P ρ ≤ W Q 1 := by
    have hcoreset := (abs_le.mp (hQ.2 C hQ' (hQ.1 ▸ hQfeas))).1
    have hPbound := priced_load_lower (z : ℝ) ρ hρ P C β hQ' (hQ.1 ▸ hQfeas)
    change W P ρ ≤ ρ * capCost (z : ℝ) P C hQ' + dotLoad β hQ' at hPbound
    change W Q 1 = 1 * D Q g + dotLoad β hQ' at hQprice
    dsimp [ρ] at hPbound
    linarith
  have hprice : priceScaled (z : ℝ) 1 C β = pricedCost (z : ℝ) C β := by
    funext x
    simp [priceScaled, pricedCost]
  change |wsum Q (pricedCost (z : ℝ) C β) - wsum P (pricedCost (z : ℝ) C β)| ≤ ε * D P σ
  rw [← hprice]
  change |W Q 1 - W P 1| ≤ ε * D P σ
  exact abs_le.mpr ⟨by linarith, upper⟩
