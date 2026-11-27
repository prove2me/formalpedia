-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:47.574349+00:00
-- url     : https://prove2.me/submissions/894c0ee2-677a-48e6-9241-0a80987e8c74

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_Allocation

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (hex : Exchangeable μ) (htwo : TwoValued μ)
    (β : ℝ) (hβ : β ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    optAllocation μ β ≤ optAllocation μ (1 / 2) := by
      have hU : ∀ (u price : Option (Fin 2) → ℝ), menuRevenue Finset.univ u price = 0 ∨
          ∃ o, 0 ≤ u o ∧ (∀ o', u o' ≤ u o) ∧ menuRevenue Finset.univ u price = price o := by
        intro u price
        unfold menuRevenue
        dsimp only
        split_ifs with h
        · right
          obtain ⟨o, ho, he⟩ := Finset.exists_mem_eq_sup' h price
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
          exact ⟨o, ho.1, fun o' => ho.2 o' trivial, he⟩
        · left; rfl
      have hL : ∀ (u price : Option (Fin 2) → ℝ) (o : Option (Fin 2)), 0 ≤ u o →
          (∀ o', u o' ≤ u o) → price o ≤ menuRevenue Finset.univ u price := by
        intro u price o h0 h1
        unfold menuRevenue
        dsimp only
        split_ifs with h
        · apply Finset.le_sup'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, forall_const]
          exact ⟨h0, h1⟩
        · exfalso; apply h; refine ⟨o, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, forall_const]
          exact ⟨h0, h1⟩
      have hU' : ∀ (β p r : ℝ) (v : Fin 2 → ℝ) (x0 x1 : ℝ), v 0 = x0 → v 1 = x1 →
          allocationRevenue β p r v = 0 ∨
          (0 ≤ x0 - p ∧ x1 - p ≤ x0 - p ∧ β * x0 + (1 - β) * x1 - r ≤ x0 - p ∧
            allocationRevenue β p r v = p) ∨
          (0 ≤ x1 - p ∧ x0 - p ≤ x1 - p ∧ β * x0 + (1 - β) * x1 - r ≤ x1 - p ∧
            allocationRevenue β p r v = p) ∨
          (0 ≤ β * x0 + (1 - β) * x1 - r ∧ x0 - p ≤ β * x0 + (1 - β) * x1 - r ∧
            x1 - p ≤ β * x0 + (1 - β) * x1 - r ∧ allocationRevenue β p r v = r) := by
        intro β p r v x0 x1 e0 e1
        rcases hU (fun o => allocationValue β v o - allocationPrice p r o) (allocationPrice p r) with
          h | ⟨o, h0, h1, h2⟩
        · left; exact h
        · right
          have a0 := h1 (some 0)
          have a1 := h1 (some 1)
          have a2 := h1 none
          rcases o with _ | i
          · right; right
            simp only [allocationValue, allocationPrice, e0, e1] at h0 a0 a1 a2
            exact ⟨h0, a0, a1, h2⟩
          · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
            · left
              simp only [allocationValue, allocationPrice, e0, e1] at h0 a0 a1 a2
              exact ⟨h0, a1, a2, h2⟩
            · right; left
              simp only [allocationValue, allocationPrice, e0, e1] at h0 a0 a1 a2
              exact ⟨h0, a0, a2, h2⟩
      have hN : ∀ (β p r : ℝ) (v : Fin 2 → ℝ), 0 ≤ p → 0 ≤ r → 0 ≤ allocationRevenue β p r v := by
        intro β p r v hp hr
        rcases hU' β p r v (v 0) (v 1) rfl rfl with h | h | h | h
        · rw [h]
        · rw [h.2.2.2]; exact hp
        · rw [h.2.2.2]; exact hp
        · rw [h.2.2.2]; exact hr
      have hL0 : ∀ (β p r : ℝ) (v : Fin 2 → ℝ) (x0 x1 : ℝ), v 0 = x0 → v 1 = x1 →
          0 ≤ x0 - p → x1 - p ≤ x0 - p → β * x0 + (1 - β) * x1 - r ≤ x0 - p →
          p ≤ allocationRevenue β p r v := by
        intro β p r v x0 x1 e0 e1 h0 h1 h2
        refine hL (fun o => allocationValue β v o - allocationPrice p r o) (allocationPrice p r)
          (some 0) (by simp only [allocationValue, allocationPrice, e0]; exact h0) ?_
        intro o'
        rcases o' with _ | i
        · simp only [allocationValue, allocationPrice, e0, e1]; exact h2
        · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          · exact le_rfl
          · simp only [allocationValue, allocationPrice, e0, e1]; exact h1
      have hL1 : ∀ (β p r : ℝ) (v : Fin 2 → ℝ) (x0 x1 : ℝ), v 0 = x0 → v 1 = x1 →
          0 ≤ x1 - p → x0 - p ≤ x1 - p → β * x0 + (1 - β) * x1 - r ≤ x1 - p →
          p ≤ allocationRevenue β p r v := by
        intro β p r v x0 x1 e0 e1 h0 h1 h2
        refine hL (fun o => allocationValue β v o - allocationPrice p r o) (allocationPrice p r)
          (some 1) (by simp only [allocationValue, allocationPrice, e1]; exact h0) ?_
        intro o'
        rcases o' with _ | i
        · simp only [allocationValue, allocationPrice, e0, e1]; exact h2
        · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          · simp only [allocationValue, allocationPrice, e0, e1]; exact h1
          · exact le_rfl
      have hLn : ∀ (β p r : ℝ) (v : Fin 2 → ℝ) (x0 x1 : ℝ), v 0 = x0 → v 1 = x1 →
          0 ≤ β * x0 + (1 - β) * x1 - r → x0 - p ≤ β * x0 + (1 - β) * x1 - r →
          x1 - p ≤ β * x0 + (1 - β) * x1 - r →
          r ≤ allocationRevenue β p r v := by
        intro β p r v x0 x1 e0 e1 h0 h1 h2
        refine hL (fun o => allocationValue β v o - allocationPrice p r o) (allocationPrice p r)
          none (by simp only [allocationValue, allocationPrice, e0, e1]; exact h0) ?_
        intro o'
        rcases o' with _ | i
        · exact le_rfl
        · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          · simp only [allocationValue, allocationPrice, e0, e1]; exact h1
          · simp only [allocationValue, allocationPrice, e0, e1]; exact h2
      obtain ⟨e, he⟩ : ∃ e : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ), ∀ v, e v = v ∘ Equiv.swap (0 : Fin 2) 1 :=
        ⟨{ toFun := fun v => v ∘ Equiv.swap (0 : Fin 2) 1
           invFun := fun v => v ∘ Equiv.swap (0 : Fin 2) 1
           left_inv := fun v => by funext i; simp
           right_inv := fun v => by funext i; simp
           measurable_toFun := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
           measurable_invFun := measurable_pi_lambda _ (fun i => measurable_pi_apply _) },
         fun v => rfl⟩
      have hmap : μ.map e = μ := by
        have : (e : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = fun v => v ∘ Equiv.swap (0 : Fin 2) 1 := funext he
        rw [this]; exact hex _
      have key : ∀ p r p' r' : ℝ, 0 ≤ p → 0 ≤ r → 0 ≤ p' → 0 ≤ r' →
          (∀ᵐ v ∂μ, allocationRevenue β p r v + allocationRevenue β p r (v ∘ Equiv.swap (0 : Fin 2) 1)
            ≤ 2 * allocationRevenue (1 / 2) p' r' v) →
          expAllocation μ β p r ≤ optAllocation μ (1 / 2) := by
        intro p r p' r' hp hr hp' hr' hae
        have h1 : expAllocation μ β p r ≤ expAllocation μ (1 / 2) p' r' := by
          unfold expAllocation
          set g : (Fin 2 → ℝ) → ENNReal := fun v => ENNReal.ofReal (allocationRevenue β p r v) with hg
          set h : (Fin 2 → ℝ) → ENNReal :=
            fun v => ENNReal.ofReal (allocationRevenue (1 / 2) p' r' v) with hh
          have hsym : ∫⁻ v, g (e v) ∂μ = ∫⁻ v, g v ∂μ := by
            rw [← lintegral_map_equiv g e, hmap]
          have h2 : ∫⁻ v, g v ∂μ + ∫⁻ v, g (e v) ∂μ ≤ ∫⁻ v, 2 * h v ∂μ := by
            refine le_trans (le_lintegral_add _ _) (lintegral_mono_ae ?_)
            filter_upwards [hae] with v hv
            simp only [hg, hh, he]
            rw [← ENNReal.ofReal_add (hN _ _ _ _ hp hr) (hN _ _ _ _ hp hr)]
            rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            exact ENNReal.ofReal_le_ofReal hv
          rw [hsym, lintegral_const_mul' 2 h (by simp), ← two_mul] at h2
          exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 h2
        refine le_trans h1 ?_
        unfold optAllocation
        exact le_iSup_of_le p' (le_iSup_of_le r' (le_iSup_of_le ⟨hp', hr'⟩ le_rfl))
      have hUB : ∀ (β p r U : ℝ) (v : Fin 2 → ℝ) (x0 x1 : ℝ), v 0 = x0 → v 1 = x1 → 0 ≤ U →
          (0 ≤ x0 - p → x1 - p ≤ x0 - p → β * x0 + (1 - β) * x1 - r ≤ x0 - p → p ≤ U) →
          (0 ≤ x1 - p → x0 - p ≤ x1 - p → β * x0 + (1 - β) * x1 - r ≤ x1 - p → p ≤ U) →
          (0 ≤ β * x0 + (1 - β) * x1 - r → x0 - p ≤ β * x0 + (1 - β) * x1 - r →
            x1 - p ≤ β * x0 + (1 - β) * x1 - r → r ≤ U) →
          allocationRevenue β p r v ≤ U := by
        intro β p r U v x0 x1 e0 e1 hU0 c0 c1 c2
        rcases hU' β p r v x0 x1 e0 e1 with h | ⟨d1, d2, d3, h⟩ | ⟨d1, d2, d3, h⟩ | ⟨d1, d2, d3, h⟩
        · rw [h]; exact hU0
        · rw [h]; exact c0 d1 d2 d3
        · rw [h]; exact c1 d1 d2 d3
        · rw [h]; exact c2 d1 d2 d3
      clear hL hU
      obtain ⟨a, b, hab, hae⟩ := htwo
      obtain ⟨hβ1, hβ2⟩ := hβ
      have hw1 : a ≤ β * a + (1 - β) * b := by nlinarith
      have hw2 : β * a + (1 - β) * b ≤ (a + b) / 2 := by nlinarith
      have hw3 : (a + b) / 2 ≤ β * b + (1 - β) * a := by nlinarith
      have hw4 : β * b + (1 - β) * a ≤ b := by nlinarith
      refine iSup_le fun p => iSup_le fun r => iSup_le fun hpr => ?_
      obtain ⟨hp, hr⟩ := hpr
      by_cases hA : r ≤ a ∨ p ≤ a
      · have ha : 0 ≤ a := by rcases hA with hA | hA <;> linarith
        apply key p r ((a + b) / 2) a hp hr (by linarith) ha
        filter_upwards [hae] with v hv
        have s0 : (v ∘ Equiv.swap (0 : Fin 2) 1) 0 = v 1 := by simp
        have s1 : (v ∘ Equiv.swap (0 : Fin 2) 1) 1 = v 0 := by simp
        rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1

        · have B1 := hUB β p r (a) v a a h0 h1 (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have B2 := hUB β p r (a) (v ∘ Equiv.swap (0 : Fin 2) 1) a a (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have L := hLn (1 / 2) ((a + b) / 2) a v a a h0 h1 (by linarith) (by linarith) (by linarith)
          linarith
        · have B1 := hUB β p r (β * b + (1 - β) * a) v a b h0 h1 (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have B2 := hUB β p r (β * a + (1 - β) * b) (v ∘ Equiv.swap (0 : Fin 2) 1) b a (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have L := hL1 (1 / 2) ((a + b) / 2) a v a b h0 h1 (by linarith) (by linarith) (by linarith)
          linarith
        · have B1 := hUB β p r (β * a + (1 - β) * b) v b a h0 h1 (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have B2 := hUB β p r (β * b + (1 - β) * a) (v ∘ Equiv.swap (0 : Fin 2) 1) a b (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have L := hL0 (1 / 2) ((a + b) / 2) a v b a h0 h1 (by linarith) (by linarith) (by linarith)
          linarith
        · have B1 := hUB β p r (a) v b b h0 h1 (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have B2 := hUB β p r (a) (v ∘ Equiv.swap (0 : Fin 2) 1) b b (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith) (fun c1 c2 c3 => by rcases hA with hA | hA <;> linarith)
          have L := hLn (1 / 2) ((a + b) / 2) a v b b h0 h1 (by linarith) (by linarith) (by linarith)
          linarith
      · push Not at hA
        obtain ⟨hAr, hAp⟩ := hA
        by_cases hb : 0 ≤ b
        · apply key p r b b hp hr hb hb
          filter_upwards [hae] with v hv
          have s0 : (v ∘ Equiv.swap (0 : Fin 2) 1) 0 = v 1 := by simp
          have s1 : (v ∘ Equiv.swap (0 : Fin 2) 1) 1 = v 0 := by simp
          rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1

          · have B1 := hUB β p r (0) v a a h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (0) (v ∘ Equiv.swap (0 : Fin 2) 1) a a (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hN (1 / 2) b b v hb hb
            linarith
          · have B1 := hUB β p r (b) v a b h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (b) (v ∘ Equiv.swap (0 : Fin 2) 1) b a (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hL1 (1 / 2) b b v a b h0 h1 (by linarith) (by linarith) (by linarith)
            linarith
          · have B1 := hUB β p r (b) v b a h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (b) (v ∘ Equiv.swap (0 : Fin 2) 1) a b (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hL0 (1 / 2) b b v b a h0 h1 (by linarith) (by linarith) (by linarith)
            linarith
          · have B1 := hUB β p r (b) v b b h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (b) (v ∘ Equiv.swap (0 : Fin 2) 1) b b (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hLn (1 / 2) b b v b b h0 h1 (by linarith) (by linarith) (by linarith)
            linarith
        · push Not at hb
          apply key p r p r hp hr hp hr
          filter_upwards [hae] with v hv
          have s0 : (v ∘ Equiv.swap (0 : Fin 2) 1) 0 = v 1 := by simp
          have s1 : (v ∘ Equiv.swap (0 : Fin 2) 1) 1 = v 0 := by simp
          rcases hv 0 with h0 | h0 <;> rcases hv 1 with h1 | h1

          · have B1 := hUB β p r (0) v a a h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (0) (v ∘ Equiv.swap (0 : Fin 2) 1) a a (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hN (1 / 2) p r v hp hr
            linarith
          · have B1 := hUB β p r (0) v a b h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (0) (v ∘ Equiv.swap (0 : Fin 2) 1) b a (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hN (1 / 2) p r v hp hr
            linarith
          · have B1 := hUB β p r (0) v b a h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (0) (v ∘ Equiv.swap (0 : Fin 2) 1) a b (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hN (1 / 2) p r v hp hr
            linarith
          · have B1 := hUB β p r (0) v b b h0 h1 (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have B2 := hUB β p r (0) (v ∘ Equiv.swap (0 : Fin 2) 1) b b (s0.trans h1) (s1.trans h0) (by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith) (fun c1 c2 c3 => by linarith)
            have L := hN (1 / 2) p r v hp hr
            linarith
