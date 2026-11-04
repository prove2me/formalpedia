-- Prove2me | solution 1 for SCInfoDesign.Nested.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:09:08.337614+00:00
-- url     : https://prove2.me/submissions/4ad3f6b7-d58e-43f9-b749-d7f44726b96f

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Nested_Setting
import Theorems.Thm_SCInfoDesign_Nested_proposition_1
import Theorems.Thm_SCInfoDesign_Nested_value_eq_convexEnvelope
import Theorems.Thm_SCInfoDesign_Nested_lemma_1
import Theorems.Thm_SCInfoDesign_Nested_gammaStar_posteriors

open SCInfoDesign.Nested BiconvexProg.BranchBound

theorem solution (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    (P.ξh ≤ P.ξ → P.IsOptimalPolicy p₀ fullDisclosure) ∧
    (P.τlow p₀ ≤ P.ξ → P.ξ ≤ P.ξh → P.IsOptimalPolicy p₀ noDisclosure) ∧
    (P.ξ ≤ P.τlow p₀ → P.IsOptimalPolicy p₀ (P.gammaStar p₀)) := by
  obtain ⟨hp0, hp1⟩ := hp₀
  have hL : 0 < P.b₀ - P.a₀ := by linarith
  -- the retailer-preferred quantity is a best-response profile (Proposition 1)
  have hBR : P.IsBestResponseProfile P.prefQ := by
    intro p hp
    obtain ⟨h1, h2', h3⟩ :=
      proposition_1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p hp
    have key : ∃ q, ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q := by
      by_cases c1 : P.τup p ≤ P.ξ
      · exact ⟨_, h1 ⟨c1, hξ1.le⟩⟩
      by_cases c2 : P.τlow p ≤ P.ξ
      · exact ⟨_, h2' ⟨c2, le_of_lt (not_le.mp c1)⟩⟩
      exact ⟨_, h3 ⟨hξ0.le, le_of_lt (not_le.mp c2)⟩⟩
    obtain ⟨q, hq⟩ := key
    have hset : {Q | P.IsOptimalQuantity p Q} = {q} := Set.ext fun Q => hq Q
    show P.IsOptimalQuantity p (sSup {Q | P.IsOptimalQuantity p Q})
    rw [hset, csSup_singleton]
    exact (hq q).2 rfl
  -- the value of (3) is a lower bound on every policy's cost (Kamenica–Gentzkow)
  have hLB : ∀ (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (Qs' : ℝ → ℝ),
      IsPolicy π' → P.IsBestResponseProfile Qs' →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ ≤ P.expectedCost p₀ π' Qs' := by
    intro M' _ π' Qs' hπ' hQs'
    have hglb := value_eq_convexEnvelope P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p₀ ⟨hp0, hp1⟩
    let e := Fintype.equivFin M'
    let π'' : Fin 2 → Fin (Fintype.card M') → ℝ := fun ω i => π' ω (e.symm i)
    have hpol : IsPolicy π'' := by
      refine ⟨fun ω i => hπ'.1 ω (e.symm i), fun ω => ?_⟩
      rw [← hπ'.2 ω]
      exact Equiv.sum_comp e.symm (fun m => π' ω m)
    have hcost : P.expectedCost p₀ π'' Qs' = P.expectedCost p₀ π' Qs' := by
      unfold Params.expectedCost
      exact Equiv.sum_comp e.symm (fun m => msgProb p₀ π' m *
        P.retailerCost (posterior p₀ π' m) (Qs' (posterior p₀ π' m)))
    rw [← hcost]
    exact hglb.1 ⟨Fintype.card M', π'', Qs', hpol, hQs', rfl⟩
  have hopt : ∀ {M : Type} [Fintype M] (π : Fin 2 → M → ℝ),
      IsPolicy π →
      P.expectedCost p₀ π P.prefQ = convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ →
      P.IsOptimalPolicy p₀ π := by
    intro M _ π hπ hc
    refine ⟨hπ, P.prefQ, hBR, ?_⟩
    intro M' _ π' Qs' hπ' hQs'
    rw [hc]
    exact hLB M' π' Qs' hπ' hQs'
  have L1 := lemma_1 P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b
  -- K evaluated through prefQ
  have hKdef : ∀ p, P.retailerCost p (P.prefQ p) = P.K p := fun p => rfl
  refine ⟨fun hξ => ?_, fun hξl hξu => ?_, fun hξ => ?_⟩
  · -- full disclosure
    have hpol : IsPolicy fullDisclosure := by
      refine ⟨fun ω m => ?_, fun ω => ?_⟩
      · unfold fullDisclosure; split_ifs <;> norm_num
      · fin_cases ω <;> simp [fullDisclosure, Fin.sum_univ_two]
    apply hopt _ hpol
    rw [L1.1 hξ p₀ ⟨hp0, hp1⟩]
    unfold Params.expectedCost
    simp only [Fin.sum_univ_two, msgProb, posterior, fullDisclosure]
    simp only [Fin.isValue, if_true, Fin.reduceEq, if_false, mul_one, mul_zero, add_zero,
      zero_add, zero_div]
    change p₀ * P.K (p₀ / p₀) + (1 - p₀) * P.K 0 = p₀ * P.K 1 + (1 - p₀) * P.K 0
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; simp
    · rw [div_self h.ne']
  · -- no disclosure
    have hpol : IsPolicy noDisclosure := by
      refine ⟨fun ω m => ?_, fun ω => ?_⟩
      · unfold noDisclosure; norm_num
      · simp [noDisclosure]
    apply hopt _ hpol
    have henv : convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ = P.K p₀ := by
      by_cases c : (P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ P.ξ
      · exact L1.2.1 c hξu p₀ ⟨hp0, hp1⟩
      · have c' := le_of_lt (not_le.mp c)
        rw [L1.2.2 c' p₀ ⟨hp0, hp1⟩]
        have hα : 0 < P.a₁ - P.a₀ := by
          by_contra h; push_neg at h
          have : (P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hL.le
          linarith
        have : p₀ ≤ P.pHat := by
          unfold Params.τlow at hξl
          unfold Params.pHat
          rw [div_le_iff₀ hL] at hξl
          rw [le_div_iff₀ hα]; linarith
        rw [if_pos this]
    rw [henv]
    unfold Params.expectedCost
    simp only [Fintype.univ_unit, Finset.sum_singleton, msgProb, posterior, noDisclosure]
    have : p₀ * 1 + (1 - p₀) * 1 = 1 := by ring
    rw [this, mul_one, div_one, one_mul]
    rfl
  · -- partial disclosure Γ*
    have hα : 0 < P.a₁ - P.a₀ := by
      by_contra h; push_neg at h
      have : P.τlow p₀ ≤ 0 := by
        unfold Params.τlow
        exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hp0 h) hL.le
      linarith
    have hξα : P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) := by
      refine le_trans hξ ?_
      unfold Params.τlow
      apply div_le_div_of_nonneg_right _ hL.le
      nlinarith
    have hpp : 0 < p₀ := by
      by_contra h; push_neg at h
      have : p₀ = 0 := le_antisymm h hp0
      unfold Params.τlow at hξ; rw [this] at hξ; simp at hξ; linarith
    have hpH : P.pHat ≤ p₀ := by
      unfold Params.τlow at hξ
      unfold Params.pHat
      rw [le_div_iff₀ hL] at hξ
      rw [div_le_iff₀ hα]; linarith
    have L3 := L1.2.2 hξα p₀ ⟨hp0, hp1⟩
    rcases eq_or_lt_of_le hξ with heq | hlt
    · -- boundary case ξ = τ̲(p₀): then p₀ = p̂ and Γ* is no disclosure in effect
      have hpe : P.pHat = p₀ := by
        unfold Params.τlow at heq
        unfold Params.pHat
        rw [heq]; field_simp
      have henv : convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ = P.K p₀ := by
        rw [L3, if_pos (le_of_eq hpe.symm)]
      have hx : P.ξ * (P.b₀ - P.a₀) = p₀ * (P.a₁ - P.a₀) := by
        unfold Params.τlow at heq; rw [heq]; field_simp
      rcases eq_or_lt_of_le hp1 with h1 | h1
      · -- p₀ = 1
        have hgs : P.gammaStar p₀ = ![![1, 0], ![0, 1]] := by
          unfold Params.gammaStar
          rw [h1]; simp
        have hpol : IsPolicy (P.gammaStar p₀) := by
          rw [hgs]
          refine ⟨fun ω m => ?_, fun ω => ?_⟩
          · fin_cases ω <;> fin_cases m <;> simp
          · fin_cases ω <;> simp [Fin.sum_univ_two]
        apply hopt _ hpol
        rw [henv]
        unfold Params.expectedCost
        rw [hgs, Fin.sum_univ_two]
        simp only [msgProb, posterior, Matrix.cons_val_zero, Matrix.cons_val_one, h1]
        simp
        rfl
      · -- p₀ < 1
        have hq : (1 - p₀) / p₀ * (P.ξ * (P.b₀ - P.a₀) /
            ((P.a₁ - P.a₀) - P.ξ * (P.b₀ - P.a₀))) = 1 := by
          rw [hx]
          have : 0 < 1 - p₀ := by linarith
          have e : (P.a₁ - P.a₀) - p₀ * (P.a₁ - P.a₀) = (1 - p₀) * (P.a₁ - P.a₀) := by ring
          rw [e]; field_simp
        have hgs : P.gammaStar p₀ = ![![0, 1], ![0, 1]] := by
          unfold Params.gammaStar
          simp only [hq]; norm_num
        have hpol : IsPolicy (P.gammaStar p₀) := by
          rw [hgs]
          refine ⟨fun ω m => ?_, fun ω => ?_⟩
          · fin_cases ω <;> fin_cases m <;> simp
          · fin_cases ω <;> simp [Fin.sum_univ_two]
        apply hopt _ hpol
        rw [henv]
        unfold Params.expectedCost
        rw [hgs, Fin.sum_univ_two]
        simp only [msgProb, posterior, Matrix.cons_val_zero, Matrix.cons_val_one]
        simp
        rfl
    · obtain ⟨hpol, hm0, hpost0, hpost1⟩ :=
        gammaStar_posteriors P ha ha₁ ha₀0 ha₁0 hξ0 hξ1 hnest_a hnest_b p₀ ⟨hp0, hp1⟩ hlt
      apply hopt _ hpol
      have hpHlt : P.pHat < p₀ := by
        unfold Params.τlow at hlt
        unfold Params.pHat
        rw [lt_div_iff₀ hL] at hlt
        rw [div_lt_iff₀ hα]; linarith
      have hpH1 : P.pHat < 1 := lt_of_lt_of_le hpHlt hp1
      rw [L3, if_neg (not_le.mpr hpHlt)]
      have hsum : msgProb p₀ (P.gammaStar p₀) 0 + msgProb p₀ (P.gammaStar p₀) 1 = 1 := by
        have h0 := hpol.2 0
        have h1 := hpol.2 1
        rw [Fin.sum_univ_two] at h0 h1
        unfold msgProb
        linear_combination p₀ * h0 + (1 - p₀) * h1
      have hm1 : msgProb p₀ (P.gammaStar p₀) 1 = 1 - (p₀ - P.pHat) / (1 - P.pHat) := by
        linarith
      unfold Params.expectedCost
      rw [Fin.sum_univ_two, hKdef, hKdef, hm0, hm1, hpost0]
      have hne : 1 - P.pHat ≠ 0 := by linarith
      rcases eq_or_lt_of_le hp1 with h1 | h1
      · subst h1
        rw [div_self hne]
        field_simp
        ring
      · rw [hpost1 h1]
        field_simp
        ring
