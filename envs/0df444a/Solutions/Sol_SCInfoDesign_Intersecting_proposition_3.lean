-- Prove2me | solution 1 for SCInfoDesign.Intersecting.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:36:08.055436+00:00
-- url     : https://prove2.me/submissions/ef59684f-efeb-48c5-9a45-5ae0c525df6f

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting
import Theorems.Thm_SCInfoDesign_Intersecting_proposition_2
import Theorems.Thm_SCInfoDesign_Intersecting_value_eq_convexEnvelope
import Theorems.Thm_SCInfoDesign_Intersecting_lemma_2
import Theorems.Thm_SCInfoDesign_Intersecting_gammaStarIS_posteriors

open SCInfoDesign.Intersecting BiconvexProg.BranchBound

theorem solution (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (h2 : 2 * P.δu < P.δd) (hmax : max (P.δd - 2 * P.δu) (P.δd * P.δu / (P.δd - 2 * P.δu)) < P.δIS)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    (P.ξbreve ≤ P.ξ → P.IsOptimalPolicy p₀ SCInfoDesign.Nested.fullDisclosure) ∧
    (P.τlowIS p₀ ≤ P.ξ → P.ξ < P.ξbreve → P.IsOptimalPolicy p₀ SCInfoDesign.Nested.noDisclosure) ∧
    (P.ξ < P.τlowIS p₀ → P.IsOptimalPolicy p₀ (P.gammaStarIS p₀)) := by
  obtain ⟨hp0, hp1⟩ := hp₀
  -- the retailer-preferred quantity is a best-response profile (Proposition 2)
  have hBR : P.IsBestResponseProfile P.prefQ := by
    intro p hp
    obtain ⟨h1, h2', h3⟩ := proposition_2 P ha₁0 hξ0 hξ1 hb hm ha p hp
    have key : ∃ q, ∀ Q, P.IsOptimalQuantity p Q ↔ Q = q := by
      by_cases c1 : P.τbarIS p ≤ P.ξ
      · exact ⟨_, h1 c1⟩
      by_cases c2 : P.τlowIS p ≤ P.ξ
      · exact ⟨_, h2' c2 (le_of_lt (not_le.mp c1))⟩
      exact ⟨_, h3 (le_of_lt (not_le.mp c2))⟩
    obtain ⟨q, hq⟩ := key
    have hset : {Q | P.IsOptimalQuantity p Q} = {q} := Set.ext fun Q => hq Q
    show P.IsOptimalQuantity p (sSup {Q | P.IsOptimalQuantity p Q})
    rw [hset, csSup_singleton]
    exact (hq q).2 rfl
  -- the value of (3) is a lower bound on every policy's cost (Kamenica–Gentzkow)
  have hLB : ∀ (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (Qs' : ℝ → ℝ),
      SCInfoDesign.Nested.IsPolicy π' → P.IsBestResponseProfile Qs' →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ ≤ P.expectedCost p₀ π' Qs' := by
    intro M' _ π' Qs' hπ' hQs'
    have hglb := value_eq_convexEnvelope P ha₁0 hξ0 hξ1 hb hm ha p₀ ⟨hp0, hp1⟩
    let e := Fintype.equivFin M'
    let π'' : Fin 2 → Fin (Fintype.card M') → ℝ := fun ω i => π' ω (e.symm i)
    have hpol : SCInfoDesign.Nested.IsPolicy π'' := by
      refine ⟨fun ω i => hπ'.1 ω (e.symm i), fun ω => ?_⟩
      rw [← hπ'.2 ω]
      exact Equiv.sum_comp e.symm (fun m => π' ω m)
    have hcost : P.expectedCost p₀ π'' Qs' = P.expectedCost p₀ π' Qs' := by
      unfold Params.expectedCost
      exact Equiv.sum_comp e.symm (fun m => SCInfoDesign.Nested.msgProb p₀ π' m *
        P.retailerCost (SCInfoDesign.Nested.posterior p₀ π' m)
          (Qs' (SCInfoDesign.Nested.posterior p₀ π' m)))
    rw [← hcost]
    exact hglb.1 ⟨Fintype.card M', π'', Qs', hpol, hQs', rfl⟩
  have hopt : ∀ {M : Type} [Fintype M] (π : Fin 2 → M → ℝ),
      SCInfoDesign.Nested.IsPolicy π →
      P.expectedCost p₀ π P.prefQ = convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ →
      P.IsOptimalPolicy p₀ π := by
    intro M _ π hπ hc
    refine ⟨hπ, P.prefQ, hBR, ?_⟩
    intro M' _ π' Qs' hπ' hQs'
    rw [hc]
    exact hLB M' π' Qs' hπ' hQs'
  have hd : 0 < P.a₀ - P.a₁ := by linarith
  have hL : 0 < P.b₁ - P.a₁ := by linarith
  have hiff : ∀ p : ℝ, P.pbreve ≤ p ↔ P.τlowIS p ≤ P.ξ := by
    intro p
    unfold Params.pbreve Params.τlowIS
    rw [div_le_iff₀ hL]
    constructor
    · intro h
      have : 1 - p ≤ P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) := by linarith
      rw [le_div_iff₀ hd] at this
      linarith
    · intro h
      have : 1 - p ≤ P.ξ * (P.b₁ - P.a₁) / (P.a₀ - P.a₁) := by
        rw [le_div_iff₀ hd]; linarith
      linarith
  have hτmono : P.τlowIS p₀ ≤ P.τlowIS 0 := by
    unfold Params.τlowIS
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith
  refine ⟨fun hξ => ?_, fun hξl hξu => ?_, fun hξ => ?_⟩
  · -- full disclosure
    have hpol : SCInfoDesign.Nested.IsPolicy SCInfoDesign.Nested.fullDisclosure := by
      refine ⟨fun ω m => ?_, fun ω => ?_⟩
      · unfold SCInfoDesign.Nested.fullDisclosure; split_ifs <;> norm_num
      · fin_cases ω <;> simp [SCInfoDesign.Nested.fullDisclosure, Fin.sum_univ_two]
    apply hopt _ hpol
    rw [(lemma_2 P ha₁0 hξ0 hξ1 hb hm ha h2 hmax p₀ ⟨hp0, hp1⟩).1 hξ]
    unfold Params.expectedCost
    simp only [Fin.sum_univ_two, SCInfoDesign.Nested.msgProb, SCInfoDesign.Nested.posterior,
      SCInfoDesign.Nested.fullDisclosure]
    simp only [Fin.isValue, if_true, Fin.reduceEq, if_false, mul_one, mul_zero, add_zero,
      zero_add, zero_div]
    change p₀ * P.K (p₀ / p₀) + (1 - p₀) * P.K 0 = (1 - p₀) * P.K 0 + p₀ * P.K 1
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; simp
    · rw [div_self h.ne']; ring
  · -- no disclosure
    have hpol : SCInfoDesign.Nested.IsPolicy SCInfoDesign.Nested.noDisclosure := by
      refine ⟨fun ω m => ?_, fun ω => ?_⟩
      · unfold SCInfoDesign.Nested.noDisclosure; norm_num
      · simp [SCInfoDesign.Nested.noDisclosure]
    apply hopt _ hpol
    have henv : convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀ = P.K p₀ := by
      have L2 := lemma_2 P ha₁0 hξ0 hξ1 hb hm ha h2 hmax p₀ ⟨hp0, hp1⟩
      by_cases c : P.τlowIS 0 ≤ P.ξ
      · exact L2.2.1 c hξu
      · rw [L2.2.2 (not_le.mp c), if_pos ((hiff p₀).2 hξl)]
    rw [henv]
    unfold Params.expectedCost
    simp only [Fintype.univ_unit, Finset.sum_singleton, SCInfoDesign.Nested.msgProb,
      SCInfoDesign.Nested.posterior, SCInfoDesign.Nested.noDisclosure]
    have : p₀ * 1 + (1 - p₀) * 1 = 1 := by ring
    rw [this, mul_one, div_one, one_mul]
    rfl
  · -- partial disclosure Γ*_IS
    obtain ⟨hpol, hm0, hm1, hpost0, hpost1⟩ :=
      gammaStarIS_posteriors P ha₁0 hξ0 hξ1 hb hm ha p₀ hp0 hξ
    apply hopt _ hpol
    have hlt : P.ξ < P.τlowIS 0 := lt_of_lt_of_le hξ hτmono
    have hnot : ¬ P.pbreve ≤ p₀ := fun h => absurd ((hiff p₀).1 h) (not_le.mpr hξ)
    have hpb : 0 < P.pbreve := lt_of_le_of_lt hp0 (not_le.mp hnot)
    rw [(lemma_2 P ha₁0 hξ0 hξ1 hb hm ha h2 hmax p₀ ⟨hp0, hp1⟩).2.2 hlt, if_neg hnot]
    unfold Params.expectedCost
    rw [Fin.sum_univ_two, hm0, hm1, hpost1]
    change p₀ / P.pbreve * P.K (SCInfoDesign.Nested.posterior p₀ (P.gammaStarIS p₀) 0) +
      (1 - p₀ / P.pbreve) * P.K 0 = _
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h; simp
    · rw [hpost0 h]
      field_simp
      ring
