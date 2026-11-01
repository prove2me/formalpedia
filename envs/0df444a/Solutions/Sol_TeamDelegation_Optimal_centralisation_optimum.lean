-- Prove2me | solution 1 for TeamDelegation.Optimal.centralisation_optimum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:46:20.048306+00:00
-- url     : https://prove2.me/submissions/16135010-20fb-44d3-a739-74902a7283f9

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

open TeamDelegation.Optimal

private lemma sum_lower {ι : Type} [Fintype ι] (σ f : ι → ℝ) (c : ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (h1 : ∑ i, σ i = 1) (hf : ∀ i, σ i ≠ 0 → c ≤ f i) :
    c ≤ ∑ i, σ i * f i := by
  have : c = ∑ i, σ i * c := by rw [← Finset.sum_mul, h1, one_mul]
  rw [this]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : σ i = 0
  · simp [h]
  · exact mul_le_mul_of_nonneg_left (hf i h) (hσ i)

/-- Dirac punishment at (correct method, shirk, shirk). -/
private noncomputable def diracσ (k : State) : Mixed ActA ActB :=
  ⟨fun a => if a = (k, false) then 1 else 0, fun b => if b = false then 1 else 0⟩

theorem solution (P : Params) (C : Costs)
    (hS : P.Standing) (hA1 : P.Assumption1) (hC : C.Standing) :
    Implements P C .cent (wcent P) (wcent P) ∧
      ∀ wA wB : ℝ, Implements P C .cent wA wB →
        wcent P ≤ wA ∧ wcent P ≤ wB := by
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨h01, h12, hq01, hq12, hqp0, hqp1, hqp2, hc1, hc2, hc3, hc4⟩ := hA1
  have hDc : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 := by
    have : P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 =
        (P.p2 - P.p1) + P.δ * (P.p1 - P.p0) := by ring
    rw [this]; have := mul_pos hδ0 (sub_pos.2 h01); linarith
  constructor
  · -- the equal centralised bonus implements the desired path
    obtain ⟨w, hw⟩ : ∃ w, w = wcent P := ⟨_, rfl⟩
    rw [← hw]
    have hw0 : 0 < w := by rw [hw]; exact div_pos he hDc
    have hwD : w * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) = P.e := by
      rw [hw, wcent, div_mul_cancel₀ _ hDc.ne']
    have hNE : (P.p1 - P.p0) * w ≤ P.e := by
      have : (P.p1 - P.p0) * w ≤ (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) * w := by
        apply mul_le_mul_of_nonneg_right _ hw0.le
        nlinarith
      linarith
    have hPC : P.e ≤ (P.p2 - P.p0) * w := by
      have : (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) * w ≤ (P.p2 - P.p0) * w := by
        apply mul_le_mul_of_nonneg_right _ hw0.le
        nlinarith
      linarith
    refine ⟨hw0.le, hw0.le, diracσ, ?_, ?_⟩
    · intro k
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · intro a; simp only [diracσ]; split_ifs <;> norm_num
      · intro b; simp only [diracσ]; split_ifs <;> norm_num
      · simp [diracσ]
      · simp [diracσ]
      · intro a ha
        simp only [diracσ]
        rw [if_neg]
        rintro rfl
        exact ha rfl
      · intro b hb; exact absurd trivial hb
      · rintro ⟨m, x⟩ hm
        simp only [stageGame, FeasibleA] at hm
        subst hm
        fin_cases m <;> cases x <;>
          simp [diracσ, FiniteGame.expPayA, stageGame, payA, succProb, workers,
            Fintype.sum_prod_type] <;> linarith
      · intro b _
        fin_cases k <;> cases b <;>
          simp [diracσ, FiniteGame.expPayB, stageGame, payB, succProb, workers,
            Fintype.sum_prod_type] <;> linarith
    · intro k
      have hδ' : 0 ≤ 1 - P.δ := by linarith
      constructor
      · rintro ⟨m, x⟩ hm
        simp only [FeasibleA] at hm
        subst hm
        fin_cases m <;> cases x <;>
          simp [diracσ, punValueA, contValueA, FiniteGame.expPayA, stageGame, payA,
            succProb, workers, desiredA] <;>
          nlinarith [mul_le_mul_of_nonneg_left hPC hδ0.le]
      · fin_cases k <;>
          simp [diracσ, punValueB, contValueB, FiniteGame.expPayB, stageGame, payB,
            succProb, workers, desiredA] <;>
          nlinarith [mul_le_mul_of_nonneg_left hPC hδ0.le]
  · -- no cheaper success bonus implements the desired path
    rintro wA wB ⟨hwA, hwB, σ, hNE, hdev⟩
    -- A's punishment payoff is at least p0 wA minus the method cost
    have hpunA : ∀ k : State,
        P.p0 * wA - (if k = (0 : Method) then C.c1A else C.c2A) ≤
          (stageGame P C .cent k wA wB).expPayA (σ k) := by
      intro k
      obtain ⟨⟨hσA, hσB, hsA, hsB, _, _⟩, hA, _⟩ := hNE k
      refine le_trans ?_ (hA (k, false) rfl)
      apply sum_lower _ _ _ hσB hsB
      intro b _
      cases b <;> simp [stageGame, payA, succProb, workers] <;> nlinarith
    have hpunB : ∀ k : State,
        P.p0 * wB - (if k = (0 : Method) then C.c1B else C.c2B) ≤
          (stageGame P C .cent k wA wB).expPayB (σ k) := by
      intro k
      obtain ⟨⟨hσA, hσB, hsA, hsB, hinf, _⟩, _, hB⟩ := hNE k
      refine le_trans ?_ (hB false trivial)
      apply sum_lower _ _ _ hσA hsA
      rintro ⟨m, x⟩ hne
      have hm : m = k := by
        by_contra hmk
        exact hne (hinf (m, x) (by simp [stageGame, FeasibleA, hmk]))
      subst hm
      cases x <;> simp [stageGame, payB, succProb, workers] <;> nlinarith
    have h0 := hpunA 0
    have h1 := hpunA 1
    have g0 := hpunB 0
    have g1 := hpunB 1
    simp at h0 h1 g0 g1
    obtain ⟨hdA, hdB⟩ := hdev 0
    have dA := hdA (0, false) rfl
    simp [punValueA, contValueA, payA, succProb, workers, desiredA] at dA hdB
    simp [punValueB, contValueB, payB, succProb, workers, desiredA] at hdB
    have hr' : 0 ≤ 1 - P.r := by linarith
    have k1 := mul_le_mul_of_nonneg_left h0 hr0
    have k2 := mul_le_mul_of_nonneg_left h1 hr'
    have k3 := mul_le_mul_of_nonneg_left g0 hr0
    have k4 := mul_le_mul_of_nonneg_left g1 hr'
    constructor
    · rw [wcent, div_le_iff₀ hDc]
      linarith [mul_le_mul_of_nonneg_left (add_le_add k1 k2) hδ0.le]
    · rw [wcent, div_le_iff₀ hDc]
      linarith [mul_le_mul_of_nonneg_left (add_le_add k3 k4) hδ0.le]
