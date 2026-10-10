-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_partition_count_transport_forward
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T14:19:50.473989+00:00
-- url     : https://prove2.me/submissions/a569959c-b499-4c6d-9e93-c7953dbc7dbb

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count
open scoped ENNReal

/-- `y + ↑r = ⊤` (for real `r`) forces `y = ⊤`. -/
private lemma pc_add_coe_top {y : EReal} {r : ℝ} (h : y + (r : EReal) = ⊤) : y = ⊤ := by
  induction y with
  | bot => rw [EReal.bot_add] at h; exact absurd h (by simp)
  | coe s => rw [← EReal.coe_add] at h; exact absurd h (EReal.coe_ne_top (s + r))
  | top => rfl

/-- Forward: `γ(Sum.inl ⟨q,hq⟩)` is an off-diagonal copy whose point lies in `Δ^S_τ ∩ Λ^E_τ`. -/
private lemma pc_forward_inl
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ)
    (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D q.1)
    (hqin : q.1 ∈ DeltaS d₂ ∩ LamE d₂) :
    ∃ (w : (EReal × EReal) × ℕ) (hw : (w.2 : ℕ∞) < D' w.1),
      γ (Sum.inl ⟨q, hq⟩) = Sum.inl ⟨w, hw⟩ ∧ w.1 ∈ DeltaS τ ∩ LamE τ := by
  obtain ⟨hi, hii, hiii, hiv⟩ := hγ
  have hr : 0 < c * δ := mul_pos hc hδ
  have h5 : (0 : ℝ) < 5 * c := by positivity
  have h6 : 5 * c * δ < d₂ - d₁ := by
    have h6' := (lt_div_iff₀ h5).mp hδc
    rwa [mul_comm δ (5 * c)] at h6'
  have h52 : d₁ + 5 * c * δ < d₂ := by linarith
  have hd2_gt_r : c * δ < d₂ := by linarith
  have h2r_lt_tau : 2 * c * δ < τ := by linarith
  have htau_pos : 0 < τ := lt_trans (by linarith : (0 : ℝ) < 2 * c * δ) h2r_lt_tau
  have hd2mr : τ < d₂ - c * δ := by linarith
  have hd2m2r : τ < d₂ - 2 * c * δ := by linarith
  have hDS : q.1.2 ≤ q.1.1 - (d₂ : EReal) := hqin.1
  have hLE : (d₂ : EReal) < q.1.1 := hqin.2
  have hDq : D q.1 ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le : (0 : ℕ∞) ≤ (q.2 : ℕ∞)) hq)
  have hxy : q.1.2 < q.1.1 := hD q.1 hDq
  have hy_ne_top : q.1.2 ≠ ⊤ := by
    intro h; rw [h] at hxy; exact not_lt_of_ge le_top hxy
  have hx_ne_bot : q.1.1 ≠ ⊥ := by
    intro h; rw [h] at hxy; exact not_lt_of_ge bot_le hxy
  set a : Copies D := Sum.inl ⟨q, hq⟩ with haeq
  have hpt_a : pt a = q.1 := rfl
  -- hreg : pt (γ a) ∈ DeltaS τ ∩ LamE τ
  have hreg : pt (γ a) ∈ DeltaS τ ∩ LamE τ := by
    by_cases hy : ((c * δ : ℝ) : EReal) < q.1.2
    case pos =>
      have hQNEa : pt a ∈ QNE (c * δ) := by
        rw [hpt_a]
        refine ⟨lt_trans (EReal.coe_lt_coe_iff.mpr hd2_gt_r) hLE, hy⟩
      have hc1 := hi a hQNEa
      have hx_le : q.1.1 ≤ (pt (γ a)).1 + ((c * δ : ℝ) : EReal) := hc1.1.1
      have hy'_le : (pt (γ a)).2 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hc1.2.2
      have hxr_le : q.1.1 - ((c * δ : ℝ) : EReal) ≤ (pt (γ a)).1 :=
        EReal.sub_le_of_le_add hx_le
      have hd2r : (d₂ : EReal) - ((c * δ : ℝ) : EReal) < q.1.1 - ((c * δ : ℝ) : EReal) :=
        EReal.sub_lt_sub_of_lt_of_le hLE (le_refl ((c * δ : ℝ) : EReal))
          (EReal.coe_ne_bot (c * δ)) (EReal.coe_ne_top (c * δ))
      have hd2r_tau : (τ : EReal) < ((d₂ - c * δ : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr hd2mr
      have h1 : (τ : EReal) < q.1.1 - ((c * δ : ℝ) : EReal) := lt_trans hd2r_tau hd2r
      have hx'_gt_tau : (τ : EReal) < (pt (γ a)).1 := lt_of_lt_of_le h1 hxr_le
      have hy'_le_x'tau : (pt (γ a)).2 ≤ (pt (γ a)).1 - (τ : EReal) := by
        by_cases hxt : (pt (γ a)).1 = ⊤
        · rw [hxt]; rw [EReal.top_sub_coe]; exact le_top
        · have hx'nb : (pt (γ a)).1 ≠ ⊥ := by
            intro h
            have h0 : (0 : EReal) < (pt (γ a)).1 :=
              lt_trans (EReal.coe_lt_coe_iff.mpr htau_pos) hx'_gt_tau
            rw [h] at h0
            exact not_lt_of_ge bot_le h0
          have hx'real : ((pt (γ a)).1.toReal : EReal) = (pt (γ a)).1 :=
            EReal.coe_toReal hxt hx'nb
          have hxne_top : q.1.1 ≠ ⊤ := by
            intro h
            rw [h] at hx_le
            exact hxt (pc_add_coe_top (le_antisymm hx_le le_top).symm)
          have hxreal : ((q.1.1).toReal : EReal) = q.1.1 := EReal.coe_toReal hxne_top hx_ne_bot
          have hxreal_le : q.1.1.toReal ≤ (pt (γ a)).1.toReal + c * δ := by
            have := hx_le
            rw [← hxreal, ← hx'real, ← EReal.coe_add] at this
            exact EReal.coe_le_coe_iff.mp this
          by_cases hyb : q.1.2 = ⊥
          · have hy'bot : (pt (γ a)).2 = ⊥ := by
              have := hy'_le
              rw [hyb, EReal.bot_add] at this
              exact le_antisymm this bot_le
            rw [hy'bot]; exact bot_le
          · have hyreal : ((q.1.2).toReal : EReal) = q.1.2 := EReal.coe_toReal hy_ne_top hyb
            have hDSreal : q.1.2.toReal ≤ q.1.1.toReal - d₂ := by
              have := hDS
              rw [← hyreal, ← hxreal, ← EReal.coe_sub] at this
              exact EReal.coe_le_coe_iff.mp this
            by_cases hy'b : (pt (γ a)).2 = ⊥
            · rw [hy'b]; exact bot_le
            · have hy'ne_top : (pt (γ a)).2 ≠ ⊤ := by
                intro h
                have := hy'_le
                rw [h] at this
                rw [← hyreal, ← EReal.coe_add] at this
                exact absurd this (not_le_of_gt (EReal.coe_lt_top (q.1.2.toReal + c * δ)))
              have hy'real : ((pt (γ a)).2.toReal : EReal) = (pt (γ a)).2 :=
                EReal.coe_toReal hy'ne_top hy'b
              have hy'real_le : (pt (γ a)).2.toReal ≤ q.1.2.toReal + c * δ := by
                have := hy'_le
                rw [← hyreal, ← hy'real, ← EReal.coe_add] at this
                exact EReal.coe_le_coe_iff.mp this
              rw [← hy'real, ← hx'real, ← EReal.coe_sub, EReal.coe_le_coe_iff]
              linarith
      exact ⟨hy'_le_x'tau, hx'_gt_tau⟩
    case neg =>
      have hLE_r : q.1.2 ≤ ((c * δ : ℝ) : EReal) := not_lt.mp hy
      have hQSEa : pt a ∈ QSE (c * δ) := by
        rw [hpt_a]
        refine ⟨lt_trans (EReal.coe_lt_coe_iff.mpr hd2_gt_r) hLE, hLE_r⟩
      have hc3 : closeE q.1.1 (pt (γ a)).1 (c * δ) := hiii a hQSEa
      have hx_le : q.1.1 ≤ (pt (γ a)).1 + ((c * δ : ℝ) : EReal) := hc3.1
      have hx'_le : (pt (γ a)).1 ≤ q.1.1 + ((c * δ : ℝ) : EReal) := hc3.2
      have hxr_le : q.1.1 - ((c * δ : ℝ) : EReal) ≤ (pt (γ a)).1 :=
        EReal.sub_le_of_le_add hx_le
      have hd2r : (d₂ : EReal) - ((c * δ : ℝ) : EReal) < q.1.1 - ((c * δ : ℝ) : EReal) :=
        EReal.sub_lt_sub_of_lt_of_le hLE (le_refl ((c * δ : ℝ) : EReal))
          (EReal.coe_ne_bot (c * δ)) (EReal.coe_ne_top (c * δ))
      have hd2r_tau : (τ : EReal) < ((d₂ - c * δ : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr hd2mr
      have h1 : (τ : EReal) < q.1.1 - ((c * δ : ℝ) : EReal) := lt_trans hd2r_tau hd2r
      have hx'_gt_tau : (τ : EReal) < (pt (γ a)).1 := lt_of_lt_of_le h1 hxr_le
      have hy'_le_2r : (pt (γ a)).2 ≤ ((2 * c * δ : ℝ) : EReal) := by
        by_contra hy'gt
        have hy'gt_r : ((c * δ : ℝ) : EReal) < (pt (γ a)).2 := by
          refine lt_trans ?_ (not_le.mp hy'gt)
          exact EReal.coe_lt_coe_iff.mpr (by linarith : (c * δ : ℝ) < 2 * c * δ)
        have hx'_gt_r : ((c * δ : ℝ) : EReal) < (pt (γ a)).1 := by
          refine lt_trans ?_ hx'_gt_tau
          exact EReal.coe_lt_coe_iff.mpr (by linarith : (c * δ : ℝ) < τ)
        have hQNEa : pt (γ a) ∈ QNE (c * δ) := ⟨hx'_gt_r, hy'gt_r⟩
        have hc1 := hii (γ a) hQNEa
        rw [Equiv.symm_apply_apply] at hc1
        rw [hpt_a] at hc1
        have hy_le : (pt (γ a)).2 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hc1.2.2
        have hyr_le : (pt (γ a)).2 - ((c * δ : ℝ) : EReal) ≤ q.1.2 :=
          EReal.sub_le_of_le_add hy_le
        have hsum : ((c * δ : ℝ) : EReal) + ((c * δ : ℝ) : EReal) = ((2 * c * δ : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          exact EReal.coe_eq_coe_iff.mpr (by ring)
        have hyr_gt_r : ((c * δ : ℝ) : EReal) < (pt (γ a)).2 - ((c * δ : ℝ) : EReal) := by
          rw [EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot (c * δ)))
              (Or.inl (EReal.coe_ne_top (c * δ))), hsum]
          exact not_le.mp hy'gt
        exact absurd hLE_r (not_le_of_gt (lt_of_lt_of_le hyr_gt_r hyr_le))
      have h2r_le_x'tau : ((2 * c * δ : ℝ) : EReal) ≤ (pt (γ a)).1 - (τ : EReal) := by
        have hco : ((τ + 3 * c * δ : ℝ) : EReal) < (d₂ : EReal) :=
          EReal.coe_lt_coe_iff.mpr (by linarith)
        have hco2 : ((τ + 3 * c * δ : ℝ) : EReal) < q.1.1 := lt_trans hco hLE
        have hco3 : ((τ + 3 * c * δ : ℝ) : EReal) - ((c * δ : ℝ) : EReal)
            < q.1.1 - ((c * δ : ℝ) : EReal) :=
          EReal.sub_lt_sub_of_lt_of_le hco2 (le_refl ((c * δ : ℝ) : EReal))
            (EReal.coe_ne_bot (c * δ)) (EReal.coe_ne_top (c * δ))
        have hco4 : ((τ + 3 * c * δ : ℝ) : EReal) - ((c * δ : ℝ) : EReal)
            = ((τ + 2 * c * δ : ℝ) : EReal) := by
          rw [← EReal.coe_sub]
          exact EReal.coe_eq_coe_iff.mpr (by ring)
        have hbig : ((τ + 2 * c * δ : ℝ) : EReal) < (pt (γ a)).1 :=
          hco4 ▸ lt_of_lt_of_le hco3 hxr_le
        have hlt : ((2 * c * δ : ℝ) : EReal) + (τ : EReal) < (pt (γ a)).1 := by
          rw [add_comm]; exact hbig
        exact le_of_lt ((EReal.lt_sub_iff_add_lt
          (Or.inl (EReal.coe_ne_bot τ)) (Or.inl (EReal.coe_ne_top τ))).mpr hlt)
      exact ⟨le_trans hy'_le_2r h2r_le_x'tau, hx'_gt_tau⟩
  -- not diagonal: γ a ≠ Sum.inr x₀
  have hnotdiag : ∀ x₀, γ a ≠ Sum.inr x₀ := by
    intro x₀
    intro hga
    have hpt : pt (γ a) = (x₀.1, x₀.1) := by rw [hga]; rfl
    have hDS' : x₀.1 ≤ x₀.1 - (τ : EReal) := by rw [hpt] at hreg; exact hreg.1
    have hLE' : (τ : EReal) < x₀.1 := by rw [hpt] at hreg; exact hreg.2
    by_cases hy : ((c * δ : ℝ) : EReal) < q.1.2
    case pos =>
      have hQNEa : pt a ∈ QNE (c * δ) := by
        rw [hpt_a]
        refine ⟨lt_trans (EReal.coe_lt_coe_iff.mpr hd2_gt_r) hLE, hy⟩
      have hc1 := hi a hQNEa
      rw [hpt_a, hpt] at hc1
      have hyu : closeE q.1.2 x₀.1 (c * δ) := hc1.2
      have hu_le : x₀.1 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hyu.2
      by_cases hu : x₀.1 = ⊤
      · exact absurd (pc_add_coe_top (le_antisymm le_top (by rw [hu] at hu_le; exact hu_le)))
          hy_ne_top
      · have hu_ne_bot : x₀.1 ≠ ⊥ := fun h => absurd (by rw [h] at hLE'; exact hLE') (not_lt_of_ge bot_le)
        have hureal : ((x₀.1).toReal : EReal) = x₀.1 := EReal.coe_toReal hu hu_ne_bot
        have hDSreal : x₀.1.toReal ≤ x₀.1.toReal - τ := by
          have := hDS'
          rw [← hureal, ← EReal.coe_sub] at this
          exact EReal.coe_le_coe_iff.mp this
        exact absurd htau_pos (by linarith)
    case neg =>
      have hLE_r : q.1.2 ≤ ((c * δ : ℝ) : EReal) := not_lt.mp hy
      have hQSEa : pt a ∈ QSE (c * δ) := by
        rw [hpt_a]
        refine ⟨lt_trans (EReal.coe_lt_coe_iff.mpr hd2_gt_r) hLE, hLE_r⟩
      have hc3 : closeE q.1.1 x₀.1 (c * δ) := by
        have h := hiii a hQSEa
        rw [hpt_a, hpt] at h
        exact h
      have hu_ge : q.1.1 - ((c * δ : ℝ) : EReal) ≤ x₀.1 := EReal.sub_le_of_le_add hc3.1
      have hd2r' : (d₂ : EReal) - ((c * δ : ℝ) : EReal) < q.1.1 - ((c * δ : ℝ) : EReal) :=
        EReal.sub_lt_sub_of_lt_of_le hLE (le_refl ((c * δ : ℝ) : EReal))
          (EReal.coe_ne_bot (c * δ)) (EReal.coe_ne_top (c * δ))
      have hd2r_tau' : (τ : EReal) < ((d₂ - c * δ : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr hd2mr
      have h1 : (τ : EReal) < q.1.1 - ((c * δ : ℝ) : EReal) := lt_trans hd2r_tau' hd2r'
      have h2 : (c * δ : ℝ) < τ := by linarith
      have hx0_gt_r : ((c * δ : ℝ) : EReal) < x₀.1 :=
        lt_trans (EReal.coe_lt_coe_iff.mpr h2) (lt_of_lt_of_le h1 hu_ge)
      have hQNEa : pt (γ a) ∈ QNE (c * δ) := by
        rw [hpt]
        exact ⟨hx0_gt_r, hx0_gt_r⟩
      have hc1 := hii (γ a) hQNEa
      rw [Equiv.symm_apply_apply, hpt_a, hpt] at hc1
      have hyu : closeE q.1.2 x₀.1 (c * δ) := hc1.2
      have hu_le : x₀.1 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hyu.2
      by_cases hu : x₀.1 = ⊤
      · exact absurd (pc_add_coe_top (le_antisymm le_top (by rw [hu] at hu_le; exact hu_le)))
          hy_ne_top
      · have hu_ne_bot : x₀.1 ≠ ⊥ := fun h => absurd (by rw [h] at hLE'; exact hLE') (not_lt_of_ge bot_le)
        have hureal : ((x₀.1).toReal : EReal) = x₀.1 := EReal.coe_toReal hu hu_ne_bot
        have hDSreal : x₀.1.toReal ≤ x₀.1.toReal - τ := by
          have := hDS'
          rw [← hureal, ← EReal.coe_sub] at this
          exact EReal.coe_le_coe_iff.mp this
        exact absurd htau_pos (by linarith)
  cases hγa : γ a with
  | inl b =>
    obtain ⟨w, hw⟩ := b
    refine ⟨w, hw, rfl, ?_⟩
    rw [hγa] at hreg
    exact hreg
  | inr x₀ => exact absurd hγa (hnotdiag x₀)

theorem solution
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂)
    (τ : ℝ) (hτ₁ : d₁ + 2 * c * δ < τ) (hτ₂ : τ < d₂ - 3 * c * δ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂}.encard
      ≤ {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ}.encard := by
  have key : ∀ (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D q.1)
      (hqin : q.1 ∈ DeltaS d₂ ∩ LamE d₂),
      ∃ (w : (EReal × EReal) × ℕ) (hw : (w.2 : ℕ∞) < D' w.1),
        γ (Sum.inl ⟨q, hq⟩) = Sum.inl ⟨w, hw⟩ ∧ w.1 ∈ DeltaS τ ∩ LamE τ :=
    fun q hq hqin =>
      pc_forward_inl D D' hD c δ hc hδ γ hγ d₁ d₂ hd₁ hδc τ hτ₁ hτ₂ q hq hqin
  choose w hw H using key
  have hInj : Function.Injective
      (fun a : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1 ∧ q.1 ∈ DeltaS d₂ ∩ LamE d₂} =>
        (⟨w a.1 a.2.1 a.2.2, ⟨hw a.1 a.2.1 a.2.2, (H a.1 a.2.1 a.2.2).2⟩⟩ :
          {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D' q.1 ∧ q.1 ∈ DeltaS τ ∩ LamE τ})) := by
    intro a₁ a₂ heq
    have hw' : w a₁.1 a₁.2.1 a₁.2.2 = w a₂.1 a₂.2.1 a₂.2.2 := congrArg Subtype.val heq
    have h₁ : γ (Sum.inl ⟨a₁.1, a₁.2.1⟩) = Sum.inl ⟨w a₁.1 a₁.2.1 a₁.2.2, hw a₁.1 a₁.2.1 a₁.2.2⟩ :=
      (H a₁.1 a₁.2.1 a₁.2.2).1
    have h₂ : γ (Sum.inl ⟨a₂.1, a₂.2.1⟩) = Sum.inl ⟨w a₂.1 a₂.2.1 a₂.2.2, hw a₂.1 a₂.2.1 a₂.2.2⟩ :=
      (H a₂.1 a₂.2.1 a₂.2.2).1
    have hga : γ (Sum.inl ⟨a₁.1, a₁.2.1⟩) = γ (Sum.inl ⟨a₂.1, a₂.2.1⟩) := by
      rw [h₁, h₂]
      exact congrArg Sum.inl (Subtype.ext hw')
    have hinl : (Sum.inl (⟨a₁.1, a₁.2.1⟩ : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1}) : Copies D)
        = (Sum.inl (⟨a₂.1, a₂.2.1⟩ : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1}) : Copies D) :=
      (Equiv.apply_eq_iff_eq γ).mp hga
    have hXY : (⟨a₁.1, a₁.2.1⟩ : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1}) =
        (⟨a₂.1, a₂.2.1⟩ : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1}) := by
      injection hinl
    have hv : a₁.1 = a₂.1 :=
      congrArg (fun x : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1} => x.1) hXY
    exact Subtype.ext hv
  exact ENat.card_le_card_of_injective hInj
