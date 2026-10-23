-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P21.detectionWaterfilling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:20:41.891156+00:00
-- url     : https://prove2.me/submissions/966d7f13-1d0b-4202-afb7-d7b15e44a609

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

noncomputable section

namespace X7P21Water

open QAlgorithms.Papers.Independent.Frontier30.P21

/-- Tangent-line bound for one water-filling term. -/
lemma term (ξ η c N M : ℝ) (hξ : 0 < ξ) (hη : 0 < η) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hc : 0 < N → η / (ξ ^ 2 + η * N) = c) (hc0 : N = 0 → η / ξ ^ 2 ≤ c) :
    ξ * Real.logb 2 (1 + η * M / ξ ^ 2) ≤
      ξ * Real.logb 2 (1 + η * N / ξ ^ 2) + ξ / Real.log 2 * (c * (M - N)) := by
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have hX : 0 < 1 + η * M / ξ ^ 2 := by positivity
  have hY : 0 < 1 + η * N / ξ ^ 2 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log (1 + η * M / ξ ^ 2) - Real.log (1 + η * N / ξ ^ 2) ≤ c * (M - N) := by
    rw [← Real.log_div hX.ne' hY.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hX hY)).trans ?_
    have e : (1 + η * M / ξ ^ 2) / (1 + η * N / ξ ^ 2) - 1 = η / (ξ ^ 2 + η * N) * (M - N) := by
      field_simp; ring
    rw [e]
    rcases eq_or_lt_of_le hN with h0 | hpos
    · subst h0
      have := hc0 rfl
      simp only [mul_zero, add_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right this hM
    · rw [hc hpos]
  simp only [Real.logb]
  have : ξ * (Real.log (1 + η * M / ξ ^ 2) / Real.log 2) - ξ * (Real.log (1 + η * N / ξ ^ 2) / Real.log 2)
      = ξ / Real.log 2 * (Real.log (1 + η * M / ξ ^ 2) - Real.log (1 + η * N / ξ ^ 2)) := by ring
  have h2 := mul_le_mul_of_nonneg_left key (div_pos hξ hl2).le
  linarith

lemma grid_pos {m : ℕ} {spacing : ℝ} (hs : 0 < spacing) (i : Fin m) : 0 < gridFrequency spacing i := by
  unfold gridFrequency; positivity

lemma trans_pos {m : ℕ} {spacing cutoff Dc : ℝ} (hs : 0 < spacing) (hc : 0 < cutoff) (hD : 0 < Dc)
    (i : Fin m) : 0 < gridTransmission spacing cutoff Dc i := by
  unfold gridTransmission; have := grid_pos (m := m) hs i; positivity

end X7P21Water

open QAlgorithms.Papers.Independent.Frontier30.P21 X7P21Water in
theorem solution (m : ℕ) (hm : 0 < m)
    (hbar spacing cutoff Dc xi E : ℝ)
    (hhbar : 0 < hbar) (hspacing : 0 < spacing) (hcutoff : 0 < cutoff)
    (hgridLow : (m : ℝ) * spacing ≤ cutoff)
    (hgridHigh : cutoff < ((m : ℝ) + 1) * spacing)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hxi : xi = 1 / 2 ∨ xi = 1) (hE : 0 ≤ E) :
    (E = 0 → OptimalAllocation (m := m) hbar spacing cutoff Dc xi E (fun _ => 0)) ∧
    (0 < E → ∃ beta : ℝ, 0 < beta ∧
      OptimalAllocation hbar spacing cutoff Dc xi E
        (receiverAllocation (m := m) hbar spacing cutoff Dc xi beta) ∧
      ∀ i : Fin m,
        (0 < receiverAllocation hbar spacing cutoff Dc xi beta i ↔
          xi ^ 2 * beta * hbar * cutoff ^ 2 / Dc < gridFrequency spacing i) ∧
        (receiverAllocation hbar spacing cutoff Dc xi beta i = 0 ↔
          gridFrequency spacing i ≤ xi ^ 2 * beta * hbar * cutoff ^ 2 / Dc)) := by
  have hξ : 0 < xi := by rcases hxi with h | h <;> rw [h] <;> norm_num
  have hw := grid_pos (m := m) hspacing
  have hη := trans_pos (m := m) hspacing hcutoff hDc0
  constructor
  · -- zero energy
    intro hE0
    subst hE0
    have hzero : ∀ M : Fin m → ℝ, FeasibleAllocation hbar spacing 0 M → M = fun _ => 0 := by
      intro M ⟨hM, hsum⟩
      unfold allocationEnergy at hsum
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ hbar * gridFrequency spacing i * M i := fun i _ =>
        mul_nonneg (mul_pos hhbar (hw i)).le (hM i)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
      funext i
      have h1 := this i (Finset.mem_univ _)
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h (mul_pos hhbar (hw i)).ne'
      · exact h
    refine ⟨⟨fun _ => le_rfl, by simp [allocationEnergy]⟩, fun M hM => ?_⟩
    rw [hzero M hM]
  · intro hEpos
    -- the energy of the water-filling allocation as a function of beta
    set F : ℝ → ℝ := fun β => allocationEnergy hbar spacing
      (receiverAllocation (m := m) hbar spacing cutoff Dc xi β) with hF
    set c : Fin m → ℝ := fun i => xi ^ 2 / gridTransmission spacing cutoff Dc i with hcdef
    have hcpos : ∀ i, 0 < c i := fun i => div_pos (by positivity) (hη i)
    have hcont : ContinuousOn F (Set.Ioi 0) := by
      simp only [hF, allocationEnergy, receiverAllocation]
      refine continuousOn_finsetSum _ (fun i _ => ?_)
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.sup ?_ continuousOn_const)
      refine ContinuousOn.sub (ContinuousOn.div continuousOn_const ?_ ?_) continuousOn_const
      · fun_prop
      · intro x hx
        exact (mul_pos (mul_pos hx hhbar) (hw i)).ne'
    have hFnn : ∀ β, 0 ≤ F β := fun β => Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_pos hhbar (hw i)).le (le_max_right _ _))
    let i0 : Fin m := ⟨0, hm⟩
    set lo := 1 / (E + hbar * gridFrequency spacing i0 * c i0) with hlo
    have hlo_pos : 0 < lo := by
      have := mul_pos (mul_pos hhbar (hw i0)) (hcpos i0); positivity
    have hFlo : E ≤ F lo := by
      have h1 : hbar * gridFrequency spacing i0 *
          receiverAllocation hbar spacing cutoff Dc xi lo i0 ≤ F lo := by
        simp only [hF, allocationEnergy]
        exact Finset.single_le_sum (f := fun i => hbar * gridFrequency spacing i *
          receiverAllocation hbar spacing cutoff Dc xi lo i)
          (fun i _ => mul_nonneg (mul_pos hhbar (hw i)).le (le_max_right _ _)) (Finset.mem_univ i0)
      have h2 : hbar * gridFrequency spacing i0 * (1 / (lo * hbar * gridFrequency spacing i0) - c i0) ≤
          hbar * gridFrequency spacing i0 * receiverAllocation hbar spacing cutoff Dc xi lo i0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (mul_pos hhbar (hw i0)).le
      have h3 : hbar * gridFrequency spacing i0 * (1 / (lo * hbar * gridFrequency spacing i0) - c i0) = E := by
        have := hw i0
        rw [hlo]
        field_simp
        ring
      linarith
    set hi := ∑ i, 1 / (hbar * gridFrequency spacing i * c i) with hhi
    have hterm_le : ∀ i, 1 / (hbar * gridFrequency spacing i * c i) ≤ hi := fun i =>
      Finset.single_le_sum (f := fun i => 1 / (hbar * gridFrequency spacing i * c i))
        (fun i _ => (one_div_pos.2 (mul_pos (mul_pos hhbar (hw i)) (hcpos i))).le) (Finset.mem_univ i)
    have hhi_pos : 0 < hi := lt_of_lt_of_le
      (one_div_pos.2 (mul_pos (mul_pos hhbar (hw i0)) (hcpos i0))) (hterm_le i0)
    have hFhi : F hi = 0 := by
      simp only [hF, allocationEnergy, receiverAllocation]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hpos := mul_pos (mul_pos hhbar (hw i)) (hcpos i)
      have h1 : 1 / (hi * hbar * gridFrequency spacing i) ≤ c i := by
        rw [div_le_iff₀ (by have := hw i; positivity)]
        have := hterm_le i
        rw [div_le_iff₀ hpos] at this
        nlinarith
      rw [max_eq_right (by simp only [hcdef] at h1; linarith)]
      ring
    have hsub : Set.uIcc lo hi ⊆ Set.Ioi 0 := by
      intro x hx
      have := (Set.mem_uIcc.1 hx)
      simp only [Set.mem_Ioi]
      rcases this with h | h <;> linarith [h.1]
    obtain ⟨β, hβmem, hFβ⟩ := intermediate_value_uIcc (hcont.mono hsub)
      (Set.mem_uIcc.2 (Or.inr ⟨by rw [hFhi]; exact hE, hFlo⟩))
    have hβ : 0 < β := hsub hβmem
    set N := receiverAllocation (m := m) hbar spacing cutoff Dc xi β with hN
    have hNnn : ∀ i, 0 ≤ N i := fun i => le_max_right _ _
    -- sign of an allocation entry
    have hsign : ∀ i, (0 < N i ↔ xi ^ 2 * β * hbar * cutoff ^ 2 / Dc < gridFrequency spacing i) := by
      intro i
      have hwi := hw i
      have hηi := hη i
      simp only [hN, receiverAllocation, lt_max_iff, lt_irrefl, or_false, sub_pos]
      rw [div_lt_div_iff₀ (by positivity) (by positivity), div_lt_iff₀ hDc0]
      simp only [gridTransmission]
      rw [div_pow, ← sub_pos, ← sub_pos (b := xi ^ 2 * β * hbar * cutoff ^ 2)]
      have e : 1 * (Dc * (gridFrequency spacing i ^ 2 / cutoff ^ 2)) -
          xi ^ 2 * (β * hbar * gridFrequency spacing i) =
          gridFrequency spacing i / cutoff ^ 2 *
            (gridFrequency spacing i * Dc - xi ^ 2 * β * hbar * cutoff ^ 2) := by
        field_simp <;> ring
      rw [e]
      constructor
      · intro h; exact pos_of_mul_pos_right h (by positivity)
      · intro h; positivity
    refine ⟨β, hβ, ⟨⟨hNnn, hFβ⟩, fun M ⟨hM, hME⟩ => ?_⟩, fun i => ⟨hsign i, ?_⟩⟩
    · -- optimality
      unfold receiverObjective
      have hl : ∀ i, xi * Real.logb 2 (1 + gridTransmission spacing cutoff Dc i * M i / xi ^ 2) ≤
          xi * Real.logb 2 (1 + gridTransmission spacing cutoff Dc i * N i / xi ^ 2) +
            xi / Real.log 2 * ((β * hbar * gridFrequency spacing i) * (M i - N i)) := by
        intro i
        have hwi := hw i
        have hηi := hη i
        apply term xi _ _ _ _ hξ hηi (hNnn i) (hM i)
        · intro hpos
          have hNi : N i = 1 / (β * hbar * gridFrequency spacing i) -
              xi ^ 2 / gridTransmission spacing cutoff Dc i := by
            have : N i = max (1 / (β * hbar * gridFrequency spacing i) -
              xi ^ 2 / gridTransmission spacing cutoff Dc i) 0 := rfl
            rw [this] at hpos ⊢
            exact max_eq_left (by
              by_contra hh
              rw [max_eq_right (le_of_lt (not_le.1 hh))] at hpos
              exact lt_irrefl _ hpos)
          rw [hNi]
          have := hηi.ne'
          have := hwi.ne'
          have := hβ.ne'
          have := hhbar.ne'
          field_simp
          ring_nf
          field_simp
        · intro h0
          have : N i = max (1 / (β * hbar * gridFrequency spacing i) -
              xi ^ 2 / gridTransmission spacing cutoff Dc i) 0 := rfl
          rw [h0] at this
          have h1 : 1 / (β * hbar * gridFrequency spacing i) ≤
              xi ^ 2 / gridTransmission spacing cutoff Dc i := by
            have := le_max_left (1 / (β * hbar * gridFrequency spacing i) -
              xi ^ 2 / gridTransmission spacing cutoff Dc i) 0
            linarith
          rw [div_le_div_iff₀ (by positivity) hηi] at h1
          rw [div_le_iff₀ (by positivity)]
          linarith
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
      rw [Finset.sum_add_distrib] at hs
      have hpull : ∑ i, xi / Real.log 2 * (β * hbar * gridFrequency spacing i * (M i - N i)) =
          xi / Real.log 2 * ∑ i, β * hbar * gridFrequency spacing i * (M i - N i) := by
        rw [Finset.mul_sum]
      rw [hpull] at hs
      have hz : ∑ i, β * hbar * gridFrequency spacing i * (M i - N i) = 0 := by
        have e1 : ∑ i, β * hbar * gridFrequency spacing i * (M i - N i) =
            β * (allocationEnergy hbar spacing M - allocationEnergy hbar spacing N) := by
          simp only [allocationEnergy, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => by ring)
        rw [e1, hME]
        have : allocationEnergy hbar spacing N = E := hFβ
        rw [this]; ring
      rw [hz, mul_zero, add_zero] at hs
      exact hs
    · have h := hsign i
      constructor
      · intro h0; by_contra hc; exact (h.2 (not_le.1 hc)).ne' h0
      · intro hle; by_contra hc
        exact (not_lt.2 hle) (h.1 (lt_of_le_of_ne (hNnn i) (Ne.symm hc)))
