-- Prove2me | solution 1 for SubscriptionPlanning.GrandOptimal.theorem_2_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:33:43.134929+00:00
-- url     : https://prove2.me/submissions/c5a0a2ab-fa6b-4e4d-9057-8878035d74dd

import Mathlib
import Definitions.Def_SubscriptionPlanning_GrandOptimal_Setting
import Theorems.Thm_SubscriptionPlanning_GrandOptimal_lemma_2

open MeasureTheory SubscriptionPlanning.GrandOptimal

namespace SubPlanThm2Aux

/-- One-dimensional screening bound: any incentive-compatible, individually rational menu of
(allocation `x`, payment `p`) on the active set `T` earns at most `c * F`, where `F` bounds the
excess revenue `f(A k)` of every posted price `A k`. Proof by peeling off the lowest level. -/
theorem screening {n : ℕ} (q A B : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) (hB : ∀ i, B i ≤ A i)
    (F : ℝ) (hF0 : 0 ≤ F)
    (hfF : ∀ k, (∑ i, q i * (if A k ≤ A i then A k - B i else 0)) ≤ F) :
    ∀ (T : Finset (Fin n)) (x p : Fin n → ℝ) (c : ℝ), 0 ≤ c →
      (∀ i ∈ T, 0 ≤ x i ∧ x i ≤ c) →
      (∀ i ∈ T, ∀ j ∈ T, A i * x j - p j ≤ A i * x i - p i) →
      (∀ i ∈ T, p i ≤ A i * x i) →
      (∀ i, i ∉ T → ∀ j ∈ T, A i ≤ A j) →
      ∑ i ∈ T, q i * (p i - x i * B i) ≤ c * F := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro x p c hc hx hIC hIR hout
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst hT; simp only [Finset.sum_empty]; exact mul_nonneg hc hF0
  obtain ⟨k0, hk0T, hk0⟩ := Finset.exists_min_image T x hT
  obtain ⟨k1, hk1T, hk1⟩ := Finset.exists_min_image T A hT
  set y := x k0 with hy
  set τ := A k1 with hτ
  have hy0 : 0 ≤ y := (hx k0 hk0T).1
  have hyc : y ≤ c := (hx k0 hk0T).2
  set x' : Fin n → ℝ := fun i => x i - y with hx'
  set p' : Fin n → ℝ := fun i => p i - y * τ with hp'
  set T' := T.filter (fun i => y < x i) with hT'
  have hsub : T' ⊂ T := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro h
    have : k0 ∈ T' := h ▸ hk0T
    rw [Finset.mem_filter] at this
    exact lt_irrefl _ this.2
  -- IR after the shift, for every active type
  have hIR' : ∀ i ∈ T, p' i ≤ A i * x' i := by
    intro i hi
    have h1 := hIC i hi k1 hk1T
    have h2 := hIR k1 hk1T
    have h3 : τ ≤ A i := hk1 i hi
    have h4 : y ≤ x k1 := hk0 k1 hk1T
    have h5 : τ * (x k1 - y) ≤ A i * (x k1 - y) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    simp only [hx', hp']
    nlinarith
  have hrec := ih T' hsub x' p' (c - y) (by linarith)
    (by
      intro i hi
      rw [Finset.mem_filter] at hi
      refine ⟨?_, ?_⟩
      · simp only [hx']; linarith [hi.2]
      · simp only [hx']; linarith [(hx i hi.1).2])
    (by
      intro i hi j hj
      have := hIC i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
      simp only [hx', hp']
      linarith)
    (fun i hi => hIR' i (Finset.mem_filter.mp hi).1)
    (by
      intro i hi j hj
      rw [Finset.mem_filter] at hj
      by_cases hiT : i ∈ T
      · have hxi : x i ≤ y := by
          by_contra hcon
          exact hi (Finset.mem_filter.mpr ⟨hiT, lt_of_not_ge hcon⟩)
        have e1 := hIC i hiT j hj.1
        have e2 := hIC j hj.1 i hiT
        by_contra hcon
        push Not at hcon
        have : 0 < (A i - A j) * (x j - x i) := mul_pos (by linarith) (by linarith)
        nlinarith
      · exact hout i hiT j hj.1)
  -- decomposition of the sum
  have hsplit : ∑ i ∈ T, q i * (p i - x i * B i) =
      ∑ i ∈ T, q i * (p' i - x' i * B i) + y * ∑ i ∈ T, q i * (τ - B i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hx', hp']; ring
  have hpart : ∑ i ∈ T, q i * (p' i - x' i * B i) ≤ ∑ i ∈ T', q i * (p' i - x' i * B i) := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun i => y < x i)]
    have : ∑ i ∈ T.filter (fun i => ¬ y < x i), q i * (p' i - x' i * B i) ≤ 0 := by
      refine Finset.sum_nonpos (fun i hi => ?_)
      rw [Finset.mem_filter] at hi
      have hxi : x i = y := le_antisymm (le_of_not_gt hi.2) (hk0 i hi.1)
      have hx0 : x' i = 0 := by simp only [hx']; linarith
      have := hIR' i hi.1
      rw [hx0, mul_zero] at this
      rw [hx0, zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (hq i) this
    linarith
  have hlevel : ∑ i ∈ T, q i * (τ - B i) ≤ F := by
    refine le_trans ?_ (hfF k1)
    have e : ∑ i ∈ T, q i * (τ - B i) = ∑ i ∈ T, q i * (if A k1 ≤ A i then A k1 - B i else 0) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [if_pos (hk1 i hi)]
    rw [e]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun i _ hiT => ?_)
    split_ifs with h
    · have : A i ≤ A k1 := hout i hiT k1 hk1T
      have hAi : A i = A k1 := le_antisymm this h
      exact mul_nonneg (hq i) (by rw [← hAi]; linarith [hB i])
    · simp
  have hyF : y * ∑ i ∈ T, q i * (τ - B i) ≤ y * F := mul_le_mul_of_nonneg_left hlevel hy0
  rw [hsplit]
  nlinarith

variable {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem util_mono (M : Model n m Ω) (i : Fin n) {S S' : Finset (Fin m)} (h : S ⊆ S')
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (ω : Ω) (o : WithBot (Fin m)) :
    util M i S r ω o ≤ util M i S' r ω o := by
  induction o using WithBot.recBotCoe with
  | bot => simp [util]
  | coe j =>
    simp only [util, WithBot.recBotCoe_coe]
    by_cases hj : j ∈ S
    · simp [hj, h hj]
    · rw [if_neg hj]
      split_ifs
      · linarith [hr j]
      · exact le_rfl

theorem best_mono (M : Model n m Ω) (i : Fin n) {S S' : Finset (Fin m)} (h : S ⊆ S')
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) (ω : Ω) :
    best M i S r ω ≤ best M i S' r ω := by
  unfold best
  refine Finset.sup'_le _ _ (fun o _ => ?_)
  exact le_trans (util_mono M i h r hr ω o) (Finset.le_sup' _ (Finset.mem_univ o))

theorem best_integrable (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) : Integrable (fun ω => best M i S r ω) M.P := by
  have := hM.isProb
  have heq : (fun ω => best M i S r ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun o => fun ω => util M i S r ω o) := by
    funext ω
    simp [best, Finset.sup'_apply]
  rw [heq]
  refine Finset.sup'_induction _ _ (p := fun f => Integrable f M.P) ?_ ?_
  · intro a ha b hb
    exact ha.sup hb
  · intro o _
    induction o using WithBot.recBotCoe with
    | bot => simpa [util] using hM.intV0
    | coe j =>
      by_cases hj : j ∈ S
      · simpa [util, hj] using hM.intV i j
      · have := (hM.intV i j).sub (integrable_const (r j))
        simp only [util, WithBot.recBotCoe_coe, hj, if_false]
        exact this

theorem subGain_nonneg (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : 0 ≤ subGain M i S r := by
  unfold subGain
  have := integral_mono (best_integrable M hM i ∅ r) (best_integrable M hM i S r)
    (fun ω => best_mono M i (Finset.empty_subset S) r hr ω)
  linarith

theorem subGain_le (M : Model n m Ω) (hM : M.Valid) (i : Fin n) (S : Finset (Fin m))
    (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) : subGain M i S r ≤ subGain M i Finset.univ r := by
  unfold subGain
  have := integral_mono (best_integrable M hM i S r) (best_integrable M hM i Finset.univ r)
    (fun ω => best_mono M i (Finset.subset_univ S) r hr ω)
  linarith

theorem rent_nonneg (M : Model n m Ω) (i : Fin n) (S : Finset (Fin m)) (r : Fin m → ℝ)
    (hr : ∀ j, 0 ≤ r j) : 0 ≤ rent M i S r := by
  unfold rent
  refine integral_nonneg (fun ω => ?_)
  unfold rentPaid
  refine Finset.sum_nonneg (fun j _ => ?_)
  split_ifs
  · exact hr j
  · exact le_rfl

theorem subGain_empty (M : Model n m Ω) (i : Fin n) (r : Fin m → ℝ) : subGain M i ∅ r = 0 := by
  unfold subGain; ring

end SubPlanThm2Aux

open SubPlanThm2Aux in
theorem solution {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : SubscriptionPlanning.GrandOptimal.Model n m Ω)
    (hM : M.Valid) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hC : SubscriptionPlanning.GrandOptimal.Condition2 M r) :
    ∃ (P : ℝ) (σ : Fin n → Bool), SubscriptionPlanning.GrandOptimal.IsGrandFeasible M r P σ ∧
      ∀ (p : Finset (Fin m) → ℝ) (S : Fin n → Finset (Fin m)),
        SubscriptionPlanning.GrandOptimal.IsFeasible M r p S →
          SubscriptionPlanning.GrandOptimal.revenue M r p S ≤
            SubscriptionPlanning.GrandOptimal.grandRevenue M r P σ := by
  -- notation
  set A : Fin n → ℝ := fun i => M.lam i * M.T * subGain M i Finset.univ r with hA
  set B : Fin n → ℝ := fun i => M.lam i * M.T * rent M i ∅ r with hBdef
  have hlT : ∀ i, 0 < M.lam i * M.T := fun i => mul_pos (hM.lam_pos i) hM.T_pos
  have hG0 : ∀ i, 0 ≤ subGain M i Finset.univ r := fun i => subGain_nonneg M hM i _ r hr
  have hs0 : ∀ i S, 0 ≤ subGain M i S r := fun i S => subGain_nonneg M hM i S r hr
  have hsG : ∀ i S, subGain M i S r ≤ subGain M i Finset.univ r := fun i S => subGain_le M hM i S r hr
  have hR0 : ∀ i S, 0 ≤ rent M i S r := fun i S => rent_nonneg M i S r hr
  have hL2 : ∀ i S, subGain M i S r + rent M i S r ≤ subGain M i Finset.univ r := fun i S =>
    SubscriptionPlanning.GrandOptimal.lemma_2 M hM r hr i S
  have hBA : ∀ i, B i ≤ A i := by
    intro i
    have h := hL2 i ∅
    rw [subGain_empty, zero_add] at h
    exact mul_le_mul_of_nonneg_left h (hlT i).le
  have hB0 : ∀ i, 0 ≤ B i := fun i => mul_nonneg (hlT i).le (hR0 i ∅)
  have hq := hM.q_nonneg
  -- the posted-price excess revenue
  set f : ℝ → ℝ := fun P => ∑ i, M.q i * (if P ≤ A i then P - B i else 0) with hf
  -- choose the best posted price (or a prohibitive one)
  obtain ⟨P0, hP0, hP0max⟩ : ∃ P0 : ℝ, 0 ≤ f P0 ∧ ∀ k, f (A k) ≤ f P0 := by
    by_cases h : ∃ k, 0 ≤ f (A k) ∧ ∀ k', f (A k') ≤ f (A k)
    · obtain ⟨k, hk1, hk2⟩ := h
      exact ⟨A k, hk1, hk2⟩
    · push Not at h
      refine ⟨∑ i, |A i| + 1, ?_, ?_⟩
      · have : f (∑ i, |A i| + 1) = 0 := by
          simp only [hf]
          refine Finset.sum_eq_zero (fun i _ => ?_)
          rw [if_neg]
          · ring
          · have h1 : A i ≤ |A i| := le_abs_self _
            have h2 : |A i| ≤ ∑ j, |A j| :=
              Finset.single_le_sum (f := fun j => |A j|) (fun j _ => abs_nonneg _)
                (Finset.mem_univ i)
            linarith
        rw [this]
      · have hall : ∀ k, f (A k) ≤ 0 := by
          intro k
          by_contra hk
          push Not at hk
          obtain ⟨k', _, hk'⟩ := Finset.exists_max_image Finset.univ (fun k => f (A k))
            ⟨k, Finset.mem_univ k⟩
          obtain ⟨k'', hk''⟩ := h k' (le_trans hk.le (hk' k (Finset.mem_univ k)))
          exact absurd (hk' k'' (Finset.mem_univ _)) (not_le.mpr hk'')
        have : f (∑ i, |A i| + 1) = 0 := by
          simp only [hf]
          refine Finset.sum_eq_zero (fun i _ => ?_)
          rw [if_neg]
          · ring
          · have h1 : A i ≤ |A i| := le_abs_self _
            have h2 : |A i| ≤ ∑ j, |A j| :=
              Finset.single_le_sum (f := fun j => |A j|) (fun j _ => abs_nonneg _)
                (Finset.mem_univ i)
            linarith
        intro k; rw [this]; exact hall k
  refine ⟨P0, fun i => decide (P0 ≤ A i), ?_, ?_⟩
  · intro i
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa [hA] using h
    · have : ¬ P0 ≤ A i := by simpa using h
      have := (lt_of_not_ge this).le
      simpa [hA] using this
  intro p S hF
  -- the reduced one-dimensional data
  set x : Fin n → ℝ := fun i => relGain M i (S i) r with hx
  set pp : Fin n → ℝ := fun i => p (S i) with hpp
  have hx01 : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
    intro i
    refine ⟨div_nonneg (hs0 i _) (hG0 i), div_le_one_of_le₀ (hsG i _) (hG0 i)⟩
  have hAx : ∀ i, A i * x i = M.lam i * M.T * subGain M i (S i) r := by
    intro i
    simp only [hA, hx, relGain]
    rcases (hG0 i).lt_or_eq with hpos | hzero
    · have hne := hpos.ne'
      field_simp
    · have : subGain M i (S i) r = 0 := le_antisymm (by rw [hzero]; exact hsG i _) (hs0 i _)
      rw [this, ← hzero]; simp
  have hAxj : ∀ i j, A i * x j ≤ M.lam i * M.T * subGain M i (S j) r := by
    intro i j
    simp only [hA, hx, relGain]
    rcases (hG0 j).lt_or_eq with hpos | hzero
    · have hc := hC.2 i j (S j)
      have : subGain M i Finset.univ r * (subGain M j (S j) r / subGain M j Finset.univ r) = subGain M i (S j) r := by
        rw [mul_div_assoc', div_eq_iff hpos.ne']
        linarith
      rw [mul_assoc, this]
    · have h0 : subGain M j Finset.univ r = 0 := by simpa using hzero.symm
      rw [h0, div_zero, mul_zero]
      exact mul_nonneg (hlT i).le (hs0 i _)
  have hIC : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      A i * x j - pp j ≤ A i * x i - pp i := by
    intro i _ j _
    have h1 := hF.2 i (S j)
    have h2 := hAxj i j
    have h3 := hAx i
    simp only [hpp]
    linarith
  have hIR : ∀ i ∈ (Finset.univ : Finset (Fin n)), pp i ≤ A i * x i := by
    intro i _
    have h1 := hF.2 i ∅
    rw [subGain_empty, hF.1, mul_zero, sub_zero] at h1
    rw [hAx i]
    simp only [hpp]
    linarith
  have hscr := screening M.q A B hq hBA (f P0) hP0 (fun k => hP0max k) Finset.univ x pp 1
    zero_le_one (fun i _ => hx01 i) hIC hIR (fun i hi => absurd (Finset.mem_univ i) hi)
  -- rent bound from part 1 of Condition 2
  have hrent : ∀ i, M.lam i * M.T * rent M i (S i) r ≤ (1 - x i) * B i := by
    intro i
    show _ ≤ (1 - x i) * (M.lam i * M.T * rent M i ∅ r)
    rcases (hG0 i).lt_or_eq with hpos | hzero
    · have hc := hC.1 i (S i)
      have : rent M i (S i) r ≤ (1 - x i) * rent M i ∅ r := by
        have key : x i * rent M i ∅ r ≤ rent M i ∅ r - rent M i (S i) r := by
          simp only [hx, relGain]
          rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
          linarith
        linarith
      calc M.lam i * M.T * rent M i (S i) r ≤ M.lam i * M.T * ((1 - x i) * rent M i ∅ r) :=
            mul_le_mul_of_nonneg_left this (hlT i).le
        _ = (1 - x i) * (M.lam i * M.T * rent M i ∅ r) := by ring
    · have hxi : x i = 0 := by
        simp only [hx, relGain]
        have h0 : subGain M i Finset.univ r = 0 := by simpa using hzero.symm
        rw [h0, div_zero]
      rw [hxi, sub_zero, one_mul]
      have h := hL2 i (S i)
      rw [← hzero] at h
      have h' : rent M i (S i) r ≤ rent M i ∅ r := by linarith [hs0 i (S i), hR0 i ∅]
      exact mul_le_mul_of_nonneg_left h' (hlT i).le
  -- assemble
  have hrev : revenue M r p S ≤ ∑ i, M.q i * B i + ∑ i, M.q i * (pp i - x i * B i) := by
    unfold revenue
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := mul_le_mul_of_nonneg_left (hrent i) (hq i)
    simp only [hpp]
    nlinarith
  have hgrand : ∑ i, M.q i * B i + f P0 ≤ grandRevenue M r P0 (fun i => decide (P0 ≤ A i)) := by
    unfold grandRevenue
    simp only [hf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases h : P0 ≤ A i
    · rw [if_pos h]
      simp only [h, decide_true, if_true]
      have := mul_nonneg (hlT i).le (hR0 i Finset.univ)
      have := mul_le_mul_of_nonneg_left (show P0 ≤ P0 + M.lam i * M.T * rent M i Finset.univ r
        by linarith) (hq i)
      nlinarith
    · rw [if_neg h]
      simp only [h, decide_false, Bool.false_eq_true, if_false, mul_zero, add_zero]
      exact le_rfl
  linarith
