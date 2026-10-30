-- Prove2me | solution 1 for RepeatedNRM.Myopic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:36:46.26778+00:00
-- url     : https://prove2.me/submissions/75675b1a-dec2-4078-a3d1-6c858ee2f814

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Proof

open RepeatedNRM.Myopic

namespace RNRMLemma2

variable (I : Instance)

/-- spending of customer `k` under allocation `y` -/
def spend (y : Fin I.n → Fin I.m → ℝ) (k : Fin I.m) : ℝ := ∑ i, I.p i k * y i k

lemma revenue_eq_sum_spend (y : Fin I.n → Fin I.m → ℝ) :
    revenue I y = ∑ k, spend I y k := by
  unfold revenue spend; rw [Finset.sum_comm]

/-- convex combination -/
def cc (t : ℝ) (x y : Fin I.n → Fin I.m → ℝ) : Fin I.n → Fin I.m → ℝ :=
  fun a c => (1 - t) * x a c + t * y a c

lemma spend_cc (t : ℝ) (x y : Fin I.n → Fin I.m → ℝ) (k : Fin I.m) :
    spend I (cc I t x y) k = (1 - t) * spend I x k + t * spend I y k := by
  unfold spend cc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; ring

lemma rowsum_cc (t : ℝ) (x y : Fin I.n → Fin I.m → ℝ) (a : Fin I.n) :
    ∑ c, cc I t x y a c = (1 - t) * ∑ c, x a c + t * ∑ c, y a c := by
  unfold cc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

lemma revenue_cc (t : ℝ) (x y : Fin I.n → Fin I.m → ℝ) :
    revenue I (cc I t x y) = (1 - t) * revenue I x + t * revenue I y := by
  rw [revenue_eq_sum_spend, revenue_eq_sum_spend, revenue_eq_sum_spend]
  simp_rw [spend_cc]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- transfer: add `η` at `(i,l)` and subtract `η'` at `(i,k)` -/
def tr (z : Fin I.n → Fin I.m → ℝ) (i : Fin I.n) (l k : Fin I.m) (η η' : ℝ) :
    Fin I.n → Fin I.m → ℝ :=
  fun a c => z a c + (if a = i then ((if c = l then η else 0) - (if c = k then η' else 0)) else 0)

lemma rowsum_tr (z : Fin I.n → Fin I.m → ℝ) (i : Fin I.n) (l k : Fin I.m) (η η' : ℝ)
    (a : Fin I.n) :
    ∑ c, tr I z i l k η η' a c = ∑ c, z a c + (if a = i then η - η' else 0) := by
  unfold tr
  rw [Finset.sum_add_distrib]
  congr 1
  split_ifs with h
  · rw [Finset.sum_sub_distrib]; simp
  · simp

lemma spend_tr (z : Fin I.n → Fin I.m → ℝ) (i : Fin I.n) (l k : Fin I.m) (η η' : ℝ)
    (c : Fin I.m) :
    spend I (tr I z i l k η η') c = spend I z c +
      ((if c = l then I.p i c * η else 0) - (if c = k then I.p i c * η' else 0)) := by
  unfold spend tr
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    split_ifs <;> ring
  · intro a _ ha; simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma revenue_tr (z : Fin I.n → Fin I.m → ℝ) (i : Fin I.n) (l k : Fin I.m) (η η' : ℝ) :
    revenue I (tr I z i l k η η') = revenue I z + I.p i l * η - I.p i k * η' := by
  rw [revenue_eq_sum_spend, revenue_eq_sum_spend]
  simp_rw [spend_tr]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']
  ring

/-- The invariant of the augmenting-path argument. -/
def Q (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (l : Fin I.m) : Prop :=
  ∃ (y : Fin I.n → Fin I.m → ℝ) (κ : ℝ), 0 < κ ∧ (∀ a c, 0 ≤ y a c) ∧
    (∀ a, ∑ c, y a c ≤ ∑ c, x a c) ∧ (∀ c, c ≠ l → spend I y c ≤ b c) ∧
    spend I y l + κ ≤ b l ∧ revenue I x < revenue I y + κ

lemma Q_scale (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ) (hx : feasible I b x)
    (l : Fin I.m) (y : Fin I.n → Fin I.m → ℝ) (κ : ℝ) (hκ : 0 < κ) (hy0 : ∀ a c, 0 ≤ y a c)
    (hys : ∀ a, ∑ c, y a c ≤ ∑ c, x a c) (hyb : ∀ c, c ≠ l → spend I y c ≤ b c)
    (hyl : spend I y l + κ ≤ b l) (hyr : revenue I x < revenue I y + κ)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 < t * κ ∧ (∀ a c, 0 ≤ cc I t x y a c) ∧
    (∀ a, ∑ c, cc I t x y a c ≤ ∑ c, x a c) ∧ (∀ c, c ≠ l → spend I (cc I t x y) c ≤ b c) ∧
    spend I (cc I t x y) l + t * κ ≤ b l ∧ revenue I x < revenue I (cc I t x y) + t * κ := by
  obtain ⟨hx0, hxb, _⟩ := hx
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨mul_pos ht0 hκ, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c; unfold cc
    have := hx0 a c; have := hy0 a c; positivity
  · intro a; rw [rowsum_cc]; have := hys a; nlinarith
  · intro c hc; rw [spend_cc]; have := hyb c hc; have := hxb c
    unfold spend at *; nlinarith
  · rw [spend_cc]; have := hxb l; unfold spend at *; nlinarith
  · rw [revenue_cc]; nlinarith

end RNRMLemma2

open RNRMLemma2 in
theorem solution (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h2 : Assumption2 I A γ) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin I.n → Fin I.m → ℝ) (hx : IsMyopicAlloc I b1 x) (j : Fin I.m)
    (hj : ∑ i ∈ A j, I.p i j * x i j < b1 j) :
    ∀ i, (∃ l ∈ customerClass I A x j, i ∈ A l) →
      ∑ l ∈ customerClass I A x j, x i l = I.s i := by
  classical
  obtain ⟨hxf, hopt⟩ := hx
  obtain ⟨hx0, hxb, hxs⟩ := hxf
  obtain ⟨_, hout, hpos, _⟩ := h2
  -- spending of j equals the sum over A j
  have hjs : spend I x j < b1 j := by
    have : spend I x j = ∑ i ∈ A j, I.p i j * x i j := by
      unfold spend
      rw [← Finset.sum_subset (Finset.subset_univ (A j))]
      intro a _ ha; rw [(hout j a ha).2]; ring
    rw [this]; exact hj
  -- base case
  have hQj : Q I b1 x j := by
    refine ⟨x, b1 j - spend I x j, by linarith, hx0, fun a => le_refl _, ?_, by linarith, ?_⟩
    · intro c _; exact hxb c
    · linarith
  -- step
  have hstep : ∀ l, InClass I A x j l → Q I b1 x l := by
    intro l hl
    induction hl with
    | self => exact hQj
    | @step l k i hl hil hxik ih =>
      by_cases hkl : k = l
      · subst hkl; exact ih
      obtain ⟨y, κ, hκ, hy0, hys, hyb, hyl, hyr⟩ := ih
      have hpil : 0 < I.p i l := hpos l i hil
      -- choose t
      set t : ℝ := min 1 (x i k / (|y i k - x i k| + κ / I.p i l)) with ht
      have hden : 0 < |y i k - x i k| + κ / I.p i l := by
        have := div_pos hκ hpil; positivity
      have ht0 : 0 < t := lt_min one_pos (div_pos hxik hden)
      have ht1 : t ≤ 1 := min_le_left _ _
      have htle : t * (|y i k - x i k| + κ / I.p i l) ≤ x i k := by
        have := min_le_right 1 (x i k / (|y i k - x i k| + κ / I.p i l))
        rw [← ht] at this
        calc t * (|y i k - x i k| + κ / I.p i l)
            ≤ x i k / (|y i k - x i k| + κ / I.p i l) * (|y i k - x i k| + κ / I.p i l) :=
              mul_le_mul_of_nonneg_right this hden.le
          _ = x i k := div_mul_cancel₀ _ hden.ne'
      obtain ⟨hκ', hz0, hzs, hzb, hzl, hzr⟩ :=
        Q_scale I b1 x ⟨hx0, hxb, hxs⟩ l y κ hκ hy0 hys hyb hyl hyr t ht0 ht1
      set z := cc I t x y with hz
      set η := t * κ / I.p i l with hη
      have hη0 : 0 < η := div_pos hκ' hpil
      have hpη : I.p i l * η = t * κ := by rw [hη]; field_simp
      -- z i k - η ≥ 0
      have hzik : η ≤ z i k := by
        have e1 : z i k = x i k + t * (y i k - x i k) := by rw [hz]; unfold cc; ring
        have e2 : -(t * |y i k - x i k|) ≤ t * (y i k - x i k) := by
          rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le _) ht0.le
        have e3 : η = t * (κ / I.p i l) := by rw [hη]; ring
        nlinarith
      have hkpos : 0 ≤ I.p i k := hI.2.1 i k
      rcases hkpos.lt_or_eq with hpk | hpk
      · -- genuine step
        refine ⟨tr I z i l k η η, I.p i k * η, mul_pos hpk hη0, ?_, ?_, ?_, ?_, ?_⟩
        · intro a c; unfold tr
          by_cases ha : a = i
          · subst ha
            by_cases hcl : c = l
            · subst hcl; simp [Ne.symm hkl]; have := hz0 a c; linarith
            · by_cases hck : c = k
              · subst hck; simp [hcl]; linarith
              · simp [hcl, hck]; exact hz0 a c
          · simp [ha]; exact hz0 a c
        · intro a; rw [rowsum_tr]; split_ifs <;> simp [hzs a]
        · intro c hc; rw [spend_tr]
          by_cases hcl : c = l
          · subst hcl; simp [Ne.symm hkl]; rw [hpη]; linarith
          · simp [hcl, hc]; exact hzb c hcl
        · rw [spend_tr]; simp [hkl]; have := hzb k hkl; linarith
        · rw [revenue_tr]; linarith
      · -- price zero for k: improving direction, contradiction
        exfalso
        have hw := hopt (tr I z i l k η η) ⟨?_, ?_, ?_⟩
        · rw [revenue_tr, ← hpk] at hw; linarith
        · intro a c; unfold tr
          by_cases ha : a = i
          · subst ha
            by_cases hcl : c = l
            · subst hcl; simp [Ne.symm hkl]; have := hz0 a c; linarith
            · by_cases hck : c = k
              · subst hck; simp [hcl]; linarith
              · simp [hcl, hck]; exact hz0 a c
          · simp [ha]; exact hz0 a c
        · intro c
          have := spend_tr I z i l k η η c
          unfold spend at this; rw [this]
          by_cases hcl : c = l
          · subst hcl; simp [Ne.symm hkl]; rw [hpη]; unfold spend at hzl; linarith
          · by_cases hck : c = k
            · subst hck; simp [hcl, ← hpk]; have := hzb c hcl; unfold spend at this; linarith
            · simp [hcl, hck]; have := hzb c hcl; unfold spend at this; linarith
        · intro a; rw [rowsum_tr]
          have := hzs a; have := hxs a
          split_ifs <;> simp <;> linarith
  -- conclusion
  intro i ⟨l, hlC, hil⟩
  have hlin : InClass I A x j l := by
    simpa [customerClass] using hlC
  have hQl := hstep l hlin
  -- total allocation of i equals supply
  have htot : ∑ k, x i k = I.s i := by
    by_contra hne
    have hlt : ∑ k, x i k < I.s i := lt_of_le_of_ne (hxs i) hne
    obtain ⟨y, κ, hκ, hy0, hys, hyb, hyl, hyr⟩ := hQl
    have hpil : 0 < I.p i l := hpos l i hil
    set g := I.s i - ∑ k, x i k with hg
    have hg0 : 0 < g := by linarith
    set t : ℝ := min 1 (g * I.p i l / κ) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htg : t * κ / I.p i l ≤ g := by
      rw [div_le_iff₀ hpil]
      have := min_le_right 1 (g * I.p i l / κ)
      rw [← ht] at this
      calc t * κ ≤ g * I.p i l / κ * κ := mul_le_mul_of_nonneg_right this hκ.le
        _ = g * I.p i l := div_mul_cancel₀ _ hκ.ne'
    obtain ⟨hκ', hz0, hzs, hzb, hzl, hzr⟩ :=
      Q_scale I b1 x ⟨hx0, hxb, hxs⟩ l y κ hκ hy0 hys hyb hyl hyr t ht0 ht1
    set z := cc I t x y with hz
    set η := t * κ / I.p i l with hη
    have hη0 : 0 < η := div_pos hκ' hpil
    have hpη : I.p i l * η = t * κ := by rw [hη]; field_simp
    have hw := hopt (tr I z i l l η 0) ⟨?_, ?_, ?_⟩
    · rw [revenue_tr] at hw; linarith
    · intro a c; unfold tr
      by_cases ha : a = i
      · subst ha
        by_cases hcl : c = l
        · subst hcl; simp; have := hz0 a c; linarith
        · simp [hcl]; exact hz0 a c
      · simp [ha]; exact hz0 a c
    · intro c
      have := spend_tr I z i l l η 0 c
      unfold spend at this; rw [this]
      by_cases hcl : c = l
      · subst hcl; simp; rw [hpη]; unfold spend at hzl; linarith
      · simp [hcl]; have := hzb c hcl; unfold spend at this; linarith
    · intro a; rw [rowsum_tr]
      have := hzs a; have := hxs a
      split_ifs with ha
      · subst ha; simp; linarith
      · simp; linarith
  -- restrict to the class
  rw [← htot]
  unfold customerClass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · rfl
  · have : ¬ 0 < x i k := fun hpos' => hk (InClass.step hlin hil hpos')
    linarith [hx0 i k]
