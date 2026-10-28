-- Prove2me | solution 1 for TailOptCaching.ETLRU.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:32:17.231104+00:00
-- url     : https://prove2.me/submissions/6cac66f0-e02d-41fd-b9ed-55ce55387df3

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

/-- per-conversation expected excess. -/
noncomputable def fE (P : Params) (i L X : ℕ) : ℝ≥0∞ :=
  ∑' Q : ℕ, P.Qlaw i Q * ENNReal.ofReal ((L : ℝ) + Q - X - P.ξ)

lemma fE_anti (P : Params) (i L : ℕ) {X X' : ℕ} (h : X ≤ X') : fE P i L X' ≤ fE P i L X := by
  unfold fE
  refine ENNReal.tsum_le_tsum fun Q => ?_
  gcongr

lemma tailProb_anti (P : Params) (i L : ℕ) {X X' : ℕ} (h : X ≤ X') :
    tailProb P i L X' ≤ tailProb P i L X := by
  unfold tailProb
  refine ENNReal.tsum_le_tsum fun Q => ?_
  have : (X : ℝ) ≤ X' := by exact_mod_cast h
  by_cases h' : (X' : ℝ) ≤ (L : ℝ) + Q - P.ξ
  · have h'' : (X : ℝ) ≤ (L : ℝ) + Q - P.ξ := le_trans this h'
    simp [h', h'']
  · simp [h']

lemma fE_pred (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (i L X : ℕ) (hX : 1 ≤ X) :
    fE P i L (X - 1) = fE P i L X + tailProb P i L X := by
  obtain ⟨m, hm⟩ := hξ
  unfold fE tailProb
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun Q => ?_
  have hc : (((X - 1 : ℕ)) : ℝ) = (X : ℝ) - 1 := by
    rw [Nat.cast_sub hX]; simp
  rw [hc, hm]
  by_cases h : (X : ℝ) ≤ (L : ℝ) + Q - m
  · rw [if_pos h]
    have h0 : (0 : ℝ) ≤ (L : ℝ) + Q - X - m := by linarith
    have : (L : ℝ) + Q - ((X : ℝ) - 1) - m = ((L : ℝ) + Q - X - m) + 1 := by ring
    rw [this, ENNReal.ofReal_add h0 zero_le_one]
    simp [mul_add]
  · rw [if_neg h, add_zero]
    have hlt : (L : ℝ) + Q - X - m < 0 := by linarith [not_le.mp h]
    have hint : ((L : ℤ) + Q - X - m : ℤ) < 0 := by
      have : (((L : ℤ) + Q - X - m : ℤ) : ℝ) < 0 := by push_cast; exact hlt
      exact_mod_cast this
    have hint' : ((L : ℤ) + Q - X - m : ℤ) + 1 ≤ 0 := by omega
    have hr : (((L : ℤ) + Q - X - m : ℤ) : ℝ) + 1 ≤ 0 := by exact_mod_cast hint'
    have e1 : (L : ℝ) + Q - ((X : ℝ) - 1) - m ≤ 0 := by push_cast at hr; linarith
    rw [ENNReal.ofReal_of_nonpos e1, ENNReal.ofReal_of_nonpos hlt.le]

/-- cost of cache vector `Y` against base state `w`. -/
noncomputable def costF (P : Params) (w : State) (Y : ℕ → ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range w.n, ENNReal.ofReal (w.lam i) * fE P i (w.L i) (Y i)

lemma nextTEL_eq (P : Params) (w : State) (Y : ℕ → ℕ) :
    nextTEL P { w with X := Y } = costF P w Y := rfl

lemma costF_anti (P : Params) (w : State) {Y Y' : ℕ → ℕ} (h : ∀ i < w.n, Y i ≤ Y' i) :
    costF P w Y' ≤ costF P w Y := by
  unfold costF
  refine Finset.sum_le_sum fun i hi => ?_
  gcongr
  exact fE_anti P i _ (h i (Finset.mem_range.mp hi))

lemma sum_shift (s : Finset ℕ) (j l : ℕ) (hj : j ∈ s) (hl : l ∈ s) (hjl : j ≠ l)
    (Y : ℕ → ℕ) (hY : 1 ≤ Y j) :
    ∑ i ∈ s, (if i = j then Y i - 1 else if i = l then Y i + 1 else Y i) = ∑ i ∈ s, Y i := by
  have hl' : l ∈ s.erase j := Finset.mem_erase.mpr ⟨hjl.symm, hl⟩
  rw [← Finset.add_sum_erase s _ hj, ← Finset.add_sum_erase s Y hj,
    ← Finset.add_sum_erase _ _ hl', ← Finset.add_sum_erase _ Y hl']
  have h1 : ∑ x ∈ (s.erase j).erase l, (if x = j then Y x - 1 else if x = l then Y x + 1 else Y x)
      = ∑ x ∈ (s.erase j).erase l, Y x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_erase.mp hx
    have h2 := Finset.mem_erase.mp this.2
    simp [this.1, h2.1]
  rw [h1]
  simp [hjl, hjl.symm]
  omega

lemma cost_shift (c : ℕ → ℕ → ℝ≥0∞) (s : Finset ℕ) (j l : ℕ) (hj : j ∈ s) (hl : l ∈ s)
    (hjl : j ≠ l) (Y : ℕ → ℕ) (mj ml : ℝ≥0∞)
    (h1 : c j (Y j - 1) = c j (Y j) + mj) (h2 : c l (Y l) = c l (Y l + 1) + ml) (hm : mj ≤ ml) :
    ∑ i ∈ s, c i (if i = j then Y i - 1 else if i = l then Y i + 1 else Y i)
      ≤ ∑ i ∈ s, c i (Y i) := by
  have hl' : l ∈ s.erase j := Finset.mem_erase.mpr ⟨hjl.symm, hl⟩
  rw [← Finset.add_sum_erase s _ hj, ← Finset.add_sum_erase s (fun i => c i (Y i)) hj,
    ← Finset.add_sum_erase _ _ hl', ← Finset.add_sum_erase _ (fun i => c i (Y i)) hl']
  have h1' : ∑ x ∈ (s.erase j).erase l,
      c x (if x = j then Y x - 1 else if x = l then Y x + 1 else Y x)
      = ∑ x ∈ (s.erase j).erase l, c x (Y x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_erase.mp hx
    have h2 := Finset.mem_erase.mp this.2
    simp [this.1, h2.1]
  rw [h1']
  simp only [if_true, hjl.symm, if_false]
  rw [h1, h2]
  calc c j (Y j) + mj + (c l (Y l + 1) + ∑ x ∈ (s.erase j).erase l, c x (Y x))
      ≤ c j (Y j) + ml + (c l (Y l + 1) + ∑ x ∈ (s.erase j).erase l, c x (Y x)) := by gcongr
    _ = _ := by ring

lemma greedy_pres (P : Params) (m : ℕ) : ∀ (w z : State), GreedyRun P m w z →
    z.n = w.n ∧ z.lam = w.lam ∧ z.L = w.L ∧ (∀ i, z.X i ≤ w.X i) ∧
      ∑ i ∈ Finset.range w.n, z.X i + m = ∑ i ∈ Finset.range w.n, w.X i := by
  induction m with
  | zero =>
    intro w z h
    simp only [GreedyRun] at h
    subst h
    simp
  | succ m ih =>
    intro w z h
    obtain ⟨z'', ⟨j, hj, hXj, _, rfl⟩, hrun⟩ := h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih _ _ hrun
    simp only [evict] at h1 h2 h3 h4 h5
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · intro i
      refine le_trans (h4 i) ?_
      by_cases hi : i = j
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · have hjs : j ∈ Finset.range w.n := Finset.mem_range.mpr hj
      have hs : ∑ i ∈ Finset.range w.n, Function.update w.X j (w.X j - 1) i + 1
          = ∑ i ∈ Finset.range w.n, w.X i := by
        rw [← Finset.add_sum_erase _ _ hjs, ← Finset.add_sum_erase _ w.X hjs]
        have : ∑ x ∈ (Finset.range w.n).erase j, Function.update w.X j (w.X j - 1) x
            = ∑ x ∈ (Finset.range w.n).erase j, w.X x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp [Function.update_of_ne (Finset.mem_erase.mp hx).1]
        rw [this]
        simp
        omega
      omega

lemma greedy_min (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (m : ℕ) :
    ∀ (w z : State), GreedyRun P m w z → ∀ Y : ℕ → ℕ, (∀ i < w.n, Y i ≤ w.X i) →
      ∑ i ∈ Finset.range w.n, Y i + m ≤ ∑ i ∈ Finset.range w.n, w.X i →
      nextTEL P z ≤ costF P w Y := by
  induction m with
  | zero =>
    intro w z h Y hY _
    simp only [GreedyRun] at h
    subst h
    have : nextTEL P z = costF P z z.X := rfl
    rw [this]
    exact costF_anti P z (fun i hi => hY i hi)
  | succ m ih =>
    intro w z h Y hY hsum
    obtain ⟨z'', ⟨j, hj, hXj, hmin, rfl⟩, hrun⟩ := h
    have hjs : j ∈ Finset.range w.n := Finset.mem_range.mpr hj
    obtain ⟨p1, p2, p3, p4, p5⟩ := greedy_pres P m _ _ hrun
    simp only [evict] at p1 p2 p3 p4 p5
    have key : ∃ Y' : ℕ → ℕ, (∀ i < w.n, Y' i ≤ Function.update w.X j (w.X j - 1) i) ∧
        ∑ i ∈ Finset.range w.n, Y' i + m ≤
          ∑ i ∈ Finset.range w.n, Function.update w.X j (w.X j - 1) i ∧
        costF P w Y' ≤ costF P w Y := by
      have hs : ∑ i ∈ Finset.range w.n, Function.update w.X j (w.X j - 1) i + 1
          = ∑ i ∈ Finset.range w.n, w.X i := by
        rw [← Finset.add_sum_erase _ _ hjs, ← Finset.add_sum_erase _ w.X hjs]
        have : ∑ x ∈ (Finset.range w.n).erase j, Function.update w.X j (w.X j - 1) x
            = ∑ x ∈ (Finset.range w.n).erase j, w.X x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp [Function.update_of_ne (Finset.mem_erase.mp hx).1]
        rw [this]
        simp
        omega
      by_cases hYj : Y j < w.X j
      · refine ⟨Y, ?_, ?_, le_refl _⟩
        · intro i hi
          by_cases hij : i = j
          · subst hij; simp; omega
          · simp [Function.update_of_ne hij]; exact hY i hi
        · omega
      · have hYj' : Y j = w.X j := le_antisymm (hY j hj) (not_lt.mp hYj)
        -- exists l with Y l < w.X l
        have hex : ∃ l ∈ Finset.range w.n, Y l < w.X l := by
          by_contra hcon
          push Not at hcon
          have : ∑ i ∈ Finset.range w.n, w.X i ≤ ∑ i ∈ Finset.range w.n, Y i :=
            Finset.sum_le_sum hcon
          omega
        obtain ⟨l, hls, hl⟩ := hex
        have hlj : l ≠ j := by rintro rfl; omega
        have hl1 : 1 ≤ w.X l := by omega
        have hY1 : 1 ≤ Y j := by omega
        set Y' : ℕ → ℕ := fun i => if i = j then Y i - 1 else if i = l then Y i + 1 else Y i
          with hY'
        refine ⟨Y', ?_, ?_, ?_⟩
        · intro i hi
          by_cases hij : i = j
          · subst hij; simp [hY']; omega
          · by_cases hil : i = l
            · subst hil; simp [hY', hij, Function.update_of_ne hij]; omega
            · simp [hY', hij, hil, Function.update_of_ne hij]; exact hY i hi
        · have := sum_shift (Finset.range w.n) j l hjs hls hlj.symm Y hY1
          simp only [hY']
          omega
        · -- cost
          have hscore := hmin l (Finset.mem_range.mp hls) hl1
          unfold costF
          refine cost_shift (fun i x => ENNReal.ofReal (w.lam i) * fE P i (w.L i) x)
            (Finset.range w.n) j l hjs hls hlj.symm Y
            (score P w j) (ENNReal.ofReal (w.lam l) * tailProb P l (w.L l) (Y l + 1)) ?_ ?_ ?_
          · rw [fE_pred P hξ j (w.L j) (Y j) hY1, mul_add, hYj']
            rfl
          · rw [← mul_add, ← fE_pred P hξ l (w.L l) (Y l + 1) (by omega)]
            simp
          · refine le_trans hscore ?_
            unfold score
            gcongr
            exact tailProb_anti P l _ (by omega)
    obtain ⟨Y', hY'1, hY'2, hY'3⟩ := key
    have := ih (evict w j) z hrun Y' hY'1 hY'2
    refine le_trans this ?_
    exact hY'3

end TailOptCaching.ETLRU

open TailOptCaching.ETLRU

theorem solution (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (s : State) (hs : WellFormed P s)
    (θ q a : ℕ) (hθ : θ ≤ s.n) (z : State)
    (hz : GreedyRun P
      ((∑ i ∈ Finset.range (nAfter s θ), Function.update s.X θ (s.L θ + q + a) i) - P.C)
      (post P s θ q a (Function.update s.X θ (s.L θ + q + a))) z) :
    Feasible P s θ q a z.X ∧
      ∀ Y, Feasible P s θ q a Y → nextTEL P z ≤ nextTEL P (post P s θ q a Y) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := greedy_pres P _ _ _ hz
  have hn : (post P s θ q a (Function.update s.X θ (s.L θ + q + a))).n = nAfter s θ := rfl
  have hX0 : (post P s θ q a (Function.update s.X θ (s.L θ + q + a))).X
      = Function.update s.X θ (s.L θ + q + a) := rfl
  rw [hn, hX0] at p5
  rw [hn] at p1
  have p4' : ∀ i, z.X i ≤ Function.update s.X θ (s.L θ + q + a) i := by
    intro i; have := p4 i; rwa [hX0] at this
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := p4' θ; simpa using this
  · intro i hi; have := p4' i; rwa [Function.update_of_ne hi] at this
  · omega
  · intro Y hY
    obtain ⟨hY1, hY2, hY3⟩ := hY
    have hle : ∀ i < (post P s θ q a (Function.update s.X θ (s.L θ + q + a))).n,
        Y i ≤ (post P s θ q a (Function.update s.X θ (s.L θ + q + a))).X i := by
      intro i _
      rw [hX0]
      by_cases hi : i = θ
      · subst hi; simpa using hY1
      · rw [Function.update_of_ne hi]; exact hY2 i hi
    have hsum : ∑ i ∈ Finset.range (nAfter s θ), Y i ≤
        ∑ i ∈ Finset.range (nAfter s θ), Function.update s.X θ (s.L θ + q + a) i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have := hle i (by rw [hn]; exact Finset.mem_range.mp hi)
      rwa [hX0] at this
    refine greedy_min P hξ _ _ z hz Y hle ?_
    rw [hn, hX0]
    omega
