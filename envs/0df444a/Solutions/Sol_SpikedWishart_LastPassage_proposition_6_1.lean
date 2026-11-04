-- Prove2me | solution 1 for SpikedWishart.LastPassage.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T21:18:10.046307+00:00
-- url     : https://prove2.me/submissions/3f9e7257-81e6-4a01-b88a-5de88eff745c

import Mathlib
import Definitions.Def_SpikedWishart_LastPassage_Model
import Definitions.Def_SpikedWishart_LastPassage_LPP
import Definitions.Def_SpikedWishart_Separated_Model
import Definitions.Def_SpikedWishart_Separated_GUE
import Definitions.Def_SpikedWishart_FixedDim_Model
import Definitions.Def_SpikedWishart_FixedDim_GUE
import Definitions.Def_SpikedWishart_FixedDim_Laguerre

set_option linter.all false

set_option maxHeartbeats 2000000

set_option autoImplicit false

-- ===== C1a.lean


open MeasureTheory

namespace B8RSK

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- single-coordinate shear: coordinate `p` becomes `s * x p + c x`. -/
noncomputable def shear (p : ι) (s : ℝ) (c : (ι → ℝ) → ℝ) (x : ι → ℝ) : ι → ℝ :=
  Function.update x p (s * x p + c x)

theorem measurable_shear (p : ι) (s : ℝ) {c : (ι → ℝ) → ℝ} (hc : Measurable c) :
    Measurable (shear p s c) := by
  unfold shear
  refine measurable_pi_lambda _ fun q => ?_
  by_cases h : q = p
  · subst h; simp only [Function.update_self]; exact ((measurable_pi_apply q).const_mul s).add hc
  · simp only [Function.update_of_ne h]; exact measurable_pi_apply q

theorem mp_affine (s c : ℝ) (hs : s = 1 ∨ s = -1) :
    MeasurePreserving (fun t : ℝ => s * t + c) volume volume := by
  rcases hs with rfl | rfl
  · simpa using measurePreserving_add_right volume c
  · have h1 := Measure.measurePreserving_neg (volume : Measure ℝ)
    have h2 := measurePreserving_add_right (volume : Measure ℝ) c
    convert h2.comp h1 using 1
    funext t; simp

theorem lintegral_shear (p : ι) (s : ℝ) (hs : s = 1 ∨ s = -1) {c : (ι → ℝ) → ℝ} (hc : Measurable c)
    (hcp : ∀ x t, c (Function.update x p t) = c x) (f : (ι → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f (shear p s c x) = ∫⁻ x, f x := by
  have hfs : Measurable (fun x => f (shear p s c x)) := hf.comp (measurable_shear p s hc)
  have huniv : (Finset.univ : Finset ι) = {p} ∪ Finset.univ.erase p := by
    ext q; by_cases h : q = p <;> simp [h]
  have hdisj : Disjoint ({p} : Finset ι) (Finset.univ.erase p) := by simp
  have key : (∫⋯∫⁻_{p}, (fun x => f (shear p s c x)) ∂(fun _ : ι => (volume : Measure ℝ))) =
      ∫⋯∫⁻_{p}, f ∂(fun _ : ι => (volume : Measure ℝ)) := by
    rw [lmarginal_singleton, lmarginal_singleton]
    funext x
    have : ∀ t : ℝ, shear p s c (Function.update x p t) = Function.update x p (s * t + c x) := by
      intro t; unfold shear; rw [hcp]; simp
    simp_rw [this]
    exact (mp_affine s (c x) hs).lintegral_comp (f := fun t => f (Function.update x p t))
      (hf.comp (measurable_update x))
  let x0 : ι → ℝ := 0
  rw [volume_pi, lintegral_eq_lmarginal_univ x0, lintegral_eq_lmarginal_univ x0, huniv,
    lmarginal_union' _ _ hfs hdisj, lmarginal_union' _ _ hf hdisj, key]

theorem measurePreserving_shear (p : ι) (s : ℝ) (hs : s = 1 ∨ s = -1) {c : (ι → ℝ) → ℝ}
    (hc : Measurable c) (hcp : ∀ x t, c (Function.update x p t) = c x) :
    MeasurePreserving (shear p s c) volume volume := by
  refine ⟨measurable_shear p s hc, ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_shear p s hc) hS, ← lintegral_indicator_one hS,
    ← lintegral_indicator_one (measurable_shear p s hc hS)]
  have := lintegral_shear p s hs hc hcp (S.indicator 1) (measurable_one.indicator hS)
  rw [← this]
  rfl

/-- simultaneous shear of the coordinates in `S`; each new value depends on its own old value and on
coordinates outside `S` only. -/
noncomputable def blockShear (S : Finset ι) (s : ι → ℝ) (c : ι → (ι → ℝ) → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun q => if q ∈ S then s q * x q + c q x else x q

theorem measurePreserving_blockShear (S : Finset ι) (s : ι → ℝ) (hs : ∀ q, s q = 1 ∨ s q = -1)
    (c : ι → (ι → ℝ) → ℝ) (hc : ∀ q, Measurable (c q))
    (hcS : ∀ q ∈ S, ∀ x y : ι → ℝ, (∀ r ∉ S, x r = y r) → c q x = c q y) :
    MeasurePreserving (blockShear S s c) volume volume := by
  induction S using Finset.induction_on with
  | empty =>
    have : blockShear (∅ : Finset ι) s c = id := by funext x q; simp [blockShear]
    rw [this]; exact MeasurePreserving.id _
  | @insert q S hq ih =>
    have ih' := ih (fun r hr x y hxy => hcS r (Finset.mem_insert_of_mem hr) x y
      (fun t ht => hxy t (fun h => ht (Finset.mem_insert_of_mem h))))
    have hcq : ∀ x t, c q (Function.update x q t) = c q x := by
      intro x t
      refine hcS q (Finset.mem_insert_self _ _) _ _ fun r hr => ?_
      have : r ≠ q := fun h => hr (h ▸ Finset.mem_insert_self _ _)
      simp [Function.update_of_ne this]
    have heq : blockShear (insert q S) s c = shear q (s q) (c q) ∘ blockShear S s c := by
      funext x r
      have hS : ∀ y, (∀ t ∉ insert q S, blockShear S s c y t = y t) := by
        intro y t ht
        have : t ∉ S := fun h => ht (Finset.mem_insert_of_mem h)
        simp [blockShear, this]
      have hcq' : c q (blockShear S s c x) = c q x :=
        hcS q (Finset.mem_insert_self _ _) _ _ (hS x)
      have hxq : blockShear S s c x q = x q := by simp [blockShear, hq]
      have hcr : ∀ r ∈ S, c r (blockShear S s c x) = c r x := by
        intro r hr; exact hcS r (Finset.mem_insert_of_mem hr) _ _ (hS x)
      simp only [Function.comp, shear]
      by_cases hrq : r = q
      · subst hrq; rw [Function.update_self, hxq, hcq']; simp [blockShear]
      · rw [Function.update_of_ne hrq]
        simp [blockShear, Finset.mem_insert, hrq]
    rw [heq]
    exact (measurePreserving_shear q (s q) (hs q) (hc q) hcq).comp ih'

end B8RSK
-- ===== C1b.lean


namespace B8RSK

/-! ℕ-indexed toggle RSK step and its cone invariant. -/

noncomputable def upv (w : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ := if a = 0 then 0 else w (a - 1) b
noncomputable def lfv (w : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ := if b = 0 then 0 else w a (b - 1)

/-- one RSK step at cell `(i, j)`: corner insertion plus toggles along the diagonal below-left. -/
noncomputable def stepN (i j : ℕ) (w : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun a b =>
  if a = i ∧ b = j then w a b + max (upv w a b) (lfv w a b)
  else if a < i ∧ a + j = b + i then
    max (upv w a b) (lfv w a b) + min (w (a + 1) b) (w a (b + 1)) - w a b
  else w a b

theorem stepN_same {i j : ℕ} (w : ℕ → ℕ → ℝ) {a b : ℕ} (h1 : ¬(a = i ∧ b = j))
    (h2 : ¬(a < i ∧ a + j = b + i)) : stepN i j w a b = w a b := by
  simp only [stepN, if_neg h1, if_neg h2]

theorem stepN_off {i j : ℕ} (w : ℕ → ℕ → ℝ) {a b : ℕ} (h : a + j ≠ b + i) :
    stepN i j w a b = w a b :=
  stepN_same w (fun h' => h (by omega)) (fun h' => h h'.2)

theorem stepN_corner (i j : ℕ) (w : ℕ → ℕ → ℝ) :
    stepN i j w i j = w i j + max (upv w i j) (lfv w i j) := by
  simp [stepN]

theorem stepN_tog {i j : ℕ} (w : ℕ → ℕ → ℝ) {a b : ℕ} (ha : a < i) (hd : a + j = b + i) :
    stepN i j w a b = max (upv w a b) (lfv w a b) + min (w (a + 1) b) (w a (b + 1)) - w a b := by
  have : ¬(a = i ∧ b = j) := fun h => by omega
  simp only [stepN, if_neg this, if_pos (And.intro ha hd)]

theorem upv_step_diag {i j : ℕ} (w : ℕ → ℕ → ℝ) {a b : ℕ} (hd : a + j = b + i) :
    upv (stepN i j w) a b = upv w a b := by
  unfold upv; split_ifs with h
  · rfl
  · exact stepN_off w (by omega)

theorem lfv_step_diag {i j : ℕ} (w : ℕ → ℕ → ℝ) {a b : ℕ} (hd : a + j = b + i) :
    lfv (stepN i j w) a b = lfv w a b := by
  unfold lfv; split_ifs with h
  · rfl
  · exact stepN_off w (by omega)

theorem upv_succ (w : ℕ → ℕ → ℝ) (a b : ℕ) : upv w (a + 1) b = w a b := by simp [upv]
theorem lfv_succ (w : ℕ → ℕ → ℝ) (a b : ℕ) : lfv w a (b + 1) = w a b := by simp [lfv]

/-- cells processed before cell `(i, j)` in row-major order (row length `M`). -/
def proc (M i j a b : ℕ) : Prop := (a < i ∧ b < M) ∨ (a = i ∧ b < j)

/-- cone invariant: processed part is a reverse plane partition, the rest is nonnegative. -/
def Good (N M i j : ℕ) (w : ℕ → ℕ → ℝ) : Prop :=
  (∀ a b, proc M i j a b → upv w a b ≤ w a b ∧ lfv w a b ≤ w a b) ∧
  (∀ a b, a < N → b < M → ¬ proc M i j a b → 0 ≤ w a b)

theorem good_step_mp {N M i j : ℕ} (hi : i < N) (hj : j < M) (w : ℕ → ℕ → ℝ)
    (hw : Good N M i j w) : Good N M i (j + 1) (stepN i j w) := by
  obtain ⟨hR, hP⟩ := hw
  refine ⟨fun a b hab => ?_, fun a b ha hb hnp => ?_⟩
  · have hb : b < M := by unfold proc at hab; omega
    by_cases hc : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hc
      have hd : a + b = b + a := Nat.add_comm _ _
      rw [stepN_corner, upv_step_diag w hd, lfv_step_diag w hd]
      have := hP a b hi hj (by unfold proc; omega)
      exact ⟨by linarith [le_max_left (upv w a b) (lfv w a b)],
        by linarith [le_max_right (upv w a b) (lfv w a b)]⟩
    by_cases ht : a < i ∧ a + j = b + i
    · rw [stepN_tog w ht.1 ht.2, upv_step_diag w ht.2, lfv_step_diag w ht.2]
      have hd : w a b ≤ w (a + 1) b := by
        have := (hR (a + 1) b (by unfold proc; omega)).1; rwa [upv_succ] at this
      have hr : w a b ≤ w a (b + 1) := by
        have := (hR a (b + 1) (by unfold proc; omega)).2; rwa [lfv_succ] at this
      have := le_min hd hr
      exact ⟨by linarith [le_max_left (upv w a b) (lfv w a b)],
        by linarith [le_max_right (upv w a b) (lfv w a b)]⟩
    have hab' : proc M i j a b := by unfold proc at hab ⊢; omega
    have hRab := hR a b hab'
    rw [stepN_same w hc ht]
    constructor
    · unfold upv
      split_ifs with h0
      · have := hRab.1; simp only [upv, if_pos h0] at this; exact this
      · by_cases hd' : a - 1 < i ∧ a - 1 + j = b + i
        · rw [stepN_tog w hd'.1 hd'.2]
          have e : a - 1 + 1 = a := by omega
          rw [e]
          have hm := hR (a - 1) b (by unfold proc; omega)
          have : max (upv w (a - 1) b) (lfv w (a - 1) b) ≤ w (a - 1) b := max_le hm.1 hm.2
          linarith [min_le_left (w a b) (w (a - 1) (b + 1))]
        · rw [stepN_same w (fun h => by unfold proc at hab; omega) hd']
          have := hRab.1; simp only [upv, if_neg h0] at this; exact this
    · unfold lfv
      split_ifs with h0
      · have := hRab.2; simp only [lfv, if_pos h0] at this; exact this
      · by_cases hd' : a < i ∧ a + j = b - 1 + i
        · rw [stepN_tog w hd'.1 hd'.2]
          have e : b - 1 + 1 = b := by omega
          rw [e]
          have hm := hR a (b - 1) (by unfold proc at hab ⊢; omega)
          have : max (upv w a (b - 1)) (lfv w a (b - 1)) ≤ w a (b - 1) := max_le hm.1 hm.2
          linarith [min_le_right (w (a + 1) (b - 1)) (w a b)]
        · rw [stepN_same w (fun h => by unfold proc at hab; omega) hd']
          have := hRab.2; simp only [lfv, if_neg h0] at this; exact this
  · unfold proc at hnp
    rw [stepN_same w (fun h => by omega) (fun h => by omega)]
    exact hP a b ha hb (by unfold proc; omega)

theorem good_step_mpr {N M i j : ℕ} (hi : i < N) (hj : j < M) (w : ℕ → ℕ → ℝ)
    (hw : Good N M i (j + 1) (stepN i j w)) : Good N M i j w := by
  obtain ⟨hR, hP⟩ := hw
  -- toggled cells end up below `min(down, right)`
  have htogU : ∀ a b, a < i → a + j = b + i →
      max (upv w a b) (lfv w a b) ≤ stepN i j w a b ∧
      stepN i j w a b ≤ min (w (a + 1) b) (w a (b + 1)) := by
    intro a b ha hd
    have h1 := hR a b (by unfold proc; omega)
    rw [upv_step_diag w hd, lfv_step_diag w hd] at h1
    have h2 := (hR (a + 1) b (by unfold proc; omega)).1
    rw [upv_succ, stepN_off w (show a + 1 + j ≠ b + i by omega)] at h2
    have h3 := (hR a (b + 1) (by unfold proc; omega)).2
    rw [lfv_succ, stepN_off w (show a + j ≠ b + 1 + i by omega)] at h3
    exact ⟨max_le h1.1 h1.2, le_min h2 h3⟩
  refine ⟨fun a b hab => ?_, fun a b ha hb hnp => ?_⟩
  · by_cases ht : a < i ∧ a + j = b + i
    · have e := stepN_tog w ht.1 ht.2
      obtain ⟨h1, h2⟩ := htogU a b ht.1 ht.2
      have hn := min_le_left (w (a + 1) b) (w a (b + 1))
      constructor <;> linarith [le_max_left (upv w a b) (lfv w a b), le_max_right (upv w a b) (lfv w a b)]
    have hc : ¬(a = i ∧ b = j) := by unfold proc at hab; omega
    have hRab := hR a b (by unfold proc at hab ⊢; omega)
    rw [stepN_same w hc ht] at hRab
    constructor
    · unfold upv
      split_ifs with h0
      · have := hRab.1; simp only [upv, if_pos h0] at this; exact this
      · by_cases hd' : a - 1 < i ∧ a - 1 + j = b + i
        · obtain ⟨h1, h2⟩ := htogU (a - 1) b hd'.1 hd'.2
          have e := stepN_tog w hd'.1 hd'.2
          have e2 : a - 1 + 1 = a := by omega
          rw [e2] at h2 e
          linarith [min_le_left (w a b) (w (a - 1) (b + 1))]
        · have := hRab.1
          simp only [upv, if_neg h0] at this
          rwa [stepN_same w (fun h => by unfold proc at hab; omega) hd'] at this
    · unfold lfv
      split_ifs with h0
      · have := hRab.2; simp only [lfv, if_pos h0] at this; exact this
      · by_cases hd' : a < i ∧ a + j = b - 1 + i
        · obtain ⟨h1, h2⟩ := htogU a (b - 1) hd'.1 hd'.2
          have e := stepN_tog w hd'.1 hd'.2
          have e2 : b - 1 + 1 = b := by omega
          rw [e2] at h2 e
          linarith [min_le_right (w (a + 1) (b - 1)) (w a b)]
        · have := hRab.2
          simp only [lfv, if_neg h0] at this
          rwa [stepN_same w (fun h => by unfold proc at hab; omega) hd'] at this
  · unfold proc at hnp
    by_cases hc : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hc
      have hd : a + b = b + a := Nat.add_comm _ _
      have := hR a b (by unfold proc; omega)
      rw [stepN_corner, upv_step_diag w hd, lfv_step_diag w hd] at this
      have := max_le this.1 this.2
      linarith
    · have := hP a b ha hb (by unfold proc; omega)
      rwa [stepN_same w hc (fun h => by omega)] at this

theorem good_step {N M i j : ℕ} (hi : i < N) (hj : j < M) (w : ℕ → ℕ → ℝ) :
    Good N M i (j + 1) (stepN i j w) ↔ Good N M i j w :=
  ⟨good_step_mpr hi hj w, good_step_mp hi hj w⟩


/-! corner invariant: the last processed cell of each diagonal carries the LPP recursion value. -/

theorem corner_step {M i j : ℕ} (hj : j < M) (X G : ℕ → ℕ → ℝ)
    (hG : ∀ a b, G a b = X a b + max (if a = 0 then 0 else G (a - 1) b) (if b = 0 then 0 else G a (b - 1)))
    (w : ℕ → ℕ → ℝ)
    (hC : ∀ a b, proc M i j a b → ¬ proc M i j (a + 1) (b + 1) → w a b = G a b)
    (hU : ∀ a b, ¬ proc M i j a b → w a b = X a b) :
    (∀ a b, proc M i (j + 1) a b → ¬ proc M i (j + 1) (a + 1) (b + 1) → stepN i j w a b = G a b) ∧
    (∀ a b, ¬ proc M i (j + 1) a b → stepN i j w a b = X a b) := by
  refine ⟨fun a b hab hs => ?_, fun a b hnp => ?_⟩
  · by_cases hc : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hc
      rw [stepN_corner, hU a b (by unfold proc; omega), hG a b]
      congr 2
      · unfold upv; split_ifs with h0
        · rfl
        · exact hC (a - 1) b (by unfold proc; omega) (by unfold proc; omega)
      · unfold lfv; split_ifs with h0
        · rfl
        · exact hC a (b - 1) (by unfold proc; omega) (by unfold proc; omega)
    · have ht : ¬(a < i ∧ a + j = b + i) := by unfold proc at hab hs; omega
      rw [stepN_same w hc ht]
      exact hC a b (by unfold proc at hab ⊢; omega) (by unfold proc at hs ⊢; omega)
  · unfold proc at hnp
    rw [stepN_same w (fun h => by omega) (fun h => by omega)]
    exact hU a b (by unfold proc; omega)

/-! diagonal sums. -/

/-- sum along the diagonal ending at `(a, b)` going down-left to the boundary. -/
noncomputable def dsum (w : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, b => w 0 b
  | a + 1, 0 => w (a + 1) 0
  | a + 1, b + 1 => w (a + 1) (b + 1) + dsum w a b

theorem dsum_zero_right (w : ℕ → ℕ → ℝ) (a : ℕ) : dsum w a 0 = w a 0 := by
  cases a <;> rfl

theorem dsum_succ_right (w : ℕ → ℕ → ℝ) (a b : ℕ) :
    dsum w a (b + 1) = w a (b + 1) + (if a = 0 then 0 else dsum w (a - 1) b) := by
  cases a with
  | zero => simp [dsum]
  | succ a => simp [dsum]

theorem dsum_succ_left (w : ℕ → ℕ → ℝ) (a b : ℕ) :
    dsum w (a + 1) b = w (a + 1) b + (if b = 0 then 0 else dsum w a (b - 1)) := by
  cases b with
  | zero => simp [dsum]
  | succ b => simp [dsum]

theorem dsum_congr_diag (w w' : ℕ → ℕ → ℝ) (d : ℕ → ℕ → Prop)
    (hd : ∀ a b, d (a + 1) (b + 1) → d a b) (hw : ∀ a b, d a b → w' a b = w a b) :
    ∀ a b, d a b → dsum w' a b = dsum w a b := by
  intro a
  induction a with
  | zero => intro b h; simp [dsum, hw 0 b h]
  | succ a ih =>
    intro b h
    cases b with
    | zero => simp [dsum, hw _ 0 h]
    | succ b => simp only [dsum]; rw [hw _ _ h, ih b (hd a b h)]

/-- processed cells of a cone state are nonnegative. -/
theorem proc_nonneg {M i j : ℕ} (hj : j ≤ M) (w : ℕ → ℕ → ℝ)
    (hR : ∀ a b, proc M i j a b → upv w a b ≤ w a b ∧ lfv w a b ≤ w a b) :
    ∀ a b, proc M i j a b → 0 ≤ w a b := by
  intro a
  induction a with
  | zero => intro b h; have := (hR 0 b h).1; simpa [upv] using this
  | succ a ih =>
    intro b h
    have h1 := (hR (a + 1) b h).1
    rw [upv_succ] at h1
    exact le_trans (ih b (by unfold proc at h ⊢; omega)) h1

/-- the toggled part of the diagonal: telescoping identity. -/
theorem dsum_tog {M i j : ℕ} (hj : j < M) (w : ℕ → ℕ → ℝ)
    (hnn : ∀ a b, proc M i j a b → 0 ≤ w a b) :
    ∀ a b, a < i → a + j = b + i →
      dsum (stepN i j w) a b = min (w (a + 1) b) (w a (b + 1)) +
        (if a = 0 then 0 else dsum w (a - 1) b) + (if b = 0 then 0 else dsum w a (b - 1)) - dsum w a b := by
  intro a
  induction a with
  | zero =>
    intro b ha hd
    simp only [dsum, stepN_tog w ha hd, upv, lfv, if_true]
    split_ifs with hb
    · simp
    · have := hnn 0 (b - 1) (by unfold proc; omega)
      rw [max_eq_right this]
      ring
  | succ a ih =>
    intro b ha hd
    cases b with
    | zero =>
      simp only [dsum_zero_right, stepN_tog w ha hd, upv_succ, lfv, if_true]
      have := hnn a 0 (by unfold proc; omega)
      rw [max_eq_left this, if_neg (Nat.succ_ne_zero a), Nat.add_sub_cancel]
      ring
    | succ b =>
      simp only [dsum]
      rw [ih b (by omega) (by omega), stepN_tog w ha hd, upv_succ, lfv_succ,
        dsum_succ_right, dsum_succ_left]
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      have := min_add_max (w (a + 1) b) (w a (b + 1))
      rw [max_comm] at this
      linarith

/-- prefix-sum invariant step. `P` is any array with the 2D prefix-sum recursion over `X`. -/
theorem pref_step {M i j : ℕ} (hj : j < M) (X P : ℕ → ℕ → ℝ)
    (hP : ∀ a b, P a b = X a b + (if a = 0 then 0 else P (a - 1) b) + (if b = 0 then 0 else P a (b - 1)) -
      (if a = 0 ∨ b = 0 then 0 else P (a - 1) (b - 1)))
    (w : ℕ → ℕ → ℝ) (hnn : ∀ a b, proc M i j a b → 0 ≤ w a b)
    (hD : ∀ a b, proc M i j a b → ¬ proc M i j (a + 1) (b + 1) → dsum w a b = P a b)
    (hU : ∀ a b, ¬ proc M i j a b → w a b = X a b) :
    ∀ a b, proc M i (j + 1) a b → ¬ proc M i (j + 1) (a + 1) (b + 1) → dsum (stepN i j w) a b = P a b := by
  intro a b hab hs
  by_cases hc : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hc
    have hXc := hU a b (by unfold proc; omega)
    rw [hP a b]
    cases a with
    | zero =>
      simp only [dsum, stepN_corner, upv, lfv, if_true, true_or, if_true, hXc]
      split_ifs with hb
      · simp
      · have := hnn 0 (b - 1) (by unfold proc; omega)
        rw [max_eq_right this, ← hD 0 (b - 1) (by unfold proc; omega) (by unfold proc; omega)]
        cases b with
        | zero => exact absurd rfl hb
        | succ b => simp [dsum]
    | succ a =>
      cases b with
      | zero =>
        simp only [dsum_zero_right, stepN_corner, upv_succ, lfv, if_true, or_true, hXc,
          Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        have := hnn a 0 (by unfold proc; omega)
        rw [max_eq_left this, ← hD a 0 (by unfold proc; omega) (by unfold proc; omega), dsum_zero_right]
        ring
      | succ b =>
        simp only [dsum]
        rw [dsum_tog hj w hnn a b (by omega) (by omega), stepN_corner, upv_succ, lfv_succ, hXc]
        simp only [Nat.succ_ne_zero, if_false, false_or, Nat.add_sub_cancel]
        have e1 := hD a (b + 1) (by unfold proc; omega) (by unfold proc; omega)
        have e2 := hD (a + 1) b (by unfold proc; omega) (by unfold proc; omega)
        have e3 := hD a b (by unfold proc; omega) (by unfold proc; omega)
        rw [dsum_succ_right] at e1
        rw [dsum_succ_left] at e2
        have := min_add_max (w (a + 1) b) (w a (b + 1))
        rw [max_comm] at this
        linarith
  · have hoff : ¬ (a + j = b + i) := by unfold proc at hab hs; omega
    rw [dsum_congr_diag w (stepN i j w) (fun a b => ¬ (a + j = b + i)) (fun a b h h' => h (by omega))
      (fun a b h => stepN_off w h) a b hoff]
    exact hD a b (by unfold proc at hab ⊢; omega) (by unfold proc at hs ⊢; omega)


/-! iteration over all cells in row-major order. -/

/-- apply the steps for cells `0, …, t-1` (cell `t` is `(t / M, t % M)`). -/
noncomputable def iterN (M : ℕ) : ℕ → (ℕ → ℕ → ℝ) → (ℕ → ℕ → ℝ)
  | 0, w => w
  | t + 1, w => stepN (t / M) (t % M) (iterN M t w)

theorem proc_succ_t {M : ℕ} (hM : 0 < M) (t : ℕ) :
    ∀ a b, proc M ((t + 1) / M) ((t + 1) % M) a b ↔ proc M (t / M) (t % M + 1) a b := by
  have ht := Nat.div_add_mod t M
  have hj := Nat.mod_lt t hM
  intro a b
  by_cases hlt : t % M + 1 < M
  · obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hM).2 (⟨by omega, hlt⟩ :
      t % M + 1 + M * (t / M) = t + 1 ∧ t % M + 1 < M)
    rw [h1, h2]
  · obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hM).2 (⟨by rw [Nat.mul_succ]; omega, hM⟩ :
      0 + M * (t / M + 1) = t + 1 ∧ 0 < M)
    rw [h1, h2]
    unfold proc; omega

theorem proc_zero_t {M : ℕ} (a b : ℕ) : ¬ proc M (0 / M) (0 % M) a b := by
  simp [proc]

theorem proc_full_t {N M : ℕ} (hM : 0 < M) (a b : ℕ) :
    proc M (N * M / M) (N * M % M) a b ↔ a < N ∧ b < M := by
  rw [Nat.mul_div_cancel _ hM, Nat.mul_mod_left]
  unfold proc; omega

theorem good_congr {N M i j i' j' : ℕ} (h : ∀ a b, proc M i j a b ↔ proc M i' j' a b) (w : ℕ → ℕ → ℝ) :
    Good N M i j w ↔ Good N M i' j' w := by
  unfold Good; simp only [h]

theorem good_iter {N M : ℕ} (hM : 0 < M) (X : ℕ → ℕ → ℝ) :
    ∀ t, t ≤ N * M → (Good N M (t / M) (t % M) (iterN M t X) ↔ Good N M 0 0 X) := by
  intro t
  induction t with
  | zero => intro _; rw [Nat.zero_div, Nat.zero_mod]; rfl
  | succ t ih =>
    intro ht
    have hi : t / M < N := (Nat.div_lt_iff_lt_mul hM).2 (by omega)
    rw [good_congr (proc_succ_t hM t), iterN, good_step hi (Nat.mod_lt t hM), ih (by omega)]

/-- cone ↔ reverse plane partition, at the ℕ level. -/
theorem cone_iff_rpp {N M : ℕ} (hM : 0 < M) (X : ℕ → ℕ → ℝ) :
    (∀ a b, a < N → b < M → upv (iterN M (N * M) X) a b ≤ iterN M (N * M) X a b ∧
        lfv (iterN M (N * M) X) a b ≤ iterN M (N * M) X a b) ↔
      (∀ a b, a < N → b < M → 0 ≤ X a b) := by
  have h := good_iter (N := N) hM X (N * M) le_rfl
  unfold Good at h
  simp only [proc_full_t hM] at h
  have h0 : ∀ a b, ¬ proc M 0 0 a b := by simp [proc]
  constructor
  · intro hR
    have := (h.1 ⟨fun a b hab => hR a b hab.1 hab.2, fun a b ha hb hn => absurd ⟨ha, hb⟩ hn⟩).2
    exact fun a b ha hb => this a b ha hb (h0 a b)
  · intro hX
    have := (h.2 ⟨fun a b hf => absurd hf (h0 a b), fun a b ha hb _ => hX a b ha hb⟩).1
    exact fun a b ha hb => this a b ⟨ha, hb⟩

/-- on the cone: corner = LPP recursion value, diagonal sums = prefix sums. -/
theorem iter_cone {N M : ℕ} (hM : 0 < M) (X G P : ℕ → ℕ → ℝ)
    (hG : ∀ a b, G a b = X a b + max (if a = 0 then 0 else G (a - 1) b) (if b = 0 then 0 else G a (b - 1)))
    (hP : ∀ a b, P a b = X a b + (if a = 0 then 0 else P (a - 1) b) + (if b = 0 then 0 else P a (b - 1)) -
      (if a = 0 ∨ b = 0 then 0 else P (a - 1) (b - 1)))
    (hX : ∀ a b, a < N → b < M → 0 ≤ X a b) :
    ∀ t, t ≤ N * M →
      (∀ a b, proc M (t / M) (t % M) a b → ¬ proc M (t / M) (t % M) (a + 1) (b + 1) →
        iterN M t X a b = G a b) ∧
      (∀ a b, ¬ proc M (t / M) (t % M) a b → iterN M t X a b = X a b) ∧
      (∀ a b, proc M (t / M) (t % M) a b → ¬ proc M (t / M) (t % M) (a + 1) (b + 1) →
        dsum (iterN M t X) a b = P a b) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun a b h => absurd h (proc_zero_t a b), fun a b _ => rfl,
      fun a b h => absurd h (proc_zero_t a b)⟩
  | succ t ih =>
    intro ht
    obtain ⟨hC, hU, hD⟩ := ih (by omega)
    have hj := Nat.mod_lt t hM
    have hgood : Good N M (t / M) (t % M) (iterN M t X) :=
      (good_iter hM X t (by omega)).2 ⟨fun a b h => by simp [proc] at h, fun a b ha hb _ => hX a b ha hb⟩
    have hnn := proc_nonneg hj.le _ hgood.1
    have hc := corner_step hj X G hG _ hC hU
    have hd := pref_step hj X P hP _ hnn hD hU
    simp only [iterN, proc_succ_t hM t]
    exact ⟨hc.1, hc.2, hd⟩

end B8RSK
-- ===== C1d.lean


open MeasureTheory

namespace B8RSK

/-- extension of an array by zero to `ℕ × ℕ`. -/
noncomputable def ext {N M : ℕ} (X : Fin N → Fin M → ℝ) (a b : ℕ) : ℝ :=
  if h : a < N ∧ b < M then X ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

theorem ext_nonneg {N M : ℕ} {X : Fin N → Fin M → ℝ} (hX : ∀ i j, 0 ≤ X i j) (a b : ℕ) :
    0 ≤ ext X a b := by
  unfold ext; split_ifs <;> simp [hX]

/-- last passage recursion array (missing neighbours count as `0`). -/
noncomputable def Gn (Xn : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  Xn a b + max (if a = 0 then 0 else Gn Xn (a - 1) b) (if b = 0 then 0 else Gn Xn a (b - 1))
termination_by a + b
decreasing_by all_goals omega

theorem Gn_eq (Xn : ℕ → ℕ → ℝ) (a b : ℕ) :
    Gn Xn a b = Xn a b + max (if a = 0 then 0 else Gn Xn (a - 1) b)
      (if b = 0 then 0 else Gn Xn a (b - 1)) := by
  rw [Gn]

theorem Gn_nonneg {Xn : ℕ → ℕ → ℝ} (hX : ∀ a b, 0 ≤ Xn a b) : ∀ n a b, a + b = n → 0 ≤ Gn Xn a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab
    rw [Gn_eq]
    have h1 : 0 ≤ (if a = 0 then (0 : ℝ) else Gn Xn (a - 1) b) := by
      split_ifs with h
      · exact le_rfl
      · exact ih (a - 1 + b) (by omega) _ _ rfl
    exact add_nonneg (hX a b) (le_trans h1 (le_max_left _ _))

theorem Gn_ge_up (Xn : ℕ → ℕ → ℝ) (a b : ℕ) : Xn (a + 1) b + Gn Xn a b ≤ Gn Xn (a + 1) b := by
  rw [Gn_eq Xn (a + 1) b]
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  exact add_le_add le_rfl (le_max_left _ _)

theorem Gn_ge_left (Xn : ℕ → ℕ → ℝ) (a b : ℕ) : Xn a (b + 1) + Gn Xn a b ≤ Gn Xn a (b + 1) := by
  rw [Gn_eq Xn a (b + 1)]
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  exact add_le_add le_rfl (le_max_right _ _)

/-- greedy predecessor. -/
noncomputable def pred (Xn : ℕ → ℕ → ℝ) (z : ℕ × ℕ) : ℕ × ℕ :=
  if z.1 = 0 then (0, z.2 - 1) else if z.2 = 0 then (z.1 - 1, 0)
  else if Gn Xn z.1 (z.2 - 1) ≤ Gn Xn (z.1 - 1) z.2 then (z.1 - 1, z.2) else (z.1, z.2 - 1)

theorem pred_sum (Xn : ℕ → ℕ → ℝ) (z : ℕ × ℕ) (hz : 1 ≤ z.1 + z.2) :
    (pred Xn z).1 + (pred Xn z).2 + 1 = z.1 + z.2 := by
  unfold pred; split_ifs <;> simp <;> omega

theorem pred_le (Xn : ℕ → ℕ → ℝ) (z : ℕ × ℕ) : (pred Xn z).1 ≤ z.1 ∧ (pred Xn z).2 ≤ z.2 := by
  unfold pred; split_ifs <;> simp <;> omega

/-- one greedy step back: the predecessor is one step down or one step left. -/
theorem pred_step (Xn : ℕ → ℕ → ℝ) (z : ℕ × ℕ) (hz : 1 ≤ z.1 + z.2) :
    (z.1 = (pred Xn z).1 + 1 ∧ z.2 = (pred Xn z).2) ∨ (z.1 = (pred Xn z).1 ∧ z.2 = (pred Xn z).2 + 1) := by
  unfold pred; split_ifs <;> simp <;> omega

theorem Gn_pred {Xn : ℕ → ℕ → ℝ} (hX : ∀ a b, 0 ≤ Xn a b) (z : ℕ × ℕ) (hz : 1 ≤ z.1 + z.2) :
    Gn Xn z.1 z.2 = Xn z.1 z.2 + Gn Xn (pred Xn z).1 (pred Xn z).2 := by
  have hnn : ∀ a b, 0 ≤ Gn Xn a b := fun a b => Gn_nonneg hX (a + b) a b rfl
  rw [Gn_eq]
  congr 1
  unfold pred
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by omega
    simp only [h1, h2, if_true, if_false]
    exact max_eq_right (hnn _ _)
  · by_cases h2 : z.2 = 0
    · simp only [h1, h2, if_true, if_false]
      exact max_eq_left (hnn _ _)
    · simp only [h1, h2, if_false]
      split_ifs with h3
      · exact max_eq_left h3
      · exact max_eq_right (le_of_lt (not_le.mp h3))

theorem iter_sum (Xn : ℕ → ℕ → ℝ) (z : ℕ × ℕ) :
    ∀ m, m ≤ z.1 + z.2 → ((pred Xn)^[m] z).1 + ((pred Xn)^[m] z).2 + m = z.1 + z.2 := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have := ih (by omega)
    rw [Function.iterate_succ_apply']
    have := pred_sum Xn ((pred Xn)^[m] z) (by omega)
    omega

theorem iter_le (Xn : ℕ → ℕ → ℝ) (z : ℕ × ℕ) :
    ∀ m, ((pred Xn)^[m] z).1 ≤ z.1 ∧ ((pred Xn)^[m] z).2 ≤ z.2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have := pred_le Xn ((pred Xn)^[m] z)
    omega

/-- telescoping along the greedy path. -/
theorem Gn_telescope {Xn : ℕ → ℕ → ℝ} (hX : ∀ a b, 0 ≤ Xn a b) (z : ℕ × ℕ) :
    ∀ j, j ≤ z.1 + z.2 → Gn Xn z.1 z.2 =
      (∑ m ∈ Finset.range j, Xn ((pred Xn)^[m] z).1 ((pred Xn)^[m] z).2) +
        Gn Xn ((pred Xn)^[j] z).1 ((pred Xn)^[j] z).2 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [ih (by omega), Finset.sum_range_succ, Function.iterate_succ_apply', add_assoc]
    congr 1
    have := iter_sum Xn z j (by omega)
    exact Gn_pred hX _ (by omega)

open SpikedWishart.LastPassage in
theorem path_sum_le {N M : ℕ} (X : Fin N → Fin M → ℝ) (a : Fin N) (b : Fin M)
    (p : UpRightPath a b) : ∑ k, X (p.1 k).1 (p.1 k).2 ≤ Gn (ext X) a b := by
  obtain ⟨p, h0a, h0b, hlast, hstep⟩ := p
  let q : ℕ → ℕ × ℕ := fun m =>
    if h : m < (a : ℕ) + b + 1 then (((p ⟨m, h⟩).1 : ℕ), ((p ⟨m, h⟩).2 : ℕ)) else (0, 0)
  let f : ℕ → ℝ := fun m => ext X (q m).1 (q m).2
  have hf : ∀ k : Fin ((a : ℕ) + b + 1), f k = X (p k).1 (p k).2 := by
    intro k
    have hq : q k = (((p k).1 : ℕ), ((p k).2 : ℕ)) := by simp only [q, dif_pos k.2, Fin.eta]
    simp only [f, hq, ext, dif_pos (And.intro (p k).1.2 (p k).2.2)]
  have hsum : ∑ k, X (p k).1 (p k).2 = ∑ m ∈ Finset.range ((a : ℕ) + b + 1), f m := by
    rw [← Fin.sum_univ_eq_sum_range]; exact Finset.sum_congr rfl fun k _ => (hf k).symm
  have claim : ∀ m, m ≤ (a : ℕ) + b → ∑ j ∈ Finset.range (m + 1), f j ≤ Gn (ext X) (q m).1 (q m).2 := by
    intro m
    induction m with
    | zero =>
      intro _
      have hq0 : q 0 = (0, 0) := by
        simp only [q, dif_pos (Nat.succ_pos _)]
        show (((p 0).1 : ℕ), ((p 0).2 : ℕ)) = (0, 0)
        rw [h0a, h0b]
      rw [Finset.sum_range_one, hq0, Gn_eq]
      simp [f, hq0]
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have hk := hstep ⟨m, by omega⟩
      have hqm : q m = (((p ⟨m, by omega⟩).1 : ℕ), ((p ⟨m, by omega⟩).2 : ℕ)) := by
        simp only [q, dif_pos (show m < (a : ℕ) + b + 1 by omega)]
      have hqm1 : q (m + 1) = (((p ⟨m + 1, by omega⟩).1 : ℕ), ((p ⟨m + 1, by omega⟩).2 : ℕ)) := by
        simp only [q, dif_pos (show m + 1 < (a : ℕ) + b + 1 by omega)]
      have hs : (p (⟨m, by omega⟩ : Fin ((a : ℕ) + b)).succ) = p ⟨m + 1, by omega⟩ := rfl
      have hc : (p (⟨m, by omega⟩ : Fin ((a : ℕ) + b)).castSucc) = p ⟨m, by omega⟩ := rfl
      rw [hs, hc] at hk
      rcases hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have e2' := congrArg Fin.val e2
        have : q (m + 1) = ((q m).1 + 1, (q m).2) := by rw [hqm, hqm1]; simp [e1, e2']
        rw [this]
        calc _ ≤ Gn (ext X) (q m).1 (q m).2 + f (m + 1) := add_le_add h1 le_rfl
          _ = ext X ((q m).1 + 1) (q m).2 + Gn (ext X) (q m).1 (q m).2 := by
            rw [add_comm]; simp only [f, this]
          _ ≤ _ := Gn_ge_up _ _ _
      · have e1' := congrArg Fin.val e1
        have : q (m + 1) = ((q m).1, (q m).2 + 1) := by rw [hqm, hqm1]; simp [e1', e2]
        rw [this]
        calc _ ≤ Gn (ext X) (q m).1 (q m).2 + f (m + 1) := add_le_add h1 le_rfl
          _ = ext X (q m).1 ((q m).2 + 1) + Gn (ext X) (q m).1 (q m).2 := by
            rw [add_comm]; simp only [f, this]
          _ ≤ _ := Gn_ge_left _ _ _
  have hqn : q ((a : ℕ) + b) = ((a : ℕ), (b : ℕ)) := by
    simp only [q, dif_pos (show (a : ℕ) + b < (a : ℕ) + b + 1 by omega)]
    have : (⟨(a : ℕ) + b, by omega⟩ : Fin ((a : ℕ) + b + 1)) = Fin.last _ := rfl
    rw [this, hlast]
  rw [hsum]
  have := claim ((a : ℕ) + b) le_rfl
  rwa [hqn] at this

/-- the greedy path to `(a, b)` (reads `back (a + b - k)`). -/
noncomputable def greedy {N M : ℕ} (X : Fin N → Fin M → ℝ) (a : Fin N) (b : Fin M) :
    SpikedWishart.LastPassage.UpRightPath a b := by
  refine ⟨fun k => (⟨((pred (ext X))^[(a : ℕ) + b - k] ((a : ℕ), (b : ℕ))).1, ?_⟩,
    ⟨((pred (ext X))^[(a : ℕ) + b - k] ((a : ℕ), (b : ℕ))).2, ?_⟩), ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (iter_le (ext X) _ _).1 a.2
  · exact lt_of_le_of_lt (iter_le (ext X) _ _).2 b.2
  · have := iter_sum (ext X) ((a : ℕ), (b : ℕ)) ((a : ℕ) + b) le_rfl
    simp only [Fin.val_zero, Nat.sub_zero]; omega
  · have := iter_sum (ext X) ((a : ℕ), (b : ℕ)) ((a : ℕ) + b) le_rfl
    simp only [Fin.val_zero, Nat.sub_zero]; omega
  · simp only [Fin.val_last, Nat.sub_self, Function.iterate_zero, id]
  · intro k
    have hk := k.2
    have e : (a : ℕ) + b - (k.castSucc : ℕ) = ((a : ℕ) + b - ((k : ℕ) + 1)) + 1 := by
      simp only [Fin.val_castSucc]; omega
    have e2 : (a : ℕ) + b - (k.succ : ℕ) = (a : ℕ) + b - ((k : ℕ) + 1) := by simp only [Fin.val_succ]
    have hz := iter_sum (ext X) ((a : ℕ), (b : ℕ)) ((a : ℕ) + b - ((k : ℕ) + 1)) (by omega)
    have hst := pred_step (ext X) ((pred (ext X))^[(a : ℕ) + b - ((k : ℕ) + 1)] ((a : ℕ), (b : ℕ)))
      (by simp only at hz; omega)
    simp only [e, e2, Function.iterate_succ_apply', Fin.ext_iff]
    exact hst

theorem greedy_sum {N M : ℕ} {X : Fin N → Fin M → ℝ} (hX : ∀ i j, 0 ≤ X i j) (a : Fin N) (b : Fin M) :
    ∑ k, X ((greedy X a b).1 k).1 ((greedy X a b).1 k).2 = Gn (ext X) a b := by
  set z : ℕ × ℕ := ((a : ℕ), (b : ℕ)) with hzdef
  set back : ℕ → ℕ × ℕ := fun m => (pred (ext X))^[m] z with hback
  have hterm : ∀ k : Fin ((a : ℕ) + b + 1), X ((greedy X a b).1 k).1 ((greedy X a b).1 k).2 =
      ext X (back ((a : ℕ) + b - k)).1 (back ((a : ℕ) + b - k)).2 := by
    intro k
    simp only [ext, back]
    rw [dif_pos (And.intro (lt_of_le_of_lt (iter_le (ext X) _ _).1 a.2)
      (lt_of_le_of_lt (iter_le (ext X) _ _).2 b.2))]
    rfl
  rw [Finset.sum_congr rfl fun k _ => hterm k,
    Fin.sum_univ_eq_sum_range (fun k => ext X (back ((a : ℕ) + b - k)).1 (back ((a : ℕ) + b - k)).2),
    ← Finset.sum_range_reflect, Finset.sum_range_succ]
  have hX' : ∀ u v, 0 ≤ ext X u v := ext_nonneg hX
  have tel := Gn_telescope hX' z ((a : ℕ) + b) le_rfl
  have h0 := iter_sum (ext X) z ((a : ℕ) + b) le_rfl
  have hb0 : back ((a : ℕ) + b) = (0, 0) := by
    simp only [back]; ext <;> simp only [hzdef] at h0 ⊢ <;> omega
  have hG0 : Gn (ext X) (back ((a : ℕ) + b)).1 (back ((a : ℕ) + b)).2 =
      ext X (back ((a : ℕ) + b)).1 (back ((a : ℕ) + b)).2 := by
    rw [hb0, Gn_eq]; simp
  have hrefl : ∑ j ∈ Finset.range ((a : ℕ) + b), ext X (back ((a : ℕ) + b - ((a : ℕ) + b + 1 - 1 - j))).1
      (back ((a : ℕ) + b - ((a : ℕ) + b + 1 - 1 - j))).2 =
      ∑ j ∈ Finset.range ((a : ℕ) + b), ext X (back j).1 (back j).2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have : (a : ℕ) + b - ((a : ℕ) + b + 1 - 1 - j) = j := by
      have := Finset.mem_range.mp hj; omega
    rw [this]
  have hlast : (a : ℕ) + b - ((a : ℕ) + b + 1 - 1 - ((a : ℕ) + b)) = (a : ℕ) + b := by omega
  rw [hrefl, hlast, ← hG0]
  simp only [back, hzdef] at tel ⊢
  exact tel.symm

open SpikedWishart.LastPassage in
theorem lpp_eq_Gn {N M : ℕ} {X : Fin N → Fin M → ℝ} (hX : ∀ i j, 0 ≤ X i j) (a : Fin N) (b : Fin M) :
    lpp X a b = Gn (ext X) a b := by
  haveI : Nonempty (UpRightPath a b) := ⟨greedy X a b⟩
  have hbdd : BddAbove (Set.range fun p : UpRightPath a b => ∑ k, X (p.1 k).1 (p.1 k).2) :=
    (Set.finite_range _).bddAbove
  unfold lpp
  refine le_antisymm (ciSup_le fun p => path_sum_le X a b p) ?_
  rw [← greedy_sum hX a b]
  exact le_ciSup hbdd (greedy X a b)

end B8RSK
-- ===== C1e_body.lean

namespace B8RSK

open MeasureTheory

section Bridge

variable {N M : ℕ}

/-- read a finite array at natural indices (zero outside). -/
noncomputable def rd (z : Fin N × Fin M → ℝ) (a b : ℕ) : ℝ :=
  if h : a < N ∧ b < M then z (⟨a, h.1⟩, ⟨b, h.2⟩) else 0

theorem rd_fin (z : Fin N × Fin M → ℝ) (q : Fin N × Fin M) : rd z q.1 q.2 = z q := by
  simp [rd, q.1.isLt, q.2.isLt]

theorem rd_out (z : Fin N × Fin M → ℝ) {a b : ℕ} (h : ¬(a < N ∧ b < M)) : rd z a b = 0 := by
  simp only [rd, dif_neg h]

noncomputable def stepF (i j : ℕ) (z : Fin N × Fin M → ℝ) : Fin N × Fin M → ℝ :=
  fun q => stepN i j (rd z) q.1 q.2

theorem rd_stepF {i j : ℕ} (hi : i < N) (hj : j < M) (z : Fin N × Fin M → ℝ) :
    rd (stepF i j z) = stepN i j (rd z) := by
  funext a b
  by_cases h : a < N ∧ b < M
  · simp only [rd, dif_pos h, stepF]
  · rw [rd_out _ h, stepN_same _ (fun h' => h (by omega)) (fun h' => h (by omega)), rd_out _ h]

noncomputable def iterF (M : ℕ) : ℕ → (Fin N × Fin M → ℝ) → (Fin N × Fin M → ℝ)
  | 0, z => z
  | t + 1, z => stepF (t / M) (t % M) (iterF M t z)

theorem rd_iterF (hM : 0 < M) (z : Fin N × Fin M → ℝ) :
    ∀ t, t ≤ N * M → rd (iterF M t z) = iterN M t (rd z) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hi : t / M < N := (Nat.div_lt_iff_lt_mul hM).2 (by omega)
    simp only [iterF, iterN]
    rw [rd_stepF hi (Nat.mod_lt t hM), ih (by omega)]

/-- the diagonal of cell `(i, j)` (cells changed by the step). -/
noncomputable def diagS (i j : ℕ) : Finset (Fin N × Fin M) :=
  Finset.univ.filter (fun q => (q.1 : ℕ) ≤ i ∧ (q.1 : ℕ) + j = q.2 + i)

noncomputable def sgn (i j : ℕ) (q : Fin N × Fin M) : ℝ :=
  if (q.1 : ℕ) = i ∧ (q.2 : ℕ) = j then 1 else -1

noncomputable def cst (i j : ℕ) (q : Fin N × Fin M) (z : Fin N × Fin M → ℝ) : ℝ :=
  if (q.1 : ℕ) = i ∧ (q.2 : ℕ) = j then max (upv (rd z) q.1 q.2) (lfv (rd z) q.1 q.2)
  else max (upv (rd z) q.1 q.2) (lfv (rd z) q.1 q.2) + min (rd z (q.1 + 1) q.2) (rd z q.1 (q.2 + 1))

theorem stepF_eq (i j : ℕ) : (stepF i j : (Fin N × Fin M → ℝ) → _) = B8RSK.blockShear (diagS i j) (sgn i j) (cst i j) := by
  funext z q
  unfold blockShear stepF
  by_cases hq : q ∈ diagS i j
  · rw [if_pos hq]
    simp only [diagS, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    by_cases hc : (q.1 : ℕ) = i ∧ (q.2 : ℕ) = j
    · simp only [stepN, sgn, cst, if_pos hc, rd_fin]; ring
    · have hlt : (q.1 : ℕ) < i := by omega
      simp only [stepN, sgn, cst, if_neg hc, if_pos (And.intro hlt hq.2), rd_fin]; ring
  · rw [if_neg hq]
    simp only [diagS, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [stepN_same _ (fun h => hq (by omega)) (fun h => hq (by omega)), rd_fin]

theorem measurable_rd (a b : ℕ) : Measurable fun z : Fin N × Fin M → ℝ => rd z a b := by
  unfold rd
  by_cases h : a < N ∧ b < M
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

theorem measurable_upv (a b : ℕ) : Measurable fun z : Fin N × Fin M → ℝ => upv (rd z) a b := by
  unfold upv
  by_cases h : a = 0
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact measurable_rd _ _

theorem measurable_lfv (a b : ℕ) : Measurable fun z : Fin N × Fin M → ℝ => lfv (rd z) a b := by
  unfold lfv
  by_cases h : b = 0
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact measurable_rd _ _

theorem measurable_cst (i j : ℕ) (q : Fin N × Fin M) : Measurable (cst i j q) := by
  unfold cst
  by_cases h : (q.1 : ℕ) = i ∧ (q.2 : ℕ) = j
  · simp only [if_pos h]; exact (measurable_upv _ _).max (measurable_lfv _ _)
  · simp only [if_neg h]
    exact ((measurable_upv _ _).max (measurable_lfv _ _)).add
      ((measurable_rd _ _).min (measurable_rd _ _))

theorem rd_agree {i j : ℕ} {z y : Fin N × Fin M → ℝ} (hzy : ∀ r ∉ diagS i j, z r = y r)
    {a b : ℕ} (h : a + j ≠ b + i) : rd z a b = rd y a b := by
  unfold rd
  split_ifs with hab
  · apply hzy
    simp only [diagS, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · rfl

theorem cst_agree (i j : ℕ) (q : Fin N × Fin M) (hq : q ∈ diagS i j) (z y : Fin N × Fin M → ℝ)
    (hzy : ∀ r ∉ diagS i j, z r = y r) : cst i j q z = cst i j q y := by
  simp only [diagS, Finset.mem_filter, Finset.mem_univ, true_and] at hq
  have hu : upv (rd z) q.1 q.2 = upv (rd y) q.1 q.2 := by
    unfold upv; split_ifs with h0
    · rfl
    · exact rd_agree hzy (by omega)
  have hl : lfv (rd z) q.1 q.2 = lfv (rd y) q.1 q.2 := by
    unfold lfv; split_ifs with h0
    · rfl
    · exact rd_agree hzy (by omega)
  unfold cst
  rw [hu, hl, rd_agree hzy (show (q.1 : ℕ) + 1 + j ≠ q.2 + i by omega),
    rd_agree hzy (show (q.1 : ℕ) + j ≠ q.2 + 1 + i by omega)]

theorem measurePreserving_stepF (i j : ℕ) :
    MeasurePreserving (stepF i j : (Fin N × Fin M → ℝ) → _) volume volume := by
  rw [stepF_eq]
  refine measurePreserving_blockShear _ _ (fun q => ?_) _ (measurable_cst i j) (cst_agree i j)
  unfold sgn; split_ifs <;> simp

theorem measurePreserving_iterF (t : ℕ) :
    MeasurePreserving (iterF M t : (Fin N × Fin M → ℝ) → _) volume volume := by
  induction t with
  | zero => exact MeasurePreserving.id _
  | succ t ih => exact (measurePreserving_stepF _ _).comp ih

end Bridge

end B8RSK
-- ===== C1f_body.lean

namespace B8RSK

open MeasureTheory

section Density

/-- Tonelli for a product of one-variable functions on `ι → ℝ`. -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ENNReal)
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : ι → ℝ, ∏ i, g i (x i) = ∏ i, ∫⁻ t, g i t := by
  have hF : Measurable fun x : ι → ℝ => ∏ i, g i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  have key : ∀ s : Finset ι, ∀ x : ι → ℝ,
      (∫⋯∫⁻_s, (fun x : ι → ℝ => ∏ i, g i (x i)) ∂(fun _ => (volume : Measure ℝ))) x =
        ∏ i, (if i ∈ s then ∫⁻ t, g i t else g i (x i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp [lmarginal_empty]
    | @insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hF hi]
      simp_rw [ih]
      have h1 : ∀ t : ℝ, (∏ k, (if k ∈ s then ∫⁻ t, g k t else g k (Function.update x i t k))) =
          g i t * ∏ k ∈ Finset.univ.erase i, (if k ∈ s then ∫⁻ t, g k t else g k (x k)) := by
        intro t
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [if_neg hi, Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp_rw [h1]
      rw [lintegral_mul_const _ (hg i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [Finset.mem_insert, true_or, if_true]
      congr 1
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [Finset.ne_of_mem_erase hk]
  rw [volume_pi, lintegral_eq_lmarginal_univ (0 : ι → ℝ), key]
  simp

theorem indicator_pi_prod {ι : Type*} [Fintype ι] (f : ι → ℝ → ENNReal) (s : ι → Set ℝ) (x : ι → ℝ) :
    (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x = ∏ i, (s i).indicator (f i) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

/-- a product of absolutely continuous measures is absolutely continuous with the product density. -/
theorem pi_withDensity {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ → ENNReal)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i))] :
    Measure.pi (fun i => (volume : Measure ℝ).withDensity (f i)) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [indicator_pi_prod]
  rw [lintegral_pi_prod _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

/-- currying is measure preserving for product measures. -/
theorem measurePreserving_curry_pi (N M : ℕ) (μ : Fin N → Fin M → Measure ℝ)
    [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin M) ℝ)
      (Measure.pi fun q : Fin N × Fin M => μ q.1 q.2) (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  have h : (Measure.pi fun q : Fin N × Fin M => μ q.1 q.2) =
      Measure.map (MeasurableEquiv.curry (Fin N) (Fin M) ℝ).symm
        (Measure.pi fun i => Measure.pi fun j => μ i j) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [MeasurableEquiv.map_apply]
    have : (MeasurableEquiv.curry (Fin N) (Fin M) ℝ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
      ext X
      simp [MeasurableEquiv.curry, Function.uncurry]
    rw [this, Fintype.prod_prod_type]
    simp only [Measure.pi_pi]
  refine ⟨(MeasurableEquiv.curry (Fin N) (Fin M) ℝ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.curry _ _ ℝ).measurable
    (MeasurableEquiv.curry _ _ ℝ).symm.measurable]
  simp

end Density

end B8RSK
-- ===== C1g_body.lean

namespace B8RSK

open MeasureTheory

section TProps

/-- 2D prefix sums. -/
noncomputable def psum (X : ℕ → ℕ → ℝ) (a b : ℕ) : ℝ :=
  ∑ a' ∈ Finset.range (a + 1), ∑ b' ∈ Finset.range (b + 1), X a' b'

theorem psum_rec (X : ℕ → ℕ → ℝ) (a b : ℕ) :
    psum X a b = X a b + (if a = 0 then 0 else psum X (a - 1) b) + (if b = 0 then 0 else psum X a (b - 1)) -
      (if a = 0 ∨ b = 0 then 0 else psum X (a - 1) (b - 1)) := by
  cases a with
  | zero =>
    cases b with
    | zero => simp [psum]
    | succ b =>
      have e : psum X 0 (b + 1) = psum X 0 b + X 0 (b + 1) := by
        simp only [psum, zero_add, Finset.sum_range_one]; exact Finset.sum_range_succ _ _
      simp only [if_true, true_or, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      linarith
  | succ a =>
    cases b with
    | zero =>
      have e : psum X (a + 1) 0 = psum X a 0 + X (a + 1) 0 := by
        simp only [psum, zero_add, Finset.sum_range_one]; exact Finset.sum_range_succ (fun a' => X a' 0) _
      simp only [if_true, or_true, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      linarith
    | succ b =>
      have e1 : psum X (a + 1) (b + 1) = psum X a (b + 1) + ∑ b' ∈ Finset.range (b + 2), X (a + 1) b' :=
        Finset.sum_range_succ _ _
      have e2 : psum X (a + 1) b = psum X a b + ∑ b' ∈ Finset.range (b + 1), X (a + 1) b' :=
        Finset.sum_range_succ _ _
      have e3 : ∑ b' ∈ Finset.range (b + 2), X (a + 1) b' =
          ∑ b' ∈ Finset.range (b + 1), X (a + 1) b' + X (a + 1) (b + 1) := Finset.sum_range_succ _ _
      simp only [Nat.succ_ne_zero, if_false, or_self, Nat.add_sub_cancel]
      linarith

/-- reverse plane partition condition on a flat array. -/
def RPPf {N M : ℕ} (Z : Fin N × Fin M → ℝ) : Prop :=
  ∀ a b, a < N → b < M → upv (rd Z) a b ≤ rd Z a b ∧ lfv (rd Z) a b ≤ rd Z a b

theorem T_props {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (z : Fin N × Fin M → ℝ) :
    (RPPf (iterF M (N * M) z) ↔ ∀ q, 0 ≤ z q) ∧
    ((∀ q, 0 ≤ z q) →
      rd (iterF M (N * M) z) (N - 1) (M - 1) = Gn (rd z) (N - 1) (M - 1) ∧
      ∀ a, a < N → dsum (rd (iterF M (N * M) z)) a (M - 1) = psum (rd z) a (M - 1)) := by
  have hT := rd_iterF (N := N) hM z (N * M) le_rfl
  have hnn : (∀ q, 0 ≤ z q) ↔ ∀ a b, a < N → b < M → 0 ≤ rd z a b := by
    constructor
    · intro h a b ha hb; simp only [rd, dif_pos (And.intro ha hb)]; exact h _
    · intro h q; rw [← rd_fin z q]; exact h _ _ q.1.isLt q.2.isLt
  refine ⟨?_, fun hz => ?_⟩
  · unfold RPPf; rw [hT, hnn]; exact cone_iff_rpp hM (rd z)
  · have hc := iter_cone hM (rd z) (Gn (rd z)) (psum (rd z)) (Gn_eq (rd z)) (psum_rec (rd z))
      (hnn.1 hz) (N * M) le_rfl
    simp only [proc_full_t hM] at hc
    rw [hT]
    refine ⟨hc.1 _ _ ⟨by omega, by omega⟩ (by omega), fun a ha => hc.2.2 _ _ ⟨ha, by omega⟩ (by omega)⟩

end TProps

end B8RSK
-- ===== C1h_body.lean
namespace B8RSK

open MeasureTheory ProbabilityTheory

section Assembly

/-- row weight read off the RPP: difference of consecutive diagonal sums ending in the last column. -/
noncomputable def rowW {N M : ℕ} (Z : Fin N × Fin M → ℝ) (a : ℕ) : ℝ :=
  dsum (rd Z) a (M - 1) - (if a = 0 then 0 else dsum (rd Z) (a - 1) (M - 1))

/-- reverse plane partitions with corner at most `x`. -/
def rppSet (N M : ℕ) (x : ℝ) : Set (Fin N × Fin M → ℝ) :=
  {Z | RPPf Z ∧ rd Z (N - 1) (M - 1) ≤ x}

/-- the RPP weight. -/
noncomputable def wR (N M : ℕ) (π : Fin N → ℝ) (Z : Fin N × Fin M → ℝ) : ENNReal :=
  ∏ i : Fin N, ENNReal.ofReal ((π i * M) ^ M * Real.exp (-(π i * M) * rowW Z i))

/-- the integrand of `R(π, M, x)`. -/
noncomputable def gR (N M : ℕ) (π : Fin N → ℝ) (x : ℝ) (Z : Fin N × Fin M → ℝ) : ENNReal :=
  (rppSet N M x).indicator (wR N M π) Z

theorem measurable_dsum {N M : ℕ} : ∀ a b : ℕ, Measurable fun Z : Fin N × Fin M → ℝ => dsum (rd Z) a b := by
  intro a
  induction a with
  | zero => intro b; exact measurable_rd 0 b
  | succ a ih =>
    intro b
    cases b with
    | zero => exact measurable_rd (a + 1) 0
    | succ b => exact (measurable_rd (a + 1) (b + 1)).add (ih b)

theorem measurable_rowW {N M : ℕ} (a : ℕ) : Measurable fun Z : Fin N × Fin M → ℝ => rowW Z a := by
  unfold rowW
  by_cases h : a = 0
  · simp only [if_pos h]; exact (measurable_dsum a (M - 1)).sub measurable_const
  · simp only [if_neg h]; exact (measurable_dsum a (M - 1)).sub (measurable_dsum (a - 1) (M - 1))

theorem measurableSet_rppSet (N M : ℕ) (x : ℝ) : MeasurableSet (rppSet N M x) := by
  have h1 : ∀ a b : ℕ, Measurable fun Z : Fin N × Fin M → ℝ =>
      upv (rd Z) a b ≤ rd Z a b ∧ lfv (rd Z) a b ≤ rd Z a b := fun a b =>
    (measurableSet_setOfPred.1 (measurableSet_le (measurable_upv a b) (measurable_rd a b))).and
      (measurableSet_setOfPred.1 (measurableSet_le (measurable_lfv a b) (measurable_rd a b)))
  have h2 : Measurable fun Z : Fin N × Fin M → ℝ => RPPf Z :=
    Measurable.forall fun a => Measurable.forall fun b => measurable_const.imp (measurable_const.imp (h1 a b))
  have h3 : Measurable fun Z : Fin N × Fin M → ℝ => rd Z (N - 1) (M - 1) ≤ x :=
    measurableSet_setOfPred.1 (measurableSet_le (measurable_rd _ _) measurable_const)
  exact measurableSet_setOfPred.2 (h2.and h3)

theorem measurable_wR (N M : ℕ) (π : Fin N → ℝ) : Measurable (wR N M π) := by
  unfold wR
  refine Finset.measurable_prod _ fun i _ => ?_
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (measurable_rowW (i : ℕ)))))

theorem measurable_gR (N M : ℕ) (π : Fin N → ℝ) (x : ℝ) : Measurable (gR N M π x) :=
  (measurable_wR N M π).indicator (measurableSet_rppSet N M x)

theorem ext_curry {N M : ℕ} (z : Fin N × Fin M → ℝ) : ext (Function.curry z) = rd z := by
  funext a b
  simp only [ext, rd, Function.curry]

/-- row sums from prefix sums. -/
theorem psum_row {N M : ℕ} (hM : 0 < M) (z : Fin N × Fin M → ℝ) (i : Fin N) :
    psum (rd z) i (M - 1) - (if (i : ℕ) = 0 then 0 else psum (rd z) ((i : ℕ) - 1) (M - 1)) =
      ∑ j : Fin M, z (i, j) := by
  have hr : ∑ j : Fin M, z (i, j) = ∑ b ∈ Finset.range M, rd z i b := by
    rw [← Fin.sum_univ_eq_sum_range (fun b => rd z i b)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (rd_fin z (i, j)).symm
  rw [hr]
  have hM' : M - 1 + 1 = M := by omega
  by_cases h : (i : ℕ) = 0
  · rw [if_pos h]
    simp only [psum, h, zero_add, Finset.sum_range_one, hM', sub_zero]
  · rw [if_neg h]
    obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
    simp only [psum, hk, Nat.add_sub_cancel, hM']
    rw [Finset.sum_range_succ]
    ring

theorem row_prod (r : ℝ) (hr : 0 < r) (M : ℕ) (y : Fin M → ℝ) :
    ∏ j : Fin M, ENNReal.ofReal (r * Real.exp (-(r * y j))) =
      ENNReal.ofReal (r ^ M * Real.exp (-r * ∑ j, y j)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (mul_pos hr (Real.exp_pos _)).le)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pointwise_C1 {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i) (x : ℝ)
    (Lf : (Fin N × Fin M → ℝ) → ℝ)
    (hLf : ∀ z, (∀ q, 0 ≤ z q) → Lf z = Gn (rd z) (N - 1) (M - 1)) (z : Fin N × Fin M → ℝ) :
    {z | Lf z ≤ x}.indicator (fun z => ∏ q : Fin N × Fin M, exponentialPDF (π q.1 * M) (z q)) z =
      gR N M π x (iterF M (N * M) z) := by
  obtain ⟨hcone, hrest⟩ := T_props hN hM z
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  by_cases h : ∀ q, 0 ≤ z q
  · obtain ⟨hcorner, hdiag⟩ := hrest h
    have hR : RPPf (iterF M (N * M) z) := hcone.2 h
    have hF : (∏ q : Fin N × Fin M, exponentialPDF (π q.1 * M) (z q)) = wR N M π (iterF M (N * M) z) := by
      simp_rw [exponentialPDF_of_nonneg (h _)]
      rw [Fintype.prod_prod_type]
      unfold wR
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [row_prod _ (mul_pos (hπ i) hMr) M (fun j => z (i, j))]
      congr 3
      unfold rowW
      rw [hdiag i i.isLt]
      by_cases h0 : (i : ℕ) = 0
      · rw [if_pos h0, ← psum_row hM z i, if_pos h0]
      · rw [if_neg h0, hdiag ((i : ℕ) - 1) (by omega), ← psum_row hM z i, if_neg h0]
    by_cases hx : Lf z ≤ x
    · have hm : iterF M (N * M) z ∈ rppSet N M x := ⟨hR, by rw [hcorner, ← hLf z h]; exact hx⟩
      rw [Set.indicator_of_mem (show z ∈ {z | Lf z ≤ x} from hx), gR, Set.indicator_of_mem hm, hF]
    · have hm : iterF M (N * M) z ∉ rppSet N M x := fun hm => hx (by rw [hLf z h, ← hcorner]; exact hm.2)
      rw [Set.indicator_of_notMem (show z ∉ {z | Lf z ≤ x} from hx), gR, Set.indicator_of_notMem hm]
  · have hm : iterF M (N * M) z ∉ rppSet N M x := fun hm => h (hcone.1 hm.1)
    rw [gR, Set.indicator_of_notMem hm]
    push Not at h
    obtain ⟨q, hq⟩ := h
    have h0 : (∏ q : Fin N × Fin M, exponentialPDF (π q.1 * M) (z q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (exponentialPDF_of_neg hq)
    by_cases hx : z ∈ {z | Lf z ≤ x}
    · rw [Set.indicator_of_mem hx, h0]
    · rw [Set.indicator_of_notMem hx]

open SpikedWishart.LastPassage in
theorem measurable_L {N M : ℕ} [NeZero N] [NeZero M] : Measurable fun X : Fin N → Fin M → ℝ => L X := by
  unfold L lpp
  refine Measurable.iSup fun p => Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

open SpikedWishart.LastPassage in
/-- C1: the exponential LPP distribution function as an RPP integral. -/
theorem expLaw_L_le {N M : ℕ} [NeZero N] [NeZero M] (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i) (x : ℝ) :
    expLaw π M {X | L X ≤ x} = ∫⁻ Z, gR N M π x Z := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  haveI hσ : ∀ i (_ : Fin M), SigmaFinite (expMeasure (π i * M)) := fun i _ => by
    haveI := isProbabilityMeasure_expMeasure (mul_pos (hπ i) hMr); infer_instance
  haveI hσ' : ∀ q : Fin N × Fin M, SigmaFinite ((volume : Measure ℝ).withDensity (exponentialPDF (π q.1 * M))) :=
    fun q => hσ q.1 q.2
  have hmap := (@measurePreserving_curry_pi N M (fun i _ => expMeasure (π i * M)) hσ).map_eq
  have hS : MeasurableSet {X : Fin N → Fin M → ℝ | L X ≤ x} := measurableSet_le measurable_L measurable_const
  have hS' : MeasurableSet ((MeasurableEquiv.curry (Fin N) (Fin M) ℝ) ⁻¹' {X | L X ≤ x}) :=
    (MeasurableEquiv.curry (Fin N) (Fin M) ℝ).measurable hS
  have hpw := pi_withDensity (ι := Fin N × Fin M) (fun q => exponentialPDF (π q.1 * M))
    (fun q => (measurable_exponentialPDFReal _).ennreal_ofReal)
  unfold expLaw
  rw [← hmap, MeasurableEquiv.map_apply]
  change (Measure.pi fun q : Fin N × Fin M => (volume : Measure ℝ).withDensity (exponentialPDF (π q.1 * M))) _ = _
  rw [hpw, withDensity_apply _ hS', ← lintegral_indicator hS']
  have hLf : ∀ z : Fin N × Fin M → ℝ, (∀ q, 0 ≤ z q) →
      L (Function.curry z) = Gn (rd z) (N - 1) (M - 1) := by
    intro z hz
    unfold L
    rw [lpp_eq_Gn (X := Function.curry z) (fun i j => hz (i, j)), ext_curry]
  have key := pointwise_C1 hN hM π hπ x (fun z => L (Function.curry z)) hLf
  calc ∫⁻ z, ((MeasurableEquiv.curry (Fin N) (Fin M) ℝ) ⁻¹' {X | L X ≤ x}).indicator
          (fun z => ∏ q : Fin N × Fin M, exponentialPDF (π q.1 * M) (z q)) z
        = ∫⁻ z, gR N M π x (iterF M (N * M) z) := lintegral_congr fun z => key z
    _ = ∫⁻ Z, gR N M π x Z := (measurePreserving_iterF (N * M)).lintegral_comp (measurable_gR N M π x)

end Assembly

end B8RSK



set_option autoImplicit false



namespace SpikedWishart.Separated.Lib
open Filter Topology MeasureTheory Matrix Polynomial
open Filter Topology MeasureTheory Matrix Complex ProbabilityTheory
open Filter Topology MeasureTheory Matrix Polynomial ProbabilityTheory Complex

-- ===== from W1a.lean =====
section

namespace Weyl

open Finset

/-- Absolute Vandermonde product `∏_{i<j} |v i - v j|`. -/
noncomputable def vdm {m : ℕ} (v : Fin m → ℝ) : ℝ := ∏ i : Fin m, ∏ j ∈ Ioi i, |v i - v j|

/-- `D_i = ∏_{l ≠ i} (μ_i - μ_l)`. -/
noncomputable def Dn {n : ℕ} (mu : Fin n → ℝ) (i : Fin n) : ℝ := ∏ l ∈ univ.erase i, (mu i - mu l)

/-- Dixon-Anderson weights `w_i = -∏_j (μ_i - λ_j) / D_i`. -/
noncomputable def wv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  -(∏ j, (mu i - la j)) / Dn mu i

/-- The corner entry `c = Σ λ - Σ μ`. -/
noncomputable def cv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) : ℝ := ∑ j, la j - ∑ i, mu i

/-- Strict interlacing `λ_0 > μ_0 > λ_1 > ... > μ_{n-1} > λ_n`. -/
def Ilace {n : ℕ} (mu : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {la | ∀ i : Fin n, mu i < la (Fin.castSucc i) ∧ la (Fin.succ i) < mu i}

theorem Dn_ne_zero {n : ℕ} {mu : Fin n → ℝ} (hmu : Function.Injective mu) (i : Fin n) :
    Dn mu i ≠ 0 := by
  unfold Dn
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hl) (hmu h).symm)

theorem degree_prod_sub_lt {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : ∑ j, a j = ∑ j, b j) :
    (∏ j, (X - C (a j)) - ∏ j, (X - C (b j))).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub, sub_eq_zero]
  have hda : (∏ j, (X - C (a j))).natDegree = n + 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card]; simp
  have hdb : (∏ j, (X - C (b j))).natDegree = n + 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card]; simp
  rcases Nat.lt_or_ge (n + 1) m with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
  rcases (show m = n ∨ m = n + 1 by omega) with rfl | rfl
  · have h1 := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin (m + 1))) a (by simp)
    have h2 := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin (m + 1))) b (by simp)
    simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h1 h2
    rw [h1, h2, hab]
  · have ma : (∏ j, (X - C (a j))).Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)
    have mb : (∏ j, (X - C (b j))).Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)
    have e1 := ma.coeff_natDegree
    have e2 := mb.coeff_natDegree
    rw [hda] at e1
    rw [hdb] at e2
    rw [e1, e2]

theorem degree_lagr_lt {n : ℕ} (mu w : Fin n → ℝ) :
    (-(∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l)))).degree < (n : WithBot ℕ) := by
  rw [degree_neg]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
  intro i _
  rw [C_mul']
  refine lt_of_le_of_lt (degree_smul_le _ _) ?_
  rw [degree_eq_natDegree (Polynomial.Monic.ne_zero
    (monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C _))), natDegree_finset_prod_X_sub_C_eq_card]
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  exact WithBot.coe_lt_coe.mpr (Nat.sub_lt hn one_pos)

/-- (P): the Dixon-Anderson polynomial identity
`∏ (X - λ_j) = (X - c) ∏ (X - μ_i) - Σ_i w_i ∏_{l≠i} (X - μ_l)`. -/
theorem poly_id {n : ℕ} {mu : Fin n → ℝ} (hmu : Function.Injective mu) (la : Fin (n + 1) → ℝ) :
    ∏ j, (X - C (la j)) = (X - C (cv mu la)) * ∏ i, (X - C (mu i)) -
      ∑ i, C (wv mu la i) * ∏ l ∈ univ.erase i, (X - C (mu l)) := by
  set nu : Fin (n + 1) → ℝ := Fin.snoc mu (cv mu la) with hnu
  have hprod : ∏ j, (X - C (nu j)) = (X - C (cv mu la)) * ∏ i, (X - C (mu i)) := by
    rw [Fin.prod_univ_castSucc]
    simp only [hnu, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  have hsum : ∑ j, la j = ∑ j, nu j := by
    simp only [hnu, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, cv]
    ring
  have key : ∏ j, (X - C (la j)) - ∏ j, (X - C (nu j)) =
      -(∑ i, C (wv mu la i) * ∏ l ∈ univ.erase i, (X - C (mu l))) := by
    refine eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin n))) (v := mu)
      hmu.injOn ?_ ?_ ?_
    · rw [card_univ, Fintype.card_fin]; exact degree_prod_sub_lt la nu hsum
    · rw [card_univ, Fintype.card_fin]; exact degree_lagr_lt mu _
    · intro i _
      have hz : eval (mu i) (∏ j, (X - C (nu j))) = 0 := by
        rw [eval_prod, Finset.prod_eq_zero (i := Fin.castSucc i) (mem_univ _)]
        simp [hnu]
      rw [eval_sub, hz, sub_zero, eval_neg, eval_finsetSum,
        Finset.sum_eq_single i]
      · rw [eval_mul, eval_C, eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        have hD := Dn_ne_zero hmu i
        rw [eval_prod]
        simp only [eval_sub, eval_X, eval_C]
        unfold wv
        change _ = -(-(∏ j, (mu i - la j)) / Dn mu i * Dn mu i)
        field_simp
      · intro l _ hli
        rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (mem_erase.mpr ⟨Ne.symm hli, mem_univ _⟩)]
        · ring
        · simp
      · intro h; exact absurd (mem_univ i) h
  rw [← hprod]
  linear_combination key

theorem poly_id_eval {n : ℕ} {mu : Fin n → ℝ} (hmu : Function.Injective mu) (la : Fin (n + 1) → ℝ)
    (t : ℝ) :
    ∏ j, (t - la j) = (t - cv mu la) * ∏ i, (t - mu i) -
      ∑ i, wv mu la i * ∏ l ∈ univ.erase i, (t - mu l) := by
  have h := congrArg (eval t) (poly_id hmu la)
  simpa [eval_prod, eval_finsetSum] using h

/-- Sign of a product of nonzero reals. -/
theorem prod_eq_sign_mul_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ j ∈ s, f j = (-1) ^ #(s.filter (fun j => f j < 0)) * ∏ j ∈ s, |f j| := by
  classical
  have h : ∀ j, f j = if f j < 0 then -|f j| else |f j| := by
    intro j
    split_ifs with hj
    · rw [abs_of_neg hj, neg_neg]
    · rw [abs_of_nonneg (not_lt.mp hj)]
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_ite, Finset.prod_neg]
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun j => f j < 0) (f := fun j => |f j|)]
  ring

theorem ilace_strictAnti {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    StrictAnti la := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  exact lt_trans (h i).2 (h i).1

theorem ilace_mu_strictAnti {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    StrictAnti mu := by
  intro i j hij
  have ha := (ilace_strictAnti h).antitone
  have hle : Fin.succ i ≤ Fin.castSucc j := by
    rw [Fin.le_def]; simp; exact hij
  exact lt_of_lt_of_le (h j).1 (ha hle) |>.trans (h i).2

theorem filter_la {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n) :
    (univ.filter (fun j => mu i - la j < 0)) = Iic (Fin.castSucc i) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_Iic, sub_neg]
  have ha := (ilace_strictAnti h).antitone
  constructor
  · intro hj
    by_contra hc
    have : Fin.succ i ≤ j := by
      rw [not_le, Fin.lt_def] at hc; rw [Fin.le_def]; simp at hc ⊢; omega
    exact absurd (lt_trans (lt_of_le_of_lt (ha this) (h i).2) hj) (lt_irrefl _)
  · intro hj
    exact lt_of_lt_of_le (h i).1 (ha hj)

theorem filter_mu {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n) :
    ((univ.erase i).filter (fun l => mu i - mu l < 0)) = Iio i := by
  ext l
  simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio, sub_neg]
  have hm := ilace_mu_strictAnti h
  constructor
  · rintro ⟨hne, hl⟩
    by_contra hc
    rcases lt_or_eq_of_le (not_lt.mp hc) with h' | h'
    · exact absurd (lt_trans hl (hm h')) (lt_irrefl _)
    · exact hne h'.symm
  · intro hl
    exact ⟨ne_of_lt hl, hm hl⟩

theorem wv_pos {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n) :
    0 < wv mu la i := by
  have hmu : Function.Injective mu := (ilace_mu_strictAnti h).injective
  have hla : Function.Injective la := (ilace_strictAnti h).injective
  unfold wv Dn
  rw [prod_eq_sign_mul_abs, prod_eq_sign_mul_abs (univ.erase i), filter_la h, filter_mu h,
    Fin.card_Iic, Fin.card_Iio, Fin.val_castSucc]
  have hA : 0 < ∏ j, |mu i - la j| := by
    apply Finset.prod_pos; intro j _
    apply abs_pos.mpr
    intro he
    have : mu i = la j := sub_eq_zero.mp he
    rcases lt_or_ge j (Fin.succ i) with hj | hj
    · have hj' : j ≤ Fin.castSucc i := by rw [Fin.le_def]; rw [Fin.lt_def] at hj; simp at hj ⊢; omega
      exact absurd (this ▸ lt_of_lt_of_le (h i).1 ((ilace_strictAnti h).antitone hj')) (lt_irrefl _)
    · exact absurd (this ▸ lt_of_le_of_lt ((ilace_strictAnti h).antitone hj) (h i).2) (lt_irrefl _)
  have hB : 0 < ∏ l ∈ univ.erase i, |mu i - mu l| := by
    apply Finset.prod_pos; intro l hl
    exact abs_pos.mpr (sub_ne_zero.mpr (fun he => (ne_of_mem_erase hl) (hmu he).symm))
  have hs : ((-1 : ℝ) ^ (i : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [pow_succ]
  have : -((-1 : ℝ) ^ (i : ℕ) * -1 * ∏ j, |mu i - la j|) / ((-1) ^ (i : ℕ) * ∏ l ∈ univ.erase i, |mu i - mu l|)
      = (∏ j, |mu i - la j|) / ∏ l ∈ univ.erase i, |mu i - mu l| := by
    have hne : ((-1 : ℝ) ^ (i : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  rw [this]
  exact div_pos hA hB

theorem vdm_eq_abs_det {m : ℕ} (v : Fin m → ℝ) : vdm v = |(vandermonde v).det| := by
  rw [det_vandermonde, vdm, Finset.abs_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl (fun j _ => abs_sub_comm _ _)

end Weyl

end

-- ===== from W1b.lean =====
section

namespace Weyl

open Finset

/-- `∏_{j} ∏_{k ≠ j} |v j - v k| = vdm v ^ 2`. -/
theorem prod_offdiag_abs {m : ℕ} (v : Fin m → ℝ) :
    ∏ j, ∏ k ∈ univ.erase j, |v j - v k| = vdm v ^ 2 := by
  have hsplit : ∀ j : Fin m, univ.erase j = Iio j ∪ Ioi j := by
    intro j; ext k
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_Iio, mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : ∀ j : Fin m, Disjoint (Iio j) (Ioi j) := by
    intro j; rw [Finset.disjoint_left]; intro k h1 h2; simp at h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
  simp_rw [hsplit, Finset.prod_union (hdisj _), Finset.prod_mul_distrib]
  have hcomm : ∏ j : Fin m, ∏ k ∈ Iio j, |v j - v k| = ∏ k : Fin m, ∏ j ∈ Ioi k, |v j - v k| :=
    Finset.prod_comm' (fun j k => by simp)
  rw [hcomm, vdm, sq]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => Finset.prod_congr rfl (fun j _ => abs_sub_comm _ _))

theorem vdm_pos {m : ℕ} {v : Fin m → ℝ} (hv : Function.Injective v) : 0 < vdm v := by
  unfold vdm
  apply Finset.prod_pos; intro i _; apply Finset.prod_pos; intro j hj
  exact abs_pos.mpr (sub_ne_zero.mpr (fun h => (ne_of_lt (mem_Ioi.mp hj)) (hv h)))

theorem prod_abs_Dn {n : ℕ} (mu : Fin n → ℝ) : ∏ i, |Dn mu i| = vdm mu ^ 2 := by
  rw [← prod_offdiag_abs]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Dn, Finset.abs_prod]

/-- `q_j = ∏_{k ≠ j} (X - λ_k)`. -/
noncomputable def qp {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ[X] :=
  ∏ k ∈ univ.erase j, (X - C (la k))

theorem qp_monic {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : (qp la j).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem qp_natDegree {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : (qp la j).natDegree = n := by
  rw [qp, natDegree_finsetProd_X_sub_C_eq_card, card_erase_of_mem (mem_univ j), card_univ,
    Fintype.card_fin, Nat.add_sub_cancel]

theorem eval_qp {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (t : ℝ) :
    (qp la j).eval t = ∏ k ∈ univ.erase j, (t - la k) := by
  rw [qp, eval_prod]; simp

theorem sum_coeff_qp {n : ℕ} (la : Fin (n + 1) → ℝ) (j : Fin (n + 1)) (t : ℝ) :
    ∑ m : Fin (n + 1), t ^ (m : ℕ) * (qp la j).coeff m = (qp la j).eval t := by
  rw [eval_eq_sum_range' (n := n + 1) (by rw [qp_natDegree]; omega)]
  rw [Fin.sum_univ_eq_sum_range (fun m => t ^ m * (qp la j).coeff m) (n + 1)]
  exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)

/-- Coefficient matrix `Cm m j = coeff_m q_j`. -/
noncomputable def Cm {n : ℕ} (la : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun m j => (qp la j).coeff m

theorem vandermonde_mul_Cm {n : ℕ} (la : Fin (n + 1) → ℝ) :
    vandermonde la * Cm la = diagonal (fun j => ∏ k ∈ univ.erase j, (la j - la k)) := by
  ext k j
  rw [mul_apply]
  simp only [vandermonde_apply, Cm, Matrix.of_apply]
  rw [sum_coeff_qp, eval_qp, diagonal_apply]
  split_ifs with h
  · subst h; rfl
  · exact Finset.prod_eq_zero (i := k) (mem_erase.mpr ⟨h, mem_univ _⟩) (sub_self _)

theorem abs_det_Cm {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : Function.Injective la) :
    |(Cm la).det| = vdm la := by
  have h := congrArg (fun A => |det A|) (vandermonde_mul_Cm la)
  simp only [det_mul, abs_mul, det_diagonal, Finset.abs_prod] at h
  rw [← vdm_eq_abs_det, prod_offdiag_abs, sq] at h
  have hp := vdm_pos hla
  exact mul_left_cancel₀ hp.ne' h

/-- `B`: Vandermonde rows of `μ` plus the last unit row. -/
noncomputable def Bm {n : ℕ} (mu : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i m => Fin.snoc (α := fun _ => ℝ) (fun i' => mu i' ^ (m : ℕ))
    (if m = Fin.last n then 1 else 0) i

theorem det_Bm {n : ℕ} (mu : Fin n → ℝ) : (Bm mu).det = (vandermonde mu).det := by
  rw [det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · simp only [Bm, Matrix.of_apply, Fin.snoc_last, if_pos rfl, Fin.succAbove_last]
    have : (Bm mu).submatrix Fin.castSucc Fin.castSucc = vandermonde mu := by
      ext i m; simp [Bm, vandermonde_apply]
    simp only [Bm] at this
    rw [this]
    simp [← pow_add, ← two_mul, pow_mul]
  · intro j _ hj
    simp [Bm, hj]
  · intro h; exact absurd (mem_univ _) h

/-- `A i j = q_j(μ_i)` for `i < n`, last row `1`. -/
noncomputable def Am {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.snoc (α := fun _ => ℝ) (fun i' => ∏ k ∈ univ.erase j, (mu i' - la k)) 1 i

theorem Bm_mul_Cm {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) : Bm mu * Cm la = Am mu la := by
  ext i j
  rw [mul_apply]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [Bm, Am, Cm, Matrix.of_apply, Fin.snoc_last, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', mem_univ, if_true]
    have := (qp_monic la j).coeff_natDegree
    rw [qp_natDegree] at this
    simpa using this
  · simp only [Bm, Am, Cm, Matrix.of_apply, Fin.snoc_castSucc]
    rw [sum_coeff_qp, eval_qp]

/-- The Jacobian matrix of `λ ↦ (w(λ), c(λ))`. -/
noncomputable def Jm {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.snoc (α := fun _ => ℝ)
    (fun i' => (∏ k ∈ univ.erase j, (mu i' - la k)) / Dn mu i') 1 i

theorem Jm_eq {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    Jm mu la = diagonal (Fin.snoc (α := fun _ => ℝ) (fun i' => (Dn mu i')⁻¹) 1) * Am mu la := by
  ext i j
  rw [diagonal_mul]
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [Jm, Am]
  · simp only [Jm, Am, Matrix.of_apply, Fin.snoc_castSucc]
    rw [div_eq_inv_mul]

theorem abs_det_Jm {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (hmu : Function.Injective mu)
    (hla : Function.Injective la) : |(Jm mu la).det| = vdm la / vdm mu := by
  rw [Jm_eq, det_mul, det_diagonal, ← Bm_mul_Cm, det_mul, det_Bm, abs_mul, abs_mul,
    abs_det_Cm hla, ← vdm_eq_abs_det, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_one, Finset.abs_prod, abs_inv]
  rw [Finset.prod_inv_distrib, prod_abs_Dn]
  have hp := vdm_pos hmu
  field_simp

end Weyl

end

-- ===== from W1c.lean =====
section

namespace Weyl

open Finset

/-- The real arrow matrix `[[diag μ, b], [bᵀ, c]]` on `Fin (n+1)`. -/
noncomputable def arrowR {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (diagonal mu) (Matrix.of fun i (_ : Fin 1) => b i) (Matrix.of fun (_ : Fin 1) j => b j)
      (Matrix.of fun _ _ => c))

theorem arrowR_cc {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (i j : Fin n) :
    arrowR mu b c (Fin.castSucc i) (Fin.castSucc j) = diagonal mu i j := by
  simp [arrowR, reindex_apply]

theorem arrowR_cl {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    arrowR mu b c (Fin.castSucc i) (Fin.last n) = b i := by
  simp [arrowR, reindex_apply]

theorem arrowR_lc {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (j : Fin n) :
    arrowR mu b c (Fin.last n) (Fin.castSucc j) = b j := by
  simp [arrowR, reindex_apply]

theorem arrowR_ll {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) :
    arrowR mu b c (Fin.last n) (Fin.last n) = c := by
  simp [arrowR, reindex_apply]

theorem arrowR_symm {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (i j : Fin (n + 1)) :
    arrowR mu b c i j = arrowR mu b c j i := by
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  · rfl
  · rw [arrowR_lc, arrowR_cl]
  · rw [arrowR_lc, arrowR_cl]
  · rw [arrowR_cc, arrowR_cc, diagonal_apply, diagonal_apply]
    by_cases h : i' = j'
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]

theorem charpoly_arrowR_eval {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) (t : ℝ) (ht : ∀ i, t ≠ mu i) :
    (arrowR mu b c).charpoly.eval t = (∏ i, (t - mu i)) * ((t - c) - ∑ i, b i ^ 2 / (t - mu i)) := by
  rw [arrowR, charpoly_reindex, eval_charpoly]
  have hsc : (scalar (Fin n ⊕ Fin 1) t : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) =
      fromBlocks (diagonal fun _ => t) 0 0 (diagonal fun _ => t) := by
    rw [scalar_apply, fromBlocks_diagonal]; congr 1; ext x; cases x <;> rfl
  rw [hsc, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  set A : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => t - mu i) with hA
  have hA' : diagonal (fun _ => t) + -diagonal mu = A := by
    rw [hA, ← sub_eq_add_neg, diagonal_sub]
  rw [hA']
  have hinv : diagonal (fun i => (t - mu i)⁻¹) * A = 1 := by
    rw [hA, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext i; exact inv_mul_cancel₀ (sub_ne_zero.mpr (ht i))
  letI : Invertible A := invertibleOfLeftInverse A _ hinv
  have hdetA : A.det = ∏ i, (t - mu i) := by rw [hA, det_diagonal]
  rw [det_fromBlocks₁₁, hdetA, det_unique]
  congr 1
  show _ = t - c - ∑ i, b i ^ 2 / (t - mu i)
  have hinvOf : (⅟A : Matrix (Fin n) (Fin n) ℝ) = diagonal (fun i => (t - mu i)⁻¹) := rfl
  rw [hinvOf]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply, mul_apply, diagonal_apply,
    Matrix.zero_apply, mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, if_true]
  rw [← sub_eq_add_neg t c]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- With `b = √w(λ)`, `c = c(λ)`, the arrow matrix has characteristic polynomial `∏ (X - λ_j)`. -/
theorem charpoly_arrowR {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    (arrowR mu (fun i => Real.sqrt (wv mu la i)) (cv mu la)).charpoly = ∏ j, (X - C (la j)) := by
  have hmu : Function.Injective mu := (ilace_mu_strictAnti h).injective
  apply eq_of_infinite_eval_eq
  have hinf : (Set.range mu)ᶜ.Infinite := (Set.finite_range mu).infinite_compl
  refine hinf.mono (fun t ht => ?_)
  have ht' : ∀ i, t ≠ mu i := fun i he => ht ⟨i, he.symm⟩
  show _ = _
  rw [charpoly_arrowR_eval _ _ _ _ ht']
  have hw : ∀ i, Real.sqrt (wv mu la i) ^ 2 = wv mu la i := fun i => Real.sq_sqrt (wv_pos h i).le
  simp only [hw]
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [poly_id_eval hmu la t, mul_sub, mul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_prod_erase univ (fun l => t - mu l) (mem_univ i)]
  have : t - mu i ≠ 0 := sub_ne_zero.mpr (ht' i)
  field_simp

/-- The complex arrow matrix. -/
noncomputable def arrowC {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (arrowR mu b c).map (fun x : ℝ => (x : ℂ))

theorem arrowC_isHermitian {n : ℕ} (mu b : Fin n → ℝ) (c : ℝ) : (arrowC mu b c).IsHermitian := by
  ext i j
  simp [arrowC, conjTranspose_apply, arrowR_symm mu b c i j]

theorem perm_conj_diag {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → ℂ) :
    diagonal (d ∘ σ) = (1 : Matrix (Fin m) (Fin m) ℂ).submatrix σ id * diagonal d *
      star ((1 : Matrix (Fin m) (Fin m) ℂ).submatrix σ id) := by
  ext i j
  simp only [mul_apply, diagonal_apply, submatrix_apply, one_apply, id, star_apply, Function.comp_apply]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, σ.injective.eq_iff]
  split_ifs with h <;> simp [h]

theorem perm_mem_unitary {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (1 : Matrix (Fin m) (Fin m) ℂ).submatrix σ id ∈ unitaryGroup (Fin m) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j
  simp only [mul_apply, submatrix_apply, one_apply, id, star_apply]
  simp [Finset.sum_ite_eq', σ.injective.eq_iff]

/-- (K) The arrow matrix with `b = √w(λ)`, `c = c(λ)` is unitarily similar to `diag λ`. -/
theorem arrowC_similar {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) :
    ∃ U ∈ unitaryGroup (Fin (n + 1)) ℂ,
      arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) =
        U * diagonal (fun j => (la j : ℂ)) * star U := by
  set A := arrowC mu (fun i => Real.sqrt (wv mu la i)) (cv mu la) with hAdef
  have hA : A.IsHermitian := arrowC_isHermitian _ _ _
  have hla : Function.Injective la := (ilace_strictAnti h).injective
  -- roots of the characteristic polynomial
  have hcp : A.charpoly = ∏ j, (X - C ((la j : ℝ) : ℂ)) := by
    have hf : (fun x : ℝ => (x : ℂ)) = ⇑Complex.ofRealHom := rfl
    rw [hAdef, arrowC, hf, charpoly_map, charpoly_arrowR h, Polynomial.map_prod]
    simp
  have hroots : Multiset.map (fun j => ((la j : ℝ) : ℂ)) univ.val =
      Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) univ.val := by
    rw [← hA.roots_charpoly_eq_eigenvalues, hcp, Finset.prod_eq_multiset_prod,
      show (fun j => X - C ((la j : ℝ) : ℂ)) = (fun a => X - C a) ∘ (fun j => ((la j : ℝ) : ℂ)) from rfl,
      ← Multiset.map_map (fun a => X - C a) (fun j => ((la j : ℝ) : ℂ)), roots_multiset_prod_X_sub_C]
  have hre := congrArg (Multiset.map Complex.re) hroots
  simp only [Multiset.map_map] at hre
  have hev : Multiset.map la univ.val = Multiset.map hA.eigenvalues univ.val := by
    simpa [Function.comp_def] using hre
  have hnd : (Multiset.map hA.eigenvalues univ.val).Nodup := by
    rw [← hev]; exact (Multiset.nodup_map_iff_inj_on univ.nodup).mpr (fun x _ y _ hxy => hla hxy)
  have hevinj : Function.Injective hA.eigenvalues := by
    intro x y hxy
    exact (Multiset.nodup_map_iff_inj_on univ.nodup).mp hnd x (Finset.mem_val.mpr (mem_univ _)) y
      (Finset.mem_val.mpr (mem_univ _)) hxy
  have hmem : ∀ i, ∃ j, la j = hA.eigenvalues i := by
    intro i
    have : hA.eigenvalues i ∈ Multiset.map la univ.val := by
      rw [hev]; exact Multiset.mem_map_of_mem _ (mem_univ i)
    obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp this
    exact ⟨j, hj⟩
  choose s hs using hmem
  have hsinj : Function.Injective s := by
    intro x y hxy; apply hevinj; rw [← hs x, ← hs y, hxy]
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj)
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix σ id
  have hd : (RCLike.ofReal ∘ hA.eigenvalues : Fin (n + 1) → ℂ) = (fun j => ((la j : ℝ) : ℂ)) ∘ σ := by
    ext i; simp [σ, hs]
  refine ⟨(hA.eigenvectorUnitary).1 * P, Submonoid.mul_mem _ hA.eigenvectorUnitary.2 (perm_mem_unitary σ), ?_⟩
  conv_lhs => rw [hspec]
  rw [hd, perm_conj_diag, star_mul]
  simp only [mul_assoc]
  rfl

end Weyl

end

-- ===== from W1d.lean =====
section

namespace Weyl

open Finset

/-- The secular function `t - c - Σ w_i / (t - μ_i)`. -/
noncomputable def sec {n : ℕ} (mu w : Fin n → ℝ) (c t : ℝ) : ℝ := t - c - ∑ i, w i / (t - mu i)

/-- The Dixon-Anderson map `λ ↦ (w(λ), c(λ))`. -/
noncomputable def Phi {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (wv mu la) (cv mu la)

/-- Target set `{y | y_i > 0 for i < n}`. -/
def Vpos (n : ℕ) : Set (Fin (n + 1) → ℝ) := {y | ∀ i : Fin n, 0 < y (Fin.castSucc i)}

/-- `R(t) = (t - c) ∏ (t - μ_i) - Σ w_i ∏_{l ≠ i} (t - μ_l)`. -/
noncomputable def Rf {n : ℕ} (mu w : Fin n → ℝ) (c t : ℝ) : ℝ :=
  (t - c) * ∏ i, (t - mu i) - ∑ i, w i * ∏ l ∈ univ.erase i, (t - mu l)

theorem Rf_eq_prod_sec {n : ℕ} (mu w : Fin n → ℝ) (c t : ℝ) (ht : ∀ i, t ≠ mu i) :
    Rf mu w c t = (∏ i, (t - mu i)) * sec mu w c t := by
  have key : ∀ i, (∏ l, (t - mu l)) * (w i / (t - mu i)) = w i * ∏ l ∈ univ.erase i, (t - mu l) := by
    intro i
    rw [← Finset.mul_prod_erase univ (fun l => t - mu l) (mem_univ i)]
    have : t - mu i ≠ 0 := sub_ne_zero.mpr (ht i)
    field_simp
  unfold Rf sec
  rw [mul_sub, mul_sub, Finset.mul_sum]
  simp_rw [key]
  ring

theorem Rf_at_mu {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    Rf mu w c (mu i) = -(w i * Dn mu i) := by
  unfold Rf Dn
  rw [Finset.prod_eq_zero (i := i) (mem_univ _) (sub_self _), mul_zero, zero_sub,
    Finset.sum_eq_single i]
  · intro l _ hli
    rw [Finset.prod_eq_zero (i := i) (mem_erase.mpr ⟨Ne.symm hli, mem_univ _⟩) (sub_self _), mul_zero]
  · intro h; exact absurd (mem_univ i) h

theorem side_iff {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n)
    (j : Fin (n + 1)) : mu i < la j ↔ j ≤ Fin.castSucc i := by
  have := congrArg (fun s => j ∈ s) (filter_la h i)
  simp only [mem_filter, mem_univ, true_and, mem_Iic, sub_neg, eq_iff_iff] at this
  exact this

theorem la_ne_mu {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (i : Fin n)
    (j : Fin (n + 1)) : la j ≠ mu i := by
  intro he
  have ha := (ilace_strictAnti h).antitone
  rcases le_or_gt j (Fin.castSucc i) with hj | hj
  · exact absurd (he ▸ lt_of_lt_of_le (h i).1 (ha hj)) (lt_irrefl _)
  · have : Fin.succ i ≤ j := by rw [Fin.le_def]; rw [Fin.lt_def] at hj; simp at hj ⊢; omega
    exact absurd (he ▸ lt_of_le_of_lt (ha this) (h i).2) (lt_irrefl _)

theorem sec_root {n : ℕ} {mu : Fin n → ℝ} {la : Fin (n + 1) → ℝ} (h : la ∈ Ilace mu) (j : Fin (n + 1)) :
    sec mu (wv mu la) (cv mu la) (la j) = 0 := by
  have hmu : Function.Injective mu := (ilace_mu_strictAnti h).injective
  have hne : ∀ i, la j ≠ mu i := fun i => la_ne_mu h i j
  have hR : Rf mu (wv mu la) (cv mu la) (la j) = 0 := by
    have := poly_id_eval hmu la (la j)
    rw [Finset.prod_eq_zero (i := j) (mem_univ _) (sub_self _)] at this
    unfold Rf; linarith
  rw [Rf_eq_prod_sec _ _ _ _ hne] at hR
  have hp : (∏ i, (la j - mu i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hne i))
  exact (mul_eq_zero.mp hR).resolve_left hp

theorem sec_lt {n : ℕ} (mu w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ℝ) {s t : ℝ} (hst : s < t)
    (hside : ∀ i, (mu i < s ↔ mu i < t)) (hs : ∀ i, s ≠ mu i) (ht : ∀ i, t ≠ mu i) :
    sec mu w c s < sec mu w c t := by
  unfold sec
  have key : ∀ i, w i / (t - mu i) ≤ w i / (s - mu i) := by
    intro i
    by_cases hi : mu i < s
    · have h1 : 0 < s - mu i := by linarith
      have h2 : 0 < t - mu i := by linarith
      exact div_le_div_of_nonneg_left (hw i) h1 (by linarith)
    · have hs' : s < mu i := lt_of_le_of_ne (not_lt.mp hi) (hs i)
      have ht' : t < mu i := lt_of_le_of_ne (not_lt.mp (fun h => hi ((hside i).mpr h))) (ht i)
      have hp : 0 < (t - mu i) * (s - mu i) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have h1 : s - mu i ≠ 0 := by linarith
      have h2 : t - mu i ≠ 0 := by linarith
      have e : w i / (s - mu i) - w i / (t - mu i) = w i * (t - s) / ((t - mu i) * (s - mu i)) := by
        field_simp; ring
      have : 0 ≤ w i * (t - s) / ((t - mu i) * (s - mu i)) :=
        div_nonneg (mul_nonneg (hw i) (by linarith)) hp.le
      linarith
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
  linarith

theorem phi_injOn {n : ℕ} (mu : Fin n → ℝ) : Set.InjOn (Phi mu) (Ilace mu) := by
  intro la ha la' ha' hP
  have hw : wv mu la = wv mu la' := by
    funext i
    have := congrFun hP (Fin.castSucc i)
    simpa [Phi] using this
  have hc : cv mu la = cv mu la' := by
    have := congrFun hP (Fin.last n)
    simpa [Phi] using this
  have hwpos : ∀ i, 0 ≤ wv mu la i := fun i => (wv_pos ha i).le
  funext j
  by_contra hne
  have hside : ∀ i, (mu i < la j ↔ mu i < la' j) := by
    intro i; rw [side_iff ha, side_iff ha']
  have r1 := sec_root ha j
  have r2 := sec_root ha' j
  rw [← hw, ← hc] at r2
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := sec_lt mu _ hwpos (cv mu la) hlt hside (fun i => la_ne_mu ha i j) (fun i => la_ne_mu ha' i j)
    linarith
  · have := sec_lt mu _ hwpos (cv mu la) hlt (fun i => (hside i).symm) (fun i => la_ne_mu ha' i j)
      (fun i => la_ne_mu ha i j)
    linarith

/-- The interval of the `j`-th root. -/
def Jset {n : ℕ} (mu : Fin n → ℝ) (j : Fin (n + 1)) : Set ℝ :=
  {t | ∀ i : Fin n, (j ≤ Fin.castSucc i → mu i < t) ∧ (¬ j ≤ Fin.castSucc i → t < mu i)}

theorem Jset_ordConnected {n : ℕ} (mu : Fin n → ℝ) (j : Fin (n + 1)) : (Jset mu j).OrdConnected := by
  refine ⟨fun a ha b hb x hx => ?_⟩
  intro i
  exact ⟨fun h => lt_of_lt_of_le ((ha i).1 h) hx.1, fun h => lt_of_le_of_lt hx.2 ((hb i).2 h)⟩

theorem Jset_ne {n : ℕ} {mu : Fin n → ℝ} {j : Fin (n + 1)} {t : ℝ} (ht : t ∈ Jset mu j) (i : Fin n) :
    t ≠ mu i := by
  by_cases h : j ≤ Fin.castSucc i
  · exact ne_of_gt ((ht i).1 h)
  · exact ne_of_lt ((ht i).2 h)

theorem sec_continuousOn {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (j : Fin (n + 1)) :
    ContinuousOn (sec mu w c) (Jset mu j) := by
  unfold sec
  refine (continuousOn_id.sub continuousOn_const).sub (continuousOn_finsetSum _ (fun i _ => ?_))
  exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    (fun t ht => sub_ne_zero.mpr (Jset_ne ht i))

theorem sum_abs_ge {n : ℕ} (mu : Fin n → ℝ) (i : Fin n) : |mu i| ≤ ∑ l, |mu l| :=
  Finset.single_le_sum (f := fun l => |mu l|) (fun l _ => abs_nonneg _) (mem_univ i)

/-- Far to the left the secular function is negative. -/
theorem sec_neg_far {n : ℕ} (mu w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    let t0 := -(|c| + ∑ i, w i + ∑ i, |mu i| + 2)
    (∀ i, t0 < mu i) ∧ sec mu w c t0 < 0 := by
  intro t0
  have hwn : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hlt : ∀ i, t0 - mu i < -1 := by
    intro i
    have := sum_abs_ge mu i
    have := neg_abs_le (mu i)
    have := abs_nonneg c
    simp only [t0]; linarith
  refine ⟨fun i => by linarith [hlt i], ?_⟩
  have key : ∀ i, -w i ≤ w i / (t0 - mu i) := by
    intro i
    have hn : t0 - mu i < 0 := by linarith [hlt i]
    rw [le_div_iff_of_neg hn]
    nlinarith [hw i, hlt i]
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
  rw [Finset.sum_neg_distrib] at this
  unfold sec
  have := le_abs_self c
  have := neg_abs_le c
  have hs : 0 ≤ ∑ i, |mu i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  simp only [t0] at this ⊢
  linarith

/-- Far to the right the secular function is positive. -/
theorem sec_pos_far {n : ℕ} (mu w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (c : ℝ) :
    let t0 := |c| + ∑ i, w i + ∑ i, |mu i| + 2
    (∀ i, mu i < t0) ∧ 0 < sec mu w c t0 := by
  intro t0
  have hwn : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hgt : ∀ i, 1 < t0 - mu i := by
    intro i
    have := sum_abs_ge mu i
    have := le_abs_self (mu i)
    have := abs_nonneg c
    simp only [t0]; linarith
  refine ⟨fun i => by linarith [hgt i], ?_⟩
  have key : ∀ i, w i / (t0 - mu i) ≤ w i := by
    intro i
    have hp : 0 < t0 - mu i := by linarith [hgt i]
    rw [div_le_iff₀ hp]
    nlinarith [hw i, hgt i]
  have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
  unfold sec
  have := le_abs_self c
  have hs : 0 ≤ ∑ i, |mu i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  simp only [t0] at this ⊢
  linarith

theorem sec_split {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (i0 : Fin n) (t : ℝ) :
    sec mu w c t = (t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) + -(w i0 * (t - mu i0)⁻¹) := by
  unfold sec
  rw [← Finset.add_sum_erase univ _ (mem_univ i0), div_eq_mul_inv]
  ring

theorem cont_rest {n : ℕ} (mu w : Fin n → ℝ) (hmu : Function.Injective mu) (c : ℝ) (i0 : Fin n) :
    ContinuousAt (fun t => t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) (mu i0) := by
  refine (continuousAt_id.sub continuousAt_const).sub ?_
  refine tendsto_finset_sum _ (fun i hi => ?_)
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const)
    (sub_ne_zero.mpr (fun h => (ne_of_mem_erase hi) (hmu h).symm))

theorem sec_atBot {n : ℕ} (mu w : Fin n → ℝ) (hmu : Function.Injective mu) (hw : ∀ i, 0 < w i)
    (c : ℝ) (i0 : Fin n) : Tendsto (sec mu w c) (𝓝[>] (mu i0)) atBot := by
  have h1 : Tendsto (fun t => t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) (𝓝[>] (mu i0))
      (𝓝 (mu i0 - c - ∑ i ∈ univ.erase i0, w i / (mu i0 - mu i))) :=
    (cont_rest mu w hmu c i0).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => t - mu i0) (𝓝[>] (mu i0)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t => t - mu i0) (𝓝 (mu i0)) (𝓝 (mu i0 - mu i0)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (Set.mem_Ioi.mp ht)
  have h3 : Tendsto (fun t => (t - mu i0)⁻¹) (𝓝[>] (mu i0)) atTop := tendsto_inv_nhdsGT_zero.comp h2
  have h4 : Tendsto (fun t => -(w i0 * (t - mu i0)⁻¹)) (𝓝[>] (mu i0)) atBot :=
    tendsto_neg_atTop_atBot.comp (h3.const_mul_atTop (hw i0))
  have := h1.add_atBot h4
  refine this.congr (fun t => (sec_split mu w c i0 t).symm)

theorem sec_atTop {n : ℕ} (mu w : Fin n → ℝ) (hmu : Function.Injective mu) (hw : ∀ i, 0 < w i)
    (c : ℝ) (i0 : Fin n) : Tendsto (sec mu w c) (𝓝[<] (mu i0)) atTop := by
  have h1 : Tendsto (fun t => t - c - ∑ i ∈ univ.erase i0, w i / (t - mu i)) (𝓝[<] (mu i0))
      (𝓝 (mu i0 - c - ∑ i ∈ univ.erase i0, w i / (mu i0 - mu i))) :=
    (cont_rest mu w hmu c i0).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun t => t - mu i0) (𝓝[<] (mu i0)) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t => t - mu i0) (𝓝 (mu i0)) (𝓝 (mu i0 - mu i0)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_neg.mpr (Set.mem_Iio.mp ht)
  have h3 : Tendsto (fun t => (t - mu i0)⁻¹) (𝓝[<] (mu i0)) atBot := tendsto_inv_nhdsLT_zero.comp h2
  have h4 : Tendsto (fun t => -(w i0 * (t - mu i0)⁻¹)) (𝓝[<] (mu i0)) atTop :=
    tendsto_neg_atBot_atTop.comp (h3.const_mul_atBot (hw i0))
  have := h1.add_atTop h4
  refine this.congr (fun t => (sec_split mu w c i0 t).symm)

theorem exists_neg {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (c : ℝ) (j : Fin (n + 1)) : ∃ a ∈ Jset mu j, sec mu w c a < 0 := by
  refine Fin.lastCases ?_ (fun i0 => ?_) j
  · obtain ⟨h1, h2⟩ := sec_neg_far mu w hw c
    refine ⟨_, fun i => ⟨fun h => absurd h ?_, fun _ => h1 i⟩, h2⟩
    rw [not_le, Fin.lt_def]; simp
  · have hev : ∀ᶠ t in 𝓝[>] (mu i0), t ∈ Jset mu (Fin.castSucc i0) := by
      have : ∀ i, ∀ᶠ t in 𝓝[>] (mu i0), (Fin.castSucc i0 ≤ Fin.castSucc i → mu i < t) ∧
          (¬ Fin.castSucc i0 ≤ Fin.castSucc i → t < mu i) := by
        intro i
        by_cases hi : Fin.castSucc i0 ≤ Fin.castSucc i
        · have hle : mu i ≤ mu i0 := hmu.antitone (Fin.castSucc_le_castSucc_iff.mp hi)
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact ⟨fun _ => lt_of_le_of_lt hle ht, fun h => absurd hi h⟩
        · have hlt : mu i0 < mu i := hmu (by rw [Fin.castSucc_le_castSucc_iff, not_le] at hi; exact hi)
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with t ht
          exact ⟨fun h => absurd h hi, fun _ => ht⟩
      exact Filter.eventually_all.mpr this
    have hneg := (sec_atBot mu w hmu.injective hw c i0).eventually (eventually_lt_atBot 0)
    obtain ⟨t, ht1, ht2⟩ := (hev.and hneg).exists
    exact ⟨t, ht1, ht2⟩

theorem exists_pos {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (c : ℝ) (j : Fin (n + 1)) : ∃ b ∈ Jset mu j, 0 < sec mu w c b := by
  refine Fin.cases ?_ (fun i0 => ?_) j
  · obtain ⟨h1, h2⟩ := sec_pos_far mu w hw c
    refine ⟨_, fun i => ⟨fun _ => h1 i, fun h => absurd (Fin.zero_le _) h⟩, h2⟩
  · have hev : ∀ᶠ t in 𝓝[<] (mu i0), t ∈ Jset mu (Fin.succ i0) := by
      have : ∀ i, ∀ᶠ t in 𝓝[<] (mu i0), (Fin.succ i0 ≤ Fin.castSucc i → mu i < t) ∧
          (¬ Fin.succ i0 ≤ Fin.castSucc i → t < mu i) := by
        intro i
        by_cases hi : Fin.succ i0 ≤ Fin.castSucc i
        · have hlt : mu i < mu i0 := hmu (by rw [Fin.le_def] at hi; rw [Fin.lt_def]; simp at hi; omega)
          filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlt)] with t ht
          exact ⟨fun _ => ht, fun h => absurd hi h⟩
        · have hle : mu i0 ≤ mu i := hmu.antitone (by
            rw [Fin.le_def] at hi ⊢; simp at hi; omega)
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact ⟨fun h => absurd h hi, fun _ => lt_of_lt_of_le ht hle⟩
      exact Filter.eventually_all.mpr this
    have hpos := (sec_atTop mu w hmu.injective hw c i0).eventually (eventually_gt_atTop 0)
    obtain ⟨t, ht1, ht2⟩ := (hev.and hpos).exists
    exact ⟨t, ht1, ht2⟩

theorem exists_root {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (c : ℝ) (j : Fin (n + 1)) : ∃ t ∈ Jset mu j, sec mu w c t = 0 := by
  obtain ⟨a, ha, hfa⟩ := exists_neg hmu w hw c j
  obtain ⟨b, hb, hfb⟩ := exists_pos hmu w hw c j
  have := (Jset_ordConnected mu j).isPreconnected.intermediate_value ha hb (sec_continuousOn mu w c j)
  obtain ⟨t, ht, hft⟩ := this ⟨hfa.le, hfb.le⟩
  exact ⟨t, ht, hft⟩

theorem degree_R_sub_lt {n : ℕ} (mu w : Fin n → ℝ) (c : ℝ) (la : Fin (n + 1) → ℝ) :
    ((X - C c) * ∏ i, (X - C (mu i)) - ∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l)) -
      ∏ j, (X - C (la j))).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
  set nu : Fin (n + 1) → ℝ := Fin.snoc mu c with hnu
  have hprod : ∏ j, (X - C (nu j)) = (X - C c) * ∏ i, (X - C (mu i)) := by
    rw [Fin.prod_univ_castSucc]
    simp only [hnu, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  have hA : (∏ j, (X - C (nu j)) - ∏ j, (X - C (la j))).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    have m1 : (∏ j, (X - C (nu j))).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
    have m2 : (∏ j, (X - C (la j))).Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
    have d1 : (∏ j, (X - C (nu j))).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree m1.ne_zero, natDegree_finsetProd_X_sub_C_eq_card]; simp
    have d2 : (∏ j, (X - C (la j))).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_eq_natDegree m2.ne_zero, natDegree_finsetProd_X_sub_C_eq_card]; simp
    rw [← d1]
    exact degree_sub_lt_left (d1.trans d2.symm) m1.ne_zero (by rw [m1.leadingCoeff, m2.leadingCoeff])
  have hL := degree_lagr_lt mu w
  rw [degree_neg] at hL
  have hL' : (∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l))).degree < ((n + 1 : ℕ) : WithBot ℕ) :=
    lt_of_lt_of_le hL (by exact_mod_cast Nat.le_succ n)
  rw [← hprod, sub_right_comm]
  exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hL')

theorem Vpos_subset_image {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) :
    Vpos n ⊆ Phi mu '' Ilace mu := by
  intro y hy
  set w : Fin n → ℝ := fun i => y (Fin.castSucc i) with hwdef
  set c : ℝ := y (Fin.last n) with hcdef
  have hw : ∀ i, 0 < w i := hy
  choose la hla hroot using exists_root hmu w hw c
  have hI : la ∈ Ilace mu := by
    intro i
    exact ⟨(hla (Fin.castSucc i) i).1 le_rfl,
      (hla (Fin.succ i) i).2 (by rw [Fin.le_def]; simp)⟩
  have hinj : Function.Injective la := (ilace_strictAnti hI).injective
  refine ⟨la, hI, ?_⟩
  -- R_{w,c} = ∏ (X - λ_j)
  have hpoly : (X - C c) * ∏ i, (X - C (mu i)) - ∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l)) =
      ∏ j, (X - C (la j)) := by
    refine eq_of_degree_sub_lt_of_eval_index_eq (s := (univ : Finset (Fin (n + 1)))) (v := la)
      hinj.injOn ?_ ?_
    · rw [card_univ, Fintype.card_fin]; exact degree_R_sub_lt mu w c la
    · intro j _
      have hR := Rf_eq_prod_sec mu w c (la j) (Jset_ne (hla j))
      rw [hroot j, mul_zero] at hR
      have e1 : eval (la j) ((X - C c) * ∏ i, (X - C (mu i)) -
          ∑ i, C (w i) * ∏ l ∈ univ.erase i, (X - C (mu l))) = Rf mu w c (la j) := by
        simp [Rf, eval_prod, eval_finsetSum]
      rw [e1, hR, eval_prod, Finset.prod_eq_zero (i := j) (mem_univ _) (by simp)]
  have hpoly2 := poly_id hmu.injective la
  have hfun : ∀ t, Rf mu w c t = Rf mu (wv mu la) (cv mu la) t := by
    intro t
    have e1 := congrArg (eval t) hpoly
    have e2 := congrArg (eval t) hpoly2
    simp only [eval_sub, eval_mul, eval_X, eval_C, eval_prod, eval_finsetSum] at e1 e2
    unfold Rf
    rw [e1, e2]
  have hwe : ∀ i, w i = wv mu la i := by
    intro i
    have := hfun (mu i)
    rw [Rf_at_mu, Rf_at_mu] at this
    have hD := Dn_ne_zero hmu.injective i
    have : (w i - wv mu la i) * Dn mu i = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hD)
  have hce : c = cv mu la := by
    obtain ⟨t0, ht0⟩ : ∃ t0, t0 ∉ Set.range mu := ((Set.finite_range mu).infinite_compl).nonempty
    have hne : ∀ i, t0 ≠ mu i := fun i he => ht0 ⟨i, he.symm⟩
    have := hfun t0
    unfold Rf at this
    simp only [← hwe] at this
    have hp : (∏ i, (t0 - mu i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hne i))
    have : (cv mu la - c) * ∏ i, (t0 - mu i) = 0 := by linarith
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hp)).symm
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Phi, Fin.snoc_last]; exact hce.symm
  · simp only [Phi, Fin.snoc_castSucc]; exact (hwe i).symm

theorem image_Phi {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu) : Phi mu '' Ilace mu = Vpos n := by
  refine Set.Subset.antisymm ?_ (Vpos_subset_image hmu)
  rintro _ ⟨la, hla, rfl⟩ i
  simp only [Phi, Fin.snoc_castSucc]
  exact wv_pos hla i

end Weyl

end

-- ===== from W2a.lean =====
section

namespace Weyl

open Finset

/-- The Jacobian as a continuous linear map. -/
noncomputable def Jlin {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Jm mu la))

theorem det_Jlin {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    (Jlin mu la).det = (Jm mu la).det := by
  rw [Jlin, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']

theorem Jlin_apply {n : ℕ} (mu : Fin n → ℝ) (la v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Jlin mu la v i = ∑ j, Jm mu la i j * v j := by
  simp [Jlin, Matrix.toLin'_apply, mulVec, dotProduct]

theorem hasFDerivAt_wv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) (i : Fin n) :
    HasFDerivAt (fun la => wv mu la i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.castSucc i)).comp
        (Jlin mu la)) la := by
  have hj : ∀ j ∈ (univ : Finset (Fin (n + 1))), HasFDerivAt (fun la : Fin (n + 1) → ℝ => mu i - la j)
      (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j)) la :=
    fun j _ => (hasFDerivAt_apply (𝕜 := ℝ) j la).const_sub (mu i)
  have hp := (HasFDerivAt.finsetProd hj).const_mul (-(Dn mu i)⁻¹)
  have hf : (fun la => wv mu la i) = fun la => -(Dn mu i)⁻¹ * ∏ j, (mu i - la j) := by
    funext la; simp only [wv, div_eq_mul_inv]; ring
  rw [hf]
  refine hp.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [Jlin_apply]
  simp [Jm, div_eq_mul_inv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem hasFDerivAt_cv {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun la => cv mu la)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
        (Jlin mu la)) la := by
  have hs := (HasFDerivAt.fun_sum (u := (univ : Finset (Fin (n + 1))))
    (fun j _ => hasFDerivAt_apply (𝕜 := ℝ) j la)).sub_const (∑ i, mu i)
  refine hs.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [Jlin_apply]
  simp [Jm]

theorem hasFDerivAt_Phi {n : ℕ} (mu : Fin n → ℝ) (la : Fin (n + 1) → ℝ) :
    HasFDerivAt (Phi mu) (Jlin mu la) la := by
  rw [hasFDerivAt_pi']
  intro i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · have : (fun la => Phi mu la (Fin.last n)) = fun la => cv mu la := by
      funext la; simp [Phi]
    rw [this]; exact hasFDerivAt_cv mu la
  · have : (fun la => Phi mu la (Fin.castSucc i')) = fun la => wv mu la i' := by
      funext la; simp [Phi]
    rw [this]; exact hasFDerivAt_wv mu la i'

theorem measurableSet_Ilace {n : ℕ} (mu : Fin n → ℝ) : MeasurableSet (Ilace mu) := by
  have : Ilace mu = ⋂ i : Fin n, ({la : Fin (n + 1) → ℝ | mu i < la (Fin.castSucc i)} ∩
      {la | la (Fin.succ i) < mu i}) := by
    ext la; simp [Ilace]
  rw [this]
  refine MeasurableSet.iInter (fun i => (measurableSet_lt measurable_const (measurable_pi_apply _)).inter
    (measurableSet_lt (measurable_pi_apply _) measurable_const))

end Weyl

end

-- ===== from W3a.lean =====
section

namespace Weyl

open Finset

end Weyl

end

-- ===== from W4a.lean =====
section

namespace Weyl

open Finset

/-- The box `Π_i (λ_{i+1}, λ_i)` of the `μ` interlacing `λ`. -/
def box {n : ℕ} (la : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i : Fin n => Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)))

theorem mem_box_iff {n : ℕ} {la : Fin (n + 1) → ℝ} {mu : Fin n → ℝ} : mu ∈ box la ↔ la ∈ Ilace mu := by
  simp only [box, Ilace, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Set.mem_setOf_eq]
  exact forall_congr' fun i => and_comm

theorem measurableSet_box {n : ℕ} (la : Fin (n + 1) → ℝ) : MeasurableSet (box la) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

theorem vdm_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ vdm v :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _

/-- The sign `∏_{i<j} (-1)`. -/
noncomputable def sgn (m : ℕ) : ℝ := ∏ i : Fin m, ∏ _j ∈ Ioi i, (-1 : ℝ)

theorem abs_sgn (m : ℕ) : |sgn m| = 1 := by
  simp [sgn, Finset.abs_prod]

theorem sgn_mul_self (m : ℕ) : sgn m * sgn m = 1 := by
  rw [← abs_mul_self, abs_mul, abs_sgn, one_mul]

theorem det_vdm_strictAnti {m : ℕ} {v : Fin m → ℝ} (hv : StrictAnti v) :
    (vandermonde v).det = sgn m * vdm v := by
  rw [det_vandermonde, vdm, sgn, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have := hv (mem_Ioi.mp hj)
  rw [abs_of_pos (by linarith)]
  ring

theorem integral_Ioo_pow {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    ∫ t in Set.Ioo a b, t ^ k = (b ^ (k + 1) - a ^ (k + 1)) / (k + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab, integral_pow]

theorem integrableOn_Ioo_pow (a b : ℝ) (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) (volume.restrict (Set.Ioo a b)) :=
  ((continuous_pow k).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self

/-- Integral of a Vandermonde determinant over a box = determinant of the 1D moment integrals. -/
theorem integral_det_vdm {n : ℕ} (la : Fin (n + 1) → ℝ) :
    ∫ mu in box la, (vandermonde mu).det =
      (Matrix.of fun (i : Fin n) (j : Fin n) =>
        ∫ t in Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)), t ^ (j : ℕ)).det := by
  have hrestr : (volume : Measure (Fin n → ℝ)).restrict (box la) =
      Measure.pi (fun i : Fin n => volume.restrict (Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)))) := by
    rw [box, show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) from rfl,
      Measure.restrict_pi_pi]
  rw [hrestr]
  have h1 : (fun mu : Fin n → ℝ => (vandermonde mu).det) =
      fun mu => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, mu i ^ (σ i : ℕ) := by
    funext mu
    rw [← det_transpose, det_apply']
    simp [vandermonde_apply]
  rw [h1, integral_finsetSum _ (fun σ _ => (Integrable.fintype_prod
    (f := fun i (t : ℝ) => t ^ (σ i : ℕ)) (fun i => integrableOn_Ioo_pow _ _ _)).const_mul _)]
  rw [← det_transpose, det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => t ^ (σ i : ℕ))]
  simp

theorem prod_inv_succ (n : ℕ) : ∏ j : Fin n, (1 / ((j : ℕ) + 1 : ℝ)) = 1 / (n.factorial : ℝ) := by
  rw [Fin.prod_univ_eq_prod_range (fun j => 1 / ((j : ℝ) + 1)) n, Nat.factorial_eq_prod_range_add_one]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const_one]

/-- The row-difference determinant equals the Vandermonde determinant up to sign. -/
theorem abs_det_diff {n : ℕ} (la : Fin (n + 1) → ℝ) :
    |(Matrix.of fun (i : Fin n) (j : Fin n) =>
        la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1)).det| = vdm la := by
  rw [vdm_eq_abs_det]
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
    Fin.cases (la 0 ^ (j : ℕ)) (fun i' : Fin n => la i'.succ ^ (j : ℕ) - la i'.castSucc ^ (j : ℕ)) i
    with hB
  have hdet : (vandermonde la).det = B.det := by
    refine det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1) (fun j => ?_) (fun i j => ?_)
    · simp [hB, vandermonde_apply]
    · simp [hB, vandermonde_apply]
  have hB2 : B.det = (B.submatrix Fin.succ Fin.succ).det := by
    rw [det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∀ i : Fin n, B i.succ 0 = 0 := by intro i; simp [hB]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp [hB, Fin.succAbove_zero]
  have hsub : B.submatrix Fin.succ Fin.succ = -(Matrix.of fun (i : Fin n) (j : Fin n) =>
        la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1)) := by
    ext i j
    simp [hB, Fin.val_succ]
  rw [hdet, hB2, hsub, det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The interlacing integral `∫_{box λ} Δ(μ) dμ = Δ(λ) / n!`. -/
theorem integral_box_vdm {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : StrictAnti la) :
    ∫ mu in box la, vdm mu = vdm la / (n.factorial : ℝ) := by
  have hcong : ∫ mu in box la, vdm mu = sgn n * ∫ mu in box la, (vandermonde mu).det := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_box la) (fun mu hmu => ?_)
    rw [det_vdm_strictAnti (ilace_mu_strictAnti (mem_box_iff.mp hmu)), ← mul_assoc, sgn_mul_self,
      one_mul]
  have hnn : 0 ≤ ∫ mu in box la, vdm mu :=
    setIntegral_nonneg (measurableSet_box la) (fun mu _ => vdm_nonneg mu)
  have hN : (Matrix.of fun (i : Fin n) (j : Fin n) =>
        ∫ t in Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)), t ^ (j : ℕ)) =
      Matrix.of fun (i : Fin n) (j : Fin n) => (1 / ((j : ℕ) + 1 : ℝ)) *
        (la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1)) := by
    ext i j
    have hle : la (Fin.succ i) ≤ la (Fin.castSucc i) := (hla (Fin.castSucc_lt_succ (i := i))).le
    simp only [Matrix.of_apply]
    rw [integral_Ioo_pow hle]
    ring
  have hrow := det_mul_row (fun j : Fin n => 1 / ((j : ℕ) + 1 : ℝ)) (Matrix.of fun (i : Fin n) (j : Fin n) =>
        la (Fin.castSucc i) ^ ((j : ℕ) + 1) - la (Fin.succ i) ^ ((j : ℕ) + 1))
  simp only [Matrix.of_apply] at hrow
  rw [← abs_of_nonneg hnn, hcong, abs_mul, abs_sgn, one_mul, integral_det_vdm, hN,
    hrow, prod_inv_succ, abs_mul, abs_det_diff,
    abs_of_pos (by positivity)]
  ring

end Weyl

end

-- ===== from W2b.lean =====
section

namespace Weyl

open Finset

/-- Change of variables `y = Φ_μ(λ)` on the interlacing region (lintegral form). -/
theorem lintegral_Vpos_eq {n : ℕ} {mu : Fin n → ℝ} (hmu : StrictAnti mu)
    (g : (Fin (n + 1) → ℝ) → ENNReal) :
    ∫⁻ y in Vpos n, g y = ∫⁻ la in Ilace mu, ENNReal.ofReal (vdm la / vdm mu) * g (Phi mu la) := by
  rw [← image_Phi hmu, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_Ilace mu)
    (fun la _ => (hasFDerivAt_Phi mu la).hasFDerivWithinAt) (phi_injOn mu)]
  refine setLIntegral_congr_fun (measurableSet_Ilace mu) (fun la hla => ?_)
  rw [det_Jlin, abs_det_Jm hmu.injective (ilace_strictAnti hla).injective]

theorem continuous_vdm {m : ℕ} : Continuous (fun v : Fin m → ℝ => vdm v) := by
  unfold vdm; fun_prop

theorem box_subset_Icc {n : ℕ} (la : Fin (n + 1) → ℝ) :
    box la ⊆ Set.Icc (fun i : Fin n => la (Fin.succ i)) (fun i => la (Fin.castSucc i)) := by
  intro mu hmu
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hmu
  exact ⟨fun i => (hmu i).1.le, fun i => (hmu i).2.le⟩

/-- The interlacing integral, lintegral form. -/
theorem lintegral_box_vdm {n : ℕ} {la : Fin (n + 1) → ℝ} (hla : StrictAnti la) :
    ∫⁻ mu in box la, ENNReal.ofReal (vdm mu) = ENNReal.ofReal (vdm la / (n.factorial : ℝ)) := by
  rw [← integral_box_vdm hla, ofReal_integral_eq_lintegral_ofReal]
  · exact (continuous_vdm.integrableOn_Icc).mono_set (box_subset_Icc la)
  · exact Filter.Eventually.of_forall (fun mu => vdm_nonneg mu)

end Weyl

end

-- ===== from Q3a.lean =====
section

/-- `stdComplexGaussian` as a pushforward of two independent `N(0,1/2)`. -/
theorem integral_cg (f : ℂ → ℂ) (hf : AEStronglyMeasurable f SpikedWishart.SoftEdge.stdComplexGaussian) :
    ∫ z, f z ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      ∫ p, f ⟨p.1, p.2⟩ ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian at hf ⊢
  exact integral_map (φ := fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable hf

/-- Scalar characteristic function of the standard complex Gaussian. -/
theorem cg_char (a b : ℝ) :
    ∫ z, cexp (((a * z.re + b * z.im : ℝ) : ℂ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      cexp (-(((a ^ 2 + b ^ 2) / 4 : ℝ) : ℂ)) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp (((a * (⟨p.1, p.2⟩ : ℂ).re + b * (⟨p.1, p.2⟩ : ℂ).im : ℝ) : ℂ) * I) =
      cexp (a * p.1 * I) * cexp (b * p.2 * I) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp (a * x * I)) (fun y : ℝ => cexp (b * y * I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `E exp(i t x²)` for `x ∼ N(0,1/2)`. -/
theorem g_sq_char (t : ℝ) :
    ∫ x, cexp ((t * x ^ 2 : ℝ) * I) ∂(gaussianReal 0 (1 / 2)) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h : ∀ x : ℝ, gaussianPDFReal 0 (1 / 2) x • cexp ((t * x ^ 2 : ℝ) * I) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) * cexp (-(1 - t * I) * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal, Complex.real_smul]
    have h2 : (2 * Real.pi * ((1 / 2 : NNReal) : ℝ)) = Real.pi := by push_cast; ring
    have h3 : (-(x - 0) ^ 2 / (2 * ((1 / 2 : NNReal) : ℝ))) = -x ^ 2 := by push_cast; ring
    have h4 : (((-x ^ 2 : ℝ)) : ℂ) + ((t * x ^ 2 : ℝ) : ℂ) * I = -(1 - t * I) * (x : ℂ) ^ 2 := by
      push_cast; ring
    rw [h2, h3, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv, mul_assoc,
      ← Complex.exp_add, h4]
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian_complex (by simp)]

/-- `E exp(i t |z|²) = 1/(1 - i t)` for the standard complex Gaussian. -/
theorem cg_normSq_char (t : ℝ) :
    ∫ z, cexp ((t * Complex.normSq z : ℝ) * I) ∂SpikedWishart.SoftEdge.stdComplexGaussian =
      1 / (1 - t * I) := by
  rw [integral_cg _ (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, cexp ((t * Complex.normSq (⟨p.1, p.2⟩ : ℂ) : ℝ) * I) =
      cexp ((t * p.1 ^ 2 : ℝ) * I) * cexp ((t * p.2 ^ 2 : ℝ) * I) := by
    intro p
    rw [← Complex.exp_add, Complex.normSq_mk]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [integral_prod_mul (fun x : ℝ => cexp ((t * x ^ 2 : ℝ) * I))
    (fun y : ℝ => cexp ((t * y ^ 2 : ℝ) * I)), g_sq_char]
  have hb : (1 - (t : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have hpi : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 = (Real.pi : ℂ) / (1 - t * I) := by
    rw [one_div, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_inv_pow _ (by norm_num)]
  calc ((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ) *
        (((Real.sqrt Real.pi)⁻¹ : ℂ) * (Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ))
      = (((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2)⁻¹ * ((Real.pi / (1 - t * I)) ^ (1 / 2 : ℂ)) ^ 2 := by
        push_cast; ring
    _ = 1 / (1 - t * I) := by
        rw [hpi, hc]; field_simp

end

-- ===== from Q3b.lean =====
section

/-- Real Frobenius pairing `Re tr(Tᴴ Y)`, written entrywise. -/
noncomputable def pair {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) : ℝ :=
  ∑ a, ∑ b, (star (T a b) * Y a b).re

theorem pair_eq_trace {α β : Type*} [Fintype α] [Fintype β] (T Y : Matrix α β ℂ) :
    pair T Y = (trace (Tᴴ * Y)).re := by
  simp only [pair, trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

theorem pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ) :
    pair T T = ∑ a, ∑ b, ((T a b).re ^ 2 + (T a b).im ^ 2) := by
  simp only [pair]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp [Complex.mul_re]
  ring

theorem eq_zero_of_pair_self {α β : Type*} [Fintype α] [Fintype β] (T : Matrix α β ℂ)
    (h : pair T T = 0) : T = 0 := by
  rw [pair_self] at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => by positivity)).mp h
  ext a b
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => by positivity)).mp
    (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
  have hr : (T a b).re = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  have hi : (T a b).im = 0 := by nlinarith [sq_nonneg (T a b).re, sq_nonneg (T a b).im]
  exact Complex.ext (by simp [hr]) (by simp [hi])

/-- Characteristic function of the i.i.d. complex Gaussian array. -/
theorem sample_char (M N : ℕ) (τ : Matrix (Fin M) (Fin N) ℂ) :
    ∫ X, cexp ((pair τ (Matrix.of X) : ℂ) * I) ∂SpikedWishart.SoftEdge.sampleLaw M N =
      cexp (-((pair τ τ / 4 : ℝ) : ℂ)) := by
  have h1 : ∀ X : Fin M → Fin N → ℂ, cexp ((pair τ (Matrix.of X) : ℂ) * I) =
      ∏ m, ∏ j, cexp ((((τ m j).re * (X m j).re + (τ m j).im * (X m j).im : ℝ) : ℂ) * I) := by
    intro X
    simp only [pair, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl (fun m _ => Finset.prod_congr rfl (fun j _ => ?_))
    congr 3
    simp [Complex.mul_re]
  simp_rw [h1]
  unfold SpikedWishart.SoftEdge.sampleLaw
  rw [integral_fintype_prod_eq_prod (fun m (x : Fin N → ℂ) =>
    ∏ j, cexp ((((τ m j).re * (x j).re + (τ m j).im * (x j).im : ℝ) : ℂ) * I))]
  have h2 : ∀ m : Fin M, ∫ x : Fin N → ℂ, ∏ j, cexp ((((τ m j).re * (x j).re +
        (τ m j).im * (x j).im : ℝ) : ℂ) * I) ∂(Measure.pi fun _ => SpikedWishart.SoftEdge.stdComplexGaussian) =
      ∏ j, cexp (-((((τ m j).re ^ 2 + (τ m j).im ^ 2) / 4 : ℝ) : ℂ)) := by
    intro m
    rw [integral_fintype_prod_eq_prod (fun j (z : ℂ) =>
      cexp ((((τ m j).re * z.re + (τ m j).im * z.im : ℝ) : ℂ) * I))]
    exact Finset.prod_congr rfl (fun j _ => cg_char _ _)
  simp_rw [h2]
  rw [pair_self]
  simp only [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The pairing as an `ℝ`-bilinear map on arrays. -/
noncomputable def Lpair (M N : ℕ) :
    (Fin M → Fin N → ℂ) →ₗ[ℝ] (Fin M → Fin N → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => pair (Matrix.of w) (Matrix.of v))
    (fun v1 v2 w => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, mul_add, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)
    (fun v w1 w2 => by
      simp only [pair, Matrix.of_apply, Pi.add_apply, star_add, add_mul, Complex.add_re,
        Finset.sum_add_distrib])
    (fun r v w => by
      simp only [pair, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Complex.real_smul]; simp [Complex.mul_re]; ring)

theorem Lpair_apply (M N : ℕ) (v w : Fin M → Fin N → ℂ) :
    Lpair M N v w = pair (Matrix.of w) (Matrix.of v) := rfl

theorem continuous_Lpair (M N : ℕ) :
    Continuous fun p : (Fin M → Fin N → ℂ) × (Fin M → Fin N → ℂ) => Lpair M N p.1 p.2 := by
  simp only [Lpair_apply, pair, Matrix.of_apply]
  fun_prop

theorem continuous_pair_of {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => pair T (Matrix.of X)) := by
  simp only [pair, Matrix.of_apply]
  fun_prop

theorem continuous_char_pair {M N : ℕ} (T : Matrix (Fin M) (Fin N) ℂ) :
    Continuous (fun X : Fin M → Fin N → ℂ => cexp ((pair T (Matrix.of X) : ℂ) * I)) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_pair_of T)).mul
    continuous_const)

theorem conjTranspose_map_star {α β : Type*} (Q : Matrix α β ℂ) : (Q.map star)ᴴ = Qᵀ := by
  ext i j; simp

theorem transpose_mul_map_star {α : Type*} [Fintype α] [DecidableEq α] (Q : Matrix α α ℂ)
    (hQ : Q ∈ unitaryGroup α ℂ) : Qᵀ * Q.map star = 1 := by
  have h := mem_unitaryGroup_iff'.mp hQ
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

theorem map_star_mul_transpose {α : Type*} [Fintype α] [DecidableEq α] (P : Matrix α α ℂ)
    (hP : P ∈ unitaryGroup α ℂ) : P.map star * Pᵀ = 1 := by
  have h := mem_unitaryGroup_iff.mp hP
  ext i j
  have := congrArg star (congrFun (congrFun h i) j)
  simp only [mul_apply, star_apply, Matrix.one_apply, transpose_apply, map_apply, star_sum,
    star_mul', star_star] at this ⊢
  rw [this]
  split_ifs <;> simp

/-- Moving a two-sided unitary action across the pairing. -/
theorem pair_unitary {M N : ℕ} (W Y : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) :
    pair W ((P * Yᵀ * Q)ᵀ) = pair (Q.map star * W * P.map star) Y := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [transpose_mul, transpose_mul, transpose_transpose, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_map_star, conjTranspose_map_star]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

theorem pair_unitary_self {M N : ℕ} (W : Matrix (Fin M) (Fin N) ℂ) (P : Matrix (Fin N) (Fin N) ℂ)
    (Q : Matrix (Fin M) (Fin M) ℂ) (hP : P ∈ unitaryGroup (Fin N) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    pair (Q.map star * W * P.map star) (Q.map star * W * P.map star) = pair W W := by
  rw [pair_eq_trace, pair_eq_trace]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_map_star, conjTranspose_map_star]
  have e : Pᵀ * (Wᴴ * Qᵀ) * (Q.map star * W * P.map star) =
      Pᵀ * (Wᴴ * (Qᵀ * Q.map star) * W) * P.map star := by
    simp only [Matrix.mul_assoc]
  rw [e, transpose_mul_map_star Q hQ, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    map_star_mul_transpose P hP, Matrix.one_mul]

/-- Unitary invariance of the i.i.d. complex Gaussian array under `H ↦ P H Q`
(`H = (of X)ᵀ`). -/
theorem sample_invariant (M N : ℕ) (P : Matrix (Fin N) (Fin N) ℂ) (Q : Matrix (Fin M) (Fin M) ℂ)
    (hP : P ∈ unitaryGroup (Fin N) ℂ) (hQ : Q ∈ unitaryGroup (Fin M) ℂ) :
    (SpikedWishart.SoftEdge.sampleLaw M N).map
        (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) =
      SpikedWishart.SoftEdge.sampleLaw M N := by
  have hmeas : Measurable (fun X : Fin M → Fin N → ℂ => fun m j => (P * (Matrix.of X)ᵀ * Q) j m) := by
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have : IsProbabilityMeasure ((SpikedWishart.SoftEdge.sampleLaw M N).map
      (fun X => fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one
    (L := Lpair M N) ?_ (continuous_Lpair M N) ?_
  · intro v hv h0
    apply hv
    have : Lpair M N v v = 0 := by rw [h0]; rfl
    rw [Lpair_apply] at this
    have := eq_zero_of_pair_self _ this
    funext m j
    exact congrFun (congrFun this m) j
  · intro w
    simp only [BoundedContinuousFunction.char_apply, Real.probChar_apply, Lpair_apply]
    rw [integral_map hmeas.aemeasurable (continuous_char_pair _).aestronglyMeasurable]
    have h3 : ∀ X : Fin M → Fin N → ℂ,
        pair (Matrix.of w) (Matrix.of (fun m j => (P * (Matrix.of X)ᵀ * Q) j m)) =
          pair (Q.map star * Matrix.of w * P.map star) (Matrix.of X) := by
      intro X
      rw [← pair_unitary]
      rfl
    simp_rw [h3]
    rw [sample_char, sample_char, pair_unitary_self _ _ _ hP hQ]

end

-- ===== from W5a.lean =====
section

namespace Weyl

/-- Density of the standard exponential law. -/
noncomputable def dexp (w : ℝ) : ℝ := (Set.Ioi (0 : ℝ)).indicator (fun w => Real.exp (-w)) w

theorem dexp_nonneg (w : ℝ) : 0 ≤ dexp w := by
  unfold dexp; by_cases h : w ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem h]

theorem measurable_dexp : Measurable dexp :=
  (Real.continuous_exp.comp continuous_neg).measurable.indicator measurableSet_Ioi

/-- The standard exponential law `Exp(1)`. -/
noncomputable def exp1 : Measure ℝ := volume.withDensity (fun w => ENNReal.ofReal (dexp w))

theorem integrable_dexp : Integrable dexp := by
  unfold dexp
  rw [integrable_indicator_iff measurableSet_Ioi]
  have := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  simpa using this

theorem integral_dexp : ∫ w, dexp w = 1 := by
  unfold dexp
  rw [integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi_zero]

theorem isProb_exp1 : IsProbabilityMeasure exp1 := by
  constructor
  rw [exp1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_dexp (Eventually.of_forall dexp_nonneg),
    integral_dexp, ENNReal.ofReal_one]

theorem integral_exp1 (g : ℝ → ℂ) : ∫ w, g w ∂exp1 = ∫ w in Set.Ioi 0, (Real.exp (-w) : ℂ) * g w := by
  have hm : Measurable (fun w => (dexp w).toNNReal) := measurable_dexp.real_toNNReal
  rw [exp1, show (fun w => ENNReal.ofReal (dexp w)) = (fun w => (((dexp w).toNNReal : NNReal) : ENNReal))
    from rfl, integral_withDensity_eq_integral_smul hm]
  unfold dexp
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext w
  by_cases h : w ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le,
      Complex.real_smul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

theorem charFun_exp1 (t : ℝ) : charFun exp1 t = 1 / (1 - t * I) := by
  rw [charFun_apply_real, integral_exp1]
  have h : ∀ w : ℝ, (Real.exp (-w) : ℂ) * cexp (t * w * I) = cexp ((t * I - 1) * w) := by
    intro w; rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [h]
  have hre : (t * I - 1 : ℂ).re < 0 := by simp
  rw [integral_exp_mul_complex_Ioi hre 0]
  have hne : (t * I - 1 : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
  have hne2 : (1 - t * I : ℂ) ≠ 0 := by
    intro h0; apply hne; linear_combination -h0
  field_simp
  simp

theorem isProb_cg : IsProbabilityMeasure SpikedWishart.SoftEdge.stdComplexGaussian := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian
  exact Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- `|g|²` of a standard complex Gaussian is `Exp(1)`. -/
theorem map_normSq_cg : SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq = exp1 := by
  have := isProb_cg
  have := isProb_exp1
  have : IsProbabilityMeasure (SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_exp1, charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  have := cg_normSq_char t
  convert this using 3
  push_cast; ring_nf

end Weyl

end

-- ===== from W5b.lean =====
section

namespace Weyl

/-- Lebesgue integral of a product over `ℝ^n`. -/
theorem lintegral_pi_prod {n : ℕ} (f : Fin n → ℝ → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → ℝ, ∏ i, f i (x i) = ∏ i, ∫⁻ t, f i t := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul]
    rw [volume_pi, Measure.pi_univ]
    simp
  | succ n ih =>
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    rw [← he.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hpt : ∀ y : ℝ × (Fin n → ℝ),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm y i) =
          f 0 y.1 * ∏ i : Fin n, f i.succ (y.2 i) := by
      intro y
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
    simp_rw [hpt]
    rw [Measure.volume_eq_prod, lintegral_prod_mul (f := f 0)
      (g := fun x' : Fin n → ℝ => ∏ i : Fin n, f i.succ (x' i)) (hf 0).aemeasurable
      (Finset.measurable_prod (f := fun (i : Fin n) (x' : Fin n → ℝ) => f i.succ (x' i)) Finset.univ
        (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable,
      ih (fun i => f i.succ) (fun i => hf i.succ), Fin.prod_univ_succ]

/-- The product of `n` exponential laws has density `∏ dexp(w_i)`. -/
theorem pi_exp1 (n : ℕ) :
    Measure.pi (fun _ : Fin n => exp1) =
      volume.withDensity (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) := by
  have := isProb_exp1
  refine Measure.pi_eq (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : (Set.pi Set.univ s).indicator (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) =
      fun w => ∏ i, (s i).indicator (fun t => ENNReal.ofReal (dexp t)) (w i) := by
    funext w
    by_cases hw : w ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hw]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [Set.indicator_of_mem (hw i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hw]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hw
      obtain ⟨i, hi⟩ := hw
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
  rw [hpt, lintegral_pi_prod _ (fun i => (measurable_dexp.ennreal_ofReal).indicator (hs i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [lintegral_indicator (hs i), exp1, withDensity_apply _ (hs i)]

end Weyl

end

-- ===== from W5c.lean =====
section

namespace Weyl

/-- Bordered Hermitian matrix `[[K, b], [bᴴ, c]]`. -/
noncomputable def blk {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks K (Matrix.of fun i (_ : Fin 1) => b i) (Matrix.of fun (_ : Fin 1) j => star (b j))
      (Matrix.of fun _ _ => (c : ℂ)))

theorem blk_cc {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) (i j : Fin n) :
    blk K b c (Fin.castSucc i) (Fin.castSucc j) = K i j := by
  simp [blk, reindex_apply]

theorem blk_cl {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) (i : Fin n) :
    blk K b c (Fin.castSucc i) (Fin.last n) = b i := by
  simp [blk, reindex_apply]

theorem blk_lc {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) (j : Fin n) :
    blk K b c (Fin.last n) (Fin.castSucc j) = star (b j) := by
  simp [blk, reindex_apply]

theorem blk_ll {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (c : ℝ) :
    blk K b c (Fin.last n) (Fin.last n) = c := by
  simp [blk, reindex_apply]

/-- Splitting off the last coordinate of an i.i.d. vector. -/
theorem mp_lastSplit {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (n : ℕ) :
    MeasurePreserving (fun r : Fin (n + 1) → X => (r (Fin.last n), fun j : Fin n => r (Fin.castSucc j)))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n)
  convert h using 1
  funext r
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.succAbove_last]
  try rfl

end Weyl

end

-- ===== from W5d.lean =====
section

namespace Weyl

theorem mp_normSqvec (n : ℕ) :
    MeasurePreserving (fun b : Fin n → ℂ => fun i => Complex.normSq (b i))
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
      (Measure.pi fun _ : Fin n => exp1) := by
  have := isProb_cg
  have := isProb_exp1
  have hsf : ∀ _ : Fin n, SigmaFinite (SpikedWishart.SoftEdge.stdComplexGaussian.map Complex.normSq) :=
    fun _ => by rw [map_normSq_cg]; infer_instance
  refine ⟨measurable_pi_lambda _ (fun i => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.pi_map_pi (fun _ => Complex.continuous_normSq.measurable.aemeasurable)]
  simp only [map_normSq_cg]

end Weyl

end

-- ===== from W6a.lean =====
section

namespace Weyl

/-- Entrywise measurable structure on square complex matrices. -/
noncomputable def matMS (m : ℕ) : MeasurableSpace (Matrix (Fin m) (Fin m) ℂ) := MeasurableSpace.pi

attribute [local instance] matMS

theorem matBorel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

attribute [local instance] matBorel

theorem of_zero_col (n : ℕ) : (Matrix.of fun (_ : Fin n) (_ : Fin 1) => (0 : ℂ)) = 0 := by ext; simp

theorem of_zero_row (n : ℕ) : (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (0 : ℂ)) = 0 := by ext; simp

/-- Unitary invariance of a standard complex Gaussian vector. -/
theorem piCG_unitary {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun b : Fin n → ℂ => P *ᵥ b)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) := by
  have := isProb_cg
  have he : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℂ))
      (SpikedWishart.SoftEdge.sampleLaw 1 n)
      (Measure.pi fun _ : Fin n => SpikedWishart.SoftEdge.stdComplexGaussian) :=
    measurePreserving_funUnique _ _
  have hT : MeasurePreserving
      (fun X : Fin 1 → Fin n → ℂ => fun m j => (P * (Matrix.of X)ᵀ * (1 : Matrix (Fin 1) (Fin 1) ℂ)) j m)
      (SpikedWishart.SoftEdge.sampleLaw 1 n) (SpikedWishart.SoftEdge.sampleLaw 1 n) := by
    refine ⟨?_, sample_invariant 1 n P 1 hP (one_mem _)⟩
    apply Continuous.measurable
    simp only [mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  have hc := he.comp (hT.comp he.symm)
  convert hc using 1
  funext b
  ext j
  simp [MeasurableEquiv.funUnique, mulVec, dotProduct, mul_apply]

theorem ofOne : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (((1 : ℝ)) : ℂ)) = 1 := by
  ext i j
  simp [Matrix.one_apply, Subsingleton.elim i j]

theorem blk_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    blk U 0 1 ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  unfold blk
  simp only [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv,
    fromBlocks_conjTranspose, fromBlocks_multiply, ofOne, Pi.zero_apply, star_zero, of_zero_col,
    of_zero_row, conjTranspose_zero, conjTranspose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one, hUU, fromBlocks_one, submatrix_one_equiv]

theorem measurableSet_Vpos (n : ℕ) : MeasurableSet (Vpos n) := by
  have : Vpos n = ⋂ i : Fin n, {y : Fin (n + 1) → ℝ | 0 < y (Fin.castSucc i)} := by
    ext y; simp [Vpos]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply _)

end Weyl

end

-- ===== from W6b.lean =====
section

namespace Weyl

attribute [local instance] matMS matBorel

end Weyl

end

end SpikedWishart.Separated.Lib

-- ===== from S0.lean =====


open MeasureTheory Set Matrix
open scoped ComplexOrder Pointwise

namespace SWL302Eig

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem isHermitian_smul_one_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    ((x : ℂ) • (1 : Matrix n n ℂ) - A).IsHermitian := by
  refine IsHermitian.sub ?_ hA
  simp [IsHermitian, conjTranspose_smul]

/-- The eigenvalues of `x - A` are the `x - λ_j(A)`, as a statement about any property. -/
theorem forall_eig_smul_one_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) (P : ℝ → Prop) :
    (∀ i, P ((isHermitian_smul_one_sub hA x).eigenvalues i)) ↔ ∀ j, P (x - hA.eigenvalues j) := by
  set hH := isHermitian_smul_one_sub hA x
  have hs : spectrum ℂ ((x : ℂ) • (1 : Matrix n n ℂ) - A) = ({(x : ℂ)} : Set ℂ) - spectrum ℂ A := by
    rw [← Algebra.algebraMap_eq_smul_one, spectrum.singleton_sub_eq]
  rw [hH.spectrum_eq_image_range, hA.spectrum_eq_image_range] at hs
  constructor
  · intro h j
    have hmem : ((x - hA.eigenvalues j : ℝ) : ℂ) ∈ (RCLike.ofReal '' Set.range hH.eigenvalues : Set ℂ) := by
      rw [hs]
      exact Set.mem_sub.mpr ⟨x, rfl, _, ⟨_, ⟨j, rfl⟩, rfl⟩, by push_cast; rfl⟩
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hmem
    have : hH.eigenvalues i = x - hA.eigenvalues j := RCLike.ofReal_injective hi
    rw [← this]; exact h i
  · intro h i
    have hmem : ((hH.eigenvalues i : ℝ) : ℂ) ∈ ({(x : ℂ)} - RCLike.ofReal '' Set.range hA.eigenvalues : Set ℂ) := by
      rw [← hs]; exact ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨y, hy, z, ⟨_, ⟨j, rfl⟩, rfl⟩, hyz⟩ := Set.mem_sub.mp hmem
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have : hH.eigenvalues i = x - hA.eigenvalues j := by
      have h2 : ((x - hA.eigenvalues j : ℝ) : ℂ) = ((hH.eigenvalues i : ℝ) : ℂ) := by
        rw [← hyz]; push_cast; rfl
      exact_mod_cast h2.symm
    rw [this]; exact h j

theorem eig_le_iff_posSemidef {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : ℝ) :
    (∀ j, hA.eigenvalues j ≤ x) ↔ ((x : ℂ) • (1 : Matrix n n ℂ) - A).PosSemidef := by
  rw [(isHermitian_smul_one_sub hA x).posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  simp only [Pi.zero_apply]
  rw [forall_eig_smul_one_sub hA x (fun t => 0 ≤ t)]
  simp only [sub_nonneg]
end SWL302Eig

namespace SWL302

open SpikedWishart.FixedDim

noncomputable def matMS (m : ℕ) : MeasurableSpace (Matrix (Fin m) (Fin m) ℂ) := MeasurableSpace.pi

attribute [local instance] matMS

theorem matBorel (m : ℕ) : BorelSpace (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (BorelSpace (Fin m → Fin m → ℂ))

attribute [local instance] matBorel

theorem isClosed_psdSet {k : ℕ} (x : ℝ) :
    IsClosed {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} := by
  have : OrderClosedTopology ℂ := Complex.orderClosedTopology
  have hset : {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef} =
      {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A)ᴴ =
        (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A} ∩
      ⋂ v : Fin k → ℂ, {A : Matrix (Fin k) (Fin k) ℂ |
        0 ≤ star v ⬝ᵥ (((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) *ᵥ v)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [hset]
  have hc : Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) :=
    continuous_const.sub continuous_id
  refine (isClosed_eq hc.matrix_conjTranspose hc).inter (isClosed_iInter fun v => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (hc.matrix_mulVec continuous_const)

theorem psd_conj {k : ℕ} (x : ℝ) {U : Matrix (Fin k) (Fin k) ℂ} (hU : U ∈ unitaryGroup (Fin k) ℂ)
    {A : Matrix (Fin k) (Fin k) ℂ} (h : ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef) :
    ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - U * A * star U).PosSemidef := by
  have hUU : U * star U = 1 := mem_unitaryGroup_iff.mp hU
  have e1 : U * ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A) * star U =
      (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - U * A * star U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU]
  rw [← e1, star_eq_conjTranspose]
  exact h.mul_mul_conjTranspose_same U

theorem psd_conj_iff {k : ℕ} (x : ℝ) {U : Matrix (Fin k) (Fin k) ℂ} (hU : U ∈ unitaryGroup (Fin k) ℂ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - U * A * star U).PosSemidef ↔
      ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef := by
  refine ⟨fun h => ?_, psd_conj x hU⟩
  have hU' : star U ∈ unitaryGroup (Fin k) ℂ := Unitary.star_mem hU
  have h2 := psd_conj x hU' h
  have hUU' : star U * U = 1 := mem_unitaryGroup_iff'.mp hU
  have e : star U * (U * A * star U) * star (star U) = A := by
    rw [star_star, Matrix.mul_assoc, Matrix.mul_assoc, hUU', Matrix.mul_one, ← Matrix.mul_assoc, hUU',
      Matrix.one_mul]
  rwa [e] at h2

theorem diag_psd_iff {k : ℕ} (x : ℝ) (ξ : Fin k → ℝ) :
    ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - diagonal fun i => (ξ i : ℂ)).PosSemidef ↔
      ξ ∈ Set.pi Set.univ (fun _ : Fin k => Set.Iic x) := by
  have e : (x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - (diagonal fun i => (ξ i : ℂ)) =
      diagonal fun i => ((x - ξ i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, one_apply]
  rw [e, posSemidef_diagonal_iff]
  simp only [Complex.zero_le_real, sub_nonneg, Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]

/-- The unnormalised Wishart matrix `W = Σ_m g_m g_mᴴ`. -/
noncomputable def Wm {M k : ℕ} (G : Fin M → Fin k → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => ∑ m, G m i * star (G m j)

theorem continuous_Wm (M k : ℕ) : Continuous (fun G : Fin M → Fin k → ℂ => Wm G) := by
  unfold Wm
  fun_prop

theorem ind_psd_conj {k : ℕ} (x : ℝ) {U : Matrix (Fin k) (Fin k) ℂ} (hU : U ∈ unitaryGroup (Fin k) ℂ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator (1 : Matrix (Fin k) (Fin k) ℂ → ENNReal) (U * A * star U) =
      {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator (1 : Matrix (Fin k) (Fin k) ℂ → ENNReal) A := by
  by_cases h : ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef
  · rw [Set.indicator_of_mem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) ((psd_conj_iff x hU A).mpr h),
      Set.indicator_of_mem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) h]
    rfl
  · rw [Set.indicator_of_notMem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) (fun h' => h ((psd_conj_iff x hU A).mp h')),
      Set.indicator_of_notMem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) h]

theorem ind_diag {k : ℕ} (x : ℝ) (ξ : Fin k → ℝ) :
    {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}.indicator (1 : Matrix (Fin k) (Fin k) ℂ → ENNReal) (diagonal fun i => (ξ i : ℂ)) =
      (Set.pi Set.univ (fun _ : Fin k => Set.Iic x)).indicator 1 ξ := by
  by_cases h : ξ ∈ Set.pi Set.univ (fun _ : Fin k => Set.Iic x)
  · rw [Set.indicator_of_mem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) ((diag_psd_iff x ξ).mpr h), Set.indicator_of_mem h]
    rfl
  · rw [Set.indicator_of_notMem (s := {A : Matrix (Fin k) (Fin k) ℂ | ((x : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) - A).PosSemidef}) (fun h' => h ((diag_psd_iff x ξ).mp h')),
      Set.indicator_of_notMem h]

/-! ## Array form of the Weyl formula (A2) and its consequence `LagWeyl` -/

/-- The `M × k` matrix with `√x_j` at `(j, j)` and zeros elsewhere. -/
noncomputable def Emb (M k : ℕ) (x : Fin k → ℝ) : Matrix (Fin M) (Fin k) ℂ :=
  fun m j => if (m : ℕ) = j then ((Real.sqrt (x j) : ℝ) : ℂ) else 0

theorem Wm_eq {M k : ℕ} (G : Matrix (Fin M) (Fin k) ℂ) : Wm G = (Gᴴ * G)ᵀ := by
  ext i j
  simp only [Wm, transpose_apply, Matrix.mul_apply, conjTranspose_apply]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem Wm_mul_left {M k : ℕ} {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ)
    (G : Matrix (Fin M) (Fin k) ℂ) : Wm (Q * G) = Wm G := by
  have h : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  rw [star_eq_conjTranspose] at h
  rw [Wm_eq, Wm_eq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, h, Matrix.one_mul]

theorem ct_transpose {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : Aᵀᴴ = Aᴴᵀ := by
  ext i j; rfl

theorem transpose_mem_unitary {k : ℕ} {V : Matrix (Fin k) (Fin k) ℂ} (hV : V ∈ unitaryGroup (Fin k) ℂ) :
    Vᵀ ∈ unitaryGroup (Fin k) ℂ := by
  rw [mem_unitaryGroup_iff]
  have h : star V * V = 1 := mem_unitaryGroup_iff'.mp hV
  rw [star_eq_conjTranspose, ct_transpose, ← transpose_mul, ← star_eq_conjTranspose, h, transpose_one]

theorem Wm_mul_right {M k : ℕ} (G : Matrix (Fin M) (Fin k) ℂ) (V : Matrix (Fin k) (Fin k) ℂ) :
    Wm (G * V) = Vᵀ * Wm G * star (Vᵀ) := by
  rw [Wm_eq, Wm_eq, conjTranspose_mul, star_eq_conjTranspose, ct_transpose,
    show Vᴴ * Gᴴ * (G * V) = Vᴴ * (Gᴴ * G) * V by simp only [Matrix.mul_assoc],
    transpose_mul, transpose_mul, Matrix.mul_assoc]

theorem Wm_Emb {M k : ℕ} (hk : k ≤ M) (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) :
    Wm (Emb M k x) = diagonal fun i => (x i : ℂ) := by
  ext i j
  unfold Wm Emb
  rw [Finset.sum_eq_single (Fin.castLE hk i)]
  · by_cases hij : i = j
    · subst hij
      simp only [Fin.coe_castLE, if_true, diagonal_apply_eq, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hx i)]
    · have : ¬ ((Fin.castLE hk i : ℕ) = j) := fun h => hij (Fin.ext (by simpa using h))
      simp [this, hij]
      exact Or.inr fun h => absurd (Fin.ext h) hij
  · intro m _ hm
    have : ¬ ((m : ℕ) = i) := fun h => hm (Fin.ext (by simpa using h))
    simp [this]
  · simp

/-- Polar step: a matrix with diagonal Gram matrix is a unitary times `Emb`. -/
theorem exists_unitary_of_gram {M k : ℕ} (hk : k ≤ M) (N : Matrix (Fin M) (Fin k) ℂ) (x : Fin k → ℝ)
    (hx : ∀ j, 0 < x j) (hN : Nᴴ * N = diagonal fun j => (x j : ℂ)) :
    ∃ Q ∈ unitaryGroup (Fin M) ℂ, N = Q * Emb M k x := by
  classical
  have hs0 : ∀ j, ((Real.sqrt (x j) : ℝ) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (Real.sqrt_pos.mpr (hx j)).ne'
  have hgram : ∀ i j, ∑ m, star (N m i) * N m j = if i = j then (x i : ℂ) else 0 := by
    intro i j
    have := congrFun (congrFun hN i) j
    rw [Matrix.mul_apply, diagonal_apply] at this
    simpa [conjTranspose_apply] using this
  let u : Fin k → EuclideanSpace ℂ (Fin M) :=
    fun j => WithLp.toLp 2 (fun m => N m j / ((Real.sqrt (x j) : ℝ) : ℂ))
  have hon : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [PiLp.inner_apply]
    have e : ∀ m, inner ℂ (u i m) (u j m) =
        star (N m i) * N m j / (((Real.sqrt (x i) : ℝ) : ℂ) * ((Real.sqrt (x j) : ℝ) : ℂ)) := by
      intro m
      simp only [u, PiLp.toLp_apply, RCLike.inner_apply, map_div₀, Complex.conj_ofReal]
      rw [Complex.star_def]
      field_simp
    rw [Finset.sum_congr rfl fun m _ => e m, ← Finset.sum_div, hgram]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hx i).le]
      exact div_self (by exact_mod_cast (hx i).ne')
    · exact zero_div _
  let v : Fin M → EuclideanSpace ℂ (Fin M) := fun m => if h : (m : ℕ) < k then u ⟨m, h⟩ else 0
  let s : Set (Fin M) := {m | (m : ℕ) < k}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    have e : s.domRestrict v = u ∘ (fun m : s => (⟨m.1, m.2⟩ : Fin k)) := by
      funext m
      simp only [Set.domRestrict, Function.comp_apply, v]
      exact dif_pos (show ((m : Fin M) : ℕ) < k from m.2)
    rw [e]
    refine hon.comp _ fun a b h => ?_
    exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val h))
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun a m => b m a, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    ext m m'
    rw [Matrix.mul_apply, one_apply]
    simp only [Matrix.star_apply, Matrix.of_apply]
    have h := orthonormal_iff_ite.mp b.orthonormal m m'
    rw [PiLp.inner_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [RCLike.inner_apply]
    ring
  · ext m j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hk j)]
    simp only [Matrix.of_apply]
    · have hmem : Fin.castLE hk j ∈ s := by simp [s]
      rw [hb _ hmem]
      simp only [v, Fin.coe_castLE, dif_pos j.2, Emb, if_true, u, PiLp.toLp_apply]
      rw [div_mul_cancel₀ _ (hs0 j)]
    · intro a _ ha
      have : ¬ ((a : ℕ) = j) := fun h => ha (Fin.ext (by simpa using h))
      simp [Emb, this]
    · simp

end SWL302

-- ===== from S1.lean =====

/-! S1: column split of the Gaussian array and the border average `hW` with its invariances.
Needs (prefix) 53ec8574_w6b.lean and the main draft d80e94b4.lean. -/

namespace SWL302

open MeasureTheory Matrix SpikedWishart.FixedDim

/-- The standard complex Gaussian vector on `ℂ^M`. -/
noncomputable def cgv (M : ℕ) : Measure (Fin M → ℂ) := Measure.pi fun _ => stdComplexGaussian

theorem cgv.isProb (M : ℕ) : IsProbabilityMeasure (cgv M) := by
  unfold cgv; infer_instance

attribute [local instance] cgv.isProb

/-- Append the column `g` to the array `G'`. -/
def join {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) : Fin M → Fin (n + 1) → ℂ :=
  fun m => Fin.snoc (G' m) (g m)

theorem join_castSucc {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) (m : Fin M) (j : Fin n) :
    join G' g m (Fin.castSucc j) = G' m j := by
  simp [join]

theorem join_last {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) (m : Fin M) :
    join G' g m (Fin.last n) = g m := by
  simp [join]

theorem continuous_join (M n : ℕ) :
    Continuous (fun p : (Fin M → Fin n → ℂ) × (Fin M → ℂ) => join p.1 p.2) := by
  refine continuous_pi fun m => continuous_pi fun j => ?_
  induction j using Fin.lastCases with
  | last => simp only [join_last]; fun_prop
  | cast j => simp only [join_castSucc]; fun_prop

theorem mp_colSplit (M n : ℕ) :
    MeasurePreserving
      (fun G : Fin M → Fin (n + 1) → ℂ => ((fun m j => G m (Fin.castSucc j)), fun m => G m (Fin.last n)))
      (sampleLaw M (n + 1)) ((sampleLaw M n).prod (cgv M)) := by
  have hrow : MeasurePreserving
      (fun r : Fin (n + 1) → ℂ => ((fun j => r (Fin.castSucc j)), r (Fin.last n)))
      (Measure.pi fun _ => stdComplexGaussian)
      ((Measure.pi fun _ : Fin n => stdComplexGaussian).prod stdComplexGaussian) :=
    Measure.measurePreserving_swap.comp
      (SpikedWishart.Separated.Lib.Weyl.mp_lastSplit stdComplexGaussian n)
  have hpi := measurePreserving_pi (fun _ : Fin M => Measure.pi fun _ : Fin (n + 1) => stdComplexGaussian)
    (fun _ => (Measure.pi fun _ : Fin n => stdComplexGaussian).prod stdComplexGaussian) (fun _ => hrow)
  have h3 := measurePreserving_arrowProdEquivProdArrow (Fin n → ℂ) ℂ (Fin M)
    (fun _ => Measure.pi fun _ : Fin n => stdComplexGaussian) (fun _ => stdComplexGaussian)
  exact h3.comp hpi

/-- Border average: integrate out the last column. -/
noncomputable def hW {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (G' : Fin M → Fin n → ℂ) : ENNReal :=
  ∫⁻ g, F (join G' g) ∂(cgv M)

theorem measurable_hW {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F) :
    Measurable (hW F) :=
  (hFm.comp (continuous_join M n).measurable).lintegral_prod_right'

theorem step_eq2 {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F) :
    ∫⁻ G, F G ∂(sampleLaw M (n + 1)) = ∫⁻ G', hW F G' ∂(sampleLaw M n) := by
  have hj : ∀ G : Fin M → Fin (n + 1) → ℂ,
      join (fun m j => G m (Fin.castSucc j)) (fun m => G m (Fin.last n)) = G := by
    intro G; funext m; exact Fin.snoc_init_self (G m)
  have hm : Measurable (fun p : (Fin M → Fin n → ℂ) × (Fin M → ℂ) => F (join p.1 p.2)) :=
    hFm.comp (continuous_join M n).measurable
  calc ∫⁻ G, F G ∂(sampleLaw M (n + 1))
      = ∫⁻ G, (fun p : (Fin M → Fin n → ℂ) × (Fin M → ℂ) => F (join p.1 p.2))
          ((fun m j => G m (Fin.castSucc j)), fun m => G m (Fin.last n)) ∂(sampleLaw M (n + 1)) := by
        simp only [hj]
    _ = ∫⁻ p, F (join p.1 p.2) ∂((sampleLaw M n).prod (cgv M)) := (mp_colSplit M n).lintegral_comp hm
    _ = _ := lintegral_prod _ hm.aemeasurable

theorem join_mul_left {M n : ℕ} {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ)
    (G' : Matrix (Fin M) (Fin n) ℂ) (g : Fin M → ℂ) :
    join (Q * G') g = Q * Matrix.of (join G' (star Q *ᵥ g)) := by
  have hQQ : Q * star Q = 1 := mem_unitaryGroup_iff.mp hQ
  funext m j
  induction j using Fin.lastCases with
  | last =>
    simp only [join, Fin.snoc_last, Matrix.mul_apply, Matrix.of_apply]
    change g m = (Q *ᵥ (star Q *ᵥ g)) m
    rw [mulVec_mulVec, hQQ, one_mulVec]
  | cast j =>
    simp only [join, Fin.snoc_castSucc, Matrix.mul_apply, Matrix.of_apply]

theorem hW_left {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F)
    (hF : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ) (G' : Matrix (Fin M) (Fin n) ℂ) :
    hW F (Q * G') = hW F G' := by
  have hmp : MeasurePreserving (fun g : Fin M → ℂ => star Q *ᵥ g) (cgv M) (cgv M) := by
    have := SpikedWishart.Separated.Lib.Weyl.piCG_unitary (star Q) (Unitary.star_mem hQ)
    exact this
  have hf : Measurable (fun g : Fin M → ℂ => F (join G' g)) :=
    hFm.comp ((continuous_join M n).comp (continuous_const.prodMk continuous_id)).measurable
  unfold hW
  rw [← hmp.lintegral_comp hf]
  refine lintegral_congr fun g => ?_
  rw [join_mul_left hQ G' g, hF Q hQ]
  rfl

theorem join_mul_right {M n : ℕ} (G' : Matrix (Fin M) (Fin n) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (g : Fin M → ℂ) :
    join (G' * V) g =
      Matrix.of (join G' g) * SpikedWishart.Separated.Lib.Weyl.blk V 0 1 := by
  funext m j
  induction j using Fin.lastCases with
  | last =>
    simp only [join, Fin.snoc_last, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, SpikedWishart.Separated.Lib.Weyl.blk_cl, SpikedWishart.Separated.Lib.Weyl.blk_ll]
    simp
  | cast j =>
    simp only [join, Fin.snoc_castSucc, Fin.snoc_last, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      SpikedWishart.Separated.Lib.Weyl.blk_cc, SpikedWishart.Separated.Lib.Weyl.blk_lc]
    simp

theorem hW_right {M n : ℕ} (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal)
    (hF : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ) (G' : Matrix (Fin M) (Fin n) ℂ) :
    hW F (G' * V) = hW F G' := by
  unfold hW
  refine lintegral_congr fun g => ?_
  rw [join_mul_right, hF _ (SpikedWishart.Separated.Lib.Weyl.blk_unitary hV)]
  rfl

end SWL302

-- ===== from S2.lean =====

/-! S2: Gram reduction. A bi-unitarily invariant `F` depends only on the unitary class of the Gram
matrix (when it is positive definite); the Gram matrix of `join (Emb μ) g` is a phase conjugate of
the arrow matrix `arrowC μ (√μ ‖g‖) (Σ ‖g‖²)`. Needs prefix 53ec8574_w6b.lean, d80e94b4.lean, S1. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

theorem gram_Emb {M k : ℕ} (hk : k ≤ M) (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) :
    (Emb M k x)ᴴ * Emb M k x = diagonal fun j => (x j : ℂ) := by
  have h := Wm_Emb hk x hx
  rw [Wm_eq] at h
  rw [← transpose_transpose ((Emb M k x)ᴴ * Emb M k x), h, diagonal_transpose]

/-- A bi-invariant `F` at a matrix with Gram matrix `W diag x Wᴴ`, `x > 0`. -/
theorem F_emb {M k : ℕ} (hk : k ≤ M) (F : (Fin M → Fin k → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G)
    (B : Matrix (Fin M) (Fin k) ℂ) {W : Matrix (Fin k) (Fin k) ℂ} (hW : W ∈ unitaryGroup (Fin k) ℂ)
    (x : Fin k → ℝ) (hx : ∀ j, 0 < x j) (h : Bᴴ * B = W * diagonal (fun j => (x j : ℂ)) * star W) :
    F B = F (Emb M k x) := by
  have h1 : star W * W = 1 := mem_unitaryGroup_iff'.mp hW
  have hg : (B * W)ᴴ * (B * W) = diagonal fun j => (x j : ℂ) := by
    rw [conjTranspose_mul, ← star_eq_conjTranspose W,
      show star W * Bᴴ * (B * W) = star W * (Bᴴ * B) * W by simp only [Matrix.mul_assoc], h]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨Q, hQ, hBW⟩ := exists_unitary_of_gram hk (B * W) x hx hg
  rw [← hR W hW B, hBW, hL Q hQ]

/-- `F` agrees on matrices whose Gram matrices are unitarily similar and positive definite. -/
theorem F_gram {M k : ℕ} (hk : k ≤ M) (F : (Fin M → Fin k → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G)
    (A B : Matrix (Fin M) (Fin k) ℂ) {V : Matrix (Fin k) (Fin k) ℂ} (hV : V ∈ unitaryGroup (Fin k) ℂ)
    (h : Aᴴ * A = V * (Bᴴ * B) * star V) (hpd : (Bᴴ * B).PosDef) : F A = F B := by
  have hH := hpd.isHermitian
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hU : (hH.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) ∈ unitaryGroup (Fin k) ℂ :=
    hH.eigenvectorUnitary.2
  have hd : (RCLike.ofReal ∘ hH.eigenvalues : Fin k → ℂ) = fun j => ((hH.eigenvalues j : ℝ) : ℂ) := rfl
  rw [hd] at hspec
  have hpos : ∀ j, 0 < hH.eigenvalues j := fun j => hpd.eigenvalues_pos j
  obtain ⟨U, hU, x, hx, hs⟩ : ∃ U ∈ unitaryGroup (Fin k) ℂ, ∃ x : Fin k → ℝ, (∀ j, 0 < x j) ∧
      Bᴴ * B = U * diagonal (fun j => (x j : ℂ)) * star U := ⟨_, hU, _, hpos, hspec⟩
  rw [F_emb hk F hL hR B hU x hx hs,
    F_emb hk F hL hR A (Submonoid.mul_mem _ hV hU) x hx ?_]
  rw [h, hs, star_mul]
  simp only [Matrix.mul_assoc]

/-- Unit phase of a complex number. -/
noncomputable def ph (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem ph_mul_norm (z : ℂ) : ph z * (‖z‖ : ℂ) = z := by
  unfold ph
  split_ifs with h
  · simp [h]
  · have h2 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [div_mul_cancel₀ _ h2]

theorem star_ph_mul_norm (z : ℂ) : star (ph z) * (‖z‖ : ℂ) = star z := by
  have h := congrArg star (ph_mul_norm z)
  rwa [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm] at h

theorem ph_mul_star (z : ℂ) : ph z * star (ph z) = 1 := by
  unfold ph
  split_ifs with h
  · simp
  · have h1 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have h2 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast h1
    rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    field_simp

/-- The phase matrix `diag(ph u_0, ..., ph u_{n-1}, 1)`. -/
noncomputable def Dm {n : ℕ} (u : Fin n → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  diagonal (Fin.snoc (α := fun _ => ℂ) (fun i => ph (u i)) 1)

theorem Dm_mem {n : ℕ} (u : Fin n → ℂ) : Dm u ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [mem_unitaryGroup_iff, Dm, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simpa using ph_mul_star (u i)

theorem Emb_castLE {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (i j : Fin n) :
    Emb M n μ (Fin.castLE h i) j = if i = j then ((Real.sqrt (μ j) : ℝ) : ℂ) else 0 := by
  unfold Emb
  simp only [Fin.val_castLE]
  by_cases hij : i = j
  · subst hij; simp
  · have : ¬ ((i : ℕ) = j) := fun e => hij (Fin.ext e)
    simp [this, hij]

theorem Emb_row_ge {M n : ℕ} (μ : Fin n → ℝ) (m : Fin M) (hm : n ≤ (m : ℕ)) (j : Fin n) :
    Emb M n μ m j = 0 := by
  unfold Emb
  have : ¬ ((m : ℕ) = j) := by omega
  simp [this]

theorem sum_Emb_col {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (i : Fin n) (f : Fin M → ℂ) :
    ∑ m, star (Emb M n μ m i) * f m = ((Real.sqrt (μ i) : ℝ) : ℂ) * f (Fin.castLE h i) := by
  rw [Finset.sum_eq_single (Fin.castLE h i)]
  · rw [Emb_castLE h μ i i, if_pos rfl, Complex.star_def, Complex.conj_ofReal]
  · intro m _ hm
    have : ¬ ((m : ℕ) = i) := fun e => hm (Fin.ext (by simpa using e))
    simp [Emb, this]
  · simp

theorem sum_col_Emb {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (j : Fin n) (f : Fin M → ℂ) :
    ∑ m, f m * Emb M n μ m j = f (Fin.castLE h j) * ((Real.sqrt (μ j) : ℝ) : ℂ) := by
  rw [Finset.sum_eq_single (Fin.castLE h j)]
  · rw [Emb_castLE h μ j j, if_pos rfl]
  · intro m _ hm
    have : ¬ ((m : ℕ) = j) := fun e => hm (Fin.ext (by simpa using e))
    simp [Emb, this]
  · simp

/-- Gram matrix of the bordered array. -/
theorem gram_join {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (g : Fin M → ℂ) :
    (Matrix.of (join (Emb M n μ) g))ᴴ *
        (Matrix.of (join (Emb M n μ) g)) =
      Dm (fun i => g (Fin.castLE h i)) *
        arrowC μ (fun i => Real.sqrt (μ i) * ‖g (Fin.castLE h i)‖) (∑ m, ‖g m‖ ^ 2) *
        star (Dm (fun i => g (Fin.castLE h i))) := by
  have hE := gram_Emb h μ hμ
  ext a b
  rw [Dm, star_eq_conjTranspose, diagonal_conjTranspose, mul_diagonal, diagonal_mul,
    Matrix.mul_apply]
  simp only [conjTranspose_apply, arrowC, Matrix.map_apply, Pi.star_apply, Matrix.of_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      simp only [join, Fin.snoc_last, arrowR_ll, star_one, one_mul, mul_one]
      push_cast
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    | cast j =>
      simp only [join, Fin.snoc_last, Fin.snoc_castSucc, arrowR_lc, one_mul]
      rw [sum_col_Emb h μ j (fun m => star (g m))]
      push_cast
      rw [mul_assoc, mul_comm (((‖g (Fin.castLE h j)‖ : ℝ)) : ℂ), star_ph_mul_norm, mul_comm]
  | cast i =>
    induction b using Fin.lastCases with
    | last =>
      simp only [join, Fin.snoc_last, Fin.snoc_castSucc, arrowR_cl, star_one,
        mul_one]
      rw [sum_Emb_col h μ i g]
      push_cast
      rw [mul_left_comm, ph_mul_norm]
    | cast j =>
      simp only [join, Fin.snoc_castSucc, arrowR_cc]
      have hij := congrFun (congrFun hE i) j
      rw [Matrix.mul_apply] at hij
      simp only [conjTranspose_apply] at hij
      rw [hij]
      by_cases hh : i = j
      · subst hh
        simp only [diagonal_apply_eq]
        rw [mul_comm, ← mul_assoc, mul_comm (star _), ph_mul_star, one_mul]
      · simp [diagonal_apply_ne _ hh]

/-- The bordered array has positive definite Gram matrix when `μ > 0` and `g_n ≠ 0`. -/
theorem posDef_join {M n : ℕ} (h : n + 1 ≤ M) (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) (g : Fin M → ℂ)
    (hg : g ⟨n, by omega⟩ ≠ 0) :
    ((Matrix.of (join (Emb M n μ) g))ᴴ *
        (Matrix.of (join (Emb M n μ) g))).PosDef := by
  set A := Matrix.of (join (Emb M n μ) g) with hA
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_self _) fun x hx => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, dotProduct_star_self_pos_iff]
  intro hAx
  have hrow : ∀ m, ∑ j : Fin n, Emb M n μ m j * x (Fin.castSucc j) + g m * x (Fin.last n) = 0 := by
    intro m
    have := congrFun hAx m
    rw [mulVec, dotProduct, Fin.sum_univ_castSucc] at this
    simpa [hA, join] using this
  have hlast : x (Fin.last n) = 0 := by
    have := hrow ⟨n, by omega⟩
    rw [Finset.sum_eq_zero fun j _ => by rw [Emb_row_ge μ _ (le_refl n), zero_mul], zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left hg
  have hcs : ∀ i : Fin n, x (Fin.castSucc i) = 0 := by
    intro i
    have := hrow (Fin.castLE (by omega) i)
    simp only [Emb_castLE, hlast, mul_zero, add_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    have hs : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (hμ i)).ne'
    exact (mul_eq_zero.mp this).resolve_left hs
  apply hx
  funext j
  induction j using Fin.lastCases with
  | last => exact hlast
  | cast i => exact hcs i

end SWL302

-- ===== from S3.lean =====

/-! S3: the normal form `N0 μ r s` of the bordered array and the two evaluations
`F (join (Emb μ) g) = F (N0 μ (rv g) (sv g))` (when `g_n ≠ 0`) and
`F (N0 μ r s) = F (Emb λ)` at the Dixon-Anderson point. Needs prefix + d80e94b4.lean + S1 + S2. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- Split `Fin M` into the first `n` and the remaining `M - n` indices. -/
def spl {M n : ℕ} (h : n ≤ M) : Fin M ≃ Fin n ⊕ Fin (M - n) :=
  (finCongr (by omega : M = n + (M - n))).trans finSumFinEquiv.symm

theorem spl_symm_inl {M n : ℕ} (h : n ≤ M) (a : Fin n) : (spl h).symm (Sum.inl a) = Fin.castLE h a := by
  apply Fin.ext; simp [spl]

theorem spl_castLE {M n : ℕ} (h : n ≤ M) (a : Fin n) : spl h (Fin.castLE h a) = Sum.inl a := by
  rw [← spl_symm_inl h a, Equiv.apply_symm_apply]

theorem spl_symm_inr_val {M n : ℕ} (h : n ≤ M) (b : Fin (M - n)) :
    (((spl h).symm (Sum.inr b) : Fin M) : ℕ) = n + b := by
  simp [spl]

theorem spl_n {M n : ℕ} (h : n + 1 ≤ M) :
    spl (by omega : n ≤ M) ⟨n, by omega⟩ = Sum.inr ⟨0, by omega⟩ := by
  apply (spl (by omega : n ≤ M)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [spl_symm_inr_val]
  simp

theorem sum_spl {M n : ℕ} (h : n ≤ M) (f : Fin M → ℝ) :
    ∑ m, f m = ∑ a : Fin n, f (Fin.castLE h a) + ∑ b : Fin (M - n), f ((spl h).symm (Sum.inr b)) := by
  rw [← Equiv.sum_comp (spl h).symm, Fintype.sum_sum_type]
  simp only [spl_symm_inl]

/-- The normal-form border column `(√r_0, ..., √r_{n-1}, √s, 0, ..., 0)`. -/
noncomputable def g0 {M n : ℕ} (h : n ≤ M) (r : Fin n → ℝ) (s : ℝ) : Fin M → ℂ :=
  fun m => Sum.elim (fun a => ((Real.sqrt (r a) : ℝ) : ℂ))
    (fun b : Fin (M - n) => if (b : ℕ) = 0 then ((Real.sqrt s : ℝ) : ℂ) else 0) (spl h m)

/-- The normal form of the bordered array. -/
noncomputable def N0 {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) (r : Fin n → ℝ) (s : ℝ) :
    Fin M → Fin (n + 1) → ℂ :=
  join (Emb M n μ) (g0 h r s)

theorem g0_castLE {M n : ℕ} (h : n ≤ M) (r : Fin n → ℝ) (s : ℝ) (a : Fin n) :
    g0 h r s (Fin.castLE h a) = ((Real.sqrt (r a) : ℝ) : ℂ) := by
  simp [g0, spl_castLE]

theorem norm_g0_castLE {M n : ℕ} (h : n ≤ M) (r : Fin n → ℝ) (s : ℝ) (a : Fin n) :
    ‖g0 h r s (Fin.castLE h a)‖ = Real.sqrt (r a) := by
  rw [g0_castLE, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem sum_norm_g0 {M n : ℕ} (h : n + 1 ≤ M) (r : Fin n → ℝ) (hr : ∀ a, 0 ≤ r a) (s : ℝ) (hs : 0 ≤ s) :
    ∑ m, ‖g0 (by omega : n ≤ M) r s m‖ ^ 2 = ∑ a, r a + s := by
  have h' : n ≤ M := by omega
  rw [sum_spl h']
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [norm_g0_castLE, Real.sq_sqrt (hr a)]
  · have hp : 0 < M - n := by omega
    rw [Finset.sum_eq_single (⟨0, hp⟩ : Fin (M - n))]
    · simp [g0, Real.sq_sqrt hs, abs_of_nonneg (Real.sqrt_nonneg s)]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun e => hb (Fin.ext e)
      simp [g0, this]
    · simp

theorem g0_n {M n : ℕ} (h : n + 1 ≤ M) (r : Fin n → ℝ) (s : ℝ) :
    g0 (by omega : n ≤ M) r s ⟨n, by omega⟩ = ((Real.sqrt s : ℝ) : ℂ) := by
  simp [g0, spl_n h]

/-- Border data of a column. -/
noncomputable def rv {M n : ℕ} (h : n ≤ M) (g : Fin M → ℂ) : Fin n → ℝ :=
  fun a => ‖g (Fin.castLE h a)‖ ^ 2

noncomputable def sv {M n : ℕ} (h : n ≤ M) (g : Fin M → ℂ) : ℝ :=
  ∑ b : Fin (M - n), ‖g ((spl h).symm (Sum.inr b))‖ ^ 2

theorem sv_pos {M n : ℕ} (h : n + 1 ≤ M) (g : Fin M → ℂ) (hg : g ⟨n, by omega⟩ ≠ 0) :
    0 < sv (by omega : n ≤ M) g := by
  have hp : 0 < M - n := by omega
  unfold sv
  have hb : (spl (by omega : n ≤ M)).symm (Sum.inr ⟨0, hp⟩) = ⟨n, by omega⟩ := by
    rw [← spl_n h, Equiv.symm_apply_apply]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun b _ => sq_nonneg ‖g ((spl _).symm (Sum.inr b))‖)
    (Finset.mem_univ (⟨0, hp⟩ : Fin (M - n))))
  rw [hb]
  exact pow_pos (norm_pos_iff.mpr hg) 2

/-- The bordered array and its normal form have the same invariant. -/
theorem F_join_eq_N0 {M n : ℕ} (h : n + 1 ≤ M) (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) (g : Fin M → ℂ) (hg : g ⟨n, by omega⟩ ≠ 0) :
    F (join (Emb M n μ) g) = F (N0 (by omega : n ≤ M) μ (rv (by omega : n ≤ M) g) (sv (by omega : n ≤ M) g)) := by
  have h' : n ≤ M := by omega
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => (hμ i).le
  have hr : ∀ a, 0 ≤ rv h' g a := fun a => sq_nonneg _
  have hs := sv_pos h g hg
  set u : Fin n → ℂ := fun i => g (Fin.castLE h' i)
  set u0 : Fin n → ℂ := fun i => g0 h' (rv h' g) (sv h' g) (Fin.castLE h' i)
  have hX : arrowC μ (fun i => Real.sqrt (μ i) * ‖g0 h' (rv h' g) (sv h' g) (Fin.castLE h' i)‖)
        (∑ m, ‖g0 h' (rv h' g) (sv h' g) m‖ ^ 2) =
      arrowC μ (fun i => Real.sqrt (μ i) * ‖g (Fin.castLE h' i)‖) (∑ m, ‖g m‖ ^ 2) := by
    congr 1
    · funext i
      rw [norm_g0_castLE, rv, Real.sqrt_sq (norm_nonneg _)]
    · rw [sum_norm_g0 h _ hr _ hs.le, sum_spl h' (fun m => ‖g m‖ ^ 2)]
      rfl
  have hA := gram_join h' μ hμ0 g
  have hB := gram_join h' μ hμ0 (g0 h' (rv h' g) (sv h' g))
  rw [hX] at hB
  have hD0 : star (Dm u0) * Dm u0 = 1 := mem_unitaryGroup_iff'.mp (Dm_mem u0)
  have hpd := posDef_join h μ hμ (g0 h' (rv h' g) (sv h' g))
    (by rw [g0_n h]; exact_mod_cast (Real.sqrt_pos.mpr hs).ne')
  refine F_gram h F hL hR (Matrix.of (join (Emb M n μ) g)) (Matrix.of (N0 h' μ (rv h' g) (sv h' g)))
    (V := Dm u * star (Dm u0)) (Submonoid.mul_mem _ (Dm_mem u) (Unitary.star_mem (Dm_mem u0))) ?_ hpd
  unfold N0
  rw [hA, hB, star_mul, star_star]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star (Dm u0)) (Dm u0), hD0, Matrix.one_mul]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ (star (Dm u0)) (Dm u0), hD0, Matrix.mul_one]

/-- At the Dixon-Anderson point the normal form is unitarily equivalent to `Emb λ`. -/
theorem F_N0_eq_Emb {M n : ℕ} (h : n + 1 ≤ M) (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) {la : Fin (n + 1) → ℝ} (hla : la ∈ Ilace μ)
    (hlap : ∀ j, 0 < la j) (hs : 0 ≤ cv μ la - ∑ i, wv μ la i / μ i) :
    F (N0 (by omega : n ≤ M) μ (fun i => wv μ la i / μ i) (cv μ la - ∑ i, wv μ la i / μ i)) =
      F (Emb M (n + 1) la) := by
  have h' : n ≤ M := by omega
  set r : Fin n → ℝ := fun i => wv μ la i / μ i with hrdef
  set s := cv μ la - ∑ i, wv μ la i / μ i with hsdef
  have hw : ∀ i, 0 < wv μ la i := fun i => wv_pos hla i
  have hr : ∀ a, 0 ≤ r a := fun a => (div_pos (hw a) (hμ a)).le
  obtain ⟨U, hU, hsim⟩ := arrowC_similar hla
  have hX : arrowC μ (fun i => Real.sqrt (μ i) * ‖g0 h' r s (Fin.castLE h' i)‖)
        (∑ m, ‖g0 h' r s m‖ ^ 2) = arrowC μ (fun i => Real.sqrt (wv μ la i)) (cv μ la) := by
    congr 1
    · funext i
      rw [norm_g0_castLE, ← Real.sqrt_mul (hμ i).le, hrdef, mul_div_cancel₀ _ (hμ i).ne']
    · rw [sum_norm_g0 h _ hr _ hs, hsdef]
      ring
  have hB := gram_join h' μ (fun i => (hμ i).le) (g0 h' r s)
  rw [hX, hsim] at hB
  set u0 : Fin n → ℂ := fun i => g0 h' r s (Fin.castLE h' i)
  refine F_emb h F hL hR (Matrix.of (N0 h' μ r s)) (W := Dm u0 * U)
    (Submonoid.mul_mem _ (Dm_mem u0) hU) la hlap ?_
  unfold N0
  rw [hB, star_mul]
  simp only [Matrix.mul_assoc]

end SWL302

-- ===== from S4.lean =====

/-! S4: the sum of `a + 1` i.i.d. `Exp(1)` variables has the Gamma density `x^a e^{-x} / a!`.
Needs prefix (W5a: dexp, exp1; W5c: mp_lastSplit). -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set SpikedWishart.Separated.Lib.Weyl

/-- Gamma density with integer shape `a + 1`. -/
noncomputable def dgam (a : ℕ) (x : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => x ^ a * Real.exp (-x) / (a.factorial : ℝ)) x

theorem measurable_dgam (a : ℕ) : Measurable (dgam a) := by
  unfold dgam
  exact (by fun_prop : Measurable fun x : ℝ => x ^ a * Real.exp (-x) / (a.factorial : ℝ)).indicator
    measurableSet_Ioi

theorem dgam_zero (x : ℝ) : dgam 0 x = dexp x := by
  simp [dgam, dexp]

theorem lintegral_exp1 (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂exp1 = ∫⁻ x, Φ x * ENNReal.ofReal (dexp x) := by
  rw [exp1, lintegral_withDensity_eq_lintegral_mul _ measurable_dexp.ennreal_ofReal hΦ]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  ring

/-- Convolution of the Gamma(a+1) density with Exp(1). -/
theorem conv_dgam (a : ℕ) (y : ℝ) :
    ∫⁻ x, ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x)) = ENNReal.ofReal (dgam (a + 1) y) := by
  have hpt : ∀ x, ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x)) =
      (Ioo 0 y).indicator (fun x => ENNReal.ofReal (x ^ a * (Real.exp (-y) / (a.factorial : ℝ)))) x := by
    intro x
    by_cases hx0 : 0 < x
    · by_cases hxy : x < y
      · have hm : x ∈ Ioo 0 y := ⟨hx0, hxy⟩
        have hyx : y - x ∈ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
        rw [indicator_of_mem hm, dgam, dexp, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx0),
          indicator_of_mem hyx, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : Real.exp (-x) * Real.exp (-(y - x)) = Real.exp (-y) := by
          rw [← Real.exp_add]; ring_nf
        calc x ^ a * Real.exp (-x) / (a.factorial : ℝ) * Real.exp (-(y - x))
            = x ^ a * (Real.exp (-x) * Real.exp (-(y - x))) / (a.factorial : ℝ) := by ring
          _ = _ := by rw [this]; ring
      · have hm : x ∉ Ioo 0 y := fun h => hxy h.2
        have hyx : y - x ∉ Ioi (0 : ℝ) := by simp only [mem_Ioi]; linarith
        rw [indicator_of_notMem hm, dexp, indicator_of_notMem hyx]
        simp
    · have hm : x ∉ Ioo 0 y := fun h => hx0 h.1
      rw [indicator_of_notMem hm, dgam, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx0)]
      simp
  rw [lintegral_congr hpt, lintegral_indicator measurableSet_Ioo]
  by_cases hy : 0 < y
  · have hint : IntegrableOn (fun x : ℝ => x ^ a * (Real.exp (-y) / (a.factorial : ℝ))) (Ioo 0 y) :=
      (by fun_prop : Continuous fun x : ℝ => x ^ a * (Real.exp (-y) / (a.factorial : ℝ))).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hy.le,
        intervalIntegral.integral_mul_const, integral_pow]
      rw [dgam, indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun x hx => ?_)
      have : 0 < x := hx.1
      simp only [Pi.zero_apply]
      positivity
  · rw [Ioo_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure, dgam,
      indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy), ENNReal.ofReal_zero]

/-- The sum of `a + 1` i.i.d. `Exp(1)` variables has density `dgam a`. -/
theorem lintegral_sum_exp1 (a : ℕ) (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ v, Φ (∑ b, v b) ∂(Measure.pi fun _ : Fin (a + 1) => exp1) =
      ∫⁻ x, Φ x * ENNReal.ofReal (dgam a x) := by
  have := isProb_exp1
  induction a generalizing Φ with
  | zero =>
    have h := measurePreserving_funUnique exp1 (Fin 1)
    have e : (fun v : Fin 1 → ℝ => Φ (∑ b, v b)) = Φ ∘ (MeasurableEquiv.funUnique (Fin 1) ℝ) := by
      funext v; simp [Fin.sum_univ_one]
    rw [e]
    refine (h.lintegral_comp hΦ).trans ?_
    rw [lintegral_exp1 Φ hΦ]
    simp only [dgam_zero]
  | succ a ih =>
    have h := mp_lastSplit exp1 (a + 1)
    have e : (fun v : Fin (a + 2) → ℝ => Φ (∑ b, v b)) =
        (fun p : ℝ × (Fin (a + 1) → ℝ) => Φ (p.1 + ∑ j, p.2 j)) ∘
          (fun r : Fin (a + 2) → ℝ => (r (Fin.last (a + 1)), fun j : Fin (a + 1) => r (Fin.castSucc j))) := by
      funext v; simp only [Function.comp_apply, Fin.sum_univ_castSucc]; rw [add_comm]
    have hm2 : Measurable (fun p : ℝ × (Fin (a + 1) → ℝ) => Φ (p.1 + ∑ j, p.2 j)) :=
      hΦ.comp (measurable_fst.add (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd))
    rw [e]
    refine (h.lintegral_comp hm2).trans ?_
    rw [lintegral_prod _ hm2.aemeasurable]
    have h1 : ∀ t : ℝ, ∫⁻ w, Φ (t + ∑ j, w j) ∂(Measure.pi fun _ : Fin (a + 1) => exp1) =
        ∫⁻ x, Φ (t + x) * ENNReal.ofReal (dgam a x) :=
      fun t => ih (fun x => Φ (t + x)) (hΦ.comp (measurable_const.add measurable_id))
    simp only [h1]
    have hj : Measurable (fun q : ℝ × ℝ => Φ (q.1 + q.2) * ENNReal.ofReal (dgam a q.2)) :=
      (hΦ.comp (measurable_fst.add measurable_snd)).mul
        ((measurable_dgam a).ennreal_ofReal.comp measurable_snd)
    rw [lintegral_exp1 _ (hj.lintegral_prod_right')]
    have hD : Measurable (fun x : ℝ => ENNReal.ofReal (dexp x)) := measurable_dexp.ennreal_ofReal
    have hG : Measurable (fun x : ℝ => ENNReal.ofReal (dgam a x)) := (measurable_dgam a).ennreal_ofReal
    calc ∫⁻ t, (∫⁻ x, Φ (t + x) * ENNReal.ofReal (dgam a x)) * ENNReal.ofReal (dexp t)
        = ∫⁻ t, ∫⁻ x, Φ (t + x) * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp t) := by
          refine lintegral_congr fun t => (lintegral_mul_const _ ?_).symm
          exact (hΦ.comp (measurable_const.add measurable_id)).mul hG
      _ = ∫⁻ x, ∫⁻ t, Φ (t + x) * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp t) := by
          refine lintegral_lintegral_swap ?_
          exact (((hΦ.comp (measurable_fst.add measurable_snd)).mul (hG.comp measurable_snd)).mul
            (hD.comp measurable_fst)).aemeasurable
      _ = ∫⁻ x, ∫⁻ y, Φ y * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x)) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_sub_right_eq_self
            (fun t => Φ (t + x) * ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp t)) x]
          simp only [sub_add_cancel]
      _ = ∫⁻ y, ∫⁻ x, Φ y * (ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x))) := by
          rw [lintegral_lintegral_swap]
          · refine lintegral_congr fun y => lintegral_congr fun x => ?_
            ring
          · exact (((hΦ.comp measurable_snd).mul (hG.comp measurable_fst)).mul
              (hD.comp (measurable_snd.sub measurable_fst))).aemeasurable
      _ = ∫⁻ y, Φ y * ENNReal.ofReal (dgam (a + 1) y) := by
          refine lintegral_congr fun y => ?_
          have hm : Measurable (fun x : ℝ => ENNReal.ofReal (dgam a x) * ENNReal.ofReal (dexp (y - x))) :=
            hG.mul (hD.comp (measurable_const.sub measurable_id))
          rw [lintegral_const_mul _ hm, conv_dgam]

end SWL302

-- ===== from S5.lean =====

/-! S5: the law of the border data `(rv g, sv g)` under `cgv M`: `Exp(1)^n ⊗ Gamma(M - n)`.
Needs prefix + d80e94b4.lean + S1..S4. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set SpikedWishart.Separated.Lib.Weyl

theorem pi_split_mp {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (e : ι ≃ α ⊕ β) :
    MeasurePreserving (fun v : ι → X => ((fun a => v (e.symm (Sum.inl a))),
        (fun b => v (e.symm (Sum.inr b)))))
      (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : α => μ).prod (Measure.pi fun _ : β => μ)) := by
  have h1 := measurePreserving_piCongrLeft (α := fun _ : α ⊕ β => X) (fun _ => μ) e
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : α ⊕ β => X) (fun _ => μ)
  have h := h2.comp h1
  convert h using 1
  funext v
  simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
  ext a
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]
  · simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

theorem lintegral_sum_exp1' (p : ℕ) (hp : 0 < p) (Φ : ℝ → ENNReal) (hΦ : Measurable Φ) :
    ∫⁻ v, Φ (∑ b, v b) ∂(Measure.pi fun _ : Fin p => exp1) =
      ∫⁻ x, Φ x * ENNReal.ofReal (dgam (p - 1) x) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  simpa using lintegral_sum_exp1 a Φ hΦ

/-- Law of the border data. -/
theorem lintegral_border {M n : ℕ} (h : n + 1 ≤ M) (Ψ : (Fin n → ℝ) × ℝ → ENNReal) (hΨ : Measurable Ψ) :
    ∫⁻ g, Ψ (rv (by omega : n ≤ M) g, sv (by omega : n ≤ M) g) ∂(cgv M) =
      ∫⁻ r, (∫⁻ x, Ψ (r, x) * ENNReal.ofReal (dgam (M - n - 1) x)) ∂(Measure.pi fun _ : Fin n => exp1) := by
  have h' : n ≤ M := by omega
  have := isProb_cg
  have := isProb_exp1
  have hsplit := pi_split_mp SpikedWishart.SoftEdge.stdComplexGaussian (spl h')
  have hns := (mp_normSqvec n).prod (mp_normSqvec (M - n))
  have hcomp := hns.comp hsplit
  have hsum : Measurable (fun q : (Fin n → ℝ) × (Fin (M - n) → ℝ) => Ψ (q.1, ∑ b, q.2 b)) :=
    hΨ.comp (measurable_fst.prodMk (Finset.measurable_sum _ fun b _ => (measurable_pi_apply b).comp measurable_snd))
  have e : ∀ g : Fin M → ℂ, Ψ (rv h' g, sv h' g) =
      (fun q : (Fin n → ℝ) × (Fin (M - n) → ℝ) => Ψ (q.1, ∑ b, q.2 b))
        (((fun p : (Fin n → ℂ) × (Fin (M - n) → ℂ) =>
          ((fun i => Complex.normSq (p.1 i)), (fun i => Complex.normSq (p.2 i)))))
          ((fun a => g ((spl h').symm (Sum.inl a))), (fun b => g ((spl h').symm (Sum.inr b))))) := by
    intro g
    simp only [sv, spl_symm_inl, Complex.normSq_eq_norm_sq]
    rfl
  simp_rw [e]
  refine (hcomp.lintegral_comp hsum).trans ?_
  rw [lintegral_prod _ hsum.aemeasurable]
  refine lintegral_congr fun r => ?_
  exact lintegral_sum_exp1' (M - n) (by omega) (fun x => Ψ (r, x)) (hΨ.comp (measurable_const.prodMk measurable_id))

end SWL302

-- ===== from S6.lean =====

/-! S6: the border average at a positive diagonal array, `hW F (Emb μ)`, by the Dixon-Anderson
change of variables (Laguerre version). Needs prefix + d80e94b4.lean + S1..S5. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

theorem cg_zero : SpikedWishart.SoftEdge.stdComplexGaussian {0} = 0 := by
  have h2 : exp1 {0} = 0 := by
    unfold exp1
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ Real.volume_singleton
  rw [← map_normSq_cg, Measure.map_apply Complex.continuous_normSq.measurable
    (measurableSet_singleton 0)] at h2
  refine measure_mono_null (fun z hz => ?_) h2
  simp only [Set.mem_singleton_iff] at hz
  simp [hz]

theorem ae_ne_zero {M n : ℕ} (h : n + 1 ≤ M) : ∀ᵐ g ∂(cgv M), g ⟨n, by omega⟩ ≠ 0 := by
  rw [ae_iff]
  have e : {g : Fin M → ℂ | ¬ g ⟨n, by omega⟩ ≠ 0} = Function.eval (⟨n, by omega⟩ : Fin M) ⁻¹' {0} := by
    ext g; simp
  rw [e]
  have h0 : stdComplexGaussian ({0} : Set ℂ) = 0 := cg_zero
  exact Measure.pi_eval_preimage_null _ h0

/-- `c - Σ w_i / μ_i = ∏ λ / ∏ μ` (the Dixon-Anderson identity at `t = 0`). -/
theorem prod_identity {n : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {la : Fin (n + 1) → ℝ}
    (hla : la ∈ Ilace μ) :
    cv μ la - ∑ i, wv μ la i / μ i = (∏ j, la j) / ∏ i, μ i := by
  have hinj := (ilace_mu_strictAnti hla).injective
  have h0 : ∏ j, (0 - la j) = Rf μ (wv μ la) (cv μ la) 0 := poly_id_eval hinj la 0
  rw [Rf_eq_prod_sec μ (wv μ la) (cv μ la) 0 (fun i => (hμ i).ne)] at h0
  unfold sec at h0
  simp only [zero_sub, Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h0
  have hs : ∑ i, wv μ la i / -μ i = -∑ i, wv μ la i / μ i := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => div_neg _
  rw [hs] at h0
  have hP : (∏ i, μ i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hμ i).ne'
  rw [eq_div_iff hP]
  have hpm : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1 : (-1 : ℝ) ^ n * ((cv μ la - ∑ i, wv μ la i / μ i) * ∏ i, μ i) = (-1) ^ n * ∏ j, la j := by
    linear_combination h0
  exact mul_left_cancel₀ hpm h1

theorem continuous_g0 {M n : ℕ} (h : n ≤ M) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => g0 h p.1 p.2) := by
  refine continuous_pi fun m => ?_
  unfold g0
  generalize spl h m = q
  rcases q with a | b
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; split_ifs <;> fun_prop

theorem continuous_N0 {M n : ℕ} (h : n ≤ M) (μ : Fin n → ℝ) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => N0 h μ p.1 p.2) := by
  unfold N0
  exact (continuous_join M n).comp (continuous_const.prodMk (continuous_g0 h))

/-- Iterated `Exp(1)^n ⊗ (density D)` integral as a Lebesgue integral on `ℝ^{n+1}`. -/
theorem lintegral_exp_dens {n : ℕ} (D : ℝ → ℝ) (hD : Measurable D)
    (Ψ : (Fin n → ℝ) × ℝ → ENNReal) (hΨ : Measurable Ψ) :
    ∫⁻ r, (∫⁻ x, Ψ (r, x) * ENNReal.ofReal (D x)) ∂(Measure.pi fun _ : Fin n => exp1) =
      ∫⁻ y : Fin (n + 1) → ℝ, Ψ (Fin.init y, y (Fin.last n)) *
        ENNReal.ofReal ((∏ i : Fin n, dexp (y i.castSucc)) * D (y (Fin.last n))) := by
  have hDw : Measurable (fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) :=
    Finset.measurable_prod _ (fun i _ => measurable_dexp.ennreal_ofReal.comp (measurable_pi_apply i))
  have hf : Measurable (fun p : (Fin n → ℝ) × ℝ => Ψ p * ENNReal.ofReal (D p.2)) :=
    hΨ.mul (hD.ennreal_ofReal.comp measurable_snd)
  have hin : Measurable (fun r : Fin n → ℝ => ∫⁻ x, Ψ (r, x) * ENNReal.ofReal (D x)) :=
    hf.lintegral_prod_right'
  have hM : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      (∏ i, ENNReal.ofReal (dexp (p.1 i))) * (Ψ p * ENNReal.ofReal (D p.2))) :=
    (hDw.comp measurable_fst).mul hf
  rw [pi_exp1, lintegral_withDensity_eq_lintegral_mul _ hDw hin]
  have e1 : ∫⁻ r, ((fun w : Fin n → ℝ => ∏ i, ENNReal.ofReal (dexp (w i))) *
      (fun r : Fin n → ℝ => ∫⁻ x, Ψ (r, x) * ENNReal.ofReal (D x))) r =
      ∫⁻ p : (Fin n → ℝ) × ℝ, (∏ i, ENNReal.ofReal (dexp (p.1 i))) * (Ψ p * ENNReal.ofReal (D p.2))
        ∂((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) := by
    rw [lintegral_prod _ hM.aemeasurable]
    refine lintegral_congr fun r => ?_
    rw [Pi.mul_apply]
    exact (lintegral_const_mul _ (hf.comp measurable_prodMk_left)).symm
  rw [e1, ← lintegral_prod_swap]
  have h := mp_lastSplit (volume : Measure ℝ) n
  refine Eq.trans (h.lintegral_comp (hM.comp measurable_swap)).symm ?_
  refine lintegral_congr (fun y => ?_)
  simp only [Function.comp_apply, Prod.swap]
  rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => dexp_nonneg _)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => dexp_nonneg _)]
  rw [show Fin.init y = fun j => y j.castSucc from rfl]
  ring

/-- `d = (μ, 1)`. -/
noncomputable def dvec {n : ℕ} (μ : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) μ 1

/-- The lower-triangular map `(r, s) ↦ (μ r, s + Σ r)`. -/
noncomputable def Tm {n : ℕ} (μ : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = j then dvec μ i else if i = Fin.last n then 1 else 0

theorem det_Tm {n : ℕ} (μ : Fin n → ℝ) : (Tm μ).det = ∏ i, μ i := by
  rw [det_of_isLowerTriangular _ ?_]
  · simp only [Tm, if_true]
    rw [Fin.prod_univ_castSucc]
    simp [dvec]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [Tm]
    rw [if_neg (ne_of_lt hij'), if_neg]
    intro hi
    rw [hi] at hij'
    exact absurd hij' (not_lt.mpr (Fin.le_last j))

theorem Tm_mulVec_cs {n : ℕ} (μ : Fin n → ℝ) (y : Fin (n + 1) → ℝ) (i : Fin n) :
    (Tm μ *ᵥ y) i.castSucc = μ i * y i.castSucc := by
  simp only [mulVec, dotProduct, Tm]
  rw [Finset.sum_eq_single i.castSucc]
  · simp [dvec]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), if_neg (Fin.castSucc_ne_last i)]
    simp
  · simp

theorem Tm_mulVec_last {n : ℕ} (μ : Fin n → ℝ) (y : Fin (n + 1) → ℝ) :
    (Tm μ *ᵥ y) (Fin.last n) = y (Fin.last n) + ∑ i : Fin n, y i.castSucc := by
  simp only [mulVec, dotProduct, Tm]
  rw [Fin.sum_univ_castSucc]
  have hne : ∀ i : Fin n, (Fin.last n = i.castSucc) = False :=
    fun i => eq_false (Fin.castSucc_ne_last i).symm
  simp [dvec, hne, add_comm]

theorem lintegral_Tm {n : ℕ} (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (G : (Fin (n + 1) → ℝ) → ENNReal) (hG : Measurable G) :
    ∫⁻ y, G (Tm μ *ᵥ y) = ENNReal.ofReal (∏ i, μ i)⁻¹ * ∫⁻ z, G z := by
  have hP : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hμ i
  have hdet : LinearMap.det (Matrix.toLin' (Tm μ)) ≠ 0 := by
    rw [LinearMap.det_toLin', det_Tm]; exact hP.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin (n + 1) → ℝ)) hdet
  rw [LinearMap.det_toLin', det_Tm, abs_of_pos (inv_pos.mpr hP)] at hmap
  have hc : Measurable (Matrix.toLin' (Tm μ)) := (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫⁻ y, G (Tm μ *ᵥ y) = ∫⁻ y, G (Matrix.toLin' (Tm μ) y) := by simp only [Matrix.toLin'_apply]
    _ = ∫⁻ z, G z ∂(Measure.map (Matrix.toLin' (Tm μ)) volume) := (lintegral_map hG hc).symm
    _ = _ := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

end SWL302

-- ===== from S6c.lean =====

/-! S6c: the border average at a positive diagonal array, `hW F (Emb μ)`, by the Dixon-Anderson
change of variables (Laguerre version). Needs prefix + d80e94b4.lean + S1..S6. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- The new Laguerre factor, supported on `λ_n > 0`. -/
noncomputable def wt {n : ℕ} (a : ℕ) (la : Fin (n + 1) → ℝ) : ℝ :=
  if 0 < la (Fin.last n) then Real.exp (-∑ j, la j) * (∏ j, la j) ^ a else 0

theorem ilace_pos {n : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {la : Fin (n + 1) → ℝ}
    (hla : la ∈ Ilace μ) (i : Fin n) : 0 < la i.castSucc :=
  (hμ i).trans (hla i).1

theorem ofReal_eq_helper (p1 p2 p3 q1 q2 q3 : ℝ) (f : ENNReal) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (h : p1 * (p2 * p3) = q1 * (q2 * q3)) :
    ENNReal.ofReal p1 * (ENNReal.ofReal p2 * (f * ENNReal.ofReal p3)) =
      ENNReal.ofReal q1 * (ENNReal.ofReal q2 * f * ENNReal.ofReal q3) := by
  have e1 : ENNReal.ofReal p1 * (ENNReal.ofReal p2 * (f * ENNReal.ofReal p3)) =
      ENNReal.ofReal (p1 * (p2 * p3)) * f := by
    rw [ENNReal.ofReal_mul hp1, ENNReal.ofReal_mul hp2]; ring
  have e2 : ENNReal.ofReal q1 * (ENNReal.ofReal q2 * f * ENNReal.ofReal q3) =
      ENNReal.ofReal (q1 * (q2 * q3)) * f := by
    rw [ENNReal.ofReal_mul hq1, ENNReal.ofReal_mul hq2]; ring
  rw [e1, e2, h]

/-- The border average at `Emb μ`, `μ` strictly decreasing and positive. -/
theorem hW_diag {M n : ℕ} (h : n + 1 ≤ M) (F : (Fin M → Fin (n + 1) → ℂ) → ENNReal) (hFm : Measurable F)
    (hL : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (Q * G) = F G)
    (hR : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F (G * V) = F G)
    {μ : Fin n → ℝ} (hanti : StrictAnti μ) (hμ : ∀ i, 0 < μ i) :
    hW F (Emb M n μ) = ENNReal.ofReal ((∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ /
        ((M - n - 1).factorial : ℝ)) *
      ∫⁻ la in Ilace μ, ENNReal.ofReal (vdm la) * F (Emb M (n + 1) la) *
        ENNReal.ofReal (wt (M - n - 1) la) := by
  have h' : n ≤ M := by omega
  have hMa : M - n = M - n - 1 + 1 := by omega
  set a := M - n - 1 with ha
  have hPμ : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hμ i
  set Ψ : (Fin n → ℝ) × ℝ → ENNReal := fun p => F (N0 h' μ p.1 p.2) with hΨdef
  have hΨ : Measurable Ψ := hFm.comp (continuous_N0 h' μ).measurable
  set G : (Fin (n + 1) → ℝ) → ENNReal := fun z =>
    Ψ (fun i => z i.castSucc / μ i, z (Fin.last n) - ∑ i, z i.castSucc / μ i) *
      ENNReal.ofReal ((∏ i, dexp (z i.castSucc / μ i)) *
        dgam a (z (Fin.last n) - ∑ i, z i.castSucc / μ i)) with hGdef
  have hr : Measurable (fun z : Fin (n + 1) → ℝ => fun i : Fin n => z i.castSucc / μ i) :=
    (by fun_prop : Continuous fun z : Fin (n + 1) → ℝ => fun i : Fin n => z i.castSucc / μ i).measurable
  have hs : Measurable (fun z : Fin (n + 1) → ℝ => z (Fin.last n) - ∑ i, z i.castSucc / μ i) :=
    (by fun_prop : Continuous fun z : Fin (n + 1) → ℝ =>
      z (Fin.last n) - ∑ i, z i.castSucc / μ i).measurable
  have hX : Measurable (fun z : Fin (n + 1) → ℝ => (∏ i, dexp (z i.castSucc / μ i)) *
      dgam a (z (Fin.last n) - ∑ i, z i.castSucc / μ i)) :=
    Measurable.mul (Finset.measurable_prod _ fun i _ =>
      measurable_dexp.comp ((measurable_pi_apply _).div_const _)) ((measurable_dgam a).comp hs)
  have hG : Measurable G := (hΨ.comp (hr.prodMk hs)).mul hX.ennreal_ofReal
  have step1 : hW F (Emb M n μ) = ∫⁻ g, Ψ (rv h' g, sv h' g) ∂(cgv M) := by
    unfold hW
    exact lintegral_congr_ae ((ae_ne_zero h).mono fun g hg => F_join_eq_N0 h F hL hR μ hμ g hg)
  have step2 := lintegral_border h Ψ hΨ
  have step3 := lintegral_exp_dens (dgam a) (measurable_dgam a) Ψ hΨ
  have step4 : ∫⁻ y : Fin (n + 1) → ℝ, Ψ (Fin.init y, y (Fin.last n)) *
        ENNReal.ofReal ((∏ i : Fin n, dexp (y i.castSucc)) * dgam a (y (Fin.last n))) =
      ∫⁻ y, G (Tm μ *ᵥ y) := by
    refine lintegral_congr fun y => ?_
    have e1 : ∀ i, (Tm μ *ᵥ y) i.castSucc / μ i = y i.castSucc := fun i => by
      rw [Tm_mulVec_cs, mul_div_cancel_left₀ _ (hμ i).ne']
    have e2 : (Tm μ *ᵥ y) (Fin.last n) - ∑ i : Fin n, y i.castSucc = y (Fin.last n) := by
      rw [Tm_mulVec_last, add_sub_cancel_right]
    rw [show Fin.init y = fun i => y i.castSucc from rfl]
    simp only [hGdef, e1, e2]
  have step5 := lintegral_Tm μ hμ G hG
  have hsupp : ∀ z, z ∉ Vpos n → G z = 0 := by
    intro z hz
    simp only [Vpos, Set.mem_setOf_eq, not_forall, not_lt] at hz
    obtain ⟨i, hi⟩ := hz
    have hd : dexp (z i.castSucc / μ i) = 0 := by
      unfold dexp
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      exact div_nonpos_of_nonpos_of_nonneg hi (hμ i).le
    have hp : ∏ j, dexp (z j.castSucc / μ j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hd
    simp only [hGdef, hp, zero_mul, ENNReal.ofReal_zero, mul_zero]
  have step6 : ∫⁻ z, G z = ∫⁻ z in Vpos n, G z := by
    rw [← lintegral_indicator (measurableSet_Vpos n)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Vpos n
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hsupp z hz]
  have step7 := lintegral_Vpos_eq hanti G
  rw [step1]
  refine step2.trans ?_
  rw [step3, step4, step5, step6, step7, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
  have hcs : ∀ i : Fin n, Phi μ la i.castSucc = wv μ la i := fun i => by
    simp only [Phi]; exact Fin.snoc_castSucc _ _ _
  have hlast : Phi μ la (Fin.last n) = cv μ la := by
    simp only [Phi]; exact Fin.snoc_last _ _
  have hP := prod_identity hμ hla
  have hlapos := fun i => ilace_pos hμ hla i
  have hprod : ∏ j, la j = (∏ i : Fin n, la i.castSucc) * la (Fin.last n) := Fin.prod_univ_castSucc _
  have hcsP : 0 < ∏ i : Fin n, la i.castSucc := Finset.prod_pos fun i _ => hlapos i
  have hK : 0 ≤ (∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ / ((a.factorial : ℕ) : ℝ) :=
    div_nonneg (div_nonneg (mul_nonneg (pow_nonneg (inv_pos.mpr hPμ).le _) (Real.exp_pos _).le)
      (vdm_nonneg μ)) (Nat.cast_nonneg _)
  simp only [hGdef, hcs, hlast]
  by_cases hpos : 0 < la (Fin.last n)
  · have hlap : ∀ j, 0 < la j := by
      intro j
      induction j using Fin.lastCases with
      | last => exact hpos
      | cast i => exact hlapos i
    have hpl : 0 < ∏ j, la j := Finset.prod_pos fun j _ => hlap j
    have hPpos : 0 < (∏ j, la j) / ∏ i, μ i := div_pos hpl hPμ
    have hs0 : 0 ≤ cv μ la - ∑ i, wv μ la i / μ i := by rw [hP]; exact hPpos.le
    have hF' : Ψ (fun i => wv μ la i / μ i, cv μ la - ∑ i, wv μ la i / μ i) = F (Emb M (n + 1) la) :=
      F_N0_eq_Emb h F hL hR μ hμ hla hlap hs0
    rw [hF', hP]
    have hd : ∀ i, dexp (wv μ la i / μ i) = Real.exp (-(wv μ la i / μ i)) := fun i => by
      unfold dexp; rw [Set.indicator_of_mem]; exact div_pos (wv_pos hla i) (hμ i)
    have hg : dgam a ((∏ j, la j) / ∏ i, μ i) =
        ((∏ j, la j) / ∏ i, μ i) ^ a * Real.exp (-((∏ j, la j) / ∏ i, μ i)) / (a.factorial : ℝ) := by
      unfold dgam; exact Set.indicator_of_mem (show _ ∈ Ioi (0 : ℝ) from hPpos) _
    have hwt : wt a la = Real.exp (-∑ j, la j) * (∏ j, la j) ^ a := by rw [wt, if_pos hpos]
    simp only [hd, hg, hwt]
    rw [← Real.exp_sum]
    have hexp : Real.exp (∑ i, -(wv μ la i / μ i)) * Real.exp (-((∏ j, la j) / ∏ i, μ i)) =
        Real.exp (∑ i, μ i) * Real.exp (-∑ j, la j) := by
      rw [Finset.sum_neg_distrib, ← Real.exp_add, ← Real.exp_add]
      congr 1
      have hc := hP
      unfold cv at hc
      linarith
    refine ofReal_eq_helper _ _ _ _ _ _ _ (inv_pos.mpr hPμ).le
      (div_nonneg (vdm_nonneg la) (vdm_nonneg μ)) hK (vdm_nonneg la) ?_
    rw [hMa, div_pow]
    linear_combination ((∏ i, μ i)⁻¹ * (vdm la / vdm μ) * ((∏ j, la j) ^ a / (∏ i, μ i) ^ a) /
      (a.factorial : ℝ)) * hexp
  · have hwt : wt a la = 0 := by rw [wt, if_neg hpos]
    have hg0 : dgam a ((∏ j, la j) / ∏ i, μ i) = 0 := by
      unfold dgam
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_Ioi, not_lt]
      refine div_nonpos_of_nonpos_of_nonneg ?_ hPμ.le
      rw [hprod]
      exact mul_nonpos_iff.mpr (Or.inl ⟨hcsP.le, not_lt.mp hpos⟩)
    rw [hP, hg0, hwt]
    simp

end SWL302

-- ===== from S7.lean =====

/-! S7: the induction step of the array Weyl formula and the final assembly.
Needs prefix + d80e94b4.lean + S1..S6c. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

end SWL302

/-! C2a (b8c3944b): nonnull (column-weighted) Laguerre chain formula, built on the d80e94b4 lib
(prefix 53ec8574_w6b + S0..S7). -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- squared Frobenius norm. -/
noncomputable def frob {M k : ℕ} (G : Fin M → Fin k → ℂ) : ℝ := ∑ m, ∑ j, Complex.normSq (G m j)

theorem continuous_frob (M k : ℕ) : Continuous (fun G : Fin M → Fin k → ℂ => frob G) := by
  unfold frob; fun_prop

theorem frob_eq_trace {M k : ℕ} (G : Matrix (Fin M) (Fin k) ℂ) : ((frob G : ℝ) : ℂ) = (Gᴴ * G).trace := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

theorem frob_left {M k : ℕ} {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q ∈ unitaryGroup (Fin M) ℂ)
    (G : Matrix (Fin M) (Fin k) ℂ) : frob (Q * G) = frob G := by
  apply Complex.ofReal_injective
  rw [frob_eq_trace, frob_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
    show Qᴴ * Q = 1 from (mem_unitaryGroup_iff'.mp hQ), Matrix.one_mul]

theorem frob_right {M k : ℕ} {V : Matrix (Fin k) (Fin k) ℂ} (hV : V ∈ unitaryGroup (Fin k) ℂ)
    (G : Matrix (Fin M) (Fin k) ℂ) : frob (G * V) = frob G := by
  apply Complex.ofReal_injective
  rw [frob_eq_trace, frob_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc G, show V * Vᴴ = 1 from (mem_unitaryGroup_iff.mp hV), Matrix.mul_one]

theorem frob_Emb {M k : ℕ} (hk : k ≤ M) {x : Fin k → ℝ} (hx : ∀ j, 0 ≤ x j) :
    frob (Emb M k x) = ∑ j, x j := by
  unfold frob
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin M)]
  · simp only [Emb, ↓reduceIte, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt (hx j)
  · intro m _ hm
    have : (m : ℕ) ≠ j := fun h => hm (Fin.ext h)
    simp [Emb, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem frob_join {M n : ℕ} (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) :
    frob (join G' g) = frob G' + ∑ m, Complex.normSq (g m) := by
  unfold frob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fin.sum_univ_castSucc]
  simp only [join, Fin.snoc_castSucc, Fin.snoc_last]

/-- column weights `∏_j exp(-a_j |col_j|²)`. -/
noncomputable def colW {M k : ℕ} (a : ℕ → ℝ) (G : Fin M → Fin k → ℂ) : ENNReal :=
  ∏ j : Fin k, ENNReal.ofReal (Real.exp (-(a j) * ∑ m, Complex.normSq (G m j)))

theorem measurable_colW {M k : ℕ} (a : ℕ → ℝ) : Measurable (fun G : Fin M → Fin k → ℂ => colW a G) := by
  unfold colW
  refine Finset.measurable_prod _ fun j _ => ?_
  exact (by fun_prop : Continuous fun G : Fin M → Fin k → ℂ =>
    Real.exp (-(a j) * ∑ m, Complex.normSq (G m j))).measurable.ennreal_ofReal

theorem colW_join {M n : ℕ} (a : ℕ → ℝ) (G' : Fin M → Fin n → ℂ) (g : Fin M → ℂ) :
    colW a (join G' g) = colW (fun j => a j - a n) G' * ENNReal.ofReal (Real.exp (-(a n) * frob (join G' g))) := by
  have hcol : ∀ j : Fin n, (∑ m, Complex.normSq (join G' g m (Fin.castSucc j))) = ∑ m, Complex.normSq (G' m j) := by
    intro j; simp only [join, Fin.snoc_castSucc]
  have hlast : (∑ m, Complex.normSq (join G' g m (Fin.last n))) = ∑ m, Complex.normSq (g m) := by
    simp only [join, Fin.snoc_last]
  unfold colW
  rw [Fin.prod_univ_castSucc]
  simp only [hcol, hlast, Fin.val_last, Fin.val_castSucc]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
  congr 1
  rw [frob_join, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hf : frob G' = ∑ j : Fin n, ∑ m, Complex.normSq (G' m j) := by unfold frob; exact Finset.sum_comm
  have hs : ∑ j : Fin n, -(a j - a n) * ∑ m, Complex.normSq (G' m j) =
      ∑ j : Fin n, -(a j) * ∑ m, Complex.normSq (G' m j) + a n * ∑ j : Fin n, ∑ m, Complex.normSq (G' m j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hf, hs]
  ring

/-- normalising factor of the bordering kernel. -/
noncomputable def kc (M n : ℕ) (μ : Fin n → ℝ) : ℝ :=
  (∏ i, μ i)⁻¹ ^ (M - n) * Real.exp (∑ i, μ i) / vdm μ / ((M - n - 1).factorial : ℝ)

/-- the weighted interlacing chain integral (level `k`, innermost = top level). -/
noncomputable def chain (M : ℕ) (a : ℕ → ℝ) : (k : ℕ) → ((Fin k → ℝ) → ENNReal) → ENNReal
  | 0, Ψ => Ψ (fun i => i.elim0)
  | n + 1, Ψ => chain M a n (fun μ => ENNReal.ofReal (kc M n μ) *
      ∫⁻ la in Ilace μ, ENNReal.ofReal (vdm la) * Ψ la * ENNReal.ofReal (wt (M - n - 1) la) *
        ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))))

theorem chain_succ (M : ℕ) (a : ℕ → ℝ) (n : ℕ) (Ψ : (Fin (n + 1) → ℝ) → ENNReal) :
    chain M a (n + 1) Ψ = chain M a n (fun μ => ENNReal.ofReal (kc M n μ) *
      ∫⁻ la in Ilace μ, ENNReal.ofReal (vdm la) * Ψ la * ENNReal.ofReal (wt (M - n - 1) la) *
        ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i)))) := rfl

/-- good set: strictly decreasing and positive. -/
def Good (k : ℕ) : Set (Fin k → ℝ) := {μ | StrictAnti μ ∧ ∀ i, 0 < μ i}

theorem chain_congr_good (M : ℕ) (a : ℕ → ℝ) (k : ℕ) (Ψ Ψ' : (Fin k → ℝ) → ENNReal)
    (h : ∀ μ ∈ Good k, Ψ μ = Ψ' μ) : chain M a k Ψ = chain M a k Ψ' := by
  cases k with
  | zero =>
    show Ψ _ = Ψ' _
    exact h _ ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    rw [chain_succ, chain_succ]
    congr 1
    funext μ
    congr 1
    refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hsa := ilace_strictAnti hla
      rw [h la ⟨hsa, fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))⟩]
    · simp [wt, hl]

theorem chain_shift (M : ℕ) (a : ℕ → ℝ) (c : ℝ) :
    ∀ (k : ℕ) (Ψ : (Fin k → ℝ) → ENNReal),
      chain M (fun j => a j - c) k (fun μ => ENNReal.ofReal (Real.exp (-c * ∑ i, μ i)) * Ψ μ) = chain M a k Ψ := by
  intro k
  induction k with
  | zero => intro Ψ; show ENNReal.ofReal _ * Ψ _ = Ψ _; simp
  | succ n ih =>
    intro Ψ
    rw [chain_succ, chain_succ, ← ih]
    congr 1
    funext μ
    rw [mul_left_comm (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))),
      ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))) _ ENNReal.ofReal_ne_top]
    congr 1
    refine lintegral_congr fun la => ?_
    have e : ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) *
        ENNReal.ofReal (Real.exp (-(a n - c) * (∑ j, la j - ∑ i, μ i))) =
        ENNReal.ofReal (Real.exp (-c * ∑ i, μ i)) *
        ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    calc ENNReal.ofReal (vdm la) * (ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) * Ψ la) *
          ENNReal.ofReal (wt (M - n - 1) la) * ENNReal.ofReal (Real.exp (-(a n - c) * (∑ j, la j - ∑ i, μ i)))
        = ENNReal.ofReal (vdm la) * Ψ la * ENNReal.ofReal (wt (M - n - 1) la) *
          (ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) *
            ENNReal.ofReal (Real.exp (-(a n - c) * (∑ j, la j - ∑ i, μ i)))) := by ring
      _ = _ := by rw [e]; ring

end SWL302

-- ===== from C2b.lean =====

/-! C2b (b8c3944b): induction for the column-weighted Laguerre chain formula. Needs C2a. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- weighted array Weyl formula at level `k`, as an interlacing chain integral. -/
def NW (k M : ℕ) : Prop :=
  ∀ a : ℕ → ℝ, ∀ F : (Fin M → Fin k → ℂ) → ENNReal, Measurable F →
    (∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (Q * G) = F G) →
    (∀ V ∈ unitaryGroup (Fin k) ℂ, ∀ G : Matrix (Fin M) (Fin k) ℂ, F (G * V) = F G) →
    ∫⁻ G, F G * colW a G ∂(sampleLaw M k) = chain M a k (fun la => F (Emb M k la))

theorem nw_zero (M : ℕ) : NW 0 M := by
  intro a F _ _ _
  have h1 : ∀ G : Fin M → Fin 0 → ℂ, F G * colW a G = F 0 := fun G => by
    rw [Subsingleton.elim G 0]; simp [colW]
  simp only [h1, lintegral_const, measure_univ, mul_one]
  show F 0 = F (Emb M 0 _)
  rw [Subsingleton.elim (α := Fin M → Fin 0 → ℂ) (Emb M 0 _) 0]

theorem nw_step {M n : ℕ} (h : n + 1 ≤ M) (H : NW n M) : NW (n + 1) M := by
  intro a F hFm hL hR
  set c := a n with hc
  set F' : (Fin M → Fin (n + 1) → ℂ) → ENNReal := fun G => F G * ENNReal.ofReal (Real.exp (-c * frob G))
    with hF'def
  have hF'm : Measurable F' :=
    hFm.mul (Real.measurable_exp.comp ((continuous_frob M (n + 1)).measurable.const_mul (-c))).ennreal_ofReal
  have hF'L : ∀ Q ∈ unitaryGroup (Fin M) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F' (Q * G) = F' G := by
    intro Q hQ G
    show F (Q * G) * _ = F G * _
    rw [hL Q hQ G, frob_left hQ G]
  have hF'R : ∀ V ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ G : Matrix (Fin M) (Fin (n + 1)) ℂ, F' (G * V) = F' G := by
    intro V hV G
    show F (G * V) * _ = F G * _
    rw [hR V hV G, frob_right hV G]
  have hprod : Measurable fun G : Fin M → Fin (n + 1) → ℂ => F G * colW a G := hFm.mul (measurable_colW a)
  have hpt : ∀ G' : Fin M → Fin n → ℂ, hW (fun G => F G * colW a G) G' =
      hW F' G' * colW (fun j => a j - c) G' := by
    intro G'
    unfold hW
    rw [← lintegral_mul_const' (colW (fun j => a j - c) G') _
      (by unfold colW; exact ENNReal.prod_ne_top fun j _ => ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun g => ?_
    show F (join G' g) * colW a (join G' g) = _
    rw [colW_join, ← hc]
    simp only [hF'def]
    ring
  rw [step_eq2 _ hprod, lintegral_congr hpt,
    H (fun j => a j - c) (hW F') (measurable_hW F' hF'm) (fun Q hQ G => hW_left F' hF'm hF'L hQ G)
      (fun V hV G => hW_right F' hF'R hV G),
    chain_succ, ← chain_shift M a c n]
  apply chain_congr_good
  rintro μ ⟨hanti, hpos⟩
  rw [hW_diag h F' hF'm hF'L hF'R hanti hpos, mul_left_comm (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))),
    ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (-c * ∑ i, μ i))) _ ENNReal.ofReal_ne_top]
  congr 1
  refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
  by_cases hl : 0 < la (Fin.last n)
  · have hsa := ilace_strictAnti hla
    have hlp : ∀ j, 0 ≤ la j := fun j => (lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))).le
    simp only [hF'def]
    rw [frob_Emb h hlp]
    have e : ENNReal.ofReal (Real.exp (-c * ∑ j, la j)) =
        ENNReal.ofReal (Real.exp (-c * ∑ i, μ i)) * ENNReal.ofReal (Real.exp (-c * (∑ j, la j - ∑ i, μ i))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    rw [e]
    ring
  · simp [wt, hl]

theorem nw_all (M : ℕ) : ∀ k, k ≤ M → NW k M := by
  intro k
  induction k with
  | zero => intro _; exact nw_zero M
  | succ n ih => intro hk; exact nw_step hk (ih (by omega))

end SWL302

-- ===== from C2f.lean =====

/-! C2f (b8c3944b): column scaling of the Gaussian array is absolutely continuous with an explicit
density (complex Gaussian of variance c⁻¹ vs variance 1). Standalone (Mathlib + FixedDim model). -/


namespace SWL302

open MeasureTheory ProbabilityTheory SpikedWishart.FixedDim

theorem lintegral_pi_prod_gen {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [SigmaFinite μ] (g : ι → α → ENNReal) (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x : ι → α, ∏ i, g i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, g i t ∂μ := by
  have hF : Measurable fun x : ι → α => ∏ i, g i (x i) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  have key : ∀ s : Finset ι, ∀ x : ι → α,
      (∫⋯∫⁻_s, (fun x : ι → α => ∏ i, g i (x i)) ∂(fun _ => μ)) x =
        ∏ i, (if i ∈ s then ∫⁻ t, g i t ∂μ else g i (x i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp [lmarginal_empty]
    | @insert i s hi ih =>
      intro x
      rw [lmarginal_insert _ hF hi]
      simp_rw [ih]
      have h1 : ∀ t : α, (∏ k, (if k ∈ s then ∫⁻ t, g k t ∂μ else g k (Function.update x i t k))) =
          g i t * ∏ k ∈ Finset.univ.erase i, (if k ∈ s then ∫⁻ t, g k t ∂μ else g k (x k)) := by
        intro t
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
        simp only [if_neg hi, Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp_rw [h1]
      rw [lintegral_mul_const _ (hg i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [Finset.mem_insert, true_or, if_true]
      congr 1
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [Finset.ne_of_mem_erase hk]
  rw [lintegral_eq_lmarginal_univ (fun _ => (default : α)), key]
  simp

theorem pi_withDensity_gen {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α] [Inhabited α]
    (μ : Measure α) [SigmaFinite μ] (f : ι → α → ENNReal)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi fun _ => μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ x : ι → α, (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [hind]
  rw [lintegral_pi_prod_gen μ _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

theorem gR_scale_aux (c : ℝ) (hc : 0 < c) (v : NNReal) (hv : (v : ℝ) = c⁻¹ * (1 / 2)) :
    gaussianReal 0 v =
      (gaussianReal 0 (1 / 2 : NNReal)).withDensity
        (fun t => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hv
    have : (0 : ℝ) < c⁻¹ * (1 / 2) := mul_pos (inv_pos.mpr hc) (by norm_num)
    linarith
  have hr : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
    fun_prop
  rw [gaussianReal_of_var_ne_zero _ hv0,
    gaussianReal_of_var_ne_zero _ (by norm_num : (1 / 2 : NNReal) ≠ 0),
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hr]
  congr 1
  funext t
  simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hv]
  have h12 : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [h12]
  have hpi := Real.pi_pos
  have hs1 : Real.sqrt (2 * Real.pi * (c⁻¹ * (1 / 2))) = Real.sqrt Real.pi / Real.sqrt c := by
    rw [show 2 * Real.pi * (c⁻¹ * (1 / 2)) = Real.pi / c by field_simp, Real.sqrt_div hpi.le]
  have hs2 : Real.sqrt (2 * Real.pi * (1 / 2)) = Real.sqrt Real.pi := by
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  rw [hs1, hs2]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have he : Real.exp (-(t - 0) ^ 2 / (2 * (c⁻¹ * (1 / 2)))) =
      Real.exp (-(t - 0) ^ 2 / (2 * (1 / 2))) * Real.exp (-(c - 1) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [he, inv_div]
  field_simp

/-- real Gaussian of variance `1/(2c)` against variance `1/2`. -/
theorem gR_scale (c : ℝ) (hc : 0 < c) :
    (gaussianReal 0 (1 / 2 : NNReal)).map (fun t => Real.sqrt c⁻¹ * t) =
      (gaussianReal 0 (1 / 2 : NNReal)).withDensity
        (fun t => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
  rw [gaussianReal_map_const_mul, mul_zero]
  refine gR_scale_aux c hc _ ?_
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.sq_sqrt (inv_nonneg.mpr hc.le)]
  norm_num

/-- complex Gaussian of variance `1/c` against the standard one. -/
theorem cg_scale (c : ℝ) (hc : 0 < c) :
    stdComplexGaussian.map (fun z => ((Real.sqrt c⁻¹ : ℝ) : ℂ) * z) =
      stdComplexGaussian.withDensity
        (fun z => ENNReal.ofReal (c * Real.exp (-(c - 1) * Complex.normSq z))) := by
  set s := Real.sqrt c⁻¹ with hs
  have hC : Measurable (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
    Complex.measurableEquivRealProd.symm.measurable
  have hr : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sqrt c * Real.exp (-(c - 1) * t ^ 2))) := by
    fun_prop
  have hm : Measurable (fun t : ℝ => s * t) := measurable_const_mul s
  unfold stdComplexGaussian
  rw [Measure.map_map (by fun_prop) hC]
  have e1 : (fun z : ℂ => ((s : ℝ) : ℂ) * z) ∘ (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) ∘ Prod.map (fun t => s * t) (fun t => s * t) := by
    funext p
    apply Complex.ext <;> simp
  rw [e1, ← Measure.map_map hC (hm.prodMap hm),
    ← Measure.map_prod_map _ _ hm hm, gR_scale c hc, prod_withDensity hr hr]
  ext t ht
  rw [Measure.map_apply hC ht, withDensity_apply _ ht, withDensity_apply _ (hC ht),
    Measure.restrict_map hC ht, lintegral_map (by fun_prop) hC]
  refine setLIntegral_congr_fun (hC ht) (fun p _ => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Complex.normSq_mk]
  rw [mul_mul_mul_comm, ← Real.exp_add, Real.mul_self_sqrt hc.le]
  congr 2
  ring

/-- the density of the column-scaled array against the standard array. -/
noncomputable def sclW {M N : ℕ} (c : Fin N → ℝ) (G : Fin M → Fin N → ℂ) : ENNReal :=
  ∏ m, ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (G m j)))

theorem measurable_sclW {M N : ℕ} (c : Fin N → ℝ) :
    Measurable (fun G : Fin M → Fin N → ℂ => sclW c G) := by
  unfold sclW
  refine Finset.measurable_prod _ fun m _ => Finset.measurable_prod _ fun j _ => ?_
  have h : Measurable (fun G : Fin M → Fin N → ℂ => G m j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply m)
  exact (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (Complex.continuous_normSq.measurable.comp h)))).ennreal_ofReal

theorem sample_scale {M N : ℕ} (c : Fin N → ℝ) (hc : ∀ j, 0 < c j) :
    (sampleLaw M N).map (fun G m j => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * G m j) =
      (sampleLaw M N).withDensity (sclW c) := by
  have hw : ∀ j, Measurable
      (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z))) := fun j =>
    (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul Complex.continuous_normSq.measurable))).ennreal_ofReal
  have hcs : ∀ j, stdComplexGaussian.map (fun z => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * z) =
      stdComplexGaussian.withDensity
        (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z))) :=
    fun j => cg_scale (c j) (hc j)
  have hP : ∀ j, IsProbabilityMeasure (stdComplexGaussian.withDensity
      (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z)))) := fun j => by
    rw [← hcs j]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hh : Measurable (fun (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j) := by
    fun_prop
  have h1 := Measure.pi_map_pi (μ := fun _ : Fin N => stdComplexGaussian)
    (f := fun j z => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * z) (fun j => (by fun_prop : Measurable _).aemeasurable)
  have hinner : (Measure.pi fun _ : Fin N => stdComplexGaussian).map
      (fun (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j) =
      (Measure.pi fun _ : Fin N => stdComplexGaussian).withDensity
        (fun g => ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) := by
    refine h1.trans ?_
    have e : (fun j => stdComplexGaussian.map (fun z => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * z)) =
        fun j => stdComplexGaussian.withDensity
          (fun z : ℂ => ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq z))) := funext hcs
    rw [e]
    exact @pi_withDensity_gen (Fin N) ℂ _ _ _ _ stdComplexGaussian _ _ hw (fun j => by haveI := hP j; infer_instance)
  have hW : Measurable (fun g : Fin N → ℂ =>
      ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) :=
    Finset.measurable_prod _ fun j _ => (hw j).comp (measurable_pi_apply j)
  have hP2 : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => stdComplexGaussian).withDensity
      (fun g => ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j))))) := by
    rw [← hinner]; exact Measure.isProbabilityMeasure_map hh.aemeasurable
  have h2 := Measure.pi_map_pi (μ := fun _ : Fin M => Measure.pi fun _ : Fin N => stdComplexGaussian)
    (f := fun _ (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j)
    (fun _ => hh.aemeasurable)
  have hs : sclW (M := M) c = fun G => ∏ m, (fun g : Fin N → ℂ =>
      ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) (G m) := by
    funext G; rfl
  unfold sampleLaw
  refine h2.trans ?_
  rw [hs]
  have e2 : (fun _ : Fin M => (Measure.pi fun _ : Fin N => stdComplexGaussian).map
      (fun (g : Fin N → ℂ) (j : Fin N) => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * g j)) =
      fun _ : Fin M => (Measure.pi fun _ : Fin N => stdComplexGaussian).withDensity
        (fun g => ∏ j, ENNReal.ofReal (c j * Real.exp (-(c j - 1) * Complex.normSq (g j)))) :=
    funext fun _ => hinner
  rw [e2]
  exact @pi_withDensity_gen (Fin M) (Fin N → ℂ) _ _ _ _ _ _ _ (fun _ => hW) (fun _ => by haveI := hP2; infer_instance)

theorem lintegral_scale {M N : ℕ} (c : Fin N → ℝ) (hc : ∀ j, 0 < c j)
    (F : (Fin M → Fin N → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ G, F (fun m j => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * G m j) ∂(sampleLaw M N) =
      ∫⁻ G, sclW c G * F G ∂(sampleLaw M N) := by
  have hs : Measurable (fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (c j)⁻¹ : ℝ) : ℂ) * G m j) := by
    fun_prop
  rw [← lintegral_map hF hs, sample_scale c hc,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_sclW c) hF]
  rfl

end SWL302

-- ===== from C2c.lean =====

/-! C2c (b8c3944b): the spiked largest-eigenvalue CDF as a weighted interlacing chain integral.
Needs C2a, C2b, C2f and the d80e94b4 lib (isClosed_psdSet, psd_conj_iff, ind_psd_conj, ind_diag, Wm_*). -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- spike weights `π_j - 1` as a sequence. -/
noncomputable def aπ {N : ℕ} (π : Fin N → ℝ) : ℕ → ℝ := fun j => if h : j < N then π ⟨j, h⟩ - 1 else 0

theorem aπ_fin {N : ℕ} (π : Fin N → ℝ) (j : Fin N) : aπ π j = π j - 1 := by
  simp [aπ, j.isLt]

theorem Wm_eq_sum {M k : ℕ} (X : Fin M → Fin k → ℂ) :
    Wm X = ∑ m, vecMulVec (X m) (star (X m)) := by
  ext i j
  rw [Matrix.sum_apply]
  rfl

theorem sampleCov_scale {M N : ℕ} (U : unitaryGroup (Fin N) ℂ) (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) :
    SpikedWishart.SoftEdge.sampleCov M U ℓ G =
      (M : ℂ)⁻¹ • ((U : Matrix (Fin N) (Fin N) ℂ) *
        Wm (fun m j => ((Real.sqrt (ℓ j) : ℝ) : ℂ) * G m j) * star (U : Matrix (Fin N) (Fin N) ℂ)) := by
  unfold SpikedWishart.SoftEdge.sampleCov SpikedWishart.SoftEdge.sampleVec
  congr 1
  rw [Wm_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, star_eq_conjTranspose]

theorem event_scale {M N : ℕ} [NeZero N] (hM : 0 < M) (U : unitaryGroup (Fin N) ℂ) (π : Fin N → ℝ)
    (x : ℝ) (G : Fin M → Fin N → ℂ) :
    SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x ↔
      ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
        Wm (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j)).PosSemidef := by
  unfold SpikedWishart.SoftEdge.largestEig
  rw [ciSup_le_iff (Set.finite_range _).bddAbove, SWL302Eig.eig_le_iff_posSemidef, sampleCov_scale]
  set W := Wm (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j)
  set V : Matrix (Fin N) (Fin N) ℂ := (U : Matrix (Fin N) (Fin N) ℂ)
  rw [← psd_conj_iff ((M : ℝ) * x) U.2 W]
  have hβ : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hb : ((M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have key : (((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - V * W * star V =
      ((M : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (M : ℂ)⁻¹ • (V * W * star V)) := by
    rw [smul_sub, smul_smul, smul_smul, show ((M : ℝ) : ℂ) = (M : ℂ) by push_cast; rfl,
      mul_inv_cancel₀ (by exact_mod_cast hβ.ne' : (M : ℂ) ≠ 0), one_smul]
    push_cast
    rfl
  rw [key]
  constructor
  · intro h
    exact h.smul (Complex.zero_le_real.mpr hβ.le)
  · intro h
    have h2 := h.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hβ.le))
    rwa [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hβ.ne', Complex.ofReal_one, one_smul] at h2

theorem sclW_eq {M N : ℕ} (π : Fin N → ℝ) (hπ : ∀ j, 0 < π j) (G : Fin M → Fin N → ℂ) :
    sclW π G = (∏ j, ENNReal.ofReal (π j ^ M)) * colW (aπ π) G := by
  unfold sclW colW
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [aπ_fin, ← ENNReal.ofReal_prod_of_nonneg (fun m _ => (mul_pos (hπ j) (Real.exp_pos _)).le),
    ← ENNReal.ofReal_mul (pow_nonneg (hπ j).le M)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    Finset.mul_sum]

theorem c2c {M N : ℕ} [NeZero N] (hNM : N ≤ M) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i)
    (U : unitaryGroup (Fin N) ℂ) (x : ℝ) :
    (sampleLaw M N) {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x} =
      (∏ i, ENNReal.ofReal (π i ^ M)) *
        chain M (aπ π) N (fun la => if la 0 ≤ (M : ℝ) * x then 1 else 0) := by
  have hM : 0 < M := lt_of_lt_of_le (NeZero.pos N) hNM
  set F : (Fin M → Fin N → ℂ) → ENNReal := fun G =>
    {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}.indicator
      (1 : Matrix (Fin N) (Fin N) ℂ → ENNReal) (Wm G) with hFdef
  have hT : MeasurableSet ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
      {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}) :=
    ((isClosed_psdSet ((M : ℝ) * x)).preimage (continuous_Wm M N)).measurableSet
  have hFe : F = ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
      {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}).indicator 1 := by
    funext G
    first | rfl | simp [hFdef, Set.indicator]
  have hF : Measurable F := by rw [hFe]; exact measurable_one.indicator hT
  have hs : Measurable (fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
    fun_prop
  have hev : {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x} =
      (fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) ⁻¹'
        ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
          {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef}) := by
    ext G
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact event_scale hM U π x G
  rw [hev, ← lintegral_indicator_one (hs hT)]
  have h1 : ∀ G : Fin M → Fin N → ℂ,
      ((fun (G : Fin M → Fin N → ℂ) m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) ⁻¹'
        ((fun G : Fin M → Fin N → ℂ => Wm G) ⁻¹'
          {A : Matrix (Fin N) (Fin N) ℂ | ((((M : ℝ) * x : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef})).indicator 1 G =
        F (fun m j => ((Real.sqrt (π j)⁻¹ : ℝ) : ℂ) * G m j) := by
    intro G
    rw [hFe]
    first | rfl | simp [Set.indicator]
  rw [lintegral_congr h1, lintegral_scale π hπ F hF]
  simp_rw [sclW_eq π hπ]
  have h2 : ∀ G : Fin M → Fin N → ℂ, (∏ j, ENNReal.ofReal (π j ^ M)) * colW (aπ π) G * F G =
      (∏ j, ENNReal.ofReal (π j ^ M)) * (F G * colW (aπ π) G) := fun G => by ring
  rw [lintegral_congr h2, lintegral_const_mul' _ _ (ENNReal.prod_ne_top fun j _ => ENNReal.ofReal_ne_top)]
  congr 1
  rw [nw_all M N hNM (aπ π) F hF
    (fun Q hQ G => by simp only [hFdef]; rw [Wm_mul_left hQ G])
    (fun V hV G => by
      simp only [hFdef]
      rw [Wm_mul_right G V]
      exact ind_psd_conj ((M : ℝ) * x) (transpose_mem_unitary hV) (Wm G))]
  apply chain_congr_good
  rintro la ⟨hanti, hpos⟩
  simp only [hFdef]
  rw [Wm_Emb hNM la (fun j => (hpos j).le), ind_diag]
  by_cases h0 : la 0 ≤ (M : ℝ) * x
  · rw [if_pos h0, Set.indicator_of_mem]
    · rfl
    · intro j _
      exact le_trans (hanti.antitone (Fin.zero_le j)) h0
  · rw [if_neg h0, Set.indicator_of_notMem]
    intro hm
    exact h0 (hm 0 (Set.mem_univ _))

end SWL302

-- ===== from C2g.lean =====

/-! C2g (b8c3944b): telescoping the weighted chain into a plain Gelfand-Tsetlin nested integral
with level weights e^{-b_n(|la|-|μ|)} and top density vdm la (∏ la)^(M-k) / ∏_{n<k} (M-n-1)!. Needs C2a. -/

namespace SWL302

attribute [local instance] cgv.isProb

open MeasureTheory Set Matrix SpikedWishart.FixedDim SpikedWishart.Separated.Lib.Weyl

/-- positivity indicator of the last coordinate. -/
noncomputable def posI {n : ℕ} (la : Fin (n + 1) → ℝ) : ℝ := if 0 < la (Fin.last n) then 1 else 0

/-- nested Gelfand-Tsetlin integral with level weights `e^{-b_n(|la|-|μ|)}` (innermost = top level). -/
noncomputable def gtI (b : ℕ → ℝ) : (k : ℕ) → ((Fin k → ℝ) → ENNReal) → ENNReal
  | 0, Φ => Φ (fun i => i.elim0)
  | n + 1, Φ => gtI b n (fun μ => ∫⁻ la in Ilace μ,
      ENNReal.ofReal (posI la * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) * Φ la)

theorem gtI_succ (b : ℕ → ℝ) (n : ℕ) (Φ : (Fin (n + 1) → ℝ) → ENNReal) :
    gtI b (n + 1) Φ = gtI b n (fun μ => ∫⁻ la in Ilace μ,
      ENNReal.ofReal (posI la * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) * Φ la) := rfl

theorem gtI_congr_good (b : ℕ → ℝ) (k : ℕ) (Φ Φ' : (Fin k → ℝ) → ENNReal)
    (h : ∀ μ ∈ Good k, Φ μ = Φ' μ) : gtI b k Φ = gtI b k Φ' := by
  cases k with
  | zero =>
    show Φ _ = Φ' _
    exact h _ ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    rw [gtI_succ, gtI_succ]
    congr 1
    funext μ
    refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hsa := ilace_strictAnti hla
      rw [h la ⟨hsa, fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))⟩]
    · simp [posI, hl]

/-- `∏_{n<k} (M-n-1)!`. -/
noncomputable def Pf (M : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => Pf M n * ((M - n - 1).factorial : ℝ)

theorem Pf_pos (M : ℕ) : ∀ k, 0 < Pf M k := by
  intro k
  induction k with
  | zero => show (0 : ℝ) < 1; norm_num
  | succ n ih =>
    show 0 < Pf M n * ((M - n - 1).factorial : ℝ)
    exact mul_pos ih (Nat.cast_pos.mpr (Nat.factorial_pos _))

/-- the telescoped top-level density. -/
noncomputable def Dk (M k : ℕ) (la : Fin k → ℝ) : ℝ := vdm la * (∏ i, la i) ^ (M - k) / Pf M k

theorem chain_tele (M : ℕ) (a b : ℕ → ℝ) (hab : ∀ n, a n = b n - 1) :
    ∀ (k : ℕ) (Ψ : (Fin k → ℝ) → ENNReal),
      chain M a k Ψ = gtI b k (fun la => ENNReal.ofReal (Dk M k la) * Ψ la) := by
  intro k
  induction k with
  | zero =>
    intro Ψ
    show Ψ _ = ENNReal.ofReal (Dk M 0 _) * Ψ _
    have : Dk M 0 (fun i => i.elim0) = 1 := by
      unfold Dk vdm
      simp [Pf]
    rw [this, ENNReal.ofReal_one, one_mul]
  | succ n ih =>
    intro Ψ
    rw [chain_succ, ih, gtI_succ]
    apply gtI_congr_good
    rintro μ ⟨hanti, hpos⟩
    have hV : 0 < vdm μ := vdm_pos hanti.injective
    have hA : 0 < ∏ i, μ i := Finset.prod_pos fun i _ => hpos i
    have hP := Pf_pos M n
    have hF : (0 : ℝ) < ((M - n - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hP1 : 0 < Pf M (n + 1) := Pf_pos M (n + 1)
    have hD : 0 ≤ Dk M n μ := by
      unfold Dk
      exact div_nonneg (mul_nonneg hV.le (pow_nonneg hA.le _)) hP.le
    have h1 : Dk M n μ * kc M n μ = Real.exp (∑ i, μ i) / Pf M (n + 1) := by
      unfold Dk kc
      show _ = Real.exp (∑ i, μ i) / (Pf M n * ((M - n - 1).factorial : ℝ))
      rw [inv_pow]
      field_simp
    rw [← mul_assoc, ← ENNReal.ofReal_mul hD, h1,
      ← lintegral_const_mul' (ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1))) _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_Ilace μ) fun la hla => ?_
    by_cases hl : 0 < la (Fin.last n)
    · have hsa := ilace_strictAnti hla
      have hlp : ∀ j, 0 < la j := fun j => lt_of_lt_of_le hl (hsa.antitone (Fin.le_last j))
      have hL : 0 < ∏ j, la j := Finset.prod_pos fun j _ => hlp j
      have hw : wt (M - n - 1) la = Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1) := by
        unfold wt; rw [if_pos hl]
      have hpI : posI la = 1 := by unfold posI; rw [if_pos hl]
      rw [hw, hpI]
      have hA0 : 0 ≤ Real.exp (∑ i, μ i) / Pf M (n + 1) := div_nonneg (Real.exp_pos _).le hP1.le
      have hB0 : 0 ≤ Real.exp (∑ i, μ i) / Pf M (n + 1) * vdm la := mul_nonneg hA0 (vdm_nonneg la)
      have hC0 : 0 ≤ Real.exp (∑ i, μ i) / Pf M (n + 1) * vdm la *
          (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) :=
        mul_nonneg hB0 (mul_nonneg (Real.exp_pos _).le (pow_nonneg hL.le _))
      have hE0 : 0 ≤ (1 : ℝ) * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) :=
        mul_nonneg zero_le_one (Real.exp_pos _).le
      have key : ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1)) * ENNReal.ofReal (vdm la) *
          ENNReal.ofReal (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) *
          ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))) =
          ENNReal.ofReal (1 * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) *
          ENNReal.ofReal (Dk M (n + 1) la) := by
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hC0,
          ← ENNReal.ofReal_mul hE0]
        congr 1
        unfold Dk
        have he : Real.exp (∑ i, μ i) * Real.exp (-∑ j, la j) *
            Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i)) = Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i)) := by
          rw [← Real.exp_add, ← Real.exp_add, hab]
          congr 1
          ring
        rw [show M - (n + 1) = M - n - 1 by omega, ← he]
        ring
      calc ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1)) *
            (ENNReal.ofReal (vdm la) * Ψ la *
              ENNReal.ofReal (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) *
              ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i))))
          = (ENNReal.ofReal (Real.exp (∑ i, μ i) / Pf M (n + 1)) * ENNReal.ofReal (vdm la) *
              ENNReal.ofReal (Real.exp (-∑ j, la j) * (∏ j, la j) ^ (M - n - 1)) *
              ENNReal.ofReal (Real.exp (-(a n) * (∑ j, la j - ∑ i, μ i)))) * Ψ la := by ring
        _ = (ENNReal.ofReal (1 * Real.exp (-(b n) * (∑ j, la j - ∑ i, μ i))) *
              ENNReal.ofReal (Dk M (n + 1) la)) * Ψ la := by rw [key]
        _ = _ := by ring
    · simp [wt, posI, hl]

end SWL302

-- ===== from C2e.lean =====

/-! C2e (b8c3944b): weighted interlacing integral with a zero endpoint (Dixon-Anderson, one exponent):
`∫_{box (y,0)} Δ(μ) (∏ μ)^a dμ = Δ(y) (∏ y)^(a+1) a! / (n+a)!`. Needs the 53ec8574 Weyl prefix. -/

namespace SWL302

open MeasureTheory Set Matrix SpikedWishart.Separated.Lib.Weyl

/-- the interlacing top `(y, 0)`. -/
noncomputable def snoc0 {n : ℕ} (y : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) y 0

theorem integral_det_pow {n : ℕ} (la : Fin (n + 1) → ℝ) (a : ℕ) :
    ∫ mu in box la, (Matrix.of fun (i : Fin n) (j : Fin n) => mu i ^ ((j : ℕ) + a)).det =
      (Matrix.of fun (i : Fin n) (j : Fin n) =>
        ∫ t in Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)), t ^ ((j : ℕ) + a)).det := by
  have hrestr : (volume : Measure (Fin n → ℝ)).restrict (box la) =
      Measure.pi (fun i : Fin n => volume.restrict (Set.Ioo (la (Fin.succ i)) (la (Fin.castSucc i)))) := by
    rw [box, show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ => volume) from rfl,
      Measure.restrict_pi_pi]
  rw [hrestr]
  have h1 : (fun mu : Fin n → ℝ => (Matrix.of fun (i : Fin n) (j : Fin n) => mu i ^ ((j : ℕ) + a)).det) =
      fun mu => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, mu i ^ ((σ i : ℕ) + a) := by
    funext mu
    rw [← det_transpose, det_apply']
    simp
  rw [h1, integral_finsetSum _ (fun σ _ => (Integrable.fintype_prod
    (f := fun i (t : ℝ) => t ^ ((σ i : ℕ) + a)) (fun i => integrableOn_Ioo_pow _ _ _)).const_mul _)]
  rw [← det_transpose, det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => t ^ ((σ i : ℕ) + a))]
  simp

/-- row reduction: differences of consecutive rows of `(y, 0)` powers. -/
theorem det_diff_snoc0 {n : ℕ} (y : Fin n → ℝ) (p : Fin n → ℕ) (hp : ∀ j, 1 ≤ p j) :
    (Matrix.of fun (i : Fin n) (j : Fin n) =>
        snoc0 y (Fin.castSucc i) ^ p j - snoc0 y (Fin.succ i) ^ p j).det =
      (Matrix.of fun (i : Fin n) (j : Fin n) => y i ^ p j).det := by
  cases n with
  | zero => simp [Matrix.det_isEmpty]
  | succ m =>
    set A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun i j => y i ^ p j with hA
    set D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
      Matrix.of fun i j => snoc0 y (Fin.castSucc i) ^ p j - snoc0 y (Fin.succ i) ^ p j with hD
    have hz : ∀ j, (0 : ℝ) ^ p j = 0 := fun j => zero_pow (by have := hp j; omega)
    have key : (A.submatrix Fin.revPerm id).det = (D.submatrix Fin.revPerm id).det := by
      refine det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1) (fun j => ?_) (fun i j => ?_)
      · simp only [hA, hD, Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.rev_zero,
          snoc0, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hz, sub_zero]
      · simp only [hA, hD, Matrix.submatrix_apply, Matrix.of_apply, id, Fin.revPerm_apply, Fin.rev_succ,
          Fin.rev_castSucc, snoc0, Fin.snoc_castSucc, one_mul]
        rw [show ((Fin.rev i).castSucc.succ : Fin (m + 2)) = (Fin.rev i).succ.castSucc from Fin.ext (by simp),
          Fin.snoc_castSucc]
        ring
    rw [Matrix.det_permute, Matrix.det_permute] at key
    have hs : ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1))) : ℤ) : ℝ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) with h | h <;>
        simp [h]
    exact (mul_left_cancel₀ hs key).symm

theorem prod_inv_add (n a : ℕ) :
    ∏ j : Fin n, (1 / ((j : ℕ) + a + 1 : ℝ)) = (a.factorial : ℝ) / ((n + a).factorial : ℝ) := by
  induction n with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.prod_empty, zero_add, div_self (by exact_mod_cast (Nat.factorial_pos a).ne')]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, show n + 1 + a = (n + a) + 1 by omega, Nat.factorial_succ]
    push_cast
    have h1 : (0 : ℝ) < ((n + a).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    field_simp

/-- weighted interlacing integral with zero endpoint. -/
theorem integral_box_snoc0_pow {n : ℕ} {y : Fin n → ℝ} (hy : StrictAnti y) (hpos : ∀ i, 0 < y i) (a : ℕ) :
    ∫ mu in box (snoc0 y), vdm mu * (∏ i, mu i) ^ a =
      vdm y * (∏ i, y i) ^ (a + 1) * ((a.factorial : ℝ) / ((n + a).factorial : ℝ)) := by
  have hrowmul : ∀ mu : Fin n → ℝ, (Matrix.of fun (i : Fin n) (j : Fin n) => mu i ^ ((j : ℕ) + a)).det =
      (∏ i, mu i) ^ a * (vandermonde mu).det := by
    intro mu
    have := det_mul_column (fun i => mu i ^ a) (vandermonde mu)
    rw [← Finset.prod_pow, ← this]
    congr 1
    ext i j
    simp [vandermonde_apply, pow_add, mul_comm]
  have hcong : ∫ mu in box (snoc0 y), vdm mu * (∏ i, mu i) ^ a =
      SpikedWishart.Separated.Lib.Weyl.sgn n *
        ∫ mu in box (snoc0 y), (Matrix.of fun (i : Fin n) (j : Fin n) => mu i ^ ((j : ℕ) + a)).det := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_box _) (fun mu hmu => ?_)
    rw [hrowmul, det_vdm_strictAnti (ilace_mu_strictAnti (mem_box_iff.mp hmu))]
    have := sgn_mul_self n
    linear_combination (-(vdm mu * (∏ i, mu i) ^ a)) * this
  have hla : StrictAnti (snoc0 y) := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    by_cases hi : (i : ℕ) + 1 < n
    · have e1 : (Fin.succ i : Fin (n + 1)) = Fin.castSucc ⟨(i : ℕ) + 1, hi⟩ := by ext; simp
      have e2 : (Fin.castSucc i : Fin (n + 1)) = Fin.castSucc ⟨(i : ℕ), by omega⟩ := by ext; simp
      rw [e1, e2, snoc0, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hy (Fin.mk_lt_mk.mpr (by omega))
    · have e1 : (Fin.succ i : Fin (n + 1)) = Fin.last n := by ext; simp; omega
      have e2 : (Fin.castSucc i : Fin (n + 1)) = Fin.castSucc ⟨(i : ℕ), by omega⟩ := by ext; simp
      rw [e1, e2, snoc0, Fin.snoc_castSucc, Fin.snoc_last]
      exact hpos _
  have hN : (Matrix.of fun (i : Fin n) (j : Fin n) =>
        ∫ t in Set.Ioo (snoc0 y (Fin.succ i)) (snoc0 y (Fin.castSucc i)), t ^ ((j : ℕ) + a)) =
      Matrix.of fun (i : Fin n) (j : Fin n) => (1 / ((j : ℕ) + a + 1 : ℝ)) *
        (snoc0 y (Fin.castSucc i) ^ ((j : ℕ) + a + 1) - snoc0 y (Fin.succ i) ^ ((j : ℕ) + a + 1)) := by
    ext i j
    have hle : snoc0 y (Fin.succ i) ≤ snoc0 y (Fin.castSucc i) := (hla (Fin.castSucc_lt_succ (i := i))).le
    simp only [Matrix.of_apply]
    rw [integral_Ioo_pow hle]
    push_cast
    ring
  have hrow := det_mul_row (fun j : Fin n => 1 / ((j : ℕ) + a + 1 : ℝ)) (Matrix.of fun (i : Fin n) (j : Fin n) =>
        snoc0 y (Fin.castSucc i) ^ ((j : ℕ) + a + 1) - snoc0 y (Fin.succ i) ^ ((j : ℕ) + a + 1))
  simp only [Matrix.of_apply] at hrow
  have hdd := det_diff_snoc0 y (fun j => (j : ℕ) + a + 1) (fun j => by omega)
  have hY : (Matrix.of fun (i : Fin n) (j : Fin n) => y i ^ ((j : ℕ) + a + 1)).det =
      (∏ i, y i) ^ (a + 1) * (vandermonde y).det := by
    have := det_mul_column (fun i => y i ^ (a + 1)) (vandermonde y)
    rw [← Finset.prod_pow, ← this]
    congr 1
    ext i j
    simp [vandermonde_apply, pow_add, mul_comm]
    ring
  rw [hcong, integral_det_pow, hN, hrow, hdd, hY, det_vdm_strictAnti hy, prod_inv_add]
  have := sgn_mul_self n
  linear_combination (vdm y * (∏ i, y i) ^ (a + 1) * ((a.factorial : ℝ) / ((n + a).factorial : ℝ))) * this

end SWL302

-- ===== from C2h.lean =====

/-! C2h (b8c3944b): relabel an lmarginal over the image of an injective `e : Fin L → ι` as a plain
integral over `Fin L → ℝ` (tool for slicing the RPP integral into diagonals). Standalone. -/


namespace SWL302

open MeasureTheory

open Classical in
/-- `x` with the coordinates `e l` replaced by `z l`. -/
noncomputable def updE {ι : Type*} {L : ℕ} (e : Fin L → ι) (x : ι → ℝ) (z : Fin L → ℝ) : ι → ℝ :=
  fun i => if h : ∃ l, e l = i then z (Classical.choose h) else x i

theorem updE_apply_e {ι : Type*} {L : ℕ} {e : Fin L → ι} (he : Function.Injective e) (x : ι → ℝ)
    (z : Fin L → ℝ) (l : Fin L) : updE e x z (e l) = z l := by
  have h : ∃ l', e l' = e l := ⟨l, rfl⟩
  unfold updE
  rw [dif_pos h, he (Classical.choose_spec h)]

theorem updE_apply_not {ι : Type*} {L : ℕ} {e : Fin L → ι} (x : ι → ℝ) (z : Fin L → ℝ) {i : ι}
    (hi : ¬ ∃ l, e l = i) : updE e x z i = x i := by
  unfold updE
  rw [dif_neg hi]

theorem lmarginal_image_fin {ι : Type*} [DecidableEq ι] {L : ℕ} (e : Fin L → ι)
    (he : Function.Injective e) (f : (ι → ℝ) → ENNReal) (x : ι → ℝ) :
    (∫⋯∫⁻_(Finset.univ.image e), f ∂(fun _ => (volume : Measure ℝ))) x =
      ∫⁻ z : Fin L → ℝ, f (updE e x z) := by
  set s : Finset ι := Finset.univ.image e with hs
  have hmem : ∀ l, e l ∈ s := fun l => Finset.mem_image_of_mem e (Finset.mem_univ l)
  let σ : Fin L ≃ s := Equiv.ofBijective (fun l => ⟨e l, hmem l⟩)
    ⟨fun l l' h => he (congrArg Subtype.val h), fun ⟨i, hi⟩ => by
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hi
      exact ⟨l, Subtype.ext hl⟩⟩
  have hmp := measurePreserving_piCongrLeft (fun _ : s => (volume : Measure ℝ)) σ
  unfold lmarginal
  rw [hmp.lintegral_map_equiv, volume_pi]
  refine lintegral_congr fun z => ?_
  congr 1
  funext i
  rw [Function.updateFinset_def]
  beta_reduce
  by_cases h : ∃ l, e l = i
  · obtain ⟨l, rfl⟩ := h
    rw [dif_pos (hmem l), updE_apply_e he]
    have : (⟨e l, hmem l⟩ : s) = σ l := rfl
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]
  · have hi : i ∉ s := by
      intro hi
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hi
      exact h ⟨l, hl⟩
    rw [dif_neg hi, updE_apply_not x z h]

end SWL302



set_option autoImplicit false

namespace SWL302

open MeasureTheory

/-- iterated block integral `T_0 = 1`, `T_{d+1} w = ∫ z, c d z w * T_d z`. -/
noncomputable def bcT (L : ℕ → ℕ) (c : (d : ℕ) → (Fin (L d) → ℝ) → (Fin (L (d + 1)) → ℝ) → ENNReal) :
    (d : ℕ) → (Fin (L d) → ℝ) → ENNReal
  | 0 => fun _ => 1
  | d + 1 => fun w => ∫⁻ z : Fin (L d) → ℝ, c d z w * bcT L c d z

theorem bcT_succ (L : ℕ → ℕ) (c : (d : ℕ) → (Fin (L d) → ℝ) → (Fin (L (d + 1)) → ℝ) → ENNReal)
    (d : ℕ) (w : Fin (L (d + 1)) → ℝ) :
    bcT L c (d + 1) w = ∫⁻ z : Fin (L d) → ℝ, c d z w * bcT L c d z := rfl

theorem measurable_bcT (L : ℕ → ℕ) (c : (d : ℕ) → (Fin (L d) → ℝ) → (Fin (L (d + 1)) → ℝ) → ENNReal)
    (hc : ∀ d, Measurable (Function.uncurry (c d))) : ∀ d, Measurable (bcT L c d) := by
  intro d
  induction d with
  | zero => exact measurable_const
  | succ d ih =>
    have hf : Measurable (fun p : (Fin (L d) → ℝ) × (Fin (L (d + 1)) → ℝ) =>
        c d p.1 p.2 * bcT L c d p.1) := (hc d).mul (ih.comp measurable_fst)
    exact hf.lintegral_prod_left'

/-- union of the first `d` blocks. -/
def bcU {ι : Type*} [DecidableEq ι] (L : ℕ → ℕ) (e : (d : ℕ) → Fin (L d) → ι) (d : ℕ) : Finset ι :=
  (Finset.range d).biUnion fun d' => Finset.univ.image (e d')

theorem measurable_comp_fin {ι : Type*} {L : ℕ} (e : Fin L → ι) :
    Measurable (fun y : ι → ℝ => y ∘ e) :=
  measurable_pi_lambda _ fun l => measurable_pi_apply (e l)

theorem bc_lmarginal {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ℕ → ℕ) (e : (d : ℕ) → Fin (L d) → ι)
    (c : (d : ℕ) → (Fin (L d) → ℝ) → (Fin (L (d + 1)) → ℝ) → ENNReal) (K : ℕ)
    (he : ∀ d, Function.Injective (e d))
    (hdisj : ∀ d d' (l : Fin (L d)) (l' : Fin (L d')), d ≤ K → d' ≤ K → d ≠ d' → e d l ≠ e d' l')
    (hc : ∀ d, Measurable (Function.uncurry (c d))) :
    ∀ d ≤ K, ∀ x : ι → ℝ,
      (∫⋯∫⁻_(bcU L e d), (fun y => ∏ d' ∈ Finset.range K, c d' (y ∘ e d') (y ∘ e (d' + 1)))
          ∂(fun _ => (volume : Measure ℝ))) x
        = (∏ d' ∈ Finset.Ico d K, c d' (x ∘ e d') (x ∘ e (d' + 1))) * bcT L c d (x ∘ e d) := by
  have hf : Measurable (fun y : ι → ℝ => ∏ d' ∈ Finset.range K, c d' (y ∘ e d') (y ∘ e (d' + 1))) :=
    Finset.measurable_prod _ fun d' _ =>
      (hc d').comp ((measurable_comp_fin (e d')).prodMk (measurable_comp_fin (e (d' + 1))))
  intro d
  induction d with
  | zero =>
    intro _ x
    simp only [bcU, Finset.range_zero, Finset.biUnion_empty, lmarginal_empty]
    rw [← Finset.range_eq_Ico]
    show _ = _ * 1
    rw [mul_one]
  | succ d ih =>
    intro hd x
    have hdK : d ≤ K := Nat.le_of_succ_le hd
    have hU : bcU L e (d + 1) = bcU L e d ∪ Finset.univ.image (e d) := by
      unfold bcU
      rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    have hdj : Disjoint (bcU L e d) (Finset.univ.image (e d)) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨d', hd', hi1⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨l', _, hl'⟩ := Finset.mem_image.mp hi1
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hi'
      have hd'd : d' < d := Finset.mem_range.mp hd'
      exact hdisj d' d l' l (by omega) hdK (by omega) (hl'.trans hl.symm)
    rw [hU, lmarginal_union' _ _ hf hdj]
    have hin : (∫⋯∫⁻_(bcU L e d), (fun y => ∏ d' ∈ Finset.range K, c d' (y ∘ e d') (y ∘ e (d' + 1)))
          ∂(fun _ => (volume : Measure ℝ))) =
        fun y => (∏ d' ∈ Finset.Ico d K, c d' (y ∘ e d') (y ∘ e (d' + 1))) * bcT L c d (y ∘ e d) :=
      funext (ih hdK)
    rw [hin, lmarginal_image_fin (e d) (he d)]
    have hz : ∀ z : Fin (L d) → ℝ, updE (e d) x z ∘ e d = z := fun z =>
      funext fun l => updE_apply_e (he d) x z l
    have hother : ∀ z : Fin (L d) → ℝ, ∀ d', d' ≤ K → d' ≠ d → updE (e d) x z ∘ e d' = x ∘ e d' := by
      intro z d' hd'K hne
      funext l
      refine updE_apply_not x z ?_
      rintro ⟨l', hl'⟩
      exact hdisj d d' l' l hdK hd'K (Ne.symm hne) hl'
    have hlt : d < K := hd
    have hP : ∀ z : Fin (L d) → ℝ,
        (∏ d' ∈ Finset.Ico (d + 1) K, c d' (updE (e d) x z ∘ e d') (updE (e d) x z ∘ e (d' + 1))) =
          ∏ d' ∈ Finset.Ico (d + 1) K, c d' (x ∘ e d') (x ∘ e (d' + 1)) := by
      intro z
      refine Finset.prod_congr rfl fun d' hd' => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hd'
      rw [hother z d' (by omega) (by omega), hother z (d' + 1) (by omega) (by omega)]
    have hstep : ∀ z : Fin (L d) → ℝ,
        (∏ d' ∈ Finset.Ico d K, c d' (updE (e d) x z ∘ e d') (updE (e d) x z ∘ e (d' + 1))) *
            bcT L c d (updE (e d) x z ∘ e d) =
          (∏ d' ∈ Finset.Ico (d + 1) K, c d' (x ∘ e d') (x ∘ e (d' + 1))) *
            (c d z (x ∘ e (d + 1)) * bcT L c d z) := by
      intro z
      rw [Finset.prod_eq_prod_Ico_succ_bot hlt, hP z, hz z, hother z (d + 1) hd (by omega)]
      ring
    simp_rw [hstep]
    rw [lintegral_const_mul]
    · rfl
    · exact (hc d).comp (measurable_id.prodMk measurable_const) |>.mul (measurable_bcT L c hc d)

/-- block-chain Fubini: if the blocks `0..K-1` cover `ι`, the full integral is `T_K`. -/
theorem bc_lintegral {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ℕ → ℕ) (e : (d : ℕ) → Fin (L d) → ι)
    (c : (d : ℕ) → (Fin (L d) → ℝ) → (Fin (L (d + 1)) → ℝ) → ENNReal) (K : ℕ)
    (he : ∀ d, Function.Injective (e d))
    (hdisj : ∀ d d' (l : Fin (L d)) (l' : Fin (L d')), d ≤ K → d' ≤ K → d ≠ d' → e d l ≠ e d' l')
    (hcov : ∀ i, ∃ d < K, ∃ l, e d l = i)
    (hc : ∀ d, Measurable (Function.uncurry (c d))) (x0 : ι → ℝ) :
    ∫⁻ y : ι → ℝ, ∏ d' ∈ Finset.range K, c d' (y ∘ e d') (y ∘ e (d' + 1)) = bcT L c K (x0 ∘ e K) := by
  have hU : bcU L e K = Finset.univ := by
    refine Finset.eq_univ_of_forall fun i => ?_
    obtain ⟨d, hd, l, hl⟩ := hcov i
    exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_range.mpr hd, Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hl⟩⟩
  have h := bc_lmarginal L e c K he hdisj hc K le_rfl x0
  rw [hU, lmarginal_univ, Finset.Ico_self, Finset.prod_empty, one_mul] at h
  rw [volume_pi]
  exact h

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory

/-- natural-index read of a block (zero outside). -/
noncomputable def rdv {L : ℕ} (z : Fin L → ℝ) (k : ℕ) : ℝ := if h : k < L then z ⟨k, h⟩ else 0

/-- row of the bottom-right cell of diagonal `d`. -/
@[irreducible] def dA (N M d : ℕ) : ℕ := if d + 1 < M then N - 1 else N + M - 2 - d
/-- column of the bottom-right cell of diagonal `d`. -/
@[irreducible] def dB (M d : ℕ) : ℕ := if d + 1 < M then d else M - 1
/-- length of diagonal `d` (zero from `d = N+M-1` on). -/
@[irreducible] def dL (N M d : ℕ) : ℕ :=
  if d + 1 < M then (if d < N - 1 then d + 1 else N) else (if d < N + M - 1 then N + M - 1 - d else 0)

theorem dA_lt (N M d : ℕ) (hN : 0 < N) : dA N M d < N := by unfold dA; split_ifs <;> omega
theorem dB_lt (M d : ℕ) (hM : 0 < M) : dB M d < M := by unfold dB; split_ifs <;> omega

/-- the cells of diagonal `d`. -/
def dE (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (d : ℕ) (k : Fin (dL N M d)) : Fin N × Fin M :=
  (⟨dA N M d - k, lt_of_le_of_lt (Nat.sub_le _ _) (dA_lt N M d hN)⟩,
   ⟨dB M d - k, lt_of_le_of_lt (Nat.sub_le _ _) (dB_lt M d hM)⟩)

theorem dL_le (N M d : ℕ) (hNM : N ≤ M) (k : ℕ) (hk : k < dL N M d) : k ≤ dA N M d ∧ k ≤ dB M d := by
  unfold dL at hk; unfold dA dB; split_ifs at hk ⊢ <;> omega

theorem dE_injective (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (d : ℕ) :
    Function.Injective (dE N M hN hM d) := by
  intro k k' h
  have h1 := congrArg (fun q : Fin N × Fin M => (q.1 : ℕ)) h
  simp only [dE] at h1
  have := dL_le N M d hNM k k.isLt
  have := dL_le N M d hNM k' k'.isLt
  exact Fin.ext (by omega)

theorem diag_nat (N M d j : ℕ) (hNM : N ≤ M) (hj : j < dL N M d) :
    dB M d - j + (N - 1) = dA N M d - j + d := by
  unfold dL at hj; unfold dA dB
  by_cases h1 : d + 1 < M
  · simp only [h1, if_true] at hj ⊢
    by_cases h2 : d < N - 1
    · simp only [h2, if_true] at hj; omega
    · simp only [h2, if_false] at hj; omega
  · simp only [h1, if_false] at hj ⊢
    by_cases h3 : d < N + M - 1
    · simp only [h3, if_true] at hj; omega
    · simp only [h3, if_false] at hj; omega

/-- the diagonal index of a cell. -/
theorem dE_diag (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (d : ℕ) (k : Fin (dL N M d)) :
    ((dE N M hN hM d k).2 : ℕ) + (N - 1) = (dE N M hN hM d k).1 + d :=
  diag_nat N M d k hNM k.isLt

theorem dE_disj (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (d d' : ℕ) (k : Fin (dL N M d))
    (k' : Fin (dL N M d')) (hne : d ≠ d') : dE N M hN hM d k ≠ dE N M hN hM d' k' := by
  intro h
  have h1 := dE_diag N M hN hM hNM d k
  have h2 := dE_diag N M hN hM hNM d' k'
  rw [h] at h1
  omega

theorem dE_cover (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (q : Fin N × Fin M) :
    ∃ d < N + M - 1, ∃ k, dE N M hN hM d k = q := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := q
  refine ⟨b + (N - 1) - a, by omega, ⟨dA N M (b + (N - 1) - a) - a, ?_⟩, ?_⟩
  · unfold dL dA; split_ifs <;> omega
  · simp only [dE, Prod.mk.injEq, Fin.mk.injEq]
    unfold dA dB; split_ifs <;> omega

theorem dL_top (N M : ℕ) : dL N M (N + M - 1) = 0 := by unfold dL; split_ifs <;> omega

/-- level `n+1` (`n < N`) is the diagonal `N+M-2-n`, of length `n+1`, entry `k` = `(n-k, M-1-k)`. -/
theorem dL_level (N M n : ℕ) (hNM : N ≤ M) (hn : n < N) : dL N M (N + M - 2 - n) = n + 1 := by
  unfold dL; split_ifs <;> omega

theorem dA_level (N M n : ℕ) (hNM : N ≤ M) (hn : n < N) : dA N M (N + M - 2 - n) = n := by
  unfold dA; split_ifs <;> omega

theorem dB_level (N M n : ℕ) (hNM : N ≤ M) (hn : n < N) : dB M (N + M - 2 - n) = M - 1 := by
  unfold dB; split_ifs <;> omega

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory B8RSK

/-- coupling condition between diagonal `d` (`z`) and diagonal `d+1` (`w`): `z ≥ 0` and weak interlacing
(Q region `d+1 < M`: `w_k ≥ z_k ≥ w_{k+1}`; P region: `z_k ≥ w_k ≥ z_{k+1}`). -/
def cIl (N M d : ℕ) (z : Fin (dL N M d) → ℝ) (w : Fin (dL N M (d + 1)) → ℝ) : Prop :=
  (∀ k, 0 ≤ z k) ∧
  (if d + 1 < M then
    (∀ k, k < dL N M d → rdv z k ≤ rdv w k ∧ (k + 1 < dL N M (d + 1) → rdv w (k + 1) ≤ rdv z k))
   else
    (∀ k, k < dL N M (d + 1) → rdv w k ≤ rdv z k ∧ (k + 1 < dL N M d → rdv z (k + 1) ≤ rdv w k)))

theorem rdv_comp {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (Z : Fin N × Fin M → ℝ) (d k : ℕ)
    (hk : k < dL N M d) : rdv (Z ∘ dE N M hN hM d) k = rd Z (dA N M d - k) (dB M d - k) := by
  unfold rdv
  rw [dif_pos hk]
  exact (rd_fin Z (dE N M hN hM d ⟨k, hk⟩)).symm

theorem rpp_nonneg {N M : ℕ} (Z : Fin N × Fin M → ℝ) (hZ : RPPf Z) :
    ∀ a b, a < N → b < M → 0 ≤ rd Z a b := by
  intro a
  induction a with
  | zero =>
    intro b _ hb
    have h := (hZ 0 b (by omega) hb).1
    simpa [upv] using h
  | succ a ih =>
    intro b ha hb
    have h := (hZ (a + 1) b ha hb).1
    simp only [upv, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at h
    exact (ih b (by omega) hb).trans h

/-- the cell read `rd Z a b` as an entry of its diagonal. -/
theorem rd_as_diag {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (Z : Fin N × Fin M → ℝ) (a b : ℕ)
    (ha : a < N) (hb : b < M) :
    dA N M (b + (N - 1) - a) - a < dL N M (b + (N - 1) - a) ∧
    rdv (Z ∘ dE N M hN hM (b + (N - 1) - a)) (dA N M (b + (N - 1) - a) - a) = rd Z a b := by
  have hk : dA N M (b + (N - 1) - a) - a < dL N M (b + (N - 1) - a) := by
    unfold dL dA; split_ifs <;> omega
  refine ⟨hk, ?_⟩
  rw [rdv_comp hN hM Z _ _ hk]
  congr 1
  · unfold dA; split_ifs <;> omega
  · unfold dA dB; split_ifs <;> omega

theorem d_cases (N M d : ℕ) :
    (d + 1 < M ∧ dA N M d = N - 1 ∧ dB M d = d ∧
      ((d < N - 1 ∧ dL N M d = d + 1) ∨ (N - 1 ≤ d ∧ dL N M d = N))) ∨
    (M ≤ d + 1 ∧ dA N M d = N + M - 2 - d ∧ dB M d = M - 1 ∧
      ((d < N + M - 1 ∧ dL N M d = N + M - 1 - d) ∨ (N + M - 1 ≤ d ∧ dL N M d = 0))) := by
  unfold dA dB dL
  by_cases h1 : d + 1 < M
  · left
    rw [if_pos h1, if_pos h1, if_pos h1]
    refine ⟨h1, rfl, rfl, ?_⟩
    by_cases h2 : d < N - 1
    · left; rw [if_pos h2]; exact ⟨h2, rfl⟩
    · right; rw [if_neg h2]; exact ⟨by omega, rfl⟩
  · right
    rw [if_neg h1, if_neg h1, if_neg h1]
    refine ⟨by omega, rfl, rfl, ?_⟩
    by_cases h3 : d < N + M - 1
    · left; rw [if_pos h3]; exact ⟨h3, rfl⟩
    · right; rw [if_neg h3]; exact ⟨by omega, rfl⟩

theorem up_le {N M : ℕ} {Z : Fin N × Fin M → ℝ} (hZ : RPPf Z) (a b : ℕ) (ha : a < N) (hb : b < M)
    (h0 : a ≠ 0) : rd Z (a - 1) b ≤ rd Z a b := by
  have h := (hZ a b ha hb).1
  simpa [upv, h0] using h

theorem left_le {N M : ℕ} {Z : Fin N × Fin M → ℝ} (hZ : RPPf Z) (a b : ℕ) (ha : a < N) (hb : b < M)
    (h0 : b ≠ 0) : rd Z a (b - 1) ≤ rd Z a b := by
  have h := (hZ a b ha hb).2
  simpa [lfv, h0] using h

theorem rdv_nonneg_of {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (Z : Fin N × Fin M → ℝ) (d : ℕ)
    (h : ∀ k, 0 ≤ (Z ∘ dE N M hN hM d) k) (k : ℕ) : 0 ≤ rdv (Z ∘ dE N M hN hM d) k := by
  unfold rdv; split_ifs
  · exact h _
  · exact le_rfl

theorem left_arith (N M d' a b : ℕ) (hNM : N ≤ M) (ha : a < N) (hb : b < M) (hb0 : b ≠ 0)
    (hd' : d' + 1 = b + (N - 1) - a) :
    (d' + 1 < M → dA N M (d' + 1) - a < dL N M d' ∧
      dA N M d' - (dA N M (d' + 1) - a) = a ∧ dB M d' - (dA N M (d' + 1) - a) = b - 1) ∧
    (¬ d' + 1 < M → dA N M (d' + 1) - a + 1 < dL N M d' ∧
      dA N M d' - (dA N M (d' + 1) - a + 1) = a ∧ dB M d' - (dA N M (d' + 1) - a + 1) = b - 1) := by
  have c0 := d_cases N M d'
  have c3 := d_cases N M (d' + 1)
  generalize dA N M d' = A0 at c0 ⊢
  generalize dA N M (d' + 1) = A1 at c3 ⊢
  generalize dB M d' = B0 at c0 ⊢
  generalize dB M (d' + 1) = B1 at c3 ⊢
  generalize dL N M d' = L0 at c0 ⊢
  generalize dL N M (d' + 1) = L1 at c3 ⊢
  constructor
  · intro hQ
    rcases c0 with h0 | h0 <;> rcases c3 with h3 | h3 <;> omega
  · intro hQ
    rcases c0 with h0 | h0 <;> rcases c3 with h3 | h3 <;> omega

theorem rpp_iff_cIl {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (Z : Fin N × Fin M → ℝ) :
    RPPf Z ↔ ∀ d, d < N + M - 1 → cIl N M d (Z ∘ dE N M hN hM d) (Z ∘ dE N M hN hM (d + 1)) := by
  constructor
  · intro hZ d hd
    refine ⟨fun k => ?_, ?_⟩
    · show 0 ≤ Z (dE N M hN hM d k)
      rw [← rd_fin Z (dE N M hN hM d k)]
      exact rpp_nonneg Z hZ _ _ (Fin.isLt _) (Fin.isLt _)
    have c1 := d_cases N M d
    have c2 := d_cases N M (d + 1)
    split_ifs with hQ
    · intro k hk
      have hk' : k < dL N M (d + 1) := by omega
      rw [rdv_comp hN hM Z d k hk, rdv_comp hN hM Z (d + 1) k hk']
      refine ⟨?_, fun hk2 => ?_⟩
      · have h := left_le hZ (dA N M (d + 1) - k) (dB M (d + 1) - k) (by omega) (by omega) (by omega)
        have e1 : dA N M d - k = dA N M (d + 1) - k := by omega
        have e2 : dB M d - k = dB M (d + 1) - k - 1 := by omega
        rw [e1, e2]; exact h
      · rw [rdv_comp hN hM Z (d + 1) (k + 1) hk2]
        have h := up_le hZ (dA N M d - k) (dB M d - k) (by omega) (by omega) (by omega)
        have e1 : dA N M (d + 1) - (k + 1) = dA N M d - k - 1 := by omega
        have e2 : dB M (d + 1) - (k + 1) = dB M d - k := by omega
        rw [e1, e2]; exact h
    · intro k hk
      have hk' : k < dL N M d := by omega
      rw [rdv_comp hN hM Z d k hk', rdv_comp hN hM Z (d + 1) k hk]
      refine ⟨?_, fun hk2 => ?_⟩
      · have h := up_le hZ (dA N M d - k) (dB M d - k) (by omega) (by omega) (by omega)
        have e1 : dA N M (d + 1) - k = dA N M d - k - 1 := by omega
        have e2 : dB M (d + 1) - k = dB M d - k := by omega
        rw [e1, e2]; exact h
      · rw [rdv_comp hN hM Z d (k + 1) hk2]
        have h := left_le hZ (dA N M (d + 1) - k) (dB M (d + 1) - k) (by omega) (by omega) (by omega)
        have e1 : dA N M d - (k + 1) = dA N M (d + 1) - k := by omega
        have e2 : dB M d - (k + 1) = dB M (d + 1) - k - 1 := by omega
        rw [e1, e2]; exact h
  · intro h a b ha hb
    obtain ⟨d, hdd⟩ : ∃ d, d = b + (N - 1) - a := ⟨_, rfl⟩
    have hd : d < N + M - 1 := by omega
    obtain ⟨hk, hr⟩ := rd_as_diag hN hM hNM Z a b ha hb
    rw [← hdd] at hk hr
    have hnn : 0 ≤ rd Z a b := hr ▸ rdv_nonneg_of hN hM Z d (h d hd).1 _
    have c1 := d_cases N M d
    have c2 := d_cases N M (d + 1)
    constructor
    · by_cases a0 : a = 0
      · simpa [upv, a0] using hnn
      simp only [upv, a0, if_false]
      have hc := (h d hd).2
      split_ifs at hc with hQ
      · have hk2 : dA N M d - a + 1 < dL N M (d + 1) := by omega
        have h1 := (hc _ hk).2 hk2
        rw [hr, rdv_comp hN hM Z (d + 1) _ hk2] at h1
        have e1 : dA N M (d + 1) - (dA N M d - a + 1) = a - 1 := by omega
        have e2 : dB M (d + 1) - (dA N M d - a + 1) = b := by omega
        rw [e1, e2] at h1; exact h1
      · have hk2 : dA N M d - a < dL N M (d + 1) := by omega
        have h1 := (hc _ hk2).1
        rw [hr, rdv_comp hN hM Z (d + 1) _ hk2] at h1
        have e1 : dA N M (d + 1) - (dA N M d - a) = a - 1 := by omega
        have e2 : dB M (d + 1) - (dA N M d - a) = b := by omega
        rw [e1, e2] at h1; exact h1
    · by_cases b0 : b = 0
      · simpa [lfv, b0] using hnn
      simp only [lfv, b0, if_false]
      obtain ⟨d', hd'⟩ : ∃ d', d' + 1 = b + (N - 1) - a := ⟨b + (N - 1) - a - 1, by omega⟩
      clear c1 c2 hk hr hdd
      have c0 := d_cases N M d'
      have c3 := d_cases N M (d' + 1)
      have hk' : dA N M (d' + 1) - a < dL N M (d' + 1) := by omega
      have E1 : dA N M (d' + 1) - (dA N M (d' + 1) - a) = a := by omega
      have E2 : dB M (d' + 1) - (dA N M (d' + 1) - a) = b := by omega
      have hd'' : d' < N + M - 1 := by omega
      obtain ⟨A1, A2⟩ := left_arith N M d' a b hNM ha hb b0 hd'
      clear c0 c3
      have hr' : rdv (Z ∘ dE N M hN hM (d' + 1)) (dA N M (d' + 1) - a) = rd Z a b := by
        rw [rdv_comp hN hM Z _ _ hk', E1, E2]
      have hc := (h d' hd'').2
      split_ifs at hc with hQ
      · obtain ⟨hk2, e1, e2⟩ := A1 hQ
        have h1 := (hc _ hk2).1
        rw [hr', rdv_comp hN hM Z d' _ hk2, e1, e2] at h1
        exact h1
      · obtain ⟨hk2, e1, e2⟩ := A2 hQ
        have h1 := (hc _ hk').2 hk2
        rw [hr', rdv_comp hN hM Z d' _ hk2, e1, e2] at h1
        exact h1

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory B8RSK Finset

theorem dsum_eq_sum (w : ℕ → ℕ → ℝ) : ∀ a b, dsum w a b = ∑ k ∈ range (min a b + 1), w (a - k) (b - k) := by
  intro a
  induction a with
  | zero => intro b; simp [dsum]
  | succ a ih =>
    intro b
    cases b with
    | zero => simp [dsum]
    | succ b =>
      show w (a + 1) (b + 1) + dsum w a b = _
      rw [ih b, Nat.add_min_add_right, Finset.sum_range_succ' (fun k => w (a + 1 - k) (b + 1 - k))]
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      ring

theorem sum_rdv {L : ℕ} (z : Fin L → ℝ) : ∑ k ∈ range L, rdv z k = ∑ k, z k := by
  rw [← Fin.sum_univ_eq_sum_range (rdv z)]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold rdv
  rw [dif_pos k.isLt]

theorem blk_sum {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (Z : Fin N × Fin M → ℝ) (d : ℕ) :
    ∑ k, (Z ∘ dE N M hN hM d) k = ∑ k ∈ range (dL N M d), rd Z (dA N M d - k) (dB M d - k) := by
  rw [← sum_rdv]
  exact Finset.sum_congr rfl fun k hk => rdv_comp hN hM Z d k (Finset.mem_range.mp hk)

theorem level_sum {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (Z : Fin N × Fin M → ℝ) (n : ℕ)
    (hn : n < N) : ∑ k, (Z ∘ dE N M hN hM (N + M - 2 - n)) k = dsum (rd Z) n (M - 1) := by
  rw [blk_sum, dL_level N M n hNM hn, dA_level N M n hNM hn, dB_level N M n hNM hn, dsum_eq_sum,
    show min n (M - 1) = n by omega]

/-- `π` read at natural indices. -/
noncomputable def pnat {N : ℕ} (π : Fin N → ℝ) (j : ℕ) : ℝ := if h : j < N then π ⟨j, h⟩ else 0

open Classical in
/-- the coupling of diagonals `d` and `d+1`. -/
noncomputable def cpl (N M : ℕ) (π : Fin N → ℝ) (x : ℝ) (d : ℕ) (z : Fin (dL N M d) → ℝ)
    (w : Fin (dL N M (d + 1)) → ℝ) : ENNReal :=
  (if cIl N M d z w then 1 else 0) * (if d = M - 1 then (if rdv z 0 ≤ x then 1 else 0) else 1) *
    (if M ≤ d + 1 then ENNReal.ofReal ((pnat π (N + M - 2 - d) * M) ^ M *
      Real.exp (-(pnat π (N + M - 2 - d) * M) * (∑ k, z k - ∑ k, w k))) else 1)

theorem gR_eq_prod {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (x : ℝ)
    (Z : Fin N × Fin M → ℝ) :
    gR N M π x Z = ∏ d ∈ range (N + M - 1), cpl N M π x d (Z ∘ dE N M hN hM d) (Z ∘ dE N M hN hM (d + 1)) := by
  classical
  set K := N + M - 1 with hK
  let F : ℕ → ENNReal := fun n => ENNReal.ofReal ((pnat π n * M) ^ M * Real.exp (-(pnat π n * M) * rowW Z n))
  unfold cpl
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_boole, Finset.prod_ite_eq']
  -- interlacing part
  have hI : (∀ d ∈ range K, cIl N M d (Z ∘ dE N M hN hM d) (Z ∘ dE N M hN hM (d + 1))) ↔ RPPf Z := by
    rw [rpp_iff_cIl hN hM hNM Z]
    simp only [Finset.mem_range]
    exact Iff.rfl
  -- corner part
  have hMK : M - 1 ∈ range K := Finset.mem_range.mpr (by omega)
  have hC : rdv (Z ∘ dE N M hN hM (M - 1)) 0 = rd Z (N - 1) (M - 1) := by
    have c := d_cases N M (M - 1)
    have h0 : 0 < dL N M (M - 1) := by omega
    rw [rdv_comp hN hM Z _ _ h0]
    congr 1 <;> omega
  -- weight part
  have hW : ∀ d ∈ range K, (if M ≤ d + 1 then ENNReal.ofReal ((pnat π (N + M - 2 - d) * M) ^ M *
      Real.exp (-(pnat π (N + M - 2 - d) * M) *
        (∑ k, (Z ∘ dE N M hN hM d) k - ∑ k, (Z ∘ dE N M hN hM (d + 1)) k))) else 1) =
      (if M ≤ d + 1 then F (K - 1 - d) else 1) := by
    intro d hd
    have hd' := Finset.mem_range.mp hd
    by_cases hMd : M ≤ d + 1
    · rw [if_pos hMd, if_pos hMd]
      obtain ⟨n, hn, rfl⟩ : ∃ n, n < N ∧ d = N + M - 2 - n := ⟨N + M - 2 - d, by omega, by omega⟩
      have hKn : K - 1 - (N + M - 2 - n) = n := by omega
      rw [hKn]
      have hS : ∑ k, (Z ∘ dE N M hN hM (N + M - 2 - n)) k - ∑ k, (Z ∘ dE N M hN hM (N + M - 2 - n + 1)) k
          = rowW Z n := by
        rw [level_sum hN hM hNM Z n hn]
        unfold rowW
        congr 1
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0
          rw [if_pos rfl, blk_sum, show N + M - 2 - 0 + 1 = N + M - 1 by omega, dL_top]
          simp
        · rw [if_neg (by omega), blk_sum, show N + M - 2 - n + 1 = N + M - 2 - (n - 1) by omega,
            dL_level N M (n - 1) hNM (by omega), dA_level N M (n - 1) hNM (by omega),
            dB_level N M (n - 1) hNM (by omega), dsum_eq_sum, show min (n - 1) (M - 1) = n - 1 by omega]
      rw [hS, show N + M - 2 - (N + M - 2 - n) = n by omega]
    · rw [if_neg hMd, if_neg hMd]
  rw [Finset.prod_congr rfl hW]
  have hW2 : ∏ d ∈ range K, (if M ≤ d + 1 then F (K - 1 - d) else 1) = ∏ n ∈ range N, F n := by
    rw [← Finset.prod_range_reflect]
    have : ∀ j ∈ range K, (if M ≤ K - 1 - j + 1 then F (K - 1 - (K - 1 - j)) else 1) =
        (if j < N then F j else 1) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_cases hjN : j < N
      · rw [if_pos (by omega), if_pos hjN, show K - 1 - (K - 1 - j) = j by omega]
      · rw [if_neg (by omega), if_neg hjN]
    rw [Finset.prod_congr rfl this, ← Finset.prod_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hW2]
  have hwR : wR N M π Z = ∏ n ∈ range N, F n := by
    unfold wR
    rw [← Fin.prod_univ_eq_prod_range F]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : pnat π (i : ℕ) = π i := by unfold pnat; rw [dif_pos i.isLt]
    simp only [F, this]
  rw [← hwR, if_pos hMK, hC]
  unfold gR rppSet
  by_cases h1 : RPPf Z
  · by_cases h2 : rd Z (N - 1) (M - 1) ≤ x
    · rw [Set.indicator_of_mem (show Z ∈ {Z | RPPf Z ∧ rd Z (N - 1) (M - 1) ≤ x} from ⟨h1, h2⟩),
        if_pos (hI.mpr h1), if_pos h2, one_mul, one_mul]
    · rw [Set.indicator_of_notMem (show Z ∉ {Z | RPPf Z ∧ rd Z (N - 1) (M - 1) ≤ x} from fun h => h2 h.2),
        if_neg h2, mul_zero, zero_mul]
  · rw [Set.indicator_of_notMem (show Z ∉ {Z | RPPf Z ∧ rd Z (N - 1) (M - 1) ≤ x} from fun h => h1 h.1),
      if_neg (fun h => h1 (hI.mp h)), zero_mul, zero_mul]

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory B8RSK Finset

theorem measurable_rdv {L : ℕ} (k : ℕ) : Measurable (fun z : Fin L → ℝ => rdv z k) := by
  by_cases h : k < L
  · simp only [rdv, dif_pos h]
    exact measurable_pi_apply _
  · simp only [rdv, dif_neg h]
    exact measurable_const

theorem measurable_cIl (N M d : ℕ) :
    Measurable (fun p : (Fin (dL N M d) → ℝ) × (Fin (dL N M (d + 1)) → ℝ) => cIl N M d p.1 p.2) := by
  unfold cIl
  refine Measurable.and (Measurable.forall fun k => ?_) ?_
  · exact measurableSet_setOfPred.mp
      (measurableSet_le measurable_const ((measurable_pi_apply k).comp measurable_fst))
  · by_cases hQ : d + 1 < M
    · simp only [if_pos hQ]
      refine Measurable.forall fun k => Measurable.imp measurable_const
        (Measurable.and ?_ (Measurable.imp measurable_const ?_))
      · exact measurableSet_setOfPred.mp
          (measurableSet_le ((measurable_rdv k).comp measurable_fst) ((measurable_rdv k).comp measurable_snd))
      · exact measurableSet_setOfPred.mp
          (measurableSet_le ((measurable_rdv (k + 1)).comp measurable_snd) ((measurable_rdv k).comp measurable_fst))
    · simp only [if_neg hQ]
      refine Measurable.forall fun k => Measurable.imp measurable_const
        (Measurable.and ?_ (Measurable.imp measurable_const ?_))
      · exact measurableSet_setOfPred.mp
          (measurableSet_le ((measurable_rdv k).comp measurable_snd) ((measurable_rdv k).comp measurable_fst))
      · exact measurableSet_setOfPred.mp
          (measurableSet_le ((measurable_rdv (k + 1)).comp measurable_fst) ((measurable_rdv k).comp measurable_snd))

theorem measurable_cpl (N M : ℕ) (π : Fin N → ℝ) (x : ℝ) (d : ℕ) :
    Measurable (Function.uncurry (cpl N M π x d)) := by
  classical
  show Measurable fun p : (Fin (dL N M d) → ℝ) × (Fin (dL N M (d + 1)) → ℝ) => cpl N M π x d p.1 p.2
  unfold cpl
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact Measurable.ite (measurableSet_setOfPred.mpr (measurable_cIl N M d)) measurable_const measurable_const
  · by_cases hd : d = M - 1
    · simp only [if_pos hd]
      exact Measurable.ite (measurableSet_le ((measurable_rdv 0).comp measurable_fst) measurable_const)
        measurable_const measurable_const
    · simp only [if_neg hd]
      exact measurable_const
  · by_cases hd : M ≤ d + 1
    · simp only [if_pos hd]
      refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul (Measurable.sub ?_ ?_))))
      · exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).comp measurable_fst
      · exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).comp measurable_snd
    · simp only [if_neg hd]
      exact measurable_const

/-- the RPP integral as the block-chain integral over the `N+M-1` diagonals. -/
theorem gR_lintegral_bcT {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (x : ℝ) :
    ∫⁻ Z, gR N M π x Z =
      bcT (dL N M) (cpl N M π x) (N + M - 1) ((0 : Fin N × Fin M → ℝ) ∘ dE N M hN hM (N + M - 1)) := by
  rw [lintegral_congr (fun Z => gR_eq_prod hN hM hNM π x Z)]
  exact bc_lintegral (dL N M) (dE N M hN hM) (cpl N M π x) (N + M - 1) (dE_injective N M hN hM hNM)
    (fun d d' l l' _ _ hne => dE_disj N M hN hM hNM d d' l l' hne) (dE_cover N M hN hM hNM)
    (measurable_cpl N M π x) 0

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory

theorem lintegral_pi_smul {ι : Type*} [Fintype ι] (c : ℝ) (hc : c ≠ 0) (f : (ι → ℝ) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ Z : ι → ℝ, f (c • Z) = ENNReal.ofReal |(c ^ Fintype.card ι)⁻¹| * ∫⁻ Z : ι → ℝ, f Z := by
  set g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := c • LinearMap.id with hg
  have hdet : LinearMap.det g = c ^ Fintype.card ι := by
    rw [hg, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fintype_fun_eq_card]
  have hdet0 : LinearMap.det g ≠ 0 := by rw [hdet]; exact pow_ne_zero _ hc
  have key := lintegral_map (μ := (volume : Measure (ι → ℝ))) hf
    (LinearMap.continuous_of_finiteDimensional g).measurable
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, lintegral_smul_measure, hdet] at key
  rw [smul_eq_mul] at key
  rw [key]
  rfl

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory B8RSK Finset

theorem rd_smul {N M : ℕ} (c : ℝ) (Z : Fin N × Fin M → ℝ) :
    rd (c • Z) = fun a b => c * rd Z a b := by
  funext a b
  unfold rd
  split_ifs <;> simp

theorem upv_smul (c : ℝ) (w : ℕ → ℕ → ℝ) (a b : ℕ) :
    upv (fun a b => c * w a b) a b = c * upv w a b := by
  unfold upv; split_ifs <;> simp

theorem lfv_smul (c : ℝ) (w : ℕ → ℕ → ℝ) (a b : ℕ) :
    lfv (fun a b => c * w a b) a b = c * lfv w a b := by
  unfold lfv; split_ifs <;> simp

theorem dsum_smul (c : ℝ) (w : ℕ → ℕ → ℝ) : ∀ a b, dsum (fun a b => c * w a b) a b = c * dsum w a b
  | 0, b => rfl
  | a + 1, 0 => rfl
  | a + 1, b + 1 => by
    show c * w (a + 1) (b + 1) + dsum (fun a b => c * w a b) a b = c * (w (a + 1) (b + 1) + dsum w a b)
    rw [dsum_smul c w a b]; ring

theorem rowW_smul {N M : ℕ} (c : ℝ) (Z : Fin N × Fin M → ℝ) (a : ℕ) :
    rowW (c • Z) a = c * rowW Z a := by
  unfold rowW
  rw [rd_smul, dsum_smul, dsum_smul]
  split_ifs <;> ring

theorem rppf_smul {N M : ℕ} {c : ℝ} (hc : 0 < c) (Z : Fin N × Fin M → ℝ) :
    RPPf (c • Z) ↔ RPPf Z := by
  unfold RPPf
  rw [rd_smul]
  simp only [upv_smul, lfv_smul]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [mul_le_mul_iff_of_pos_left hc, mul_le_mul_iff_of_pos_left hc]

theorem gR_smul_pt {N M : ℕ} (hM : 0 < M) (π : Fin N → ℝ) (x : ℝ) (Z : Fin N × Fin M → ℝ) :
    gR N M π x Z = ENNReal.ofReal ((M : ℝ) ^ (N * M)) *
      gR N M (fun i => π i / M) (M * x) ((M : ℝ) • Z) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hmem : (M : ℝ) • Z ∈ rppSet N M (M * x) ↔ Z ∈ rppSet N M x := by
    simp only [rppSet, Set.mem_setOf_eq]
    rw [rppf_smul hMr, rd_smul]
    simp only
    rw [mul_le_mul_iff_of_pos_left hMr]
  unfold gR
  by_cases hZ : Z ∈ rppSet N M x
  · rw [Set.indicator_of_mem hZ, Set.indicator_of_mem (hmem.2 hZ)]
    unfold wR
    have hb : ∀ i : Fin N, (π i * M) ^ M * Real.exp (-(π i * M) * rowW Z i) =
        (M : ℝ) ^ M * ((π i / M * M) ^ M * Real.exp (-(π i / M * M) * rowW ((M : ℝ) • Z) i)) := by
      intro i
      rw [div_mul_cancel₀ _ hMr.ne', rowW_smul, mul_pow]
      ring_nf
    simp_rw [hb]
    simp_rw [ENNReal.ofReal_mul (pow_nonneg hMr.le M)]
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (pow_nonneg hMr.le M),
      ← pow_mul, mul_comm M N]
  · rw [Set.indicator_of_notMem hZ, Set.indicator_of_notMem (fun h => hZ (hmem.1 h)), mul_zero]

end SWL302

namespace SWL302

open MeasureTheory B8RSK

theorem rpp_scale {N M : ℕ} (hM : 0 < M) (π : Fin N → ℝ) (x : ℝ) :
    ∫⁻ Z, gR N M π x Z = ∫⁻ Z, gR N M (fun i => π i / M) (M * x) Z := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  rw [lintegral_congr (fun Z => gR_smul_pt hM π x Z), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_pi_smul (M : ℝ) hMr.ne' _ (measurable_gR N M _ _), ← mul_assoc,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, abs_of_pos (inv_pos.mpr (pow_pos hMr _)),
    ← ENNReal.ofReal_mul (pow_nonneg hMr.le _), mul_inv_cancel₀ (pow_pos hMr _).ne', ENNReal.ofReal_one, one_mul]

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory Set SpikedWishart.Separated.Lib.Weyl

theorem rdv_eq {L : ℕ} (z : Fin L → ℝ) (j : Fin L) (k : ℕ) (h : k = j) : rdv z k = z j := by
  subst h; simp [rdv]

theorem rdv_out {L : ℕ} (z : Fin L → ℝ) (k : ℕ) (h : L ≤ k) : rdv z k = 0 := by
  unfold rdv; rw [dif_neg (by omega)]

theorem rdv_snoc0 {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : rdv (snoc0 w) k = rdv w k := by
  unfold rdv snoc0 Fin.snoc
  split_ifs <;> first | rfl | omega | simp

/-- weak Q coupling: `w_{k+1} ≤ z_k ≤ w_k`, `z ≥ 0`. -/
def wQ {m m' : ℕ} (z : Fin m → ℝ) (w : Fin m' → ℝ) : Prop :=
  (∀ k, 0 ≤ z k) ∧ ∀ k, k < m → rdv z k ≤ rdv w k ∧ (k + 1 < m' → rdv w (k + 1) ≤ rdv z k)

/-- weak P coupling: `z_{k+1} ≤ w_k ≤ z_k`, `z ≥ 0`. -/
def wP {m m' : ℕ} (z : Fin m → ℝ) (w : Fin m' → ℝ) : Prop :=
  (∀ k, 0 ≤ z k) ∧ ∀ k, k < m' → rdv w k ≤ rdv z k ∧ (k + 1 < m → rdv z (k + 1) ≤ rdv w k)

theorem ae_avoid {m L : ℕ} (w : Fin L → ℝ) : ∀ᵐ z : Fin m → ℝ, ∀ j k, z j ≠ rdv w k := by
  rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k
  exact Measure.ae_eval_ne _ j _

theorem mem_box_rdv {n : ℕ} (w : Fin (n + 1) → ℝ) (z : Fin n → ℝ) :
    z ∈ box w ↔ ∀ i : Fin n, rdv w (i + 1) < z i ∧ z i < rdv w i := by
  simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  refine forall_congr' fun i => ?_
  rw [rdv_eq w i.succ (i + 1) (by simp), rdv_eq w i.castSucc i (by simp)]

theorem mem_box_snoc0_rdv {n : ℕ} (w : Fin n → ℝ) (z : Fin n → ℝ) :
    z ∈ box (snoc0 w) ↔ ∀ i : Fin n, rdv w (i + 1) < z i ∧ z i < rdv w i := by
  rw [mem_box_rdv]
  refine forall_congr' fun i => ?_
  rw [rdv_snoc0 w _ (by omega), rdv_snoc0 w _ (by omega)]

theorem wQ_iff {n m' : ℕ} (z : Fin n → ℝ) (w : Fin m' → ℝ) (hw : ∀ k, 0 ≤ rdv w k)
    (hz : ∀ j k, z j ≠ rdv w k) : wQ z w ↔ ∀ i : Fin n, rdv w (i + 1) < z i ∧ z i < rdv w i := by
  constructor
  · rintro ⟨h0, h⟩ i
    have h1 := (h i i.isLt).1
    rw [rdv_eq z i i rfl] at h1
    refine ⟨lt_of_le_of_ne ?_ (Ne.symm (hz i (i + 1))), lt_of_le_of_ne h1 (hz i i)⟩
    by_cases hi : (i : ℕ) + 1 < m'
    · have h2 := (h i i.isLt).2 hi
      rwa [rdv_eq z i i rfl] at h2
    · rw [rdv_out w _ (by omega)]; exact h0 i
  · intro h
    refine ⟨fun k => le_trans (hw _) (h k).1.le, fun k hk => ?_⟩
    rw [rdv_eq z ⟨k, hk⟩ k rfl]
    exact ⟨(h ⟨k, hk⟩).2.le, fun _ => (h ⟨k, hk⟩).1.le⟩

theorem wP_iff {n : ℕ} (z : Fin (n + 1) → ℝ) (w : Fin n → ℝ) (hz : ∀ j k, z j ≠ rdv w k) :
    wP z w ↔ z ∈ Ilace w ∧ 0 < z (Fin.last n) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨fun i => ?_, lt_of_le_of_ne (h0 _) (fun he => hz (Fin.last n) n (by rw [rdv_out w n le_rfl]; exact he.symm))⟩
    have h1 := (h i i.isLt).1
    have h2 := (h i i.isLt).2 (by omega)
    rw [rdv_eq w i i rfl, rdv_eq z i.castSucc i (by simp)] at h1
    rw [rdv_eq w i i rfl, rdv_eq z i.succ (i + 1) (by simp)] at h2
    refine ⟨lt_of_le_of_ne h1 (fun he => hz i.castSucc i (by rw [rdv_eq w i i rfl]; exact he.symm)),
      lt_of_le_of_ne h2 (fun he => hz i.succ i (by rw [rdv_eq w i i rfl]; exact he))⟩
  · rintro ⟨hI, hl⟩
    have sa := ilace_strictAnti hI
    refine ⟨fun k => (lt_of_lt_of_le hl (sa.antitone (Fin.le_last k))).le, fun k hk => ?_⟩
    have hi := hI ⟨k, hk⟩
    rw [rdv_eq w ⟨k, hk⟩ k rfl, rdv_eq z (Fin.castSucc ⟨k, hk⟩) k rfl]
    refine ⟨hi.1.le, fun _ => ?_⟩
    rw [rdv_eq z (Fin.succ ⟨k, hk⟩) (k + 1) rfl]
    exact hi.2.le

theorem rdv_nonneg_good {L : ℕ} {w : Fin L → ℝ} (hw : w ∈ Good L) (k : ℕ) : 0 ≤ rdv w k := by
  unfold rdv; split_ifs
  · exact (hw.2 _).le
  · exact le_rfl

theorem good_of_box {n : ℕ} {w : Fin (n + 1) → ℝ} (hw : w ∈ Good (n + 1)) {z : Fin n → ℝ} (hb : z ∈ box w) :
    z ∈ Good n :=
  ⟨ilace_mu_strictAnti (mem_box_iff.1 hb), fun i => lt_trans (hw.2 _) (hb i (Set.mem_univ i)).1⟩

theorem good_of_box_snoc0 {n : ℕ} {w : Fin n → ℝ} {z : Fin n → ℝ} (hb : z ∈ box (snoc0 w)) : z ∈ Good n := by
  have sa := ilace_mu_strictAnti (mem_box_iff.1 hb)
  refine ⟨sa, fun i => ?_⟩
  have hl : n - 1 < n := by have := i.isLt; omega
  have h := ((mem_box_snoc0_rdv w z).1 hb ⟨n - 1, hl⟩).1
  rw [rdv_out w _ (by show n ≤ n - 1 + 1; omega)] at h
  exact lt_of_lt_of_le h (sa.antitone (by rw [Fin.le_iff_val_le_val]; show (i : ℕ) ≤ n - 1; have := i.isLt; omega))

/-- growing Q step: `∫ 1{wQ z w} T z = vdm w / (K m!)`. -/
theorem stepQG {m m' : ℕ} (h : m' = m + 1) (w : Fin m' → ℝ) (hw : w ∈ Good m') (K : ℝ) (hK : 0 < K)
    (F : (Fin m → ℝ) → ENNReal) (hF : ∀ z, z ∈ Good m → wQ z w → F z = ENNReal.ofReal (vdm z / K))
    (hF0 : ∀ z, ¬ wQ z w → F z = 0) :
    ∫⁻ z, F z = ENNReal.ofReal (vdm w / (K * (m.factorial : ℝ))) := by
  subst h
  have hae : ∀ᵐ z : Fin m → ℝ, F z = (box w).indicator (fun z => ENNReal.ofReal (vdm z) * ENNReal.ofReal K⁻¹) z := by
    filter_upwards [ae_avoid (m := m) w] with z hz
    have hiff : wQ z w ↔ z ∈ box w := by
      rw [wQ_iff z w (rdv_nonneg_good hw) hz, mem_box_rdv]
    by_cases hc : wQ z w
    · have hb := hiff.1 hc
      rw [Set.indicator_of_mem hb, hF z (good_of_box hw hb) hc, div_eq_mul_inv,
        ENNReal.ofReal_mul (vdm_nonneg _)]
    · rw [hF0 z hc, Set.indicator_of_notMem (fun hb => hc (hiff.2 hb))]
  rw [lintegral_congr_ae hae, lintegral_indicator (measurableSet_box w),
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_box_vdm hw.1,
    ← ENNReal.ofReal_mul (div_nonneg (vdm_nonneg _) (Nat.cast_nonneg _))]
  congr 1
  field_simp

/-- constant Q step: `∫ 1{wQ z w} vdm z (∏ z)^a / K = vdm w (∏ w)^(a+1) (a!/(m+a)!) / K`. -/
theorem stepQC {m m' : ℕ} (h : m' = m) (w : Fin m' → ℝ) (hw : w ∈ Good m') (a : ℕ) (K : ℝ) (hK : 0 < K)
    (F : (Fin m → ℝ) → ENNReal)
    (hF : ∀ z, z ∈ Good m → wQ z w → F z = ENNReal.ofReal (vdm z * (∏ i, z i) ^ a / K))
    (hF0 : ∀ z, ¬ wQ z w → F z = 0) :
    ∫⁻ z, F z = ENNReal.ofReal (vdm w * (∏ i, w i) ^ (a + 1) *
      ((a.factorial : ℝ) / ((m + a).factorial : ℝ)) / K) := by
  subst h
  have hae : ∀ᵐ z : Fin m' → ℝ, F z = (box (snoc0 w)).indicator
      (fun z => ENNReal.ofReal (vdm z * (∏ i, z i) ^ a) * ENNReal.ofReal K⁻¹) z := by
    filter_upwards [ae_avoid (m := m') w] with z hz
    have hiff : wQ z w ↔ z ∈ box (snoc0 w) := by
      rw [wQ_iff z w (rdv_nonneg_good hw) hz, mem_box_snoc0_rdv]
    by_cases hc : wQ z w
    · have hb := hiff.1 hc
      have hg := good_of_box_snoc0 hb
      rw [Set.indicator_of_mem hb, hF z hg hc, div_eq_mul_inv,
        ENNReal.ofReal_mul (mul_nonneg (vdm_nonneg _) (pow_nonneg (Finset.prod_nonneg fun i _ => (hg.2 i).le) _))]
    · rw [hF0 z hc, Set.indicator_of_notMem (fun hb => hc (hiff.2 hb))]
  rw [lintegral_congr_ae hae, lintegral_indicator (measurableSet_box _),
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hint := integral_box_snoc0_pow hw.1 hw.2 a
  have hnn : ∀ z ∈ box (snoc0 w), 0 ≤ vdm z * (∏ i, z i) ^ a := fun z hz =>
    mul_nonneg (vdm_nonneg _) (pow_nonneg (Finset.prod_nonneg fun i _ => ((good_of_box_snoc0 hz).2 i).le) _)
  rw [← ofReal_integral_eq_lintegral_ofReal, hint, ← ENNReal.ofReal_mul]
  · congr 1
  · exact mul_nonneg (mul_nonneg (vdm_nonneg _) (pow_nonneg (Finset.prod_nonneg fun i _ => (hw.2 i).le) _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hI : IntegrableOn (fun z : Fin m' → ℝ => vdm z * (∏ i, z i) ^ a)
        (Set.Icc (fun i => (snoc0 w) i.succ) (fun i => (snoc0 w) i.castSucc)) :=
      (Continuous.integrableOn_Icc (continuous_vdm.mul ((continuous_finsetProd _ fun i _ => continuous_apply i).pow a)))
    exact hI.mono_set (box_subset_Icc _)
  · exact (ae_restrict_iff' (measurableSet_box _)).2 (Filter.Eventually.of_forall hnn)

/-- P step: weak coupling + `z ≥ 0` is a.e. the strict `Ilace` with positive last entry. -/
theorem stepP {n : ℕ} (w : Fin n → ℝ) (F G : (Fin (n + 1) → ℝ) → ENNReal)
    (hF : ∀ z, z ∈ Good (n + 1) → wP z w → F z = G z) (hF0 : ∀ z, ¬ wP z w → F z = 0) :
    ∫⁻ z, F z = ∫⁻ z in Ilace w, (if 0 < z (Fin.last n) then 1 else 0) * G z := by
  rw [← lintegral_indicator (measurableSet_Ilace w)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_avoid (m := n + 1) w] with z hz
  have hiff := wP_iff z w hz
  by_cases hc : wP z w
  · have hI := (hiff.1 hc)
    rw [Set.indicator_of_mem hI.1, if_pos hI.2, one_mul,
      hF z ⟨ilace_strictAnti hI.1, fun k => lt_of_lt_of_le hI.2 ((ilace_strictAnti hI.1).antitone (Fin.le_last k))⟩ hc]
  · rw [hF0 z hc]
    by_cases hI : z ∈ Ilace w
    · rw [Set.indicator_of_mem hI, if_neg (fun hl => hc (hiff.2 ⟨hI, hl⟩)), zero_mul]
    · rw [Set.indicator_of_notMem hI]

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory Set Finset B8RSK SpikedWishart.Separated.Lib.Weyl

/-- Q-phase normalisation `∏_{i<d} (i+1)!/(i+1-N)!`. -/
noncomputable def Kq (N d : ℕ) : ℝ :=
  ∏ i ∈ range d, (((i + 1).factorial : ℝ) / ((i + 1 - N).factorial : ℝ))

theorem Kq_succ (N d : ℕ) : Kq N (d + 1) = Kq N d * (((d + 1).factorial : ℝ) / ((d + 1 - N).factorial : ℝ)) := by
  unfold Kq; rw [prod_range_succ]

theorem Kq_pos (N d : ℕ) : 0 < Kq N d :=
  prod_pos fun _ _ => div_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) (Nat.cast_pos.2 (Nat.factorial_pos _))

theorem Pf_eq (M : ℕ) : ∀ k, Pf M k = ∏ n ∈ range k, ((M - n - 1).factorial : ℝ)
  | 0 => by simp [Pf]
  | k + 1 => by rw [prod_range_succ, ← Pf_eq M k]; rfl

theorem Pf_succ_M (M : ℕ) : ∀ k, k ≤ M → Pf (M + 1) k * ((M - k).factorial : ℝ) = Pf M k * (M.factorial : ℝ)
  | 0, _ => by simp [Pf]
  | k + 1, hk => by
    have ih := Pf_succ_M M k (by omega)
    show Pf (M + 1) k * ((M + 1 - k - 1).factorial : ℝ) * ((M - (k + 1)).factorial : ℝ) =
      Pf M k * ((M - k - 1).factorial : ℝ) * (M.factorial : ℝ)
    rw [show M + 1 - k - 1 = M - k by omega, show M - (k + 1) = M - k - 1 by omega]
    linear_combination ((M - k - 1).factorial : ℝ) * ih

theorem Kq_Pf {N : ℕ} (hN : 0 < N) : ∀ M, N ≤ M → Kq N (M - 1) = Pf M N := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have h1 : Pf (n + 1) (n + 1) = ∏ j ∈ range (n + 1), ((j.factorial : ℕ) : ℝ) := by
      rw [Pf_eq, ← prod_range_reflect]
      refine prod_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      congr 2; omega
    rw [h1, prod_range_succ', Nat.factorial_zero, Nat.cast_one, mul_one, show n + 1 - 1 = n by omega]
    unfold Kq
    refine prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [show i + 1 - (n + 1) = 0 by omega, Nat.factorial_zero, Nat.cast_one, div_one]
  | succ M hNM ih =>
    have hM1 : M - 1 + 1 = M := by omega
    rw [show M + 1 - 1 = M - 1 + 1 by omega, Kq_succ, ih, hM1]
    have h := Pf_succ_M M N hNM
    have hf : (0 : ℝ) < ((M - N).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
    field_simp
    linarith [h]

theorem dL_Qm (N M d : ℕ) (hNM : N ≤ M) (hd : d < M) : dL N M d = min (d + 1) N := by
  unfold dL; split_ifs <;> omega

theorem vdm_len1 {L : ℕ} (h : L = 1) (y : Fin L → ℝ) : vdm y = 1 := by
  subst h
  unfold vdm
  refine prod_eq_one fun i _ => prod_eq_one fun j hj => ?_
  exact absurd (mem_Ioi.1 hj) (by
    intro hlt; rw [Fin.lt_def] at hlt; have := i.isLt; have := j.isLt; omega)

open Classical in
theorem cpl_Q {N M : ℕ} (π : Fin N → ℝ) (x : ℝ) {d : ℕ} (hd : d + 1 < M) (z : Fin (dL N M d) → ℝ)
    (w : Fin (dL N M (d + 1)) → ℝ) : cpl N M π x d z w = if wQ z w then 1 else 0 := by
  have hiff : cIl N M d z w ↔ wQ z w := by unfold cIl wQ; rw [if_pos hd]
  unfold cpl
  rw [if_neg (show d ≠ M - 1 by omega), if_neg (show ¬ M ≤ d + 1 by omega), mul_one, mul_one]
  by_cases h : wQ z w
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/-- Q phase closed form. -/
theorem TQ {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) (π : Fin N → ℝ) (x : ℝ) :
    ∀ d, d < M → ∀ y : Fin (dL N M d) → ℝ, y ∈ Good (dL N M d) →
      bcT (dL N M) (cpl N M π x) d y = ENNReal.ofReal (vdm y * (∏ i, y i) ^ (d + 1 - N) / Kq N d) := by
  intro d
  induction d with
  | zero =>
    intro hM y _
    show (1 : ENNReal) = _
    rw [vdm_len1 (by rw [dL_Qm N M 0 hNM hM]; omega) y, show 0 + 1 - N = 0 by omega, pow_zero]
    simp [Kq]
  | succ d ih =>
    intro hd w hw
    rw [bcT_succ]
    have hd' : d + 1 < M := hd
    have hm := dL_Qm N M d hNM (by omega)
    have hm' := dL_Qm N M (d + 1) hNM hd
    have hF0 : ∀ z : Fin (dL N M d) → ℝ, ¬ wQ z w →
        cpl N M π x d z w * bcT (dL N M) (cpl N M π x) d z = 0 := by
      intro z h; rw [cpl_Q π x hd', if_neg h, zero_mul]
    by_cases hg : d + 1 < N
    · have hF : ∀ z : Fin (dL N M d) → ℝ, z ∈ Good (dL N M d) → wQ z w →
          cpl N M π x d z w * bcT (dL N M) (cpl N M π x) d z = ENNReal.ofReal (vdm z / Kq N d) := by
        intro z hz h
        rw [cpl_Q π x hd', if_pos h, one_mul, ih (by omega) z hz, show d + 1 - N = 0 by omega, pow_zero, mul_one]
      rw [stepQG (by rw [hm, hm']; omega) w hw (Kq N d) (Kq_pos N d) _ hF hF0, Kq_succ,
        show d + 1 + 1 - N = 0 by omega, pow_zero, mul_one, show d + 1 - N = 0 by omega,
        Nat.factorial_zero, Nat.cast_one, div_one, hm, show min (d + 1) N = d + 1 by omega]
    · have hF : ∀ z : Fin (dL N M d) → ℝ, z ∈ Good (dL N M d) → wQ z w →
          cpl N M π x d z w * bcT (dL N M) (cpl N M π x) d z =
            ENNReal.ofReal (vdm z * (∏ i, z i) ^ (d + 1 - N) / Kq N d) := by
        intro z hz h
        rw [cpl_Q π x hd', if_pos h, one_mul, ih (by omega) z hz]
      rw [stepQC (by rw [hm, hm']; omega) w hw (d + 1 - N) (Kq N d) (Kq_pos N d) _ hF hF0, Kq_succ,
        hm, show min (d + 1) N = N by omega, show N + (d + 1 - N) = d + 1 by omega,
        show d + 1 + 1 - N = d + 1 - N + 1 by omega]
      have h1 : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
      have h2 : (0 : ℝ) < ((d + 1 - N).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
      have h3 := Kq_pos N d
      congr 1
      field_simp

/-- top of the Q phase: the level-`N` diagonal carries `Dk`. -/
theorem TQ_top {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) (π : Fin N → ℝ) (x : ℝ)
    (y : Fin (dL N M (M - 1)) → ℝ) (hy : y ∈ Good (dL N M (M - 1))) :
    bcT (dL N M) (cpl N M π x) (M - 1) y = ENNReal.ofReal (vdm y * (∏ i, y i) ^ (M - N) / Pf M N) := by
  rw [TQ hN hNM π x (M - 1) (by omega) y hy, Kq_Pf hN M hNM, show M - 1 + 1 - N = M - N by omega]

end SWL302


set_option autoImplicit false

namespace SWL302

open MeasureTheory Set Finset B8RSK SpikedWishart.Separated.Lib.Weyl

/-- level rates `b_n = π_n` (`1` outside). -/
noncomputable def bpi {N : ℕ} (π : Fin N → ℝ) (j : ℕ) : ℝ := if h : j < N then π ⟨j, h⟩ else 1

theorem gtI_cast (b : ℕ → ℝ) {k k' : ℕ} (h : k = k') (Φ : (Fin k → ℝ) → ENNReal) :
    gtI b k Φ = gtI b k' (fun la => Φ (fun i => la (Fin.cast h i))) := by
  subst h; rfl

theorem vdm_cast {m m' : ℕ} (h : m = m') (z : Fin m' → ℝ) : vdm (fun i : Fin m => z (Fin.cast h i)) = vdm z := by
  subst h; rfl

theorem prod_cast {m m' : ℕ} (h : m = m') (z : Fin m' → ℝ) :
    ∏ i : Fin m, z (Fin.cast h i) = ∏ i, z i := by
  subst h; rfl

theorem stepPT {n m m' : ℕ} (h1 : m = n + 1) (h1' : m' = n) (w : Fin m' → ℝ) (F : (Fin m → ℝ) → ENNReal)
    (bn : ℝ) (C : ENNReal) (hC : C ≠ ⊤) (Ξ : (Fin (n + 1) → ℝ) → ENNReal)
    (hF0 : ∀ z, ¬ wP z w → F z = 0)
    (hF : ∀ z, z ∈ Good m → wP z w → F z =
      C * (ENNReal.ofReal (Real.exp (-bn * (∑ k, z k - ∑ k, w k))) * Ξ (fun i => z (Fin.cast h1.symm i)))) :
    ∫⁻ z, F z = C * ∫⁻ la in Ilace (fun i : Fin n => w (Fin.cast h1'.symm i)),
      ENNReal.ofReal (posI la * Real.exp (-bn * (∑ j, la j - ∑ i, w (Fin.cast h1'.symm i)))) * Ξ la := by
  subst h1 h1'
  rw [stepP w F (fun z => C * (ENNReal.ofReal (Real.exp (-bn * (∑ k, z k - ∑ k, w k))) * Ξ z)) hF hF0,
    ← lintegral_const_mul' _ _ hC]
  refine setLIntegral_congr_fun (measurableSet_Ilace _) fun la _ => ?_
  simp only [posI, Fin.cast_eq_self]
  split_ifs <;> simp

open Classical in
theorem cpl_P {N M : ℕ} (π : Fin N → ℝ) (x : ℝ) {d : ℕ} (hd : ¬ d + 1 < M) (z : Fin (dL N M d) → ℝ)
    (w : Fin (dL N M (d + 1)) → ℝ) : cpl N M π x d z w =
      (if wP z w then 1 else 0) * (if d = M - 1 then (if rdv z 0 ≤ x then 1 else 0) else 1) *
        ENNReal.ofReal ((pnat π (N + M - 2 - d) * M) ^ M *
          Real.exp (-(pnat π (N + M - 2 - d) * M) * (∑ k, z k - ∑ k, w k))) := by
  have hiff : cIl N M d z w ↔ wP z w := by unfold cIl wP; rw [if_neg hd]
  unfold cpl
  rw [if_pos (show M ≤ d + 1 by omega)]
  by_cases h : wP z w
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem pnat_bpi {N M : ℕ} (hM : 0 < M) (π : Fin N → ℝ) (n : ℕ) (hn : n < N) :
    pnat (fun i => π i / M) n * M = bpi π n := by
  have hMr : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  simp only [pnat, bpi, dif_pos hn]
  field_simp

open Classical in
/-- P phase induction. -/
theorem PI {N M : ℕ} [NeZero N] (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i) (x : ℝ) :
    ∀ j, j ≤ N → ∃ Ξ : (Fin (N - j) → ℝ) → ENNReal,
      gtI (bpi π) N (fun la => ENNReal.ofReal (Dk M N la) * (if la 0 ≤ x then 1 else 0)) = gtI (bpi π) (N - j) Ξ ∧
      ∀ (h : dL N M (M - 1 + j) = N - j) (z : Fin (dL N M (M - 1 + j)) → ℝ), z ∈ Good (dL N M (M - 1 + j)) →
        (if j = 0 then (if rdv z 0 ≤ x then 1 else 0) else 1) *
            bcT (dL N M) (cpl N M (fun i => π i / M) x) (M - 1 + j) z =
          (∏ t ∈ range j, ENNReal.ofReal (bpi π (N - 1 - t) ^ M)) * Ξ (fun i => z (Fin.cast h.symm i)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun la => ENNReal.ofReal (Dk M N la) * (if la 0 ≤ x then 1 else 0), rfl, fun h z hz => ?_⟩
    rw [if_pos rfl, prod_range_zero, one_mul]
    show (if rdv z 0 ≤ x then 1 else 0) * bcT (dL N M) (cpl N M (fun i => π i / M) x) (M - 1) z = _
    rw [TQ_top hN hNM _ x z hz]
    have e1 : vdm z = vdm (fun i => z (Fin.cast h.symm i)) := (vdm_cast _ z).symm
    have e2 : (∏ i : Fin (dL N M (M - 1)), z i) = ∏ i, z (Fin.cast h.symm i) := (prod_cast _ z).symm
    have e3 : rdv z 0 = z (Fin.cast h.symm 0) := rdv_eq z (Fin.cast h.symm 0) 0 (by simp)
    rw [e1, e2, e3]
    exact mul_comm _ _
  | succ j ih =>
    intro hj
    obtain ⟨Ξ, hgt, hrel⟩ := ih (by omega)
    have h0 : N - j = N - (j + 1) + 1 := by omega
    refine ⟨fun μ => ∫⁻ la in Ilace μ, ENNReal.ofReal (posI la * Real.exp (-(bpi π (N - (j + 1))) *
        (∑ k, la k - ∑ i, μ i))) * Ξ (fun i => la (Fin.cast h0 i)), ?_, fun h z hz => ?_⟩
    · rw [hgt, gtI_cast (bpi π) h0 Ξ, gtI_succ]
    · have hd : ¬ M - 1 + j + 1 < M := by omega
      have hj0 : j + 1 ≠ 0 := by omega
      have hlev : dL N M (M - 1 + j) = N - (j + 1) + 1 := by
        rw [show M - 1 + j = N + M - 2 - (N - 1 - j) by omega, dL_level N M (N - 1 - j) hNM (by omega)]; omega
      have hlev' : dL N M (M - 1 + j) = N - j := by rw [hlev]; omega
      have hbeta : 0 < bpi π (N - (j + 1)) := by
        simp only [bpi, dif_pos (show N - (j + 1) < N by omega)]; exact hπ _
      rw [if_neg hj0, one_mul]
      show ∫⁻ y : Fin (dL N M (M - 1 + j)) → ℝ, cpl N M (fun i => π i / M) x (M - 1 + j) y z *
          bcT (dL N M) (cpl N M (fun i => π i / M) x) (M - 1 + j) y = _
      have hC : (∏ t ∈ range j, ENNReal.ofReal (bpi π (N - 1 - t) ^ M)) *
          ENNReal.ofReal (bpi π (N - (j + 1)) ^ M) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
      rw [stepPT (n := N - (j + 1)) hlev h z _ (bpi π (N - (j + 1))) _ hC (fun la => Ξ (fun i => la (Fin.cast h0 i)))]
      · rw [prod_range_succ, show N - 1 - j = N - (j + 1) by omega]
      · intro y hy
        rw [cpl_P _ x hd, if_neg hy]; simp
      · intro y hyg hy
        have hr := hrel hlev' y hyg
        have hcor : (if M - 1 + j = M - 1 then (if rdv y 0 ≤ x then (1 : ENNReal) else 0) else 1) =
            (if j = 0 then (if rdv y 0 ≤ x then 1 else 0) else 1) := by
          split_ifs <;> first | rfl | (exfalso; omega)
        rw [cpl_P _ x hd, if_pos hy, one_mul, hcor,
          show N + M - 2 - (M - 1 + j) = N - (j + 1) by omega, pnat_bpi hM π _ (by omega),
          ENNReal.ofReal_mul (pow_nonneg hbeta.le _),
          show ∀ (A B E T : ENNReal), A * (B * E) * T = B * E * (A * T) from fun A B E T => by ring, hr]
        rw [show ∀ (B E C X : ENNReal), B * E * (C * X) = C * B * (E * X) from fun B E C X => by ring]
        rfl

/-- the block chain at the top equals `(∏ π^M) * gtI`. -/
theorem D3 {N M : ℕ} [NeZero N] (hM : 0 < M) (hNM : N ≤ M) (π : Fin N → ℝ) (hπ : ∀ i, 0 < π i) (x : ℝ) :
    ∀ d, d = M - 1 + N → ∀ w : Fin (dL N M d) → ℝ,
      bcT (dL N M) (cpl N M (fun i => π i / M) x) d w = (∏ i, ENNReal.ofReal (π i ^ M)) *
        gtI (bpi π) N (fun la => ENNReal.ofReal (Dk M N la) * (if la 0 ≤ x then 1 else 0)) := by
  intro d hd w
  subst hd
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨Ξ, hgt, hrel⟩ := PI hM hNM π hπ x N le_rfl
  have hdl : dL N M (M - 1 + N) = N - N := by
    rw [show M - 1 + N = N + M - 1 by omega, dL_top]; omega
  have hgood : w ∈ Good (dL N M (M - 1 + N)) := by
    refine ⟨fun a b _ => ?_, fun a => ?_⟩
    · exfalso; have := a.isLt; omega
    · exfalso; have := a.isLt; omega
  have hr := hrel hdl w hgood
  rw [if_neg (by omega), one_mul] at hr
  rw [hr, hgt, gtI_cast (bpi π) (show N - N = 0 by omega) Ξ]
  congr 1
  · rw [prod_range_reflect (fun t => ENNReal.ofReal (bpi π t ^ M)) N,
      ← Fin.prod_univ_eq_prod_range (fun t => ENNReal.ofReal (bpi π t ^ M)) N]
    refine prod_congr rfl fun i _ => ?_
    simp [bpi]
  · show Ξ _ = Ξ _
    congr 1
    funext i
    exfalso; have := i.isLt; omega

end SWL302


set_option autoImplicit false

namespace SWL302

theorem hab_bpi {N : ℕ} (π : Fin N → ℝ) : ∀ n, aπ π n = bpi π n - 1 := by
  intro n; unfold aπ bpi; split_ifs <;> ring

end SWL302

open SpikedWishart.LastPassage MeasureTheory ProbabilityTheory in
theorem solution {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ≤ M) (π : Fin N → ℝ)
    (hπ : ∀ i, 0 < π i) (U : Matrix.unitaryGroup (Fin N) ℂ) (x : ℝ) :
    (expLaw π M).real {X | L X ≤ x} =
      (sampleLaw M N).real {G | SpikedWishart.SoftEdge.largestEig M U (fun i => (π i)⁻¹) G ≤ x} := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 := B8RSK.expLaw_L_le (N := N) (M := M) π hπ x
  have h2 := SWL302.rpp_scale (N := N) hM π x
  have h3 := SWL302.gR_lintegral_bcT hN hM hNM (fun i => π i / M) (M * x)
  have h4 := SWL302.D3 hM hNM π hπ (M * x) (N + M - 1) (by omega)
    ((0 : Fin N × Fin M → ℝ) ∘ SWL302.dE N M hN hM (N + M - 1))
  have h5 := SWL302.c2c hNM π hπ U x
  have h6 := SWL302.chain_tele M (SWL302.aπ π) (SWL302.bpi π) (SWL302.hab_bpi π) N
    (fun la => if la 0 ≤ (M : ℝ) * x then 1 else 0)
  rw [measureReal_def, measureReal_def, h1, h2, h3, h4,
    show sampleLaw M N = SpikedWishart.FixedDim.sampleLaw M N from rfl, h5, h6]
