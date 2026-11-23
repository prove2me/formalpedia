-- Prove2me | solution 1 for ReusableMatching.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T20:45:44.385979+00:00
-- url     : https://prove2.me/submissions/a040ba52-c217-4ee9-9c35-152919770da0

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_criticalThreshold
import Definitions.Def_ReusableMatching_window
import Definitions.Def_ReusableMatching_G__bf4f7e
import Theorems.Thm_ReusableMatching_lemma_4
import Theorems.Thm_ReusableMatching_lemma_5
import Theorems.Thm_ReusableMatching_lemma_7

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RM9

open ReusableMatching MeasureTheory

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

/-! ### `g` and prices -/

lemma g_pos (β x : ℝ) : 0 < g β x := Real.exp_pos _

lemma g_le_one {β x : ℝ} (hβ : 0 ≤ β) (hx : x ≤ 1) : g β x ≤ 1 := by
  unfold g; rw [Real.exp_le_one_iff]; nlinarith

lemma g_one (β : ℝ) : g β 1 = 1 := by simp [g]

lemma g_mono {β x y : ℝ} (hβ : 0 ≤ β) (h : x ≤ y) : g β x ≤ g β y :=
  Real.exp_le_exp.2 (by nlinarith)

lemma price_nonneg (I : OBMRRInstance V n) {β : ℝ} (hβ : 0 ≤ β) (Y : Seeds V n) (v : V)
    (t : Fin n) : 0 ≤ reducedPrice I β Y v t :=
  mul_nonneg (I.r_nonneg v) (sub_nonneg.2 (g_le_one hβ (Y _).2.2))

lemma price_le (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (v : V) (t : Fin n) :
    reducedPrice I β Y v t ≤ I.r v := by
  unfold reducedPrice; nlinarith [g_pos β (Y (v, period I t) : ℝ), I.r_nonneg v]

/-! ### `leastArgmax` -/

lemma lam_none {C : Finset V} {f : V → ℝ} : leastArgmax C f = none ↔ ¬ C.Nonempty := by
  unfold leastArgmax; split_ifs with h <;> simp_all

lemma lam_some {C : Finset V} {f : V → ℝ} {v : V} (h : leastArgmax C f = some v) :
    v ∈ C ∧ (∀ w ∈ C, f w ≤ f v) ∧ (∀ w ∈ C, f w = f v → v ≤ w) := by
  unfold leastArgmax at h
  split_ifs at h with hC
  simp only [Option.some.injEq] at h
  subst h
  generalize_proofs hne
  have hm := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hm
  refine ⟨hm.1, fun w hw => (Finset.le_sup' f hw).trans_eq hm.2.symm, fun w hw hfw => ?_⟩
  exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hw, hfw.trans hm.2⟩)

lemma lam_eq_some {C : Finset V} {f : V → ℝ} {v : V} (hv : v ∈ C)
    (hmax : ∀ w ∈ C, f w ≤ f v) (hmin : ∀ w ∈ C, f w = f v → v ≤ w) :
    leastArgmax C f = some v := by
  cases h : leastArgmax C f with
  | none => exact absurd ⟨v, hv⟩ (lam_none.1 h)
  | some u =>
    obtain ⟨hu, hum, humin⟩ := lam_some h
    have : f u = f v := le_antisymm (hmax u hu) (hum v hv)
    rw [le_antisymm (humin v hv this.symm) (hmin u hu this)]

lemma lam_congr {C : Finset V} {fa fb : V → ℝ} (h : ∀ w ∈ C, fa w = fb w) :
    leastArgmax C fa = leastArgmax C fb := by
  cases hb : leastArgmax C fb with
  | none => exact lam_none.2 (lam_none.1 hb)
  | some v =>
    obtain ⟨hv, hmax, hmin⟩ := lam_some hb
    refine lam_eq_some hv (fun w hw => ?_) (fun w hw hw' => ?_)
    · rw [h w hw, h v hv]; exact hmax w hw
    · rw [h w hw, h v hv] at hw'; exact hmin w hw hw'

lemma lam_lower {C : Finset V} {fa fb : V → ℝ} {i : V}
    (hne : ∀ v, leastArgmax C fb = some v → v ≠ i)
    (hoff : ∀ w, w ≠ i → fa w = fb w) (hi : fa i ≤ fb i) :
    leastArgmax C fa = leastArgmax C fb := by
  cases hb : leastArgmax C fb with
  | none => exact lam_none.2 (lam_none.1 hb)
  | some v =>
    have hvi := hne v hb
    obtain ⟨hv, hmax, hmin⟩ := lam_some hb
    have hle : ∀ w, fa w ≤ fb w := fun w => by
      by_cases hw : w = i
      · subst hw; exact hi
      · exact (hoff w hw).le
    refine lam_eq_some hv (fun w hw => ?_) (fun w hw hw' => ?_)
    · rw [hoff v hvi]; exact (hle w).trans (hmax w hw)
    · rw [hoff v hvi] at hw'
      apply hmin w hw
      exact le_antisymm (hmax w hw) (hw' ▸ hle w)

/-! ### The run -/

lemma assign_ge (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) :
    ∀ t s, t ≤ s → assignment I β Y t s = none := by
  intro t
  induction t with
  | zero => intro s _; rfl
  | succ t ih =>
    intro s hs
    simp only [assignment]
    rw [Function.update_of_ne (by omega)]
    exact ih s (by omega)

lemma assign_stable (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) :
    ∀ t s, s < t → assignment I β Y t s = assignment I β Y (s + 1) s := by
  intro t
  induction t with
  | zero => intro s hs; omega
  | succ t ih =>
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with h | h
    · simp only [assignment]
      rw [Function.update_of_ne (by omega)]
      exact ih s h
    · subst h; rfl

lemma assign_self (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) :
    assignment I β Y (t + 1) t = chooseResource I β Y (assignment I β Y t) t := by
  simp [assignment, t.2]

lemma PR_eq (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) :
    PeriodicReranking I β Y t = chooseResource I β Y (assignment I β Y t) t := by
  unfold PeriodicReranking
  rw [assign_stable I β Y n t t.2, assign_self]

lemma assign_eq_PR (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : ℕ) (u : Fin n)
    (hu : (u : ℕ) < t) (ht : t ≤ n) :
    assignment I β Y t u = PeriodicReranking I β Y u := by
  unfold PeriodicReranking
  rw [assign_stable I β Y t u hu, assign_stable I β Y n u u.2]

lemma isAvail_iff (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (v : V) (t : Fin n) :
    IsAvailable I (assignment I β Y t) v t ↔
      ∀ u : Fin n, u < t → PeriodicReranking I β Y u = some v → (u : ℕ) + I.d ≤ t := by
  constructor
  · intro h u hu hPR
    exact h u hu (by rw [assign_eq_PR I β Y t u hu t.2.le]; exact hPR)
  · intro h s hs hs'
    have hsn : s < n := by omega
    have := assign_eq_PR I β Y t ⟨s, hsn⟩ hs t.2.le
    simp only at this
    exact h ⟨s, hsn⟩ hs (this ▸ hs')

lemma PR_spec (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n) {v : V}
    (h : PeriodicReranking I β Y t = some v) :
    (v, t) ∈ I.E ∧ IsAvailable I (assignment I β Y t) v t ∧
      ∀ w, (w, t) ∈ I.E → IsAvailable I (assignment I β Y t) w t →
        reducedPrice I β Y w t ≤ reducedPrice I β Y v t ∧
        (reducedPrice I β Y w t = reducedPrice I β Y v t → v ≤ w) := by
  rw [PR_eq] at h
  unfold chooseResource at h
  obtain ⟨hv, hmax, hmin⟩ := lam_some h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hmax hmin
  exact ⟨hv.1, hv.2, fun w hw hwa => ⟨hmax w ⟨hw, hwa⟩, hmin w ⟨hw, hwa⟩⟩⟩

lemma PR_none (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : Fin n)
    (h : PeriodicReranking I β Y t = none) :
    ∀ w, (w, t) ∈ I.E → ¬ IsAvailable I (assignment I β Y t) w t := by
  rw [PR_eq] at h
  unfold chooseResource at h
  have := lam_none.1 h
  intro w hw hwa
  exact this ⟨w, by simp [hw, hwa]⟩

/-- Agreement of two runs up to time `T`. -/
lemma agree (I : OBMRRInstance V n) (β : ℝ) (Ya Yb : Seeds V n) (T : ℕ)
    (h : ∀ t : Fin n, (t : ℕ) < T → assignment I β Ya t = assignment I β Yb t →
      chooseResource I β Ya (assignment I β Ya t) t =
        chooseResource I β Yb (assignment I β Ya t) t) :
    assignment I β Ya T = assignment I β Yb T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have ih' := ih (fun t ht => h t (by omega))
    simp only [assignment]
    rw [ih']
    congr 1
    split_ifs with hT
    · have := h ⟨T, hT⟩ (by simp) ih'
      rw [ih'] at this
      exact this
    · rfl

lemma step_congr (I : OBMRRInstance V n) (β : ℝ) (Ya Yb : Seeds V n) (a : ℕ → Option V)
    (t : Fin n) (h : ∀ w, reducedPrice I β Ya w t = reducedPrice I β Yb w t) :
    chooseResource I β Ya a t = chooseResource I β Yb a t := by
  unfold chooseResource
  exact lam_congr (fun w _ => h w)

lemma step_lower (I : OBMRRInstance V n) (β : ℝ) (Ya Yb : Seeds V n) (a : ℕ → Option V)
    (t : Fin n) (i : V) (hne : ∀ v, chooseResource I β Yb a t = some v → v ≠ i)
    (hoff : ∀ w, w ≠ i → reducedPrice I β Ya w t = reducedPrice I β Yb w t)
    (hi : reducedPrice I β Ya i t ≤ reducedPrice I β Yb i t) :
    chooseResource I β Ya a t = chooseResource I β Yb a t := by
  unfold chooseResource at hne ⊢
  exact lam_lower hne hoff hi

/-! ### `twoSeed` -/

lemma period_ne_prev (I : OBMRRInstance V n) (j : Fin n) : period I j ≠ prevPeriod I j := by
  intro h
  have := congrArg Fin.val h
  simp [period, prevPeriod] at this

lemma ts_ne (I : OBMRRInstance V n) (Y : Seeds V n) (i : V) (j : Fin n) (y1 y2 : unitInterval)
    {v : V} (hv : v ≠ i) (k : Fin (n + 1)) : twoSeed I Y i j y1 y2 (v, k) = Y (v, k) := by
  simp [twoSeed, Function.update_apply, hv]

lemma ts_pp (I : OBMRRInstance V n) (Y : Seeds V n) (i : V) (j : Fin n) (y1 y2 : unitInterval) :
    twoSeed I Y i j y1 y2 (i, prevPeriod I j) = y1 := by
  simp [twoSeed, Function.update_apply, (period_ne_prev I j).symm]

lemma ts_p (I : OBMRRInstance V n) (Y : Seeds V n) (i : V) (j : Fin n) (y1 y2 : unitInterval) :
    twoSeed I Y i j y1 y2 (i, period I j) = y2 := by
  simp [twoSeed, Function.update_apply]

lemma ts_other (I : OBMRRInstance V n) (Y : Seeds V n) (i : V) (j : Fin n)
    (y1 y2 : unitInterval) (k : Fin (n + 1)) (h1 : k ≠ prevPeriod I j) (h2 : k ≠ period I j) :
    twoSeed I Y i j y1 y2 (i, k) = Y (i, k) := by
  simp [twoSeed, Function.update_apply, h1, h2]

lemma price_ts_ne (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (y1 y2 y1' y2' : unitInterval) {v : V} (hv : v ≠ i) (t : Fin n) :
    reducedPrice I β (twoSeed I Y i j y1 y2) v t = reducedPrice I β (twoSeed I Y i j y1' y2') v t := by
  simp [reducedPrice, ts_ne I Y i j _ _ hv]

/-! ### Periods -/

lemma per_prev (I : OBMRRInstance V n) (j t : Fin n) (h1 : (j : ℕ) < t + I.d)
    (h2 : (t : ℕ) < (j : ℕ) / I.d * I.d) : period I t = prevPeriod I j := by
  have hd := I.one_le_d
  apply Fin.ext
  simp only [period, prevPeriod]
  have hq : (t : ℕ) / I.d < (j : ℕ) / I.d := (Nat.div_lt_iff_lt_mul (by omega)).2 h2
  have hj : (j : ℕ) / I.d * I.d ≤ j := Nat.div_mul_le_self _ _
  have hq1 : 1 ≤ (j : ℕ) / I.d := Nat.lt_of_le_of_lt (Nat.zero_le _) hq
  have hsub : ((j : ℕ) / I.d - 1) * I.d + I.d = (j : ℕ) / I.d * I.d := by
    rw [Nat.sub_one_mul]; have : I.d ≤ (j : ℕ) / I.d * I.d := Nat.le_mul_of_pos_left _ hq1; omega
  have : (j : ℕ) / I.d - 1 ≤ (t : ℕ) / I.d := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  omega

lemma per_cur (I : OBMRRInstance V n) (j t : Fin n) (h1 : (j : ℕ) / I.d * I.d ≤ (t : ℕ))
    (h2 : t ≤ j) : period I t = period I j := by
  have hd := I.one_le_d
  apply Fin.ext
  simp only [period]
  have hj : (j : ℕ) < (j : ℕ) / I.d * I.d + I.d := Nat.lt_div_mul_add (by omega)
  have : (t : ℕ) / I.d = (j : ℕ) / I.d :=
    Nat.div_eq_of_lt_le h1 (by rw [Nat.succ_mul]; have := Fin.le_def.1 h2; omega)
  omega

lemma per_lt (I : OBMRRInstance V n) (j t : Fin n) (h : (t : ℕ) < (j : ℕ) / I.d * I.d) :
    period I t ≠ period I j := by
  have hd := I.one_le_d
  intro he
  have := congrArg Fin.val he
  simp only [period] at this
  have hq : (t : ℕ) / I.d < (j : ℕ) / I.d := (Nat.div_lt_iff_lt_mul (by omega)).2 h
  omega

lemma same_period_close (I : OBMRRInstance V n) (t s : Fin n) (h : period I t = period I s) :
    (s : ℕ) < t + I.d := by
  have hd := I.one_le_d
  have := congrArg Fin.val h
  simp only [period] at this
  have h1 : (s : ℕ) < s / I.d * I.d + I.d := Nat.lt_div_mul_add (by omega)
  have h2 : (t : ℕ) / I.d * I.d ≤ t := Nat.div_mul_le_self _ _
  have h3 : (t : ℕ) / I.d = s / I.d := by omega
  rw [h3] at h2; omega

lemma price_period (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (v : V) (t t' : Fin n)
    (h : period I t = period I t') : reducedPrice I β Y v t = reducedPrice I β Y v t' := by
  simp [reducedPrice, h]

lemma dualBeta_nonneg (I : OBMRRInstance V n) {β : ℝ} (hβ : 0 ≤ β) (Y : Seeds V n) (j : Fin n) :
    0 ≤ dualBeta I β Y j := by
  unfold dualBeta
  cases PeriodicReranking I β Y j with
  | none => simp
  | some v => exact price_nonneg I hβ Y v j

lemma dualAlpha_nonneg (I : OBMRRInstance V n) {β : ℝ} (Y : Seeds V n) (i : V) (t : Fin n) :
    0 ≤ dualAlpha I β Y i t := by
  unfold dualAlpha
  split_ifs
  · exact mul_nonneg (I.r_nonneg i) (g_pos _ _).le
  · rfl

lemma price_i_one (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (y1 : unitInterval) (t : Fin n) (h : period I t = period I j) :
    reducedPrice I β (twoSeed I Y i j y1 1) i t = 0 := by
  simp [reducedPrice, h, ts_p, g_one]

lemma price_i_one' (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (y2 : unitInterval) (t : Fin n) (h : period I t = prevPeriod I j) :
    reducedPrice I β (twoSeed I Y i j 1 y2) i t = 0 := by
  simp [reducedPrice, h, ts_pp, g_one]

/-! ### Lemma 8(a)-type: top regime -/

lemma top_eq (I : OBMRRInstance V n) {β : ℝ} (hβ : 0 < β) (i : V) (j : Fin n) (Y : Seeds V n)
    (y1 : unitInterval) (hnm : ¬ MatchedInPrevPeriod I β (twoSeed I Y i j y1 1) i j) :
    criticalThreshold I β Y i j y1 j = criticalThreshold I β Y i j 1 j := by
  have hag : assignment I β (twoSeed I Y i j y1 1) j = assignment I β (twoSeed I Y i j 1 1) j := by
    apply agree
    intro t ht hh
    by_cases hp : period I t = prevPeriod I j
    · symm
      apply step_lower I β _ _ _ t i
      · intro v hv hvi
        subst hvi
        rw [← PR_eq] at hv
        exact hnm ⟨t, hp, hv⟩
      · intro w hw; exact price_ts_ne I β Y i j _ _ _ _ hw t
      · rw [price_i_one' I β Y i j 1 t hp]; exact price_nonneg I hβ.le _ _ _
    · apply step_congr
      intro w
      by_cases hw : w = i
      · subst hw
        by_cases hpj : period I t = period I j
        · simp [reducedPrice, hpj, ts_p]
        · simp [reducedPrice, ts_other I Y w j _ _ _ hp hpj]
      · exact price_ts_ne I β Y i j _ _ _ _ hw t
  have hpr : ∀ v, reducedPrice I β (twoSeed I Y i j y1 1) v j =
      reducedPrice I β (twoSeed I Y i j 1 1) v j := by
    intro v
    by_cases hv : v = i
    · subst hv; simp [reducedPrice, ts_p]
    · exact price_ts_ne I β Y i j _ _ _ _ hv j
  have hav : availableSet I β (twoSeed I Y i j y1 1) j = availableSet I β (twoSeed I Y i j 1 1) j := by
    ext v; simp only [availableSet, Finset.mem_filter, Finset.mem_univ, true_and, hag]
  unfold criticalThreshold
  simp only [hpr]
  rw [hav]

/-! ### The critical threshold is at most the competing price -/

lemma ct_le {β r M : ℝ} (hβ : 0 < β) (hr : 0 ≤ r) (hM : 0 ≤ M) :
    r * (1 - g β (sSup {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ r * (1 - g β y)})) ≤ M := by
  set S := {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ r * (1 - g β y)}
  by_cases hS : S.Nonempty
  · have hbdd : BddAbove S := ⟨1, fun y hy => hy.1.2⟩
    have hx1 : sSup S ≤ 1 := csSup_le hS (fun y hy => hy.1.2)
    by_contra hlt
    push Not at hlt
    rcases hx1.lt_or_eq with hx1 | hx1
    · have hcont : Continuous (fun y => r * (1 - g β y)) := by unfold g; fun_prop
      have hev : ∀ᶠ y in nhds (sSup S), M < r * (1 - g β y) ∧ y < 1 :=
        ((hcont.tendsto _).eventually (lt_mem_nhds hlt)).and (Iio_mem_nhds hx1)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
      have hy := hball (y := sSup S + ε / 2) (by
        rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
      obtain ⟨y0, hy0⟩ := hS
      have hx0 : 0 ≤ sSup S := le_trans hy0.1.1 (le_csSup hbdd hy0)
      have hmem : sSup S + ε / 2 ∈ S := ⟨⟨by linarith, hy.2.le⟩, hy.1.le⟩
      have := le_csSup hbdd hmem
      linarith
    · rw [hx1, g_one] at hlt; simp at hlt; linarith
  · rw [Set.not_nonempty_iff_eq_empty.1 hS, Real.sSup_empty]
    have h0 : (0 : ℝ) ∉ S := fun h => hS ⟨0, h⟩
    simp only [S, Set.mem_setOf_eq, Set.mem_Icc, le_refl, zero_le_one, and_self, true_and,
      not_le] at h0
    exact h0.le

lemma ct_mem (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (y1 : unitInterval) (t : Fin n) :
    0 ≤ criticalThreshold I β Y i j y1 t ∧ criticalThreshold I β Y i j y1 t ≤ 1 := by
  unfold criticalThreshold
  simp only
  constructor
  · exact Real.sSup_nonneg (fun y hy => hy.1.1)
  · exact Real.sSup_le (fun y hy => hy.1.2) zero_le_one


/-! ### Integral lemmas -/

lemma hasDerivAt_G {β : ℝ} (hβ : 0 < β) (x : ℝ) : HasDerivAt (G β) (g β x) x := by
  unfold G g
  have h := ((hasDerivAt_id x).sub_const 1).const_mul β |>.exp
  have := h.div_const β
  refine (this.congr_deriv ?_)
  field_simp; rfl

lemma key_int (F : unitInterval → ℝ) (hF : Integrable F) {β r Z1 Z2 cb m tp : ℝ} (hβ : 0 < β)
    (h0 : 0 ≤ Z1) (h12 : Z1 ≤ Z2) (h2 : Z2 ≤ 1)
    (hb : ∀ y : unitInterval, (y : ℝ) < Z1 → cb ≤ F y)
    (hm : ∀ y : unitInterval, Z1 < y → (y : ℝ) < Z2 → r * g β y + m ≤ F y)
    (ht : ∀ y : unitInterval, Z2 < (y : ℝ) → tp ≤ F y) :
    cb * Z1 + r * (G β Z2 - G β Z1) + m * (Z2 - Z1) + tp * (1 - Z2) ≤ ∫ y, F y := by
  set F' : ℝ → ℝ := Set.IccExtend (zero_le_one' ℝ) F with hF'
  have hFF : ∀ y : unitInterval, F' y = F y := fun y => Set.IccExtend_val _ _ y
  have hcomp : F' ∘ Subtype.val = F := funext hFF
  have hint : ∫ y, F y = ∫ x in (0:ℝ)..1, F' x := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      ← integral_subtype_comap measurableSet_Icc]
    simp only [hFF]; rfl
  have hI : IntegrableOn F' (Set.Icc 0 1) := by
    rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc, hcomp]; exact hF
  have hII : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable F' volume a b := fun a b ha hab hb =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 (hI.mono_set (Set.Icc_subset_Icc ha hb))
  have hgc : Continuous (g β) := by unfold g; fun_prop
  rw [hint, ← intervalIntegral.integral_add_adjacent_intervals (hII 0 Z1 le_rfl h0 (h12.trans h2))
    (hII Z1 1 h0 (h12.trans h2) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hII Z1 Z2 h0 h12 h2) (hII Z2 1 (h0.trans h12) h2 le_rfl)]
  have e1 : ∫ x in (0:ℝ)..Z1, cb = cb * Z1 := by simp; ring
  have e2 : ∫ x in Z1..Z2, (r * g β x + m) = r * (G β Z2 - G β Z1) + m * (Z2 - Z1) := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by simp),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_G hβ x)
        (hgc.intervalIntegrable _ _)]
    simp; ring
  have e3 : ∫ x in Z2..(1:ℝ), tp = tp * (1 - Z2) := by simp; ring
  have i1 : ∫ x in (0:ℝ)..Z1, cb ≤ ∫ x in (0:ℝ)..Z1, F' x :=
    intervalIntegral.integral_mono_on_of_le_Ioo h0 (by simp) (hII 0 Z1 le_rfl h0 (h12.trans h2))
      (fun x hx => by
        have hx1 : x ∈ unitInterval := ⟨hx.1.le, (hx.2.trans_le (h12.trans h2)).le⟩
        have := hFF ⟨x, hx1⟩; simp only at this; rw [this]; exact hb _ hx.2)
  have i2 : ∫ x in Z1..Z2, (r * g β x + m) ≤ ∫ x in Z1..Z2, F' x :=
    intervalIntegral.integral_mono_on_of_le_Ioo h12 (by apply Continuous.intervalIntegrable; fun_prop)
      (hII Z1 Z2 h0 h12 h2)
      (fun x hx => by
        have hx1 : x ∈ unitInterval := ⟨h0.trans hx.1.le, (hx.2.trans_le h2).le⟩
        have := hFF ⟨x, hx1⟩; simp only at this; rw [this]; exact hm ⟨x, hx1⟩ hx.1 hx.2)
  have i3 : ∫ x in Z2..(1:ℝ), tp ≤ ∫ x in Z2..(1:ℝ), F' x :=
    intervalIntegral.integral_mono_on_of_le_Ioo h2 (by simp) (hII Z2 1 (h0.trans h12) h2 le_rfl)
      (fun x hx => by
        have hx1 : x ∈ unitInterval := ⟨(h0.trans h12).trans hx.1.le, hx.2.le⟩
        have := hFF ⟨x, hx1⟩; simp only at this; rw [this]; exact ht _ hx.1)
  linarith

lemma convex_bound {β z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (1 - g β 0) * (1 - z) ≤ G β 1 - G β z := by
  unfold G g
  set u := 1 - z with hu
  have hu0 : 0 ≤ u := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-β)) (sub_nonneg.2 hu1) hu0
    (by ring : (1 - u) + u = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  have e1 : β * (0 - 1) = -β := by ring
  have e2 : β * (z - 1) = u * -β := by rw [hu]; ring
  have e3 : β * (1 - 1) = 0 := by ring
  rw [e1, e2, e3, Real.exp_zero]
  have hA : 0 ≤ 1 - Real.exp (u * -β) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
  have h1 : (1 - Real.exp (-β)) * u ≤ 1 - Real.exp (u * -β) := by nlinarith
  have h2 : 1 - Real.exp (u * -β) ≤ (1 - Real.exp (u * -β)) / β := le_div_self hA hβ hβ1
  have h3 : (1 - Real.exp (u * -β)) / β = 1 / β - Real.exp (u * -β) / β := by ring
  linarith

/-! ### Measurability -/

lemma meas_price (I : OBMRRInstance V n) (β : ℝ) (v : V) (t : Fin n) :
    Measurable (fun Y : Seeds V n => reducedPrice I β Y v t) := by
  have h : Measurable (fun Y : Seeds V n => ((Y (v, period I t) : unitInterval) : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply _)
  unfold reducedPrice g
  exact measurable_const.mul (measurable_const.sub
    (Real.measurable_exp.comp (measurable_const.mul (h.sub_const 1))))

lemma choose_iff (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (a : ℕ → Option V) (t : Fin n)
    (o : Option V) :
    chooseResource I β Y a t = o ↔ ∃ C : Finset V,
      (∀ v, v ∈ C ↔ ((v, t) ∈ I.E ∧ IsAvailable I a v t)) ∧
      leastArgmax C (fun v => reducedPrice I β Y v t) = o := by
  classical
  constructor
  · intro h
    refine ⟨Finset.univ.filter (fun v => (v, t) ∈ I.E ∧ IsAvailable I a v t), fun v => by simp, ?_⟩
    rw [← h]; unfold chooseResource; congr 1
  · rintro ⟨C, hC, h⟩
    rw [← h]; unfold chooseResource; congr 1; ext v; simp [hC]

lemma meas_lam (C : Finset V) (f : V → Seeds V n → ℝ) (hf : ∀ v, Measurable (f v))
    (o : Option V) : Measurable (fun Y => leastArgmax C (fun v => f v Y) = o) := by
  classical
  cases o with
  | none => simp only [lam_none]; exact measurable_const
  | some v =>
    have : (fun Y => leastArgmax C (fun w => f w Y) = some v) = fun Y => v ∈ C ∧
        (∀ w, w ∈ C → f w Y ≤ f v Y) ∧ (∀ w, w ∈ C → f w Y = f v Y → v ≤ w) := by
      funext Y; apply propext; exact ⟨lam_some, fun ⟨a, b, c⟩ => lam_eq_some a b c⟩
    rw [this]
    refine measurable_const.and ((Measurable.forall fun w => measurable_const.imp ?_).and
      (Measurable.forall fun w => measurable_const.imp ((?_ : Measurable _).imp measurable_const)))
    · exact measurableSet_setOfPred.1 (measurableSet_le (hf w) (hf v))
    · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (hf w) (hf v))

lemma meas_assign (I : OBMRRInstance V n) (β : ℝ) :
    ∀ t s (o : Option V), Measurable (fun Y : Seeds V n => assignment I β Y t s = o) := by
  intro t
  induction t with
  | zero => intro s o; simp only [assignment]; exact measurable_const
  | succ t ih =>
    intro s o
    simp only [assignment, Function.update_apply]
    by_cases hs : s = t
    · simp only [hs, if_true]
      by_cases h : t < n
      · simp only [dif_pos h]
        have : (fun Y => chooseResource I β Y (assignment I β Y t) ⟨t, h⟩ = o) = fun Y =>
            ∃ C : Finset V, (∀ v, v ∈ C ↔ ((v, (⟨t, h⟩ : Fin n)) ∈ I.E ∧
              IsAvailable I (assignment I β Y t) v t)) ∧
              leastArgmax C (fun v => reducedPrice I β Y v ⟨t, h⟩) = o := by
          funext Y; exact propext (choose_iff ..)
        rw [this]
        refine Measurable.exists fun C => (Measurable.forall fun v =>
          measurable_const.iff (measurable_const.and ?_)).and
          (meas_lam C _ (fun v => meas_price I β v _) o)
        unfold IsAvailable
        exact Measurable.forall fun u => measurable_const.imp ((ih u (some v)).imp measurable_const)
      · simp only [dif_neg h]; exact measurable_const
    · simp only [hs, if_false]; exact ih s o

lemma meas_dualBeta (I : OBMRRInstance V n) (β : ℝ) (j : Fin n) :
    Measurable (fun Y : Seeds V n => dualBeta I β Y j) := by
  have : (fun Y => dualBeta I β Y j) = fun Y => ∑ v, if PeriodicReranking I β Y j = some v then
      reducedPrice I β Y v j else 0 := by
    funext Y; unfold dualBeta
    cases PeriodicReranking I β Y j with
    | none => simp
    | some w => simp
  rw [this]
  exact Finset.measurable_sum _ fun v _ =>
    Measurable.ite (measurableSet_setOfPred.2 (meas_assign I β n j (some v)))
      (meas_price I β v j) measurable_const

lemma meas_dualAlpha (I : OBMRRInstance V n) (β : ℝ) (i : V) (t : Fin n) :
    Measurable (fun Y : Seeds V n => dualAlpha I β Y i t) := by
  have h : Measurable (fun Y : Seeds V n => ((Y (i, period I t) : unitInterval) : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply _)
  unfold dualAlpha
  refine Measurable.ite (measurableSet_setOfPred.2 (meas_assign I β n t (some i))) ?_
    measurable_const
  unfold g
  exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (h.sub_const 1)))

lemma meas_twoSeed (I : OBMRRInstance V n) (Y : Seeds V n) (i : V) (j : Fin n) :
    Measurable (fun p : unitInterval × unitInterval => twoSeed I Y i j p.1 p.2) := by
  rw [measurable_pi_iff]; intro k
  simp only [twoSeed, Function.update_apply]
  by_cases h1 : k = (i, period I j)
  · simp only [if_pos h1]; exact measurable_snd
  · by_cases h2 : k = (i, prevPeriod I j)
    · simp only [if_neg h1, if_pos h2]; exact measurable_fst
    · simp only [if_neg h1, if_neg h2]; exact measurable_const

lemma integrand_measurable (I : OBMRRInstance V n) (β : ℝ) (i : V) (j : Fin n) (Y : Seeds V n) :
    Measurable (fun p : unitInterval × unitInterval =>
      dualBeta I β (twoSeed I Y i j p.1 p.2) j +
        ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j p.1 p.2) i t) :=
  ((meas_dualBeta I β j).comp (meas_twoSeed I Y i j)).add
    (Finset.measurable_sum _ fun t _ => (meas_dualAlpha I β i t).comp (meas_twoSeed I Y i j))

lemma Q_bound (I : OBMRRInstance V n) {β : ℝ} (hβ : 0 ≤ β) (i : V) (j : Fin n) (Y : Seeds V n) :
    0 ≤ dualBeta I β Y j + ∑ t ∈ window I j, dualAlpha I β Y i t ∧
    dualBeta I β Y j + ∑ t ∈ window I j, dualAlpha I β Y i t ≤
      ∑ v, I.r v + (window I j).card * I.r i := by
  have hb : dualBeta I β Y j ≤ ∑ v, I.r v := by
    unfold dualBeta
    cases PeriodicReranking I β Y j with
    | none => exact Finset.sum_nonneg fun v _ => I.r_nonneg v
    | some w =>
      exact le_trans (price_le I β Y w j)
        (Finset.single_le_sum (fun v _ => I.r_nonneg v) (Finset.mem_univ w))
  have ha : ∀ t, dualAlpha I β Y i t ≤ I.r i := by
    intro t; unfold dualAlpha; split_ifs
    · exact mul_le_of_le_one_right (I.r_nonneg i) (g_le_one hβ (Y _).2.2)
    · exact I.r_nonneg i
  refine ⟨add_nonneg (dualBeta_nonneg I hβ Y j)
    (Finset.sum_nonneg fun t _ => dualAlpha_nonneg I Y i t), add_le_add hb ?_⟩
  calc ∑ t ∈ window I j, dualAlpha I β Y i t ≤ ∑ t ∈ window I j, I.r i :=
        Finset.sum_le_sum fun t _ => ha t
    _ = _ := by simp

/-! ### Middle regime -/

lemma assign_nat (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t u : ℕ) (hu : u < t)
    (ht : t ≤ n) : assignment I β Y t u = assignment I β Y n u := by
  rw [assign_stable I β Y t u hu, assign_stable I β Y n u (by omega)]

lemma mid_step1 (I : OBMRRInstance V n) (β : ℝ) (i : V) (j : Fin n) (Y : Seeds V n)
    (y1 y2 : unitInterval) (hB1 : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    dualBeta I β (twoSeed I Y i j y1 y2) j = dualBeta I β (twoSeed I Y i j y1 1) j := by
  classical
  have hnav : ∀ t : Fin n, period I t = period I j → t ≤ j →
      ¬ IsAvailable I (assignment I β (twoSeed I Y i j y1 1) t) i t := by
    intro t hp ht hav; apply hB1
    simp only [availableInSubperiod, availableSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, hp, ht, hav⟩
  have hag : assignment I β (twoSeed I Y i j y1 y2) (j + 1) =
      assignment I β (twoSeed I Y i j y1 1) (j + 1) := by
    apply agree
    intro t ht hh
    by_cases hp : period I t = period I j
    · unfold chooseResource
      apply lam_congr
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hwi : w ≠ i := by
        intro h; rw [h, hh] at hw
        exact hnav t hp (Fin.le_def.2 (by omega)) hw.2
      exact price_ts_ne I β Y i j _ _ _ _ hwi t
    · apply step_congr; intro w
      by_cases hw : w = i
      · rw [hw]
        by_cases hpp : period I t = prevPeriod I j
        · simp [reducedPrice, hpp, ts_pp]
        · simp [reducedPrice, ts_other I Y i j _ _ _ hpp hp]
      · exact price_ts_ne I β Y i j _ _ _ _ hw t
  have hPR : PeriodicReranking I β (twoSeed I Y i j y1 y2) j =
      PeriodicReranking I β (twoSeed I Y i j y1 1) j := by
    have h1 := assign_eq_PR I β (twoSeed I Y i j y1 y2) (j + 1) j (by omega) (by omega)
    have h2 := assign_eq_PR I β (twoSeed I Y i j y1 1) (j + 1) j (by omega) (by omega)
    rw [← h1, ← h2, hag]
  unfold dualBeta
  rw [hPR]
  cases h : PeriodicReranking I β (twoSeed I Y i j y1 1) j with
  | none => rfl
  | some v =>
    have hvi : v ≠ i := by
      intro hv; rw [hv] at h; exact hnav j rfl le_rfl (PR_spec I β _ j h).2.1
    exact price_ts_ne I β Y i j _ _ _ _ hvi j

lemma mid_step2 (I : OBMRRInstance V n) {β : ℝ} (hβ : 0 < β) (i : V) (j : Fin n) (Y : Seeds V n)
    (hA : ¬ MatchedInPrevPeriod I β (twoSeed I Y i j 1 1) i j) (y1 : unitInterval)
    (hB1 : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j) (w : V) (hwi : w ≠ i)
    (hwav : IsAvailable I (assignment I β (twoSeed I Y i j 1 1) j) w j)
    (hwpos : 0 < reducedPrice I β (twoSeed I Y i j 1 1) w j) :
    IsAvailable I (assignment I β (twoSeed I Y i j y1 1) j) w j := by
  classical
  have hd := I.one_le_d
  have hnav : ∀ t : Fin n, period I t = period I j → t ≤ j →
      ¬ IsAvailable I (assignment I β (twoSeed I Y i j y1 1) t) i t := by
    intro t hp ht hav; apply hB1
    simp only [availableInSubperiod, availableSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, hp, ht, hav⟩
  have hj := hnav j rfl le_rfl
  simp only [IsAvailable, not_forall] at hj
  obtain ⟨s, hsj, hBs', hjs⟩ := hj
  have hjs : (j : ℕ) < s + I.d := by omega
  have hsn : s < n := by omega
  have hBs : assignment I β (twoSeed I Y i j y1 1) n s = some i := by
    rw [← assign_nat I β _ j s hsj j.2.le]; exact hBs'
  have hPj : (j : ℕ) / I.d * I.d ≤ j := Nat.div_mul_le_self _ _
  have hsP : s < (j : ℕ) / I.d * I.d := by
    by_contra hc; push Not at hc
    have hsp := PR_spec I β _ ⟨s, hsn⟩ hBs
    exact hnav ⟨s, hsn⟩ (per_cur I j ⟨s, hsn⟩ hc (Fin.le_def.2 (show s ≤ (j : ℕ) by omega)))
      (Fin.le_def.2 (show s ≤ (j : ℕ) by omega)) hsp.2.1
  have hsprev : period I ⟨s, hsn⟩ = prevPeriod I j := per_prev I j ⟨s, hsn⟩ hjs hsP
  have hpre : assignment I β (twoSeed I Y i j 1 1) s =
      assignment I β (twoSeed I Y i j y1 1) s := by
    apply agree
    intro t ht hh
    by_cases hp : period I t = prevPeriod I j
    · apply step_lower I β _ _ _ t i
      · intro v hv hvi
        rw [hvi, hh, ← PR_eq] at hv
        have hsp := (PR_spec I β _ ⟨s, hsn⟩ hBs).2.1
        have h1 := hsp t ht (by rw [assign_nat I β _ s t ht (by omega)]; exact hv)
        have h2 : s < (t : ℕ) + I.d := same_period_close I t ⟨s, hsn⟩ (hp.trans hsprev.symm)
        have h1' : (t : ℕ) + I.d ≤ s := h1
        omega
      · intro w hw; exact price_ts_ne I β Y i j _ _ _ _ hw t
      · rw [price_i_one' I β Y i j 1 t hp]; exact price_nonneg I hβ.le _ _ _
    · have hpj : period I t ≠ period I j := per_lt I j t (by omega)
      apply step_congr
      intro w
      by_cases hw : w = i
      · rw [hw]
        simp [reducedPrice, ts_other I Y i j _ _ _ hp hpj]
      · exact price_ts_ne I β Y i j _ _ _ _ hw t
  have hpre' : ∀ u, u < s → assignment I β (twoSeed I Y i j 1 1) n u =
      assignment I β (twoSeed I Y i j y1 1) n u := by
    intro u hu
    rw [← assign_nat I β _ s u hu (by omega), ← assign_nat I β _ s u hu (by omega), hpre]
  have havail : ∀ t : Fin n, s ≤ (t : ℕ) → t ≤ j →
      (∀ v, v ≠ i → ((t : ℕ) ≤ (j : ℕ) / I.d * I.d ∨
          0 < reducedPrice I β (twoSeed I Y i j 1 1) v j) →
        ∀ u, s ≤ u → u < t → assignment I β (twoSeed I Y i j y1 1) n u = some v →
          ∃ u', s ≤ u' ∧ u' < t ∧ assignment I β (twoSeed I Y i j 1 1) n u' = some v) →
      ∀ v, v ≠ i → ((t : ℕ) ≤ (j : ℕ) / I.d * I.d ∨
          0 < reducedPrice I β (twoSeed I Y i j 1 1) v j) →
      IsAvailable I (assignment I β (twoSeed I Y i j 1 1) t) v t →
      IsAvailable I (assignment I β (twoSeed I Y i j y1 1) t) v t := by
    intro t hst htj hInv v hv hpos hav u hu hBu
    rw [assign_nat I β _ t u hu t.2.le] at hBu
    by_contra hlt
    by_cases hus : u < s
    · have := hav u hu (by rw [assign_nat I β _ t u hu t.2.le, hpre' u hus]; exact hBu)
      exact hlt this
    · obtain ⟨u', h1, h2, h3⟩ := hInv v hv hpos u (by omega) hu hBu
      have := hav u' h2 (by rw [assign_nat I β _ t u' h2 t.2.le]; exact h3)
      have : (t : ℕ) ≤ j := htj
      omega
  have hconv : ∀ t : Fin n, ∀ v,
      IsAvailable I (assignment I β (twoSeed I Y i j y1 1) t) v t →
      (∃ u', s ≤ u' ∧ u' < t ∧ assignment I β (twoSeed I Y i j 1 1) n u' = some v) ∨
      IsAvailable I (assignment I β (twoSeed I Y i j 1 1) t) v t := by
    intro t v hBav
    by_cases hex : ∃ u', s ≤ u' ∧ u' < t ∧ assignment I β (twoSeed I Y i j 1 1) n u' = some v
    · exact Or.inl hex
    · right
      intro u hu hAu
      rw [assign_nat I β _ t u hu t.2.le] at hAu
      by_cases hus : u < s
      · exact hBav u hu (by rw [assign_nat I β _ t u hu t.2.le, ← hpre' u hus]; exact hAu)
      · exact absurd ⟨u, by omega, hu, hAu⟩ hex
  have hind : ∀ k, s + k ≤ j →
      (∀ v, v ≠ i → (s + k ≤ (j : ℕ) / I.d * I.d ∨
          0 < reducedPrice I β (twoSeed I Y i j 1 1) v j) →
        ∀ u, s ≤ u → u < s + k → assignment I β (twoSeed I Y i j y1 1) n u = some v →
          ∃ u', s ≤ u' ∧ u' < s + k ∧ assignment I β (twoSeed I Y i j 1 1) n u' = some v) := by
    intro k
    induction k with
    | zero => intro _ v _ _ u h1 h2; omega
    | succ k ih =>
      intro hk v hv hpos u hsu hut hBu
      have hIH := ih (by omega)
      have htn : s + k < n := by omega
      rcases (show u < s + k ∨ u = s + k by omega) with hlt | heq
      · obtain ⟨u', h1, h2, h3⟩ := hIH v hv (hpos.imp_left (fun h => by omega)) u hsu hlt hBu
        exact ⟨u', h1, by omega, h3⟩
      · obtain ⟨tf, htf⟩ : ∃ tf : Fin n, (tf : ℕ) = s + k := ⟨⟨s + k, htn⟩, rfl⟩
        rw [heq, ← htf] at hBu
        have hBt : PeriodicReranking I β (twoSeed I Y i j y1 1) tf = some v := hBu
        obtain ⟨hvE, hvB, hvmax⟩ := PR_spec I β _ tf hBt
        rcases hconv tf v hvB with hex | hvA
        · obtain ⟨u', h1, h2, h3⟩ := hex; exact ⟨u', h1, by omega, h3⟩
        · cases ha : PeriodicReranking I β (twoSeed I Y i j 1 1) tf with
          | none => exact absurd hvA (PR_none I β _ tf ha v hvE)
          | some a =>
            obtain ⟨haE, haA, hamax⟩ := PR_spec I β _ tf ha
            have hva := hamax v hvE hvA
            have hai : a ≠ i ∧ ((tf : ℕ) ≤ (j : ℕ) / I.d * I.d ∨
                0 < reducedPrice I β (twoSeed I Y i j 1 1) a j) := by
              by_cases htP : (tf : ℕ) < (j : ℕ) / I.d * I.d
              · have hp : period I tf = prevPeriod I j := per_prev I j tf (by omega) htP
                exact ⟨fun hai => hA ⟨tf, hp, hai ▸ ha⟩, Or.inl htP.le⟩
              · push Not at htP
                have hp : period I tf = period I j :=
                  per_cur I j tf htP (Fin.le_def.2 (by omega))
                have hvpos : 0 < reducedPrice I β (twoSeed I Y i j 1 1) v j := by
                  rcases hpos with h | h
                  · omega
                  · exact h
                rw [price_period I β _ v tf j hp] at hva
                have hapos : 0 < reducedPrice I β (twoSeed I Y i j 1 1) a j := by
                  rw [← price_period I β _ a tf j hp]; linarith [hva.1]
                refine ⟨fun hai => ?_, Or.inr hapos⟩
                rw [hai, price_i_one I β Y i j 1 j rfl] at hapos
                exact lt_irrefl _ hapos
            have haB := havail tf (by omega) (Fin.le_def.2 (by omega))
              (by rw [htf]; exact hIH) a hai.1 hai.2 haA
            have hav := hvmax a haE haB
            rw [price_ts_ne I β Y i j y1 1 1 1 hai.1 tf,
              price_ts_ne I β Y i j y1 1 1 1 hv tf] at hav
            have heq' : reducedPrice I β (twoSeed I Y i j 1 1) v tf =
                reducedPrice I β (twoSeed I Y i j 1 1) a tf := le_antisymm hva.1 hav.1
            have h1 := hva.2 heq'
            have h2 := hav.2 heq'.symm
            have hav' : a = v := le_antisymm h1 h2
            rw [hav'] at ha
            exact ⟨tf, by omega, by omega, ha⟩
  have hInvj := hind ((j : ℕ) - s) (by omega)
  rw [show s + ((j : ℕ) - s) = j by omega] at hInvj
  exact havail j (by omega) le_rfl hInvj w hwi (Or.inr hwpos) hwav

/-- Middle regime: when `i` is not matched in period `k(j)-1` of `PR(1,1)` and
`i ∉ S_{p(j)}(y1,1)`, then `β_j(y1,y2) ≥ r_i(1 - g(y^c_j(1)))`. -/
lemma mid_bound (I : OBMRRInstance V n) {β : ℝ} (hβ : 0 < β) (i : V) (j : Fin n)
    (Y : Seeds V n) (hA : ¬ MatchedInPrevPeriod I β (twoSeed I Y i j 1 1) i j)
    (y1 y2 : unitInterval) (hB1 : i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    I.r i * (1 - g β (criticalThreshold I β Y i j 1 j)) ≤
      dualBeta I β (twoSeed I Y i j y1 y2) j := by
  classical
  rw [mid_step1 I β i j Y y1 y2 hB1]
  have hM : ∀ w, (w, j) ∈ I.E → IsAvailable I (assignment I β (twoSeed I Y i j 1 1) j) w j →
      reducedPrice I β (twoSeed I Y i j 1 1) w j ≤ dualBeta I β (twoSeed I Y i j y1 1) j := by
    intro w hw hav
    by_cases hpos : 0 < reducedPrice I β (twoSeed I Y i j 1 1) w j
    · have hwi : w ≠ i := by
        intro h; rw [h, price_i_one I β Y i j 1 j rfl] at hpos; exact lt_irrefl _ hpos
      have hBav := mid_step2 I hβ i j Y hA y1 hB1 w hwi hav hpos
      unfold dualBeta
      cases h : PeriodicReranking I β (twoSeed I Y i j y1 1) j with
      | none => exact absurd hBav (PR_none I β _ j h w hw)
      | some b =>
        have := ((PR_spec I β _ j h).2.2 w hw hBav).1
        rw [← price_ts_ne I β Y i j y1 1 1 1 hwi j]
        exact this
    · push Not at hpos; exact hpos.trans (dualBeta_nonneg I hβ.le _ j)
  unfold criticalThreshold
  dsimp only
  refine le_trans (ct_le hβ (I.r_nonneg i) ?_) ?_
  · split_ifs with hC
    · obtain ⟨w, hw⟩ := hC
      refine le_trans ?_ (Finset.le_sup' _ hw)
      exact price_nonneg I hβ.le _ _ _
    · exact le_rfl
  · split_ifs with hC
    · refine Finset.sup'_le _ _ fun w hw => ?_
      simp only [availableSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hM w hw.2 hw.1
    · exact dualBeta_nonneg I hβ.le _ j

lemma bot_ineq {β r c : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hr : 0 ≤ r) (hc : 0 ≤ c) :
    r * (1 - g β 0) ≤ r * (1 - g β c) + r * (G β c - G β 0) := by
  have hg : g β 0 ≤ g β c := g_mono hβ.le hc
  have : g β c - g β 0 ≤ G β c - G β 0 := by
    unfold G; rw [← sub_div]; exact le_div_self (by linarith) hβ hβ1
  nlinarith

lemma const_le_int (F : unitInterval → ℝ) (hF : Integrable F) {c : ℝ} (h : ∀ y, c ≤ F y) :
    c ≤ ∫ y, F y := by
  have := integral_mono (integrable_const c) hF h
  simpa using this

end RM9

open ReusableMatching MeasureTheory in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E)
    (Y : Seeds V n) :
    ∃ z1 z2 : ℝ, 0 ≤ z1 ∧ z1 ≤ z2 ∧ z2 ≤ 1 ∧
      I.r i * (G β z2 - G β z1 + (1 - g β (criticalThreshold I β Y i j 1 j)) * (1 - z1) +
          (1 - z2) * (G β (criticalThreshold I β Y i j 1 j) - G β 0) + z1 * (1 - g β 0)) ≤
        ∫ y1 : unitInterval, ∫ y2 : unitInterval,
          (dualBeta I β (twoSeed I Y i j y1 y2) j +
            ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t) := by
  classical
  obtain ⟨Z1, Z2, hZ, hTop, hMid, hBot⟩ := lemma_7 I β hβ0 i j hij Y
  have hZ' : (Z1 : ℝ) ≤ Z2 := hZ
  set Q : unitInterval → unitInterval → ℝ := fun y1 y2 =>
    dualBeta I β (twoSeed I Y i j y1 y2) j +
      ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t with hQ
  have hmeas : Measurable (Function.uncurry Q) := RM9.integrand_measurable I β i j Y
  set K : ℝ := ∑ v, I.r v + (window I j).card * I.r i with hK
  have hQb : ∀ y1 y2, 0 ≤ Q y1 y2 ∧ Q y1 y2 ≤ K := fun y1 y2 =>
    RM9.Q_bound I hβ0.le i j (twoSeed I Y i j y1 y2)
  have hint2 : Integrable (Function.uncurry Q) (volume.prod volume) :=
    (integrable_const K).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun p => by
      show ‖Q p.1 p.2‖ ≤ K
      rw [Real.norm_eq_abs, abs_of_nonneg (hQb _ _).1]; exact (hQb _ _).2)
  have hint1 : ∀ y1, Integrable (Q y1) := fun y1 =>
    (integrable_const K).mono' (hmeas.comp measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ fun y2 => by
        show ‖Q y1 y2‖ ≤ K
        rw [Real.norm_eq_abs, abs_of_nonneg (hQb _ _).1]; exact (hQb _ _).2)
  have hF : Integrable (fun y1 => ∫ y2, Q y1 y2) := hint2.integral_prod_left
  -- regimes with `i ∈ S_{p(j)}(y1,1)`
  have hS : ∀ y1 : unitInterval, i ∈ availableInSubperiod I β (twoSeed I Y i j y1 1) j →
      I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) +
        I.r i * (G β (criticalThreshold I β Y i j y1 j) - G β 0) ≤ ∫ y2, Q y1 y2 := by
    intro y1 hy1
    obtain ⟨h4a, h4b, h4c⟩ := lemma_4 I β hβ0 i j hij Y y1 hy1
    obtain ⟨hc0, hc1⟩ := RM9.ct_mem I β Y i j y1 j
    have hk := RM9.key_int (Q y1) (hint1 y1) (r := I.r i) (cb := 0)
      (m := I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)))
      (tp := I.r i * (1 - g β (criticalThreshold I β Y i j y1 j))) hβ0 le_rfl hc0 hc1
      (fun y hy => absurd hy (not_lt.2 y.2.1))
      (fun y _ hy2 => by
        have h1 := h4c y; rw [if_pos hy2] at h1
        have h2 := h4a y
        show _ ≤ dualBeta I β (twoSeed I Y i j y1 y) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y) i t
        linarith)
      (fun y hy => by
        have h1 := h4c y; rw [if_neg (not_lt.2 hy.le)] at h1
        have h2 := h4a y
        show _ ≤ dualBeta I β (twoSeed I Y i j y1 y) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y) i t
        linarith)
    have e : (0 : ℝ) * 0 + I.r i * (G β (criticalThreshold I β Y i j y1 j) - G β 0) +
        I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) *
          (criticalThreshold I β Y i j y1 j - 0) +
        I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) *
          (1 - criticalThreshold I β Y i j y1 j) =
        I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) +
          I.r i * (G β (criticalThreshold I β Y i j y1 j) - G β 0) := by ring
    linarith
  have hBotF : ∀ y1 : unitInterval, (y1 : ℝ) < Z1 → I.r i * (1 - g β 0) ≤ ∫ y2, Q y1 y2 := by
    intro y1 hy
    have h := hS y1 (hBot y1 hy).1
    exact le_trans (RM9.bot_ineq hβ0 hβ1 (I.r_nonneg i) (RM9.ct_mem I β Y i j y1 j).1) h
  rcases eq_or_lt_of_le (Z2.2.2 : (Z2 : ℝ) ≤ 1) with hZ2 | hZ2
  · refine ⟨1, 1, zero_le_one, le_rfl, le_rfl, ?_⟩
    have hk := RM9.key_int (fun y1 => ∫ y2, Q y1 y2) hF (r := I.r i)
      (cb := I.r i * (1 - g β 0)) (m := 0) (tp := 0) hβ0 Z1.2.1 (hZ2 ▸ hZ') le_rfl hBotF
      (fun y1 h1 h2 => by
        have hn := (hMid y1 h1 (by show (y1 : ℝ) < Z2; rw [hZ2]; exact h2)).1
        have h5 := lemma_5 I β hβ0 i j hij Y y1 hn
        refine RM9.const_le_int _ (hint1 y1) fun y2 => ?_
        have := h5 y2
        have := RM9.dualBeta_nonneg I hβ0.le (twoSeed I Y i j y1 y2) j
        show _ ≤ dualBeta I β (twoSeed I Y i j y1 y2) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t
        linarith)
      (fun y1 h => absurd h (not_lt.2 y1.2.2))
    have hc := mul_le_mul_of_nonneg_left (RM9.convex_bound hβ0 hβ1 Z1.2.1 Z1.2.2) (I.r_nonneg i)
    have e1 : I.r i * (G β 1 - G β 1 + (1 - g β (criticalThreshold I β Y i j 1 j)) * (1 - 1) +
        (1 - 1) * (G β (criticalThreshold I β Y i j 1 j) - G β 0) + 1 * (1 - g β 0)) =
        I.r i * (1 - g β 0) := by ring
    have e2 : I.r i * (1 - g β 0) * Z1 + I.r i * (G β 1 - G β Z1) + 0 * (1 - Z1) + 0 * (1 - 1)
        - I.r i * (1 - g β 0) =
        I.r i * (G β 1 - G β Z1) - I.r i * ((1 - g β 0) * (1 - Z1)) := by ring
    rw [e1]
    linarith
  · refine ⟨Z1, Z2, Z1.2.1, hZ', Z2.2.2, ?_⟩
    have hZ2' : Z2 < (1 : unitInterval) := hZ2
    have hA := (hTop 1 hZ2').2
    set x := criticalThreshold I β Y i j 1 j with hx
    have hk := RM9.key_int (fun y1 => ∫ y2, Q y1 y2) hF (r := I.r i)
      (cb := I.r i * (1 - g β 0)) (m := I.r i * (1 - g β x))
      (tp := I.r i * (1 - g β x) + I.r i * (G β x - G β 0)) hβ0 Z1.2.1 hZ' Z2.2.2 hBotF
      (fun y1 h1 h2 => by
        have hn := (hMid y1 h1 h2).1
        have h5 := lemma_5 I β hβ0 i j hij Y y1 hn
        refine RM9.const_le_int _ (hint1 y1) fun y2 => ?_
        have := h5 y2
        have := RM9.mid_bound I hβ0 i j Y hA y1 y2 hn
        show _ ≤ dualBeta I β (twoSeed I Y i j y1 y2) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t
        linarith)
      (fun y1 h => by
        have h' := hS y1 (hTop y1 h).1
        rw [RM9.top_eq I hβ0 i j Y y1 (hTop y1 h).2] at h'
        exact h')
    have e : I.r i * (G β Z2 - G β Z1 + (1 - g β x) * (1 - Z1) + (1 - Z2) * (G β x - G β 0) +
        Z1 * (1 - g β 0)) = I.r i * (1 - g β 0) * Z1 + I.r i * (G β Z2 - G β Z1) +
        I.r i * (1 - g β x) * (Z2 - Z1) + (I.r i * (1 - g β x) + I.r i * (G β x - G β 0)) *
          (1 - Z2) := by ring
    rw [e]
    exact hk
