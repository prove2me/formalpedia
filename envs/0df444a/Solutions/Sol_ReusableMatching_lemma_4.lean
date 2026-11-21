-- Prove2me | solution 1 for ReusableMatching.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:04:32.822078+00:00
-- url     : https://prove2.me/submissions/abe9e9fa-1937-417b-85aa-937e788ecd7e

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_availableInSubperiod
import Definitions.Def_ReusableMatching_criticalThreshold
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

namespace Aux_RM

theorem mem_filter_any {α : Type*} (s : Finset α) (p : α → Prop) (inst : DecidablePred p)
    (a : α) : a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := @Finset.mem_filter α p inst s a

theorem leastArgmax_mem {V : Type*} [LinearOrder V] (C : Finset V) (f : V → ℝ) (v : V)
    (h : leastArgmax C f = some v) : v ∈ C := by
  unfold leastArgmax at h
  by_cases hne : C.Nonempty
  · rw [dif_pos hne] at h
    injection h with h
    rw [← h]
    exact ((mem_filter_any _ _ _ _).mp (Finset.min'_mem _ _)).1
  · rw [dif_neg hne] at h
    cases h

theorem leastArgmax_congr {V : Type*} [LinearOrder V] (C : Finset V) (f f' : V → ℝ)
    (hf : ∀ v ∈ C, f v = f' v) : leastArgmax C f = leastArgmax C f' := by
  have hff : ∀ h : C.Nonempty, C.sup' h f = C.sup' h f' := fun h => Finset.sup'_congr h rfl hf
  have key : ∀ (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty), A = B →
      A.min' hA = B.min' hB := by
    rintro A B hA hB rfl
    rfl
  unfold leastArgmax
  by_cases h : C.Nonempty
  · rw [dif_pos h, dif_pos h]
    congr 1
    apply key
    ext v
    rw [mem_filter_any, mem_filter_any]
    constructor
    · rintro ⟨hv, hv2⟩
      exact ⟨hv, by rw [← hf v hv, ← hff h]; exact hv2⟩
    · rintro ⟨hv, hv2⟩
      exact ⟨hv, by rw [hf v hv, hff h]; exact hv2⟩
  · rw [dif_neg h, dif_neg h]

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem assign_succ (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (t : ℕ) :
    assignment I β Y (t + 1) = Function.update (assignment I β Y t) t
      (if h : t < n then chooseResource I β Y (assignment I β Y t) ⟨t, h⟩ else none) := rfl

theorem assign_stab (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) :
    ∀ m s, s < m → assignment I β Y m s = assignment I β Y (s + 1) s := by
  intro m
  induction m with
  | zero => intro s hs; exact absurd hs (Nat.not_lt_zero _)
  | succ m ih =>
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
    · rw [assign_succ, Function.update_of_ne (by omega), ih s h]
    · rw [h]

theorem assign_avail (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (s : ℕ) (v : V)
    (h : assignment I β Y (s + 1) s = some v) :
    s < n ∧ IsAvailable I (assignment I β Y s) v s := by
  rw [assign_succ, Function.update_self] at h
  by_cases hs : s < n
  · rw [dif_pos hs] at h
    refine ⟨hs, ?_⟩
    unfold chooseResource at h
    have := leastArgmax_mem _ _ v h
    exact ((mem_filter_any _ _ _ _).mp this).2.2
  · rw [dif_neg hs] at h
    cases h

end Aux_RM

namespace Aux_RM

open MeasureTheory

theorem min'_spec {V : Type*} [LinearOrder V] (F : Finset V) (hF : F.Nonempty) (v : V) :
    F.min' hF = v ↔ v ∈ F ∧ ∀ w ∈ F, v ≤ w := by
  constructor
  · rintro rfl
    exact ⟨Finset.min'_mem F hF, fun w hw => Finset.min'_le F w hw⟩
  · rintro ⟨hv, hle⟩
    exact le_antisymm (Finset.min'_le F v hv) (Finset.le_min' F hF v hle)

theorem la_none {V : Type*} [LinearOrder V] (C : Finset V) (P : V → ℝ) :
    leastArgmax C P = none ↔ ¬ C.Nonempty := by
  unfold leastArgmax
  by_cases h : C.Nonempty
  · rw [dif_pos h]
    simp [h]
  · rw [dif_neg h]
    simp [h]

theorem la_some {V : Type*} [LinearOrder V] (C : Finset V) (P : V → ℝ) (v : V) :
    leastArgmax C P = some v ↔
      v ∈ C ∧ (∀ w, w ∈ C → P w ≤ P v) ∧ (∀ w, w ∈ C → w < v → P w < P v) := by
  unfold leastArgmax
  by_cases h : C.Nonempty
  · rw [dif_pos h, Option.some_inj, min'_spec, mem_filter_any]
    simp only [mem_filter_any]
    constructor
    · rintro ⟨⟨hvC, hvs⟩, hmin⟩
      refine ⟨hvC, fun w hw => (Finset.le_sup' P hw).trans hvs.ge, fun w hw hwv => ?_⟩
      have h1 : P w ≤ P v := (Finset.le_sup' P hw).trans hvs.ge
      rcases lt_or_eq_of_le h1 with h2 | h2
      · exact h2
      · exfalso
        have := hmin w ⟨hw, h2.trans hvs⟩
        exact absurd hwv (not_lt.mpr this)
    · rintro ⟨hvC, hle, hlt⟩
      have hvs : P v = C.sup' h P :=
        le_antisymm (Finset.le_sup' P hvC) (Finset.sup'_le h P (fun w hw => hle w hw))
      refine ⟨⟨hvC, hvs⟩, fun w hw => ?_⟩
      obtain ⟨hwC, hws⟩ := hw
      by_contra hcon
      push_neg at hcon
      have := hlt w hwC hcon
      rw [hws, ← hvs] at this
      exact lt_irrefl _ this
  · rw [dif_neg h]
    constructor
    · intro h'
      cases h'
    · rintro ⟨hv, _⟩
      exact absurd ⟨v, hv⟩ h

theorem la_meas {V : Type*} [Fintype V] [LinearOrder V] (C : Finset V) (w : Option V) :
    MeasurableSet {P : V → ℝ | leastArgmax C P = w} := by
  cases w with
  | none =>
    have : {P : V → ℝ | leastArgmax C P = none} = {_P | ¬ C.Nonempty} := by
      ext P
      exact la_none C P
    rw [this]
    exact MeasurableSet.const _
  | some v =>
    have : {P : V → ℝ | leastArgmax C P = some v} =
        {P | v ∈ C ∧ (∀ w, w ∈ C → P w ≤ P v) ∧ (∀ w, w ∈ C → w < v → P w < P v)} := by
      ext P
      exact la_some C P v
    rw [this]
    apply measurableSet_setOfPred.mpr
    apply Measurable.and measurable_const
    apply Measurable.and
    · apply Measurable.forall
      intro w
      apply Measurable.imp measurable_const
      exact measurableSet_setOfPred.mp (measurableSet_le (measurable_pi_apply w) (measurable_pi_apply v))
    · apply Measurable.forall
      intro w
      apply Measurable.imp measurable_const
      apply Measurable.imp measurable_const
      exact measurableSet_setOfPred.mp (measurableSet_lt (measurable_pi_apply w) (measurable_pi_apply v))

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem choose_congr (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (a a' : ℕ → Option V)
    (t : Fin n) (h : ∀ s, s < (t : ℕ) → a s = a' s) :
    chooseResource I β Y a t = chooseResource I β Y a' t := by
  unfold chooseResource
  congr 1
  ext v
  rw [mem_filter_any, mem_filter_any]
  unfold IsAvailable
  constructor
  · rintro ⟨hu, he, hav⟩
    exact ⟨hu, he, fun s hs hsv => hav s hs (by rw [h s hs]; exact hsv)⟩
  · rintro ⟨hu, he, hav⟩
    exact ⟨hu, he, fun s hs hsv => hav s hs (by rw [← h s hs]; exact hsv)⟩

theorem seed_meas (q : V × Fin (n + 1)) :
    Measurable fun Y : Seeds V n => ((Y q : unitInterval) : ℝ) :=
  measurable_subtype_coe.comp (measurable_pi_apply q)

theorem g_meas (β : ℝ) (q : V × Fin (n + 1)) :
    Measurable fun Y : Seeds V n => g β (Y q) := by
  unfold g
  exact Real.measurable_exp.comp (((seed_meas q).sub_const 1).const_mul β)

theorem choose_meas (I : OBMRRInstance V n) (β : ℝ) (a : ℕ → Option V) (t : Fin n)
    (w : Option V) : MeasurableSet {Y : Seeds V n | chooseResource I β Y a t = w} := by
  have hΦ : Measurable fun Y : Seeds V n => fun v => reducedPrice I β Y v t := by
    apply measurable_pi_lambda
    intro v
    unfold reducedPrice
    exact (measurable_const.sub (g_meas β _)).const_mul (I.r v)
  unfold chooseResource
  exact hΦ (la_meas _ w)

theorem assign_meas (I : OBMRRInstance V n) (β : ℝ) :
    ∀ (m s : ℕ) (w : Option V), MeasurableSet {Y : Seeds V n | assignment I β Y m s = w} := by
  intro m
  induction m with
  | zero =>
    intro s w
    show MeasurableSet {Y : Seeds V n | (none : Option V) = w}
    exact MeasurableSet.const _
  | succ m ih =>
    intro s w
    by_cases hs : s = m
    · subst hs
      have e : ∀ Y : Seeds V n, assignment I β Y (s + 1) s =
          (if h : s < n then chooseResource I β Y (assignment I β Y s) ⟨s, h⟩ else none) := by
        intro Y
        rw [assign_succ, Function.update_self]
      simp only [e]
      by_cases hm : s < n
      · simp only [dif_pos hm]
        have hset : {Y : Seeds V n | chooseResource I β Y (assignment I β Y s) ⟨s, hm⟩ = w} =
            ⋃ hst : Fin s → Option V,
              ({Y : Seeds V n | ∀ k : Fin s, assignment I β Y s k = hst k} ∩
               {Y : Seeds V n | chooseResource I β Y
                  (fun r => if hr : r < s then hst ⟨r, hr⟩ else none) ⟨s, hm⟩ = w}) := by
          ext Y
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
          constructor
          · intro hY
            refine ⟨fun k => assignment I β Y s k, fun k => rfl, ?_⟩
            rw [← hY]
            apply choose_congr
            intro r hr
            simp only [dif_pos (show r < s from hr)]
          · rintro ⟨hst, hagr, hY⟩
            rw [← hY]
            apply choose_congr
            intro r hr
            have hr' : r < s := hr
            simp only [dif_pos hr']
            exact hagr ⟨r, hr'⟩
        rw [hset]
        apply MeasurableSet.iUnion
        intro hst
        apply MeasurableSet.inter
        · apply measurableSet_setOfPred.mpr
          apply Measurable.forall
          intro k
          exact measurableSet_setOfPred.mp (ih k (hst k))
        · exact choose_meas I β _ _ w
      · simp only [dif_neg hm]
        exact MeasurableSet.const _
    · have e : ∀ Y : Seeds V n, assignment I β Y (m + 1) s = assignment I β Y m s := by
        intro Y
        rw [assign_succ, Function.update_of_ne hs]
      simp only [e]
      exact ih s w

end Aux_RM

namespace Aux_RM

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem g_bounds (β : ℝ) (hβ : 0 < β) (y : unitInterval) : 0 ≤ g β y ∧ g β y ≤ 1 := by
  unfold g
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_le_one_iff]
  have := y.2.2
  have h1 : (y : ℝ) - 1 ≤ 0 := by linarith
  nlinarith

theorem mem_avail_sub (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j t : Fin n)
    (hpt : period I t = period I j) (htj : t ≤ j)
    (hav : IsAvailable I (assignment I β Y t) i t) :
    i ∈ availableInSubperiod I β Y j := by
  unfold availableInSubperiod
  rw [mem_filter_any]
  refine ⟨Finset.mem_univ _, t, hpt, htj, ?_⟩
  unfold availableSet
  rw [mem_filter_any]
  exact ⟨Finset.mem_univ _, hav⟩

theorem PR_eq (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (s m : ℕ) (hs : s < n)
    (hsm : s < m) :
    PeriodicReranking I β Y ⟨s, hs⟩ = assignment I β Y m s := by
  unfold PeriodicReranking
  show assignment I β Y n s = assignment I β Y m s
  rw [assign_stab I β Y n s hs, assign_stab I β Y m s hsm]

end Aux_RM

namespace Aux_RM

theorem cmp_choice {V : Type*} [LinearOrder V] (C : Finset V) (P P' : V → ℝ) (i : V)
    (hP : ∀ w, w ≠ i → P' w = P w) (hi : P i ≤ P' i) :
    (leastArgmax C P' = leastArgmax C P ∨ leastArgmax C P' = some i) ∧
      (leastArgmax C P = some i → leastArgmax C P' = some i) := by
  have part2 : leastArgmax C P = some i → leastArgmax C P' = some i := by
    intro h
    rw [la_some] at h ⊢
    obtain ⟨hiC, hle, hlt⟩ := h
    refine ⟨hiC, fun w hw => ?_, fun w hw hwi => ?_⟩
    · by_cases hwi : w = i
      · subst hwi
        exact le_rfl
      · rw [hP w hwi]
        have := hle w hw
        linarith
    · have hwi' : w ≠ i := ne_of_lt hwi
      rw [hP w hwi']
      have := hlt w hw hwi
      linarith
  refine ⟨?_, part2⟩
  cases hc' : leastArgmax C P' with
  | none =>
    left
    rw [eq_comm, la_none]
    rw [la_none] at hc'
    exact hc'
  | some v' =>
    by_cases hv' : v' = i
    · right
      rw [hv']
    · left
      symm
      rw [la_some]
      rw [la_some] at hc'
      obtain ⟨hvC, hle, hlt⟩ := hc'
      refine ⟨hvC, fun w hw => ?_, fun w hw hwv => ?_⟩
      · by_cases hwi : w = i
        · rw [hwi]
          have := hle i (hwi ▸ hw)
          rw [hP v' hv'] at this
          linarith
        · have := hle w hw
          rw [hP w hwi, hP v' hv'] at this
          exact this
      · by_cases hwi : w = i
        · have := hlt w hw hwv
          rw [hP v' hv'] at this
          rw [hwi] at this ⊢
          linarith
        · have := hlt w hw hwv
          rw [hP w hwi, hP v' hv'] at this
          exact this

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem choose_eq (I : OBMRRInstance V n) (β : ℝ) (a : ℕ → Option V) (t : Fin n) :
    ∃ C : Finset V, ∀ Y' : Seeds V n,
      chooseResource I β Y' a t = leastArgmax C (fun v => reducedPrice I β Y' v t) :=
  ⟨_, fun _ => rfl⟩

theorem pp_ne (I : OBMRRInstance V n) (i : V) (j : Fin n) :
    (i, prevPeriod I j) ≠ (i, period I j) := by
  intro h
  have h' : ((prevPeriod I j : Fin (n + 1)) : ℕ) = ((period I j : Fin (n + 1)) : ℕ) := by
    rw [(Prod.mk.inj h).2]
  have e1 : ((prevPeriod I j : Fin (n + 1)) : ℕ) = (j : ℕ) / I.d := rfl
  have e2 : ((period I j : Fin (n + 1)) : ℕ) = (j : ℕ) / I.d + 1 := rfl
  rw [e1, e2] at h'
  exact (Nat.succ_ne_self _) h'.symm

theorem lemma6_main (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n)
    (Y : Seeds V n) (z y2 : unitInterval) (tz : Fin n) (htz : period I tz = prevPeriod I j)
    (hmatch : PeriodicReranking I β (twoSeed I Y i j z y2) tz = some i)
    (y1 : unitInterval) (hy : y1 ≤ z) :
    ∃ t : Fin n, period I t = prevPeriod I j ∧ t ≤ tz ∧
      PeriodicReranking I β (twoSeed I Y i j y1 y2) t = some i := by
  obtain ⟨R, hR⟩ : ∃ Z, Z = twoSeed I Y i j z y2 := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ Z, Z = twoSeed I Y i j y1 y2 := ⟨_, rfl⟩
  rw [← hR] at hmatch
  rw [← hR']
  have hpp := pp_ne I i j
  have hseed_eq : ∀ q, q ≠ (i, prevPeriod I j) → R q = R' q := by
    intro q hq
    rw [hR, hR']
    unfold twoSeed
    by_cases hq2 : q = (i, period I j)
    · rw [hq2, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq2, Function.update_of_ne hq2, Function.update_of_ne hq,
        Function.update_of_ne hq]
  have hRi : R (i, prevPeriod I j) = z := by
    rw [hR]; unfold twoSeed; rw [Function.update_of_ne hpp, Function.update_self]
  have hR'i : R' (i, prevPeriod I j) = y1 := by
    rw [hR']; unfold twoSeed; rw [Function.update_of_ne hpp, Function.update_self]
  have hprice : ∀ (m : Fin n) (v : V), (v ≠ i ∨ period I m ≠ prevPeriod I j) →
      reducedPrice I β R' v m = reducedPrice I β R v m := by
    intro m v h
    unfold reducedPrice
    rw [hseed_eq (v, period I m) (by
      intro hh
      rcases h with h | h
      · exact h (Prod.mk.inj hh).1
      · exact h (Prod.mk.inj hh).2)]
  have hprice_i : ∀ m : Fin n, reducedPrice I β R i m ≤ reducedPrice I β R' i m := by
    intro m
    by_cases hm : period I m = prevPeriod I j
    · unfold reducedPrice
      rw [hm, hRi, hR'i]
      have hyz : (y1 : ℝ) ≤ (z : ℝ) := hy
      have hg : g β y1 ≤ g β z := by
        unfold g
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hr := I.r_nonneg i
      nlinarith
    · exact (hprice m i (Or.inr hm)).ge
  have hchoice : ∀ (m : Fin n) (a : ℕ → Option V),
      (chooseResource I β R' a m = chooseResource I β R a m ∨
        (chooseResource I β R' a m = some i ∧ period I m = prevPeriod I j)) ∧
      (chooseResource I β R a m = some i → chooseResource I β R' a m = some i) := by
    intro m a
    obtain ⟨C, hC⟩ := choose_eq I β a m
    rw [hC R, hC R']
    by_cases hm : period I m = prevPeriod I j
    · obtain ⟨h1, h2⟩ := cmp_choice C (fun v => reducedPrice I β R v m)
        (fun v => reducedPrice I β R' v m) i (fun w hw => hprice m w (Or.inl hw)) (hprice_i m)
      exact ⟨h1.imp id (fun h => ⟨h, hm⟩), h2⟩
    · have heq : leastArgmax C (fun v => reducedPrice I β R' v m) =
          leastArgmax C (fun v => reducedPrice I β R v m) := by
        apply leastArgmax_congr
        intro v _
        exact hprice m v (Or.inr hm)
      exact ⟨Or.inl heq, fun h => by rw [heq]; exact h⟩
  have hTn := tz.isLt
  have key : ∀ m : ℕ, m ≤ (tz : ℕ) →
      (∃ t : Fin n, period I t = prevPeriod I j ∧ (t : ℕ) < m ∧
        assignment I β R' (t + 1) t = some i) ∨
      assignment I β R m = assignment I β R' m := by
    intro m
    induction m with
    | zero => intro _; right; rfl
    | succ m ih =>
      intro hm
      rcases ih (by omega) with h | h
      · left
        obtain ⟨t, h1, h2, h3⟩ := h
        exact ⟨t, h1, by omega, h3⟩
      · have hmn : m < n := by omega
        obtain ⟨hc1, _⟩ := hchoice ⟨m, hmn⟩ (assignment I β R' m)
        rcases hc1 with hc | ⟨hc, hp⟩
        · right
          rw [assign_succ, assign_succ, h, dif_pos hmn, dif_pos hmn, hc]
        · left
          refine ⟨⟨m, hmn⟩, hp, (show m < m + 1 by omega), ?_⟩
          show assignment I β R' (m + 1) m = some i
          rw [assign_succ, Function.update_self, dif_pos hmn]
          exact hc
  rcases key tz le_rfl with h | h
  · obtain ⟨t, h1, h2, h3⟩ := h
    refine ⟨t, h1, le_of_lt h2, ?_⟩
    unfold PeriodicReranking
    rw [assign_stab I β R' n t t.isLt]
    exact h3
  · refine ⟨tz, htz, le_rfl, ?_⟩
    have hR1 : assignment I β R (tz + 1) tz = some i := by
      unfold PeriodicReranking at hmatch
      rw [← assign_stab I β R n tz tz.isLt]
      exact hmatch
    rw [assign_succ, Function.update_self, dif_pos tz.isLt] at hR1
    have hR'1 := (hchoice tz (assignment I β R tz)).2 hR1
    rw [h] at hR'1
    unfold PeriodicReranking
    rw [assign_stab I β R' n tz tz.isLt, assign_succ, Function.update_self, dif_pos tz.isLt]
    exact hR'1

end Aux_RM

namespace Aux_RM

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem choose_eq2 (I : OBMRRInstance V n) (β : ℝ) (a : ℕ → Option V) (t : Fin n) :
    ∃ C : Finset V, (∀ w, w ∈ C ↔ ((w, t) ∈ I.E ∧ IsAvailable I a w t)) ∧ ∀ Y' : Seeds V n,
      chooseResource I β Y' a t = leastArgmax C (fun v => reducedPrice I β Y' v t) := by
  refine ⟨_, ?_, fun _ => rfl⟩
  intro w
  rw [mem_filter_any]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem rp_nonneg (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (Y : Seeds V n) (v : V)
    (t : Fin n) : 0 ≤ reducedPrice I β Y v t := by
  unfold reducedPrice
  have hg := g_bounds β hβ (Y (v, period I t))
  exact mul_nonneg (I.r_nonneg v) (by linarith [hg.2])

theorem dualBeta_nonneg (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (Y : Seeds V n)
    (t : Fin n) : 0 ≤ dualBeta I β Y t := by
  unfold dualBeta
  cases PeriodicReranking I β Y t with
  | none => exact le_rfl
  | some v => exact rp_nonneg I β hβ Y v t

theorem choice_cmp (I : OBMRRInstance V n) (β : ℝ) (Ylo Yhi : Seeds V n) (i : V)
    (k : Fin (n + 1)) (hag : ∀ q, q ≠ (i, k) → Ylo q = Yhi q)
    (hg : g β (Yhi (i, k)) ≤ g β (Ylo (i, k))) (m : Fin n) (a : ℕ → Option V) :
    (chooseResource I β Yhi a m = chooseResource I β Ylo a m ∨
      (chooseResource I β Yhi a m = some i ∧ period I m = k)) ∧
    (chooseResource I β Ylo a m = some i → chooseResource I β Yhi a m = some i) := by
  have hprice : ∀ v : V, (v ≠ i ∨ period I m ≠ k) →
      reducedPrice I β Yhi v m = reducedPrice I β Ylo v m := by
    intro v h
    unfold reducedPrice
    rw [hag (v, period I m) (by
      intro hh
      rcases h with h | h
      · exact h (Prod.mk.inj hh).1
      · exact h (Prod.mk.inj hh).2)]
  have hprice_i : reducedPrice I β Ylo i m ≤ reducedPrice I β Yhi i m := by
    by_cases hm : period I m = k
    · unfold reducedPrice
      rw [hm]
      have hr := I.r_nonneg i
      nlinarith
    · exact (hprice i (Or.inr hm)).ge
  obtain ⟨C, _, hC⟩ := choose_eq2 I β a m
  rw [hC Ylo, hC Yhi]
  by_cases hm : period I m = k
  · obtain ⟨h1, h2⟩ := cmp_choice C (fun v => reducedPrice I β Ylo v m)
      (fun v => reducedPrice I β Yhi v m) i (fun w hw => hprice w (Or.inl hw)) hprice_i
    exact ⟨h1.imp id (fun h => ⟨h, hm⟩), h2⟩
  · have heq : leastArgmax C (fun v => reducedPrice I β Yhi v m) =
        leastArgmax C (fun v => reducedPrice I β Ylo v m) := by
      apply leastArgmax_congr
      intro v _
      exact hprice v (Or.inr hm)
    exact ⟨Or.inl heq, fun h => by rw [heq]; exact h⟩

theorem agree_until (I : OBMRRInstance V n) (β : ℝ) (Ylo Yhi : Seeds V n) (i : V)
    (k : Fin (n + 1)) (hag : ∀ q, q ≠ (i, k) → Ylo q = Yhi q)
    (hg : g β (Yhi (i, k)) ≤ g β (Ylo (i, k))) :
    ∀ m : ℕ, m ≤ n →
      (∃ t : Fin n, period I t = k ∧ (t : ℕ) < m ∧ assignment I β Yhi (t + 1) t = some i) ∨
      assignment I β Ylo m = assignment I β Yhi m := by
  intro m
  induction m with
  | zero => intro _; right; rfl
  | succ m ih =>
    intro hm
    rcases ih (by omega) with h | h
    · left
      obtain ⟨t, h1, h2, h3⟩ := h
      exact ⟨t, h1, by omega, h3⟩
    · have hmn : m < n := by omega
      obtain ⟨hc1, _⟩ := choice_cmp I β Ylo Yhi i k hag hg ⟨m, hmn⟩ (assignment I β Yhi m)
      rcases hc1 with hc | ⟨hc, hp⟩
      · right
        rw [assign_succ, assign_succ, h, dif_pos hmn, dif_pos hmn, hc]
      · left
        refine ⟨⟨m, hmn⟩, hp, (show m < m + 1 by omega), ?_⟩
        show assignment I β Yhi (m + 1) m = some i
        rw [assign_succ, Function.update_self, dif_pos hmn]
        exact hc

end Aux_RM

namespace Aux_RM

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem PR_choose (I : OBMRRInstance V n) (β : ℝ) (Z : Seeds V n) (t : Fin n) :
    PeriodicReranking I β Z t = chooseResource I β Z (assignment I β Z t) t := by
  unfold PeriodicReranking
  rw [assign_stab I β Z n t t.isLt, assign_succ, Function.update_self, dif_pos t.isLt]

theorem assign_step (I : OBMRRInstance V n) (β : ℝ) (Z : Seeds V n) (m : ℕ) (hmn : m < n) :
    assignment I β Z (m + 1) m = chooseResource I β Z (assignment I β Z m) ⟨m, hmn⟩ := by
  rw [assign_succ, Function.update_self, dif_pos hmn]

theorem dualBeta_of (I : OBMRRInstance V n) (β : ℝ) (Z : Seeds V n) (t : Fin n)
    (o : Option V) (h : PeriodicReranking I β Z t = o) :
    dualBeta I β Z t = o.elim 0 (fun v => reducedPrice I β Z v t) := by
  unfold dualBeta
  rw [h]

theorem beta_eq_max (I : OBMRRInstance V n) (β : ℝ) (Y' : Seeds V n) (t : Fin n) :
    (if h : ((availableSet I β Y' t).filter (fun v => (v, t) ∈ I.E)).Nonempty then
      ((availableSet I β Y' t).filter (fun v => (v, t) ∈ I.E)).sup' h
        (fun v => reducedPrice I β Y' v t) else 0) = dualBeta I β Y' t := by
  obtain ⟨C', hC'mem, hC'⟩ := choose_eq2 I β (assignment I β Y' t) t
  have hPR : PeriodicReranking I β Y' t = leastArgmax C' (fun v => reducedPrice I β Y' v t) := by
    rw [← hC' Y', PR_choose]
  have hmem : ∀ w, w ∈ (availableSet I β Y' t).filter (fun v => (v, t) ∈ I.E) ↔ w ∈ C' := by
    intro w
    rw [Finset.mem_filter, hC'mem]
    unfold availableSet
    rw [mem_filter_any]
    exact ⟨fun ⟨⟨_, ha⟩, he⟩ => ⟨he, ha⟩, fun ⟨he, ha⟩ => ⟨⟨Finset.mem_univ _, ha⟩, he⟩⟩
  unfold dualBeta
  rw [hPR]
  by_cases hC : ((availableSet I β Y' t).filter (fun v => (v, t) ∈ I.E)).Nonempty
  · rw [dif_pos hC]
    have hC'ne : C'.Nonempty := by
      obtain ⟨w, hw⟩ := hC
      exact ⟨w, (hmem w).mp hw⟩
    cases hla : leastArgmax C' (fun v => reducedPrice I β Y' v t) with
    | none =>
      rw [la_none] at hla
      exact absurd hC'ne hla
    | some u =>
      rw [la_some] at hla
      obtain ⟨huC, hle, _⟩ := hla
      show _ = reducedPrice I β Y' u t
      apply le_antisymm
      · exact Finset.sup'_le hC _ (fun w hw => hle w ((hmem w).mp hw))
      · exact Finset.le_sup' (fun v => reducedPrice I β Y' v t) ((hmem u).mpr huC)
  · rw [dif_neg hC]
    have hC'e : ¬ C'.Nonempty := by
      rintro ⟨w, hw⟩
      exact hC ⟨w, (hmem w).mpr hw⟩
    have : leastArgmax C' (fun v => reducedPrice I β Y' v t) = none := (la_none _ _).mpr hC'e
    simp [this]

theorem ct_eq (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (y1 : unitInterval) (t : Fin n) :
    criticalThreshold I β Y i j y1 t = sSup {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧
      dualBeta I β (twoSeed I Y i j y1 1) t ≤ I.r i * (1 - g β y)} := by
  rw [← beta_eq_max I β (twoSeed I Y i j y1 1) t]
  rfl

theorem lemma4_main (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n)
    (hij : (i, j) ∈ I.E) (Y : Seeds V n) (y1 : unitInterval)
    (hi : i ∈ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    (∀ y2 : unitInterval,
      dualBeta I β (twoSeed I Y i j y1 1) j ≤ dualBeta I β (twoSeed I Y i j y1 y2) j) ∧
    I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) ≤
      dualBeta I β (twoSeed I Y i j y1 1) j ∧
    (∀ y2 : unitInterval,
      (if (y2 : ℝ) < criticalThreshold I β Y i j y1 j then I.r i * g β y2 else 0) ≤
        ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t) := by
  have hd : 0 < I.d := by have := I.one_le_d; omega
  have hjn := j.isLt
  rw [ct_eq I β Y i j y1 j]
  obtain ⟨R1, hR1⟩ : ∃ Z, Z = twoSeed I Y i j y1 1 := ⟨_, rfl⟩
  rw [← hR1]
  rw [← hR1] at hi
  have hseed : ∀ y2 : unitInterval, ∀ q, q ≠ (i, period I j) →
      R1 q = twoSeed I Y i j y1 y2 q := by
    intro y2 q hq
    rw [hR1]
    unfold twoSeed
    rw [Function.update_of_ne hq, Function.update_of_ne hq]
  have hR1j : R1 (i, period I j) = 1 := by
    rw [hR1]; unfold twoSeed; rw [Function.update_self]
  have hR2j : ∀ y2 : unitInterval, twoSeed I Y i j y1 y2 (i, period I j) = y2 := by
    intro y2; unfold twoSeed; rw [Function.update_self]
  have hg1 : g β ((1 : unitInterval) : ℝ) = 1 := by unfold g; simp
  have hgle : ∀ y2 : unitInterval,
      g β (twoSeed I Y i j y1 y2 (i, period I j)) ≤ g β (R1 (i, period I j)) := by
    intro y2
    rw [hR2j, hR1j, hg1]
    exact (g_bounds β hβ y2).2
  have hprice_eq : ∀ (y2 : unitInterval) (v : V) (m : Fin n), v ≠ i →
      reducedPrice I β (twoSeed I Y i j y1 y2) v m = reducedPrice I β R1 v m := by
    intro y2 v m hv
    unfold reducedPrice
    rw [hseed y2 (v, period I m) (fun hh => hv (Prod.mk.inj hh).1)]
  have hP1i : ∀ m : Fin n, period I m = period I j → reducedPrice I β R1 i m = 0 := by
    intro m hm
    unfold reducedPrice
    rw [hm, hR1j, hg1]
    ring
  have hper : ∀ (Z : Seeds V n) (v : V) (m : Fin n), period I m = period I j →
      reducedPrice I β Z v m = reducedPrice I β Z v j := by
    intro Z v m hm
    unfold reducedPrice
    rw [hm]
  -- the maximum price M at j in the run R1
  obtain ⟨M, hM⟩ : ∃ M, M = dualBeta I β R1 j := ⟨_, rfl⟩
  rw [← hM]
  have hM0 : 0 ≤ M := by rw [hM]; exact dualBeta_nonneg I β hβ R1 j
  obtain ⟨C1, hC1mem, hC1⟩ := choose_eq2 I β (assignment I β R1 j) j
  have hPR1 : PeriodicReranking I β R1 j = leastArgmax C1 (fun v => reducedPrice I β R1 v j) := by
    rw [← hC1 R1, PR_choose]
  have hMmax : ∀ w ∈ C1, reducedPrice I β R1 w j ≤ M := by
    intro w hw
    cases hla : leastArgmax C1 (fun v => reducedPrice I β R1 v j) with
    | none =>
      rw [la_none] at hla
      exact absurd ⟨w, hw⟩ hla
    | some u =>
      have hMu : M = reducedPrice I β R1 u j := by
        rw [hM]; exact dualBeta_of I β R1 j _ (hPR1.trans hla)
      rw [la_some] at hla
      rw [hMu]
      exact hla.2.1 w hw
  -- the critical-threshold set
  have hcont : Continuous fun y : ℝ => I.r i * (1 - g β y) := by
    unfold g; fun_prop
  refine ⟨?_, ?_, ?_⟩
  -- Part 1a
  · intro y2
    have hseed2 := hseed y2
    have hgle2 := hgle y2
    obtain ⟨R2, hR2⟩ : ∃ Z, Z = twoSeed I Y i j y1 y2 := ⟨_, rfl⟩
    rw [← hR2]
    rw [← hR2] at hseed2 hgle2
    have hpe : ∀ (v : V) (m : Fin n), v ≠ i →
        reducedPrice I β R2 v m = reducedPrice I β R1 v m := by
      intro v m hv
      rw [hR2]
      exact hprice_eq y2 v m hv
    obtain ⟨t0, ht0⟩ : ∃ t0, t0 = (j : ℕ) / I.d * I.d := ⟨_, rfl⟩
    have ht0j : t0 ≤ (j : ℕ) := by rw [ht0]; exact Nat.div_mul_le_self _ _
    have hjt0 : (j : ℕ) < t0 + I.d := by rw [ht0]; exact Nat.lt_div_mul_add hd
    have hper_lo : ∀ s : ℕ, s < t0 → s / I.d < (j : ℕ) / I.d := by
      intro s hs
      rw [Nat.div_lt_iff_lt_mul hd]
      rw [ht0] at hs
      exact hs
    have hper_in : ∀ s : ℕ, t0 ≤ s → s ≤ (j : ℕ) → s / I.d = (j : ℕ) / I.d := by
      intro s h1 h2
      apply le_antisymm (Nat.div_le_div_right h2)
      rw [Nat.le_div_iff_mul_le hd]
      rw [ht0] at h1
      exact h1
    have hag0 : assignment I β R1 t0 = assignment I β R2 t0 := by
      rcases agree_until I β R1 R2 i (period I j) hseed2 hgle2 t0 (by omega) with h | h
      · exfalso
        obtain ⟨t, htp, htl, _⟩ := h
        have h1 : (t : ℕ) / I.d + 1 = (j : ℕ) / I.d + 1 := congrArg Fin.val htp
        have h2 := hper_lo t htl
        omega
      · exact h
    have hagZ : ∀ s, s < t0 → assignment I β R2 (s + 1) s = assignment I β R1 (s + 1) s := by
      intro s hs
      rw [← assign_stab I β R2 t0 s hs, ← assign_stab I β R1 t0 s hs, hag0]
    have avail_iff : ∀ (Z : Seeds V n),
        (∀ s, s < t0 → assignment I β Z (s + 1) s = assignment I β R1 (s + 1) s) →
        ∀ m : ℕ, t0 ≤ m → m ≤ (j : ℕ) → ∀ v,
          (IsAvailable I (assignment I β Z m) v m ↔
            ((∀ s, s < t0 → assignment I β R1 (s + 1) s = some v → s + I.d ≤ m) ∧
             ∀ s, t0 ≤ s → s < m → assignment I β Z (s + 1) s ≠ some v)) := by
      intro Z hZ m hm1 hm2 v
      unfold IsAvailable
      constructor
      · intro h
        refine ⟨fun s hs hsv => h s (by omega) (by rw [assign_stab I β Z m s (by omega), hZ s hs]; exact hsv),
          fun s hs1 hs2 hsv => ?_⟩
        have := h s hs2 (by rw [assign_stab I β Z m s hs2]; exact hsv)
        omega
      · rintro ⟨hb, hc⟩ s hs hsv
        rw [assign_stab I β Z m s hs] at hsv
        by_cases hst : s < t0
        · rw [hZ s hst] at hsv
          exact hb s hst hsv
        · exact absurd hsv (hc s (by omega) hs)
    have av1 := avail_iff R1 (fun _ _ => rfl)
    have av2 := avail_iff R2 hagZ
    -- invariant
    have inv : ∀ m : ℕ, t0 ≤ m → m ≤ (j : ℕ) → ∀ v, v ≠ i → 0 < reducedPrice I β R1 v j →
        (∀ s, t0 ≤ s → s < m → assignment I β R1 (s + 1) s ≠ some v) →
        (∀ s, t0 ≤ s → s < m → assignment I β R2 (s + 1) s ≠ some v) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro _ v _ _ _ s hs1 hs2
        exact absurd hs2 (by omega)
      | succ m hm ih =>
        intro hmj v hv hpos hno1 s hs1 hs2 h2
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs2 with hsm | hsm
        · exact ih (by omega) v hv hpos (fun s' h1 h2' => hno1 s' h1 (by omega)) s hs1 hsm h2
        · rw [hsm] at h2
          clear hs1 hs2 hsm s
          have hmn : m < n := by omega
          have hmper : period I ⟨m, hmn⟩ = period I j := by
            apply Fin.ext
            show m / I.d + 1 = (j : ℕ) / I.d + 1
            rw [hper_in m hm (by omega)]
          obtain ⟨C2, hC2mem, hC2⟩ := choose_eq2 I β (assignment I β R2 m) ⟨m, hmn⟩
          obtain ⟨C1', hC1'mem, hC1'⟩ := choose_eq2 I β (assignment I β R1 m) ⟨m, hmn⟩
          have hch2 : leastArgmax C2 (fun w => reducedPrice I β R2 w ⟨m, hmn⟩) = some v := by
            rw [← hC2 R2, ← assign_step I β R2 m hmn]
            exact h2
          have hla2 := (la_some _ _ _).mp hch2
          obtain ⟨hvC2, hle2, hlt2⟩ := hla2
          have hvC2' := (hC2mem v).mp hvC2
          have hvav2 := (av2 m hm (by omega) v).mp hvC2'.2
          have hvav1 : IsAvailable I (assignment I β R1 m) v m :=
            (av1 m hm (by omega) v).mpr ⟨hvav2.1, fun s' h1 h2' => hno1 s' h1 (by omega)⟩
          have hvC1 : v ∈ C1' := (hC1'mem v).mpr ⟨hvC2'.1, hvav1⟩
          have hPv : 0 < reducedPrice I β R1 v ⟨m, hmn⟩ := by
            rw [hper R1 v ⟨m, hmn⟩ hmper]; exact hpos
          -- elements of C1' with positive price lie in C2
          have hinC2 : ∀ w ∈ C1', w ≠ i → 0 < reducedPrice I β R1 w ⟨m, hmn⟩ → w ∈ C2 := by
            intro w hw hwi hwpos
            have hw' := (hC1'mem w).mp hw
            have hwav1 := (av1 m hm (by omega) w).mp hw'.2
            have hwpos' : 0 < reducedPrice I β R1 w j := by
              rw [← hper R1 w ⟨m, hmn⟩ hmper]; exact hwpos
            have hno2 := ih (by omega) w hwi hwpos' hwav1.2
            have hwav2 : IsAvailable I (assignment I β R2 m) w m :=
              (av2 m hm (by omega) w).mpr ⟨hwav1.1, hno2⟩
            exact (hC2mem w).mpr ⟨hw'.1, hwav2⟩
          have hch1 : leastArgmax C1' (fun w => reducedPrice I β R1 w ⟨m, hmn⟩) = some v := by
            rw [la_some]
            refine ⟨hvC1, fun w hw => ?_, fun w hw hwv => ?_⟩
            · by_cases hwi : w = i
              · rw [hwi, hP1i _ hmper]; exact hPv.le
              · rcases (rp_nonneg I β hβ R1 w ⟨m, hmn⟩).lt_or_eq with hwpos | hw0
                · have h3 := hle2 w (hinC2 w hw hwi hwpos)
                  rw [hpe w _ hwi, hpe v _ hv] at h3
                  exact h3
                · rw [← hw0]; exact hPv.le
            · by_cases hwi : w = i
              · rw [hwi, hP1i _ hmper]; exact hPv
              · rcases (rp_nonneg I β hβ R1 w ⟨m, hmn⟩).lt_or_eq with hwpos | hw0
                · have h3 := hlt2 w (hinC2 w hw hwi hwpos) hwv
                  rw [hpe w _ hwi, hpe v _ hv] at h3
                  exact h3
                · rw [← hw0]; exact hPv
          apply hno1 m hm (by omega)
          rw [assign_step I β R1 m hmn, hC1' R1]
          exact hch1
    -- final comparison at j
    obtain ⟨C2j, hC2jmem, hC2j⟩ := choose_eq2 I β (assignment I β R2 j) j
    have hPR2 : PeriodicReranking I β R2 j = leastArgmax C2j (fun v => reducedPrice I β R2 v j) := by
      rw [← hC2j R2, PR_choose]
    have hb2 := dualBeta_nonneg I β hβ R2 j
    cases hla : leastArgmax C1 (fun v => reducedPrice I β R1 v j) with
    | none =>
      have : M = 0 := by rw [hM]; exact dualBeta_of I β R1 j _ (hPR1.trans hla)
      rw [this]; exact hb2
    | some u =>
      have hMu : M = reducedPrice I β R1 u j := by
        rw [hM]; exact dualBeta_of I β R1 j _ (hPR1.trans hla)
      rw [hMu]
      have hla' := (la_some _ _ _).mp hla
      by_cases hcase : u ≠ i ∧ 0 < reducedPrice I β R1 u j
      · obtain ⟨hui, hupos⟩ := hcase
        have hu' := (hC1mem u).mp hla'.1
        have huav1 := (av1 j ht0j le_rfl u).mp hu'.2
        have hno2 := inv j ht0j le_rfl u hui hupos huav1.2
        have huav2 : IsAvailable I (assignment I β R2 j) u j :=
          (av2 j ht0j le_rfl u).mpr ⟨huav1.1, hno2⟩
        have huC2 : u ∈ C2j := (hC2jmem u).mpr ⟨hu'.1, huav2⟩
        cases hla2 : leastArgmax C2j (fun v => reducedPrice I β R2 v j) with
        | none =>
          rw [la_none] at hla2
          exact absurd ⟨u, huC2⟩ hla2
        | some u2 =>
          have hb : dualBeta I β R2 j = reducedPrice I β R2 u2 j :=
            dualBeta_of I β R2 j _ (hPR2.trans hla2)
          rw [hb]
          have := ((la_some _ _ _).mp hla2).2.1 u huC2
          rw [hpe u j hui] at this
          exact this
      · have : reducedPrice I β R1 u j ≤ 0 := by
          by_cases hui : u = i
          · simp [hui, hP1i j rfl]
          · push_neg at hcase
            exact hcase hui
        linarith
  -- Part 1b
  · obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ I.r i * (1 - g β y)} :=
      ⟨_, rfl⟩
    rw [← hS]
    by_cases hSne : S.Nonempty
    · have hbdd : BddAbove S := ⟨1, fun y hy => by rw [hS] at hy; exact hy.1.2⟩
      have hc1 : sSup S ≤ 1 := csSup_le hSne (fun y hy => by rw [hS] at hy; exact hy.1.2)
      rcases lt_or_eq_of_le hc1 with hlt | heq
      · have hc0 : 0 ≤ sSup S := by
          obtain ⟨y, hy⟩ := hSne
          have := le_csSup hbdd hy
          rw [hS] at hy
          linarith [hy.1.1]
        have hsub : Set.Ioc (sSup S) 1 ⊆ {y : ℝ | I.r i * (1 - g β y) ≤ M} := by
          intro y hy
          by_contra hcon
          have hyS : y ∈ S := by
            rw [hS]
            exact ⟨⟨by linarith [hy.1], hy.2⟩, le_of_lt (not_le.mp hcon)⟩
          have := le_csSup hbdd hyS
          linarith [hy.1]
        have hcl : IsClosed {y : ℝ | I.r i * (1 - g β y) ≤ M} := isClosed_le hcont continuous_const
        have hclo := closure_minimal hsub hcl
        rw [closure_Ioc (ne_of_lt hlt)] at hclo
        exact hclo ⟨le_rfl, hc1⟩
      · rw [heq]
        unfold g
        simpa using hM0
    · rw [Set.not_nonempty_iff_eq_empty.mp hSne, Real.sSup_empty]
      by_contra hcon
      apply hSne
      refine ⟨0, ?_⟩
      rw [hS]
      exact ⟨⟨le_rfl, zero_le_one⟩, le_of_lt (not_le.mp hcon)⟩
  -- Part 2
  · intro y2
    have hsum_nn : 0 ≤ ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t := by
      apply Finset.sum_nonneg
      intro t _
      unfold dualAlpha
      split_ifs
      · exact mul_nonneg (I.r_nonneg i) (g_bounds β hβ _).1
      · exact le_rfl
    split_ifs with hlt
    swap
    · exact hsum_nn
    by_cases hr0 : I.r i = 0
    · rw [hr0, zero_mul]; exact hsum_nn
    have hrpos : 0 < I.r i := lt_of_le_of_ne (I.r_nonneg i) (Ne.symm hr0)
    -- a point of the set above y2
    have hSne : ({y : ℝ | y ∈ Set.Icc (0 : ℝ) 1 ∧ M ≤ I.r i * (1 - g β y)}).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty] at hlt
      exact absurd hlt (not_lt.mpr y2.2.1)
    obtain ⟨y, hyS, hy2y⟩ := exists_lt_of_lt_csSup hSne hlt
    have hhy : M < I.r i * (1 - g β y2) := by
      have hg : g β y2 < g β y := by
        unfold g
        exact Real.exp_lt_exp.mpr (by nlinarith)
      have := hyS.2
      nlinarith
    have hseed2 := hseed y2
    have hgle2 := hgle y2
    have hR2j2 := hR2j y2
    obtain ⟨R2, hR2⟩ : ∃ Z, Z = twoSeed I Y i j y1 y2 := ⟨_, rfl⟩
    rw [← hR2]
    rw [← hR2] at hseed2 hgle2 hR2j2
    have hpe : ∀ (v : V) (m : Fin n), v ≠ i →
        reducedPrice I β R2 v m = reducedPrice I β R1 v m := by
      intro v m hv
      rw [hR2]
      exact hprice_eq y2 v m hv
    have hP2i : reducedPrice I β R2 i j = I.r i * (1 - g β y2) := by
      unfold reducedPrice; rw [hR2j2]
    -- R2 matches i in period p(j) at some t ≤ j
    have hex : ∃ t : Fin n, period I t = period I j ∧ t ≤ j ∧
        PeriodicReranking I β R2 t = some i := by
      by_contra hno
      push_neg at hno
      have hnoR2 : ∀ s : ℕ, (hs : s < n) → s ≤ (j : ℕ) → period I ⟨s, hs⟩ = period I j →
          assignment I β R2 (s + 1) s ≠ some i := by
        intro s hs hsj hps hsi
        apply hno ⟨s, hs⟩ hps hsj
        rw [PR_eq I β R2 s (s + 1) hs (by omega)]
        exact hsi
      have hagree : ∀ m : ℕ, m ≤ (j : ℕ) → assignment I β R1 m = assignment I β R2 m := by
        intro m hm
        rcases agree_until I β R1 R2 i (period I j) hseed2 hgle2 m (by omega) with h | h
        · exfalso
          obtain ⟨t, htp, htl, hta⟩ := h
          exact hnoR2 t t.isLt (by omega) htp hta
        · exact h
      have hno1 : ∀ s : ℕ, (hs : s < n) → s < (j : ℕ) → period I ⟨s, hs⟩ = period I j →
          assignment I β R1 (s + 1) s ≠ some i := by
        intro s hs hsj hps hsi
        rw [assign_step I β R1 s hs] at hsi
        have h2 := (choice_cmp I β R1 R2 i (period I j) hseed2 hgle2 ⟨s, hs⟩
          (assignment I β R1 s)).2 hsi
        rw [hagree s hsj.le] at h2
        apply hnoR2 s hs hsj.le hps
        rw [assign_step I β R2 s hs]
        exact h2
      -- i is available at j in R1
      unfold availableInSubperiod at hi
      rw [mem_filter_any] at hi
      obtain ⟨_, ts, hpts, htsj, hts⟩ := hi
      unfold availableSet at hts
      rw [mem_filter_any] at hts
      have havs := hts.2
      have hvts : (ts : ℕ) / I.d + 1 = (j : ℕ) / I.d + 1 := congrArg Fin.val hpts
      have htsj' : (ts : ℕ) ≤ j := htsj
      have havj : IsAvailable I (assignment I β R1 j) i j := by
        intro s hs hsi
        by_cases hst : s < (ts : ℕ)
        · have : assignment I β R1 ts s = some i := by
            rw [assign_stab I β R1 ts s hst, ← assign_stab I β R1 j s hs]
            exact hsi
          have := havs s hst this
          omega
        · exfalso
          have hsn : s < n := by omega
          have hps : period I ⟨s, hsn⟩ = period I j := by
            apply Fin.ext
            show s / I.d + 1 = (j : ℕ) / I.d + 1
            have h1 : (ts : ℕ) / I.d ≤ s / I.d := Nat.div_le_div_right (by omega)
            have h2 : s / I.d ≤ (j : ℕ) / I.d := Nat.div_le_div_right (by omega)
            generalize s / I.d = a at h1 h2 ⊢
            generalize (ts : ℕ) / I.d = b at h1 hvts
            generalize (j : ℕ) / I.d = c at h2 hvts ⊢
            omega
          apply hno1 s hsn hs hps
          rw [← assign_stab I β R1 j s hs]
          exact hsi
      have hiC1 : i ∈ C1 := (hC1mem i).mpr ⟨hij, havj⟩
      have hch : leastArgmax C1 (fun v => reducedPrice I β R2 v j) = some i := by
        rw [la_some]
        refine ⟨hiC1, fun w hw => ?_, fun w hw hwi => ?_⟩
        · by_cases hwi : w = i
          · exact le_of_eq (by rw [hwi])
          · rw [hpe w j hwi, hP2i]
            have := hMmax w hw
            linarith
        · have hwi' : w ≠ i := ne_of_lt hwi
          rw [hpe w j hwi', hP2i]
          have := hMmax w hw
          linarith
      apply hno j rfl le_rfl
      rw [PR_choose, ← hagree j le_rfl, hC1 R2]
      exact hch
    obtain ⟨t, htp, htj, htPR⟩ := hex
    have hval : dualAlpha I β R2 i t = I.r i * g β y2 := by
      unfold dualAlpha
      rw [if_pos htPR, htp, hR2j2]
    have hmem : t ∈ window I j := by
      unfold window
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, htj, ?_⟩
      have hvt : (t : ℕ) / I.d + 1 = (j : ℕ) / I.d + 1 := congrArg Fin.val htp
      have h1 : (j : ℕ) < (j : ℕ) / I.d * I.d + I.d := Nat.lt_div_mul_add hd
      have h2 : (t : ℕ) / I.d * I.d ≤ (t : ℕ) := Nat.div_mul_le_self _ _
      have h3 : (t : ℕ) / I.d = (j : ℕ) / I.d := Nat.add_right_cancel hvt
      rw [h3] at h2
      generalize (j : ℕ) / I.d * I.d = A at h1 h2
      omega
    have hnn : ∀ t ∈ window I j, 0 ≤ dualAlpha I β R2 i t := by
      intro t _
      unfold dualAlpha
      split_ifs
      · exact mul_nonneg (I.r_nonneg i) (g_bounds β hβ _).1
      · exact le_rfl
    rw [← hval]
    exact Finset.single_le_sum hnn hmem

end Aux_RM


end ReusableMatching

open ReusableMatching in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (y1 : unitInterval) (hi : i ∈ availableInSubperiod I β (twoSeed I Y i j y1 1) j) :
    (∀ y2 : unitInterval,
      dualBeta I β (twoSeed I Y i j y1 1) j ≤ dualBeta I β (twoSeed I Y i j y1 y2) j) ∧
    I.r i * (1 - g β (criticalThreshold I β Y i j y1 j)) ≤
      dualBeta I β (twoSeed I Y i j y1 1) j ∧
    (∀ y2 : unitInterval,
      (if (y2 : ℝ) < criticalThreshold I β Y i j y1 j then I.r i * g β y2 else 0) ≤
        ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t) :=
  Aux_RM.lemma4_main I β hβ i j hij Y y1 hi
