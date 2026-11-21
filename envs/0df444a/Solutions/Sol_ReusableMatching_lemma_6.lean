-- Prove2me | solution 1 for ReusableMatching.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:42:37.839185+00:00
-- url     : https://prove2.me/submissions/97010280-ba13-41bd-9f0f-ada934f3dc31

import Mathlib
import Definitions.Def_ReusableMatching_PeriodicReranking
import Definitions.Def_ReusableMatching_twoSeed

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


end ReusableMatching

open ReusableMatching in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Y : Seeds V n)
    (z y2 : unitInterval) (tz : Fin n) (htz : period I tz = prevPeriod I j)
    (hmatch : PeriodicReranking I β (twoSeed I Y i j z y2) tz = some i) :
    ∀ y1 : unitInterval, y1 ≤ z →
      ∃ t : Fin n, period I t = prevPeriod I j ∧ t ≤ tz ∧
        PeriodicReranking I β (twoSeed I Y i j y1 y2) t = some i :=
  fun y1 hy => Aux_RM.lemma6_main I β hβ i j Y z y2 tz htz hmatch y1 hy
