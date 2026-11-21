-- Prove2me | solution 1 for ReusableMatching.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:16:15.800075+00:00
-- url     : https://prove2.me/submissions/e6a3b4c2-1c55-4bb5-8831-29417d47db85

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_twoSeed
import Definitions.Def_ReusableMatching_window

namespace ReusableMatching

open MeasureTheory

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

open MeasureTheory

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem PR_meas (I : OBMRRInstance V n) (β : ℝ) (t : Fin n) (w : Option V) :
    MeasurableSet {Y : Seeds V n | PeriodicReranking I β Y t = w} :=
  assign_meas I β n t w

theorem int_ite (I : OBMRRInstance V n) (β : ℝ) (i : V) (t : Fin n) (F : Seeds V n → ℝ)
    (hF : Measurable F) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ Y, |F Y| ≤ C) :
    Integrable (fun Y => if PeriodicReranking I β Y t = some i then F Y else 0)
      (seedMeasure V n) := by
  haveI : IsProbabilityMeasure (seedMeasure V n) := by
    unfold seedMeasure; infer_instance
  refine Integrable.of_bound (Measurable.ite (PR_meas I β t (some i)) hF measurable_const).aestronglyMeasurable C
    (ae_of_all _ (fun Y => ?_))
  split_ifs
  · rw [Real.norm_eq_abs]; exact hC Y
  · simpa using hC0

theorem rp_meas (I : OBMRRInstance V n) (β : ℝ) (v : V) (t : Fin n) :
    Measurable fun Y : Seeds V n => reducedPrice I β Y v t := by
  unfold reducedPrice
  exact (measurable_const.sub (g_meas β _)).const_mul (I.r v)

theorem alpha_meas (I : OBMRRInstance V n) (β : ℝ) (i : V) (t : Fin n) :
    Measurable fun Y : Seeds V n => dualAlpha I β Y i t := by
  unfold dualAlpha
  exact Measurable.ite (PR_meas I β t (some i)) ((g_meas β _).const_mul (I.r i)) measurable_const

theorem beta_sum (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (j : Fin n) :
    dualBeta I β Y j =
      ∑ v, (if PeriodicReranking I β Y j = some v then reducedPrice I β Y v j else 0) := by
  unfold dualBeta
  cases h : PeriodicReranking I β Y j with
  | none => simp
  | some v => simp

theorem beta_meas (I : OBMRRInstance V n) (β : ℝ) (j : Fin n) :
    Measurable fun Y : Seeds V n => dualBeta I β Y j := by
  have : (fun Y : Seeds V n => dualBeta I β Y j) = fun Y =>
      ∑ v, (if PeriodicReranking I β Y j = some v then reducedPrice I β Y v j else 0) :=
    funext fun Y => beta_sum I β Y j
  rw [this]
  apply Finset.measurable_sum
  intro v _
  exact Measurable.ite (PR_meas I β j (some v)) (rp_meas I β v j) measurable_const

theorem alpha_int (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (i : V) (t : Fin n) :
    Integrable (fun Y => dualAlpha I β Y i t) (seedMeasure V n) := by
  have := int_ite I β i t (fun Y => I.r i * g β (Y (i, period I t)))
    ((g_meas β _).const_mul (I.r i)) (I.r i) (I.r_nonneg i) (fun Y => by
      have hg := g_bounds β hβ (Y (i, period I t))
      have hr := I.r_nonneg i
      rw [abs_of_nonneg (mul_nonneg hr hg.1)]
      nlinarith)
  exact this

theorem beta_int (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (j : Fin n) :
    Integrable (fun Y => dualBeta I β Y j) (seedMeasure V n) := by
  have : (fun Y : Seeds V n => dualBeta I β Y j) = fun Y =>
      ∑ v, (if PeriodicReranking I β Y j = some v then reducedPrice I β Y v j else 0) :=
    funext fun Y => beta_sum I β Y j
  rw [this]
  apply integrable_finsetSum
  intro v _
  refine int_ite I β v j (fun Y => reducedPrice I β Y v j) (rp_meas I β v j) (I.r v)
    (I.r_nonneg v) ?_
  intro Y
  unfold reducedPrice
  have hg := g_bounds β hβ (Y (v, period I j))
  have hr := I.r_nonneg v
  rw [abs_of_nonneg (mul_nonneg hr (by linarith))]
  nlinarith

end Aux_RM

namespace Aux_RM

open MeasureTheory

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem ofReal_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases hint : Integrable f μ
  · rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf)]
  · rw [integral_undef hint, ENNReal.ofReal_zero]
    exact zero_le

theorem lemma3_main (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n)
    (Γ : ℝ) (hΓ : 0 < Γ)
    (h3 : ∀ Y : Seeds V n, Γ * I.r i ≤
      ∫ y1 : unitInterval, ∫ y2 : unitInterval,
        (dualBeta I β (twoSeed I Y i j y1 y2) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t)) :
    Γ * I.r i ≤
      ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) +
        ∑ t ∈ window I j, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n) := by
  haveI : IsProbabilityMeasure (seedMeasure V n) := by
    unfold seedMeasure; infer_instance
  obtain ⟨F, hF⟩ : ∃ F : Seeds V n → ℝ, F = fun Y =>
      dualBeta I β Y j + ∑ t ∈ window I j, dualAlpha I β Y i t := ⟨_, rfl⟩
  have hFY : ∀ Y, F Y = dualBeta I β Y j + ∑ t ∈ window I j, dualAlpha I β Y i t := by
    intro Y; rw [hF]
  have hα_nn : ∀ Y t, 0 ≤ dualAlpha I β Y i t := by
    intro Y t
    unfold dualAlpha
    split_ifs
    · exact mul_nonneg (I.r_nonneg i) (g_bounds β hβ _).1
    · exact le_rfl
  have hF_nn : ∀ Y, 0 ≤ F Y := by
    intro Y
    rw [hFY]
    exact add_nonneg (dualBeta_nonneg I β hβ Y j)
      (Finset.sum_nonneg (fun t _ => hα_nn Y t))
  have hF_meas : Measurable F := by
    rw [hF]
    exact (beta_meas I β j).add (Finset.measurable_sum _ (fun t _ => alpha_meas I β i t))
  have hαsum_int : Integrable (fun Y => ∑ t ∈ window I j, dualAlpha I β Y i t) (seedMeasure V n) :=
    integrable_finsetSum _ (fun t _ => alpha_int I β hβ i t)
  have hF_int : Integrable F (seedMeasure V n) := by
    rw [hF]
    exact (beta_int I β hβ j).add hαsum_int
  -- rewrite the right-hand side as ∫ F
  have hR : ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) +
      ∑ t ∈ window I j, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n) =
      ∫ Y, F Y ∂(seedMeasure V n) := by
    have e1 : ∑ t ∈ window I j, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n) =
        ∫ Y, ∑ t ∈ window I j, dualAlpha I β Y i t ∂(seedMeasure V n) :=
      (integral_finsetSum _ (fun t _ => alpha_int I β hβ i t)).symm
    rw [e1, ← integral_add (beta_int I β hβ j) hαsum_int, hF]
  rw [hR]
  -- pointwise lower bound for the inner double integral
  have hq : (i, prevPeriod I j) ∉ ({(i, period I j)} : Finset (V × Fin (n + 1))) := by
    rw [Finset.mem_singleton]
    exact pp_ne I i j
  have hg_meas : Measurable fun Y : Seeds V n => ENNReal.ofReal (F Y) :=
    ENNReal.measurable_ofReal.comp hF_meas
  have hinner : ∀ x : Seeds V n, ENNReal.ofReal (Γ * I.r i) ≤
      ∫⁻ y1 : unitInterval, ∫⁻ y2 : unitInterval,
        ENNReal.ofReal (F (twoSeed I x i j y1 y2)) := by
    intro x
    have hx := h3 x
    have hG_nn : ∀ y1 : unitInterval, 0 ≤ ∫ y2 : unitInterval, F (twoSeed I x i j y1 y2) :=
      fun y1 => integral_nonneg (fun y2 => hF_nn _)
    calc ENNReal.ofReal (Γ * I.r i)
        ≤ ENNReal.ofReal (∫ y1 : unitInterval, ∫ y2 : unitInterval, F (twoSeed I x i j y1 y2)) := by
          apply ENNReal.ofReal_le_ofReal
          simp only [hFY]
          exact hx
      _ ≤ ∫⁻ y1 : unitInterval, ENNReal.ofReal (∫ y2 : unitInterval, F (twoSeed I x i j y1 y2)) :=
          ofReal_int_le _ _ hG_nn
      _ ≤ ∫⁻ y1 : unitInterval, ∫⁻ y2 : unitInterval, ENNReal.ofReal (F (twoSeed I x i j y1 y2)) :=
          lintegral_mono (fun y1 => ofReal_int_le _ _ (fun y2 => hF_nn _))
  have key : ∫⁻ _Y, ENNReal.ofReal (Γ * I.r i) ∂(seedMeasure V n) ≤
      ∫⁻ Y, ENNReal.ofReal (F Y) ∂(seedMeasure V n) := by
    unfold seedMeasure
    refine lintegral_le_of_lmarginal_le
      ({(i, prevPeriod I j), (i, period I j)} : Finset (V × Fin (n + 1)))
      measurable_const hg_meas (Pi.le_def.mpr (fun x => ?_))
    have hL : lmarginal (fun _ => (volume : Measure unitInterval))
        ({(i, prevPeriod I j), (i, period I j)} : Finset (V × Fin (n + 1)))
        (fun _ => ENNReal.ofReal (Γ * I.r i)) x = ENNReal.ofReal (Γ * I.r i) := by
      rw [lmarginal_insert _ measurable_const hq x]
      simp [lmarginal_singleton]
    have hRR : lmarginal (fun _ => (volume : Measure unitInterval))
        ({(i, prevPeriod I j), (i, period I j)} : Finset (V × Fin (n + 1)))
        (fun Y => ENNReal.ofReal (F Y)) x =
        ∫⁻ y1 : unitInterval, ∫⁻ y2 : unitInterval,
          ENNReal.ofReal (F (twoSeed I x i j y1 y2)) := by
      rw [lmarginal_insert _ hg_meas hq x]
      simp only [lmarginal_singleton]
      rfl
    rw [hL, hRR]
    exact hinner x
  rw [lintegral_const, measure_univ, mul_one,
    ← ofReal_integral_eq_lintegral_ofReal hF_int (ae_of_all _ hF_nn)] at key
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hF_nn)).mp key

end Aux_RM


end ReusableMatching

open ReusableMatching MeasureTheory in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) (i : V) (j : Fin n) (hij : (i, j) ∈ I.E) (Γ : ℝ) (hΓ : 0 < Γ)
    (h3 : ∀ Y : Seeds V n, Γ * I.r i ≤
      ∫ y1 : unitInterval, ∫ y2 : unitInterval,
        (dualBeta I β (twoSeed I Y i j y1 y2) j +
          ∑ t ∈ window I j, dualAlpha I β (twoSeed I Y i j y1 y2) i t)) :
    Γ * I.r i ≤
      ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) +
        ∑ t ∈ window I j, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n) :=
  Aux_RM.lemma3_main I β hβ i j Γ hΓ h3
