-- Prove2me | solution 1 for ReusableMatching.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:36:38.397676+00:00
-- url     : https://prove2.me/submissions/92894746-fa33-47e9-baec-80a9b4725234

import Mathlib
import Definitions.Def_ReusableMatching_dualBeta
import Definitions.Def_ReusableMatching_dualAlpha
import Definitions.Def_ReusableMatching_reward

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

open MeasureTheory

variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}

theorem g_bounds (β : ℝ) (hβ : 0 < β) (y : unitInterval) : 0 ≤ g β y ∧ g β y ≤ 1 := by
  unfold g
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_le_one_iff]
  have := y.2.2
  have h1 : (y : ℝ) - 1 ≤ 0 := by linarith
  nlinarith

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

theorem lemma2_main (I : OBMRRInstance V n) (β : ℝ) (hβ : 0 < β) :
    (∑ i, ∑ t, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n)) +
        ∑ j, ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) ≤
      ∫ Y, reward I β Y ∂(seedMeasure V n) := by
  -- pointwise identity
  have hpt : ∀ (Y : Seeds V n) (t : Fin n),
      ∑ i, dualAlpha I β Y i t + dualBeta I β Y t = (PeriodicReranking I β Y t).elim 0 I.r := by
    intro Y t
    unfold dualAlpha dualBeta
    cases h : PeriodicReranking I β Y t with
    | none => simp
    | some v =>
      first
        | (simp [reducedPrice]; ring1)
        | simp [reducedPrice]
  have hsum : ∀ Y : Seeds V n,
      ∑ i, ∑ t, dualAlpha I β Y i t + ∑ j, dualBeta I β Y j = reward I β Y := by
    intro Y
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    unfold reward
    exact Finset.sum_congr rfl (fun t _ => hpt Y t)
  -- integrability
  have hαint : ∀ i t, Integrable (fun Y => dualAlpha I β Y i t) (seedMeasure V n) := by
    intro i t
    have := int_ite I β i t (fun Y => I.r i * g β (Y (i, period I t)))
      ((g_meas β _).const_mul (I.r i)) (I.r i) (I.r_nonneg i) (fun Y => by
        have hg := g_bounds β hβ (Y (i, period I t))
        have hr := I.r_nonneg i
        rw [abs_of_nonneg (mul_nonneg hr hg.1)]
        nlinarith)
    exact this
  have hβeq : ∀ (Y : Seeds V n) (j : Fin n), dualBeta I β Y j =
      ∑ i, (if PeriodicReranking I β Y j = some i then reducedPrice I β Y i j else 0) := by
    intro Y j
    unfold dualBeta
    cases h : PeriodicReranking I β Y j with
    | none => simp
    | some v => simp
  have hβint : ∀ j, Integrable (fun Y => dualBeta I β Y j) (seedMeasure V n) := by
    intro j
    have : (fun Y => dualBeta I β Y j) =
        fun Y => ∑ i, (if PeriodicReranking I β Y j = some i then reducedPrice I β Y i j else 0) := by
      funext Y; exact hβeq Y j
    rw [this]
    apply integrable_finsetSum
    intro i _
    refine int_ite I β i j (fun Y => reducedPrice I β Y i j) ?_ (I.r i) (I.r_nonneg i) ?_
    · unfold reducedPrice
      exact (measurable_const.sub (g_meas β _)).const_mul (I.r i)
    · intro Y
      unfold reducedPrice
      have hg := g_bounds β hβ (Y (i, period I j))
      have hr := I.r_nonneg i
      rw [abs_of_nonneg (mul_nonneg hr (by linarith))]
      nlinarith
  have e1 : ∀ i, ∑ t, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n) =
      ∫ Y, ∑ t, dualAlpha I β Y i t ∂(seedMeasure V n) :=
    fun i => (integral_finsetSum _ (fun t _ => hαint i t)).symm
  have hαsum : ∀ i, Integrable (fun Y => ∑ t, dualAlpha I β Y i t) (seedMeasure V n) :=
    fun i => integrable_finsetSum _ (fun t _ => hαint i t)
  have e2 : ∑ i, ∫ Y, ∑ t, dualAlpha I β Y i t ∂(seedMeasure V n) =
      ∫ Y, ∑ i, ∑ t, dualAlpha I β Y i t ∂(seedMeasure V n) :=
    (integral_finsetSum _ (fun i _ => hαsum i)).symm
  have e3 : ∑ j, ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) =
      ∫ Y, ∑ j, dualBeta I β Y j ∂(seedMeasure V n) :=
    (integral_finsetSum _ (fun j _ => hβint j)).symm
  have i1 : Integrable (fun Y => ∑ i, ∑ t, dualAlpha I β Y i t) (seedMeasure V n) :=
    integrable_finsetSum _ (fun i _ => hαsum i)
  have i2 : Integrable (fun Y => ∑ j, dualBeta I β Y j) (seedMeasure V n) :=
    integrable_finsetSum _ (fun j _ => hβint j)
  rw [Finset.sum_congr rfl (fun i _ => e1 i), e2, e3, ← integral_add i1 i2]
  apply le_of_eq
  congr 1
  funext Y
  exact hsum Y

end Aux_RM


end ReusableMatching

open ReusableMatching MeasureTheory in
theorem solution {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ} (I : OBMRRInstance V n)
    (β : ℝ) (hβ : 0 < β) :
    (∑ i, ∑ t, ∫ Y, dualAlpha I β Y i t ∂(seedMeasure V n)) +
        ∑ j, ∫ Y, dualBeta I β Y j ∂(seedMeasure V n) ≤
      ∫ Y, reward I β Y ∂(seedMeasure V n) :=
  Aux_RM.lemma2_main I β hβ
