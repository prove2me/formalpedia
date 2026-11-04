-- Prove2me | solution 1 for QueueBandit.EarlyLower.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:25:11.977396+00:00
-- url     : https://prove2.me/submissions/275a4242-ba19-4855-997b-89223ce07f60

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics

open QueueBandit.LateLower QueueBandit.EarlyLower MeasureTheory ProbabilityTheory

namespace QB3L22

variable {U K : ℕ}

/-- Replace coordinate `s` of a seed sequence by a fresh seed. -/
noncomputable def upd (s : ℕ) (p : (ℕ → Seed U K) × Seed U K) : ℕ → Seed U K :=
  Function.update p.1 s p.2

lemma measurable_upd (s : ℕ) : Measurable (upd (U := U) (K := K) s) := by
  rw [measurable_pi_iff]
  intro i
  by_cases h : i = s
  · subst h; simp only [upd, Function.update_self]; exact measurable_snd
  · simp only [upd, Function.update_of_ne h]; exact (measurable_pi_apply i).comp measurable_fst

lemma upd_mp (s : ℕ) : MeasurePreserving (upd (U := U) (K := K) s)
    ((seedMeasure U K).prod (seedLaw U K)) (seedMeasure U K) := by
  refine ⟨measurable_upd s, ?_⟩
  unfold seedMeasure
  apply Measure.eq_infinitePi
  intro I t ht
  classical
  rw [Measure.map_apply (measurable_upd s) (MeasurableSet.pi I.countable_toSet fun i _ => ht i)]
  set T' : ℕ → Set (Seed U K) := fun i => if i = s then Set.univ else t i with hT'
  have hset : upd s ⁻¹' (Set.pi (↑I) t) =
      (Set.pi (↑I) T') ×ˢ (if s ∈ I then t s else Set.univ) := by
    ext ⟨ω, x⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, upd, hT']
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · by_cases his : i = s
        · simp [his]
        · have := h i hi; rw [Function.update_of_ne his] at this; simp [his, this]
      · split_ifs with hs
        · have := h s hs; rwa [Function.update_self] at this
        · trivial
    · rintro ⟨h1, h2⟩ i hi
      by_cases his : i = s
      · subst his; rw [Function.update_self]; simpa [hi] using h2
      · rw [Function.update_of_ne his]; simpa [his] using h1 i hi
  rw [hset, Measure.prod_prod, Measure.infinitePi_pi (μ := fun _ : ℕ => seedLaw U K) (fun i _ => by
    simp only [hT']; split_ifs; exacts [MeasurableSet.univ, ht i])]
  by_cases hs : s ∈ I
  · rw [if_pos hs, ← Finset.mul_prod_erase I _ hs, ← Finset.mul_prod_erase I (fun i => seedLaw U K (t i)) hs]
    simp only [hT', if_pos rfl, measure_univ, one_mul]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  · rw [if_neg hs, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [hT']; rw [if_neg (fun h : i = s => hs (h ▸ hi))]

/-- The system-level replacement map `((q, ω), x) ↦ (q, update ω s x)`. -/
noncomputable def updS (s : ℕ) (p : ((Fin U → ℕ) × (ℕ → Seed U K)) × Seed U K) :
    (Fin U → ℕ) × (ℕ → Seed U K) :=
  (p.1.1, upd s (p.1.2, p.2))

lemma updS_mp (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (s : ℕ) :
    MeasurePreserving (updS (U := U) (K := K) s)
      ((sysMeasure (K := K) ν).prod (seedLaw U K)) (sysMeasure (K := K) ν) := by
  unfold sysMeasure
  have h1 := measurePreserving_prodAssoc ν (seedMeasure U K) (seedLaw U K)
  have h2 := (MeasurePreserving.id ν).prod (upd_mp (U := U) (K := K) s)
  have := h2.comp h1
  convert this using 1
  funext p; rfl

instance sys_prob (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (sysMeasure (K := K) ν) := by
  unfold sysMeasure; infer_instance

/-- Integrating out a fresh seed. -/
lemma integral_fresh (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (s : ℕ)
    (Γ : (Fin U → ℕ) × (ℕ → Seed U K) → Seed U K → ℝ)
    (hm : Measurable (Function.uncurry Γ)) (C : ℝ) (hb : ∀ z x, |Γ z x| ≤ C)
    (hinv : ∀ z x y, Γ (z.1, Function.update z.2 s y) x = Γ z x) :
    ∫ z, Γ z (z.2 s) ∂(sysMeasure (K := K) ν) =
      ∫ z, (∫ x, Γ z x ∂(seedLaw U K)) ∂(sysMeasure (K := K) ν) := by
  have hmp := updS_mp (K := K) ν s
  have hG : Measurable (fun z : (Fin U → ℕ) × (ℕ → Seed U K) => Γ z (z.2 s)) := by
    have : (fun z : (Fin U → ℕ) × (ℕ → Seed U K) => Γ z (z.2 s)) =
        Function.uncurry Γ ∘ (fun z => (z, z.2 s)) := rfl
    rw [this]
    exact hm.comp (measurable_id.prodMk ((measurable_pi_apply s).comp measurable_snd))
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (hmp.map_eq ▸ hG.aestronglyMeasurable)]
  have hpt : ∀ p : ((Fin U → ℕ) × (ℕ → Seed U K)) × Seed U K,
      Γ (updS s p) ((updS s p).2 s) = Γ p.1 p.2 := by
    rintro ⟨⟨q, ω⟩, x⟩
    simp only [updS, upd, Function.update_self]
    exact hinv (q, ω) x x
  simp_rw [hpt]
  have hint : Integrable (Function.uncurry Γ) ((sysMeasure (K := K) ν).prod (seedLaw U K)) :=
    Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb p.1 p.2)
  exact integral_prod (Function.uncurry Γ) hint

/-! ## Coin flips from uniform seeds -/

lemma one_coin {α : Type*} [MeasurableSpace α] (m : Measure α) [IsProbabilityMeasure m]
    (S : Set α) [DecidablePred (· ∈ S)] (hS : MeasurableSet S) (ψ : ℕ → ℝ) :
    ∫ x, ψ (if x ∈ S then 1 else 0) ∂m = (1 - m.real S) * ψ 0 + m.real S * ψ 1 := by
  have hpt : ∀ x, ψ (if x ∈ S then 1 else 0) = ψ 0 + (ψ 1 - ψ 0) * S.indicator 1 x := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [hpt]
  have hi : Integrable (fun x => (ψ 1 - ψ 0) * S.indicator (1 : α → ℝ) x) m :=
    ((integrable_indicator_iff hS).2 (integrable_const (1 : ℝ)).integrableOn).const_mul _
  rw [integral_add (integrable_const _) hi, integral_const, integral_const_mul,
    integral_indicator_one hS]
  simp; ring

lemma one_coin' {α : Type*} [MeasurableSpace α] (m : Measure α) [IsProbabilityMeasure m]
    (q : α → Prop) [DecidablePred q] (hq : MeasurableSet {x | q x}) (ψ : ℕ → ℝ) :
    ∫ x, ψ (if q x then 1 else 0) ∂m = (1 - m.real {x | q x}) * ψ 0 + m.real {x | q x} * ψ 1 := by
  have := one_coin m {x | q x} hq ψ
  simpa using this

lemma vol_I_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (volume : Measure unitInterval) {y : unitInterval | (y : ℝ) ≤ c} = ENNReal.ofReal c := by
  have : {y : unitInterval | (y : ℝ) ≤ c} = Set.Iic ⟨c, hc0, hc1⟩ := by
    ext y; simp [← Subtype.coe_le_coe]
  rw [this, unitInterval.volume_Iic]

lemma measurableSet_I_le {β : Type*} [MeasurableSpace β] (g : β → unitInterval) (hg : Measurable g)
    (c : ℝ) : MeasurableSet {y : β | ((g y : unitInterval) : ℝ) ≤ c} :=
  measurableSet_le (measurable_subtype_coe.comp hg) measurable_const

/-- The arrival set of queue `u` in a seed. -/
def arrSet (lam : Fin U → ℝ) (u : Fin U) : Set (Seed U K) := {x | ((x.1 u : unitInterval) : ℝ) ≤ lam u}

/-- The service set of link `(u, k)` in a seed. -/
def offSet (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) : Set (Seed U K) :=
  {x | ((x.2.1 u k : unitInterval) : ℝ) ≤ mu u k}

lemma measurableSet_arrSet (lam : Fin U → ℝ) (u : Fin U) :
    MeasurableSet (arrSet (K := K) lam u) :=
  measurableSet_I_le _ ((measurable_pi_apply u).comp measurable_fst) _

lemma measurableSet_offSet (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) :
    MeasurableSet (offSet mu u k) :=
  measurableSet_I_le _ ((measurable_pi_apply k).comp ((measurable_pi_apply u).comp
    (measurable_fst.comp measurable_snd))) _

lemma vol_pi_eval {ι β : Type*} [Fintype ι] [MeasureSpace β]
    [IsProbabilityMeasure (volume : Measure β)] (i : ι) (B : Set β) (hB : MeasurableSet B) :
    (volume : Measure (ι → β)) {f | f i ∈ B} = volume B := by
  rw [volume_pi]
  exact (measurePreserving_eval (fun _ : ι => (volume : Measure β)) i).measure_preimage
    hB.nullMeasurableSet

lemma seedLaw_arrSet (lam : Fin U → ℝ) (u : Fin U) (h0 : 0 ≤ lam u) (h1 : lam u ≤ 1) :
    (seedLaw U K).real (arrSet lam u) = lam u := by
  have hset : arrSet (K := K) lam u =
      {f : Fin U → unitInterval | f u ∈ {y : unitInterval | (y : ℝ) ≤ lam u}} ×ˢ Set.univ := by
    ext x; simp [arrSet]
  rw [measureReal_def, hset]
  unfold seedLaw
  rw [show (volume : Measure (Seed U K)) = (volume : Measure (Fin U → unitInterval)).prod volume
    from rfl, Measure.prod_prod, measure_univ, mul_one,
    vol_pi_eval u {y : unitInterval | (y : ℝ) ≤ lam u}
      (measurableSet_le measurable_subtype_coe measurable_const), vol_I_le _ h0 h1,
    ENNReal.toReal_ofReal h0]

lemma seedLaw_offSet (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (h0 : 0 ≤ mu u k)
    (h1 : mu u k ≤ 1) : (seedLaw U K).real (offSet mu u k) = mu u k := by
  have hset : offSet mu u k = (Set.univ : Set (Fin U → unitInterval)) ×ˢ
      ({g : Fin U → Fin K → unitInterval | g u ∈ {f : Fin K → unitInterval |
        f k ∈ {y : unitInterval | (y : ℝ) ≤ mu u k}}} ×ˢ (Set.univ : Set unitInterval)) := by
    ext x; simp [offSet]
  rw [measureReal_def, hset]
  unfold seedLaw
  rw [show (volume : Measure (Seed U K)) = (volume : Measure (Fin U → unitInterval)).prod
    ((volume : Measure (Fin U → Fin K → unitInterval)).prod volume) from rfl,
    Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, one_mul, mul_one,
    vol_pi_eval u {f : Fin K → unitInterval | f k ∈ {y : unitInterval | (y : ℝ) ≤ mu u k}}
      (measurableSet_I_le (fun f : Fin K → unitInterval => f k) (measurable_pi_apply k) _),
    vol_pi_eval k {y : unitInterval | (y : ℝ) ≤ mu u k}
      (measurableSet_le measurable_subtype_coe measurable_const), vol_I_le _ h0 h1,
    ENNReal.toReal_ofReal h0]

/-! ## Measurability of the schedule (as in the Corollary 20 reduction) -/

lemma meas_seed_coord (s : ℕ) : Measurable (fun ω : ℕ → Seed U K => ω s) := measurable_pi_apply s

lemma meas_offered_set (mu : Fin U → Fin K → ℝ) (s : ℕ) (u : Fin U) (k : Fin K) :
    MeasurableSet {ω : ℕ → Seed U K | offered mu ω s u k = 1} := by
  have : {ω : ℕ → Seed U K | offered mu ω s u k = 1} =
      (fun ω : ℕ → Seed U K => (((ω s).2.1 u k : unitInterval) : ℝ)) ⁻¹' Set.Iic (mu u k) := by
    ext ω; simp only [offered, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    split_ifs with h <;> simp [h]
  rw [this]
  apply measurableSet_Iic.preimage
  exact measurable_subtype_coe.comp ((measurable_pi_apply k).comp
    ((measurable_pi_apply u).comp (measurable_fst.comp (measurable_snd.comp (meas_seed_coord s)))))

lemma meas_act_set (π : Policy U K) (n : ℕ) (h : History U K n) (m : Matching U K) (s : ℕ) :
    MeasurableSet {ω : ℕ → Seed U K | π.act n h (ω s).2.2 = m} :=
  (π.measurableSet_act n h m).preimage (measurable_snd.comp (measurable_snd.comp (meas_seed_coord s)))

lemma hist_fiber (π : Policy U K) (mu : Fin U → Fin K → ℝ) :
    ∀ (n : ℕ) (h : History U K n), MeasurableSet {ω : ℕ → Seed U K | hist π mu ω n = h}
  | 0, h => by
    have : {ω : ℕ → Seed U K | hist π mu ω 0 = h} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      funext i; exact i.elim0
    rw [this]; exact MeasurableSet.univ
  | n + 1, h => by
    have hset : {ω : ℕ → Seed U K | hist π mu ω (n + 1) = h} =
        {ω | hist π mu ω n = Fin.init h} ∩ ({ω | π.act n (Fin.init h) (ω (n + 1)).2.2 =
          (h (Fin.last n)).1} ∩ ⋂ u : Fin U, {ω | decide (offered mu ω (n + 1) u
            ((h (Fin.last n)).1 u) = 1) = (h (Fin.last n)).2 u}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · intro hh
        subst hh
        simp only [hist, Fin.init_snoc, Fin.snoc_last, and_self, implies_true]
      · rintro ⟨h1, h2, h3⟩
        simp only [hist]
        rw [h1]
        conv_rhs => rw [← Fin.snoc_init_self h]
        congr 1
        rw [h2]
        exact Prod.ext rfl (funext fun u => h3 u)
    rw [hset]
    refine (hist_fiber π mu n _).inter ((meas_act_set π n _ _ _).inter ?_)
    refine MeasurableSet.iInter fun u => ?_
    cases hb : (h (Fin.last n)).2 u
    · have : {ω : ℕ → Seed U K | decide (offered mu ω (n + 1) u ((h (Fin.last n)).1 u) = 1) =
          false} = {ω | offered mu ω (n + 1) u ((h (Fin.last n)).1 u) = 1}ᶜ := by
        ext ω; simp
      rw [this]; exact (meas_offered_set mu _ _ _).compl
    · have : {ω : ℕ → Seed U K | decide (offered mu ω (n + 1) u ((h (Fin.last n)).1 u) = 1) =
          true} = {ω | offered mu ω (n + 1) u ((h (Fin.last n)).1 u) = 1} := by
        ext ω; simp
      rw [this]; exact meas_offered_set mu _ _ _

lemma sched_fiber (π : Policy U K) (mu : Fin U → Fin K → ℝ) (s : ℕ) (u : Fin U) (k : Fin K) :
    MeasurableSet {ω : ℕ → Seed U K | sched π mu ω s u = k} := by
  have : {ω : ℕ → Seed U K | sched π mu ω s u = k} =
      ⋃ h : History U K (s - 1), ⋃ m ∈ {m : Matching U K | m u = k},
        ({ω | hist π mu ω (s - 1) = h} ∩ {ω | π.act (s - 1) h (ω s).2.2 = m}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop, sched]
    constructor
    · intro hk; exact ⟨_, _, hk, rfl, rfl⟩
    · rintro ⟨h, m, hm, rfl, rfl⟩; exact hm
  rw [this]
  refine MeasurableSet.iUnion fun h => ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun m _ => ?_
  exact (hist_fiber π mu _ h).inter (meas_act_set π _ h m s)

lemma count_eq (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (u : Fin U)
    (k : Fin K) (t : ℕ) :
    count π mu ω u k t = ∑ s ∈ Finset.Icc 1 t, if sched π mu ω s u = k then 1 else 0 := by
  unfold count
  rw [Finset.card_filter]

lemma count_integrable (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K)
    (t : ℕ) : Integrable (fun ω => (count π mu ω u k t : ℝ)) (seedMeasure U K) := by
  have hmeas : Measurable (fun ω => (count π mu ω u k t : ℝ)) := by
    simp_rw [count_eq, Nat.cast_sum]
    refine Finset.measurable_sum _ fun s _ => ?_
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Measurable.ite (sched_fiber π mu s u k) measurable_const measurable_const
  refine Integrable.of_bound hmeas.aestronglyMeasurable (t : ℝ) (Filter.Eventually.of_forall ?_)
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have : count π mu ω u k t ≤ t := by
    unfold count
    calc _ ≤ (Finset.Icc 1 t).card := Finset.card_filter_le _ _
      _ = t := by simp
  exact_mod_cast this

lemma meas_count (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K)
    (t : ℕ) : Measurable (fun ω => (count π mu ω u k t : ℝ)) := by
  simp_rw [count_eq, Nat.cast_sum]
  refine Finset.measurable_sum _ fun s _ => ?_
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact Measurable.ite (sched_fiber π mu s u k) measurable_const measurable_const

lemma expCount_nonneg (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U)
    (k : Fin K) (t : ℕ) : 0 ≤ expCount π mu u k t :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

/-! ## Bounded measurable integrands -/

lemma int_of_bdd {α : Type*} [MeasurableSpace α] (m : Measure α) [IsFiniteMeasure m]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma int_ind_eq {α : Type*} [MeasurableSpace α] (m : Measure α) (S : Set α)
    [DecidablePred (· ∈ S)] (hS : MeasurableSet S) :
    ∫ x, (if x ∈ S then (1 : ℝ) else 0) ∂m = m.real S := by
  have : (fun x => if x ∈ S then (1 : ℝ) else 0) = S.indicator 1 := by
    ext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [this, integral_indicator_one hS]

lemma int_ind_eq' {α : Type*} [MeasurableSpace α] (m : Measure α) (q : α → Prop)
    [DecidablePred q] (hq : MeasurableSet {x | q x}) :
    ∫ x, (if q x then (1 : ℝ) else 0) ∂m = m.real {x | q x} := by
  have : (fun x => if q x then (1 : ℝ) else 0) = {x | q x}.indicator 1 := by
    ext x; by_cases hx : q x <;> simp [hx]
  rw [this, integral_indicator_one hq]

/-! ## Two independent coins in one seed -/

/-- Arrival indicator of queue `u` in a seed. -/
noncomputable def aS (lam : Fin U → ℝ) (u : Fin U) (x : Seed U K) : ℕ :=
  if ((x.1 u : unitInterval) : ℝ) ≤ lam u then 1 else 0

/-- Service indicator of link `(u, k)` in a seed. -/
noncomputable def bS (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (x : Seed U K) : ℕ :=
  if ((x.2.1 u k : unitInterval) : ℝ) ≤ mu u k then 1 else 0

lemma aS_le (lam : Fin U → ℝ) (u : Fin U) (x : Seed U K) : aS lam u x ≤ 1 := by
  unfold aS; split_ifs <;> omega

lemma bS_le (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (x : Seed U K) : bS mu u k x ≤ 1 := by
  unfold bS; split_ifs <;> omega

lemma meas_aS (lam : Fin U → ℝ) (u : Fin U) : Measurable (aS (K := K) lam u) := by
  unfold aS; exact Measurable.ite (measurableSet_arrSet lam u) measurable_const measurable_const

lemma meas_bS (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) : Measurable (bS mu u k) := by
  unfold bS; exact Measurable.ite (measurableSet_offSet mu u k) measurable_const measurable_const

lemma arrival_eq (lam : Fin U → ℝ) (ω : ℕ → Seed U K) (t : ℕ) (u : Fin U) :
    arrival lam ω t u = aS lam u (ω t) := rfl

lemma offered_eq (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (t : ℕ) (u : Fin U) (k : Fin K) :
    offered mu ω t u k = bS mu u k (ω t) := rfl

lemma seed_split (F : (Fin U → unitInterval) → ℝ) (H : ((Fin U → Fin K → unitInterval) × unitInterval) → ℝ) :
    ∫ x, F x.1 * H x.2 ∂(seedLaw U K) = (∫ y, F y) * ∫ y, H y := by
  unfold seedLaw
  exact integral_prod_mul (μ := (volume : Measure (Fin U → unitInterval))) F H

lemma volA (lam : Fin U → ℝ) (u : Fin U) (h0 : 0 ≤ lam u) (h1 : lam u ≤ 1) :
    (volume : Measure (Fin U → unitInterval)).real {f | ((f u : unitInterval) : ℝ) ≤ lam u} = lam u := by
  rw [measureReal_def, show {f : Fin U → unitInterval | ((f u : unitInterval) : ℝ) ≤ lam u} =
      {f | f u ∈ {y : unitInterval | (y : ℝ) ≤ lam u}} from rfl,
    vol_pi_eval u {y : unitInterval | (y : ℝ) ≤ lam u}
      (measurableSet_le measurable_subtype_coe measurable_const), vol_I_le _ h0 h1,
    ENNReal.toReal_ofReal h0]

lemma volB (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (h0 : 0 ≤ mu u k) (h1 : mu u k ≤ 1) :
    (volume : Measure ((Fin U → Fin K → unitInterval) × unitInterval)).real
      {y | ((y.1 u k : unitInterval) : ℝ) ≤ mu u k} = mu u k := by
  have hset : {y : (Fin U → Fin K → unitInterval) × unitInterval | ((y.1 u k : unitInterval) : ℝ) ≤ mu u k} =
      {g : Fin U → Fin K → unitInterval | g u ∈ {f : Fin K → unitInterval |
        f k ∈ {y : unitInterval | (y : ℝ) ≤ mu u k}}} ×ˢ (Set.univ : Set unitInterval) := by
    ext x; simp
  rw [measureReal_def, hset]
  rw [show (volume : Measure ((Fin U → Fin K → unitInterval) × unitInterval)) =
    (volume : Measure (Fin U → Fin K → unitInterval)).prod volume from rfl,
    Measure.prod_prod, measure_univ, mul_one,
    vol_pi_eval u {f : Fin K → unitInterval | f k ∈ {y : unitInterval | (y : ℝ) ≤ mu u k}}
      (measurableSet_I_le (fun f : Fin K → unitInterval => f k) (measurable_pi_apply k) _),
    vol_pi_eval k {y : unitInterval | (y : ℝ) ≤ mu u k}
      (measurableSet_le measurable_subtype_coe measurable_const), vol_I_le _ h0 h1,
    ENNReal.toReal_ofReal h0]

lemma two_coin (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K)
    (ha0 : 0 ≤ lam u) (ha1 : lam u ≤ 1) (hb0 : 0 ≤ mu u k) (hb1 : mu u k ≤ 1)
    (φ : ℕ → ℕ → ℝ) :
    ∫ x, φ (aS lam u x) (bS mu u k x) ∂(seedLaw U K) =
      (1 - lam u) * ((1 - mu u k) * φ 0 0 + mu u k * φ 0 1) +
        lam u * ((1 - mu u k) * φ 1 0 + mu u k * φ 1 1) := by
  have hAm : MeasurableSet {f : Fin U → unitInterval | ((f u : unitInterval) : ℝ) ≤ lam u} :=
    measurableSet_I_le _ (measurable_pi_apply u) _
  have hBm : MeasurableSet {y : (Fin U → Fin K → unitInterval) × unitInterval |
      ((y.1 u k : unitInterval) : ℝ) ≤ mu u k} :=
    measurableSet_I_le _ ((measurable_pi_apply k).comp ((measurable_pi_apply u).comp measurable_fst)) _
  unfold seedLaw
  rw [show (volume : Measure (Seed U K)) = (volume : Measure (Fin U → unitInterval)).prod volume
    from rfl]
  have hmeas : Measurable (fun p : (Fin U → unitInterval) × ((Fin U → Fin K → unitInterval) × unitInterval) =>
        φ (aS lam u p) (bS mu u k p)) :=
    (measurable_of_countable (fun q : ℕ × ℕ => φ q.1 q.2)).comp ((meas_aS lam u).prodMk (meas_bS mu u k))
  rw [integral_prod _ (int_of_bdd _ _ hmeas (|φ 0 0| + |φ 0 1| + |φ 1 0| + |φ 1 1|) (by
    intro p; unfold aS bS
    split_ifs <;> linarith [abs_nonneg (φ 0 0), abs_nonneg (φ 0 1),
      abs_nonneg (φ 1 0), abs_nonneg (φ 1 1)]))]
  unfold aS bS
  dsimp only
  have h1 : ∀ x : Fin U → unitInterval,
      ∫ y : (Fin U → Fin K → unitInterval) × unitInterval,
        φ (if ((x u : unitInterval) : ℝ) ≤ lam u then 1 else 0)
          (if ((y.1 u k : unitInterval) : ℝ) ≤ mu u k then 1 else 0) =
      (1 - mu u k) * φ (if ((x u : unitInterval) : ℝ) ≤ lam u then 1 else 0) 0 +
        mu u k * φ (if ((x u : unitInterval) : ℝ) ≤ lam u then 1 else 0) 1 := by
    intro x
    rw [one_coin' volume (fun y : (Fin U → Fin K → unitInterval) × unitInterval =>
      ((y.1 u k : unitInterval) : ℝ) ≤ mu u k) hBm, volB mu u k hb0 hb1]
  simp_rw [h1]
  have h2 := one_coin' (volume : Measure (Fin U → unitInterval))
    (fun f : Fin U → unitInterval => ((f u : unitInterval) : ℝ) ≤ lam u) hAm
    (fun i => (1 - mu u k) * φ i 0 + mu u k * φ i 1)
  try dsimp only at h2
  rw [h2, volA lam u ha0 ha1]

lemma volC (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (h0 : 0 ≤ mu u k) (h1 : mu u k ≤ 1) :
    (volume : Measure (Fin U → Fin K → unitInterval)).real
      {g | ((g u k : unitInterval) : ℝ) ≤ mu u k} = mu u k := by
  rw [measureReal_def, show {g : Fin U → Fin K → unitInterval | ((g u k : unitInterval) : ℝ) ≤ mu u k} =
      {g | g u ∈ {f : Fin K → unitInterval | f k ∈ {y : unitInterval | (y : ℝ) ≤ mu u k}}} from rfl,
    vol_pi_eval u {f : Fin K → unitInterval | f k ∈ {y : unitInterval | (y : ℝ) ≤ mu u k}}
      (measurableSet_I_le (fun f : Fin K → unitInterval => f k) (measurable_pi_apply k) _),
    vol_pi_eval k {y : unitInterval | (y : ℝ) ≤ mu u k}
      (measurableSet_le measurable_subtype_coe measurable_const), vol_I_le _ h0 h1,
    ENNReal.toReal_ofReal h0]

/-- The service coin of link `(u, k)` is independent of the scheduler's private seed. -/
lemma serv_coin (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (h0 : 0 ≤ mu u k)
    (h1 : mu u k ≤ 1) (g : unitInterval → ℝ) :
    ∫ x, g x.2.2 * (bS mu u k x : ℝ) ∂(seedLaw U K) = mu u k * ∫ x, g x.2.2 ∂(seedLaw U K) := by
  have e1 : (fun x : Seed U K => g x.2.2 * (bS mu u k x : ℝ)) = fun x =>
      (fun _ : Fin U → unitInterval => (1 : ℝ)) x.1 *
        (fun y : (Fin U → Fin K → unitInterval) × unitInterval =>
          (if ((y.1 u k : unitInterval) : ℝ) ≤ mu u k then (1 : ℝ) else 0) * g y.2) x.2 := by
    funext x; simp only [bS]; split_ifs <;> simp
  have e2 : (fun x : Seed U K => g x.2.2) = fun x =>
      (fun _ : Fin U → unitInterval => (1 : ℝ)) x.1 *
        (fun y : (Fin U → Fin K → unitInterval) × unitInterval => g y.2) x.2 := by
    funext x; simp
  rw [e1, e2, seed_split (fun _ : Fin U → unitInterval => (1 : ℝ))
      (fun y : (Fin U → Fin K → unitInterval) × unitInterval =>
          (if ((y.1 u k : unitInterval) : ℝ) ≤ mu u k then (1 : ℝ) else 0) * g y.2),
    seed_split (fun _ : Fin U → unitInterval => (1 : ℝ))
      (fun y : (Fin U → Fin K → unitInterval) × unitInterval => g y.2)]
  simp only [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_mul]
  rw [show (volume : Measure ((Fin U → Fin K → unitInterval) × unitInterval)) =
    (volume : Measure (Fin U → Fin K → unitInterval)).prod volume from rfl]
  have h4 : ∫ y : (Fin U → Fin K → unitInterval) × unitInterval, g y.2
      ∂((volume : Measure (Fin U → Fin K → unitInterval)).prod volume) = ∫ y, g y := by
    simpa using integral_prod_mul (μ := (volume : Measure (Fin U → Fin K → unitInterval)))
      (fun _ => (1 : ℝ)) g
  rw [integral_prod_mul (fun g' : Fin U → Fin K → unitInterval =>
      (if ((g' u k : unitInterval) : ℝ) ≤ mu u k then (1 : ℝ) else 0)) g, h4]
  have h3 := one_coin' (volume : Measure (Fin U → Fin K → unitInterval))
    (fun g' : Fin U → Fin K → unitInterval => ((g' u k : unitInterval) : ℝ) ≤ mu u k)
    (measurableSet_I_le _ ((measurable_pi_apply k).comp (measurable_pi_apply u)) _)
    (fun n => (n : ℝ))
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_zero, mul_one, zero_add] at h3
  rw [h3, volC mu u k h0 h1]

/-! ## The genie queue is stationary -/

section Genie

variable (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) (u : Fin U)

/-- `Q*_u(j)` as a function of the system state `(Q(0), ω)`. -/
noncomputable def G (j : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) : ℕ :=
  genieQueue lam mu kstar z.1 z.2 j u

lemma G_succ (j : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) : G lam mu kstar u (j + 1) z =
    G lam mu kstar u j z + aS lam u (z.2 (j + 1)) - bS mu u (kstar u) (z.2 (j + 1)) := rfl

lemma meas_G : ∀ j, Measurable (G (K := K) lam mu kstar u j)
  | 0 => (measurable_pi_apply u).comp measurable_fst
  | j + 1 => by
    have h1 : Measurable (fun z : (Fin U → ℕ) × (ℕ → Seed U K) => aS lam u (z.2 (j + 1))) :=
      (meas_aS lam u).comp ((measurable_pi_apply (j + 1)).comp measurable_snd)
    have h2 : Measurable (fun z : (Fin U → ℕ) × (ℕ → Seed U K) =>
        bS mu u (kstar u) (z.2 (j + 1))) :=
      (meas_bS mu u (kstar u)).comp ((measurable_pi_apply (j + 1)).comp measurable_snd)
    have : G (K := K) lam mu kstar u (j + 1) = (fun p : ℕ × ℕ × ℕ => p.1 + p.2.1 - p.2.2) ∘
        (fun z => (G lam mu kstar u j z, aS lam u (z.2 (j + 1)),
          bS mu u (kstar u) (z.2 (j + 1)))) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((meas_G j).prodMk (h1.prodMk h2))

lemma G_inv : ∀ (j s : ℕ), j < s → ∀ (z : (Fin U → ℕ) × (ℕ → Seed U K)) (y : Seed U K),
    G lam mu kstar u j (z.1, Function.update z.2 s y) = G lam mu kstar u j z
  | 0, _, _, _, _ => rfl
  | j + 1, s, hs, z, y => by
    rw [G_succ, G_succ, G_inv j s (by omega) z y]
    simp only [Function.update_of_ne (show j + 1 ≠ s by omega)]

lemma genie_step (hl0 : 0 ≤ lam u) (hl1 : lam u ≤ 1) (hm0 : 0 ≤ mu u (kstar u))
    (hm1 : mu u (kstar u) ≤ 1) (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (j : ℕ)
    (φ : ℕ → ℕ → ℕ → ℝ) (C : ℝ) (hC : ∀ g a b, a ≤ 1 → b ≤ 1 → |φ g a b| ≤ C) :
    ∫ z, φ (G lam mu kstar u j z) (aS lam u (z.2 (j + 1))) (bS mu u (kstar u) (z.2 (j + 1)))
        ∂(sysMeasure (K := K) ν) =
      ∫ z, ((1 - lam u) * ((1 - mu u (kstar u)) * φ (G lam mu kstar u j z) 0 0 +
          mu u (kstar u) * φ (G lam mu kstar u j z) 0 1) +
        lam u * ((1 - mu u (kstar u)) * φ (G lam mu kstar u j z) 1 0 +
          mu u (kstar u) * φ (G lam mu kstar u j z) 1 1)) ∂(sysMeasure (K := K) ν) := by
  have hm : Measurable (Function.uncurry fun (z : (Fin U → ℕ) × (ℕ → Seed U K)) (x : Seed U K) =>
      φ (G lam mu kstar u j z) (aS lam u x) (bS mu u (kstar u) x)) := by
    have : (Function.uncurry fun (z : (Fin U → ℕ) × (ℕ → Seed U K)) (x : Seed U K) =>
        φ (G lam mu kstar u j z) (aS lam u x) (bS mu u (kstar u) x)) =
        (fun t : ℕ × ℕ × ℕ => φ t.1 t.2.1 t.2.2) ∘ (fun p => (G lam mu kstar u j p.1,
          aS lam u p.2, bS mu u (kstar u) p.2)) := rfl
    rw [this]
    exact (measurable_of_countable _).comp (((meas_G lam mu kstar u j).comp measurable_fst).prodMk
      (((meas_aS lam u).comp measurable_snd).prodMk ((meas_bS mu u (kstar u)).comp measurable_snd)))
  have := integral_fresh ν (j + 1) (fun z x => φ (G lam mu kstar u j z) (aS lam u x)
    (bS mu u (kstar u) x)) hm C (fun z x => hC _ _ _ (aS_le _ _ _) (bS_le _ _ _ _))
    (fun z x y => by rw [G_inv lam mu kstar u j (j + 1) (by omega)])
  refine this.trans ?_
  congr 1; funext z
  exact two_coin lam mu u (kstar u) hl0 hl1 hm0 hm1 (φ (G lam mu kstar u j z))

lemma int_ind_G (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (j c : ℕ) :
    Integrable (fun z => if G lam mu kstar u j z = c then (1 : ℝ) else 0) (sysMeasure (K := K) ν) :=
  int_of_bdd _ _ (Measurable.ite ((meas_G lam mu kstar u j) (measurableSet_singleton c))
    measurable_const measurable_const) 1 (fun z => by split_ifs <;> simp)

instance initLaw_prob : IsProbabilityMeasure (initLaw lam mu kstar) := by
  unfold initLaw; infer_instance

/-- Basic facts about `ρ_u` under Assumption 2. -/
lemma rho_facts (hl0 : 0 ≤ lam u) (hm1 : mu u (kstar u) ≤ 1)
    (heps : 0 < eps lam mu kstar u) :
    0 ≤ rho lam mu kstar u ∧ rho lam mu kstar u < 1 ∧
      (1 - lam u) * mu u (kstar u) * rho lam mu kstar u = lam u * (1 - mu u (kstar u)) := by
  unfold eps muStarU at heps
  have hb : 0 < mu u (kstar u) := by linarith
  have ha : 0 < 1 - lam u := by linarith
  unfold rho muStarU
  refine ⟨div_nonneg (mul_nonneg hl0 (by linarith)) (by positivity), ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; nlinarith
  · field_simp

lemma genie_law (hl0 : 0 ≤ lam u) (hl1 : lam u ≤ 1) (hm0 : 0 ≤ mu u (kstar u))
    (hm1 : mu u (kstar u) ≤ 1) (heps : 0 < eps lam mu kstar u) :
    ∀ j n, ∫ z, (if G lam mu kstar u j z = n then (1 : ℝ) else 0)
        ∂(sysMeasure (K := K) (initLaw lam mu kstar)) =
      (1 - rho lam mu kstar u) * rho lam mu kstar u ^ n := by
  obtain ⟨hρ0, hρ1, hkey⟩ := rho_facts lam mu kstar u hl0 hm1 heps
  set ρ := rho lam mu kstar u with hρ
  intro j
  induction j with
  | zero =>
    intro n
    have hS : MeasurableSet {z : (Fin U → ℕ) × (ℕ → Seed U K) | G lam mu kstar u 0 z = n} :=
      (meas_G lam mu kstar u 0) (measurableSet_singleton n)
    rw [int_ind_eq' _ _ hS]
    have hset : {z : (Fin U → ℕ) × (ℕ → Seed U K) | G lam mu kstar u 0 z = n} =
        (@Function.eval (Fin U) (fun _ => ℕ) u ⁻¹' ({n} : Set ℕ)) ×ˢ
          (Set.univ : Set (ℕ → Seed U K)) := by
      ext z; simp [G, genieQueue]
    rw [hset, measureReal_def]
    unfold sysMeasure
    rw [Measure.prod_prod, measure_univ, mul_one]
    unfold initLaw
    rw [(measurePreserving_eval _ u).measure_preimage (measurableSet_singleton n).nullMeasurableSet]
    have hmem : 1 - ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hp : Set.projIcc (0 : ℝ) 1 zero_le_one (1 - ρ) ≠ 0 := by
      rw [Set.projIcc_of_mem _ hmem]
      intro h
      have := congrArg Subtype.val h
      simp at this; linarith
    rw [geometricMeasure_singleton hp, Set.projIcc_of_mem _ hmem]
    simp only
    rw [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (by linarith) n) (by linarith))]
    ring
  | succ j ih =>
    intro n
    refine Eq.trans (genie_step lam mu kstar u hl0 hl1 hm0 hm1 (initLaw lam mu kstar) j
      (fun g a b => if g + a - b = n then (1 : ℝ) else 0) 1
      (fun g a b _ _ => by
        show |(if g + a - b = n then (1 : ℝ) else 0)| ≤ 1
        split_ifs <;> simp)) ?_
    rcases n with _ | m
    · have hpt : ∀ g : ℕ, ((1 - lam u) * ((1 - mu u (kstar u)) * (if g + 0 - 0 = 0 then (1 : ℝ) else 0) +
            mu u (kstar u) * (if g + 0 - 1 = 0 then (1 : ℝ) else 0)) +
          lam u * ((1 - mu u (kstar u)) * (if g + 1 - 0 = 0 then (1 : ℝ) else 0) +
            mu u (kstar u) * (if g + 1 - 1 = 0 then (1 : ℝ) else 0))) =
          (1 - lam u * (1 - mu u (kstar u))) * (if g = 0 then (1 : ℝ) else 0) +
            (1 - lam u) * mu u (kstar u) * (if g = 1 then (1 : ℝ) else 0) := by
        intro g
        split_ifs <;> first | (exfalso; omega) | ring
      simp_rw [hpt]
      rw [integral_add ((int_ind_G lam mu kstar u _ j 0).const_mul _)
          ((int_ind_G lam mu kstar u _ j 1).const_mul _),
        integral_const_mul, integral_const_mul, ih 0, ih 1]
      linear_combination (1 - ρ) * hkey
    · have hpt : ∀ g : ℕ, ((1 - lam u) * ((1 - mu u (kstar u)) * (if g + 0 - 0 = m + 1 then (1 : ℝ) else 0) +
            mu u (kstar u) * (if g + 0 - 1 = m + 1 then (1 : ℝ) else 0)) +
          lam u * ((1 - mu u (kstar u)) * (if g + 1 - 0 = m + 1 then (1 : ℝ) else 0) +
            mu u (kstar u) * (if g + 1 - 1 = m + 1 then (1 : ℝ) else 0))) =
          ((1 - lam u) * (1 - mu u (kstar u)) + lam u * mu u (kstar u)) * (if g = m + 1 then (1 : ℝ) else 0) +
            (1 - lam u) * mu u (kstar u) * (if g = m + 2 then (1 : ℝ) else 0) +
            lam u * (1 - mu u (kstar u)) * (if g = m then (1 : ℝ) else 0) := by
        intro g
        split_ifs <;> first | (exfalso; omega) | ring
      simp_rw [hpt]
      have i1 := (int_ind_G lam mu kstar u (initLaw lam mu kstar) j (m + 1)).const_mul
        ((1 - lam u) * (1 - mu u (kstar u)) + lam u * mu u (kstar u))
      have i2 := (int_ind_G lam mu kstar u (initLaw lam mu kstar) j (m + 2)).const_mul
        ((1 - lam u) * mu u (kstar u))
      have i3 := (int_ind_G lam mu kstar u (initLaw lam mu kstar) j m).const_mul
        (lam u * (1 - mu u (kstar u)))
      have i12 : Integrable (fun z => ((1 - lam u) * (1 - mu u (kstar u)) + lam u * mu u (kstar u)) *
          (if G lam mu kstar u j z = m + 1 then (1 : ℝ) else 0) +
          (1 - lam u) * mu u (kstar u) * (if G lam mu kstar u j z = m + 2 then (1 : ℝ) else 0))
          (sysMeasure (K := K) (initLaw lam mu kstar)) := i1.add i2
      rw [integral_add i12 i3, integral_add i1 i2,
        integral_const_mul, integral_const_mul, integral_const_mul, ih, ih, ih]
      linear_combination (-(1 - ρ) ^ 2 * ρ ^ m) * hkey

lemma genie_incr_bound (g a b : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :
    |((g + a - b : ℕ) : ℝ) - g| ≤ 1 := by
  rcases Nat.lt_or_ge (g + a) b with h | h
  · have h1 : g + a - b = 0 := by omega
    have h2 : g = 0 := by omega
    rw [h1, h2]; simp
  · rw [Nat.cast_sub h, Nat.cast_add]
    have : (a : ℝ) ≤ 1 := by exact_mod_cast ha
    have : (b : ℝ) ≤ 1 := by exact_mod_cast hb
    rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]

lemma int_G_diff (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (j : ℕ) :
    Integrable (fun z => (G lam mu kstar u (j + 1) z : ℝ) - G lam mu kstar u j z)
      (sysMeasure (K := K) ν) :=
  int_of_bdd _ _ ((measurable_of_countable _).comp (meas_G lam mu kstar u (j + 1)) |>.sub
    ((measurable_of_countable _).comp (meas_G lam mu kstar u j))) 1
    (fun z => by rw [G_succ]; exact genie_incr_bound _ _ _ (aS_le _ _ _) (bS_le _ _ _ _))

lemma genie_incr (hl0 : 0 ≤ lam u) (hl1 : lam u ≤ 1) (hm0 : 0 ≤ mu u (kstar u))
    (hm1 : mu u (kstar u) ≤ 1) (heps : 0 < eps lam mu kstar u) (j : ℕ) :
    ∫ z, ((G lam mu kstar u (j + 1) z : ℝ) - G lam mu kstar u j z)
        ∂(sysMeasure (K := K) (initLaw lam mu kstar)) = 0 := by
  obtain ⟨hρ0, hρ1, hkey⟩ := rho_facts lam mu kstar u hl0 hm1 heps
  set ρ := rho lam mu kstar u with hρ
  refine Eq.trans (genie_step lam mu kstar u hl0 hl1 hm0 hm1 (initLaw lam mu kstar) j
    (fun g a b => ((g + a - b : ℕ) : ℝ) - g) 1
    (fun g a b ha hb => genie_incr_bound g a b ha hb)) ?_
  have hpt : ∀ g : ℕ, ((1 - lam u) * ((1 - mu u (kstar u)) * (((g + 0 - 0 : ℕ) : ℝ) - g) +
        mu u (kstar u) * (((g + 0 - 1 : ℕ) : ℝ) - g)) +
      lam u * ((1 - mu u (kstar u)) * (((g + 1 - 0 : ℕ) : ℝ) - g) + mu u (kstar u) * (((g + 1 - 1 : ℕ) : ℝ) - g))) =
      (lam u * (1 - mu u (kstar u)) - (1 - lam u) * mu u (kstar u)) + (1 - lam u) * mu u (kstar u) * (if g = 0 then (1 : ℝ) else 0) := by
    intro g
    rcases g with _ | g
    · simp
    · have e1 : g + 1 + 0 - 0 = g + 1 := by omega
      have e2 : g + 1 + 0 - 1 = g := by omega
      have e3 : g + 1 + 1 - 0 = g + 2 := by omega
      have e4 : g + 1 + 1 - 1 = g + 1 := by omega
      rw [e1, e2, e3, e4]
      simp only [Nat.add_one_ne_zero, if_false]
      push_cast; ring
  simp_rw [hpt]
  rw [integral_add (integrable_const _) ((int_ind_G lam mu kstar u _ j 0).const_mul _),
    integral_const, integral_const_mul, genie_law lam mu kstar u hl0 hl1 hm0 hm1 heps j 0]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, pow_zero, mul_one]
  linear_combination (-1 : ℝ) * hkey

lemma G_sub0_bound (t : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) :
    |(G lam mu kstar u t z : ℝ) - G lam mu kstar u 0 z| ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : |(G lam mu kstar u (t + 1) z : ℝ) - G lam mu kstar u t z| ≤ 1 := by
      rw [G_succ]; exact genie_incr_bound _ _ _ (aS_le _ _ _) (bS_le _ _ _ _)
    calc |(G lam mu kstar u (t + 1) z : ℝ) - G lam mu kstar u 0 z|
        = |((G lam mu kstar u (t + 1) z : ℝ) - G lam mu kstar u t z) +
            ((G lam mu kstar u t z : ℝ) - G lam mu kstar u 0 z)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ 1 + t := by linarith
      _ = ((t + 1 : ℕ) : ℝ) := by push_cast; ring

lemma int_G_sub0 (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (t : ℕ) :
    Integrable (fun z => (G lam mu kstar u t z : ℝ) - G lam mu kstar u 0 z)
      (sysMeasure (K := K) ν) :=
  int_of_bdd _ _ ((measurable_of_countable _).comp (meas_G lam mu kstar u t) |>.sub
    ((measurable_of_countable _).comp (meas_G lam mu kstar u 0))) t
    (G_sub0_bound lam mu kstar u t)

/-- Stationarity: `E[Q*_u(t) − Q_u(0)] = 0`. -/
lemma genie_total (hl0 : 0 ≤ lam u) (hl1 : lam u ≤ 1) (hm0 : 0 ≤ mu u (kstar u))
    (hm1 : mu u (kstar u) ≤ 1) (heps : 0 < eps lam mu kstar u) (t : ℕ) :
    ∫ z, ((G lam mu kstar u t z : ℝ) - G lam mu kstar u 0 z)
        ∂(sysMeasure (K := K) (initLaw lam mu kstar)) = 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hpt : (fun z => (G lam mu kstar u (t + 1) z : ℝ) - G lam mu kstar u 0 z) =
        fun z => ((G lam mu kstar u (t + 1) z : ℝ) - G lam mu kstar u t z) +
          ((G lam mu kstar u t z : ℝ) - G lam mu kstar u 0 z) := by
      funext z; ring
    rw [hpt, integral_add (int_G_diff lam mu kstar u _ t) (int_G_sub0 lam mu kstar u _ t), ih,
      genie_incr lam mu kstar u hl0 hl1 hm0 hm1 heps t, add_zero]

end Genie

/-! ## The queue under the policy -/

section Pol

variable (π : Policy U K) (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (u : Fin U)

/-- `Q_u(t)` as a function of the system state. -/
noncomputable def Qf (t : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) : ℕ :=
  queue π lam mu z.1 z.2 t u

/-- The service `S_u(s)` offered to queue `u` in slot `s`. -/
noncomputable def Sv (s : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) : ℕ :=
  bS mu u (sched π mu z.2 s u) (z.2 s)

lemma Qf_succ (t : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) : Qf π lam mu u (t + 1) z =
    Qf π lam mu u t z + aS lam u (z.2 (t + 1)) - Sv π mu u (t + 1) z := rfl

lemma meas_sched_u (s : ℕ) : Measurable (fun ω : ℕ → Seed U K => sched π mu ω s u) :=
  measurable_to_countable' (fun k => sched_fiber π mu s u k)

lemma meas_Sv (s : ℕ) : Measurable (Sv (K := K) π mu u s) := by
  have h1 : Measurable (fun p : Fin K × Seed U K => bS mu u p.1 p.2) :=
    measurable_from_prod_countable_right (fun k => meas_bS mu u k)
  have h2 : Measurable (fun z : (Fin U → ℕ) × (ℕ → Seed U K) => (sched π mu z.2 s u, z.2 s)) :=
    ((meas_sched_u π mu u s).comp measurable_snd).prodMk
      ((measurable_pi_apply s).comp measurable_snd)
  exact h1.comp h2

lemma meas_Qf : ∀ t, Measurable (Qf (K := K) π lam mu u t)
  | 0 => (measurable_pi_apply u).comp measurable_fst
  | t + 1 => by
    have : Qf (K := K) π lam mu u (t + 1) = (fun p : ℕ × ℕ × ℕ => p.1 + p.2.1 - p.2.2) ∘
        (fun z => (Qf π lam mu u t z, aS lam u (z.2 (t + 1)), Sv π mu u (t + 1) z)) := rfl
    rw [this]
    exact (measurable_of_countable _).comp ((meas_Qf t).prodMk
      (((meas_aS (K := K) lam u).comp ((measurable_pi_apply (t + 1)).comp
        (measurable_snd (α := Fin U → ℕ) (β := ℕ → Seed U K)))).prodMk
        (meas_Sv π mu u (t + 1))))

lemma Qf_bound (t : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) :
    |(Qf π lam mu u t z : ℝ) - z.1 u| ≤ t := by
  induction t with
  | zero => simp [Qf, queue]
  | succ t ih =>
    have h1 : |(Qf π lam mu u (t + 1) z : ℝ) - Qf π lam mu u t z| ≤ 1 := by
      rw [Qf_succ]; exact genie_incr_bound _ _ _ (aS_le _ _ _) (bS_le _ _ _ _)
    calc |(Qf π lam mu u (t + 1) z : ℝ) - z.1 u|
        = |((Qf π lam mu u (t + 1) z : ℝ) - Qf π lam mu u t z) +
            ((Qf π lam mu u t z : ℝ) - z.1 u)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ 1 + t := by linarith
      _ = ((t + 1 : ℕ) : ℝ) := by push_cast; ring

lemma natsub_ge (x a b : ℕ) : (x : ℝ) + a - b ≤ ((x + a - b : ℕ) : ℝ) := by
  rcases le_or_gt b (x + a) with h | h
  · rw [Nat.cast_sub h]; push_cast; exact le_refl _
  · rw [Nat.sub_eq_zero_of_le h.le]
    have : (x : ℝ) + a < b := by exact_mod_cast h
    simp only [Nat.cast_zero]; linarith

lemma Qf_lower (t : ℕ) (z : (Fin U → ℕ) × (ℕ → Seed U K)) :
    ∑ s ∈ Finset.range t, ((aS lam u (z.2 (s + 1)) : ℝ) - Sv π mu u (s + 1) z) ≤
      (Qf π lam mu u t z : ℝ) - z.1 u := by
  induction t with
  | zero => simp [Qf, queue]
  | succ t ih =>
    rw [Finset.sum_range_succ, Qf_succ]
    have := natsub_ge (Qf π lam mu u t z) (aS lam u (z.2 (t + 1))) (Sv π mu u (t + 1) z)
    linarith

lemma hist_inv (s : ℕ) (y : Seed U K) : ∀ n, n < s → ∀ ω : ℕ → Seed U K,
    hist π mu (Function.update ω s y) n = hist π mu ω n
  | 0, _, _ => rfl
  | n + 1, hn, ω => by
    simp only [hist]
    rw [hist_inv s y n (by omega) ω]
    simp only [offered, Function.update_of_ne (show n + 1 ≠ s by omega)]
    rfl

lemma integral_snd_sys (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (f : (ℕ → Seed U K) → ℝ) (hf : Measurable f) :
    ∫ z, f z.2 ∂(sysMeasure (K := K) ν) = ∫ ω, f ω ∂(seedMeasure U K) := by
  unfold sysMeasure
  rw [← integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  rw [← Measure.snd, Measure.snd_prod]

lemma meas_ind_act (n : ℕ) (h : History U K n) (k : Fin K) :
    MeasurableSet {x : Seed U K | (π.act n h x.2.2) u = k} := by
  have : {x : Seed U K | (π.act n h x.2.2) u = k} =
      ⋃ m ∈ {m : Matching U K | m u = k}, (fun x : Seed U K => x.2.2) ⁻¹' {c | π.act n h c = m} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun m _ =>
    (π.measurableSet_act n h m).preimage (measurable_snd.comp measurable_snd)

/-- Integrating out the seed of slot `s`, with the scheduler's history fixed. -/
lemma sched_fresh (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (s : ℕ) (hs : 1 ≤ s)
    (k : Fin K) (c : Seed U K → ℝ) (hc : Measurable c) (hcb : ∀ x, |c x| ≤ 1) :
    ∫ z, (if sched π mu z.2 s u = k then (1 : ℝ) else 0) * c (z.2 s) ∂(sysMeasure (K := K) ν) =
      ∫ z, (∫ x, (if (π.act (s - 1) (hist π mu z.2 (s - 1)) x.2.2) u = k then (1 : ℝ) else 0) *
        c x ∂(seedLaw U K)) ∂(sysMeasure (K := K) ν) := by
  classical
  set Γ : (Fin U → ℕ) × (ℕ → Seed U K) → Seed U K → ℝ := fun z x =>
    (if (π.act (s - 1) (hist π mu z.2 (s - 1)) x.2.2) u = k then (1 : ℝ) else 0) * c x with hΓ
  have hm : Measurable (Function.uncurry Γ) := by
    have hsum : Function.uncurry Γ = fun p => ∑ h : History U K (s - 1),
        (if hist π mu p.1.2 (s - 1) = h then (1 : ℝ) else 0) *
          ((if (π.act (s - 1) h p.2.2.2) u = k then (1 : ℝ) else 0) * c p.2) := by
      funext p
      simp only [Function.uncurry, hΓ, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    rw [hsum]
    refine Finset.measurable_sum _ fun h _ => ?_
    refine Measurable.mul ?_ (Measurable.mul ?_ (hc.comp measurable_snd))
    · exact Measurable.ite ((hist_fiber π mu (s - 1) h).preimage
        (measurable_snd.comp measurable_fst)) measurable_const measurable_const
    · exact Measurable.ite ((meas_ind_act π u (s - 1) h k).preimage measurable_snd)
        measurable_const measurable_const
  have hb : ∀ z x, |Γ z x| ≤ 1 := by
    intro z x
    simp only [hΓ]
    split_ifs
    · simpa using hcb x
    · simp
  have hinv : ∀ z x y, Γ (z.1, Function.update z.2 s y) x = Γ z x := by
    intro z x y
    simp only [hΓ]
    rw [hist_inv π mu s y (s - 1) (by omega) z.2]
  have := integral_fresh ν s Γ hm 1 hb hinv
  refine Eq.trans ?_ this
  congr 1

lemma E_arr (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (s : ℕ) (h0 : 0 ≤ lam u)
    (h1 : lam u ≤ 1) :
    ∫ z, (aS lam u (z.2 s) : ℝ) ∂(sysMeasure (K := K) ν) = lam u := by
  have hm : Measurable (Function.uncurry fun (_ : (Fin U → ℕ) × (ℕ → Seed U K)) (x : Seed U K) =>
      (aS lam u x : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp ((meas_aS lam u).comp measurable_snd)
  have := integral_fresh ν s (fun _ x => (aS lam u x : ℝ)) hm 1
    (fun _ x => by have := aS_le (K := K) lam u x; rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> simp [h])
    (fun _ _ _ => rfl)
  refine this.trans ?_
  have h2 := one_coin' (seedLaw U K) (fun x : Seed U K => ((x.1 u : unitInterval) : ℝ) ≤ lam u)
    (measurableSet_arrSet lam u) (fun n => (n : ℝ))
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_zero, mul_one, zero_add] at h2
  have h3 : ∫ x, (aS lam u x : ℝ) ∂(seedLaw U K) = lam u := by
    simp only [aS, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [h2]
    exact seedLaw_arrSet lam u h0 h1
  simp only [h3, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

lemma int_ind_sched (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (s : ℕ) (k : Fin K) :
    Integrable (fun z => if sched π mu z.2 s u = k then (1 : ℝ) else 0) (sysMeasure (K := K) ν) :=
  int_of_bdd _ _ (Measurable.ite ((sched_fiber π mu s u k).preimage measurable_snd)
    measurable_const measurable_const) 1 (fun z => by split_ifs <;> simp)

lemma E_serv (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν] (s : ℕ) (hs : 1 ≤ s)
    (hmu : ∀ k, 0 ≤ mu u k ∧ mu u k ≤ 1) :
    ∫ z, (Sv π mu u s z : ℝ) ∂(sysMeasure (K := K) ν) =
      ∑ k : Fin K, mu u k * ∫ z, (if sched π mu z.2 s u = k then (1 : ℝ) else 0)
        ∂(sysMeasure (K := K) ν) := by
  have hpt : (fun z => (Sv π mu u s z : ℝ)) = fun z => ∑ k : Fin K,
      (if sched π mu z.2 s u = k then (1 : ℝ) else 0) * (bS mu u k (z.2 s) : ℝ) := by
    funext z
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [Sv]
  rw [hpt, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    have hbS : ∀ x, |(bS mu u k x : ℝ)| ≤ 1 := by
      intro x; have := bS_le mu u k x
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> simp [h]
    rw [sched_fresh π mu u ν s hs k (fun x => (bS mu u k x : ℝ))
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (meas_bS mu u k)) hbS]
    have hin : ∀ z : (Fin U → ℕ) × (ℕ → Seed U K),
        ∫ x, (if (π.act (s - 1) (hist π mu z.2 (s - 1)) x.2.2) u = k then (1 : ℝ) else 0) *
          (bS mu u k x : ℝ) ∂(seedLaw U K) =
        mu u k * ∫ x, (if (π.act (s - 1) (hist π mu z.2 (s - 1)) x.2.2) u = k then (1 : ℝ) else 0)
          ∂(seedLaw U K) := fun z =>
      serv_coin mu u k (hmu k).1 (hmu k).2
        (fun c => if (π.act (s - 1) (hist π mu z.2 (s - 1)) c) u = k then (1 : ℝ) else 0)
    simp_rw [hin]
    rw [integral_const_mul]
    have hR := sched_fresh π mu u ν s hs k (fun _ => (1 : ℝ)) measurable_const (fun _ => by simp)
    simp only [mul_one] at hR
    rw [hR]
  · intro k _
    exact int_of_bdd _ _ (Measurable.mul (Measurable.ite ((sched_fiber π mu s u k).preimage
      measurable_snd) measurable_const measurable_const)
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        ((meas_bS mu u k).comp ((measurable_pi_apply s).comp measurable_snd)))) 1
      (fun z => by
        have := bS_le mu u k (z.2 s)
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> split_ifs <;> simp [h])

end Pol

end QB3L22

open QB3L22 in
theorem solution {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hlam : ∀ u, 0 ≤ lam u ∧ lam u ≤ 1) (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1)
    (hA1 : QueueBandit.LateLower.Assumption1 mu kstar) (hA2 : ∀ u, 0 < eps lam mu kstar u)
    (π : QueueBandit.LateLower.Policy U K) (u : Fin U) (t : ℕ) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        QueueBandit.LateLower.gap mu kstar u k * QueueBandit.LateLower.expCount π mu u k t) -
        eps lam mu kstar u * t ≤
      QueueBandit.LateLower.queueRegret lam mu kstar (initLaw lam mu kstar) π u t := by
  classical
  set ν := initLaw lam mu kstar with hν
  have hl0 := (hlam u).1
  have hl1 := (hlam u).2
  have hm0 := (hmu u (kstar u)).1
  have hm1 := (hmu u (kstar u)).2
  -- integrability of `Q_u(t) − Q_u(0)`
  have hintQ : Integrable (fun z => (Qf π lam mu u t z : ℝ) - z.1 u) (sysMeasure (K := K) ν) :=
    int_of_bdd _ _ ((measurable_of_countable _).comp (meas_Qf π lam mu u t) |>.sub
      ((measurable_of_countable _).comp ((measurable_pi_apply u).comp measurable_fst))) t
      (Qf_bound π lam mu u t)
  -- Ψ = E[Q(t) − Q(0)] − E[Q*(t) − Q*(0)]
  have hQ : queueRegret lam mu kstar ν π u t =
      ∫ z, ((Qf π lam mu u t z : ℝ) - z.1 u) ∂(sysMeasure (K := K) ν) -
        ∫ z, ((G lam mu kstar u t z : ℝ) - G lam mu kstar u 0 z) ∂(sysMeasure (K := K) ν) := by
    unfold queueRegret
    rw [← integral_sub hintQ (int_G_sub0 lam mu kstar u _ t)]
    congr 1; funext z
    simp only [Qf, G, genieQueue]
    ring
  rw [hQ, hν, genie_total lam mu kstar u hl0 hl1 hm0 hm1 (hA2 u) t, sub_zero]
  -- the indicator expectations
  set I : ℕ → Fin K → ℝ := fun s k =>
    ∫ z, (if sched π mu z.2 s u = k then (1 : ℝ) else 0) ∂(sysMeasure (K := K) ν) with hI
  have hE : ∀ k, expCount π mu u k t = ∑ s ∈ Finset.range t, I (s + 1) k := by
    intro k
    unfold expCount
    rw [← integral_snd_sys ν _ (meas_count π mu u k t)]
    have hc : ∀ ω : ℕ → Seed U K, (count π mu ω u k t : ℝ) =
        ∑ s ∈ Finset.range t, (if sched π mu ω (s + 1) u = k then (1 : ℝ) else 0) := by
      intro ω
      rw [count_eq, Nat.cast_sum]
      clear hI hQ hintQ
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
        push_cast; rfl
    simp_rw [hc]
    rw [integral_finsetSum _ (fun s _ => int_ind_sched π mu u ν (s + 1) k)]
  have hI1 : ∀ s, ∑ k : Fin K, I s k = 1 := by
    intro s
    simp only [hI]
    rw [← integral_finsetSum _ (fun k _ => int_ind_sched π mu u ν s k)]
    have : (fun z : (Fin U → ℕ) × (ℕ → Seed U K) =>
        ∑ k : Fin K, (if sched π mu z.2 s u = k then (1 : ℝ) else 0)) = fun _ => 1 := by
      funext z; rw [Finset.sum_ite_eq]; simp
    rw [this]; simp
  have hsumE : ∑ k : Fin K, expCount π mu u k t = t := by
    simp_rw [hE]
    rw [Finset.sum_comm]
    simp [hI1]
  -- lower bound on `E[Q(t) − Q(0)]`
  have hlow : (lam u) * t - ∑ k : Fin K, mu u k * expCount π mu u k t ≤
      ∫ z, ((Qf π lam mu u t z : ℝ) - z.1 u) ∂(sysMeasure (K := K) ν) := by
    have hint_s : ∀ s ∈ Finset.range t, Integrable
        (fun z => (aS lam u (z.2 (s + 1)) : ℝ) - Sv π mu u (s + 1) z) (sysMeasure (K := K) ν) := by
      intro s _
      refine int_of_bdd _ _ (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
        ((meas_aS (K := K) lam u).comp ((measurable_pi_apply (s + 1)).comp measurable_snd))).sub
        ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (meas_Sv π mu u (s + 1)))) 1 ?_
      intro z
      have ha := aS_le (K := K) lam u (z.2 (s + 1))
      have hb := bS_le mu u (sched π mu z.2 (s + 1) u) (z.2 (s + 1))
      simp only [Sv]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with h1 | h1 <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h2 | h2 <;> simp [h1, h2]
    have h1 := integral_mono (integrable_finsetSum _ hint_s) hintQ (fun z => Qf_lower π lam mu u t z)
    rw [integral_finsetSum _ hint_s] at h1
    have h2 : ∀ s ∈ Finset.range t,
        ∫ z, ((aS lam u (z.2 (s + 1)) : ℝ) - Sv π mu u (s + 1) z) ∂(sysMeasure (K := K) ν) =
          lam u - ∑ k : Fin K, mu u k * I (s + 1) k := by
      intro s _
      have ia : Integrable (fun z => (aS lam u (z.2 (s + 1)) : ℝ)) (sysMeasure (K := K) ν) :=
        int_of_bdd _ _ ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
          ((meas_aS (K := K) lam u).comp ((measurable_pi_apply (s + 1)).comp measurable_snd))) 1
          (fun z => by
            have ha := aS_le (K := K) lam u (z.2 (s + 1))
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with h | h <;> simp [h])
      have isv : Integrable (fun z => (Sv π mu u (s + 1) z : ℝ)) (sysMeasure (K := K) ν) :=
        int_of_bdd _ _ ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
          (meas_Sv π mu u (s + 1))) 1
          (fun z => by
            have hb := bS_le mu u (sched π mu z.2 (s + 1) u) (z.2 (s + 1))
            simp only [Sv]
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> simp [h])
      rw [integral_sub ia isv, E_arr lam u ν (s + 1) hl0 hl1,
        E_serv π mu u ν (s + 1) (by omega) (hmu u)]
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib] at h1
    have h3 : ∑ s ∈ Finset.range t, ∑ k : Fin K, mu u k * I (s + 1) k =
        ∑ k : Fin K, mu u k * expCount π mu u k t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [hE, Finset.mul_sum]
    rw [h3] at h1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    linarith
  -- algebra
  have hfilt : Finset.univ.filter (fun k : Fin K => k ≠ kstar u) = Finset.univ.erase (kstar u) :=
    Finset.filter_ne' _ _
  rw [hfilt]
  have hs1 := Finset.add_sum_erase Finset.univ (fun k => expCount π mu u k t)
    (Finset.mem_univ (kstar u))
  have hs2 := Finset.add_sum_erase Finset.univ (fun k => mu u k * expCount π mu u k t)
    (Finset.mem_univ (kstar u))
  have hs3 : ∑ k ∈ Finset.univ.erase (kstar u), gap mu kstar u k * expCount π mu u k t =
      mu u (kstar u) * ∑ k ∈ Finset.univ.erase (kstar u), expCount π mu u k t -
        ∑ k ∈ Finset.univ.erase (kstar u), mu u k * expCount π mu u k t := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold gap; ring
  rw [hs3]
  have h5 : mu u (kstar u) * ∑ k ∈ Finset.univ.erase (kstar u), expCount π mu u k t =
      mu u (kstar u) * t - mu u (kstar u) * expCount π mu u (kstar u) t := by
    rw [← hsumE, ← hs1]; ring
  unfold eps muStarU
  linarith
