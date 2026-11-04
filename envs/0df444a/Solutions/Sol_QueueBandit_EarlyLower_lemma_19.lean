-- Prove2me | solution 1 for QueueBandit.EarlyLower.lemma_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:36:11.308025+00:00
-- url     : https://prove2.me/submissions/e57b9a98-5e0a-4135-a108-4d6d7bbc1106
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics
import Theorems.Thm_QueueBandit_EarlyLower_history_bretagnolle_huber

open QueueBandit.LateLower QueueBandit.EarlyLower MeasureTheory

namespace QB3L19

section KL
open Real

/-- The Bernoulli divergence as an explicit function of its first argument. -/
noncomputable def klF (q p : ℝ) : ℝ :=
  p * log p + (1 - p) * log (1 - p) - p * log q - (1 - p) * log (1 - q)

lemma klBern_eq (p q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    RegretBandits.Stochastic.klBern p q = klF q p := by
  unfold RegretBandits.Stochastic.klBern klF
  have h1 : p * log (p / q) = p * log p - p * log q := by
    by_cases hp : p = 0
    · simp [hp]
    · rw [log_div hp hq0.ne']; ring
  have h2 : (1 - p) * log ((1 - p) / (1 - q)) = (1 - p) * log (1 - p) - (1 - p) * log (1 - q) := by
    by_cases hp : 1 - p = 0
    · simp [hp]
    · rw [log_div hp (by linarith)]; ring
  rw [h1, h2]; ring

lemma klF_antitone (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : AntitoneOn (klF q) (Set.Icc 0 q) := by
  have hcont : Continuous (klF q) := by
    unfold klF
    have c1 : Continuous fun x : ℝ => x * log x := continuous_mul_log
    have c2 : Continuous fun x : ℝ => (1 - x) * log (1 - x) :=
      continuous_mul_log.comp (continuous_const.sub continuous_id)
    exact ((c1.add c2).sub (continuous_id.mul continuous_const)).sub
      ((continuous_const.sub continuous_id).mul continuous_const)
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 q) hcont.continuousOn
    (f' := fun x => log x - log (1 - x) - log q + log (1 - q)) ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hxq⟩ := hx
    have hx1 : 1 - x ≠ 0 := by linarith
    have d1 := hasDerivAt_mul_log hx0.ne'
    have d2 : HasDerivAt (fun x : ℝ => (1 - x) * log (1 - x)) ((log (1 - x) + 1) * (-1)) x := by
      have := (hasDerivAt_mul_log hx1).comp x ((hasDerivAt_id x).const_sub 1)
      exact this
    have d3 := ((d1.add d2).sub ((hasDerivAt_id x).mul_const (log q))).sub
      (((hasDerivAt_id x).const_sub 1).mul_const (log (1 - q)))
    apply HasDerivAt.hasDerivWithinAt
    convert d3 using 1
    · funext y; simp [klF]
    · simp; ring
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx0, hxq⟩ := hx
    have h1 : log x < log q := log_lt_log hx0 hxq
    have h2 : log (1 - q) < log (1 - x) := log_lt_log (by linarith) (by linarith)
    linarith

/-- `KL(p₂, q) ≤ KL(p₁, q)` for `0 ≤ p₁ ≤ p₂ ≤ q < 1`. -/
lemma klBern_anti (p1 p2 q : ℝ) (hp1 : 0 ≤ p1) (h12 : p1 ≤ p2) (h2q : p2 ≤ q) (hq0 : 0 < q)
    (hq1 : q < 1) :
    RegretBandits.Stochastic.klBern p2 q ≤ RegretBandits.Stochastic.klBern p1 q := by
  rw [klBern_eq _ _ hq0 hq1, klBern_eq _ _ hq0 hq1]
  exact klF_antitone q hq0 hq1 ⟨hp1, h12.trans h2q⟩ ⟨hp1.trans h12, h2q⟩ h12

lemma klBern_self (p : ℝ) : RegretBandits.Stochastic.klBern p p = 0 := by
  unfold RegretBandits.Stochastic.klBern
  by_cases hp : p = 0
  · simp [hp]
  · by_cases hp1 : 1 - p = 0
    · simp [hp1, div_self hp]
    · simp [div_self hp, div_self hp1]

end KL

variable {U K : ℕ}

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

lemma expCount_nonneg (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U)
    (k : Fin K) (t : ℕ) : 0 ≤ expCount π mu u k t :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

lemma sum_Icc_range (f : ℕ → ℝ) (t : ℕ) :
    ∑ s ∈ Finset.Icc 1 t, f s = ∑ s ∈ Finset.range t, f (s + 1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

lemma hist_sched (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) :
    ∀ (n : ℕ) (i : Fin n), (hist π mu ω n i).1 = sched π mu ω (i.val + 1)
  | 0, i => i.elim0
  | n + 1, i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [hist, Fin.snoc_last, Fin.val_last, sched]; rfl
    · simp only [hist, Fin.snoc_castSucc, Fin.val_castSucc]
      exact hist_sched π mu ω n j

lemma count_hist (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (u : Fin U)
    (k : Fin K) (t : ℕ) :
    (count π mu ω u k t : ℝ) =
      ∑ i : Fin t, (if (hist π mu ω t i).1 u = k then (1 : ℝ) else 0) := by
  rw [count_eq, Nat.cast_sum]
  push_cast
  rw [sum_Icc_range (fun s => if sched π mu ω s u = k then (1 : ℝ) else 0) t,
    ← Fin.sum_univ_eq_sum_range (fun s => if sched π mu ω (s + 1) u = k then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hist_sched]

lemma count_total (π : Policy U K) (mu : Fin U → Fin K → ℝ) (ω : ℕ → Seed U K) (u : Fin U)
    (t : ℕ) : ∑ j : Fin K, (count π mu ω u j t : ℝ) = t := by
  simp_rw [count_eq, Nat.cast_sum]
  rw [Finset.sum_comm]
  have : ∀ s ∈ Finset.Icc 1 t, ∑ j : Fin K, ((if sched π mu ω s u = j then 1 else 0 : ℕ) : ℝ) = 1 := by
    intro s _
    push_cast
    rw [Finset.sum_ite_eq]; simp
  rw [Finset.sum_congr rfl this]
  simp

/-- The perturbed instance `μ̂` of the proof of Lemma 19: entries `(u, k)` and `(u', k*_u)` (where
`k*_{u'} = k`, if such `u'` exists) are replaced by `β`. -/
noncomputable def muHat (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) (u : Fin U) (k : Fin K)
    (β : ℝ) : Fin U → Fin K → ℝ :=
  fun v j => if (v = u ∧ j = k) ∨ (kstar v = k ∧ j = kstar u) then β else mu v j

/-- The optimal matching of `μ̂`: `u` and `u'` swap their best servers. -/
def kHat (kstar : Fin U → Fin K) (u : Fin U) (k : Fin K) : Fin U → Fin K :=
  fun v => if v = u then k else if kstar v = k then kstar u else kstar v

lemma kHat_injective (kstar : Fin U → Fin K) (hinj : Function.Injective kstar) (u : Fin U)
    (k : Fin K) (hk : k ≠ kstar u) : Function.Injective (kHat kstar u k) := by
  intro v1 v2 h
  unfold kHat at h
  by_cases h1 : v1 = u <;> by_cases h2 : v2 = u
  · rw [h1, h2]
  · rw [if_pos h1, if_neg h2] at h
    by_cases h3 : kstar v2 = k
    · rw [if_pos h3] at h; exact absurd h hk
    · rw [if_neg h3] at h; exact absurd h.symm h3
  · rw [if_neg h1, if_pos h2] at h
    by_cases h3 : kstar v1 = k
    · rw [if_pos h3] at h; exact absurd h.symm hk
    · rw [if_neg h3] at h; exact absurd h h3
  · rw [if_neg h1, if_neg h2] at h
    by_cases h3 : kstar v1 = k <;> by_cases h4 : kstar v2 = k
    · exact hinj (h3.trans h4.symm)
    · rw [if_pos h3, if_neg h4] at h; exact absurd (hinj h.symm) h2
    · rw [if_neg h3, if_pos h4] at h; exact absurd (hinj h) h1
    · rw [if_neg h3, if_neg h4] at h; exact hinj h

lemma muHat_A1 (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) (hA1 : Assumption1 mu kstar)
    (u : Fin U) (k : Fin K) (hk : k ≠ kstar u) (β : ℝ) (hβ : ∀ v j, mu v j < β) :
    Assumption1 (muHat mu kstar u k β) (kHat kstar u k) := by
  refine ⟨kHat_injective kstar hA1.1 u k hk, ?_⟩
  intro v j hj
  have eβ : ∀ v j, ((v = u ∧ j = k) ∨ (kstar v = k ∧ j = kstar u)) →
      muHat mu kstar u k β v j = β := fun v j h => by unfold muHat; rw [if_pos h]
  have eμ : ∀ v j, ¬((v = u ∧ j = k) ∨ (kstar v = k ∧ j = kstar u)) →
      muHat mu kstar u k β v j = mu v j := fun v j h => by unfold muHat; rw [if_neg h]
  by_cases h1 : v = u
  · subst h1
    have hk' : kHat kstar v k v = k := by simp [kHat]
    rw [hk'] at hj ⊢
    rw [eβ v k (Or.inl ⟨rfl, rfl⟩), eμ v j]
    · exact hβ _ _
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hj h
      · exact hk h.symm
  · by_cases h3 : kstar v = k
    · have hk' : kHat kstar u k v = kstar u := by simp [kHat, h1, h3]
      rw [hk'] at hj ⊢
      rw [eβ v (kstar u) (Or.inr ⟨h3, rfl⟩), eμ v j]
      · exact hβ _ _
      · rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact h1 h
        · exact hj h
    · have hk' : kHat kstar u k v = kstar v := by simp [kHat, h1, h3]
      rw [hk'] at hj ⊢
      have hn : ∀ j', ¬((v = u ∧ j' = k) ∨ (kstar v = k ∧ j' = kstar u)) := by
        rintro j' (⟨h, _⟩ | ⟨h, _⟩)
        · exact h1 h
        · exact h3 h
      rw [eμ v j (hn j), eμ v (kstar v) (hn _)]
      exact hA1.2 v j hj

lemma muHat_bounds (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ v j, 0 ≤ mu v j ∧ mu v j ≤ 1) (u : Fin U) (k : Fin K) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : ∀ v j, 0 ≤ muHat mu kstar u k β v j ∧ muHat mu kstar u k β v j ≤ 1 := by
  intro v j
  unfold muHat
  split_ifs
  · exact ⟨hβ0, hβ1⟩
  · exact hmu v j

lemma le_muStar (mu : Fin U → Fin K → ℝ) (v : Fin U) (j : Fin K) : mu v j ≤ muStar mu := by
  unfold muStar
  rw [dif_pos ⟨(v, j), Finset.mem_univ _⟩]
  exact Finset.le_sup' (fun p : Fin U × Fin K => mu p.1 p.2) (Finset.mem_univ (v, j))

lemma muMin_le (mu : Fin U → Fin K → ℝ) (v : Fin U) (j : Fin K) : muMin mu ≤ mu v j := by
  unfold muMin
  rw [dif_pos ⟨(v, j), Finset.mem_univ _⟩]
  exact Finset.inf'_le (fun p : Fin U × Fin K => mu p.1 p.2) (Finset.mem_univ (v, j))

lemma muMin_nonneg (mu : Fin U → Fin K → ℝ) (hmu : ∀ v j, 0 ≤ mu v j ∧ mu v j ≤ 1) :
    0 ≤ muMin mu := by
  unfold muMin
  split_ifs with h
  · rw [Finset.le_inf'_iff]; intro p _; exact (hmu p.1 p.2).1
  · exact le_rfl

/-- Markov's inequality for a nonnegative integrable function, strict-threshold form. -/
lemma markov_lt {α : Type*} [MeasurableSpace α] (m : Measure α) [IsFiniteMeasure m] (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f m) (a : ℝ) (ha : 0 < a) :
    m.real {x | a < f x} ≤ (∫ x, f x ∂m) / a := by
  rw [le_div_iff₀ ha, mul_comm]
  calc a * m.real {x | a < f x} ≤ a * m.real {x | a ≤ f x} := by
        apply mul_le_mul_of_nonneg_left _ ha.le
        exact measureReal_mono (fun x (hx : x ∈ {x | a < f x}) => show a ≤ f x from le_of_lt hx)
    _ ≤ ∫ x, f x ∂m := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hfi a

lemma markov_le {α : Type*} [MeasurableSpace α] (m : Measure α) [IsFiniteMeasure m] (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f m) (a : ℝ) (ha : 0 < a) :
    m.real {x | a ≤ f x} ≤ (∫ x, f x ∂m) / a := by
  rw [le_div_iff₀ ha, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hfi a

end QB3L19

open QB3L19 in
theorem solution {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (hU : 0 < U)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : QueueBandit.LateLower.Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (π : QueueBandit.LateLower.Policy U K)
    (hπ : QueueBandit.LateLower.IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : Fin U, ∀ k : Fin K, k ≠ kstar u → ∀ t : ℕ, τ < t →
      QueueBandit.LateLower.invKL mu * ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        QueueBandit.LateLower.expCount π mu u k t +
          ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
            (if kstar u' = k then QueueBandit.LateLower.expCount π mu u' (kstar u) t else 0) := by
  classical
  have hX0 : ∀ (u : Fin U) (k : Fin K) (t : ℕ), 0 ≤ expCount π mu u k t +
      ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
        (if kstar u' = k then expCount π mu u' (kstar u) t else 0) := by
    intro u k t
    apply add_nonneg (expCount_nonneg π mu u k t)
    apply Finset.sum_nonneg
    intro u' _
    split_ifs
    · exact expCount_nonneg π mu _ _ t
    · exact le_rfl
  by_cases hstar : muStar mu < 1
  swap
  · refine ⟨0, 1, one_pos, fun u k _ t _ => ?_⟩
    have : invKL mu = 0 := by unfold invKL; rw [if_neg hstar]
    rw [this, zero_mul]
    exact hX0 u k t
  -- the main case `μ* < 1`
  set β : ℝ := (muStar mu + 1) / 2 with hβdef
  have hmuβ : ∀ v j, mu v j < β := fun v j => by
    have := le_muStar mu v j; rw [hβdef]; linarith
  have hstar0 : 0 ≤ muStar mu := le_trans (hmu ⟨0, hU⟩ ⟨0, by omega⟩).1 (le_muStar mu _ _)
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hmin0 := muMin_nonneg mu hmu
  have hminβ : muMin mu ≤ β := (muMin_le mu ⟨0, hU⟩ ⟨0, by omega⟩).trans (hmuβ _ _).le
  set klmin := RegretBandits.Stochastic.klBern (muMin mu) β with hklmin
  have hklmin0 : 0 ≤ klmin := by
    have := klBern_anti (muMin mu) β β hmin0 hminβ le_rfl hβ0 hβ1
    rw [klBern_self] at this; exact this
  have hkl_le : ∀ v j, RegretBandits.Stochastic.klBern (mu v j) β ≤ klmin := fun v j =>
    klBern_anti (muMin mu) (mu v j) β hmin0 (muMin_le mu v j) (hmuβ v j).le hβ0 hβ1
  have hinvKL : invKL mu = klmin⁻¹ := by unfold invKL; rw [if_pos hstar]
  -- consistency constants
  obtain ⟨C0, hC0⟩ := hπ mu kstar hmu hA1
  have hex : ∀ (u : Fin U) (k : Fin K), ∃ C : ℝ, k ≠ kstar u → ∀ t : ℕ, 1 ≤ t → ∀ v j,
      j ≠ kHat kstar u k v → expCount π (muHat mu kstar u k β) v j t ≤ C * (t : ℝ) ^ α := by
    intro u k
    by_cases hk : k ≠ kstar u
    · obtain ⟨C, hC⟩ := hπ (muHat mu kstar u k β) (kHat kstar u k)
        (muHat_bounds mu kstar hmu u k β hβ0.le hβ1.le) (muHat_A1 mu kstar hA1 u k hk β hmuβ)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Ch hCh using hex
  set C : ℝ := 1 + |C0| + ∑ u : Fin U, ∑ k : Fin K, |Ch u k| with hCdef
  have hsum0 : 0 ≤ ∑ u : Fin U, ∑ k : Fin K, |Ch u k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC0le : C0 ≤ C := by rw [hCdef]; linarith [le_abs_self C0]
  have hChle : ∀ u k, Ch u k ≤ C := by
    intro u k
    have h1 : |Ch u k| ≤ ∑ k' : Fin K, |Ch u k'| :=
      Finset.single_le_sum (f := fun k' => |Ch u k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k' : Fin K, |Ch u k'| ≤ ∑ u' : Fin U, ∑ k' : Fin K, |Ch u' k'| :=
      Finset.single_le_sum (f := fun u' => ∑ k' : Fin K, |Ch u' k'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u)
    rw [hCdef]; linarith [le_abs_self (Ch u k), abs_nonneg C0]
  refine ⟨0, C, hCpos, fun u k hk t ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have htα : 0 ≤ (t : ℝ) ^ α := Real.rpow_nonneg htpos.le α
  set μh := muHat mu kstar u k β with hμh
  -- the event `T_uk(t+1) > t/2`, as a set of histories
  set S : Set (History U K t) := {h | (t : ℝ) / 2 <
    ∑ i : Fin t, (if (h i).1 u = k then (1 : ℝ) else 0)} with hS
  have hBH := QueueBandit.EarlyLower.history_bretagnolle_huber π mu μh hmu
    (muHat_bounds mu kstar hmu u k β hβ0.le hβ1.le)
    (fun v j hne => by
      have : μh v j = β := by
        by_contra hb
        apply hne
        simp only [hμh, muHat] at hb ⊢
        split_ifs at hb ⊢ with hc
        · exact absurd rfl hb
        · rfl
      rw [this]; exact ⟨hβ0, hβ1⟩) t S
  -- Markov under `μ`
  have hPa : (seedMeasure U K).real {ω | hist π mu ω t ∈ S} ≤
      expCount π mu u k t / ((t : ℝ) / 2) := by
    have hset : {ω | hist π mu ω t ∈ S} = {ω | (t : ℝ) / 2 < (count π mu ω u k t : ℝ)} := by
      ext ω; simp only [hS, Set.mem_setOf_eq, count_hist]
    rw [hset]
    exact markov_lt _ _ (fun _ => Nat.cast_nonneg _) (count_integrable π mu u k t) _ (by positivity)
  -- Markov under `μ̂`
  have hPb : (seedMeasure U K).real {ω | hist π μh ω t ∉ S} ≤
      (∑ j ∈ Finset.univ.erase k, expCount π μh u j t) / ((t : ℝ) / 2) := by
    have hset : {ω | hist π μh ω t ∉ S} ⊆
        {ω | (t : ℝ) / 2 ≤ ∑ j ∈ Finset.univ.erase k, (count π μh ω u j t : ℝ)} := by
      intro ω hω
      simp only [hS, Set.mem_setOf_eq, not_lt, ← count_hist] at hω ⊢
      have htot := count_total π μh ω u t
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at htot
      linarith
    have hint : Integrable (fun ω => ∑ j ∈ Finset.univ.erase k, (count π μh ω u j t : ℝ))
        (seedMeasure U K) := integrable_finsetSum _ (fun j _ => count_integrable π μh u j t)
    calc (seedMeasure U K).real {ω | hist π μh ω t ∉ S}
        ≤ (seedMeasure U K).real
            {ω | (t : ℝ) / 2 ≤ ∑ j ∈ Finset.univ.erase k, (count π μh ω u j t : ℝ)} :=
          measureReal_mono hset
      _ ≤ _ := by
          have := markov_le _ _ (fun ω => Finset.sum_nonneg fun j _ => Nat.cast_nonneg _) hint _
            (by positivity : (0 : ℝ) < (t : ℝ) / 2)
          rw [integral_finsetSum _ (fun j _ => count_integrable π μh u j t)] at this
          exact this
  -- consistency bounds
  have hEuk : expCount π mu u k t ≤ C * (t : ℝ) ^ α :=
    (hC0 t ht u k hk).trans (mul_le_mul_of_nonneg_right hC0le htα)
  have hEh : ∑ j ∈ Finset.univ.erase k, expCount π μh u j t ≤ ((K : ℝ) - 1) * (C * (t : ℝ) ^ α) := by
    have hkh : kHat kstar u k u = k := by simp [kHat]
    have : ∀ j ∈ Finset.univ.erase k, expCount π μh u j t ≤ C * (t : ℝ) ^ α := by
      intro j hj
      have hj' : j ≠ kHat kstar u k u := by rw [hkh]; exact Finset.ne_of_mem_erase hj
      exact (hCh u k hk t ht u j hj').trans (mul_le_mul_of_nonneg_right (hChle u k) htα)
    calc _ ≤ ∑ j ∈ Finset.univ.erase k, C * (t : ℝ) ^ α := Finset.sum_le_sum this
      _ = ((K : ℝ) - 1) * (C * (t : ℝ) ^ α) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
        simp
  -- the divergence bound
  set X := expCount π mu u k t + ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
      (if kstar u' = k then expCount π mu u' (kstar u) t else 0) with hX
  set D := ∑ v : Fin U, ∑ j : Fin K, RegretBandits.Stochastic.klBern (mu v j) (μh v j) *
      expCount π mu v j t with hD
  have hDX : D ≤ klmin * X := by
    set E := fun v j => expCount π mu v j t with hE
    have hE0 : ∀ v j, 0 ≤ E v j := fun v j => expCount_nonneg π mu v j t
    have hpt : ∀ v j, RegretBandits.Stochastic.klBern (mu v j) (μh v j) * E v j ≤
        klmin * ((if v = u ∧ j = k then E v j else 0) +
          (if kstar v = k ∧ j = kstar u then E v j else 0)) := by
      intro v j
      have hi1 : 0 ≤ (if v = u ∧ j = k then E v j else 0) := by split_ifs <;> simp [hE0]
      have hi2 : 0 ≤ (if kstar v = k ∧ j = kstar u then E v j else 0) := by
        split_ifs <;> simp [hE0]
      by_cases hc : (v = u ∧ j = k) ∨ (kstar v = k ∧ j = kstar u)
      · have hμ : μh v j = β := by simp only [hμh, muHat]; rw [if_pos hc]
        rw [hμ]
        have hsum : E v j ≤ (if v = u ∧ j = k then E v j else 0) +
            (if kstar v = k ∧ j = kstar u then E v j else 0) := by
          rcases hc with h | h
          · rw [if_pos h]; linarith
          · rw [if_pos h (c := kstar v = k ∧ j = kstar u)]; linarith
        calc RegretBandits.Stochastic.klBern (mu v j) β * E v j ≤ klmin * E v j :=
              mul_le_mul_of_nonneg_right (hkl_le v j) (hE0 v j)
          _ ≤ _ := mul_le_mul_of_nonneg_left hsum hklmin0
      · have hμ : μh v j = mu v j := by simp only [hμh, muHat]; rw [if_neg hc]
        rw [hμ, klBern_self, zero_mul]
        exact mul_nonneg hklmin0 (add_nonneg hi1 hi2)
    have h1 : D ≤ ∑ v : Fin U, ∑ j : Fin K, klmin * ((if v = u ∧ j = k then E v j else 0) +
          (if kstar v = k ∧ j = kstar u then E v j else 0)) :=
      Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun j _ => hpt v j
    have h2 : ∑ v : Fin U, ∑ j : Fin K, (if v = u ∧ j = k then E v j else 0) = E u k := by
      rw [Finset.sum_eq_single u, Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [hj]
      · simp
      · intro v _ hv; apply Finset.sum_eq_zero; intro j _; simp [hv]
      · simp
    have h3 : ∑ v : Fin U, ∑ j : Fin K, (if kstar v = k ∧ j = kstar u then E v j else 0) =
        ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
          (if kstar u' = k then expCount π mu u' (kstar u) t else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_eq_single (kstar u)]
      · by_cases hv : v = u
        · subst hv; simp [Ne.symm hk]
        · simp [hv, hE]
      · intro j _ hj; simp [hj]
      · simp
    simp_rw [← Finset.mul_sum, Finset.sum_add_distrib] at h1
    rw [h2, h3] at h1
    rw [hX]
    exact h1
  -- combine
  have hmain : (1 / 2 : ℝ) * Real.exp (-D) ≤ 2 * K * C * (t : ℝ) ^ α / t := by
    have h1 := hBH
    have h2 : expCount π mu u k t / ((t : ℝ) / 2) +
        (∑ j ∈ Finset.univ.erase k, expCount π μh u j t) / ((t : ℝ) / 2) ≤
        2 * K * C * (t : ℝ) ^ α / t := by
      rw [← add_div, div_le_div_iff₀ (by positivity) htpos]
      nlinarith
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hA : 0 < 4 * K * C * (t : ℝ) ^ (α - 1) := by positivity
  have hexp : Real.exp (-D) ≤ 4 * K * C * (t : ℝ) ^ (α - 1) := by
    rw [Real.rpow_sub_one htpos.ne']
    have : 2 * K * C * (t : ℝ) ^ α / t * 2 = 4 * K * C * ((t : ℝ) ^ α / t) := by ring
    linarith
  have hlog : -D ≤ Real.log (4 * K * C) + (α - 1) * Real.log t := by
    have := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp, Real.log_mul (by positivity) (Real.rpow_pos_of_pos htpos _).ne',
      Real.log_rpow htpos] at this
    exact this
  have hL : (1 - α) * Real.log t - Real.log (4 * K * C) ≤ klmin * X := by linarith
  rw [hinvKL]
  rcases hklmin0.lt_or_eq with hpos | hzero
  · rw [inv_mul_le_iff₀ hpos]; linarith
  · rw [← hzero, inv_zero, zero_mul]; exact hX0 u k t
