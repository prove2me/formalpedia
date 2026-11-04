-- Prove2me | solution 1 for QueueBandit.LateLower.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:59:42.196141+00:00
-- url     : https://prove2.me/submissions/3af2a816-f265-413f-a2e5-27a4e70ece79
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance
import Definitions.Def_QueueBandit_LateLower_Dynamics
import Theorems.Thm_QueueBandit_LateLower_corollary_20
import Theorems.Thm_QueueBandit_LateLower_lemma_21
import Theorems.Thm_QueueBandit_LateLower_fact_1

open MeasureTheory Finset Filter

namespace QBThm3Aux

open QueueBandit.LateLower

variable {U K : ℕ}

theorem measurableSet_offered (mu : Fin U → Fin K → ℝ) (t : ℕ) (u : Fin U) (k : Fin K)
    (b : Bool) :
    MeasurableSet {ω : ℕ → Seed U K | decide (offered mu ω t u k = 1) = b} := by
  have hS : MeasurableSet {ω : ℕ → Seed U K | (((ω t).2.1 u k : ℝ)) ≤ mu u k} := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp ((measurable_pi_apply k).comp
      ((measurable_pi_apply u).comp (measurable_fst.comp (measurable_snd.comp
        (measurable_pi_apply t)))))
  have hm : Measurable (fun ω : ℕ → Seed U K => offered mu ω t u k) := by
    unfold offered
    exact Measurable.ite hS measurable_const measurable_const
  exact ((measurable_from_nat (f := fun j : ℕ => decide (j = 1))).comp hm)
    (measurableSet_singleton b)

theorem measurableSet_hist (π : Policy U K) (mu : Fin U → Fin K → ℝ) :
    ∀ (n : ℕ) (h : History U K n), MeasurableSet {ω : ℕ → Seed U K | hist π mu ω n = h} := by
  intro n
  induction n with
  | zero =>
    intro h
    have : {ω : ℕ → Seed U K | hist π mu ω 0 = h} = Set.univ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; funext i; exact i.elim0
    rw [this]; exact MeasurableSet.univ
  | succ n ih =>
    intro h
    have hseed : Measurable (fun ω : ℕ → Seed U K => (ω (n + 1)).2.2) :=
      measurable_snd.comp (measurable_snd.comp (measurable_pi_apply (n + 1)))
    have heq : {ω : ℕ → Seed U K | hist π mu ω (n + 1) = h} =
        ⋃ h' : History U K n, ⋃ m : Matching U K, ⋃ b : Fin U → Bool,
          ({ω | hist π mu ω n = h'} ∩ ((fun ω : ℕ → Seed U K => (ω (n + 1)).2.2) ⁻¹'
              {x | π.act n h' x = m}) ∩
            (⋂ u : Fin U, {ω | decide (offered mu ω (n + 1) u (m u) = 1) = b u})) ∩
            {_ω | Fin.snoc (α := fun _ => Obs U K) h' (m, b) = h} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_iInter]
      constructor
      · intro H
        refine ⟨hist π mu ω n, π.act n (hist π mu ω n) (ω (n + 1)).2.2,
          fun u => decide (offered mu ω (n + 1) u (π.act n (hist π mu ω n) (ω (n + 1)).2.2 u) = 1),
          ⟨⟨rfl, rfl⟩, fun u => rfl⟩, ?_⟩
        rw [← H]; rfl
      · rintro ⟨h', m, b, ⟨⟨h1, h2⟩, h3⟩, h4⟩
        rw [← h4]
        show Fin.snoc (α := fun _ => Obs U K) (hist π mu ω n) _ = _
        rw [h1]
        congr 1
        rw [h2]
        refine Prod.ext rfl ?_
        funext u
        exact h3 u
    rw [heq]
    refine MeasurableSet.iUnion fun h' => MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun b => ?_
    refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter (ih h') ?_) ?_)
      (MeasurableSet.const _)
    · exact hseed (π.measurableSet_act n h' m)
    · exact MeasurableSet.iInter fun u => measurableSet_offered mu (n + 1) u (m u) (b u)

theorem measurableSet_sched (π : Policy U K) (mu : Fin U → Fin K → ℝ) (t : ℕ) (u : Fin U)
    (k : Fin K) : MeasurableSet {ω : ℕ → Seed U K | sched π mu ω t u = k} := by
  have hseed : Measurable (fun ω : ℕ → Seed U K => (ω t).2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_pi_apply t))
  have heq : {ω : ℕ → Seed U K | sched π mu ω t u = k} =
      ⋃ h' : History U K (t - 1), ⋃ m : Matching U K,
        ({ω | hist π mu ω (t - 1) = h'} ∩ ((fun ω : ℕ → Seed U K => (ω t).2.2) ⁻¹'
            {x | π.act (t - 1) h' x = m})) ∩ {_ω | m u = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · intro H
      exact ⟨_, _, ⟨rfl, rfl⟩, H⟩
    · rintro ⟨h', m, ⟨h1, h2⟩, h3⟩
      unfold sched
      rw [h1, h2]; exact h3
  rw [heq]
  exact MeasurableSet.iUnion fun h' => MeasurableSet.iUnion fun m =>
    ((ih_aux h' m)).inter (MeasurableSet.const _)
where
  ih_aux (h' : History U K (t - 1)) (m : Matching U K) :
      MeasurableSet ({ω : ℕ → Seed U K | hist π mu ω (t - 1) = h'} ∩
        ((fun ω : ℕ → Seed U K => (ω t).2.2) ⁻¹' {x | π.act (t - 1) h' x = m})) :=
    (measurableSet_hist π mu (t - 1) h').inter
      ((measurable_snd.comp (measurable_snd.comp (measurable_pi_apply t)))
        (π.measurableSet_act (t - 1) h' m))


theorem sum_prob_eq_expCount (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K) (n : ℕ) :
    ∑ m ∈ Icc 1 n, (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k} =
      expCount π mu u k n := by
  have hprod : ∀ m, (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k} =
      (seedMeasure U K).real {ω | sched π mu ω m u = k} := by
    intro m
    have : {x : (Fin U → ℕ) × (ℕ → Seed U K) | sched π mu x.2 m u = k} =
        (Set.univ : Set (Fin U → ℕ)) ×ˢ {ω | sched π mu ω m u = k} := by
      ext x; simp
    rw [this, sysMeasure, measureReal_def, Measure.prod_prod, measure_univ, one_mul,
      measureReal_def]
  simp_rw [hprod]
  unfold expCount count
  have hc : ∀ ω : ℕ → Seed U K,
      ((((Icc 1 n).filter fun s => sched π mu ω s u = k).card : ℕ) : ℝ) =
        ∑ m ∈ Icc 1 n, ({ω' : ℕ → Seed U K | sched π mu ω' m u = k}.indicator 1 ω : ℝ) := by
    intro ω
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : sched π mu ω m u = k
    · simp [h, Set.indicator_of_mem (show ω ∈ {ω' : ℕ → Seed U K | sched π mu ω' m u = k} from h)]
    · simp [h, Set.indicator_of_notMem (show ω ∉ {ω' : ℕ → Seed U K | sched π mu ω' m u = k} from h)]
  simp_rw [hc]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_indicator_one (measurableSet_sched π mu m u k)]
  · intro m _
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_sched π mu m u k)

theorem expCount_nonneg (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K)
    (n : ℕ) : 0 ≤ expCount π mu u k n :=
  integral_nonneg fun _ => Nat.cast_nonneg _

theorem lamMin_le (hU : 0 < U) (lam : Fin U → ℝ) (u : Fin U) : lamMin lam ≤ lam u := by
  unfold lamMin
  rw [dif_pos (univ_nonempty_iff.mpr ⟨u⟩)]
  exact inf'_le _ (mem_univ u)

theorem lamMin_nonneg (lam : Fin U → ℝ) (h : ∀ u, 0 ≤ lam u) : 0 ≤ lamMin lam := by
  unfold lamMin
  split_ifs with hne
  · exact le_inf' _ _ fun u _ => h u
  · exact le_rfl

theorem gapMin_le (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) (u : Fin U) (k : Fin K)
    (hk : k ≠ kstar u) : gapMin mu kstar ≤ gap mu kstar u k := by
  have hmem : (u, k) ∈ subPairs kstar := by simp [subPairs, hk]
  unfold gapMin
  rw [dif_pos ⟨_, hmem⟩]
  exact inf'_le (fun p => gap mu kstar p.1 p.2) hmem

theorem gapMin_nonneg (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hA1 : Assumption1 mu kstar) : 0 ≤ gapMin mu kstar := by
  unfold gapMin
  split_ifs with hne
  · refine le_inf' _ _ fun p hp => ?_
    have hp' : p.2 ≠ kstar p.1 := by simpa [subPairs] using hp
    have := hA1.2 p.1 p.2 hp'
    unfold gap; linarith
  · exact le_rfl

/-- Summing Lemma 21 over the first `n` slots. -/
theorem sum_regret_ge (hU : 0 < U) (hUK : U ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hinst : IsInstance lam mu kstar) (hA2 : ∀ u, lam u < mu u (kstar u))
    (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (π : Policy U K) (u : Fin U) (n : ℕ) :
    lamMin lam * gapMin mu kstar * ∑ k ∈ univ.erase (kstar u), expCount π mu u k n ≤
      ∑ m ∈ Icc 1 n, queueRegret lam mu kstar ν π u m := by
  have hlm0 := lamMin_nonneg lam fun v => (hinst.1 v).1
  have hgm0 := gapMin_nonneg mu kstar hinst.2.2
  have hlu := lamMin_le hU lam u
  have hstep : ∀ m ∈ Icc 1 n, lamMin lam * gapMin mu kstar *
      ∑ k ∈ univ.erase (kstar u), (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k} ≤
      queueRegret lam mu kstar ν π u m := by
    intro m hm
    have h21 := lemma_21 hUK lam mu kstar hinst hA2 ν π u m (mem_Icc.mp hm).1
    refine le_trans ?_ h21
    have hP : 0 ≤ ∑ k ∈ univ.erase (kstar u),
        (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k} :=
      sum_nonneg fun _ _ => measureReal_nonneg
    have h1 : gapMin mu kstar * ∑ k ∈ univ.erase (kstar u),
          (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k} ≤
        ∑ k ∈ univ.erase (kstar u),
          gap mu kstar u k * (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k} := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      exact mul_le_mul_of_nonneg_right (gapMin_le mu kstar u k (ne_of_mem_erase hk))
        measureReal_nonneg
    calc lamMin lam * gapMin mu kstar * ∑ k ∈ univ.erase (kstar u),
          (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k}
        = lamMin lam * (gapMin mu kstar * ∑ k ∈ univ.erase (kstar u),
          (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k}) := by ring
      _ ≤ lam u * (gapMin mu kstar * ∑ k ∈ univ.erase (kstar u),
          (sysMeasure (K := K) ν).real {x | sched π mu x.2 m u = k}) :=
          mul_le_mul_of_nonneg_right hlu (mul_nonneg hgm0 hP)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (hinst.1 u).1
  calc lamMin lam * gapMin mu kstar * ∑ k ∈ univ.erase (kstar u), expCount π mu u k n
      = ∑ m ∈ Icc 1 n, lamMin lam * gapMin mu kstar *
          ∑ k ∈ univ.erase (kstar u), (sysMeasure (K := K) ν).real
            {x | sched π mu x.2 m u = k} := by
        simp_rw [← sum_prob_eq_expCount ν π mu u _ n]
        rw [Finset.sum_comm, ← mul_sum]
    _ ≤ _ := sum_le_sum hstep

/-- Queue-regret is nonnegative in every slot `t ≥ 1` (from Lemma 21). -/
theorem regret_nonneg (hUK : U ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hinst : IsInstance lam mu kstar) (hA2 : ∀ u, lam u < mu u (kstar u))
    (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (π : Policy U K) (u : Fin U) (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ queueRegret lam mu kstar ν π u t := by
  refine le_trans ?_ (lemma_21 hUK lam mu kstar hinst hA2 ν π u t ht)
  refine mul_nonneg (hinst.1 u).1 (sum_nonneg fun k hk => mul_nonneg ?_ measureReal_nonneg)
  have := hinst.2.2.2 u k (ne_of_mem_erase hk)
  unfold gap; linarith

/-- Conclusion via Fact 1. -/
theorem freq_of_sum (a : ℕ → ℝ) (c : ℝ) (h0 : ∀ t, 1 ≤ t → 0 ≤ a t)
    (hsum : 0 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 2 * c * Real.log n ≤ ∑ m ∈ Icc 1 n, a m) :
    ∃ᶠ t : ℕ in atTop, c * (1 / (t : ℝ)) ≤ a t := by
  by_cases hc : c ≤ 0
  · refine Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hc (by positivity)) (h0 t ht)
  · push Not at hc
    obtain ⟨N₀, hN⟩ := hsum hc
    have := fact_1 a (2 * c) (by linarith) N₀ hN
    refine this.mono fun t ht => ?_
    have : 2 * c / (2 * (t : ℝ)) = c * (1 / (t : ℝ)) := by
      rcases eq_or_ne (t : ℝ) 0 with h | h
      · simp [h]
      · field_simp
    linarith

/-- Turning `L B(n) ≤ S n` into `L (1-α)/2 log n ≤ S n` for large `n`. -/
theorem log_bound (L α κ : ℝ) (hL : 0 ≤ L) (hα1 : α < 1) (τ : ℕ) (S : ℕ → ℝ)
    (hS : ∀ n : ℕ, τ < n → L * ((1 - α) * Real.log n - κ) ≤ S n) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → L * (1 - α) / 2 * Real.log n ≤ S n := by
  have h1 : ∀ᶠ n : ℕ in atTop, 2 * κ / (1 - α) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have h2 : ∀ᶠ n : ℕ in atTop, τ < n := eventually_gt_atTop τ
  obtain ⟨N₀, hN⟩ := eventually_atTop.mp (h1.and h2)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hlog, hτ⟩ := hN n hn
  refine le_trans ?_ (hS n hτ)
  have hpos : 0 < 1 - α := by linarith
  have hk : κ ≤ (1 - α) / 2 * Real.log n := by
    rw [div_le_iff₀ hpos] at hlog; linarith
  have : (1 - α) / 2 * Real.log n ≤ (1 - α) * Real.log n - κ := by linarith
  calc L * (1 - α) / 2 * Real.log n = L * ((1 - α) / 2 * Real.log n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hL

end QBThm3Aux

open QueueBandit.LateLower in
theorem solution {U K : ℕ} (hU : 0 < U) (hUK : U ≤ K) (hK : 2 ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hinst : IsInstance lam mu kstar) (hA2 : ∀ u, lam u < mu u (kstar u))
    (ν : Measure (Fin U → ℕ)) [IsProbabilityMeasure ν]
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : Policy U K) (hπ : IsAlphaConsistent π α) :
    (∃ᶠ t : ℕ in atTop,
      lamMin lam / 8 * D mu kstar * (1 - α) * ((K : ℝ) - 1) * (1 / (t : ℝ)) ≤
        (1 / (U : ℝ)) * ∑ u, queueRegret lam mu kstar ν π u t) ∧
    ∀ u : Fin U, ∃ᶠ t : ℕ in atTop,
      lamMin lam / 8 * D mu kstar * (1 - α) * max ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) *
          (1 / (t : ℝ)) ≤
        queueRegret lam mu kstar ν π u t := by
  obtain ⟨τ, C, hC, hcor⟩ :=
    corollary_20 hU hUK hK mu kstar hinst.2.1 hinst.2.2 α hα0 hα1 π hπ
  have hlm0 := QBThm3Aux.lamMin_nonneg lam fun v => (hinst.1 v).1
  have hgm0 := QBThm3Aux.gapMin_nonneg mu kstar hinst.2.2
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hpos1 : 0 < 1 - α := by linarith
  have hsr := QBThm3Aux.sum_regret_ge hU hUK lam mu kstar hinst hA2 ν π
  have hnn := QBThm3Aux.regret_nonneg hUK lam mu kstar hinst hA2 ν π
  constructor
  · refine QBThm3Aux.freq_of_sum _ _ (fun t ht => ?_) (fun hc => ?_)
    · exact mul_nonneg (by positivity) (sum_nonneg fun u _ => hnn u t ht)
    · set L := lamMin lam * ((K : ℝ) - 1) * D mu kstar / 2 with hLdef
      have hL : 0 ≤ L := by
        have : 0 < L * (1 - α) := by
          have : lamMin lam / 8 * D mu kstar * (1 - α) * ((K : ℝ) - 1) =
            L * (1 - α) / 4 := by rw [hLdef]; ring
          linarith
        exact (pos_of_mul_pos_left this hpos1.le).le
      have hS : ∀ n : ℕ, τ < n → L * ((1 - α) * Real.log n - Real.log (4 * K * C)) ≤
          ∑ m ∈ Icc 1 n, (1 / (U : ℝ)) * ∑ u, queueRegret lam mu kstar ν π u m := by
        intro n hn
        have ha := (hcor n hn).1
        rw [← mul_sum, Finset.sum_comm]
        have hs : ∑ u, lamMin lam * gapMin mu kstar *
            ∑ k ∈ univ.erase (kstar u), expCount π mu u k n ≤
            ∑ u, ∑ m ∈ Icc 1 n, queueRegret lam mu kstar ν π u m :=
          sum_le_sum fun u _ => hsr u n
        rw [← mul_sum] at hs
        have hB := mul_le_mul_of_nonneg_left ha (show 0 ≤ lamMin lam / 2 by positivity)
        have e2 : L * ((1 - α) * Real.log n - Real.log (4 * K * C)) =
            (1 / (U : ℝ)) * (lamMin lam / 2 * ((U : ℝ) * ((K : ℝ) - 1) * D mu kstar *
              ((1 - α) * Real.log n - Real.log (4 * K * C)))) := by
          rw [hLdef]; field_simp
        rw [e2]
        refine mul_le_mul_of_nonneg_left (le_trans hB (le_of_eq_of_le ?_ hs)) (by positivity)
        ring
      obtain ⟨N₀, hN⟩ := QBThm3Aux.log_bound L α (Real.log (4 * K * C)) hL hα1 τ _ hS
      refine ⟨N₀, fun n hn => ?_⟩
      have := hN n hn
      have e : 2 * (lamMin lam / 8 * D mu kstar * (1 - α) * ((K : ℝ) - 1)) * Real.log n =
        L * (1 - α) / 2 * Real.log n := by rw [hLdef]; ring
      linarith
  · intro u
    refine QBThm3Aux.freq_of_sum _ _ (fun t ht => hnn u t ht) (fun hc => ?_)
    set M := max ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) with hMdef
    set L := lamMin lam * M * D mu kstar / 2 with hLdef
    have hL : 0 ≤ L := by
      have : 0 < L * (1 - α) := by
        have : lamMin lam / 8 * D mu kstar * (1 - α) * M = L * (1 - α) / 4 := by
          rw [hLdef]; ring
        linarith
      exact (pos_of_mul_pos_left this hpos1.le).le
    have hLD : 0 ≤ lamMin lam * D mu kstar := by
      have hM : 0 < M := by
        have : (1 : ℝ) ≤ U := by exact_mod_cast hU
        have hKU : (U : ℝ) ≤ K := by exact_mod_cast hUK
        rcases eq_or_lt_of_le this with h | h
        · have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
          exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
        · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have : 0 ≤ lamMin lam * D mu kstar * M := by
        have : lamMin lam * D mu kstar * M = 2 * L := by rw [hLdef]; ring
        linarith
      exact nonneg_of_mul_nonneg_left this hM
    have hS : ∀ n : ℕ, τ < n → L * ((1 - α) * Real.log n - Real.log (4 * K * C)) ≤
        ∑ m ∈ Icc 1 n, queueRegret lam mu kstar ν π u m := by
      intro n hn
      obtain ⟨_, hb, hcc⟩ := hcor n hn
      refine le_trans ?_ (hsr u n)
      set B := (1 - α) * Real.log n - Real.log (4 * K * C) with hBdef
      set E := ∑ k ∈ univ.erase (kstar u), expCount π mu u k n with hEdef
      have hsub : ∑ k ∈ univ.filter (fun k => ∀ u', kstar u' ≠ k), expCount π mu u k n ≤ E := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => QBThm3Aux.expCount_nonneg _ _ _ _ _
        intro k hk
        simp only [mem_filter, mem_univ, true_and] at hk
        exact mem_erase.mpr ⟨fun h => hk u h.symm, mem_univ _⟩
      have hgE : M * D mu kstar * B / 2 ≤ gapMin mu kstar * E := by
        rcases le_total ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) with h | h
        · rw [hMdef, max_eq_right h]
          have := hcc u
          have := mul_le_mul_of_nonneg_left hsub hgm0
          linarith
        · rw [hMdef, max_eq_left h]
          have := hb u
          linarith
      calc L * B = lamMin lam * (M * D mu kstar * B / 2) := by rw [hLdef]; ring
        _ ≤ lamMin lam * (gapMin mu kstar * E) := mul_le_mul_of_nonneg_left hgE hlm0
        _ = _ := by ring
    obtain ⟨N₀, hN⟩ := QBThm3Aux.log_bound L α (Real.log (4 * K * C)) hL hα1 τ _ hS
    refine ⟨N₀, fun n hn => ?_⟩
    have := hN n hn
    have e : 2 * (lamMin lam / 8 * D mu kstar * (1 - α) * M) * Real.log n =
        L * (1 - α) / 2 * Real.log n := by
      rw [hLdef]; ring
    linarith
