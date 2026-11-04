-- Prove2me | solution 1 for QueueBandit.EarlyLower.corollary_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:01:02.603047+00:00
-- url     : https://prove2.me/submissions/fd53fa96-b81c-46ca-91ca-e268b0ac2da5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics
import Theorems.Thm_QueueBandit_EarlyLower_lemma_19

open QueueBandit.LateLower QueueBandit.EarlyLower MeasureTheory

namespace QB3Cor20

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

/-- Pointwise matching inequality: in each slot at most one other queue is served by `k*_u`, and
then queue `u` is served by a server other than `k*_u`. -/
lemma count_matching (π : Policy U K) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (ω : ℕ → Seed U K) (u : Fin U) (t : ℕ) :
    ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u), count π mu ω u' (kstar u) t ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), count π mu ω u k t := by
  simp_rw [count_eq]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ.filter (fun k : Fin K => k ≠ kstar u))]
  apply Finset.sum_le_sum
  intro s _
  set κ := sched π mu ω s
  by_cases hκ : κ u = kstar u
  · have : ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
        (if κ u' = kstar u then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u' hu'
      have hne : u' ≠ u := (Finset.mem_filter.1 hu').2
      have : κ u' ≠ kstar u := by
        rw [← hκ]; exact fun h => hne (κ.injective h)
      simp [this]
    rw [this]; exact Nat.zero_le _
  · have hR : ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        (if κ u = k then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq]
      simp [hκ]
    rw [hR, ← Finset.card_filter]
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact κ.injective (ha.2.trans hb.2.symm)

lemma expCount_matching (π : Policy U K) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (u : Fin U) (t : ℕ) :
    ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u), expCount π mu u' (kstar u) t ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), expCount π mu u k t := by
  unfold expCount
  rw [← integral_finsetSum _ (fun i _ => count_integrable π mu i _ t),
    ← integral_finsetSum _ (fun i _ => count_integrable π mu u i t)]
  apply integral_mono (integrable_finsetSum _ (fun i _ => count_integrable π mu i _ t))
    (integrable_finsetSum _ (fun i _ => count_integrable π mu u i t))
  intro ω
  simp only
  exact_mod_cast count_matching π mu kstar ω u t

/-- Reindexing by the injective `kstar`: the servers `k*_{u'}`, `u' ≠ u`, are sub-optimal for `u`. -/
lemma expCount_reindex (π : Policy U K) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hinj : Function.Injective kstar) (u : Fin U) (t : ℕ) :
    ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u), expCount π mu u (kstar u') t ≤
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), expCount π mu u k t := by
  rw [← Finset.sum_image (f := fun k => expCount π mu u k t) (fun a _ b _ h => hinj h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    obtain ⟨u', hu', rfl⟩ := hk
    exact fun h => hu' (hinj h)
  · intro k _ _; exact expCount_nonneg π mu u k t

lemma D_eq (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) :
    D mu kstar = gapMin mu kstar * invKL mu := by
  unfold D invKL
  split_ifs <;> simp [div_eq_mul_inv]

lemma gapMin_nonneg (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hA1 : Assumption1 mu kstar) : 0 ≤ gapMin mu kstar := by
  unfold gapMin
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    intro p hp
    have hp' : p.2 ≠ kstar p.1 := (Finset.mem_filter.1 hp).2
    have := hA1.2 p.1 p.2 hp'
    unfold gap; linarith
  · exact le_rfl

end QB3Cor20

open QB3Cor20 in
theorem solution {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (hU : 0 < U)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : QueueBandit.LateLower.Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (π : QueueBandit.LateLower.Policy U K)
    (hπ : QueueBandit.LateLower.IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, τ < t →
      ((U : ℝ) * ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar *
            ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
          2 * QueueBandit.LateLower.gapMin mu kstar *
            ∑ u : Fin U, ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
              QueueBandit.LateLower.expCount π mu u k t) ∧
      (∀ u : Fin U,
        ((U : ℝ) - 1) * QueueBandit.LateLower.D mu kstar *
            ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
          2 * QueueBandit.LateLower.gapMin mu kstar *
            ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
              QueueBandit.LateLower.expCount π mu u k t) ∧
      (∀ u : Fin U,
        ((K : ℝ) - U) * QueueBandit.LateLower.D mu kstar *
            ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
          QueueBandit.LateLower.gapMin mu kstar *
            ∑ k ∈ Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k),
              QueueBandit.LateLower.expCount π mu u k t) := by
  obtain ⟨τ, C, hC, h19⟩ := QueueBandit.EarlyLower.lemma_19 hUK hK hU mu kstar hmu hA1 α hα0 hα1
    π hπ
  refine ⟨τ, C, hC, fun t ht => ?_⟩
  have hinj : Function.Injective kstar := hA1.1
  have hgm := gapMin_nonneg mu kstar hA1
  set L := (1 - α) * Real.log t - Real.log (4 * K * C) with hL
  set E := fun u k => expCount π mu u k t with hE
  have hE0 : ∀ u k, 0 ≤ E u k := fun u k => expCount_nonneg π mu u k t
  -- the inner sum of Lemma 19 at server `k*_{u'}`
  have hinner : ∀ u u' : Fin U, u' ≠ u →
      ∑ u'' ∈ Finset.univ.filter (fun u'' : Fin U => u'' ≠ u),
        (if kstar u'' = kstar u' then E u'' (kstar u) else 0) = E u' (kstar u) := by
    intro u u' hu'
    simp_rw [hinj.eq_iff]
    rw [Finset.sum_ite_eq']
    simp [hu']
  -- the inner sum of Lemma 19 vanishes at a server optimal for no queue
  have hinner0 : ∀ u : Fin U, ∀ k : Fin K, (∀ u' : Fin U, kstar u' ≠ k) →
      ∑ u'' ∈ Finset.univ.filter (fun u'' : Fin U => u'' ≠ u),
        (if kstar u'' = k then E u'' (kstar u) else 0) = 0 := by
    intro u k hk
    apply Finset.sum_eq_zero
    intro u'' _
    simp [hk u'']
  have hcardU : ∀ u : Fin U,
      ((Finset.univ.filter (fun u' : Fin U => u' ≠ u)).card : ℝ) = (U : ℝ) - 1 := by
    intro u
    rw [Finset.filter_ne' Finset.univ u, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]
    simp
  have hcardK : ∀ u : Fin U,
      ((Finset.univ.filter (fun k : Fin K => k ≠ kstar u)).card : ℝ) = (K : ℝ) - 1 := by
    intro u
    rw [Finset.filter_ne' Finset.univ (kstar u), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, Nat.cast_sub (by omega)]
    simp
  have hcardC : ((Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k)).card : ℝ) =
      (K : ℝ) - U := by
    have hset : Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k) =
        Finset.univ \ Finset.univ.image kstar := by
      ext k; simp
    rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_image_of_injective _ hinj, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin, Nat.cast_sub hUK]
  have hDeq := D_eq mu kstar
  refine ⟨?_, ?_, ?_⟩
  · -- part (a)
    have hsum : ∀ u : Fin U, ((K : ℝ) - 1) * (invKL mu * L) ≤
        ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), E u k +
          ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u), E u' (kstar u) := by
      intro u
      have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), invKL mu * L ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), (E u k +
            ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
              (if kstar u' = k then E u' (kstar u) else 0)) :=
        Finset.sum_le_sum fun k hk => h19 u k (Finset.mem_filter.1 hk).2 t ht
      rw [Finset.sum_const, nsmul_eq_mul, hcardK, Finset.sum_add_distrib] at h1
      have h2 : ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
            ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
              (if kstar u' = k then E u' (kstar u) else 0) =
          ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u), E u' (kstar u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u' hu'
        have hne : kstar u' ≠ kstar u := fun h => (Finset.mem_filter.1 hu').2 (hinj h)
        rw [Finset.sum_ite_eq]
        simp [hne]
      rw [h2] at h1
      exact h1
    have hswap : ∑ u : Fin U, ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
          E u' (kstar u) =
        ∑ u' : Fin U, ∑ u ∈ Finset.univ.filter (fun u : Fin U => u ≠ u'), E u' (kstar u) := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro u' _
      apply Finset.sum_congr rfl; intro u _
      by_cases h : u = u'
      · simp [h]
      · simp [h, Ne.symm h]
    have hre : ∀ u' : Fin U,
        ∑ u ∈ Finset.univ.filter (fun u : Fin U => u ≠ u'), E u' (kstar u) ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u'), E u' k :=
      fun u' => expCount_reindex π mu kstar hinj u' t
    have htot := Finset.sum_le_sum fun u (_ : u ∈ (Finset.univ : Finset (Fin U))) => hsum u
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_add_distrib, hswap] at htot
    have hre' := Finset.sum_le_sum fun u' (_ : u' ∈ (Finset.univ : Finset (Fin U))) => hre u'
    set S := ∑ u : Fin U, ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), E u k
    have hfin : (U : ℝ) * (((K : ℝ) - 1) * (invKL mu * L)) ≤ 2 * S := by linarith
    have := mul_le_mul_of_nonneg_left hfin hgm
    rw [hDeq]
    calc (U : ℝ) * ((K : ℝ) - 1) * (gapMin mu kstar * invKL mu) * L
        = gapMin mu kstar * ((U : ℝ) * (((K : ℝ) - 1) * (invKL mu * L))) := by ring
      _ ≤ gapMin mu kstar * (2 * S) := this
      _ = 2 * gapMin mu kstar * S := by ring
  · -- part (b)
    intro u
    have h1 : ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u), invKL mu * L ≤
        ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
          (E u (kstar u') + E u' (kstar u)) := by
      apply Finset.sum_le_sum
      intro u' hu'
      have hne : u' ≠ u := (Finset.mem_filter.1 hu').2
      have hk : kstar u' ≠ kstar u := fun h => hne (hinj h)
      have := h19 u (kstar u') hk t ht
      rw [hinner u u' hne] at this
      exact this
    rw [Finset.sum_const, nsmul_eq_mul, hcardU, Finset.sum_add_distrib] at h1
    have h2 := expCount_reindex π mu kstar hinj u t
    have h3 := expCount_matching π mu kstar u t
    set Sb := ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u), E u k
    have hfin : ((U : ℝ) - 1) * (invKL mu * L) ≤ 2 * Sb := by
      simp only [hE] at h1 ⊢; linarith
    have := mul_le_mul_of_nonneg_left hfin hgm
    rw [hDeq]
    calc ((U : ℝ) - 1) * (gapMin mu kstar * invKL mu) * L
        = gapMin mu kstar * (((U : ℝ) - 1) * (invKL mu * L)) := by ring
      _ ≤ gapMin mu kstar * (2 * Sb) := this
      _ = 2 * gapMin mu kstar * Sb := by ring
  · -- part (c)
    intro u
    have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k),
        invKL mu * L ≤
        ∑ k ∈ Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k), E u k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : ∀ u' : Fin U, kstar u' ≠ k := (Finset.mem_filter.1 hk).2
      have := h19 u k (fun h => hk' u h.symm) t ht
      rw [hinner0 u k hk', add_zero] at this
      exact this
    rw [Finset.sum_const, nsmul_eq_mul, hcardC] at h1
    have := mul_le_mul_of_nonneg_left h1 hgm
    rw [hDeq]
    calc ((K : ℝ) - U) * (gapMin mu kstar * invKL mu) * L
        = gapMin mu kstar * (((K : ℝ) - U) * (invKL mu * L)) := by ring
      _ ≤ _ := this
