-- Prove2me | solution 1 for QueueBandit.LateLower.corollary_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:02:18.796945+00:00
-- url     : https://prove2.me/submissions/d370aad3-3a0d-4ea5-b906-90e2b647c63f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance
import Definitions.Def_QueueBandit_LateLower_Dynamics
import Theorems.Thm_QueueBandit_LateLower_lemma_19

open MeasureTheory Finset Filter

namespace QBCor20Aux

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



theorem count_eq_sum_indicator (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U)
    (k : Fin K) (t : ℕ) (ω : ℕ → Seed U K) :
    ((count π mu ω u k t : ℕ) : ℝ) =
      ∑ m ∈ Icc 1 t, ({ω' : ℕ → Seed U K | sched π mu ω' m u = k}.indicator 1 ω : ℝ) := by
  unfold count
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : sched π mu ω m u = k
  · simp [h]
  · simp [h]

theorem integrable_count (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U)
    (k : Fin K) (t : ℕ) :
    Integrable (fun ω => ((count π mu ω u k t : ℕ) : ℝ)) (seedMeasure U K) := by
  simp_rw [count_eq_sum_indicator]
  exact integrable_finsetSum _ fun m _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_sched π mu m u k)

/-- Pathwise: queue `u` is served by exactly one server in each slot. -/
theorem sum_count_eq (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (t : ℕ)
    (ω : ℕ → Seed U K) : ∑ k, count π mu ω u k t = t := by
  unfold count
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun s => sched π mu ω s u)
    (fun _ _ => mem_univ _)]
  simp

/-- Pathwise: server `k` serves at most one queue in each slot. -/
theorem sum_count_le (π : Policy U K) (mu : Fin U → Fin K → ℝ) (k : Fin K) (t : ℕ)
    (ω : ℕ → Seed U K) : ∑ u, count π mu ω u k t ≤ t := by
  unfold count
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ s ∈ Icc 1 t, ∑ u : Fin U, (if sched π mu ω s u = k then 1 else 0)
      ≤ ∑ s ∈ Icc 1 t, 1 := by
        refine sum_le_sum fun s _ => ?_
        rw [← Finset.card_filter]
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        simp only [mem_filter, mem_univ, true_and] at ha hb
        exact (sched π mu ω s).injective (ha.trans hb.symm)
    _ = t := by simp

/-- Pathwise form of (29): `Σ_{u' ≠ u} T_{u' k*_u} ≤ Σ_{k ≠ k*_u} T_{uk}`. -/
theorem count_ineq (π : Policy U K) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (u : Fin U) (t : ℕ) (ω : ℕ → Seed U K) :
    ∑ u' ∈ univ.erase u, ((count π mu ω u' (kstar u) t : ℕ) : ℝ) ≤
      ∑ k ∈ univ.erase (kstar u), ((count π mu ω u k t : ℕ) : ℝ) := by
  have h1 := sum_count_eq π mu u t ω
  have h2 := sum_count_le π mu (kstar u) t ω
  rw [← Finset.add_sum_erase _ _ (mem_univ (kstar u))] at h1
  rw [← Finset.add_sum_erase _ _ (mem_univ u)] at h2
  rw [← Nat.cast_sum, ← Nat.cast_sum]
  exact_mod_cast (by omega :
    ∑ u' ∈ univ.erase u, count π mu ω u' (kstar u) t ≤
      ∑ k ∈ univ.erase (kstar u), count π mu ω u k t)

theorem expCount_nonneg (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U) (k : Fin K)
    (n : ℕ) : 0 ≤ expCount π mu u k n :=
  integral_nonneg fun _ => Nat.cast_nonneg _

theorem expCount_ineq (π : Policy U K) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (u : Fin U) (t : ℕ) :
    ∑ u' ∈ univ.erase u, expCount π mu u' (kstar u) t ≤
      ∑ k ∈ univ.erase (kstar u), expCount π mu u k t := by
  unfold expCount
  rw [← integral_finsetSum _ (fun i _ => integrable_count π mu i (kstar u) t),
    ← integral_finsetSum _ (fun i _ => integrable_count π mu u i t)]
  exact integral_mono (integrable_finsetSum _ fun i _ => integrable_count π mu i (kstar u) t)
    (integrable_finsetSum _ fun i _ => integrable_count π mu u i t)
    (fun ω => count_ineq π mu kstar u t ω)

theorem gapMin_nonneg (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hA1 : Assumption1 mu kstar) : 0 ≤ gapMin mu kstar := by
  unfold gapMin
  split_ifs with hne
  · refine le_inf' _ _ fun p hp => ?_
    have hp' : p.2 ≠ kstar p.1 := by simpa [subPairs] using hp
    have := hA1.2 p.1 p.2 hp'
    unfold gap; linarith
  · exact le_rfl

theorem D_eq (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K) :
    D mu kstar = gapMin mu kstar * invKL mu := by
  unfold D invKL
  split_ifs <;> simp [div_eq_mul_inv]

end QBCor20Aux

open QueueBandit.LateLower in
theorem solution {U K : ℕ} (hU : 0 < U) (hUK : U ≤ K) (hK : 2 ≤ K)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : Policy U K) (hπ : IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, τ < t →
      ((U : ℝ) * ((K : ℝ) - 1) * D mu kstar *
          ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        2 * gapMin mu kstar * ∑ u, ∑ k ∈ univ.erase (kstar u), expCount π mu u k t) ∧
      (∀ u : Fin U, ((U : ℝ) - 1) * D mu kstar *
          ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        2 * gapMin mu kstar * ∑ k ∈ univ.erase (kstar u), expCount π mu u k t) ∧
      (∀ u : Fin U, ((K : ℝ) - U) * D mu kstar *
          ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        gapMin mu kstar *
          ∑ k ∈ univ.filter (fun k => ∀ u', kstar u' ≠ k), expCount π mu u k t) := by
  obtain ⟨τ, C, hC, h19⟩ := lemma_19 hU hUK hK mu kstar hmu hA1 α hα0 hα1 π hπ
  refine ⟨τ, C, hC, fun t ht => ?_⟩
  set B := (1 - α) * Real.log t - Real.log (4 * K * C) with hB
  set I := invKL mu with hI
  have hg := QBCor20Aux.gapMin_nonneg mu kstar hA1
  have hD := QBCor20Aux.D_eq mu kstar
  have hinj := hA1.1
  -- Lemma 19 at `k = k*_v`, `v ≠ u`
  have hswap : ∀ u v : Fin U, v ≠ u →
      I * B ≤ expCount π mu u (kstar v) t + expCount π mu v (kstar u) t := by
    intro u v hvu
    have hk : kstar v ≠ kstar u := fun h => hvu (hinj h)
    have := h19 u (kstar v) hk t ht
    have hs : ∑ u' ∈ univ.erase u,
        (if kstar u' = kstar v then expCount π mu u' (kstar u) t else 0) =
        expCount π mu v (kstar u) t := by
      simp_rw [hinj.eq_iff]
      rw [Finset.sum_ite_eq' (univ.erase u) v]
      simp [hvu]
    linarith
  -- the second sum of Lemma 19 summed over `k ≠ k*_u`
  have hsecond : ∀ u : Fin U,
      ∑ k ∈ univ.erase (kstar u), ∑ u' ∈ univ.erase u,
        (if kstar u' = k then expCount π mu u' (kstar u) t else 0) =
      ∑ u' ∈ univ.erase u, expCount π mu u' (kstar u) t := by
    intro u
    rw [Finset.sum_comm]
    refine sum_congr rfl fun u' hu' => ?_
    rw [Finset.sum_ite_eq (univ.erase (kstar u)) (kstar u')]
    have : kstar u' ≠ kstar u := fun h => (ne_of_mem_erase hu') (hinj h)
    simp [this]
  -- image sum: Σ_{v ≠ u} E[T_{u k*_v}] ≤ Σ_{k ≠ k*_u} E[T_{uk}]
  have himg : ∀ u : Fin U, ∑ v ∈ univ.erase u, expCount π mu u (kstar v) t ≤
      ∑ k ∈ univ.erase (kstar u), expCount π mu u k t := by
    intro u
    rw [← Finset.sum_image (f := fun k => expCount π mu u k t)
      (fun a _ b _ h => hinj h)]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => QBCor20Aux.expCount_nonneg _ _ _ _ _
    intro k hk
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hk
    exact mem_erase.mpr ⟨fun h => ne_of_mem_erase hv (hinj h), mem_univ _⟩
  have hKr : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hUr : ((U - 1 : ℕ) : ℝ) = (U : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  refine ⟨?_, ?_, ?_⟩
  · -- part (a)
    have hsum : ∑ u : Fin U, ∑ k ∈ univ.erase (kstar u), I * B ≤
        ∑ u, ∑ k ∈ univ.erase (kstar u), expCount π mu u k t +
          ∑ u, ∑ u' ∈ univ.erase u, expCount π mu u' (kstar u) t := by
      rw [← sum_add_distrib]
      refine sum_le_sum fun u _ => ?_
      rw [← hsecond u, ← sum_add_distrib]
      exact sum_le_sum fun k hk => h19 u k (ne_of_mem_erase hk) t ht
    have hle : ∑ u, ∑ u' ∈ univ.erase u, expCount π mu u' (kstar u) t ≤
        ∑ u, ∑ k ∈ univ.erase (kstar u), expCount π mu u k t :=
      sum_le_sum fun u _ => QBCor20Aux.expCount_ineq π mu kstar u t
    have hcard : ∑ u : Fin U, ∑ k ∈ univ.erase (kstar u), I * B =
        (U : ℝ) * ((K : ℝ) - 1) * (I * B) := by
      simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
        nsmul_eq_mul, hKr]
      ring
    rw [hcard] at hsum
    have := mul_le_mul_of_nonneg_left (show (U : ℝ) * ((K : ℝ) - 1) * (I * B) ≤
      2 * ∑ u, ∑ k ∈ univ.erase (kstar u), expCount π mu u k t by linarith) hg
    rw [hD]
    nlinarith [this]
  · -- part (b)
    intro u
    have h1 : ∑ v ∈ univ.erase u, I * B ≤
        ∑ v ∈ univ.erase u, expCount π mu u (kstar v) t +
          ∑ v ∈ univ.erase u, expCount π mu v (kstar u) t := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun v hv => hswap u v (ne_of_mem_erase hv)
    have hcard : ∑ v ∈ univ.erase u, I * B = ((U : ℝ) - 1) * (I * B) := by
      simp only [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
        nsmul_eq_mul, hUr]
    rw [hcard] at h1
    have h2 := himg u
    have h3 := QBCor20Aux.expCount_ineq π mu kstar u t
    have := mul_le_mul_of_nonneg_left (show ((U : ℝ) - 1) * (I * B) ≤
      2 * ∑ k ∈ univ.erase (kstar u), expCount π mu u k t by linarith) hg
    rw [hD]
    nlinarith [this]
  · -- part (c)
    intro u
    set F := univ.filter (fun k : Fin K => ∀ u', kstar u' ≠ k) with hF
    have hFc : F = univ \ univ.image kstar := by
      ext k; simp [hF]
    have hcardF : ((F.card : ℕ) : ℝ) = (K : ℝ) - U := by
      rw [hFc, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
        card_image_of_injective _ hinj, card_univ, Fintype.card_fin, Nat.cast_sub hUK]
    have h1 : ∑ k ∈ F, I * B ≤ ∑ k ∈ F, expCount π mu u k t := by
      refine sum_le_sum fun k hk => ?_
      have hk' : ∀ u', kstar u' ≠ k := (mem_filter.mp hk).2
      have := h19 u k (fun h => hk' u h.symm) t ht
      have hs : ∑ u' ∈ univ.erase u,
          (if kstar u' = k then expCount π mu u' (kstar u) t else 0) = 0 :=
        sum_eq_zero fun u' _ => if_neg (hk' u')
      linarith
    rw [sum_const, nsmul_eq_mul, hcardF] at h1
    have := mul_le_mul_of_nonneg_left h1 hg
    rw [hD]
    nlinarith [this]
