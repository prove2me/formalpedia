-- Prove2me | solution 1 for ScheduledQueue.Diffusion.count_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:42:13.686795+00:00
-- url     : https://prove2.me/submissions/b7d90d68-c25b-4003-a90a-0bebbb8fe588

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

open Set

/-- per-index identity -/
lemma SQD_ind_identity (t s a : ℝ) (ht : 0 ≤ t) (h1 : s ≠ t) (h2 : s ≠ 0) (h3 : a ≠ t) (h4 : a ≠ 0) :
    ((if a ∈ Ioc 0 t then 1 else 0 : ℤ)) =
      (if s ∈ Ioc 0 t then 1 else 0 : ℤ)
        + ((if t < s ∧ a ≤ t then 1 else 0 : ℤ) - (if s < t ∧ t ≤ a then 1 else 0 : ℤ))
        - ((if 0 < s ∧ a ≤ 0 then 1 else 0 : ℤ) - (if s < 0 ∧ 0 ≤ a then 1 else 0 : ℤ)) := by
  simp only [mem_Ioc]
  rcases lt_or_gt_of_ne h1 with b1 | b1 <;> rcases lt_or_gt_of_ne h2 with b2 | b2 <;>
    rcases lt_or_gt_of_ne h3 with b3 | b3 <;> rcases lt_or_gt_of_ne h4 with b4 | b4 <;>
    first | (exfalso; linarith) |
      simp [b1, b2, b3, b4, b1.le, b2.le, b3.le, b4.le, not_le.mpr b1, not_le.mpr b2,
        not_le.mpr b3, not_le.mpr b4, not_lt.mpr b1.le, not_lt.mpr b2.le, not_lt.mpr b3.le,
        not_lt.mpr b4.le]

lemma SQD_setEq {p : ℤ → Prop} [DecidablePred p] (F : Finset ℤ) (hF : ∀ i, p i → i ∈ F) :
    {i | p i} = ↑(F.filter p) := by
  ext i; simp only [mem_setOf_eq, Finset.coe_filter]; exact ⟨fun hp => ⟨hF i hp, hp⟩, fun h => h.2⟩

/-- outside a finite set of indices, no index contributes to any of the six counts -/
lemma SQD_support (h t u : ℝ) (hh : 0 < h) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : ℤ → ℝ)
    (hfin : {i : ℤ | ((i.natAbs : ℕ) : ℝ) < 2 * |x i| / h}.Finite) :
    ∃ F : Finset ℤ, ∀ i : ℤ, i ∉ F →
      ¬ (i * h + u * h + x i ∈ Ioc 0 t) ∧ ¬ (i * h + u * h ∈ Ioc 0 t) ∧
      ¬ (t < i * h + u * h ∧ i * h + u * h + x i ≤ t) ∧
      ¬ (i * h + u * h < t ∧ t ≤ i * h + u * h + x i) ∧
      ¬ ((0:ℝ) < i * h + u * h ∧ i * h + u * h + x i ≤ 0) ∧
      ¬ (i * h + u * h < 0 ∧ (0:ℝ) ≤ i * h + u * h + x i) := by
  set M : ℕ := ⌈2 * t / h⌉₊ + 3 with hM
  refine ⟨hfin.toFinset ∪ Finset.Icc (-(M : ℤ)) M, fun i hi => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, mem_setOf_eq, Finset.mem_Icc, not_or,
    not_and, not_le, not_lt] at hi
  obtain ⟨hx, hiM⟩ := hi
  have hx' : |x i| ≤ ((i.natAbs : ℕ) : ℝ) * h / 2 := by
    rw [div_le_iff₀ hh] at hx; linarith
  have hceil : 2 * t / h ≤ (⌈2 * t / h⌉₊ : ℝ) := Nat.le_ceil _
  have h2t : 2 * t ≤ (⌈2 * t / h⌉₊ : ℝ) * h := by
    rw [div_le_iff₀ hh] at hceil; linarith
  have hxa := abs_le.mp hx'
  rcases le_or_gt 0 i with hi0 | hi0
  · have hn : ((i.natAbs : ℕ) : ℝ) = (i : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hi0)]
    have hiM' : (M : ℤ) < i := by
      by_contra hc; push Not at hc; exact absurd (hiM (by omega)) (by omega)
    have hiM'' : (M : ℝ) < (i : ℝ) := by exact_mod_cast hiM'
    rw [hn] at hxa
    have hMr : (M : ℝ) = (⌈2 * t / h⌉₊ : ℝ) + 3 := by rw [hM]; push_cast; ring
    have key : t < (i : ℝ) * h / 2 := by
      have : ((⌈2 * t / h⌉₊ : ℝ) + 3) * h < (i : ℝ) * h := by
        apply mul_lt_mul_of_pos_right _ hh; linarith
      nlinarith
    have hih : 0 ≤ (i : ℝ) * h := by positivity
    have huh : 0 ≤ u * h := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mem_Ioc, not_and, not_le, not_lt] <;>
      intros <;> nlinarith
  · have hn : ((i.natAbs : ℕ) : ℝ) = -(i : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hi0)]
    have hiM' : i < -(M : ℤ) := by
      by_contra hc; push Not at hc; exact absurd (hiM hc) (by omega)
    have hiM'' : (i : ℝ) < -(M : ℝ) := by exact_mod_cast hiM'
    rw [hn] at hxa
    have hM3 : (3 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * t / h⌉₊]
    have huh : u * h ≤ h := by nlinarith
    have k1 : (i : ℝ) * h + u * h < 0 := by nlinarith
    have k2 : (i : ℝ) * h + u * h + x i < 0 := by nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mem_Ioc, not_and, not_le, not_lt] <;>
      intros <;> linarith

lemma SQD_det (h t u : ℝ) (hh : 0 < h) (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : ℤ → ℝ)
    (hfin : {i : ℤ | ((i.natAbs : ℕ) : ℝ) < 2 * |x i| / h}.Finite)
    (hties : ∀ i : ℤ, i * h + u * h ≠ t ∧ i * h + u * h ≠ 0 ∧ i * h + u * h + x i ≠ t ∧
      i * h + u * h + x i ≠ 0) :
    {i : ℤ | t < i * h + u * h ∧ i * h + u * h + x i ≤ t}.encard ≠ ⊤ ∧
    {i : ℤ | i * h + u * h < t ∧ t ≤ i * h + u * h + x i}.encard ≠ ⊤ ∧
    {i : ℤ | (0:ℝ) < i * h + u * h ∧ i * h + u * h + x i ≤ 0}.encard ≠ ⊤ ∧
    {i : ℤ | i * h + u * h < 0 ∧ (0:ℝ) ≤ i * h + u * h + x i}.encard ≠ ⊤ ∧
    {i : ℤ | i * h + u * h + x i ∈ Ioc 0 t}.Finite ∧
    ({i : ℤ | i * h + u * h + x i ∈ Ioc 0 t}.ncard : ℤ) =
      ({i : ℤ | i * h + u * h ∈ Ioc 0 t}.ncard : ℤ)
        + ((({i : ℤ | t < i * h + u * h ∧ i * h + u * h + x i ≤ t}.encard).toNat : ℤ)
          - (({i : ℤ | i * h + u * h < t ∧ t ≤ i * h + u * h + x i}.encard).toNat : ℤ))
        - ((({i : ℤ | (0:ℝ) < i * h + u * h ∧ i * h + u * h + x i ≤ 0}.encard).toNat : ℤ)
          - (({i : ℤ | i * h + u * h < 0 ∧ (0:ℝ) ≤ i * h + u * h + x i}.encard).toNat : ℤ)) := by
  classical
  obtain ⟨F, hF⟩ := SQD_support h t u hh ht hu0 hu1 x hfin
  have e1 := SQD_setEq (p := fun i : ℤ => t < i * h + u * h ∧ i * h + u * h + x i ≤ t) F
    (fun i hp => by by_contra hc; exact (hF i hc).2.2.1 hp)
  have e2 := SQD_setEq (p := fun i : ℤ => i * h + u * h < t ∧ t ≤ i * h + u * h + x i) F
    (fun i hp => by by_contra hc; exact (hF i hc).2.2.2.1 hp)
  have e3 := SQD_setEq (p := fun i : ℤ => (0:ℝ) < i * h + u * h ∧ i * h + u * h + x i ≤ 0) F
    (fun i hp => by by_contra hc; exact (hF i hc).2.2.2.2.1 hp)
  have e4 := SQD_setEq (p := fun i : ℤ => i * h + u * h < 0 ∧ (0:ℝ) ≤ i * h + u * h + x i) F
    (fun i hp => by by_contra hc; exact (hF i hc).2.2.2.2.2 hp)
  have e5 := SQD_setEq (p := fun i : ℤ => i * h + u * h + x i ∈ Ioc 0 t) F
    (fun i hp => by by_contra hc; exact (hF i hc).1 hp)
  have e6 := SQD_setEq (p := fun i : ℤ => i * h + u * h ∈ Ioc 0 t) F
    (fun i hp => by by_contra hc; exact (hF i hc).2.1 hp)
  rw [e1, e2, e3, e4, e5, e6]
  simp only [Set.encard_coe_eq_coe_finsetCard, Set.ncard_coe_finset,
    ENat.toNat_natCast]
  refine ⟨ENat.natCast_ne_top _, ENat.natCast_ne_top _, ENat.natCast_ne_top _, ENat.natCast_ne_top _,
    Finset.finite_toSet _, ?_⟩
  simp only [Finset.natCast_card_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨a1, a2, a3, a4⟩ := hties i
  exact SQD_ind_identity t _ _ ht a1 a2 a3 a4

open MeasureTheory ProbabilityTheory

lemma SQD_noatom (h c d : ℝ) (hh : 0 < h) :
    (volume.restrict (Icc (0:ℝ) 1)) {v : ℝ | d + v * h = c} = 0 := by
  have hsub : {v : ℝ | d + v * h = c} ⊆ {(c - d) / h} := by
    intro v hv
    simp only [mem_setOf_eq] at hv
    simp only [mem_singleton_iff]
    field_simp; linarith
  refine measure_mono_null hsub ?_
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

lemma SQD_ae_sched {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) (d c : ℝ) :
    ∀ᵐ ω ∂P, d + U ω * h ≠ c := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [hin.uniform.measure_eq (p := fun v => d + v * h = c)
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact SQD_noatom h c d hh

lemma SQD_ae_arr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) (i : ℤ) (d c : ℝ) :
    ∀ᵐ ω ∂P, d + U ω * h + ξ i ω ≠ c := by
  have hind : IndepFun U (ξ i) P := hin.indep_shift.comp measurable_id (measurable_pi_apply i)
  have hUm : AEMeasurable U P := hin.uniform.aemeasurable
  have hξm : AEMeasurable (ξ i) P := (hin.measurable i).aemeasurable
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hUm hξm).mp hind
  set S : Set (ℝ × ℝ) := {p | d + p.1 * h + p.2 = c} with hSdef
  have hS : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have e1 : P {ω | d + U ω * h + ξ i ω = c} = P.map (fun ω => (U ω, ξ i ω)) S := by
    rw [Measure.map_apply_of_aemeasurable (hUm.prodMk hξm) hS]; rfl
  rw [e1, hmap, Measure.prod_apply_symm hS, hin.uniform.map_eq]
  have : ∀ y : ℝ, (volume.restrict (Icc (0:ℝ) 1)) ((fun x => (x, y)) ⁻¹' S) = 0 := by
    intro y
    have := SQD_noatom h (c - y) d hh
    refine measure_mono_null ?_ this
    intro v hv
    simp only [hSdef, mem_preimage, mem_setOf_eq] at hv
    simp only [mem_setOf_eq]; linarith
  simp [this]

lemma SQD_ae_fin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, {i : ℤ | ((i.natAbs : ℕ) : ℝ) < 2 * |ξ i ω| / h}.Finite := by
  apply ae_finite_setOfPred_mem (s := fun i : ℤ => {ω | ((i.natAbs : ℕ) : ℝ) < 2 * |ξ i ω| / h})
  set X : Ω → ℝ := fun ω => 2 * |ξ 0 ω| / h with hX
  set g : ℕ → ENNReal := fun n => P {ω | X ω ∈ Ioi (n : ℝ)} with hg
  have hfun : Measurable (fun x : ℝ => 2 * |x| / h) := by fun_prop
  have heq : ∀ i : ℤ, P {ω | ((i.natAbs : ℕ) : ℝ) < 2 * |ξ i ω| / h} = g i.natAbs := by
    intro i
    have hid := (hin.identDistrib i).comp hfun
    have := hid.measure_mem_eq (s := Ioi ((i.natAbs : ℕ) : ℝ)) measurableSet_Ioi
    simp only [hg, hX]; exact this
  simp_rw [heq]
  have hint : Integrable X P := ((hin.integrable.abs).const_mul 2).div_const h
  have hnn : 0 ≤ X := fun ω => by simp only [hX]; positivity
  have hsum : ∑' j : ℕ, P {ω | X ω ∈ Ioi (j : ℝ)} < ⊤ := by
    letI : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hint hnn
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have h1 : ∑' n : ℕ, g ((n : ℤ).natAbs) = ∑' n : ℕ, g n := by simp
  have h2 : ∑' n : ℕ, g ((-(n + 1 : ℤ)).natAbs) ≤ ∑' n : ℕ, g n := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    have : (-(n + 1 : ℤ)).natAbs = n + 1 := by omega
    rw [this]
    refine measure_mono (fun ω hω => ?_)
    simp only [mem_setOf_eq, mem_Ioi] at hω ⊢
    push_cast at hω; linarith
  rw [h1]
  exact (ENNReal.add_lt_top.mpr ⟨hsum, lt_of_le_of_lt h2 hsum⟩).ne

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P,
      early h ξ U t ω ≠ ⊤ ∧ late h ξ U t ω ≠ ⊤ ∧
      early h ξ U 0 ω ≠ ⊤ ∧ late h ξ U 0 ω ≠ ⊤ ∧
      {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 t}.Finite ∧
      (ScheduledQueue.Stability.count h ξ U t ω : ℤ) =
        (scheduled h U t ω : ℤ)
          + (((early h ξ U t ω).toNat : ℤ) - ((late h ξ U t ω).toNat : ℤ))
          - (((early h ξ U 0 ω).toNat : ℤ) - ((late h ξ U 0 ω).toNat : ℤ)) := by
  intro t ht
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0:ℝ) 1 := by
    rw [ae_iff]
    rw [hin.uniform.measure_eq (p := fun v => v ∉ Icc (0:ℝ) 1) measurableSet_Icc.compl]
    show (volume.restrict (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1)ᶜ = 0
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    simp
  have hties : ∀ᵐ ω ∂P, ∀ i : ℤ, (i : ℝ) * h + U ω * h ≠ t ∧ (i : ℝ) * h + U ω * h ≠ 0 ∧
      (i : ℝ) * h + U ω * h + ξ i ω ≠ t ∧ (i : ℝ) * h + U ω * h + ξ i ω ≠ 0 := by
    rw [ae_all_iff]; intro i
    filter_upwards [SQD_ae_sched P h hh ξ U hin ((i : ℝ) * h) t,
      SQD_ae_sched P h hh ξ U hin ((i : ℝ) * h) 0,
      SQD_ae_arr P h hh ξ U hin i ((i : ℝ) * h) t,
      SQD_ae_arr P h hh ξ U hin i ((i : ℝ) * h) 0] with ω a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  filter_upwards [hU, SQD_ae_fin P h hh ξ U hin, hties] with ω hu hf hti
  have key := SQD_det h t (U ω) hh ht hu.1 hu.2 (fun i => ξ i ω) hf hti
  have hA : {j : ℤ | ScheduledQueue.Stability.arrival h ξ U j ω ∈ Ioc 0 t} =
      {i : ℤ | (i : ℝ) * h + U ω * h + ξ i ω ∈ Ioc 0 t} := by
    ext j; simp only [ScheduledQueue.Stability.arrival, mem_setOf_eq, mul_comm h (U ω)]
  simp only [early, late, scheduled, ScheduledQueue.Stability.count, hA]
  exact key
