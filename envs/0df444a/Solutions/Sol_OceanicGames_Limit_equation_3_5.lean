-- Prove2me | solution 1 for OceanicGames.Limit.equation_3_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:13:16.903725+00:00
-- url     : https://prove2.me/submissions/fdd9ddce-c2ed-4091-959e-40b212489948

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic



namespace OceanicGames.Limit

open MeasureTheory Set Finset

theorem orderSet_meas {m : ℕ} (i : Fin m) (S : Finset (Fin m)) :
    MeasurableSet (orderSet i S) := by
  unfold orderSet
  have h1 : MeasurableSet (OceanicGames.Interior.cube m) := measurableSet_Icc
  have h2 : MeasurableSet {x : Fin m → ℝ | ∀ j ∈ S, x j < x i} := by
    have : {x : Fin m → ℝ | ∀ j ∈ S, x j < x i} = ⋂ j ∈ S, {x | x j < x i} := by
      ext x; simp
    rw [this]
    exact Finset.measurableSet_biInter S fun j _ =>
      measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  have h3 : MeasurableSet {x : Fin m → ℝ | ∀ j ∉ S, x i ≤ x j} := by
    have : {x : Fin m → ℝ | ∀ j ∉ S, x i ≤ x j} = ⋂ j ∈ Sᶜ, {x | x i ≤ x j} := by
      ext x; simp
    rw [this]
    exact Finset.measurableSet_biInter Sᶜ fun j _ =>
      measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
  exact h1.inter (h2.inter h3)

theorem pred_eq_of_mem_orderSet {m : ℕ} {i : Fin m} {S : Finset (Fin m)} {x : Fin m → ℝ}
    (hx : x ∈ orderSet i S) : OceanicGames.Interior.pred x (x i) = S := by
  obtain ⟨_, h1, h2⟩ := hx
  ext j
  simp only [OceanicGames.Interior.pred, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hj
    exact absurd (h2 j hj) (not_le.2 h)
  · intro hj; exact h1 j hj

theorem pivot_inter_order {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) :
    OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S =
      orderSet i S ∩ {x | OceanicGames.Interior.wsum w S + alpha * x i ≤ c ∧
        c ≤ OceanicGames.Interior.wsum w S + w i + alpha * x i} := by
  ext x
  constructor
  · rintro ⟨⟨_, h1, h2⟩, hx⟩
    rw [pred_eq_of_mem_orderSet hx] at h1 h2
    exact ⟨hx, h1, h2⟩
  · rintro ⟨hx, h1, h2⟩
    refine ⟨⟨hx.1, ?_, ?_⟩, hx⟩
    · rw [pred_eq_of_mem_orderSet hx]; exact h1
    · rw [pred_eq_of_mem_orderSet hx]; exact h2

theorem equation_3_4_core {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m) :
    OceanicGames.Interior.value c alpha w i =
      ∑ S ∈ (Finset.univ.erase i).powerset,
        (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal := by
  classical
  unfold OceanicGames.Interior.value
  have hmeas : ∀ S : Finset (Fin m), MeasurableSet
      (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S) := by
    intro S
    rw [pivot_inter_order]
    refine (orderSet_meas i S).inter ?_
    have hf : Measurable fun x : Fin m → ℝ => OceanicGames.Interior.wsum w S + alpha * x i := by
      fun_prop
    have hg : Measurable fun x : Fin m → ℝ => OceanicGames.Interior.wsum w S + w i + alpha * x i := by
      fun_prop
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le hf measurable_const
    · exact measurableSet_le measurable_const hg
  have hU : OceanicGames.Interior.pivotSet c alpha w i =
      ⋃ S ∈ (Finset.univ.erase i).powerset,
        (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hx
      refine ⟨OceanicGames.Interior.pred x (x i), ?_, hx, ?_⟩
      · rw [Finset.mem_powerset]
        intro j hj
        simp only [OceanicGames.Interior.pred, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rintro rfl
        exact lt_irrefl _ hj
      · refine ⟨hx.1, ?_, ?_⟩
        · intro j hj
          simpa [OceanicGames.Interior.pred] using hj
        · intro j hj
          simpa [OceanicGames.Interior.pred] using hj
    · rintro ⟨S, _, hx, _⟩; exact hx
  have hfin : ∀ S : Finset (Fin m),
      volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S) ≠ ⊤ := by
    intro S
    have hc : volume (Set.Icc (0 : Fin m → ℝ) 1) < ⊤ := isCompact_Icc.measure_lt_top
    refine ne_top_of_le_ne_top hc.ne ?_
    apply measure_mono
    exact fun x hx => hx.1.1
  conv_lhs => rw [hU]
  rw [measure_biUnion_finset, ENNReal.toReal_sum]
  · intro S _; exact hfin S
  · intro S _ S' _ hne
    refine Set.disjoint_left.2 ?_
    intro x hx hx'
    exact hne ((pred_eq_of_mem_orderSet hx.2).symm.trans (pred_eq_of_mem_orderSet hx'.2))
  · intro S _; exact hmeas S


theorem card_filter_succAbove {k : ℕ} (p : Fin (k+1)) (S : Finset (Fin (k+1))) (hS : p ∉ S) :
    (Finset.univ.filter fun j : Fin k => p.succAbove j ∈ S).card = S.card := by
  classical
  rw [← Finset.card_map (Fin.succAboveEmb p)]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.succAboveEmb_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hj
  · intro hy
    have : y ≠ p := fun h => hS (h ▸ hy)
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq this
    exact ⟨j, hy, rfl⟩

theorem cell_set_eq {k : ℕ} (p : Fin (k+1)) (S : Finset (Fin (k+1))) (hS : p ∉ S) (lo hi : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) p).symm ⁻¹'
      {x : Fin (k+1) → ℝ | x ∈ Set.Icc (0:Fin (k+1) → ℝ) 1 ∧ x p ∈ Set.Icc lo hi ∧
        (∀ j ∈ S, x j < x p) ∧ ∀ j ∉ S, x p ≤ x j} =
    {q : ℝ × (Fin k → ℝ) | q.1 ∈ Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi ∧
      q.2 ∈ Set.pi Set.univ (fun j : Fin k =>
        if p.succAbove j ∈ S then Set.Ico 0 q.1 else Set.Icc q.1 1)} := by
  classical
  ext ⟨t, y⟩
  simp only [Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply, Set.mem_setOf_eq,
    Set.mem_Icc, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    true_implies, Pi.le_def, Pi.zero_apply, Pi.one_apply]
  have e1 : ∀ j, (Fin.insertNthEquiv (fun _ => ℝ) p) (t, y) j =
      Fin.insertNth (α := fun _ => ℝ) p t y j := fun _ => rfl
  simp only [e1]
  have h0 : (∀ i, 0 ≤ Fin.insertNth (α := fun _ => ℝ) p t y i) ↔ 0 ≤ t ∧ ∀ i : Fin k, 0 ≤ y i := by
    rw [Fin.forall_iff_succAbove p]; simp
  have h1 : (∀ i, Fin.insertNth (α := fun _ => ℝ) p t y i ≤ 1) ↔ t ≤ 1 ∧ ∀ i : Fin k, y i ≤ 1 := by
    rw [Fin.forall_iff_succAbove p]; simp
  have h2 : (∀ j ∈ S, Fin.insertNth (α := fun _ => ℝ) p t y j < t) ↔
      ∀ i : Fin k, p.succAbove i ∈ S → y i < t := by
    rw [Fin.forall_iff_succAbove (P := fun j => j ∈ S → Fin.insertNth (α := fun _ => ℝ) p t y j < t) p]; simp [hS]
  have h3 : (∀ j ∉ S, t ≤ Fin.insertNth (α := fun _ => ℝ) p t y j) ↔
      ∀ i : Fin k, p.succAbove i ∉ S → t ≤ y i := by
    rw [Fin.forall_iff_succAbove (P := fun j => j ∉ S → t ≤ Fin.insertNth (α := fun _ => ℝ) p t y j) p]; simp
  simp only [Fin.insertNth_apply_same]
  rw [h0, h1, h2, h3]
  constructor
  · rintro ⟨⟨⟨h0t, h0y⟩, h1t, h1y⟩, hlo, hS2, hS3⟩
    refine ⟨⟨⟨h0t, h1t⟩, hlo⟩, fun i => ?_⟩
    by_cases hi : p.succAbove i ∈ S
    · simp only [hi, if_true, Set.mem_Ico]; exact ⟨h0y i, hS2 i hi⟩
    · simp only [hi, if_false, Set.mem_Icc]; exact ⟨hS3 i hi, h1y i⟩
  · rintro ⟨⟨⟨h0t, h1t⟩, hlo⟩, hy⟩
    refine ⟨⟨⟨h0t, fun i => ?_⟩, h1t, fun i => ?_⟩, hlo, fun i hi => ?_, fun i hi => ?_⟩
    · have := hy i
      by_cases hi : p.succAbove i ∈ S
      · simp only [hi, if_true, Set.mem_Ico] at this; exact this.1
      · simp only [hi, if_false, Set.mem_Icc] at this; exact h0t.trans this.1
    · have := hy i
      by_cases hi : p.succAbove i ∈ S
      · simp only [hi, if_true, Set.mem_Ico] at this; exact (this.2.trans_le h1t).le
      · simp only [hi, if_false, Set.mem_Icc] at this; exact this.2
    · have := hy i
      simp only [hi, if_true, Set.mem_Ico] at this; exact this.2
    · have := hy i
      simp only [hi, if_false, Set.mem_Icc] at this; exact this.1

theorem cell_meas {N : ℕ} (p : Fin N) (S : Finset (Fin N)) (lo hi : ℝ) :
    MeasurableSet {x : Fin N → ℝ | x ∈ Set.Icc (0:Fin N → ℝ) 1 ∧ x p ∈ Set.Icc lo hi ∧
        (∀ j ∈ S, x j < x p) ∧ ∀ j ∉ S, x p ≤ x j} := by
  have h1 : MeasurableSet (Set.Icc (0:Fin N → ℝ) 1) := measurableSet_Icc
  have h0 : MeasurableSet {x : Fin N → ℝ | x p ∈ Set.Icc lo hi} :=
    (measurable_pi_apply p) measurableSet_Icc
  have h2 : MeasurableSet {x : Fin N → ℝ | ∀ j ∈ S, x j < x p} := by
    have : {x : Fin N → ℝ | ∀ j ∈ S, x j < x p} = ⋂ j ∈ S, {x | x j < x p} := by
      ext x; simp
    rw [this]
    exact Finset.measurableSet_biInter S fun j _ =>
      measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply p)
  have h3 : MeasurableSet {x : Fin N → ℝ | ∀ j ∉ S, x p ≤ x j} := by
    have : {x : Fin N → ℝ | ∀ j ∉ S, x p ≤ x j} = ⋂ j ∈ Sᶜ, {x | x p ≤ x j} := by
      ext x; simp
    rw [this]
    exact Finset.measurableSet_biInter Sᶜ fun j _ =>
      measurableSet_le (measurable_pi_apply p) (measurable_pi_apply j)
  exact h1.inter (h0.inter (h2.inter h3))

theorem cell_volume {k : ℕ} (p : Fin (k+1)) (S : Finset (Fin (k+1))) (hS : p ∉ S) (lo hi : ℝ) :
    volume {x : Fin (k+1) → ℝ | x ∈ Set.Icc (0:Fin (k+1) → ℝ) 1 ∧ x p ∈ Set.Icc lo hi ∧
        (∀ j ∈ S, x j < x p) ∧ ∀ j ∉ S, x p ≤ x j} =
    ENNReal.ofReal (∫ t in Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi, t ^ S.card * (1 - t) ^ (k - S.card)) := by
  classical
  set E := {x : Fin (k+1) → ℝ | x ∈ Set.Icc (0:Fin (k+1) → ℝ) 1 ∧ x p ∈ Set.Icc lo hi ∧
        (∀ j ∈ S, x j < x p) ∧ ∀ j ∉ S, x p ≤ x j} with hE
  have hEmeas : MeasurableSet E := cell_meas p S lo hi
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) p
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => (volume : Measure ℝ)) p
  have hAmeas : MeasurableSet (e.symm ⁻¹' E) := e.symm.measurable hEmeas
  have h1 : volume E = (volume.prod (Measure.pi fun _ : Fin k => (volume : Measure ℝ)))
      (e.symm ⁻¹' E) := by
    have := hmp.measure_preimage_equiv (e.symm ⁻¹' E)
    have e2 : e ⁻¹' (e.symm ⁻¹' E) = E := by ext x; simp
    rw [e2] at this
    exact this
  have hK : MeasurableSet (Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi) := measurableSet_Icc.inter measurableSet_Icc
  rw [h1]
  have hA := cell_set_eq p S hS lo hi
  have hAmeas' := hAmeas
  rw [hA] at hAmeas'
  rw [hA, Measure.prod_apply hAmeas']
  have hslice : ∀ t : ℝ, (Measure.pi fun _ : Fin k => (volume : Measure ℝ))
      (Prod.mk t ⁻¹' {q : ℝ × (Fin k → ℝ) | q.1 ∈ Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi ∧
      q.2 ∈ Set.pi Set.univ (fun j : Fin k =>
        if p.succAbove j ∈ S then Set.Ico 0 q.1 else Set.Icc q.1 1)}) =
      (Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi).indicator
        (fun t => ENNReal.ofReal t ^ S.card * ENNReal.ofReal (1 - t) ^ (k - S.card)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi
    · rw [Set.indicator_of_mem ht]
      have : Prod.mk t ⁻¹' {q : ℝ × (Fin k → ℝ) | q.1 ∈ Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi ∧
          q.2 ∈ Set.pi Set.univ (fun j : Fin k =>
            if p.succAbove j ∈ S then Set.Ico 0 q.1 else Set.Icc q.1 1)} =
          Set.pi Set.univ (fun j : Fin k =>
            if p.succAbove j ∈ S then Set.Ico 0 t else Set.Icc t 1) := by
        ext y
        exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩
      rw [this, Measure.pi_pi]
      have : ∀ j : Fin k, volume (if p.succAbove j ∈ S then Set.Ico 0 t else Set.Icc t 1) =
          if p.succAbove j ∈ S then ENNReal.ofReal t else ENNReal.ofReal (1 - t) := by
        intro j
        split_ifs
        · simp
        · simp
      simp_rw [this]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, card_filter_succAbove p S hS]
      congr 2
      have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
        (fun j : Fin k => p.succAbove j ∈ S)
      rw [card_filter_succAbove p S hS, Finset.card_univ, Fintype.card_fin] at h2
      omega
    · rw [Set.indicator_of_notMem ht]
      have : Prod.mk t ⁻¹' {q : ℝ × (Fin k → ℝ) | q.1 ∈ Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi ∧
          q.2 ∈ Set.pi Set.univ (fun j : Fin k =>
            if p.succAbove j ∈ S then Set.Ico 0 q.1 else Set.Icc q.1 1)} = ∅ := by
        ext y
        exact ⟨fun h => absurd h.1 ht, fun h => h.elim⟩
      rw [this]; simp
  simp_rw [hslice]
  rw [lintegral_indicator hK]
  have hnn : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi,
      ENNReal.ofReal t ^ S.card * ENNReal.ofReal (1 - t) ^ (k - S.card) =
      ENNReal.ofReal (t ^ S.card * (1 - t) ^ (k - S.card)) := by
    intro t ht
    rw [ENNReal.ofReal_mul (pow_nonneg ht.1.1 _), ENNReal.ofReal_pow ht.1.1,
      ENNReal.ofReal_pow (by linarith [ht.1.2])]
  rw [setLIntegral_congr_fun hK hnn]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · refine Continuous.integrableOn_Icc (by fun_prop) |>.mono_set Set.inter_subset_left
  · refine (ae_restrict_iff' hK).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have := ht.1.1
    have := ht.1.2
    show 0 ≤ t ^ S.card * (1 - t) ^ (k - S.card)
    exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)


theorem clamp_integral (f : ℝ → ℝ) (lo hi : ℝ) (h : lo ≤ hi) :
    ∫ t in Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi, f t = ∫ t in Set.Icc (clamp01 lo) (clamp01 hi), f t := by
  unfold clamp01
  rcases lt_or_ge hi 0 with h1 | h1
  · have e1 : Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi = ∅ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨a, b⟩, c, d⟩
      linarith
    have e2 : max 0 (min lo 1) = 0 := max_eq_left (min_le_of_left_le (by linarith))
    have e3 : max 0 (min hi 1) = 0 := max_eq_left (min_le_of_left_le (by linarith))
    rw [e1, e2, e3]
    simp [Set.Icc_self]
  · rcases lt_or_ge 1 lo with h2 | h2
    · have e1 : Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨a, b⟩, c, d⟩
        linarith
      have e2 : max 0 (min lo 1) = 1 := by
        rw [min_eq_right h2.le]; exact max_eq_right zero_le_one
      have e3 : max 0 (min hi 1) = 1 := by
        rw [min_eq_right (by linarith)]; exact max_eq_right zero_le_one
      rw [e1, e2, e3]
      simp [Set.Icc_self]
    · have e2 : max 0 (min lo 1) = max 0 lo := by rw [min_eq_left h2]
      have e3 : max 0 (min hi 1) = min hi 1 := max_eq_right (le_min h1 zero_le_one)
      have e4 : Set.Icc (0:ℝ) 1 ∩ Set.Icc lo hi = Set.Icc (max 0 lo) (min hi 1) := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Icc, max_le_iff, le_min_iff]
        tauto
      rw [e2, e3, e4]

theorem equation_3_5_core {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) (hS : S ⊆ Finset.univ.erase i)
    (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal =
      ∫ t in Set.Icc
        (clamp01 ((c - OceanicGames.Interior.wsum w (insert i S)) / alpha))
        (clamp01 ((c - OceanicGames.Interior.wsum w S) / alpha)),
        t ^ S.card * (1 - t) ^ (m - S.card - 1) := by
  classical
  have hiS : i ∉ S := fun h => by simpa using hS h
  have hws : OceanicGames.Interior.wsum w (insert i S) = OceanicGames.Interior.wsum w S + w i := by
    unfold OceanicGames.Interior.wsum
    rw [Finset.sum_insert hiS]; ring
  rw [hws]
  have hlh : (c - (OceanicGames.Interior.wsum w S + w i)) / alpha ≤
      (c - OceanicGames.Interior.wsum w S) / alpha := by
    apply div_le_div_of_nonneg_right _ halpha.le
    linarith [hw i]
  cases m with
  | zero => exact i.elim0
  | succ k =>
    have hset : OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S =
        {x : Fin (k+1) → ℝ | x ∈ Set.Icc (0:Fin (k+1) → ℝ) 1 ∧
          x i ∈ Set.Icc ((c - (OceanicGames.Interior.wsum w S + w i)) / alpha)
            ((c - OceanicGames.Interior.wsum w S) / alpha) ∧
          (∀ j ∈ S, x j < x i) ∧ ∀ j ∉ S, x i ≤ x j} := by
      rw [pivot_inter_order]
      ext x
      simp only [Set.mem_inter_iff, orderSet, Set.mem_setOf_eq, Set.mem_Icc, OceanicGames.Interior.cube]
      rw [div_le_iff₀ halpha, le_div_iff₀ halpha]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
        refine ⟨h1, ⟨by linarith, by linarith⟩, h2, h3⟩
      · rintro ⟨h1, ⟨h2, h3⟩, h4, h5⟩
        exact ⟨⟨h1, h4, h5⟩, by linarith, by linarith⟩
    rw [hset, cell_volume i S hiS, ENNReal.toReal_ofReal, clamp_integral _ _ _ hlh]
    · congr 1
      funext t
      rw [show k + 1 - S.card - 1 = k - S.card by omega]
    · apply setIntegral_nonneg (measurableSet_Icc.inter measurableSet_Icc)
      intro t ht
      exact mul_nonneg (pow_nonneg ht.1.1 _) (pow_nonneg (by linarith [ht.1.2]) _)

end OceanicGames.Limit

open OceanicGames.Limit
open MeasureTheory Set Finset

theorem solution {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin m)) (hS : S ⊆ Finset.univ.erase i)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal =
      ∫ t in Set.Icc
        (clamp01 ((c - OceanicGames.Interior.wsum w (insert i S)) / alpha))
        (clamp01 ((c - OceanicGames.Interior.wsum w S) / alpha)),
        t ^ S.card * (1 - t) ^ (m - S.card - 1) := by
  exact equation_3_5_core c alpha w i S hS halpha hw
