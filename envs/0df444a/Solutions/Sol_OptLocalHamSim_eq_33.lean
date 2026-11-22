-- Prove2me | solution 1 for OptLocalHamSim.eq_33
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T03:23:48.794782+00:00
-- url     : https://prove2.me/submissions/cd3e9741-c857-4ae1-90fe-93eeb6d89e63

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal

namespace OptLocalHamSim

/-- The open chain region `0 < s 0 < ... < s (k-1) < h`. -/
def R (k : ℕ) (h : ℝ) : Set (Fin k → ℝ) :=
  {s | (∀ i, 0 < s i ∧ s i < h) ∧ StrictMono s}

/-- Prefix sums of `qq i + 1`. -/
def b (k : ℕ) (qq : Fin k → ℕ) (i : Fin k) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin k => a ≤ i), ((qq a : ℝ) + 1)

lemma measurableSet_strictMono (k : ℕ) : MeasurableSet {s : Fin k → ℝ | StrictMono s} := by
  cases k with
  | zero =>
    have h : {s : Fin 0 → ℝ | StrictMono s} = univ := by
      ext s
      simp [StrictMono]
    rw [h]
    exact MeasurableSet.univ
  | succ n =>
    have h : {s : Fin (n+1) → ℝ | StrictMono s}
        = ⋂ i : Fin n, {s : Fin (n+1) → ℝ | s i.castSucc < s i.succ} := by
      ext s
      simp only [mem_setOf_eq, mem_iInter]
      exact Fin.strictMono_iff_lt_succ
    rw [h]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt (measurable_pi_apply i.castSucc) (measurable_pi_apply i.succ)

lemma measurableSet_R (k : ℕ) (h : ℝ) : MeasurableSet (R k h) := by
  unfold R
  have h1 : MeasurableSet {s : Fin k → ℝ | ∀ i, 0 < s i ∧ s i < h} := by
    have hEq : {s : Fin k → ℝ | ∀ i, 0 < s i ∧ s i < h}
        = ⋂ i, ({s : Fin k → ℝ | 0 < s i} ∩ {s : Fin k → ℝ | s i < h}) := by
      ext s
      simp
    rw [hEq]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const)
  exact h1.inter (measurableSet_strictMono k)

lemma measurableSet_R_prod (k : ℕ) :
    MeasurableSet {z : ℝ × (Fin k → ℝ) | z.2 ∈ R k z.1} := by
  unfold R
  have h1 : MeasurableSet {z : ℝ × (Fin k → ℝ) | ∀ j, 0 < z.2 j ∧ z.2 j < z.1} := by
    have hEq : {z : ℝ × (Fin k → ℝ) | ∀ j, 0 < z.2 j ∧ z.2 j < z.1}
        = ⋂ j, ({z : ℝ × (Fin k → ℝ) | 0 < z.2 j}
            ∩ {z : ℝ × (Fin k → ℝ) | z.2 j < z.1}) := by
      ext z
      simp
    rw [hEq]
    exact MeasurableSet.iInter fun j =>
      (measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_snd)).inter
        (measurableSet_lt ((measurable_pi_apply j).comp measurable_snd) measurable_fst)
  have h2 : MeasurableSet {z : ℝ × (Fin k → ℝ) | StrictMono z.2} :=
    (measurableSet_strictMono k).preimage measurable_snd
  exact h1.inter h2

lemma strictMono_insertNth_iff {k : ℕ} (t : ℝ) (s' : Fin k → ℝ) :
    StrictMono (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') ↔ StrictMono s' ∧ ∀ j : Fin k, s' j < t := by
  have hcast : ∀ j : Fin k, (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') (Fin.castSucc j) = s' j := by
    intro j
    rw [← Fin.succAbove_last]
    exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s' _
  have hlast : (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') (Fin.last k) = t := by
    simp only [Fin.insertNth_apply_same]
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · intro i j hij
      have := hs (Fin.castSucc_lt_castSucc_iff.mpr hij)
      rwa [hcast i, hcast j] at this
    · intro j
      have := hs (Fin.castSucc_lt_last j)
      rwa [hcast j, hlast] at this
  · rintro ⟨hs', hlt⟩ i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [hcast i, hcast j]
        exact hs' (Fin.castSucc_lt_castSucc_iff.mpr hij)
      · rw [hcast i, hlast]
        exact hlt i
    · exact absurd hij (Fin.not_lt.mpr (Fin.le_last j))

lemma insertNth_mem_R {k : ℕ} (h t : ℝ) (s' : Fin k → ℝ) :
    (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') ∈ R (k+1) h ↔ t ∈ Ioo (0:ℝ) h ∧ s' ∈ R k t := by
  have hcast : ∀ j : Fin k, (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') (Fin.castSucc j) = s' j := by
    intro j
    rw [← Fin.succAbove_last]
    exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s' _
  have hlast : (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') (Fin.last k) = t := by
    simp only [Fin.insertNth_apply_same]
  constructor
  · rintro ⟨hb, hmono⟩
    have ht : t ∈ Ioo (0:ℝ) h := by
      have := hb (Fin.last k)
      rwa [hlast] at this
    have hmono' : StrictMono s' := by
      intro i j hij
      have := hmono (Fin.castSucc_lt_castSucc_iff.mpr hij)
      rwa [hcast i, hcast j] at this
    refine ⟨ht, ?_, hmono'⟩
    intro j
    exact ⟨by
      have := hb (Fin.castSucc j)
      rw [hcast j] at this
      exact this.1,
    by
      have := hmono (Fin.castSucc_lt_last j)
      rwa [hcast j, hlast] at this⟩
  · rintro ⟨⟨ht0, hth⟩, hb, hmono⟩
    constructor
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [hcast j]
        exact ⟨(hb j).1, lt_trans (hb j).2 hth⟩
      · rw [hlast]
        exact ⟨ht0, hth⟩
    · rw [strictMono_insertNth_iff]
      exact ⟨hmono, fun j => (hb j).2⟩

lemma b_last (k : ℕ) (qq : Fin (k+1) → ℕ) :
    b (k+1) qq (Fin.last k) = ((∑ i, (qq i + 1) : ℕ) : ℝ) := by
  unfold b
  rw [Finset.filter_true_of_mem (fun a _ => Fin.le_last a)]
  push_cast
  rfl

lemma b_castSucc (k : ℕ) (qq : Fin (k+1) → ℕ) (j : Fin k) :
    b (k+1) qq (Fin.castSucc j) = b k (fun i => qq (Fin.castSucc i)) j := by
  unfold b
  refine Finset.sum_bij (fun a ha => (⟨a.1, ?_⟩ : Fin k)) ?_ ?_ ?_ ?_
  · have ha' : a ≤ Fin.castSucc j := (Finset.mem_filter.mp ha).2
    have := Fin.le_castSucc_iff.mp ha'
    simp only [Fin.lt_def, Fin.val_succ] at this
    omega
  · intro a ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have ha' : a ≤ Fin.castSucc j := (Finset.mem_filter.mp ha).2
    have h1 : a.1 ≤ j.1 := by
      have := Fin.le_castSucc_iff.mp ha'
      simp only [Fin.lt_def, Fin.val_succ] at this
      omega
    simpa [Fin.le_def] using h1
  · intro a ha a' ha' heq
    apply Fin.ext
    simpa using congrArg Fin.val heq
  · intro bb hb
    refine ⟨Fin.castSucc bb, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hb' : bb ≤ j := (Finset.mem_filter.mp hb).2
      exact Fin.castSucc_le_castSucc_iff.mpr hb'
    · apply Fin.ext
      simp
  · intro a ha
    congr 2

set_option maxHeartbeats 1600000 in
lemma main : ∀ (k : ℕ) (qq : Fin k → ℕ) (h : ℝ), 0 < h →
    ∫ s : Fin k → ℝ, (R k h).indicator (fun s => ∏ i, s i ^ qq i) s
      = h ^ (∑ i, (qq i + 1)) / ∏ i, (b k qq i) := by
  classical
  intro k
  induction k with
  | zero =>
    intro qq h hh
    have hR : R 0 h = univ := by
      ext s
      exact ⟨fun _ => mem_univ _, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
    rw [hR]
    have hprod : (fun s : Fin 0 → ℝ => ∏ i, s i ^ qq i) = fun _ => (1:ℝ) := by
      funext s
      simp
    simp only [hprod, Set.indicator_univ]
    rw [integral_const]
    have hvol : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp
    have hreal : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
      rw [Measure.real, hvol]
      simp
    simp [hreal]
  | succ k ih =>
    intro qq h hh
    set S : ℕ := ∑ j : Fin k, (qq (Fin.castSucc j) + 1) with hS
    set B : ℝ := ∏ j : Fin k, b k (fun i => qq (Fin.castSucc i)) j with hB
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => ℝ) (Fin.last k) with he
    have hmp : MeasurePreserving e volume (volume.prod volume) := by
      have h := measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => (volume : Measure ℝ)) (Fin.last k)
      simpa only [← volume_pi] using h
    let G : ℝ × (Fin k → ℝ) → ℝ := fun z =>
      (Ioo (0:ℝ) h).indicator (fun t => t ^ qq (Fin.last k) *
        ((R k t).indicator (fun s' => ∏ j, s' j ^ qq (Fin.castSucc j)) z.2)) z.1
    have hesymm : ∀ (z : ℝ × (Fin k → ℝ)), (e.symm z : Fin (k+1) → ℝ) = Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) z.1 z.2 := by
      rintro ⟨t, s'⟩
      funext i
      simp only [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
    have hpoint : ∀ z : ℝ × (Fin k → ℝ),
        (R (k+1) h).indicator (fun s => ∏ i, s i ^ qq i) (e.symm z) = G z := by
      rintro ⟨t, s'⟩
      rw [hesymm]
      have hcast' : ∀ x : Fin k, (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') (Fin.castSucc x) = s' x := by
        intro x
        rw [← Fin.succAbove_last]
        exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s' _
      have hprod : (∏ i : Fin (k+1), (Fin.insertNth (α := fun _ : Fin (k+1) => ℝ) (Fin.last k) t s') i ^ qq i)
          = t ^ qq (Fin.last k) * ∏ j : Fin k, s' j ^ qq (Fin.castSucc j) := by
        rw [Fin.prod_univ_castSucc]
        simp only [hcast', Fin.insertNth_apply_same]
        ring
      simp only [G, Set.indicator_apply]
      by_cases hz : t ∈ Ioo (0:ℝ) h
      · rw [if_pos hz]
        by_cases hs : s' ∈ R k t
        · rw [if_pos hs, if_pos (insertNth_mem_R h t s' |>.mpr ⟨hz, hs⟩), hprod]
        · rw [if_neg hs, if_neg (fun hh' => hs (insertNth_mem_R h t s' |>.mp hh').2)]
          try ring
      · rw [if_neg hz, if_neg (fun hh' => hz (insertNth_mem_R h t s' |>.mp hh').1)]
    have hGmeas : Measurable G := by
      have hbase : Measurable (fun z : ℝ × (Fin k → ℝ) => z.1 ^ qq (Fin.last k) * ∏ j, z.2 j ^ qq (Fin.castSucc j)) := by
        fun_prop
      have hset : MeasurableSet {z : ℝ × (Fin k → ℝ) | z.1 ∈ Ioo (0:ℝ) h ∧ z.2 ∈ R k z.1} :=
        (measurableSet_Ioo.preimage measurable_fst).inter (measurableSet_R_prod k)
      have hEq : G = {z : ℝ × (Fin k → ℝ) | z.1 ∈ Ioo (0:ℝ) h ∧ z.2 ∈ R k z.1}.indicator
          (fun z => z.1 ^ qq (Fin.last k) * ∏ j, z.2 j ^ qq (Fin.castSucc j)) := by
        funext z
        by_cases h1 : z.1 ∈ Ioo (0:ℝ) h
        · by_cases h2 : z.2 ∈ R k z.1
          · simp only [G]
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
              Set.indicator_of_mem (show z ∈ {z : ℝ × (Fin k → ℝ) | z.1 ∈ Ioo (0:ℝ) h ∧ z.2 ∈ R k z.1} from ⟨h1, h2⟩)]
          · simp only [G]
            rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (show z ∉ {z : ℝ × (Fin k → ℝ) | z.1 ∈ Ioo (0:ℝ) h ∧ z.2 ∈ R k z.1} from fun hc => h2 hc.2)]
            try ring
        · simp only [G]
          rw [Set.indicator_of_notMem h1,
            Set.indicator_of_notMem (show z ∉ {z : ℝ × (Fin k → ℝ) | z.1 ∈ Ioo (0:ℝ) h ∧ z.2 ∈ R k z.1} from fun hc => h1 hc.1)]
      rw [hEq]
      exact hbase.indicator hset
    have hsupp : Function.support G ⊆ Ioo (0:ℝ) h ×ˢ univ.pi (fun _ : Fin k => Ioo (0:ℝ) h) := by
      rintro ⟨t, s'⟩ hz
      by_cases ht : t ∈ Ioo (0:ℝ) h
      · refine ⟨ht, ?_⟩
        by_contra hcon
        apply hz
        have hz0 : G (t, s') = 0 := by
          have hnotmem : s' ∉ R k t := by
            intro hmem
            exact hcon (fun j _ => ⟨(hmem.1 j).1, lt_trans (hmem.1 j).2 ht.2⟩)
          simp only [G, Set.indicator_of_mem ht, Set.indicator_of_notMem hnotmem]
          ring
        exact hz0
      · exfalso
        apply hz
        simp only [G, Set.indicator_of_notMem ht]
    have hboxfin : (volume.prod volume) (Ioo (0:ℝ) h ×ˢ univ.pi (fun _ : Fin k => Ioo (0:ℝ) h)) ≠ ∞ := by
      rw [Measure.prod_prod]
      rw [show (volume : Measure (Fin k → ℝ)) (univ.pi (fun _ : Fin k => Ioo (0:ℝ) h))
          = ∏ _i : Fin k, volume (Ioo (0:ℝ) h) from by
        rw [volume_pi, Measure.pi_pi]]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Real.volume_Ioo, sub_zero]
      exact ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne (ENNReal.pow_ne_top ENNReal.ofReal_lt_top.ne)
    have hbox_meas : MeasurableSet (Ioo (0:ℝ) h ×ˢ univ.pi (fun _ : Fin k => Ioo (0:ℝ) h)) :=
      measurableSet_Ioo.prod (MeasurableSet.pi Set.finite_univ.countable (fun i _ => measurableSet_Ioo))
    have hGint : Integrable G (volume.prod volume) := by
      rw [← integrableOn_iff_integrable_of_support_subset hsupp]
      haveI : IsFiniteMeasure ((volume.prod volume).restrict (Ioo (0:ℝ) h ×ˢ univ.pi (fun _ : Fin k => Ioo (0:ℝ) h))) :=
        ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact lt_top_iff_ne_top.mpr hboxfin⟩
      refine Integrable.of_bound hGmeas.aestronglyMeasurable
        ((max 1 h) ^ (qq (Fin.last k) + ∑ j : Fin k, qq (Fin.castSucc j))) ?_
      filter_upwards [ae_restrict_mem hbox_meas] with z hz
      obtain ⟨ht, hs⟩ := hz
      have hs' : ∀ j : Fin k, 0 < z.2 j ∧ z.2 j < h := by
        intro j
        exact (Set.mem_univ_pi.mp hs) j
      have hmax : (0:ℝ) < max 1 h := lt_of_lt_of_le zero_lt_one (le_max_left 1 h)
      have hzh : z.1 ≤ max 1 h := le_trans ht.2.le (le_max_right 1 h)
      have hzh0 : (0:ℝ) ≤ z.1 := ht.1.le
      by_cases hmem : z.2 ∈ R k z.1
      · have hprod_nn : (0:ℝ) ≤ ∏ j : Fin k, z.2 j ^ qq (Fin.castSucc j) :=
          Finset.prod_nonneg (fun j _ => pow_nonneg (hs' j).1.le _)
        have hval : ‖G z‖ = z.1 ^ qq (Fin.last k) * ∏ j, z.2 j ^ qq (Fin.castSucc j) := by
          have hEq : G z = z.1 ^ qq (Fin.last k) * ∏ j, z.2 j ^ qq (Fin.castSucc j) := by
            simp only [G, Set.indicator_of_mem ht, Set.indicator_of_mem hmem]
          rw [hEq]
          exact abs_of_nonneg (mul_nonneg (pow_nonneg hzh0 _) hprod_nn)
        rw [hval]
        have h1 : z.1 ^ qq (Fin.last k) ≤ (max 1 h) ^ qq (Fin.last k) :=
          pow_le_pow_left₀ hzh0 hzh _
        have h2 : (∏ j : Fin k, z.2 j ^ qq (Fin.castSucc j)) ≤ ∏ j : Fin k, (max 1 h) ^ qq (Fin.castSucc j) := by
          apply Finset.prod_le_prod
          · intro j _
            exact pow_nonneg (hs' j).1.le _
          · intro j _
            exact pow_le_pow_left₀ (hs' j).1.le (le_trans (hs' j).2.le (le_max_right 1 h)) _
        have h3 : (∏ j : Fin k, (max 1 h) ^ qq (Fin.castSucc j))
            = (max 1 h) ^ (∑ j : Fin k, qq (Fin.castSucc j)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
        calc z.1 ^ qq (Fin.last k) * ∏ j : Fin k, z.2 j ^ qq (Fin.castSucc j)
            ≤ (max 1 h) ^ qq (Fin.last k) * (max 1 h) ^ (∑ j : Fin k, qq (Fin.castSucc j)) := by
              rw [← h3]
              exact mul_le_mul h1 h2 hprod_nn (pow_nonneg hmax.le _)
          _ = (max 1 h) ^ (qq (Fin.last k) + ∑ j : Fin k, qq (Fin.castSucc j)) := by
              rw [← pow_add]
      · have hval : G z = 0 := by
          simp only [G, Set.indicator_of_mem ht, Set.indicator_of_notMem hmem]
          ring
        rw [hval, norm_zero]
        exact (by positivity : (0:ℝ) ≤ (max 1 h) ^ (qq (Fin.last k) + ∑ j : Fin k, qq (Fin.castSucc j)))
    have hchange : (∫ s : Fin (k+1) → ℝ, (R (k+1) h).indicator (fun s => ∏ i, s i ^ qq i) s)
        = ∫ z : ℝ × (Fin k → ℝ), (R (k+1) h).indicator (fun s => ∏ i, s i ^ qq i) (e.symm z) ∂(volume.prod volume) := by
      have h := hmp.integral_comp' (fun z : ℝ × (Fin k → ℝ) =>
        (R (k+1) h).indicator (fun s => ∏ i, s i ^ qq i) (e.symm z))
      simpa using h
    have hchange2 : (∫ z : ℝ × (Fin k → ℝ), (R (k+1) h).indicator (fun s => ∏ i, s i ^ qq i) (e.symm z) ∂(volume.prod volume))
        = ∫ z : ℝ × (Fin k → ℝ), G z ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    rw [hchange, hchange2, integral_prod G hGint]
    have hinner : ∀ t : ℝ, (∫ s' : Fin k → ℝ, G (t, s'))
        = (Ioo (0:ℝ) h).indicator
            (fun u => u ^ qq (Fin.last k) * (u ^ S / B)) t := by
      intro t
      by_cases ht : t ∈ Ioo (0:ℝ) h
      · rw [Set.indicator_of_mem ht]
        have hfun : ∀ s' : Fin k → ℝ, G (t, s')
            = t ^ qq (Fin.last k) * ((R k t).indicator (fun s' => ∏ j, s' j ^ qq (Fin.castSucc j)) s') := by
          intro s'
          simp only [G, Set.indicator_of_mem ht]
        rw [show (∫ s', G (t, s')) = ∫ s', t ^ qq (Fin.last k) *
            ((R k t).indicator (fun s' => ∏ j, s' j ^ qq (Fin.castSucc j)) s') from by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hfun]
        rw [integral_const_mul]
        rw [show (∫ s' : Fin k → ℝ, (R k t).indicator (fun s' => ∏ j, s' j ^ qq (Fin.castSucc j)) s')
            = t ^ (∑ j : Fin k, (qq (Fin.castSucc j) + 1)) / ∏ j : Fin k, b k (fun i => qq (Fin.castSucc i)) j
            from ih (fun i => qq (Fin.castSucc i)) t ht.1]
      · rw [Set.indicator_of_notMem ht]
        have hfun : ∀ s' : Fin k → ℝ, G (t, s') = 0 := by
          intro s'
          simp only [G, Set.indicator_of_notMem ht]
        rw [show (∫ s', G (t, s')) = ∫ s', (0:ℝ) from by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hfun]
        simp
    rw [funext hinner, integral_indicator measurableSet_Ioo]
    have hIoo : (∫ t in Ioo (0:ℝ) h, t ^ qq (Fin.last k) * (t ^ S / B))
        = h ^ (qq (Fin.last k) + S + 1) / (((qq (Fin.last k) + S + 1 : ℕ)) : ℝ) / B := by
      have hfun : ∀ t : ℝ, t ^ qq (Fin.last k) * (t ^ S / B) = t ^ (qq (Fin.last k) + S) / B := by
        intro t
        rw [← mul_div_assoc, ← pow_add]
      rw [show (∫ t in Ioo (0:ℝ) h, t ^ qq (Fin.last k) * (t ^ S / B))
          = ∫ t in Ioo (0:ℝ) h, t ^ (qq (Fin.last k) + S) / B from by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hfun]
      rw [integral_div]
      rw [show (∫ t in Ioo (0:ℝ) h, t ^ (qq (Fin.last k) + S))
          = h ^ (qq (Fin.last k) + S + 1) / (((qq (Fin.last k) + S + 1 : ℕ)) : ℝ) from by
        rw [← integral_Ioc_eq_integral_Ioo]
        rw [← intervalIntegral.integral_of_le (le_of_lt hh)]
        rw [integral_pow]
        push_cast
        simp]
    rw [hIoo]
    have hsum : (∑ i : Fin (k+1), (qq i + 1)) = (qq (Fin.last k) + 1) + S := by
      rw [Fin.sum_univ_castSucc, hS]
      omega
    have hprodR : (∏ i : Fin (k+1), b (k+1) qq i)
        = B * ((∑ i : Fin (k+1), (qq i + 1) : ℕ) : ℝ) := by
      rw [Fin.prod_univ_castSucc, b_last]
      have h1 : (∏ i : Fin k, b (k+1) qq (Fin.castSucc i))
          = ∏ j : Fin k, b k (fun i => qq (Fin.castSucc i)) j :=
        Finset.prod_congr rfl (fun j _ => b_castSucc k qq j)
      rw [h1, ← hB]
    rw [hprodR, hsum]
    have hE : qq (Fin.last k) + S + 1 = (qq (Fin.last k) + 1) + S := by omega
    rw [hE, div_div]
    congr 1
    ring

end OptLocalHamSim

/-- `OptLocalHamSim.eq_33`: the scalar time integral of the Dyson expansion over the open chain
`0 < s 0 < ... < s (k-1) < h` equals `h^(∑ i, (qq i + 1)) / ∏ i, (∑ a ≤ i, (qq a + 1))`. -/
theorem solution (k : ℕ) (qq : Fin k → ℕ) (h : ℝ) (hh : 0 < h) :
    ∫ s : Fin k → ℝ, Set.indicator {s : Fin k → ℝ | (∀ i, 0 < s i ∧ s i < h) ∧ StrictMono s}
        (fun s => ∏ i, s i ^ qq i) s =
      h ^ (∑ i, (qq i + 1)) /
        ∏ i, (∑ a ∈ Finset.univ.filter (fun a : Fin k => a ≤ i), ((qq a : ℝ) + 1)) := by
  have hmain := OptLocalHamSim.main k qq h hh
  simpa only [OptLocalHamSim.R, OptLocalHamSim.b] using hmain
