-- Prove2me | solution 1 for TailRiskSharing.TailConv.infConv_lawInvariant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:19:00.523112+00:00
-- url     : https://prove2.me/submissions/82ef7c6f-5171-400e-8d2a-cfd505834452

import Mathlib
import Definitions.Def_TailRiskSharing_TailConv_Setting
import Theorems.Thm_TailRiskSharing_TailConv_infConv_monotone

set_option autoImplicit false

open MeasureTheory

namespace TCLI

variable {Ω : Type*} [MeasurableSpace Ω]

lemma atomless_real (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) {s : Set Ω} (hs : MeasurableSet s)
    (hpos : 0 < P.real s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < P.real t ∧ P.real t < P.real s := by
  have h1 : 0 < P s := by
    rw [measureReal_def] at hpos
    exact ENNReal.toReal_pos_iff.mp hpos |>.1
  obtain ⟨t, hts, htm, ht0, hts'⟩ := hP s hs h1
  refine ⟨t, hts, htm, ?_, ?_⟩
  · rw [measureReal_def]; exact ENNReal.toReal_pos ht0.ne' (measure_ne_top _ _)
  · rw [measureReal_def, measureReal_def]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hts'

lemma small_subset_pow (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) {s : Set Ω} (hs : MeasurableSet s)
    (hpos : 0 < P.real s) (k : ℕ) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < P.real t ∧ P.real t ≤ P.real s / 2 ^ k := by
  induction k with
  | zero => exact ⟨s, subset_rfl, hs, hpos, by simp⟩
  | succ k ih =>
    obtain ⟨t, hts, htm, ht0, htk⟩ := ih
    obtain ⟨u, hut, hum, hu0, hut'⟩ := atomless_real P hP htm ht0
    by_cases hhalf : P.real u ≤ P.real t / 2
    · refine ⟨u, hut.trans hts, hum, hu0, ?_⟩
      rw [pow_succ]
      calc P.real u ≤ P.real t / 2 := hhalf
        _ ≤ (P.real s / 2 ^ k) / 2 := by linarith
        _ = P.real s / (2 ^ k * 2) := by ring
    · push Not at hhalf
      have hdiff : P.real (t \ u) = P.real t - P.real u := measureReal_sdiff hut hum
      refine ⟨t \ u, Set.diff_subset.trans hts, htm.diff hum, by linarith, ?_⟩
      rw [pow_succ]
      calc P.real (t \ u) ≤ P.real t / 2 := by linarith
        _ ≤ (P.real s / 2 ^ k) / 2 := by linarith
        _ = P.real s / (2 ^ k * 2) := by ring

lemma small_subset (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) {s : Set Ω} (hs : MeasurableSet s)
    (hpos : 0 < P.real s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < P.real t ∧ P.real t ≤ δ := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ / P.real s by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨t, hts, htm, ht0, htk⟩ := small_subset_pow P hP hs hpos k
  refine ⟨t, hts, htm, ht0, le_trans htk ?_⟩
  have : P.real s / 2 ^ k = (1/2)^k * P.real s := by rw [one_div_pow]; ring
  rw [lt_div_iff₀ hpos] at hk
  linarith

/-- Sierpiński: an atomless probability measure takes every intermediate value on subsets. -/
theorem sierpinski (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) {s : Set Ω} (hs : MeasurableSet s)
    {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ P.real s) :
    ∃ t ⊆ s, MeasurableSet t ∧ P.real t = x := by
  classical
  -- candidates
  let cand : Set Ω → Set ℝ := fun C =>
    {r | ∃ D ⊆ s \ C, MeasurableSet D ∧ P.real C + P.real D ≤ x ∧ r = P.real D}
  let σ : Set Ω → ℝ := fun C => sSup (cand C)
  have hbdd : ∀ C, BddAbove (cand C) := fun C =>
    ⟨1, fun r ⟨D, _, _, _, hr⟩ => hr ▸ measureReal_le_one⟩
  have hgood : ∀ C, P.real C ≤ x → ∃ D ⊆ s \ C, MeasurableSet D ∧ P.real C + P.real D ≤ x ∧
      σ C / 2 ≤ P.real D := by
    intro C hC
    have hne : (cand C).Nonempty := ⟨0, ∅, Set.empty_subset _, MeasurableSet.empty,
      by simp; exact hC, by simp⟩
    by_cases hσ : σ C ≤ 0
    · exact ⟨∅, Set.empty_subset _, MeasurableSet.empty, by simp; exact hC, by simp; linarith⟩
    · push Not at hσ
      obtain ⟨r, ⟨D, hD, hDm, hDx, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne
        (show σ C / 2 < σ C by linarith)
      exact ⟨D, hD, hDm, hDx, hr.le⟩
  let good : Set Ω → Prop := fun C => MeasurableSet C ∧ C ⊆ s ∧ P.real C ≤ x
  let step : Set Ω → Set Ω := fun C =>
    if h : good C then C ∪ Classical.choose (hgood C h.2.2) else C
  let Cs : ℕ → Set Ω := fun k => step^[k] ∅
  have hCs_succ : ∀ k, Cs (k + 1) = step (Cs k) := fun k => by
    simp only [Cs]; rw [Function.iterate_succ_apply']
  have hinv : ∀ k, good (Cs k) := by
    intro k
    induction k with
    | zero => exact ⟨MeasurableSet.empty, Set.empty_subset _, by simp [Cs]; exact hx0⟩
    | succ k ih =>
      rw [hCs_succ]
      simp only [step, dif_pos ih]
      obtain ⟨hD, hDm, hDx, -⟩ := Classical.choose_spec (hgood (Cs k) ih.2.2)
      refine ⟨ih.1.union hDm, Set.union_subset ih.2.1 (hD.trans Set.diff_subset), ?_⟩
      rw [measureReal_union (Set.disjoint_of_subset_right hD Set.disjoint_sdiff_right) hDm]
      exact hDx
  have hinc : ∀ k, P.real (Cs k) + σ (Cs k) / 2 ≤ P.real (Cs (k + 1)) := by
    intro k
    rw [hCs_succ]
    simp only [step, dif_pos (hinv k)]
    obtain ⟨hD, hDm, -, hσD⟩ := Classical.choose_spec (hgood (Cs k) (hinv k).2.2)
    rw [measureReal_union (Set.disjoint_of_subset_right hD Set.disjoint_sdiff_right) hDm]
    linarith
  have hmono : Monotone Cs := by
    apply monotone_nat_of_le_succ
    intro k
    rw [hCs_succ]
    simp only [step, dif_pos (hinv k)]
    exact Set.subset_union_left
  let C := ⋃ k, Cs k
  have hCm : MeasurableSet C := MeasurableSet.iUnion fun k => (hinv k).1
  have hCs : C ⊆ s := Set.iUnion_subset fun k => (hinv k).2.1
  have hlim : Filter.Tendsto (fun k => P.real (Cs k)) Filter.atTop (nhds (P.real C)) :=
    (ENNReal.tendsto_toReal (measure_ne_top P C)).comp (tendsto_measure_iUnion_atTop hmono)
  have hCx : P.real C ≤ x := le_of_tendsto' hlim fun k => (hinv k).2.2
  refine ⟨C, hCs, hCm, le_antisymm hCx ?_⟩
  by_contra hlt
  push Not at hlt
  have hpos : 0 < P.real (s \ C) := by
    rw [measureReal_sdiff hCs hCm]; linarith
  obtain ⟨D, hD, hDm, hD0, hDle⟩ := small_subset P hP (hs.diff hCm) hpos
    (show 0 < x - P.real C by linarith)
  have hσ : ∀ k, P.real D ≤ σ (Cs k) := by
    intro k
    apply le_csSup (hbdd _)
    refine ⟨D, fun ω hω => ⟨(hD hω).1, fun h => (hD hω).2 (Set.mem_iUnion.mpr ⟨k, h⟩)⟩, hDm,
      ?_, rfl⟩
    have : P.real (Cs k) ≤ P.real C := measureReal_mono (Set.subset_iUnion _ k)
    linarith
  have hgrow : ∀ k : ℕ, (k : ℝ) * (P.real D / 2) ≤ P.real (Cs k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hinc k
      have := hσ k
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / P.real D)
  have h1 := hgrow k
  have h3 : (2 / P.real D) * (P.real D / 2) < (k : ℝ) * (P.real D / 2) :=
    mul_lt_mul_of_pos_right hk (by positivity)
  have h2 : P.real (Cs k) ≤ 1 := measureReal_le_one
  have : (2 / P.real D) * (P.real D / 2) = 1 := by field_simp
  nlinarith

/-- Nested Sierpiński. -/
theorem sierpinski_nested (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) {C D : Set Ω} (hC : MeasurableSet C)
    (hD : MeasurableSet D) (hCD : C ⊆ D) {x : ℝ} (hx0 : P.real C ≤ x) (hx1 : x ≤ P.real D) :
    ∃ E, C ⊆ E ∧ E ⊆ D ∧ MeasurableSet E ∧ P.real E = x := by
  have hdiff : P.real (D \ C) = P.real D - P.real C := measureReal_sdiff hCD hC
  obtain ⟨t, ht, htm, htx⟩ := sierpinski P hP (hD.diff hC) (x := x - P.real C) (by linarith)
    (by linarith)
  refine ⟨C ∪ t, Set.subset_union_left, Set.union_subset hCD (ht.trans Set.diff_subset),
    hC.union htm, ?_⟩
  rw [measureReal_union (Set.disjoint_of_subset_right ht Set.disjoint_sdiff_right) htm]
  linarith


section Dyadic

variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)

open Classical in
/-- midpoint set. -/
noncomputable def midSet (C D : Set Ω) : Set Ω :=
  if h : MeasurableSet C ∧ MeasurableSet D ∧ C ⊆ D then
    Classical.choose (sierpinski_nested P hP h.1 h.2.1 h.2.2
      (x := (P.real C + P.real D) / 2) (by linarith [measureReal_mono (μ := P) h.2.2])
      (by linarith [measureReal_mono (μ := P) h.2.2]))
  else C

lemma midSet_spec {C D : Set Ω} (hC : MeasurableSet C) (hD : MeasurableSet D) (hCD : C ⊆ D) :
    C ⊆ midSet P hP C D ∧ midSet P hP C D ⊆ D ∧ MeasurableSet (midSet P hP C D) ∧
      P.real (midSet P hP C D) = (P.real C + P.real D) / 2 := by
  have h : MeasurableSet C ∧ MeasurableSet D ∧ C ⊆ D := ⟨hC, hD, hCD⟩
  unfold midSet
  rw [dif_pos h]
  exact Classical.choose_spec (sierpinski_nested P hP h.1 h.2.1 h.2.2
      (x := (P.real C + P.real D) / 2) (by linarith [measureReal_mono (μ := P) h.2.2])
      (by linarith [measureReal_mono (μ := P) h.2.2]))

/-- dyadic family `c k m ≈ C_{m/2^k}`. -/
noncomputable def dy (E : Set Ω) : ℕ → ℕ → Set Ω
  | 0 => fun m => if m = 0 then ∅ else E
  | k + 1 => fun m => if m % 2 = 0 then dy E k (m / 2) else
      midSet P hP (dy E k (m / 2)) (dy E k (m / 2 + 1))

lemma dy_props (E : Set Ω) (hE : MeasurableSet E) (k : ℕ) :
    (∀ m, MeasurableSet (dy P hP E k m)) ∧ (∀ m, dy P hP E k m ⊆ dy P hP E k (m + 1)) ∧
    (∀ m, dy P hP E k m ⊆ E) ∧ (∀ m, 2 ^ k ≤ m → dy P hP E k m = E) ∧
    (∀ m, m ≤ 2 ^ k → P.real (dy P hP E k m) = m / 2 ^ k * P.real E) := by
  induction k with
  | zero =>
    refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m hm => ?_, fun m hm => ?_⟩
    · simp only [dy]; split_ifs; exacts [MeasurableSet.empty, hE]
    · simp only [dy]; split_ifs <;> simp_all
    · simp only [dy]; split_ifs <;> simp
    · simp only [dy]; simp at hm; rw [if_neg (by omega)]
    · simp only [dy]; simp at hm
      interval_cases m <;> simp
  | succ k ih =>
    obtain ⟨hm, hmono, hsub, htop, hmeas⟩ := ih
    have hmid := fun m => midSet_spec P hP (hm (m / 2)) (hm (m / 2 + 1)) (hmono (m / 2))
    refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m hm2 => ?_, fun m hm2 => ?_⟩
    · simp only [dy]; split_ifs
      · exact hm _
      · exact (hmid m).2.2.1
    · simp only [dy]
      rcases Nat.even_or_odd m with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · have h1 : (a + a) % 2 = 0 := by omega
        have h2 : (a + a + 1) % 2 ≠ 0 := by omega
        rw [if_pos h1, if_neg h2]
        have h3 : (a + a + 1) / 2 = (a + a) / 2 := by omega
        rw [h3]
        exact (hmid (a + a)).1
      · have h1 : (2 * a + 1) % 2 ≠ 0 := by omega
        have h2 : (2 * a + 1 + 1) % 2 = 0 := by omega
        rw [if_neg h1, if_pos h2]
        have h3 : (2 * a + 1 + 1) / 2 = (2 * a + 1) / 2 + 1 := by omega
        rw [h3]
        exact (hmid (2 * a + 1)).2.1
    · simp only [dy]; split_ifs
      · exact hsub _
      · exact (hmid m).2.1.trans (hsub _)
    · simp only [dy]
      have hge : 2 ^ k ≤ m / 2 := by rw [pow_succ] at hm2; omega
      split_ifs
      · exact htop _ hge
      · have e1 := htop _ hge
        have e2 := htop (m / 2 + 1) (by omega)
        exact Set.Subset.antisymm ((hmid m).2.1.trans e2.subset) (e1.symm.subset.trans (hmid m).1)
    · simp only [dy]
      have hpk : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      split_ifs with he
      · have hle : m / 2 ≤ 2 ^ k := by rw [pow_succ] at hm2; omega
        rw [hmeas _ hle]
        have : ((m / 2 : ℕ) : ℝ) = (m : ℝ) / 2 := by
          rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero he) (by norm_num)]; norm_num
        rw [this, hpk]; field_simp
      · have hle : m / 2 + 1 ≤ 2 ^ k := by rw [pow_succ] at hm2; omega
        rw [(hmid m).2.2.2, hmeas _ (by omega), hmeas _ hle]
        have hodd : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
          have : m = 2 * (m / 2) + 1 := by omega
          exact_mod_cast this
        rw [hodd, hpk]; push_cast; field_simp; ring

lemma dy_mono_m (E : Set Ω) (hE : MeasurableSet E) (k : ℕ) {m m' : ℕ} (h : m ≤ m') :
    dy P hP E k m ⊆ dy P hP E k m' := by
  have := (dy_props P hP E hE k).2.1
  exact (monotone_nat_of_le_succ this) h

lemma dy_refine (E : Set Ω) (k l m : ℕ) : dy P hP E (k + l) (m * 2 ^ l) = dy P hP E k m := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← Nat.add_assoc]
    simp only [dy]
    have h1 : m * 2 ^ (l + 1) % 2 = 0 := by rw [pow_succ]; simp [← mul_assoc]
    rw [if_pos h1]
    have h2 : m * 2 ^ (l + 1) / 2 = m * 2 ^ l := by
      rw [pow_succ, ← mul_assoc]; simp
    rw [h2, ih]

lemma dy_cross (E : Set Ω) (hE : MeasurableSet E) {k k' m m' : ℕ}
    (h : (m : ℝ) / 2 ^ k ≤ (m' : ℝ) / 2 ^ k') : dy P hP E k m ⊆ dy P hP E k' m' := by
  have e1 := dy_refine P hP E k k' m
  have e2 := dy_refine P hP E k' k m'
  rw [Nat.add_comm k' k] at e2
  rw [← e1, ← e2]
  apply dy_mono_m P hP E hE
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  have : ((m * 2 ^ k' : ℕ) : ℝ) ≤ ((m' * 2 ^ k : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

include hP in
/-- A uniform random variable on a measurable set. -/
theorem exists_uniform_on (E : Set Ω) (hE : MeasurableSet E) :
    ∃ U : Ω → ℝ, Measurable U ∧ (∀ ω, 0 ≤ U ω ∧ U ω ≤ 1) ∧
      ∀ t, 0 ≤ t → t ≤ 1 → P.real (E ∩ U ⁻¹' Set.Iic t) = t * P.real E := by
  classical
  let S : Ω → Set ℝ := fun ω => {r | ∃ k m, ω ∈ dy P hP E k m ∧ r = (m : ℝ) / 2 ^ k}
  let U : Ω → ℝ := fun ω => if ω ∈ E then sInf (S ω) else 0
  have hSbdd : ∀ ω, BddBelow (S ω) := fun ω => ⟨0, fun r ⟨k, m, _, hr⟩ => hr ▸ by positivity⟩
  have hSne : ∀ ω ∈ E, (S ω).Nonempty := by
    intro ω hω
    refine ⟨1, 0, 1, ?_, by simp⟩
    simp only [dy]; simpa using hω
  have hU1 : ∀ ω ∈ E, U ω ≤ 1 := by
    intro ω hω
    simp only [U, if_pos hω]
    exact csInf_le (hSbdd ω) ⟨0, 1, by simp only [dy]; simpa using hω, by simp⟩
  have hU0 : ∀ ω, 0 ≤ U ω := by
    intro ω
    simp only [U]; split_ifs with hω
    · exact le_csInf (hSne ω hω) fun r ⟨k, m, _, hr⟩ => hr ▸ by positivity
    · exact le_rfl
  have hlt : ∀ ω ∈ E, ∀ r, U ω < r ↔ ∃ k m, ω ∈ dy P hP E k m ∧ (m : ℝ) / 2 ^ k < r := by
    intro ω hω r
    simp only [U, if_pos hω]
    constructor
    · intro h
      obtain ⟨_, ⟨k, m, hkm, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hSne ω hω) h
      exact ⟨k, m, hkm, hlt⟩
    · rintro ⟨k, m, hkm, hlt⟩
      exact lt_of_le_of_lt (csInf_le (hSbdd ω) ⟨k, m, hkm, rfl⟩) hlt
  have hmeasU : Measurable U := by
    apply measurable_of_Iio
    intro r
    have : U ⁻¹' Set.Iio r = (⋃ k : ℕ, ⋃ m : ℕ, if (m : ℝ) / 2 ^ k < r then dy P hP E k m else ∅) ∪
        (Eᶜ ∩ {_ω | 0 < r}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      by_cases hω : ω ∈ E
      · rw [hlt ω hω]
        constructor
        · rintro ⟨k, m, h1, h2⟩; left; exact ⟨k, m, by rw [if_pos h2]; exact h1⟩
        · rintro (⟨k, m, h⟩ | ⟨h, _⟩)
          · split_ifs at h with h2
            · exact ⟨k, m, h, h2⟩
            · exact absurd h (Set.notMem_empty _)
          · exact absurd hω h
      · have hU : U ω = 0 := by simp [U, hω]
        rw [hU]
        constructor
        · intro h; right; exact ⟨hω, h⟩
        · rintro (⟨k, m, h⟩ | ⟨_, h⟩)
          · split_ifs at h
            · exact absurd ((dy_props P hP E hE k).2.2.1 m h) hω
            · exact absurd h (Set.notMem_empty _)
          · exact h
    rw [this]
    refine MeasurableSet.union (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun m => ?_)
      (hE.compl.inter (MeasurableSet.const _))
    split_ifs
    · exact (dy_props P hP E hE k).1 m
    · exact MeasurableSet.empty
  refine ⟨U, hmeasU, fun ω => ⟨hU0 ω, ?_⟩, ?_⟩
  · by_cases hω : ω ∈ E
    · exact hU1 ω hω
    · simp [U, hω]
  intro t ht0 ht1
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · have : E ∩ U ⁻¹' Set.Iic 1 = E := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, and_iff_left_iff_imp]
      exact hU1 ω
    rw [this, one_mul]
  -- bounds at every level
  have hlow : ∀ k : ℕ, (⌊t * 2 ^ k⌋₊ : ℝ) / 2 ^ k * P.real E ≤ P.real (E ∩ U ⁻¹' Set.Iic t) := by
    intro k
    have hle : ⌊t * 2 ^ k⌋₊ ≤ 2 ^ k := by
      have := Nat.floor_le (show 0 ≤ t * 2 ^ k by positivity)
      have h2 : t * 2 ^ k ≤ 2 ^ k := by nlinarith [pow_pos (two_pos (α := ℝ)) k]
      exact_mod_cast this.trans h2
    rw [← (dy_props P hP E hE k).2.2.2.2 _ hle]
    refine measureReal_mono ?_
    intro ω hω
    have hωE := (dy_props P hP E hE k).2.2.1 _ hω
    refine ⟨hωE, ?_⟩
    simp only [Set.mem_preimage, Set.mem_Iic, U, if_pos hωE]
    refine le_trans (csInf_le (hSbdd ω) ⟨k, _, hω, rfl⟩) ?_
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hup : ∀ k : ℕ, P.real (E ∩ U ⁻¹' Set.Iic t) ≤
      ((⌊t * 2 ^ k⌋₊ + 1 : ℕ) : ℝ) / 2 ^ k * P.real E := by
    intro k
    have hlt1 : t * 2 ^ k < (⌊t * 2 ^ k⌋₊ + 1 : ℕ) := by push_cast; exact Nat.lt_floor_add_one _
    have hle : ⌊t * 2 ^ k⌋₊ + 1 ≤ 2 ^ k := by
      have h2 : t * 2 ^ k < 2 ^ k := by nlinarith [pow_pos (two_pos (α := ℝ)) k]
      have := Nat.floor_lt (show 0 ≤ t * 2 ^ k by positivity) |>.mpr (by exact_mod_cast h2)
      omega
    rw [← (dy_props P hP E hE k).2.2.2.2 _ hle]
    refine measureReal_mono ?_
    rintro ω ⟨hωE, hωU⟩
    simp only [Set.mem_preimage, Set.mem_Iic] at hωU
    have : U ω < ((⌊t * 2 ^ k⌋₊ + 1 : ℕ) : ℝ) / 2 ^ k := by
      rw [lt_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hωU (show (0:ℝ) ≤ 2 ^ k by positivity)
      linarith
    obtain ⟨k', m', h1, h2⟩ := (hlt ω hωE _).mp this
    exact dy_cross P hP E hE h2.le h1
  have hPE : 0 ≤ P.real E := measureReal_nonneg
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h1 := hup k
    have h2 : ((⌊t * 2 ^ k⌋₊ + 1 : ℕ) : ℝ) / 2 ^ k ≤ t + (1 / 2) ^ k := by
      push_cast
      rw [div_le_iff₀ (by positivity), add_mul, one_div_pow, one_div,
        inv_mul_cancel₀ (show (2:ℝ) ^ k ≠ 0 by positivity)]
      linarith [Nat.floor_le (show 0 ≤ t * 2 ^ k by positivity)]
    have hPE1 : P.real E ≤ 1 := measureReal_le_one
    have h3 := mul_le_mul_of_nonneg_right h2 hPE
    nlinarith [pow_pos (show (0:ℝ) < 1 / 2 by norm_num) k]
  · apply le_of_forall_pos_lt_add
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h1 := hlow k
    have h2 : t - (1 / 2) ^ k ≤ (⌊t * 2 ^ k⌋₊ : ℝ) / 2 ^ k := by
      rw [le_div_iff₀ (by positivity), sub_mul, one_div_pow, one_div,
        inv_mul_cancel₀ (show (2:ℝ) ^ k ≠ 0 by positivity)]
      linarith [Nat.lt_floor_add_one (t * 2 ^ k)]
    have hPE1 : P.real E ≤ 1 := measureReal_le_one
    have h3 := mul_le_mul_of_nonneg_right h2 hPE
    nlinarith [pow_pos (show (0:ℝ) < 1 / 2 by norm_num) k]

end Dyadic

end TCLI

open MeasureTheory

namespace TCLI

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the (clamped) quantile set. -/
def qset (K : ℝ → ℝ) (p M u : ℝ) : Set ℝ := {v | -M - 1 ≤ v ∧ (M ≤ v ∨ u * p ≤ K v)}

lemma qset_ne (K : ℝ → ℝ) (p M u : ℝ) (hM : 0 ≤ M) : (qset K p M u).Nonempty :=
  ⟨M, by constructor <;> [linarith; exact Or.inl le_rfl]⟩

lemma qset_bdd (K : ℝ → ℝ) (p M u : ℝ) : BddBelow (qset K p M u) := ⟨-M - 1, fun _ h => h.1⟩

lemma qinf_mono (K : ℝ → ℝ) (p M : ℝ) (hp : 0 ≤ p) (hM : 0 ≤ M) :
    Monotone (fun u => sInf (qset K p M u)) := by
  intro a b hab
  apply csInf_le_csInf (qset_bdd K p M a) (qset_ne K p M b hM)
  rintro v ⟨h1, h2 | h2⟩
  · exact ⟨h1, Or.inl h2⟩
  · exact ⟨h1, Or.inr (le_trans (mul_le_mul_of_nonneg_right hab hp) h2)⟩

lemma quantile_galois (K : ℝ → ℝ) (p M : ℝ) (hp : 0 < p) (hM : 0 ≤ M) (hmono : Monotone K)
    (hright : ∀ w c, (∀ w', w < w' → c ≤ K w') → c ≤ K w) (hlow : ∀ w, w < -M → K w = 0)
    (hhigh : K M = p) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (w : ℝ) :
    sInf (qset K p M u) ≤ w ↔ u * p ≤ K w := by
  have hup : 0 < u * p := mul_pos hu0 hp
  constructor
  · intro h
    have hG : u * p ≤ K (sInf (qset K p M u)) := by
      apply hright
      intro w' hw'
      obtain ⟨v, ⟨_, hv | hv⟩, hvw⟩ := exists_lt_of_csInf_lt (qset_ne K p M u hM) hw'
      · have : K M ≤ K v := hmono hv
        have : u * p ≤ p := by nlinarith
        exact le_trans (by linarith) (hmono hvw.le)
      · exact le_trans hv (hmono hvw.le)
    exact le_trans hG (hmono h)
  · intro h
    apply csInf_le (qset_bdd K p M u)
    refine ⟨?_, Or.inr h⟩
    by_contra hlt; push Not at hlt
    rw [hlow w (by linarith)] at h
    linarith

lemma subcdf_right (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    (V : Ω → ℝ) (hV : Measurable V) :
    ∀ w c, (∀ w', w < w' → c ≤ P.real (A ∩ V ⁻¹' Set.Iic w')) → c ≤ P.real (A ∩ V ⁻¹' Set.Iic w) := by
  intro w c h
  let s : ℕ → Set Ω := fun n => A ∩ V ⁻¹' Set.Iic (w + 1 / ((n : ℝ) + 1))
  have hs : ∀ n, NullMeasurableSet (s n) P :=
    fun n => (hA.inter (hV measurableSet_Iic)).nullMeasurableSet
  have hanti : Antitone s := by
    intro n m hnm ω ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simp only [Set.mem_preimage, Set.mem_Iic] at h2 ⊢
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hnm 1
    linarith
  have hinter : (⋂ n, s n) = A ∩ V ⁻¹' Set.Iic w := by
    ext ω
    simp only [s, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro h
      refine ⟨(h 0).1, ?_⟩
      by_contra hlt; push Not at hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < V ω - w by linarith)
      have := (h n).2
      linarith
    · rintro ⟨h1, h2⟩ n
      exact ⟨h1, by have : 0 < 1 / ((n : ℝ) + 1) := by positivity
                    linarith⟩
  have ht := tendsto_measure_iInter_atTop hs hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp ht
  apply ge_of_tendsto ht'
  filter_upwards with n
  have : 0 < 1 / ((n : ℝ) + 1) := by positivity
  exact h _ (by linarith)

/-- Transfer of a bounded real random variable along equally distributed integer labels. -/
theorem transfer_real (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (NX NY : Ω → ℤ) (hNX : Measurable NX)
    (hNY : Measurable NY) (hlaw : ∀ z, P.real (NX ⁻¹' {z}) = P.real (NY ⁻¹' {z}))
    (V : Ω → ℝ) (hV : Measurable V) (M : ℝ) (hVb : ∀ ω, |V ω| ≤ M) :
    ∃ W : Ω → ℝ, Measurable W ∧
      P.map (fun ω => (NY ω, W ω)) = P.map (fun ω => (NX ω, V ω)) := by
  classical
  have hE : ∀ z, MeasurableSet (NY ⁻¹' {z}) := fun z => hNY (measurableSet_singleton z)
  have hA : ∀ z, MeasurableSet (NX ⁻¹' {z}) := fun z => hNX (measurableSet_singleton z)
  choose U hUm hU01 hUlaw using fun z => exists_uniform_on P hP (NY ⁻¹' {z}) (hE z)
  set M' := max M 0 with hM'
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hVb' : ∀ ω, |V ω| ≤ M' := fun ω => le_trans (hVb ω) (le_max_left _ _)
  let K : ℤ → ℝ → ℝ := fun z w => P.real (NX ⁻¹' {z} ∩ V ⁻¹' Set.Iic w)
  let p : ℤ → ℝ := fun z => P.real (NX ⁻¹' {z})
  let G : ℤ → ℝ → ℝ := fun z u => sInf (qset (K z) (p z) M' u)
  let W : Ω → ℝ := fun ω => G (NY ω) (U (NY ω) ω)
  have hp0 : ∀ z, 0 ≤ p z := fun z => measureReal_nonneg
  have hGm : ∀ z, Measurable (fun ω => G z (U z ω)) := fun z =>
    (qinf_mono (K z) (p z) M' (hp0 z) hM0).measurable.comp (hUm z)
  have hWpre : ∀ S : Set ℝ, W ⁻¹' S = ⋃ z, NY ⁻¹' {z} ∩ (fun ω => G z (U z ω)) ⁻¹' S := by
    intro S; ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff, W]
    constructor
    · intro h; exact ⟨NY ω, rfl, h⟩
    · rintro ⟨z, rfl, h⟩; exact h
  have hWm : Measurable W := by
    intro S hS
    rw [hWpre]
    exact MeasurableSet.iUnion fun z => (hE z).inter (hGm z hS)
  have hKmono : ∀ z, Monotone (K z) := by
    intro z a b hab
    exact measureReal_mono (Set.inter_subset_inter_right _ (fun ω (h : V ω ≤ a) => le_trans h hab))
  have hKle : ∀ z w, K z w ≤ p z := fun z w => measureReal_mono Set.inter_subset_left
  have hKlow : ∀ z w, w < -M' → K z w = 0 := by
    intro z w hw
    have : NX ⁻¹' {z} ∩ V ⁻¹' Set.Iic w = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and, not_le]
      intro _
      have := neg_abs_le (V ω); have := hVb' ω; linarith
    simp only [K, this, measureReal_empty]
  have hKhigh : ∀ z, K z M' = p z := by
    intro z
    have : NX ⁻¹' {z} ∩ V ⁻¹' Set.Iic M' = NX ⁻¹' {z} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, and_iff_left_iff_imp]
      intro _; exact le_trans (le_abs_self _) (hVb' ω)
    simp only [K, p, this]
  have hkey : ∀ z w, P.real (NY ⁻¹' {z} ∩ W ⁻¹' Set.Iic w) = K z w := by
    intro z w
    by_cases hpz : p z = 0
    · have h1 : K z w = 0 := le_antisymm (hpz ▸ hKle z w) (measureReal_nonneg)
      have h2 : P.real (NY ⁻¹' {z}) = 0 := by rw [← hlaw z]; exact hpz
      rw [h1]
      exact le_antisymm (h2 ▸ measureReal_mono Set.inter_subset_left) measureReal_nonneg
    have hpz' : 0 < p z := lt_of_le_of_ne (hp0 z) (Ne.symm hpz)
    set t := K z w / p z with ht
    have ht0 : 0 ≤ t := div_nonneg measureReal_nonneg (hp0 z)
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hpz']; exact hKle z w
    have hpos : MeasurableSet {ω | 0 < U z ω} := measurableSet_lt measurable_const (hUm z)
    have hnull : P.real (NY ⁻¹' {z} ∩ U z ⁻¹' Set.Iic 0) = 0 := by
      rw [hUlaw z 0 le_rfl zero_le_one, zero_mul]
    have hsplit : ∀ S : Set Ω, MeasurableSet S →
        P.real (NY ⁻¹' {z} ∩ S) = P.real (NY ⁻¹' {z} ∩ S ∩ {ω | 0 < U z ω}) := by
      intro S hS
      have h1 := measureReal_inter_add_diff (μ := P) (s := NY ⁻¹' {z} ∩ S) hpos
      have h2 : P.real ((NY ⁻¹' {z} ∩ S) \ {ω | 0 < U z ω}) = 0 := by
        apply le_antisymm _ measureReal_nonneg
        refine le_trans (measureReal_mono ?_) hnull.le
        rintro ω ⟨⟨h1, _⟩, h2⟩
        refine ⟨h1, ?_⟩
        simp only [Set.mem_setOf_eq, not_lt] at h2
        exact h2
      linarith
    have hEq : NY ⁻¹' {z} ∩ W ⁻¹' Set.Iic w ∩ {ω | 0 < U z ω} =
        NY ⁻¹' {z} ∩ U z ⁻¹' Set.Iic t ∩ {ω | 0 < U z ω} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Iic,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        have h2' : G z (U z ω) ≤ w := by simp only [W, h1] at h2; exact h2
        have := (quantile_galois (K z) (p z) M' hpz' hM0 (hKmono z)
          (subcdf_right P _ (hA z) V hV) (hKlow z) (hKhigh z) h3 (hU01 z ω).2 w).mp h2'
        rw [ht, le_div_iff₀ hpz']; exact this
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        show G (NY ω) (U (NY ω) ω) ≤ w
        rw [h1]
        apply (quantile_galois (K z) (p z) M' hpz' hM0 (hKmono z)
          (subcdf_right P _ (hA z) V hV) (hKlow z) (hKhigh z) h3 (hU01 z ω).2 w).mpr
        rw [ht, le_div_iff₀ hpz'] at h2; exact h2
    rw [hsplit _ (hWm measurableSet_Iic), hEq, ← hsplit _ ((hUm z) measurableSet_Iic),
      hUlaw z t ht0 ht1, ← hlaw z]
    show K z w / p z * p z = K z w
    field_simp
  -- equality of laws on each label
  have hslice : ∀ z (T : Set ℝ), MeasurableSet T →
      P (NY ⁻¹' {z} ∩ W ⁻¹' T) = P (NX ⁻¹' {z} ∩ V ⁻¹' T) := by
    intro z T hT
    have hmeq : (P.restrict (NY ⁻¹' {z})).map W = (P.restrict (NX ⁻¹' {z})).map V := by
      apply Measure.ext_of_Iic
      intro a
      rw [Measure.map_apply hWm measurableSet_Iic, Measure.map_apply hV measurableSet_Iic,
        Measure.restrict_apply (hWm measurableSet_Iic), Measure.restrict_apply (hV measurableSet_Iic),
        Set.inter_comm, Set.inter_comm (V ⁻¹' _)]
      have : P.real (NY ⁻¹' {z} ∩ W ⁻¹' Set.Iic a) = P.real (NX ⁻¹' {z} ∩ V ⁻¹' Set.Iic a) :=
        hkey z a
      rw [measureReal_def, measureReal_def] at this
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp this
    have := congrArg (fun μ => μ T) hmeq
    rw [Measure.map_apply hWm hT, Measure.map_apply hV hT, Measure.restrict_apply (hWm hT),
      Measure.restrict_apply (hV hT)] at this
    rw [Set.inter_comm, this, Set.inter_comm]
  refine ⟨W, hWm, ?_⟩
  ext S hS
  rw [Measure.map_apply (hNY.prodMk hWm) hS, Measure.map_apply (hNX.prodMk hV) hS]
  have hdec : ∀ (N : Ω → ℤ) (F : Ω → ℝ), (fun ω => (N ω, F ω)) ⁻¹' S =
      ⋃ z, N ⁻¹' {z} ∩ F ⁻¹' (Prod.mk z ⁻¹' S) := by
    intro N F; ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨N ω, rfl, h⟩
    · rintro ⟨z, rfl, h⟩; exact h
  have hdisj : ∀ (N : Ω → ℤ) (F : Ω → ℝ),
      Pairwise (Function.onFun Disjoint fun z => N ⁻¹' {z} ∩ F ⁻¹' (Prod.mk z ⁻¹' S)) := by
    intro N F a b hab
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact hab (h1.symm.trans h2)
  rw [hdec NY W, hdec NX V, measure_iUnion (hdisj NY W)
      (fun z => (hE z).inter (hWm (measurable_prodMk_left hS))),
    measure_iUnion (hdisj NX V) (fun z => (hA z).inter (hV (measurable_prodMk_left hS)))]
  congr 1
  funext z
  exact hslice z _ (measurable_prodMk_left hS)


theorem transfer_vec (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (NX NY : Ω → ℤ) (hNX : Measurable NX)
    (hNY : Measurable NY) (hlaw : ∀ z, P.real (NX ⁻¹' {z}) = P.real (NY ⁻¹' {z}))
    {n : ℕ} (V : Ω → (Fin n → ℝ)) (hV : Measurable V) :
    ∃ W : Ω → (Fin n → ℝ), Measurable W ∧
      P.map (fun ω => (NY ω, W ω)) = P.map (fun ω => (NX ω, V ω)) := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real (α := Fin n → ℝ)
  let f : (Fin n → ℝ) → ℝ := fun v => Real.arctan (e v)
  have hfm : Measurable f := Real.measurable_arctan.comp he.measurable
  have hf : MeasurableEmbedding f :=
    hfm.measurableEmbedding (Real.arctan_injective.comp he.injective)
  obtain ⟨g, hgm, hgf⟩ := hf.exists_measurable_extend measurable_id (fun _ => ⟨0⟩)
  obtain ⟨W', hW'm, hW'⟩ := transfer_real P hP NX NY hNX hNY hlaw (fun ω => f (V ω))
    (hfm.comp hV) 2 (fun ω => by
      rw [abs_le]
      have h1 := Real.arctan_lt_pi_div_two (e (V ω))
      have h2 := Real.neg_pi_div_two_lt_arctan (e (V ω))
      have h3 := Real.pi_lt_four
      constructor <;> simp only [f] <;> linarith)
  refine ⟨fun ω => g (W' ω), hgm.comp hW'm, ?_⟩
  have hmap : Measurable (Prod.map (id : ℤ → ℤ) g) := measurable_id.prodMap hgm
  have e1 : (fun ω => (NY ω, g (W' ω))) = Prod.map id g ∘ (fun ω => (NY ω, W' ω)) := rfl
  have e2 : (fun ω => (NX ω, V ω)) = Prod.map id g ∘ (fun ω => (NX ω, f (V ω))) := by
    funext ω
    simp only [Function.comp, Prod.map, id]
    rw [show g (f (V ω)) = V ω from congrFun hgf (V ω)]
  have hm2 : Measurable (fun ω => (NX ω, f (V ω))) := hNX.prodMk (hfm.comp hV)
  rw [e1, e2, ← Measure.map_map hmap (hNY.prodMk hW'm), ← Measure.map_map hmap hm2, hW']

end TCLI

open MeasureTheory Filter Topology

namespace TCLI

open TailRiskSharing.VaRConv TailRiskSharing.TailConv

variable {Ω : Type*} [MeasurableSpace Ω]

lemma law_transport {β : Type*} [MeasurableSpace β] (P : Measure Ω) [IsProbabilityMeasure P]
    (G1 G2 : Ω → β) (h1 : Measurable G1) (h2 : Measurable G2) (hlaw : P.map G1 = P.map G2)
    (φ : β → ℝ) (hφ : Measurable φ) :
    (∀ x, distFn P (fun ω => φ (G1 ω)) x = distFn P (fun ω => φ (G2 ω)) x) ∧
      ((fun ω => φ (G2 ω)) ∈ Linf P → (fun ω => φ (G1 ω)) ∈ Linf P) := by
  constructor
  · intro x
    unfold distFn
    show P.real (G1 ⁻¹' (φ ⁻¹' Set.Iic x)) = P.real (G2 ⁻¹' (φ ⁻¹' Set.Iic x))
    rw [← map_measureReal_apply h1 (hφ measurableSet_Iic),
      ← map_measureReal_apply h2 (hφ measurableSet_Iic), hlaw]
  · rintro ⟨_, C, hC⟩
    refine ⟨hφ.comp h1, C, ?_⟩
    have hS : MeasurableSet {y | |φ y| ≤ C} :=
      measurableSet_le (continuous_abs.measurable.comp hφ) measurable_const
    have := (ae_map_iff h2.aemeasurable hS).mpr hC
    rw [← hlaw] at this
    exact (ae_map_iff h1.aemeasurable hS).mp this

lemma add_mem_Linf (P : Measure Ω) {X Y : Ω → ℝ} (hX : X ∈ Linf P) (hY : Y ∈ Linf P) :
    (fun ω => X ω + Y ω) ∈ Linf P := by
  obtain ⟨hXm, C, hC⟩ := hX
  obtain ⟨hYm, D, hD⟩ := hY
  refine ⟨hXm.add hYm, C + D, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  exact le_trans (abs_add_le _ _) (by linarith)

lemma sub_mem_Linf (P : Measure Ω) {X Y : Ω → ℝ} (hX : X ∈ Linf P) (hY : Y ∈ Linf P) :
    (fun ω => X ω - Y ω) ∈ Linf P := by
  obtain ⟨hXm, C, hC⟩ := hX
  obtain ⟨hYm, D, hD⟩ := hY
  refine ⟨hXm.sub hYm, C + D, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  exact le_trans (abs_sub _ _) (by linarith)

lemma disc (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ Linf P) (c : ℝ)
    (hc : 0 < c) :
    Measurable (fun ω => ⌈c * X ω⌉) ∧ (fun ω => ((⌈c * X ω⌉ : ℤ) : ℝ) / c) ∈ Linf P ∧
      (∀ ω, X ω ≤ ((⌈c * X ω⌉ : ℤ) : ℝ) / c ∧ ((⌈c * X ω⌉ : ℤ) : ℝ) / c ≤ X ω + 1 / c) ∧
      ∀ z : ℤ, P.real ((fun ω => ⌈c * X ω⌉) ⁻¹' {z}) =
        distFn P X (z / c) - distFn P X ((z - 1) / c) := by
  obtain ⟨hXm, C, hC⟩ := hX
  have hNm : Measurable (fun ω => ⌈c * X ω⌉) := (measurable_const.mul hXm).ceil
  have hbd : ∀ ω, X ω ≤ ((⌈c * X ω⌉ : ℤ) : ℝ) / c ∧ ((⌈c * X ω⌉ : ℤ) : ℝ) / c ≤ X ω + 1 / c := by
    intro ω
    constructor
    · rw [le_div_iff₀ hc, mul_comm]; exact Int.le_ceil _
    · rw [div_le_iff₀ hc, add_mul, one_div, inv_mul_cancel₀ hc.ne', mul_comm]
      exact (Int.ceil_lt_add_one _).le
  refine ⟨hNm, ⟨(measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hNm |>.div_const c,
    |C| + 1 / c, ?_⟩, hbd, ?_⟩
  · filter_upwards [hC] with ω hω
    rw [abs_le] at hω ⊢
    have := hbd ω
    have h1 : 0 < 1 / c := by positivity
    constructor <;> [skip; skip] <;> nlinarith [le_abs_self C, neg_abs_le C]
  · intro z
    have hset : (fun ω => ⌈c * X ω⌉) ⁻¹' {z} =
        {ω | X ω ≤ z / c} \ {ω | X ω ≤ (z - 1) / c} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq, not_le,
        Int.ceil_eq_iff]
      rw [le_div_iff₀ hc, div_lt_iff₀ hc, mul_comm (X ω)]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
    rw [hset, measureReal_sdiff _ (measurableSet_le hXm measurable_const)]
    · rfl
    · intro ω (h : X ω ≤ (z - 1) / c)
      show X ω ≤ z / c
      have : ((z : ℝ) - 1) / c ≤ z / c := by
        apply div_le_div_of_nonneg_right _ hc.le; linarith
      linarith

theorem lawInv (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hcont : IsSupNormContinuousFromAbove P (Linf P) (ρ j)) :
    IsLawInvariantE P (Linf P) (infConv (Linf P) ρ) := by
  classical
  have hLI : ∀ i, ∀ Z1 ∈ Linf P, ∀ Z2 ∈ Linf P,
      (∀ x, distFn P Z1 x = distFn P Z2 x) → ρ i Z1 = ρ i Z2 :=
    fun i Z1 h1 Z2 h2 h => htail i Z1 h1 Z2 h2 (fun x => by rw [h x])
  have hM := TailRiskSharing.TailConv.infConv_monotone P hP n hn ρ j hmono
  have key : ∀ X ∈ Linf P, ∀ Y ∈ Linf P, (∀ x, distFn P X x = distFn P Y x) →
      infConv (Linf P) ρ Y ≤ infConv (Linf P) ρ X := by
    intro X hX Y hY hXY
    conv_rhs => unfold infConv
    refine le_iInf₂ fun Xs hXs => ?_
    obtain ⟨hXsL, hXsum⟩ := hXs
    let Xseq : ℕ → Ω → ℝ := fun k ω =>
      Xs j ω + (((⌈((k : ℝ) + 1) * X ω⌉ : ℤ) : ℝ) / ((k : ℝ) + 1) - X ω)
    have hXseqL : ∀ k, Xseq k ∈ Linf P := fun k =>
      add_mem_Linf P (hXsL j) (sub_mem_Linf P (disc P X hX _ (by positivity)).2.1 hX)
    have hstep : ∀ k : ℕ, infConv (Linf P) ρ Y ≤
        (((∑ i, ρ i (Xs i)) - ρ j (Xs j) + ρ j (Xseq k) : ℝ) : EReal) := by
      intro k
      set c : ℝ := (k : ℝ) + 1 with hcdef
      have hc : 0 < c := by positivity
      obtain ⟨hNXm, hXkL, hXkb, hXkl⟩ := disc P X hX c hc
      obtain ⟨hNYm, hYkL, hYkb, hYkl⟩ := disc P Y hY c hc
      set NX : Ω → ℤ := fun ω => ⌈c * X ω⌉
      set NY : Ω → ℤ := fun ω => ⌈c * Y ω⌉
      have hlaw : ∀ z, P.real (NX ⁻¹' {z}) = P.real (NY ⁻¹' {z}) := by
        intro z; rw [hXkl z, hYkl z, hXY, hXY]
      let Vx : Ω → (Fin n → ℝ) := fun ω i => Xs i ω
      have hVx : Measurable Vx := measurable_pi_lambda _ (fun i => (hXsL i).1)
      obtain ⟨Wv, hWvm, hWlaw⟩ := transfer_vec P hP NX NY hNXm hNYm hlaw Vx hVx
      let φ : Fin n → ℤ × (Fin n → ℝ) → ℝ := fun i q =>
        if i = j then (q.1 : ℝ) / c - ∑ i' ∈ Finset.univ.erase j, q.2 i' else q.2 i
      have hφm : ∀ i, Measurable (φ i) := by
        intro i
        by_cases h : i = j
        · subst h
          simp only [φ, if_true]
          exact (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp measurable_fst).div_const
            c).sub (Finset.measurable_sum _ fun i' _ => (measurable_pi_apply i').comp measurable_snd)
        · simp only [φ, if_neg h]
          exact (measurable_pi_apply i).comp measurable_snd
      have hφsum : ∀ q : ℤ × (Fin n → ℝ), ∑ i, φ i q = (q.1 : ℝ) / c := by
        intro q
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have : ∑ i ∈ Finset.univ.erase j, φ i q = ∑ i ∈ Finset.univ.erase j, q.2 i :=
          Finset.sum_congr rfl (fun i hi => by simp only [φ, if_neg (Finset.ne_of_mem_erase hi)])
        rw [this]; simp only [φ, if_true]; ring
      have hGY : Measurable (fun ω => (NY ω, Wv ω)) := hNYm.prodMk hWvm
      have hGX : Measurable (fun ω => (NX ω, Vx ω)) := hNXm.prodMk hVx
      have htr := fun i => law_transport P _ _ hGY hGX hWlaw (φ i) (hφm i)
      -- the X-side allocation
      have hXi_ne : ∀ i, i ≠ j → (fun ω => φ i (NX ω, Vx ω)) = Xs i := by
        intro i h; funext ω; simp only [φ, if_neg h, Vx]
      have hXi_j : (fun ω => φ j (NX ω, Vx ω)) = Xseq k := by
        funext ω
        simp only [φ, if_true, Vx, Xseq]
        have := hXsum ω
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at this
        rw [← hcdef]
        show (NX ω : ℝ) / c - _ = _
        linarith
      have hXiL : ∀ i, (fun ω => φ i (NX ω, Vx ω)) ∈ Linf P := by
        intro i
        by_cases h : i = j
        · subst h; rw [hXi_j]; exact hXseqL k
        · rw [hXi_ne i h]; exact hXsL i
      let Wi : Fin n → Ω → ℝ := fun i ω => φ i (NY ω, Wv ω)
      have hWiL : ∀ i, Wi i ∈ Linf P := fun i => (htr i).2 (hXiL i)
      have hYk : (fun ω => ((NY ω : ℤ) : ℝ) / c) ∈ Linf P := hYkL
      have hWA : Wi ∈ Allocations (Linf P) n (fun ω => ((NY ω : ℤ) : ℝ) / c) :=
        ⟨hWiL, fun ω => hφsum (NY ω, Wv ω)⟩
      have h1 : infConv (Linf P) ρ Y ≤ infConv (Linf P) ρ (fun ω => ((NY ω : ℤ) : ℝ) / c) :=
        hM Y hY _ hYk (Filter.Eventually.of_forall fun ω => (hYkb ω).1)
      have h2 : infConv (Linf P) ρ (fun ω => ((NY ω : ℤ) : ℝ) / c) ≤
          ((∑ i, ρ i (Wi i) : ℝ) : EReal) := iInf₂_le Wi hWA
      have h3 : ∑ i, ρ i (Wi i) = ∑ i, ρ i (fun ω => φ i (NX ω, Vx ω)) :=
        Finset.sum_congr rfl fun i _ => hLI i _ (hWiL i) _ (hXiL i) ((htr i).1)
      have h4 : ∑ i, ρ i (fun ω => φ i (NX ω, Vx ω)) =
          (∑ i, ρ i (Xs i)) - ρ j (Xs j) + ρ j (Xseq k) := by
        have : ∑ i, (ρ i (fun ω => φ i (NX ω, Vx ω)) - ρ i (Xs i)) =
            ρ j (Xseq k) - ρ j (Xs j) := by
          rw [Finset.sum_eq_single j]
          · rw [hXi_j]
          · intro i _ h; rw [hXi_ne i h, sub_self]
          · intro h; exact absurd (Finset.mem_univ j) h
        rw [Finset.sum_sub_distrib] at this
        linarith
      rw [← h4, ← h3]
      exact h1.trans h2
    have hlim : Tendsto (fun k => ρ j (Xseq k)) atTop (𝓝 (ρ j (Xs j))) := by
      apply hcont Xseq (Xs j) hXseqL (hXsL j)
      · intro k
        refine Filter.Eventually.of_forall fun ω => ?_
        have := (disc P X hX ((k : ℝ) + 1) (by positivity)).2.2.1 ω
        simp only [Xseq]; linarith [this.1]
      · intro η hη
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
        filter_upwards [eventually_ge_atTop N] with k hk
        refine Filter.Eventually.of_forall fun ω => ?_
        have := (disc P X hX ((k : ℝ) + 1) (by positivity)).2.2.1 ω
        have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.add_le_add_right hk 1
        simp only [Xseq]
        rw [abs_le]
        constructor <;> linarith [this.1, this.2]
    have hT : Tendsto (fun k => (((∑ i, ρ i (Xs i)) - ρ j (Xs j) + ρ j (Xseq k) : ℝ) : EReal))
        atTop (𝓝 ((∑ i, ρ i (Xs i) : ℝ) : EReal)) := by
      have := (tendsto_const_nhds (x := (∑ i, ρ i (Xs i)) - ρ j (Xs j))).add hlim
      rw [sub_add_cancel] at this
      exact (continuous_coe_real_ereal.tendsto _).comp this
    exact ge_of_tendsto' hT hstep
  intro X hX Y hY hXY
  exact le_antisymm (key Y hY X hX (fun x => (hXY x).symm)) (key X hX Y hY hXY)

end TCLI

open TailRiskSharing.TailConv


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) (hn : 1 ≤ n)
    (ρ : Fin n → (Ω → ℝ) → ℝ) (εs : Fin n → ℝ) (hε : ∀ i, 0 < εs i ∧ εs i < 1)
    (htail : ∀ i, TailRiskSharing.VaRTail.IsTailRiskMeasure P (Linf P) (εs i) (ρ i))
    (j : Fin n) (hmono : TailRiskSharing.VaRTail.IsMonotone P (Linf P) (ρ j))
    (hcont : IsSupNormContinuousFromAbove P (Linf P) (ρ j)) :
    IsLawInvariantE P (Linf P) (TailRiskSharing.VaRConv.infConv (Linf P) ρ) :=
  TCLI.lawInv P hP n hn ρ εs hε htail j hmono hcont
