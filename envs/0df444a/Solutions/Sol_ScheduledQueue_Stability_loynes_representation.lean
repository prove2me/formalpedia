-- Prove2me | solution 1 for ScheduledQueue.Stability.loynes_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:30:04.402316+00:00
-- url     : https://prove2.me/submissions/54f50adb-0647-4a47-a4cc-ac8a05a0ba58

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQLoynesAux

/-- A countable grid of `[0,t]` (containing `0` and `t`, dense). -/
noncomputable def vq (t : ℝ) (q : ℚ) : ℝ := t * min (max (q : ℝ) 0) 1

theorem vq_mem {t : ℝ} (ht : 0 ≤ t) (q : ℚ) : vq t q ∈ Icc 0 t := by
  have h1 : 0 ≤ min (max (q : ℝ) 0) 1 := le_min (le_max_right _ _) zero_le_one
  have h2 : min (max (q : ℝ) 0) 1 ≤ 1 := min_le_right _ _
  simp only [vq, mem_Icc]
  exact ⟨mul_nonneg ht h1, by nlinarith [mul_le_mul_of_nonneg_left h2 ht]⟩

/-- Lemma A: for a nondecreasing count `C` finite at `t`, the supremum of `h C(s) - s` over
`[0,t]` equals the supremum over the countable grid. -/
theorem sup_eq_rat {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (C : ℝ → ℕ∞) (hmono : Monotone C)
    (hfin : C t ≠ ⊤) :
    ⨆ s : Icc 0 t, (h * ((C s).toNat : ℝ) - s) = ⨆ q : ℚ, (h * ((C (vq t q)).toNat : ℝ) - vq t q) := by
  have hle : ∀ s, s ≤ t → (C s).toNat ≤ (C t).toNat := fun s hs =>
    ENat.toNat_le_toNat (hmono hs) hfin
  have hbdd1 : BddAbove (range fun s : Icc 0 t => h * ((C s).toNat : ℝ) - s) := by
    refine ⟨h * (C t).toNat, ?_⟩
    rintro _ ⟨⟨s, hs0, hst⟩, rfl⟩
    have : ((C s).toNat : ℝ) ≤ (C t).toNat := by exact_mod_cast hle s hst
    simp only
    nlinarith
  have hbdd2 : BddAbove (range fun q : ℚ => h * ((C (vq t q)).toNat : ℝ) - vq t q) := by
    refine ⟨h * (C t).toNat, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hm := vq_mem ht q
    have : ((C (vq t q)).toNat : ℝ) ≤ (C t).toNat := by exact_mod_cast hle _ hm.2
    simp only
    nlinarith [hm.1]
  have : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨s, hs0, hst⟩
    -- approximate `s` from the right by grid points
    apply _root_.le_of_forall_pos_le_add
    intro ε hε
    rcases eq_or_lt_of_le hst with hst' | hst'
    · refine le_trans ?_ (le_add_of_nonneg_right hε.le)
      refine le_trans (le_of_eq ?_) (le_ciSup hbdd2 1)
      simp [vq, hst']
    · have ht0 : 0 < t := lt_of_le_of_lt hs0 hst'
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s / t < min ((s + ε) / t) 1 by
        apply lt_min
        · exact div_lt_div_of_pos_right (by linarith) ht0
        · rwa [div_lt_one ht0])
      have hq0 : (0 : ℝ) ≤ q := le_trans (div_nonneg hs0 ht0.le) hq1.le
      have hq1' : (q : ℝ) ≤ 1 := le_trans hq2.le (min_le_right _ _)
      have hv : vq t q = t * q := by
        simp only [vq, max_eq_left hq0, min_eq_left hq1']
      have hsv : s ≤ vq t q := by
        rw [hv]; rw [div_lt_iff₀ ht0] at hq1; linarith
      have hvs : vq t q ≤ s + ε := by
        rw [hv]
        have := lt_of_lt_of_le hq2 (min_le_left _ _)
        rw [lt_div_iff₀ ht0] at this; linarith
      have hC : ((C s).toNat : ℝ) ≤ (C (vq t q)).toNat := by
        exact_mod_cast ENat.toNat_le_toNat (hmono hsv) (ne_top_of_le_ne_top hfin (hmono (vq_mem ht q).2))
      have := le_ciSup hbdd2 q
      simp only at this ⊢
      nlinarith
  · apply ciSup_le
    intro q
    exact le_ciSup (f := fun s : Icc 0 t => h * ((C s).toNat : ℝ) - s) hbdd1 ⟨vq t q, vq_mem ht q⟩

/-- Lemma B: time reversal of the workload supremum for a finite point configuration with no
point at `0` or at `t`. -/
theorem workload_sup_eq {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (a : ℤ → ℝ)
    (hfin : {j | a j ∈ Icc 0 t}.Finite) (h0 : ∀ j, a j ≠ 0) (htt : ∀ j, a j ≠ t) :
    ⨆ s : Icc 0 t, (h * ((({j | a j ∈ Ioc 0 t}.ncard : ℕ) : ℝ) - ({j | a j ∈ Ioc 0 (s : ℝ)}.ncard : ℝ))
        - (t - s)) =
      ⨆ v : Icc 0 t, (h * (({j | t - a j ∈ Ioc 0 (v : ℝ)}.encard).toNat : ℝ) - v) := by
  set K : ℕ := {j | a j ∈ Icc 0 t}.ncard
  have hfinS : ∀ S : Set ℤ, S ⊆ {j | a j ∈ Icc 0 t} → S.Finite := fun S hS => hfin.subset hS
  have hD : ∀ s : ℝ, 0 ≤ s → s ≤ t → ((({j | a j ∈ Ioc 0 t}.ncard : ℕ) : ℝ) -
      ({j | a j ∈ Ioc 0 s}.ncard : ℝ)) = ({j | a j ∈ Ioc s t}.ncard : ℝ) := by
    intro s hs0 hst
    have hu : {j | a j ∈ Ioc 0 t} = {j | a j ∈ Ioc 0 s} ∪ {j | a j ∈ Ioc s t} := by
      ext j; simp only [mem_setOf_eq, mem_union, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; by_cases hj : a j ≤ s
        · left; exact ⟨h1, hj⟩
        · right; exact ⟨lt_of_not_ge hj, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2.trans hst⟩
        · exact ⟨lt_of_le_of_lt hs0 h1, h2⟩
    have hdisj : Disjoint {j | a j ∈ Ioc 0 s} {j | a j ∈ Ioc s t} := by
      rw [Set.disjoint_left]; intro j h1 h2
      simp only [mem_setOf_eq, mem_Ioc] at h1 h2; linarith [h1.2, h2.1]
    have hf1 : {j | a j ∈ Ioc 0 s}.Finite := hfinS _ (fun j (hj : a j ∈ Ioc 0 s) =>
      (⟨hj.1.le, hj.2.trans hst⟩ : a j ∈ Icc 0 t))
    have hf2 : {j | a j ∈ Ioc s t}.Finite := hfinS _ (fun j (hj : a j ∈ Ioc s t) =>
      (⟨le_trans hs0 hj.1.le, hj.2⟩ : a j ∈ Icc 0 t))
    rw [hu, Set.ncard_union_eq hdisj hf1 hf2]
    push_cast; ring
  have hE : ∀ v : ℝ, (({j | t - a j ∈ Ioc 0 v}.encard).toNat : ℝ) = ({j | a j ∈ Ico (t - v) t}.ncard : ℝ) := by
    intro v
    rw [← Set.ncard_def]
    congr 2
    ext j; simp only [mem_setOf_eq, mem_Ioc, mem_Ico]; constructor <;> intro hj <;> constructor <;> linarith [hj.1, hj.2]
  have hDle : ∀ s, 0 ≤ s → ({j | a j ∈ Ioc s t}.ncard : ℝ) ≤ K := by
    intro s hs
    have hsub : {j | a j ∈ Ioc s t} ⊆ {j | a j ∈ Icc 0 t} := fun j (hj : a j ∈ Ioc s t) =>
      (⟨le_trans hs hj.1.le, hj.2⟩ : a j ∈ Icc 0 t)
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have hEle : ∀ v, v ≤ t → ({j | a j ∈ Ico (t - v) t}.ncard : ℝ) ≤ K := by
    intro v hv
    have hsub : {j | a j ∈ Ico (t - v) t} ⊆ {j | a j ∈ Icc 0 t} := fun j (hj : a j ∈ Ico (t - v) t) =>
      (⟨by linarith [hj.1], hj.2.le⟩ : a j ∈ Icc 0 t)
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have hbddL : BddAbove (range fun s : Icc 0 t => h * ((({j | a j ∈ Ioc 0 t}.ncard : ℕ) : ℝ) -
      ({j | a j ∈ Ioc 0 (s : ℝ)}.ncard : ℝ)) - (t - s)) := by
    refine ⟨h * K, ?_⟩
    rintro _ ⟨⟨s, hs0, hst⟩, rfl⟩
    simp only
    rw [hD s hs0 hst]
    nlinarith [hDle s hs0]
  have hbddR : BddAbove (range fun v : Icc 0 t => h * (({j | t - a j ∈ Ioc 0 (v : ℝ)}.encard).toNat : ℝ) - v) := by
    refine ⟨h * K, ?_⟩
    rintro _ ⟨⟨v, hv0, hvt⟩, rfl⟩
    simp only
    rw [hE v]
    nlinarith [hEle v hvt]
  have : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨s, hs0, hst⟩
    refine le_trans ?_ (le_ciSup hbddR ⟨t - s, by linarith, by linarith⟩)
    simp only
    rw [hD s hs0 hst, hE]
    have hsub : {j | a j ∈ Ioc s t} ⊆ {j | a j ∈ Ico (t - (t - s)) t} := by
      intro j hj
      simp only [mem_setOf_eq, mem_Ioc, mem_Ico] at hj ⊢
      exact ⟨by linarith [hj.1], lt_of_le_of_ne hj.2 (htt j)⟩
    have hf : {j | a j ∈ Ico (t - (t - s)) t}.Finite := hfinS _ (fun j (hj : a j ∈ Ico (t - (t - s)) t) =>
      (⟨by linarith [hj.1], hj.2.le⟩ : a j ∈ Icc 0 t))
    have : ({j | a j ∈ Ioc s t}.ncard : ℝ) ≤ {j | a j ∈ Ico (t - (t - s)) t}.ncard := by
      exact_mod_cast Set.ncard_le_ncard hsub hf
    nlinarith
  · apply ciSup_le
    rintro ⟨v, hv0, hvt⟩
    simp only
    rw [hE]
    rcases eq_or_lt_of_le hvt with hvt' | hvt'
    · -- `v = t`: no point at `0`
      rw [hvt', sub_self]
      refine le_trans ?_ (le_ciSup hbddL ⟨0, le_rfl, ht⟩)
      simp only
      rw [hD 0 le_rfl ht]
      have hsub : {j | a j ∈ Ico 0 t} ⊆ {j | a j ∈ Ioc 0 t} := by
        intro j hj
        simp only [mem_setOf_eq, mem_Ioc, mem_Ico] at hj ⊢
        exact ⟨lt_of_le_of_ne hj.1 (h0 j).symm, hj.2.le⟩
      have hf : {j | a j ∈ Ioc 0 t}.Finite := hfinS _ (fun j (hj : a j ∈ Ioc 0 t) =>
        (⟨hj.1.le, hj.2⟩ : a j ∈ Icc 0 t))
      have : ({j | a j ∈ Ico 0 t}.ncard : ℝ) ≤ {j | a j ∈ Ioc 0 t}.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hf
      nlinarith
    · apply _root_.le_of_forall_pos_le_add
      intro ε hε
      set s' : ℝ := max 0 (t - v - ε)
      have hs'0 : 0 ≤ s' := le_max_left _ _
      have hs't : s' < t - v := max_lt (by linarith) (by linarith)
      have hs'v : t - v - ε ≤ s' := le_max_right _ _
      have hL := le_ciSup hbddL ⟨s', hs'0, by linarith⟩
      simp only at hL
      rw [hD s' hs'0 (by linarith)] at hL
      have hsub : {j | a j ∈ Ico (t - v) t} ⊆ {j | a j ∈ Ioc s' t} := by
        intro j hj
        simp only [mem_setOf_eq, mem_Ioc, mem_Ico] at hj ⊢
        exact ⟨by linarith [hj.1], hj.2.le⟩
      have hf : {j | a j ∈ Ioc s' t}.Finite := hfinS _ (fun j (hj : a j ∈ Ioc s' t) =>
        (⟨le_trans hs'0 hj.1.le, hj.2⟩ : a j ∈ Icc 0 t))
      have : ({j | a j ∈ Ico (t - v) t}.ncard : ℝ) ≤ {j | a j ∈ Ioc s' t}.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hf
      nlinarith

/-- Count of reversed points `j h + u h - x_j` in `(0, s]` for a configuration `p = (u, x)`. -/
noncomputable def cnt (h : ℝ) (p : ℝ × (ℤ → ℝ)) (s : ℝ) : ℕ∞ :=
  {j : ℤ | (j : ℝ) * h + p.1 * h - p.2 j ∈ Ioc 0 s}.encard

/-- The countable-supremum version of `M(t)` as a function of the configuration. -/
noncomputable def Fq (h t : ℝ) (p : ℝ × (ℤ → ℝ)) : ℝ :=
  ⨆ q : ℚ, (h * ((cnt h p (vq t q)).toNat : ℝ) - vq t q)

theorem toNat_eq_toReal (e : ℕ∞) : (e.toNat : ℝ) = (e : ℝ≥0∞).toReal := by
  induction e using ENat.recTopCoe <;> simp

theorem measurable_cnt (h s : ℝ) : Measurable fun p : ℝ × (ℤ → ℝ) => ((cnt h p s).toNat : ℝ) := by
  have e : (fun p : ℝ × (ℤ → ℝ) => ((cnt h p s).toNat : ℝ)) = fun p =>
      (∑' j : ℤ, {p : ℝ × (ℤ → ℝ) | (j : ℝ) * h + p.1 * h - p.2 j ∈ Ioc 0 s}.indicator
        (fun _ => (1 : ℝ≥0∞)) p).toReal := by
    funext p
    have hj : ∀ j : ℤ, {p : ℝ × (ℤ → ℝ) | (j : ℝ) * h + p.1 * h - p.2 j ∈ Ioc 0 s}.indicator
        (fun _ => (1 : ℝ≥0∞)) p =
        {j : ℤ | (j : ℝ) * h + p.1 * h - p.2 j ∈ Ioc 0 s}.indicator (fun _ => (1 : ℝ≥0∞)) j := by
      intro j; simp only [Set.indicator, mem_setOf_eq]
    simp_rw [hj]
    rw [← tsum_subtype _ (fun _ => (1 : ℝ≥0∞)), ENNReal.tsum_set_one, toNat_eq_toReal, cnt]
  rw [e]
  refine Measurable.ennreal_toReal (Measurable.ennreal_tsum fun j => ?_)
  refine measurable_const.indicator (measurableSet_preimage ?_ measurableSet_Ioc)
  fun_prop

theorem measurable_Fq (h t : ℝ) : Measurable (Fq h t) := by
  unfold Fq
  exact Measurable.iSup fun q => ((measurable_cnt h _).const_mul h).sub_const _

/-- The uniform law on `[0,1]` is invariant under `u ↦ frac(θ - u)`. -/
theorem uniform_invariant {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun u => if u ≤ θ then θ - u else θ - u + 1) =
      volume.restrict (Icc (0 : ℝ) 1) := by
  set φ : ℝ → ℝ := fun u => if u ≤ θ then θ - u else θ - u + 1
  have hφ : Measurable φ := Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
  ext A hA
  rw [Measure.map_apply hφ hA, Measure.restrict_apply (hφ hA), Measure.restrict_apply hA]
  have hset : φ ⁻¹' A ∩ Icc 0 1 = ((fun u => θ - u) ⁻¹' (A ∩ Icc 0 θ)) ∪
      ((fun u => (θ + 1) - u) ⁻¹' (A ∩ Ico θ 1)) := by
    ext u
    simp only [φ, mem_inter_iff, mem_preimage, mem_Icc, mem_Ico, mem_union]
    by_cases hu : u ≤ θ
    · simp only [hu, if_true]
      constructor
      · rintro ⟨h1, h2, h3⟩; left; exact ⟨h1, by linarith, by linarith⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨h1, by linarith, by linarith⟩
        · exfalso; linarith
    · simp only [hu, if_false]
      push Not at hu
      constructor
      · rintro ⟨h1, h2, h3⟩; right
        exact ⟨by rwa [show θ + 1 - u = θ - u + 1 by ring], by linarith, by linarith⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exfalso; linarith
        · exact ⟨by rwa [show θ - u + 1 = θ + 1 - u by ring], by linarith, by linarith⟩
  have hdisj : Disjoint ((fun u => θ - u) ⁻¹' (A ∩ Icc 0 θ))
      ((fun u => (θ + 1) - u) ⁻¹' (A ∩ Ico θ 1)) := by
    rw [Set.disjoint_left]
    intro u h1 h2
    simp only [mem_preimage, mem_inter_iff, mem_Icc, mem_Ico] at h1 h2
    linarith [h1.2.2, h2.2.2]
  have hm2 : MeasurableSet ((fun u => (θ + 1) - u) ⁻¹' (A ∩ Ico θ 1)) :=
    measurableSet_preimage (by fun_prop) (hA.inter measurableSet_Ico)
  rw [hset, measure_union hdisj hm2,
    (Measure.measurePreserving_sub_left volume θ).measure_preimage
      (hA.inter measurableSet_Icc).nullMeasurableSet,
    (Measure.measurePreserving_sub_left volume (θ + 1)).measure_preimage
      (hA.inter measurableSet_Ico).nullMeasurableSet]
  have hsplit : A ∩ Icc 0 1 = (A ∩ Ico 0 θ) ∪ (A ∩ Icc θ 1) := by
    ext u; simp only [mem_inter_iff, mem_Icc, mem_Ico, mem_union]
    constructor
    · rintro ⟨hu, h1, h2⟩
      by_cases h : u < θ
      · left; exact ⟨hu, h1, h⟩
      · right; exact ⟨hu, le_of_not_gt h, h2⟩
    · rintro (⟨hu, h1, h2⟩ | ⟨hu, h1, h2⟩)
      · exact ⟨hu, h1, by linarith⟩
      · exact ⟨hu, by linarith, h2⟩
  have hdisj2 : Disjoint (A ∩ Ico 0 θ) (A ∩ Icc θ 1) := by
    rw [Set.disjoint_left]; intro u h1 h2
    simp only [mem_inter_iff, mem_Icc, mem_Ico] at h1 h2; linarith [h1.2.2, h2.2.1]
  rw [hsplit, measure_union hdisj2 (hA.inter measurableSet_Icc)]
  have e1 : volume (A ∩ Icc 0 θ) = volume (A ∩ Ico 0 θ) :=
    measure_congr ((ae_eq_refl A).inter Ico_ae_eq_Icc.symm)
  have e2 : volume (A ∩ Ico θ 1) = volume (A ∩ Icc θ 1) :=
    measure_congr ((ae_eq_refl A).inter Ico_ae_eq_Icc)
  rw [e1, e2]

/-- The reflected-and-shifted configuration map. -/
noncomputable def Φ (θ : ℝ) (m : ℤ) (p : ℝ × (ℤ → ℝ)) : ℝ × (ℤ → ℝ) :=
  (if p.1 ≤ θ then θ - p.1 else θ - p.1 + 1,
    fun i => p.2 ((if p.1 ≤ θ then m else m - 1) - i))

theorem measurable_Φ (θ : ℝ) (m : ℤ) : Measurable (Φ θ m) := by
  unfold Φ
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.ite (measurableSet_le measurable_fst measurable_const) (by fun_prop) (by fun_prop)
  · refine measurable_pi_lambda _ fun i => ?_
    have e : (fun p : ℝ × (ℤ → ℝ) => p.2 ((if p.1 ≤ θ then m else m - 1) - i)) =
        fun p => if p.1 ≤ θ then p.2 (m - i) else p.2 (m - 1 - i) := by
      funext p; split_ifs <;> rfl
    rw [e]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const) (by fun_prop) (by fun_prop)

open ScheduledQueue.Stability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : ℝ} {ξ : ℤ → Ω → ℝ} {U : Ω → ℝ}

theorem reflect_invariant (hin : ScheduledInput P ξ U) (c : ℤ) :
    (P.map (fun ω i => ξ i ω)).map (fun x : ℤ → ℝ => fun i => x (c - i)) = P.map (fun ω i => ξ i ω) := by
  have hmeas : Measurable fun ω i => ξ i ω := measurable_pi_lambda _ hin.measurable
  rw [Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) hmeas]
  have hinj : Function.Injective (fun i : ℤ => c - i) := fun a b hab => by simpa using hab
  have hid := IdentDistrib.pi (X := fun i => ξ (c - i)) (Y := ξ)
    (fun i => (hin.identDistrib (c - i)).trans (hin.identDistrib i).symm)
    (hin.indep.precomp hinj) hin.indep
  exact hid.map_eq

theorem law_Φ (hin : ScheduledInput P ξ U) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (m : ℤ) :
    IdentDistrib (fun ω => Φ θ m (U ω, fun i => ξ i ω)) (fun ω => (U ω, fun i => ξ i ω)) P P := by
  have hΞ : Measurable fun ω i => ξ i ω := measurable_pi_lambda _ hin.measurable
  have hUae : AEMeasurable U P := hin.uniform.aemeasurable
  have hpair : AEMeasurable (fun ω => (U ω, fun i => ξ i ω)) P := hUae.prodMk hΞ.aemeasurable
  set μU : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  set ν : Measure (ℤ → ℝ) := P.map (fun ω i => ξ i ω)
  have hprod : P.map (fun ω => (U ω, fun i => ξ i ω)) = μU.prod ν := by
    rw [hin.indep_shift.map_prod_eq_prod_map_map hUae hΞ.aemeasurable, hin.uniform.map_eq]
  have hinv : (μU.prod ν).map (Φ θ m) = μU.prod ν := by
    symm
    apply Measure.prod_eq
    intro A B hA hB
    rw [Measure.map_apply (measurable_Φ θ m) (hA.prod hB),
      Measure.prod_apply (measurable_Φ θ m (hA.prod hB))]
    set φ : ℝ → ℝ := fun u => if u ≤ θ then θ - u else θ - u + 1
    have hφ : Measurable φ := Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
    have hsec : ∀ u : ℝ, ν (Prod.mk u ⁻¹' (Φ θ m ⁻¹' (A ×ˢ B))) =
        (φ ⁻¹' A).indicator (fun _ => ν B) u := by
      intro u
      by_cases hu : φ u ∈ A
      · rw [indicator_of_mem (show u ∈ φ ⁻¹' A from hu)]
        have e : Prod.mk u ⁻¹' (Φ θ m ⁻¹' (A ×ˢ B)) =
            (fun x : ℤ → ℝ => fun i => x ((if u ≤ θ then m else m - 1) - i)) ⁻¹' B := by
          ext x; simp only [mem_preimage, Φ, mem_prod]
          exact ⟨fun hx => hx.2, fun hx => ⟨hu, hx⟩⟩
        rw [e]
        have hR : Measurable (fun x : ℤ → ℝ => fun i => x ((if u ≤ θ then m else m - 1) - i)) :=
          measurable_pi_lambda _ fun i => measurable_pi_apply _
        rw [← Measure.map_apply hR hB, reflect_invariant hin]
      · rw [indicator_of_notMem (show u ∉ φ ⁻¹' A from hu)]
        have e : Prod.mk u ⁻¹' (Φ θ m ⁻¹' (A ×ˢ B)) = ∅ := by
          ext x; simp only [mem_preimage, Φ, mem_prod, mem_empty_iff_false, iff_false, not_and]
          intro hx; exact absurd hx hu
        rw [e, measure_empty]
    simp_rw [hsec]
    rw [lintegral_indicator_const (hφ hA), ← Measure.map_apply hφ hA, uniform_invariant hθ0 hθ1,
      mul_comm]
  refine ⟨(measurable_Φ θ m).comp_aemeasurable hpair, hpair, ?_⟩
  have := AEMeasurable.map_map_of_aemeasurable (measurable_Φ θ m).aemeasurable hpair
  rw [Function.comp_def] at this
  rw [← this, hprod, hinv]

theorem bc_eventually_lt (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn


/-- Almost surely every reversed count `#{j : R_j ∈ (0,s]}` is finite. -/
theorem revCount_finite (hh : 0 < h) (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, revCount h ξ U s ω ≠ ⊤ := by
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0 : ℝ) 1 := by
    rw [hin.uniform.ae_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc.mem]
    exact ae_restrict_mem measurableSet_Icc
  have h1 : ∀ K : ℕ, ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, ξ (m : ℤ) ω + K < m * h := by
    intro K
    apply bc_eventually_lt hh (W := fun ω => ξ 0 ω + K)
      (hin.integrable.add (integrable_const _))
    intro m
    exact (hin.identDistrib (m : ℤ)).comp (u := fun x : ℝ => x + (K : ℝ)) (by fun_prop)
  have h2 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (-(m : ℤ)) ω + h < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω + h)
      (hin.integrable.neg.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x => -x + h) (by fun_prop)
  rw [← ae_all_iff] at h1
  filter_upwards [h1, h2, hU] with ω h1 h2 hU
  intro s
  obtain ⟨K, hK⟩ := exists_nat_ge s
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 K)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  have hsub : {j : ℤ | revArrival h ξ U j ω ∈ Ioc 0 s} ⊆
      (Finset.Icc (-(N2 : ℤ)) N1 : Set ℤ) := by
    intro j ⟨hj1, hj2⟩
    simp only [revArrival] at hj1 hj2
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · by_contra hc
      have hm := hN2 (-j).toNat (by omega)
      have e : (-(((-j).toNat : ℕ) : ℤ)) = j := by omega
      have e2 : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by
        have : (((-j).toNat : ℕ) : ℤ) = -j := by omega
        exact_mod_cast this
      rw [e, e2] at hm
      nlinarith [hU.2]
    · by_contra hc
      have hm := hN1 j.toNat (by omega)
      have e : ((j.toNat : ℕ) : ℤ) = j := by omega
      have e2 : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast e
      rw [e, e2] at hm
      nlinarith [hU.1]
  exact ((Finset.finite_toSet _).subset hsub).encard_lt_top.ne


theorem uniform_mem (hin : ScheduledInput P ξ U) : ∀ᵐ ω ∂P, U ω ∈ Icc (0 : ℝ) 1 := by
  rw [hin.uniform.ae_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc.mem]
  exact ae_restrict_mem measurableSet_Icc

/-- Almost surely only finitely many customers arrive in any bounded window `[0,T]`. -/
theorem arrivals_finite (hh : 0 < h) (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, {j : ℤ | arrival h ξ U j ω ∈ Icc 0 T}.Finite := by
  have h1 : ∀ K : ℕ, ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (m : ℤ) ω + K < m * h := by
    intro K
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω + K)
      (hin.integrable.neg.add (integrable_const _))
    intro m
    exact (hin.identDistrib (m : ℤ)).comp (u := fun x : ℝ => -x + (K : ℝ)) (by fun_prop)
  have h2 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, ξ (-(m : ℤ)) ω + h < m * h := by
    apply bc_eventually_lt hh (W := fun ω => ξ 0 ω + h)
      (hin.integrable.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x : ℝ => x + h) (by fun_prop)
  rw [← ae_all_iff] at h1
  filter_upwards [h1, h2, uniform_mem hin] with ω h1 h2 hU
  intro T
  obtain ⟨K, hK⟩ := exists_nat_ge T
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 K)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  have hsub : {j : ℤ | arrival h ξ U j ω ∈ Icc 0 T} ⊆ (Finset.Icc (-(N2 : ℤ)) N1 : Set ℤ) := by
    intro j ⟨hj1, hj2⟩
    simp only [arrival] at hj1 hj2
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · by_contra hc
      have hm := hN2 (-j).toNat (by omega)
      have e : (-(((-j).toNat : ℕ) : ℤ)) = j := by omega
      have e2 : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by
        have : (((-j).toNat : ℕ) : ℤ) = -j := by omega
        exact_mod_cast this
      rw [e, e2] at hm
      nlinarith [hU.2]
    · by_contra hc
      have hm := hN1 j.toNat (by omega)
      have e : ((j.toNat : ℕ) : ℤ) = j := by omega
      have e2 : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast e
      rw [e, e2] at hm
      nlinarith [hU.1]
  exact (Finset.finite_toSet _).subset hsub

/-- Almost surely no customer arrives exactly at a given time `c`. -/
theorem no_atom (hh : 0 < h) (hin : ScheduledInput P ξ U) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ j : ℤ, arrival h ξ U j ω ≠ c := by
  rw [ae_all_iff]
  intro j
  have hind : IndepFun U (ξ j) P :=
    hin.indep_shift.comp (φ := id) (ψ := fun x : ℤ → ℝ => x j) measurable_id (measurable_pi_apply j)
  have hUae : AEMeasurable U P := hin.uniform.aemeasurable
  have hprod : P.map (fun ω => (U ω, ξ j ω)) = (volume.restrict (Icc (0 : ℝ) 1)).prod (P.map (ξ j)) := by
    rw [hind.map_prod_eq_prod_map_map hUae (hin.measurable j).aemeasurable, hin.uniform.map_eq]
  set D : Set (ℝ × ℝ) := {p | (j : ℝ) * h + h * p.1 + p.2 = c}
  have hD : MeasurableSet D := measurableSet_eq_fun (by fun_prop) measurable_const
  rw [ae_iff]
  have e : {ω | ¬ arrival h ξ U j ω ≠ c} = (fun ω => (U ω, ξ j ω)) ⁻¹' D := by
    ext ω; simp [D, arrival]
  rw [e, ← Measure.map_apply_of_aemeasurable (hUae.prodMk (hin.measurable j).aemeasurable) hD, hprod,
    Measure.prod_apply_symm hD]
  have hz : ∀ y : ℝ, volume.restrict (Icc (0 : ℝ) 1) ((fun u => (u, y)) ⁻¹' D) = 0 := by
    intro y
    apply measure_mono_null (t := {(c - j * h - y) / h})
    · intro u hu
      simp only [mem_preimage, D, mem_setOf_eq] at hu
      simp only [mem_singleton_iff]
      field_simp
      linarith
    · exact le_antisymm ((Measure.restrict_le_self _).trans_eq Real.volume_singleton) bot_le
  simp_rw [hz]
  exact lintegral_zero

end SQLoynesAux

open ScheduledQueue.Stability SQLoynesAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    ∀ t : ℝ, 0 ≤ t → IdentDistrib (workload h ξ U t) (revMax h ξ U t) P P := by
  intro t ht
  set θ : ℝ := Int.fract (t / h)
  set m : ℤ := ⌊t / h⌋
  have hθ0 : 0 ≤ θ := Int.fract_nonneg _
  have hθ1 : θ < 1 := Int.fract_lt_one _
  have ht_eq : t = ((m : ℝ) + θ) * h := by
    rw [Int.floor_add_fract, div_mul_cancel₀ _ hh.ne']
  -- `M(t)` as a function of the configuration
  have hM : revMax h ξ U t =ᵐ[P] fun ω => Fq h t (U ω, fun i => ξ i ω) := by
    filter_upwards [revCount_finite hh hin] with ω hf
    have hmono : Monotone fun s => revCount h ξ U s ω := fun s s' hss' =>
      encard_le_encard (fun j hj => ⟨hj.1, hj.2.trans hss'⟩)
    have := sup_eq_rat hh ht (fun s => revCount h ξ U s ω) hmono (hf t)
    simp only [revMax, Lam]
    rw [this]
    rfl
  -- `W(t)` as the same function of the reflected configuration
  have hW : workload h ξ U t =ᵐ[P] fun ω => Fq h t (Φ θ m (U ω, fun i => ξ i ω)) := by
    filter_upwards [arrivals_finite hh hin, no_atom hh hin 0, no_atom hh hin t] with ω hfin h0 htt
    have hB := workload_sup_eq hh ht (fun j => arrival h ξ U j ω) (hfin t) h0 htt
    set e : ℤ := if U ω ≤ θ then m else m - 1
    have hpt : ∀ i : ℤ, (i : ℝ) * h + (Φ θ m (U ω, fun i => ξ i ω)).1 * h -
        (Φ θ m (U ω, fun i => ξ i ω)).2 i = t - arrival h ξ U (e - i) ω := by
      intro i
      simp only [Φ, arrival, e]
      by_cases hu : U ω ≤ θ
      · simp only [hu, if_true]; rw [ht_eq]; push_cast; ring
      · simp only [hu, if_false]; rw [ht_eq]; push_cast; ring
    have hcnt : ∀ v : ℝ, cnt h (Φ θ m (U ω, fun i => ξ i ω)) v =
        {j | t - arrival h ξ U j ω ∈ Ioc 0 v}.encard := by
      intro v
      simp only [cnt, hpt]
      have hset : {i : ℤ | t - arrival h ξ U (e - i) ω ∈ Ioc 0 v} =
          (fun j => e - j) '' {j | t - arrival h ξ U j ω ∈ Ioc 0 v} := by
        ext i; simp only [mem_setOf_eq, mem_image]
        constructor
        · intro hi; exact ⟨e - i, hi, by ring⟩
        · rintro ⟨j, hj, rfl⟩; simpa using hj
      rw [hset]
      exact Function.Injective.encard_image (fun a b hab => by simpa using hab) _
    have hmono : Monotone fun v => cnt h (Φ θ m (U ω, fun i => ξ i ω)) v := fun v v' hvv' =>
      encard_le_encard (fun j hj => ⟨hj.1, hj.2.trans hvv'⟩)
    have hfinC : cnt h (Φ θ m (U ω, fun i => ξ i ω)) t ≠ ⊤ := by
      rw [hcnt]
      refine ((hfin t).subset ?_).encard_lt_top.ne
      intro j hj
      simp only [mem_setOf_eq, mem_Ioc, mem_Icc] at hj ⊢
      constructor <;> linarith [hj.1, hj.2]
    have hS := sup_eq_rat hh ht _ hmono hfinC
    simp only [hcnt] at hS
    show workload h ξ U t ω = _
    simp only [workload, count]
    rw [hB, hS]
    unfold Fq
    simp only [hcnt]
  have hlaw := law_Φ hin hθ0 hθ1 m
  have hF := hlaw.comp (measurable_Fq h t)
  have hWae : AEMeasurable (workload h ξ U t) P := hF.aemeasurable_fst.congr hW.symm
  exact ((IdentDistrib.of_ae_eq hWae hW).trans hF).trans
    (IdentDistrib.of_ae_eq hF.aemeasurable_snd hM.symm)
