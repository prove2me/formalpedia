-- Prove2me | solution 1 for PermLimits.Existence.converges_iff_stepLimit_densityConv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:48:48.804028+00:00
-- url     : https://prove2.me/submissions/df4c7554-abfe-4d6c-bc70-50752206bf0c

import Mathlib
import Definitions.Def_PermLimits_Shared_LimitPermutation
import Definitions.Def_PermLimits_Shared_ConvergesTo
import Definitions.Def_PermLimits_Shared_StepLimit
import Definitions.Def_PermLimits_Shared_LimitConvergence
open PermLimits.Shared

namespace PermLimits.Existence

open Filter unitInterval MeasureTheory

/-- Row index map on naturals. -/
noncomputable def aux_cis_rowF {n : ℕ} (hn : 0 < n) (c : ℕ) : Fin n :=
  ⟨min (c - 1) (n - 1), by omega⟩

/-- The row of `x` in the step limit permutation. -/
noncomputable def aux_cis_row {n : ℕ} (hn : 0 < n) (x : I) : Fin n :=
  aux_cis_rowF hn ⌈(n : ℝ) * (x : ℝ)⌉₊

lemma aux_cis_stepLimit_eq {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x y : I) :
    stepLimit π x y =
      min 1 (max 0 ((n : ℝ) * (y : ℝ) - ((π (aux_cis_row hn x) : ℕ) : ℝ))) := by
  rw [stepLimit, dif_pos hn]; rfl

lemma aux_cis_row_mono {n : ℕ} (hn : 0 < n) {x x' : I} (h : x ≤ x') :
    aux_cis_row hn x ≤ aux_cis_row hn x' := by
  unfold aux_cis_row aux_cis_rowF
  rw [Fin.mk_le_mk]
  have : ⌈(n : ℝ) * (x : ℝ)⌉₊ ≤ ⌈(n : ℝ) * (x' : ℝ)⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr h) (Nat.cast_nonneg n))
  omega

lemma aux_cis_row_bounds {n : ℕ} (hn : 0 < n) (x : I) :
    ((aux_cis_row hn x : ℕ) : ℝ) ≤ (n : ℝ) * x ∧
      (n : ℝ) * x ≤ ((aux_cis_row hn x : ℕ) : ℝ) + 1 := by
  have hx0 : (0:ℝ) ≤ x := x.2.1
  have hx1 : (x:ℝ) ≤ 1 := x.2.2
  have hcn : ⌈(n : ℝ) * (x : ℝ)⌉₊ ≤ n := by
    apply Nat.ceil_le.mpr
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hval : (aux_cis_row hn x : ℕ) = ⌈(n : ℝ) * (x : ℝ)⌉₊ - 1 := by
    simp only [aux_cis_row, aux_cis_rowF]; omega
  rw [hval]
  have h1 : (n:ℝ) * x ≤ ⌈(n : ℝ) * (x : ℝ)⌉₊ := Nat.le_ceil _
  rcases Nat.eq_zero_or_pos ⌈(n : ℝ) * (x : ℝ)⌉₊ with h0 | hpos
  · rw [h0] at h1 ⊢
    simp only [zero_tsub, Nat.cast_zero, zero_add] at h1 ⊢
    constructor
    · positivity
    · linarith
  · have h2 : (⌈(n : ℝ) * (x : ℝ)⌉₊ : ℝ) < (n:ℝ) * x + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [Nat.cast_sub hpos]
    push_cast
    constructor <;> linarith

lemma aux_cis_quantile {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (x u : I) :
    (quantile (stepLimit π) x u : ℝ) =
      if (u : ℝ) = 0 then 0 else (((π (aux_cis_row hn x) : ℕ) : ℝ) + u) / n := by
  have hj0 : (0:ℝ) ≤ ((π (aux_cis_row hn x) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hjn : ((π (aux_cis_row hn x) : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast (π (aux_cis_row hn x)).isLt
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hu0 : (0:ℝ) ≤ u := u.2.1
  have hu1 : (u:ℝ) ≤ 1 := u.2.2
  split_ifs with hu
  · have hle : quantile (stepLimit π) x u ≤ 0 := by
      apply sInf_le
      show (u:ℝ) ≤ stepLimit π x 0
      rw [aux_cis_stepLimit_eq hn, hu]
      exact le_min zero_le_one (le_max_left _ _)
    have h1 : (quantile (stepLimit π) x u : ℝ) ≤ ((0 : I) : ℝ) := Subtype.coe_le_coe.mpr hle
    have h2 : (0:ℝ) ≤ quantile (stepLimit π) x u := (quantile (stepLimit π) x u).2.1
    simp only [Set.Icc.coe_zero] at h1
    linarith
  · have hupos : (0:ℝ) < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    set j : ℝ := ((π (aux_cis_row hn x) : ℕ) : ℝ) with hj
    have hy0 : (j + u) / n ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by positivity, (div_le_one hnpos).mpr (by linarith)⟩
    have key : quantile (stepLimit π) x u = ⟨(j + u) / n, hy0⟩ := by
      apply le_antisymm
      · apply sInf_le
        show (u:ℝ) ≤ stepLimit π x ⟨(j + u) / n, hy0⟩
        rw [aux_cis_stepLimit_eq hn]
        have : (n:ℝ) * ((j + u) / n) - j = u := by field_simp; ring
        simp only [← hj]
        rw [this, max_eq_right hu0, min_eq_right hu1]
      · apply le_sInf
        intro y hy
        have hy' : (u:ℝ) ≤ stepLimit π x y := hy
        rw [aux_cis_stepLimit_eq hn] at hy'
        simp only [← hj] at hy'
        have h3 : (u:ℝ) ≤ max 0 ((n:ℝ) * y - j) := (le_min_iff.mp hy').2
        have h4 : (u:ℝ) ≤ (n:ℝ) * y - j := by
          rcases le_max_iff.mp h3 with h | h
          · linarith
          · exact h
        show ((⟨(j + u) / n, hy0⟩ : I) : ℝ) ≤ (y : ℝ)
        simp only
        rw [div_le_iff₀ hnpos]
        linarith
    rw [key]

lemma aux_cis_row_meas {n : ℕ} (hn : 0 < n) : Measurable (aux_cis_row hn) := by
  have : Measurable (fun x : I => ⌈(n : ℝ) * (x : ℝ)⌉₊) :=
    (measurable_const.mul measurable_subtype_coe).nat_ceil
  exact (measurable_from_nat (f := aux_cis_rowF hn)).comp this

lemma aux_cis_g_meas {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    Measurable (fun p : I × I => (p.1, quantile (stepLimit π) p.1 p.2)) := by
  refine measurable_fst.prodMk ?_
  apply unitInterval.measurableEmbedding_coe.measurable_comp_iff.mp
  have : (Subtype.val ∘ fun p : I × I => quantile (stepLimit π) p.1 p.2) =
      fun p => if (p.2 : ℝ) = 0 then 0 else (((π (aux_cis_row hn p.1) : ℕ) : ℝ) + p.2) / n := by
    funext p; exact aux_cis_quantile hn π p.1 p.2
  rw [this]
  refine Measurable.ite ?_ measurable_const ?_
  · exact (measurable_subtype_coe.comp measurable_snd) (measurableSet_singleton (0:ℝ))
  · refine Measurable.div_const (Measurable.add ?_ (measurable_subtype_coe.comp measurable_snd)) _
    exact (measurable_of_countable (fun a : Fin n => ((π a : ℕ) : ℝ))).comp
      ((aux_cis_row_meas hn).comp measurable_fst)

/-- The open box of row `a`. -/
def aux_cis_B {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (a : Fin n) : Set (I × I) :=
  {q | aux_cis_row hn q.1 = a ∧ ((π a : ℕ) : ℝ) / n < (q.2 : ℝ) ∧
    (q.2 : ℝ) < (((π a : ℕ) : ℝ) + 1) / n}

lemma aux_cis_B_meas {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (a : Fin n) :
    MeasurableSet (aux_cis_B hn π a) := by
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact ((aux_cis_row_meas hn).comp measurable_fst) (measurableSet_singleton a)
  · exact measurableSet_lt measurable_const (measurable_subtype_coe.comp measurable_snd)
  · exact measurableSet_lt (measurable_subtype_coe.comp measurable_snd) measurable_const

lemma aux_cis_preimage_B {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (a : Fin n) :
    (fun p : I × I => (p.1, quantile (stepLimit π) p.1 p.2)) ⁻¹' aux_cis_B hn π a =
      {x | aux_cis_row hn x = a} ×ˢ Set.Ioo (0 : I) 1 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  ext ⟨x, u⟩
  simp only [Set.mem_preimage, aux_cis_B, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioo]
  rw [aux_cis_quantile hn π x u]
  have hu0 : (0:ℝ) ≤ u := u.2.1
  have hj0 : (0:ℝ) ≤ ((π a : ℕ) : ℝ) := Nat.cast_nonneg _
  have h0 : ((0:I) < u) ↔ (0:ℝ) < u := by
    rw [← Subtype.coe_lt_coe]; simp
  have h1 : (u < (1:I)) ↔ (u:ℝ) < 1 := by
    rw [← Subtype.coe_lt_coe]; simp
  rw [h0, h1]
  constructor
  · rintro ⟨hr, ha1, ha2⟩
    subst hr
    refine ⟨rfl, ?_⟩
    split_ifs at ha1 ha2 with hu
    · exfalso
      have : (0:ℝ) ≤ ((π (aux_cis_row hn x) : ℕ) : ℝ) / n := by positivity
      linarith
    · constructor
      · have := (div_lt_div_iff_of_pos_right hnpos).mp ha1
        linarith
      · have := (div_lt_div_iff_of_pos_right hnpos).mp ha2
        linarith
  · rintro ⟨hr, hu1, hu2⟩
    subst hr
    refine ⟨rfl, ?_⟩
    rw [if_neg (ne_of_gt hu1)]
    constructor
    · apply (div_lt_div_iff_of_pos_right hnpos).mpr
      linarith
    · apply (div_lt_div_iff_of_pos_right hnpos).mpr
      linarith

lemma aux_cis_vol_row {n : ℕ} (hn : 0 < n) (a : Fin n) :
    volume {x : I | aux_cis_row hn x = a} = ENNReal.ofReal (1 / n) := by
  rw [unitInterval.volume_apply]
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have ha : ((a:ℕ):ℝ) + 1 ≤ n := by exact_mod_cast a.isLt
  have hlen : ((a:ℕ) + 1 : ℝ) / n - (a:ℕ) / n = 1 / n := by field_simp; ring
  apply le_antisymm
  · calc volume (Subtype.val '' {x : I | aux_cis_row hn x = a})
        ≤ volume (Set.Icc (((a:ℕ):ℝ) / n) ((((a:ℕ):ℝ) + 1) / n)) := by
          apply measure_mono
          rintro _ ⟨x, hx, rfl⟩
          have hb := aux_cis_row_bounds hn x
          have hx' : aux_cis_row hn x = a := hx
          rw [hx'] at hb
          constructor
          · rw [div_le_iff₀ hnpos]; linarith
          · rw [le_div_iff₀ hnpos]; linarith
      _ = ENNReal.ofReal (1 / n) := by rw [Real.volume_Icc, hlen]
  · calc ENNReal.ofReal (1 / n)
        = volume (Set.Ioo (((a:ℕ):ℝ) / n) ((((a:ℕ):ℝ) + 1) / n)) := by
          rw [Real.volume_Ioo, hlen]
      _ ≤ _ := by
          apply measure_mono
          intro t ht
          have ht0 : 0 ≤ t := le_trans (by positivity) ht.1.le
          have ht1 : t ≤ 1 := le_trans ht.2.le ((div_le_one hnpos).mpr ha)
          refine ⟨⟨t, ht0, ht1⟩, ?_, rfl⟩
          have hb := aux_cis_row_bounds hn ⟨t, ht0, ht1⟩
          simp only at hb
          have e1 : ((a:ℕ):ℝ) < n * t := by
            have := (div_lt_iff₀ hnpos).mp ht.1; linarith
          have e2 : n * t < ((a:ℕ):ℝ) + 1 := by
            have := (lt_div_iff₀ hnpos).mp ht.2; linarith
          have f1 : ((aux_cis_row hn ⟨t, ht0, ht1⟩ : ℕ) : ℝ) < (a:ℕ) + 1 := by linarith
          have f2 : ((a:ℕ):ℝ) < (aux_cis_row hn ⟨t, ht0, ht1⟩ : ℕ) + 1 := by linarith
          have g1 : (aux_cis_row hn ⟨t, ht0, ht1⟩ : ℕ) < (a:ℕ) + 1 := by exact_mod_cast f1
          have g2 : (a:ℕ) < (aux_cis_row hn ⟨t, ht0, ht1⟩ : ℕ) + 1 := by exact_mod_cast f2
          show aux_cis_row hn ⟨t, ht0, ht1⟩ = a
          apply Fin.ext
          omega

lemma aux_cis_mu_B {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) (a : Fin n) :
    limitMeasure (stepLimit π) (aux_cis_B hn π a) = ENNReal.ofReal (1 / n) := by
  unfold limitMeasure
  rw [Measure.map_apply (aux_cis_g_meas hn π) (aux_cis_B_meas hn π a), aux_cis_preimage_B,
    Measure.volume_eq_prod, Measure.prod_prod, aux_cis_vol_row, unitInterval.volume_Ioo]
  simp

lemma aux_cis_mu_compl {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) :
    limitMeasure (stepLimit π) (⋃ a, aux_cis_B hn π a)ᶜ = 0 := by
  unfold limitMeasure
  rw [Measure.map_apply (aux_cis_g_meas hn π)
    (MeasurableSet.compl (MeasurableSet.iUnion fun a => aux_cis_B_meas hn π a))]
  apply measure_mono_null (t := Set.univ ×ˢ (Set.Ioo (0:I) 1)ᶜ)
  · intro p hp
    refine ⟨trivial, fun hu => hp ?_⟩
    have hmem : p ∈ {x | aux_cis_row hn x = aux_cis_row hn p.1} ×ˢ Set.Ioo (0:I) 1 :=
      ⟨rfl, hu⟩
    rw [← aux_cis_preimage_B hn π] at hmem
    exact Set.mem_iUnion.mpr ⟨_, hmem⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod,
      measure_compl measurableSet_Ioo (measure_ne_top _ _), unitInterval.volume_Ioo]
    simp

lemma aux_cis_Ly {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) {a b : Fin n} {q q' : I × I}
    (hq : q ∈ aux_cis_B hn π a) (hq' : q' ∈ aux_cis_B hn π b) (hab : a ≠ b) :
    q.2 < q'.2 ↔ π a < π b := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨_, hq1, hq2⟩ := hq
  obtain ⟨_, hq1', hq2'⟩ := hq'
  rw [← Subtype.coe_lt_coe, Fin.lt_def]
  have hne : (π a : ℕ) ≠ (π b : ℕ) := fun h => hab (π.injective (Fin.ext h))
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : ((π a : ℕ) : ℝ) + 1 ≤ ((π b : ℕ) : ℝ) := by exact_mod_cast h
    have : (((π a : ℕ) : ℝ) + 1) / n ≤ ((π b : ℕ) : ℝ) / n :=
      div_le_div_of_nonneg_right h' hnpos.le
    exact ⟨fun _ => h, fun _ => by linarith⟩
  · have h' : ((π b : ℕ) : ℝ) + 1 ≤ ((π a : ℕ) : ℝ) := by exact_mod_cast h
    have : (((π b : ℕ) : ℝ) + 1) / n ≤ ((π a : ℕ) : ℝ) / n :=
      div_le_div_of_nonneg_right h' hnpos.le
    constructor
    · intro h2; exfalso; linarith
    · intro h2; exfalso; omega

lemma aux_cis_Lx1 {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) {a b : Fin n} {q q' : I × I}
    (hq : q ∈ aux_cis_B hn π a) (hq' : q' ∈ aux_cis_B hn π b) (hab : a < b) :
    q.1 < q'.1 := by
  by_contra h
  push Not at h
  have := aux_cis_row_mono hn h
  rw [hq.1, hq'.1] at this
  exact absurd hab (not_lt.mpr this)

lemma aux_cis_Lx2 {n : ℕ} (hn : 0 < n) (π : Equiv.Perm (Fin n)) {a b : Fin n} {q q' : I × I}
    (hq : q ∈ aux_cis_B hn π a) (hq' : q' ∈ aux_cis_B hn π b) (h : q.1 < q'.1) :
    a ≤ b := by
  have := aux_cis_row_mono hn h.le
  rwa [hq.1, hq'.1] at this

/-- The good row tuples. -/
noncomputable def aux_cis_goodP {n k : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (r : Fin k → Fin n) : Prop :=
  ∃ ρ : Equiv.Perm (Fin k), (∀ i j, i < j → r (ρ i) < r (ρ j)) ∧
    ∀ i j, (π (r (ρ i)) < π (r (ρ j)) ↔ τ i < τ j)

open Classical in
/-- The finset of good row tuples. -/
noncomputable def aux_cis_good {n k : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    Finset (Fin k → Fin n) :=
  Finset.univ.filter (fun r => aux_cis_goodP τ π r)

open Classical in
/-- The finset of non-injective tuples. -/
noncomputable def aux_cis_noninj (k n : ℕ) : Finset (Fin k → Fin n) :=
  Finset.univ.filter (fun r => ¬ Function.Injective r)

lemma aux_cis_goodP_inj {n k : ℕ} {τ : Equiv.Perm (Fin k)} {π : Equiv.Perm (Fin n)}
    {r : Fin k → Fin n} (h : aux_cis_goodP τ π r) : Function.Injective r := by
  obtain ⟨ρ, h1, _⟩ := h
  have hm : StrictMono (fun i => r (ρ i)) := fun i j hij => h1 i j hij
  intro a b hab
  have : ρ.symm a = ρ.symm b := hm.injective (by simpa using hab)
  simpa using this

lemma aux_cis_good_sub {n k : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    {r : Fin k → Fin n} (h : aux_cis_goodP τ π r) :
    (Set.univ.pi fun i => aux_cis_B hn π (r i)) ⊆ patternEvent τ := by
  intro p hp
  rw [Set.mem_univ_pi] at hp
  have hinj := aux_cis_goodP_inj h
  obtain ⟨ρ, h1, h2⟩ := h
  refine ⟨ρ, fun i j hij => aux_cis_Lx1 hn π (hp _) (hp _) (h1 i j hij), fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij; simp
  · rw [aux_cis_Ly hn π (hp _) (hp _) (fun he => hij (ρ.injective (hinj he)))]
    exact h2 i j

lemma aux_cis_inj_good {n k : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    {r : Fin k → Fin n} (hinj : Function.Injective r) {p : Fin k → I × I}
    (hp : p ∈ Set.univ.pi fun i => aux_cis_B hn π (r i)) (hA : p ∈ patternEvent τ) :
    aux_cis_goodP τ π r := by
  rw [Set.mem_univ_pi] at hp
  obtain ⟨ρ, h1, h2⟩ := hA
  refine ⟨ρ, fun i j hij => ?_, fun i j => ?_⟩
  · have hle := aux_cis_Lx2 hn π (hp _) (hp _) (h1 i j hij)
    have hne : r (ρ i) ≠ r (ρ j) := fun he => (ne_of_lt hij) (ρ.injective (hinj he))
    exact lt_of_le_of_ne hle hne
  · by_cases hij : i = j
    · subst hij; simp
    · rw [← aux_cis_Ly hn π (hp _) (hp _) (fun he => hij (ρ.injective (hinj he)))]
      exact h2 i j

lemma aux_cis_lower {n k : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    ((aux_cis_good τ π).card : ENNReal) * ENNReal.ofReal (1 / n) ^ k ≤
      Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π)) (patternEvent τ) := by
  have : IsProbabilityMeasure (limitMeasure (stepLimit π)) :=
    Measure.isProbabilityMeasure_map (aux_cis_g_meas hn π).aemeasurable
  have hP : ∀ r : Fin k → Fin n, Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
      (Set.univ.pi fun i => aux_cis_B hn π (r i)) = ENNReal.ofReal (1 / n) ^ k := by
    intro r
    rw [Measure.pi_pi]
    simp [aux_cis_mu_B]
  calc ((aux_cis_good τ π).card : ENNReal) * ENNReal.ofReal (1 / n) ^ k
      = ∑ r ∈ aux_cis_good τ π, Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
          (Set.univ.pi fun i => aux_cis_B hn π (r i)) := by
        simp [hP]
    _ = Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
          (⋃ r ∈ aux_cis_good τ π, Set.univ.pi fun i => aux_cis_B hn π (r i)) := by
        rw [measure_biUnion_finset]
        · intro r _ r' _ hne
          refine Set.disjoint_left.mpr fun p hp hp' => hne ?_
          rw [Set.mem_univ_pi] at hp hp'
          funext i
          exact (hp i).1.symm.trans (hp' i).1
        · intro r _
          exact MeasurableSet.univ_pi fun i => aux_cis_B_meas hn π (r i)
    _ ≤ _ := by
        apply measure_mono
        refine Set.iUnion₂_subset fun r hr => aux_cis_good_sub hn τ π ?_
        classical
        simpa [aux_cis_good] using hr

lemma aux_cis_upper {n k : ℕ} (hn : 0 < n) (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π)) (patternEvent τ) ≤
      (((aux_cis_good τ π).card + (aux_cis_noninj k n).card : ℕ) : ENNReal) *
        ENNReal.ofReal (1 / n) ^ k := by
  classical
  have : IsProbabilityMeasure (limitMeasure (stepLimit π)) :=
    Measure.isProbabilityMeasure_map (aux_cis_g_meas hn π).aemeasurable
  have hP : ∀ r : Fin k → Fin n, Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
      (Set.univ.pi fun i => aux_cis_B hn π (r i)) = ENNReal.ofReal (1 / n) ^ k := by
    intro r
    rw [Measure.pi_pi]
    simp [aux_cis_mu_B]
  set T := aux_cis_good τ π ∪ aux_cis_noninj k n with hT
  have hsub : patternEvent τ ⊆ (⋃ r ∈ T, Set.univ.pi fun i => aux_cis_B hn π (r i)) ∪
      ⋃ i : Fin k, Function.eval i ⁻¹' (⋃ a, aux_cis_B hn π a)ᶜ := by
    intro p hp
    by_cases hU : ∀ i, p i ∈ ⋃ a, aux_cis_B hn π a
    · left
      have hpr : p ∈ Set.univ.pi fun i => aux_cis_B hn π (aux_cis_row hn (p i).1) := by
        rw [Set.mem_univ_pi]; intro i
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hU i)
        have : aux_cis_row hn (p i).1 = a := ha.1
        rw [this]; exact ha
      rw [Set.mem_iUnion₂]
      refine ⟨fun i => aux_cis_row hn (p i).1, ?_, hpr⟩
      by_cases hinj : Function.Injective (fun i => aux_cis_row hn (p i).1)
      · refine Finset.mem_union_left _ ?_
        simp only [aux_cis_good, Finset.mem_filter, Finset.mem_univ, true_and]
        exact aux_cis_inj_good hn τ π hinj hpr hp
      · refine Finset.mem_union_right _ ?_
        simp only [aux_cis_noninj, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hinj
    · right
      push Not at hU
      obtain ⟨i, hi⟩ := hU
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  calc Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π)) (patternEvent τ)
      ≤ Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
          ((⋃ r ∈ T, Set.univ.pi fun i => aux_cis_B hn π (r i)) ∪
            ⋃ i : Fin k, Function.eval i ⁻¹' (⋃ a, aux_cis_B hn π a)ᶜ) := measure_mono hsub
    _ ≤ Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
          (⋃ r ∈ T, Set.univ.pi fun i => aux_cis_B hn π (r i)) +
        Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
          (⋃ i : Fin k, Function.eval i ⁻¹' (⋃ a, aux_cis_B hn π a)ᶜ) := measure_union_le _ _
    _ ≤ (∑ r ∈ T, Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))
          (Set.univ.pi fun i => aux_cis_B hn π (r i))) + 0 := by
        gcongr
        · exact measure_biUnion_finset_le _ _
        · rw [measure_iUnion_null]
          intro i
          exact Measure.pi_eval_preimage_null _ (aux_cis_mu_compl hn π)
    _ = (T.card : ENNReal) * ENNReal.ofReal (1 / n) ^ k := by simp [hP]
    _ ≤ _ := by
        gcongr
        exact_mod_cast Finset.card_union_le _ _

lemma aux_cis_perm_strictMono_eq {k : ℕ} (e : Equiv.Perm (Fin k)) (he : StrictMono e) (i : Fin k) :
    e i = i := by
  have hsymm : StrictMono e.symm := by
    intro a b hab
    by_contra h
    push Not at h
    have := he.monotone h
    simp at this
    exact absurd hab (not_lt.mpr this)
  have h1 : i ≤ e i := he.le_apply
  have h2 : e i ≤ e.symm (e i) := hsymm.le_apply
  simp at h2
  exact le_antisymm h2 h1

lemma aux_cis_card_good {n k : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    (aux_cis_good τ π).card = k.factorial * occurrences τ π := by
  classical
  unfold occurrences
  rw [show k.factorial = (Finset.univ : Finset (Equiv.Perm (Fin k))).card by
    simp [Fintype.card_perm], ← Finset.card_product]
  symm
  apply Finset.card_bij (fun (q : Equiv.Perm (Fin k) × (Fin k → Fin n)) _ =>
    fun i => q.2 (q.1.symm i))
  · rintro ⟨ρ, x⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [aux_cis_good, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨ρ, ?_, ?_⟩
    · simpa using hq.1
    · simpa using hq.2
  · rintro ⟨ρ, x⟩ hq ⟨ρ', x'⟩ hq' heq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hq hq'
    have hx : StrictMono x := fun i j h => hq.1 i j h
    have hx' : StrictMono x' := fun i j h => hq'.1 i j h
    have hσ : ∀ l, x l = x' (ρ'.symm (ρ l)) := fun l => by
      have := congrFun heq (ρ l); simpa using this
    have hmono : StrictMono (ρ.trans ρ'.symm) := by
      intro i j hij
      have := hx hij
      rw [hσ i, hσ j] at this
      exact hx'.lt_iff_lt.mp this
    have hid := aux_cis_perm_strictMono_eq _ hmono
    have hρ : ρ = ρ' := by
      ext l
      have := congrArg ρ' (hid l)
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at this
      rw [this]
    subst hρ
    have hxx : x = x' := by
      funext l; rw [hσ l]; simp
    rw [hxx]
  · intro r hr
    simp only [aux_cis_good, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨ρ, h1, h2⟩ := hr
    refine ⟨(ρ, fun i => r (ρ i)), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h1, h2⟩
    · funext i; simp

lemma aux_cis_card_inj (k n : ℕ) :
    (Finset.univ.filter (fun r : Fin k → Fin n => Function.Injective r)).card =
      n.descFactorial k := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq]
  simp

lemma aux_cis_card_noninj (k n : ℕ) :
    (aux_cis_noninj k n).card + n.descFactorial k = n ^ k := by
  classical
  rw [← aux_cis_card_inj k n, aux_cis_noninj, add_comm]
  convert Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → Fin n))) (fun r : Fin k → Fin n => Function.Injective r)
  simp

lemma aux_cis_card_good_le {n k : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    (aux_cis_good τ π).card ≤ n.descFactorial k := by
  classical
  rw [← aux_cis_card_inj k n]
  apply Finset.card_le_card
  intro r hr
  simp only [aux_cis_good, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact aux_cis_goodP_inj hr

lemma aux_cis_bound {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (τ : Equiv.Perm (Fin k))
    (π : Equiv.Perm (Fin n)) :
    |permDensity τ π - limitDensity τ (stepLimit π)| ≤
      1 - (n.descFactorial k : ℝ) / (n : ℝ) ^ k := by
  have : IsProbabilityMeasure (limitMeasure (stepLimit π)) :=
    Measure.isProbabilityMeasure_map (aux_cis_g_meas hn π).aemeasurable
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hN : (0:ℝ) < (n:ℝ) ^ k := pow_pos hnpos k
  set c : ℕ := (aux_cis_good τ π).card with hc
  set e : ℕ := (aux_cis_noninj k n).card with he
  set D : ℕ := n.descFactorial k with hD
  have hDpos : (0:ℝ) < D := by exact_mod_cast Nat.descFactorial_pos.mpr hk
  have hDN : (D:ℝ) ≤ (n:ℝ) ^ k := by exact_mod_cast Nat.descFactorial_le_pow n k
  have hcD : (c:ℝ) ≤ D := by exact_mod_cast aux_cis_card_good_le τ π
  have heD : (e:ℝ) + D = (n:ℝ) ^ k := by exact_mod_cast aux_cis_card_noninj k n
  have hw : (ENNReal.ofReal (1 / n) ^ k).toReal = 1 / (n:ℝ) ^ k := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]; simp
  have hfin : Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π)) (patternEvent τ) ≠ ⊤ :=
    measure_ne_top _ _
  have hlow : (c:ℝ) / (n:ℝ) ^ k ≤ limitDensity τ (stepLimit π) := by
    have := ENNReal.toReal_mono hfin (aux_cis_lower hn τ π)
    rw [ENNReal.toReal_mul, hw] at this
    simp only [ENNReal.toReal_natCast] at this
    unfold limitDensity
    rw [measureReal_def]
    rw [div_eq_mul_one_div]
    exact this
  have hup : limitDensity τ (stepLimit π) ≤ ((c:ℝ) + e) / (n:ℝ) ^ k := by
    have h1 := aux_cis_upper hn τ π
    have h2 : ((((aux_cis_good τ π).card + (aux_cis_noninj k n).card : ℕ) : ENNReal) *
        ENNReal.ofReal (1 / n) ^ k) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    have := ENNReal.toReal_mono h2 h1
    rw [ENNReal.toReal_mul, hw] at this
    simp only [ENNReal.toReal_natCast] at this
    unfold limitDensity
    rw [measureReal_def, div_eq_mul_one_div]
    push_cast at this
    exact this
  have hperm : permDensity τ π = (c:ℝ) / D := by
    rw [permDensity, if_pos hk, hc, aux_cis_card_good, hD, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    field_simp
  rw [hperm, abs_sub_le_iff]
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg _
  have hcle : (c:ℝ) / D ≤ 1 := (div_le_one hDpos).mpr hcD
  have hq : (0:ℝ) ≤ 1 - (D:ℝ) / (n:ℝ) ^ k := by
    rw [sub_nonneg]; exact (div_le_one hN).mpr hDN
  have key : (c:ℝ) / D - c / (n:ℝ) ^ k = (c / D) * (1 - D / (n:ℝ) ^ k) := by
    field_simp
  have hcc : (c:ℝ) / (n:ℝ) ^ k ≤ c / D := div_le_div_of_nonneg_left hc0 hDpos hDN
  have he' : ((c:ℝ) + e) / (n:ℝ) ^ k = c / (n:ℝ) ^ k + (1 - D / (n:ℝ) ^ k) := by
    have : (e:ℝ) = (n:ℝ) ^ k - D := by linarith
    rw [this]; field_simp
  constructor
  · have : (c:ℝ) / D * (1 - D / (n:ℝ) ^ k) ≤ 1 - D / (n:ℝ) ^ k :=
      mul_le_of_le_one_left hq hcle
    linarith
  · linarith

lemma aux_cis_bound2 {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) (τ : Equiv.Perm (Fin k))
    (π : Equiv.Perm (Fin n)) :
    |permDensity τ π - limitDensity τ (stepLimit π)| ≤ 1 - (1 - (k:ℝ) / n) ^ k := by
  refine le_trans (aux_cis_bound hn hk τ π) ?_
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : (n - k) ^ k ≤ n.descFactorial k :=
    le_trans (Nat.pow_le_pow_left (by omega) k) (Nat.pow_sub_le_descFactorial n k)
  have h2 : (((n - k : ℕ) : ℝ)) ^ k ≤ (n.descFactorial k : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_sub hk] at h2
  have h3 : (1 - (k:ℝ) / n) ^ k = ((n:ℝ) - k) ^ k / (n:ℝ) ^ k := by
    rw [← div_pow]; congr 1; field_simp
  rw [h3]
  have : ((n:ℝ) - k) ^ k / (n:ℝ) ^ k ≤ (n.descFactorial k : ℝ) / (n:ℝ) ^ k :=
    div_le_div_of_nonneg_right h2 (by positivity)
  linarith

lemma aux_cis_diff_tendsto (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    Tendsto (fun m => permDensity τ (s m).2 - limitDensity τ (stepLimit (s m).2))
      atTop (nhds 0) := by
  have hf : Tendsto (fun n : ℕ => 1 - (1 - (k:ℝ) / n) ^ k) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (k:ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (k:ℝ)
    have h1 := ((tendsto_const_nhds (x := (1:ℝ))).sub h0).pow k
    have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub h1
    simpa using h2
  apply squeeze_zero_norm' _ (hf.comp hs)
  filter_upwards [hs.eventually (eventually_ge_atTop (max k 1))] with m hm
  rw [Real.norm_eq_abs]
  exact aux_cis_bound2 (by omega) (by omega) τ (s m).2

end PermLimits.Existence

open PermLimits.Existence Filter unitInterval

theorem solution (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hs : Tendsto (fun m => (s m).1) atTop atTop) (Z : I → I → ℝ) (hZ : IsLimitPerm Z) :
    ConvergesTo s Z ↔ DensityConv (fun m => stepLimit (s m).2) Z := by
  constructor
  · rintro ⟨_, h⟩ k τ
    have := (h k τ).sub (aux_cis_diff_tendsto s hs τ)
    simpa using this
  · intro h
    refine ⟨hs, fun k τ => ?_⟩
    have := (h k τ).add (aux_cis_diff_tendsto s hs τ)
    simpa using this
