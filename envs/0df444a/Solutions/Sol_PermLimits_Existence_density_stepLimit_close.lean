-- Prove2me | solution 1 for PermLimits.Existence.density_stepLimit_close
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:51:13.384326+00:00
-- url     : https://prove2.me/submissions/6edf292a-ad91-43af-9c97-67a4d126fb35

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitMeasure
import Definitions.Def_PermLimits_Shared_StepLimit
open PermLimits.Shared

namespace PermLimits.Existence

open unitInterval MeasureTheory

noncomputable def aux_dsc_row (n : ℕ) (hn : 0 < n) (x : I) : Fin n :=
  ⟨min (⌈(n : ℝ) * (x : ℝ)⌉₊ - 1) (n - 1), by omega⟩

lemma aux_dsc_stepLimit_eq {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (x y : I) :
    stepLimit π x y =
      min 1 (max 0 ((n : ℝ) * (y : ℝ) - ((π (aux_dsc_row n hn x) : ℕ) : ℝ))) := by
  unfold stepLimit; rw [dif_pos hn]; rfl

lemma aux_dsc_row_mono {n : ℕ} (hn : 0 < n) {x x' : I} (h : x ≤ x') :
    aux_dsc_row n hn x ≤ aux_dsc_row n hn x' := by
  rw [Fin.le_def]
  simp only [aux_dsc_row]
  apply min_le_min_right
  apply Nat.sub_le_sub_right
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr h) (Nat.cast_nonneg n)

lemma aux_dsc_row_eq_of_mem {n : ℕ} (hn : 0 < n) (j : Fin n) (x : I)
    (h1 : ((j : ℕ) : ℝ) < (n : ℝ) * x) (h2 : (n : ℝ) * x ≤ (j : ℕ) + 1) :
    aux_dsc_row n hn x = j := by
  have hc : ⌈(n : ℝ) * (x : ℝ)⌉₊ = (j : ℕ) + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    constructor <;> linarith
  apply Fin.ext
  simp only [aux_dsc_row, hc]
  have := j.2
  omega

lemma aux_dsc_mem_of_row_eq {n : ℕ} (hn : 0 < n) (j : Fin n) (x : I)
    (h : aux_dsc_row n hn x = j) :
    ((j : ℕ) : ℝ) ≤ (n : ℝ) * x ∧ (n : ℝ) * x ≤ (j : ℕ) + 1 := by
  have hx0 : (0 : ℝ) ≤ x := x.2.1
  have hx1 : (x : ℝ) ≤ 1 := x.2.2
  have hnx : (n : ℝ) * x ≤ n := by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hcle : ⌈(n : ℝ) * (x : ℝ)⌉₊ ≤ n := by
    rw [Nat.ceil_le]; exact hnx
  have hj : (j : ℕ) = ⌈(n : ℝ) * (x : ℝ)⌉₊ - 1 := by
    have := congrArg Fin.val h
    simp only [aux_dsc_row] at this
    omega
  rcases Nat.eq_zero_or_pos ⌈(n : ℝ) * (x : ℝ)⌉₊ with h0 | hpos
  · have hj0 : (j : ℕ) = 0 := by omega
    rw [Nat.ceil_eq_zero] at h0
    rw [hj0]; push_cast
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have hc : ⌈(n : ℝ) * (x : ℝ)⌉₊ = (j : ℕ) + 1 := by omega
    rw [Nat.ceil_eq_iff (by omega)] at hc
    push_cast at hc
    constructor <;> linarith [hc.1, hc.2]

lemma aux_dsc_measurable_row {n : ℕ} (hn : 0 < n) : Measurable (aux_dsc_row n hn) := by
  have h1 : Measurable (fun x : I => ⌈(n : ℝ) * (x : ℝ)⌉₊) :=
    (measurable_const.mul measurable_subtype_coe).nat_ceil
  have h2 : Measurable (fun m : ℕ => (⟨min (m - 1) (n - 1), by omega⟩ : Fin n)) :=
    measurable_from_nat
  exact h2.comp h1

lemma aux_dsc_quantile_pos {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (x u : I)
    (hu : u ≠ 0) :
    ((quantile (stepLimit π) x u : I) : ℝ) =
      (((π (aux_dsc_row n hn x) : ℕ) : ℝ) + u) / n := by
  set j : ℝ := ((π (aux_dsc_row n hn x) : ℕ) : ℝ) with hjdef
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hu0 : (0 : ℝ) < u := by
    rcases lt_or_eq_of_le u.2.1 with h | h
    · exact h
    · exact absurd (Subtype.ext h.symm) hu
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  have hj0 : 0 ≤ j := Nat.cast_nonneg _
  have hjn : j + 1 ≤ n := by
    have := (π (aux_dsc_row n hn x)).2
    rw [hjdef]; exact_mod_cast this
  have hc : (j + u) / n ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hnpos]; linarith
  have hset : {y : I | (u : ℝ) ≤ stepLimit π x y} = Set.Ici ⟨(j + u) / n, hc⟩ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, aux_dsc_stepLimit_eq π hn]
    rw [← Subtype.coe_le_coe]
    change _ ↔ (j + u) / n ≤ (y : ℝ)
    rw [div_le_iff₀ hnpos, le_min_iff, le_max_iff, ← hjdef]
    constructor
    · rintro ⟨_, h | h⟩
      · linarith
      · linarith
    · intro h
      exact ⟨hu1, Or.inr (by linarith)⟩
  unfold quantile
  rw [hset, csInf_Ici]

lemma aux_dsc_quantile_zero {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (x : I) :
    quantile (stepLimit π) x 0 = 0 := by
  have hset : {y : I | ((0 : I) : ℝ) ≤ stepLimit π x y} = Set.Ici 0 := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, aux_dsc_stepLimit_eq π hn]
    constructor
    · intro _; exact y.2.1
    · intro _
      exact le_min (by simp) (by simp)
  unfold quantile
  rw [hset, csInf_Ici]


noncomputable def aux_dsc_E {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (j : Fin n) :
    Set (I × I) :=
  {q | aux_dsc_row n hn q.1 = j ∧ ((π j : ℕ) : ℝ) < (n : ℝ) * (q.2 : ℝ) ∧
    (n : ℝ) * (q.2 : ℝ) ≤ ((π j : ℕ) : ℝ) + 1}

lemma aux_dsc_measurableSet_E {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (j : Fin n) :
    MeasurableSet (aux_dsc_E π hn j) := by
  have hm : Measurable (fun q : I × I => (n : ℝ) * (q.2 : ℝ)) :=
    measurable_const.mul (measurable_subtype_coe.comp measurable_snd)
  exact ((aux_dsc_measurable_row hn).comp measurable_fst (measurableSet_singleton j)).inter
    ((measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const))

lemma aux_dsc_measurable_f {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) :
    Measurable (fun p : I × I => (p.1, quantile (stepLimit π) p.1 p.2)) := by
  have hq : Measurable (fun p : I × I => ((quantile (stepLimit π) p.1 p.2 : I) : ℝ)) := by
    have heq : (fun p : I × I => ((quantile (stepLimit π) p.1 p.2 : I) : ℝ)) =
        fun p => if p.2 = 0 then (0 : ℝ)
          else (((π (aux_dsc_row n hn p.1) : ℕ) : ℝ) + p.2) / n := by
      funext p
      split_ifs with h
      · rw [h, aux_dsc_quantile_zero π hn]; rfl
      · exact aux_dsc_quantile_pos π hn p.1 p.2 h
    rw [heq]
    refine Measurable.ite ?_ measurable_const ?_
    · exact measurable_snd (measurableSet_singleton 0)
    · have h1 : Measurable (fun p : I × I => ((π (aux_dsc_row n hn p.1) : ℕ) : ℝ)) :=
        (measurable_of_countable (fun j : Fin n => ((π j : ℕ) : ℝ))).comp
          ((aux_dsc_measurable_row hn).comp measurable_fst)
      exact (h1.add (measurable_subtype_coe.comp measurable_snd)).div_const _
  exact measurable_fst.prodMk hq.subtype_mk

lemma aux_dsc_preimage_E {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (j : Fin n) :
    (fun p : I × I => (p.1, quantile (stepLimit π) p.1 p.2)) ⁻¹' aux_dsc_E π hn j =
      (aux_dsc_row n hn ⁻¹' {j}) ×ˢ {u : I | u ≠ 0} := by
  ext ⟨x, u⟩
  simp only [aux_dsc_E, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_prod,
    Set.mem_singleton_iff]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  by_cases hu : u = 0
  · subst hu
    rw [aux_dsc_quantile_zero π hn]
    simp only [ne_eq, not_true_eq_false, and_false, iff_false]
    rintro ⟨_, h, _⟩
    have : ((0 : I) : ℝ) = 0 := rfl
    rw [this, mul_zero] at h
    exact absurd h (not_lt.mpr (Nat.cast_nonneg _))
  · rw [aux_dsc_quantile_pos π hn x u hu]
    have hu0 : (0 : ℝ) < u := by
      rcases lt_or_eq_of_le u.2.1 with h | h
      · exact h
      · exact absurd (Subtype.ext h.symm) hu
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    constructor
    · rintro ⟨h1, _, _⟩; exact ⟨h1, hu⟩
    · rintro ⟨h1, _⟩
      rw [h1, mul_div_cancel₀ _ hnpos.ne']
      exact ⟨rfl, by linarith, by linarith⟩

lemma aux_dsc_volume_row {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (volume (aux_dsc_row n hn ⁻¹' {j}) : ENNReal) = ENNReal.ofReal (1 / n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hjn : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.2
  rw [unitInterval.volume_apply]
  apply le_antisymm
  · calc volume (Subtype.val '' (aux_dsc_row n hn ⁻¹' {j}))
        ≤ volume (Set.Icc (((j : ℕ) : ℝ) / n) ((((j : ℕ) : ℝ) + 1) / n)) := by
          apply measure_mono
          rintro _ ⟨x, hx, rfl⟩
          obtain ⟨h1, h2⟩ := aux_dsc_mem_of_row_eq hn j x hx
          constructor
          · rw [div_le_iff₀ hnpos]; linarith
          · rw [le_div_iff₀ hnpos]; linarith
      _ = ENNReal.ofReal (1 / n) := by
          rw [Real.volume_Icc]; congr 1; field_simp; ring
  · calc ENNReal.ofReal (1 / n)
        = volume (Set.Ioc (((j : ℕ) : ℝ) / n) ((((j : ℕ) : ℝ) + 1) / n)) := by
          rw [Real.volume_Ioc]; congr 1; field_simp; ring
      _ ≤ _ := by
          apply measure_mono
          intro y hy
          obtain ⟨hy1, hy2⟩ := hy
          rw [div_lt_iff₀ hnpos] at hy1
          rw [le_div_iff₀ hnpos] at hy2
          have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
          have hy0 : 0 ≤ y := by nlinarith
          have hy1' : y ≤ 1 := by nlinarith
          refine ⟨⟨y, hy0, hy1'⟩, ?_, rfl⟩
          show aux_dsc_row n hn ⟨y, hy0, hy1'⟩ = j
          exact aux_dsc_row_eq_of_mem hn j _ (by simp only; linarith) (by simp only; linarith)

lemma aux_dsc_volume_ne_zero : (volume {u : I | u ≠ 0} : ENNReal) = 1 := by
  have : {u : I | u ≠ 0} = ({0} : Set I)ᶜ := by ext; simp
  rw [this, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_univ,
    measure_singleton, tsub_zero]

lemma aux_dsc_mu_E {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (j : Fin n) :
    limitMeasure (stepLimit π) (aux_dsc_E π hn j) = ENNReal.ofReal (1 / n) := by
  unfold limitMeasure
  rw [Measure.map_apply (aux_dsc_measurable_f π hn) (aux_dsc_measurableSet_E π hn j),
    aux_dsc_preimage_E, Measure.volume_eq_prod, Measure.prod_prod, aux_dsc_volume_row,
    aux_dsc_volume_ne_zero, mul_one]

lemma aux_dsc_mu_univ {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) :
    limitMeasure (stepLimit π) Set.univ = 1 := by
  unfold limitMeasure
  rw [Measure.map_apply (aux_dsc_measurable_f π hn) MeasurableSet.univ, Set.preimage_univ,
    measure_univ]


lemma aux_dsc_isProb {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) :
    IsProbabilityMeasure (limitMeasure (stepLimit π)) :=
  ⟨aux_dsc_mu_univ π hn⟩

def aux_dsc_B {n k : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (r : Fin k → Fin n) :
    Set (Fin k → I × I) :=
  Set.univ.pi (fun i => aux_dsc_E π hn (r i))

def aux_dsc_P {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) (r : Fin k → Fin n) :
    Prop :=
  ∃ ρ : Equiv.Perm (Fin k), (∀ i j, i < j → r (ρ i) < r (ρ j)) ∧
    ∀ i j, (π (r (ρ i)) < π (r (ρ j)) ↔ τ i < τ j)

lemma aux_dsc_nu_B {n k : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) (r : Fin k → Fin n) :
    (Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π))) (aux_dsc_B π hn r) =
      ENNReal.ofReal (1 / n) ^ k := by
  have := aux_dsc_isProb π hn
  rw [aux_dsc_B, Measure.pi_pi]
  simp only [aux_dsc_mu_E]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma aux_dsc_measurableSet_B {n k : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n)
    (r : Fin k → Fin n) : MeasurableSet (aux_dsc_B π hn r) :=
  MeasurableSet.univ_pi (fun i => aux_dsc_measurableSet_E π hn (r i))

lemma aux_dsc_disjoint_B {n k : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n)
    (s : Set (Fin k → Fin n)) : s.PairwiseDisjoint (aux_dsc_B π hn) := by
  intro r _ r' _ hrr'
  rw [Function.onFun, Set.disjoint_left]
  intro p hp hp'
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hrr'
  have h1 := (hp i (Set.mem_univ i)).1
  have h2 := (hp' i (Set.mem_univ i)).1
  exact hi (h1.symm.trans h2)

lemma aux_dsc_P_inj {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    {r : Fin k → Fin n} (h : aux_dsc_P τ π r) : Function.Injective r := by
  obtain ⟨ρ, h1, _⟩ := h
  intro a b hab
  have ha : ρ (ρ.symm a) = a := ρ.apply_symm_apply a
  have hb : ρ (ρ.symm b) = b := ρ.apply_symm_apply b
  rcases lt_trichotomy (ρ.symm a) (ρ.symm b) with hlt | heq | hgt
  · have := h1 _ _ hlt; rw [ha, hb, hab] at this; exact absurd this (lt_irrefl _)
  · simpa using heq
  · have := h1 _ _ hgt; rw [ha, hb, hab] at this; exact absurd this (lt_irrefl _)

lemma aux_dsc_mem_pattern_iff {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (hn : 0 < n) {r : Fin k → Fin n} (hr : Function.Injective r) {p : Fin k → I × I}
    (hp : p ∈ aux_dsc_B π hn r) :
    p ∈ patternEvent τ ↔ aux_dsc_P τ π r := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [aux_dsc_B, Set.mem_pi, Set.mem_univ, true_implies, aux_dsc_E,
    Set.mem_ofPred_eq] at hp
  have h1 : ∀ a b, (p a).1 < (p b).1 ↔ r a < r b := by
    intro a b
    constructor
    · intro h
      have hle : r a ≤ r b := by
        rw [← (hp a).1, ← (hp b).1]; exact aux_dsc_row_mono hn h.le
      have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ h
      exact lt_of_le_of_ne hle (fun h' => hne (hr h'))
    · intro h
      by_contra hc
      push Not at hc
      have := aux_dsc_row_mono hn hc
      rw [(hp a).1, (hp b).1] at this
      exact absurd h (not_lt.mpr this)
  have h2 : ∀ a b, (p a).2 < (p b).2 ↔ π (r a) < π (r b) := by
    intro a b
    obtain ⟨_, ha1, ha2⟩ := hp a
    obtain ⟨_, hb1, hb2⟩ := hp b
    constructor
    · intro h
      by_contra hc
      push Not at hc
      rcases lt_or_eq_of_le hc with hlt | heq
      · have hlt' : (π (r b) : ℕ) + 1 ≤ (π (r a) : ℕ) := hlt
        have : ((π (r b) : ℕ) : ℝ) + 1 ≤ ((π (r a) : ℕ) : ℝ) := by exact_mod_cast hlt'
        have h' : ((p a).2 : ℝ) < (p b).2 := h
        have := mul_lt_mul_of_pos_left h' hnpos
        linarith
      · have : a = b := hr (π.injective heq.symm)
        subst this; exact lt_irrefl _ h
    · intro h
      have hlt' : (π (r a) : ℕ) + 1 ≤ (π (r b) : ℕ) := h
      have : ((π (r a) : ℕ) : ℝ) + 1 ≤ ((π (r b) : ℕ) : ℝ) := by exact_mod_cast hlt'
      show ((p a).2 : ℝ) < (p b).2
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc hnpos.le
      linarith
  simp only [patternEvent, Set.mem_ofPred_eq, aux_dsc_P, h1, h2]

open Classical in
lemma aux_dsc_card_R {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun r : Fin k → Fin n => aux_dsc_P τ π r)).card =
      k.factorial * occurrences τ π := by
  classical
  set O := Finset.univ.filter (fun x : Fin k → Fin n =>
    (∀ i j, i < j → x i < x j) ∧ ∀ i j, (π (x i) < π (x j) ↔ τ i < τ j)) with hO
  have hocc : occurrences τ π = O.card := by
    unfold occurrences; rw [hO]
  have himg : Finset.univ.filter (fun r : Fin k → Fin n => aux_dsc_P τ π r) =
      (O ×ˢ (Finset.univ : Finset (Equiv.Perm (Fin k)))).image
        (fun xρ => fun i => xρ.1 (xρ.2.symm i)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, and_true, Prod.exists]
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold aux_dsc_P
    constructor
    · rintro ⟨ρ, h1, h2⟩
      exact ⟨fun i => r (ρ i), ρ, ⟨h1, h2⟩, by funext i; simp⟩
    · rintro ⟨x, ρ, ⟨h1, h2⟩, rfl⟩
      exact ⟨ρ, by simpa using h1, by simpa using h2⟩
  rw [himg, Finset.card_image_of_injOn, Finset.card_product, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, hocc, mul_comm]
  rintro ⟨x, ρ⟩ hx ⟨x', ρ'⟩ hx' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hO, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.coe_univ, Set.mem_univ, and_true] at hx hx'
  simp only at heq
  have hxm : StrictMono x := fun i j hij => hx.1 i j hij
  have hxm' : StrictMono x' := fun i j hij => hx'.1 i j hij
  have hrange : Set.range x = Set.range x' := by
    have h := congrArg Set.range heq
    change Set.range (x ∘ ρ.symm) = Set.range (x' ∘ ρ'.symm) at h
    rwa [ρ.symm.surjective.range_comp, ρ'.symm.surjective.range_comp] at h
  have hxx : x = x' := (hxm.range_inj hxm').mp hrange
  subst hxx
  have hs : ρ.symm = ρ'.symm := Equiv.ext fun i => hxm.injective (congrFun heq i)
  have : ρ = ρ' := by simpa using congrArg Equiv.symm hs
  rw [this]

lemma aux_dsc_card_inj (k n : ℕ) [DecidablePred (fun r : Fin k → Fin n => Function.Injective r)] :
    (Finset.univ.filter (fun r : Fin k → Fin n => Function.Injective r)).card =
      n.descFactorial k := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

lemma aux_dsc_desc_ineq (n : ℕ) :
    ∀ k : ℕ, n * n ^ k ≤ n * n.descFactorial k + k.choose 2 * n ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := aux_dsc_desc_ineq n k
    have hd := Nat.descFactorial_le_pow n k
    have hc : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    rw [Nat.descFactorial_succ, hc, pow_succ]
    rcases le_or_gt k n with hkn | hkn
    · obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
      rw [show k + m - k = m by omega]
      nlinarith [Nat.mul_le_mul_right (k + m) ih, Nat.mul_le_mul_left ((k + m) * k) hd]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hkn] at ih ⊢
      simp only [mul_zero, zero_add] at ih ⊢
      nlinarith [Nat.mul_le_mul_right n ih, Nat.zero_le (k * (n ^ k * n))]

end PermLimits.Existence

open PermLimits.Existence
open unitInterval MeasureTheory

theorem solution {k n : ℕ} (τ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin n))
    (hk : 0 < k) (hkn : k ≤ n) :
    |permDensity τ π - limitDensity τ (stepLimit π)| ≤ (1 / (n : ℝ)) * (Nat.choose k 2 : ℝ) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hμ := aux_dsc_isProb π hn
  set ν := Measure.pi (fun _ : Fin k => limitMeasure (stepLimit π)) with hν
  have hνprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hνreal_B : ∀ r : Fin k → Fin n, ν.real (aux_dsc_B π hn r) = (1 / (n : ℝ)) ^ k := by
    intro r
    rw [measureReal_def, hν, aux_dsc_nu_B, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity)]
  set R := Finset.univ.filter (fun r : Fin k → Fin n => aux_dsc_P τ π r) with hR
  set Inj := Finset.univ.filter (fun r : Fin k → Fin n => Function.Injective r) with hInj
  have hRInj : R ⊆ Inj := by
    intro r hr
    simp only [hR, hInj, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact aux_dsc_P_inj τ π hr
  set T := Inj \ R with hT
  have hcardR : (R.card : ℝ) = k.factorial * occurrences τ π := by
    rw [hR, aux_dsc_card_R]; push_cast; ring
  have hcardInj : Inj.card = n.descFactorial k := aux_dsc_card_inj k n
  have hcardT : T.card + R.card = Inj.card := Finset.card_sdiff_add_card_eq_card hRInj
  have hlow : (R.card : ℝ) * (1 / (n : ℝ)) ^ k ≤ ν.real (patternEvent τ) := by
    have hsub : (⋃ r ∈ R, aux_dsc_B π hn r) ⊆ patternEvent τ := by
      intro p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨r, hr, hpr⟩ := hp
      have hPr : aux_dsc_P τ π r := by simpa [hR] using hr
      exact (aux_dsc_mem_pattern_iff τ π hn (aux_dsc_P_inj τ π hPr) hpr).mpr hPr
    calc (R.card : ℝ) * (1 / (n : ℝ)) ^ k = ∑ r ∈ R, ν.real (aux_dsc_B π hn r) := by
          rw [Finset.sum_congr rfl (fun r _ => hνreal_B r), Finset.sum_const, nsmul_eq_mul]
      _ = ν.real (⋃ r ∈ R, aux_dsc_B π hn r) := by
          rw [measureReal_biUnion_finset (aux_dsc_disjoint_B π hn _)
            (fun r _ => aux_dsc_measurableSet_B π hn r)]
      _ ≤ ν.real (patternEvent τ) := measureReal_mono hsub
  have hup : ν.real (patternEvent τ) + (T.card : ℝ) * (1 / (n : ℝ)) ^ k ≤ 1 := by
    have hdisj : Disjoint (patternEvent τ) (⋃ r ∈ T, aux_dsc_B π hn r) := by
      rw [Set.disjoint_left]
      intro p hpS hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨r, hr, hpr⟩ := hp
      simp only [hT, hR, hInj, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and] at hr
      exact hr.2 ((aux_dsc_mem_pattern_iff τ π hn hr.1 hpr).mp hpS)
    have hmeas : MeasurableSet (⋃ r ∈ T, aux_dsc_B π hn r) :=
      Finset.measurableSet_biUnion T (fun r _ => aux_dsc_measurableSet_B π hn r)
    calc ν.real (patternEvent τ) + (T.card : ℝ) * (1 / (n : ℝ)) ^ k
        = ν.real (patternEvent τ) + ν.real (⋃ r ∈ T, aux_dsc_B π hn r) := by
          rw [measureReal_biUnion_finset (aux_dsc_disjoint_B π hn _)
            (fun r _ => aux_dsc_measurableSet_B π hn r),
            Finset.sum_congr rfl (fun r _ => hνreal_B r), Finset.sum_const, nsmul_eq_mul]
      _ = ν.real (patternEvent τ ∪ ⋃ r ∈ T, aux_dsc_B π hn r) :=
          (measureReal_union hdisj hmeas (measure_ne_top ν _) (measure_ne_top ν _)).symm
      _ ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ
  have htZ : limitDensity τ (stepLimit π) = ν.real (patternEvent τ) := rfl
  have htπ : permDensity τ π = (occurrences τ π : ℝ) / (n.choose k : ℝ) := by
    unfold permDensity; rw [if_pos hkn]
  rw [htZ, htπ]
  set tZ := ν.real (patternEvent τ) with htZdef
  have hCn : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hD : (n.descFactorial k : ℝ) = k.factorial * n.choose k := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n k
  have hDN : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow n k
  have hineq : (n : ℝ) * (n : ℝ) ^ k ≤ n * n.descFactorial k + (k.choose 2 : ℝ) * (n : ℝ) ^ k := by
    exact_mod_cast aux_dsc_desc_ineq n k
  have hRle : (R.card : ℝ) ≤ n.descFactorial k := by
    rw [← hcardInj]; exact_mod_cast Finset.card_le_card hRInj
  have hTR : (T.card : ℝ) + R.card = n.descFactorial k := by
    exact_mod_cast (hcardT.trans hcardInj)
  set c : ℝ := (1 / (n : ℝ)) ^ k with hcdef
  have hcN : c * (n : ℝ) ^ k = 1 := by
    rw [hcdef, div_pow, one_pow, div_mul_cancel₀]; positivity
  have hcpos : 0 < c := by positivity
  set L : ℝ := (occurrences τ π : ℝ) with hL
  set Cn : ℝ := (n.choose k : ℝ) with hCndef
  set D : ℝ := (n.descFactorial k : ℝ) with hDdef
  set F : ℝ := (k.factorial : ℝ) with hFdef
  set x := L / Cn with hx
  have hLx : L = x * Cn := by rw [hx, div_mul_cancel₀]; exact hCn.ne'
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hCn.le
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hCn]
    have : F * L ≤ F * Cn := by rw [← hcardR, ← hD]; exact hRle
    exact le_of_mul_le_mul_left this hF
  set e := D * c with he
  have he0 : 0 ≤ e := mul_nonneg (Nat.cast_nonneg _) hcpos.le
  have he1 : e ≤ 1 := by
    rw [he]; have := mul_le_mul_of_nonneg_right hDN hcpos.le; linarith
  have hlow' : x * e ≤ tZ := by
    have : (R.card : ℝ) * c = x * e := by
      rw [hcardR, he, hD, hLx]; ring
    rw [← this]; exact hlow
  have hup' : tZ ≤ 1 - e + x * e := by
    have hT' : (T.card : ℝ) = D - R.card := by linarith
    have h2 : (R.card : ℝ) * c = x * e := by
      rw [hcardR, he, hD, hLx]; ring
    rw [hT'] at hup
    have : (D - R.card) * c = e - x * e := by rw [sub_mul, h2, he]
    linarith
  have hδ : 1 - e ≤ (1 / (n : ℝ)) * (k.choose 2 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hineq hcpos.le
    have h2 : (n : ℝ) * (1 - e) ≤ (k.choose 2 : ℝ) := by
      have : (n : ℝ) * (n : ℝ) ^ k * c = n := by rw [mul_assoc, mul_comm ((n:ℝ)^k), hcN, mul_one]
      have h3 : ((n : ℝ) * D + (k.choose 2 : ℝ) * (n : ℝ) ^ k) * c =
          n * e + (k.choose 2 : ℝ) := by
        rw [add_mul, he, mul_assoc, mul_assoc, mul_comm ((n:ℝ)^k), hcN, mul_one]
      nlinarith
    rw [one_div_mul_eq_div, le_div_iff₀ hnpos]; linarith
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr he1)]
  · nlinarith [mul_nonneg hx0 (sub_nonneg.mpr he1)]
