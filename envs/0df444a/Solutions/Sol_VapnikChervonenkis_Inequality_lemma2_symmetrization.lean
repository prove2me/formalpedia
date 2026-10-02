-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.lemma2_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:07:00.222661+00:00
-- url     : https://prove2.me/submissions/7b472755-c36c-46ca-b4a0-f0fab8d3d7bb

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

set_option autoImplicit false

lemma vc47_relFreq_bounds {X : Type*} (A : Set X) {l : ℕ} (hl : 1 ≤ l) (x : Fin l → X) :
    0 ≤ VapnikChervonenkis.Shared.relFreq A x ∧ VapnikChervonenkis.Shared.relFreq A x ≤ 1 := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  unfold VapnikChervonenkis.Shared.relFreq
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hlpos]
  have := Finset.card_filter_le (Finset.univ : Finset (Fin l)) (fun i => x i ∈ A)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

open MeasureTheory ProbabilityTheory in
lemma vc47_cheb {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (A : Set X) (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) (l : ℕ)
    (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    (1 / 2 : ENNReal) ≤ (Measure.pi fun _ : Fin l ↦ P)
      {y | |VapnikChervonenkis.Shared.relFreq A y - P.real A| ≤ ε / 2} := by
  classical
  set μ : Measure (Fin l → X) := Measure.pi fun _ : Fin l ↦ P with hμ
  set p : ℝ := P.real A with hp
  have hlε : 2 ≤ (l : ℝ) * ε ^ 2 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).1 hl
    exact this
  have hlpos : (0 : ℝ) < l := by
    by_contra h0
    have h0' := not_lt.1 h0
    nlinarith [sq_nonneg ε, mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) (sq_nonneg ε)]
  set f : X → ℝ := A.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hA
  have hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x; simp only [hf, Set.indicator_apply, Pi.one_apply]; split_ifs <;> norm_num
  have hfL2 : MemLp f 2 P :=
    MemLp.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf01 x).1, (hf01 x).2])
  have hfint : ∫ x, f x ∂P = p := by
    rw [hf, integral_indicator_one hA]
  set N : (Fin l → X) → ℝ := ∑ i, fun y : Fin l → X => f (y i) with hN
  have hNapp : ∀ y, N y = ∑ i, f (y i) := fun y => by simp [hN, Finset.sum_apply]
  have hrf : ∀ y : Fin l → X, VapnikChervonenkis.Shared.relFreq A y = N y / l := by
    intro y
    unfold VapnikChervonenkis.Shared.relFreq
    rw [Finset.card_filter, Nat.cast_sum, hNapp]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : y i ∈ A <;> simp [hf, Set.indicator_apply, h]
  have hNm : Measurable N := by
    have : N = fun y => ∑ i, f (y i) := funext hNapp
    rw [this]; exact Finset.measurable_sum _ (fun i _ => hfm.comp (measurable_pi_apply i))
  have hNL2 : MemLp N 2 μ :=
    MemLp.of_bound hNm.aestronglyMeasurable l (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, hNapp]
      calc |∑ i, f (y i)| ≤ ∑ i, |f (y i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin l, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            rw [abs_le]; constructor <;> linarith [(hf01 (y i)).1, (hf01 (y i)).2]
        _ = l := by simp)
  have hmean : μ[N] = l * p := by
    simp_rw [hNapp]
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · rw [Finset.sum_congr rfl fun i _ =>
        integral_comp_eval (μ := fun _ : Fin l => P) (i := i) hfm.aestronglyMeasurable]
      simp [hfint]
    · exact integrable_comp_eval (μ := fun _ : Fin l => P) (hfL2.integrable one_le_two)
  have hvar : Var[N; μ] ≤ l * (1 / 4) := by
    have hv := variance_sum_pi (μ := fun _ : Fin l => P) (X := fun _ => f) (fun _ => hfL2)
    rw [hN, hv]
    have hv1 : Var[f; P] ≤ 1 / 4 := by
      have := variance_le_sub_mul_sub (μ := P) (a := 0) (b := 1)
        (Filter.Eventually.of_forall hf01) hfm.aemeasurable
      rw [hfint] at this
      nlinarith [sq_nonneg (p - 1 / 2)]
    calc ∑ _i : Fin l, Var[f; P] ≤ ∑ _i : Fin l, (1 / 4 : ℝ) := Finset.sum_le_sum fun _ _ => hv1
      _ = l * (1 / 4) := by simp
  set cc : ℝ := l * ε / 2 with hcc
  have hc : 0 < cc := by positivity
  have hcheb := meas_ge_le_variance_div_sq hNL2 hc
  set G : Set (Fin l → X) :=
    {y | |VapnikChervonenkis.Shared.relFreq A y - p| ≤ ε / 2} with hGdef
  have hsub : Gᶜ ⊆ {ω | cc ≤ |N ω - μ[N]|} := by
    intro y hy
    simp only [hGdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, hrf] at hy ⊢
    have h1 : |N y - μ[N]| = l * |N y / l - p| := by
      rw [hmean, show N y - l * p = l * (N y / l - p) by field_simp, abs_mul,
        abs_of_pos hlpos]
    rw [h1, hcc]
    have := mul_le_mul_of_nonneg_left hy.le hlpos.le
    linarith
  have hbound : ENNReal.ofReal (Var[N; μ] / cc ^ 2) ≤ 1 / 2 := by
    rw [show (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (by positivity)]
    rw [hcc]
    have h2 : (l : ℝ) * (1 / 4) ≤ 1 / 2 * (l * ε / 2) ^ 2 := by
      have : (l : ℝ) * ε ^ 2 ≥ 2 := hlε
      nlinarith [mul_pos hlpos hlpos]
    linarith
  have hG : MeasurableSet G := by
    have : G = {y | |N y / l - p| ≤ ε / 2} := by
      ext y; simp only [hGdef, Set.mem_ofPred_eq, hrf]
    rw [this]
    exact measurableSet_le (continuous_abs.measurable.comp
      ((hNm.div_const _).sub_const _)) measurable_const
  have hcompl : μ Gᶜ ≤ 1 / 2 := (measure_mono hsub).trans (hcheb.trans hbound)
  have htot := measure_add_measure_compl (μ := μ) hG
  rw [measure_univ] at htot
  have h1 : μ G + μ Gᶜ ≤ μ G + 1 / 2 := add_le_add le_rfl hcompl
  rw [htot] at h1
  have h1' : (1 / 2 : ENNReal) + 1 / 2 ≤ μ G + 1 / 2 := by
    rw [ENNReal.add_halves]; exact h1
  exact ENNReal.le_of_add_le_add_right (by simp) h1'

lemma vc47_append_meas {X : Type*} [MeasurableSpace X] (l : ℕ) :
    Measurable (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X)) := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact (measurable_pi_apply i).comp measurable_fst
  | right i =>
    simp only [Fin.append_right]
    exact (measurable_pi_apply i).comp measurable_snd

lemma vc47_rho_eq {X : Type*} (S : Set (Set X)) (l : ℕ) (p : (Fin l → X) × (Fin l → X)) :
    VapnikChervonenkis.Shared.semiSampleDeviation S l (Fin.append p.1 p.2)
      = ⨆ A : S, |VapnikChervonenkis.Shared.relFreq (A : Set X) p.1
          - VapnikChervonenkis.Shared.relFreq (A : Set X) p.2| := by
  unfold VapnikChervonenkis.Shared.semiSampleDeviation
  simp only [Fin.append_left, Fin.append_right]

open MeasureTheory in
lemma vc47_symm {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A) (l : ℕ)
    (hπ : Measurable (VapnikChervonenkis.Shared.maxDeviation S P l))
    (hρ : Measurable (VapnikChervonenkis.Shared.semiSampleDeviation S l))
    {ε : ℝ} (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    Measure.pi (fun _ : Fin l => P) {x | ε < VapnikChervonenkis.Shared.maxDeviation S P l x}
      ≤ 2 * ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P))
        {p | ε / 2 < VapnikChervonenkis.Shared.semiSampleDeviation S l (Fin.append p.1 p.2)} := by
  classical
  have hl1 : 1 ≤ l := by
    have : (0 : ℝ) < l := lt_of_lt_of_le (by positivity) hl
    exact_mod_cast this
  set Q : Measure (Fin l → X) := Measure.pi fun _ : Fin l => P with hQ
  set E : Set (Fin l → X) := {x | ε < VapnikChervonenkis.Shared.maxDeviation S P l x} with hEdef
  set B : Set ((Fin l → X) × (Fin l → X)) :=
    {p | ε / 2 < VapnikChervonenkis.Shared.semiSampleDeviation S l (Fin.append p.1 p.2)}
    with hBdef
  have hE : MeasurableSet E := measurableSet_lt measurable_const hπ
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (hρ.comp (vc47_append_meas l))
  have key : (1 / 2 : ENNReal) * Q E ≤ (Q.prod Q) B := by
    rw [Measure.prod_apply hB]
    refine le_trans (le_of_eq (lintegral_indicator_const hE (1 / 2 : ENNReal)).symm)
      (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ E
    · rw [Set.indicator_apply, if_pos hx]
      have hx' : ε < VapnikChervonenkis.Shared.maxDeviation S P l x := hx
      have hne : Nonempty S := by
        by_contra h
        rw [not_nonempty_iff] at h
        unfold VapnikChervonenkis.Shared.maxDeviation at hx'
        rw [Real.iSup_of_isEmpty] at hx'
        linarith
      unfold VapnikChervonenkis.Shared.maxDeviation at hx'
      obtain ⟨A, hA⟩ := exists_lt_of_lt_ciSup hx'
      refine le_trans (vc47_cheb P (A : Set X) (hS A A.2) hε l hl) (measure_mono ?_)
      intro y hy
      have hy' : |VapnikChervonenkis.Shared.relFreq (A : Set X) y - P.real (A : Set X)| ≤ ε / 2 :=
        hy
      show ε / 2 < VapnikChervonenkis.Shared.semiSampleDeviation S l (Fin.append x y)
      have := vc47_rho_eq S l (x, y)
      simp only at this
      rw [this]
      have hbdd : BddAbove (Set.range fun A : S =>
          |VapnikChervonenkis.Shared.relFreq (A : Set X) x
            - VapnikChervonenkis.Shared.relFreq (A : Set X) y|) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨A', rfl⟩
        have h1 := vc47_relFreq_bounds (A' : Set X) hl1 x
        have h2 := vc47_relFreq_bounds (A' : Set X) hl1 y
        show |_| ≤ 1
        rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have h3 := le_ciSup hbdd A
      have h4 := abs_sub_le (VapnikChervonenkis.Shared.relFreq (A : Set X) x)
        (VapnikChervonenkis.Shared.relFreq (A : Set X) y) (P.real (A : Set X))
      have h5 : |VapnikChervonenkis.Shared.relFreq (A : Set X) x - P.real (A : Set X)|
          ≤ |VapnikChervonenkis.Shared.relFreq (A : Set X) x
            - VapnikChervonenkis.Shared.relFreq (A : Set X) y|
          + |VapnikChervonenkis.Shared.relFreq (A : Set X) y - P.real (A : Set X)| := h4
      linarith
    · rw [Set.indicator_apply, if_neg hx]; exact zero_le
  have : Q E = 2 * ((1 / 2 : ENNReal) * Q E) := by
    rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  rw [this]
  gcongr
open MeasureTheory in
lemma vc9d_append_map {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (l : ℕ) :
    ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P)).map
        (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X))
      = Measure.pi (fun _ : Fin (l + l) => P) := by
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (vc47_append_meas l) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => s (Fin.castAdd l i)) ×ˢ
        Set.univ.pi (fun i => s (Fin.natAdd l i)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h (Fin.castAdd l i); rwa [Fin.append_left] at this
      · have := h (Fin.natAdd l i); rwa [Fin.append_right] at this
    · rintro ⟨h1, h2⟩ j
      induction j using Fin.addCases with
      | left i => rw [Fin.append_left]; exact h1 i
      | right i => rw [Fin.append_right]; exact h2 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

open MeasureTheory Filter Topology VapnikChervonenkis in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    Measure.pi (fun _ : Fin l => P) {x | ε < Shared.maxDeviation S P l x}
      ≤ 2 * Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} := by
  refine (vc47_symm P S hS l (hπ l) (hρ l) hε hl).trans ?_
  gcongr
  rw [← vc9d_append_map P l,
    Measure.map_apply (vc47_append_meas l) (measurableSet_le measurable_const (hρ l))]
  refine measure_mono fun p hp => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hp ⊢
  exact le_of_lt hp
