-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.theorem4_entropy_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T19:56:48.416985+00:00
-- url     : https://prove2.me/submissions/734be895-fc9d-480a-b607-c177a7dcba3d

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_deviation
import Definitions.Def_VapnikChervonenkis_Entropy_entropy

set_option autoImplicit false

/- Complete checked body: AttributedCore -/
section

set_option autoImplicit false

/- Complete attributed source: Sol_VapnikChervonenkis_Entropy_lemma2_symmetrization.lean -/
section
-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.lemma2_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:04:54.016751+00:00
-- url     : https://prove2.me/submissions/6ac1d188-51b4-4dae-9177-a4d1746a32d9


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
    by_cases h : y i ∈ A <;> simp [hf, h]
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
theorem VCEntropySource.symmetrization {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    Measure.pi (fun _ : Fin l => P) {x | ε < Shared.maxDeviation S P l x}
      ≤ 2 * Measure.pi (fun _ : Fin (l + l) => P)
          {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} := by
  refine (vc47_symm P S hS l (hπ l) (hρ l) hε hl).trans ?_
  gcongr
  rw [← vc9d_append_map P l,
    Measure.map_apply (vc47_append_meas l) (measurableSet_le measurable_const (hρ l))]
  refine measure_mono fun p hp => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hp ⊢
  exact le_of_lt hp

end

/- Complete attributed source: Sol_VapnikChervonenkis_Entropy_lemma3_entropy_rate_limit.lean -/
section
-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.lemma3_entropy_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:58:19.259489+00:00
-- url     : https://prove2.me/submissions/315ea97a-3d70-40cd-8baa-0fecdeb91a01


open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

lemma aux_e3l_idx_le {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    Shared.index S x ≤ 2 ^ n := by
  unfold Shared.index
  exact (Finset.card_le_univ _).trans (by simp)

lemma aux_e3l_logb_nonneg {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    0 ≤ Real.logb 2 (Shared.index S x : ℝ) := by
  rcases Nat.eq_zero_or_pos (Shared.index S x) with h | h
  · simp [h]
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

lemma aux_e3l_logb_le {X : Type*} (S : Set (Set X)) {n : ℕ} (x : Fin n → X) :
    Real.logb 2 (Shared.index S x : ℝ) ≤ n := by
  rcases Nat.eq_zero_or_pos (Shared.index S x) with h | h
  · simp [h]
  · calc Real.logb 2 (Shared.index S x : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ n) := by
          apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h)
          exact_mod_cast aux_e3l_idx_le S x
      _ = n := by simp [Real.logb_pow]

lemma aux_e3l_idx_mul {X : Type*} (S : Set (Set X)) {l m : ℕ} (z : Fin (l + m) → X) :
    Shared.index S z ≤ Shared.index S (fun i : Fin l => z (Fin.castAdd m i)) *
      Shared.index S (fun j : Fin m => z (Fin.natAdd l j)) := by
  classical
  unfold Shared.index
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun t : Finset (Fin (l + m)) =>
    (Finset.univ.filter (fun i : Fin l => Fin.castAdd m i ∈ t),
      Finset.univ.filter (fun j : Fin m => Fin.natAdd l j ∈ t)))
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    obtain ⟨A, hA, hAt⟩ := ht
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq]
    refine ⟨⟨A, hA, fun i => ?_⟩, ⟨A, hA, fun j => ?_⟩⟩
    · simp [hAt]
    · simp [hAt]
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · have := congrArg (fun s => i ∈ s) h1
      simpa using this
    · have := congrArg (fun s => j ∈ s) h2
      simpa using this

lemma aux_e3l_logb_sub {X : Type*} (S : Set (Set X)) {l m : ℕ} (z : Fin (l + m) → X) :
    Real.logb 2 (Shared.index S z : ℝ) ≤
      Real.logb 2 (Shared.index S (fun i : Fin l => z (Fin.castAdd m i)) : ℝ) +
      Real.logb 2 (Shared.index S (fun j : Fin m => z (Fin.natAdd l j)) : ℝ) := by
  have ha := aux_e3l_logb_nonneg S (fun i : Fin l => z (Fin.castAdd m i))
  have hb := aux_e3l_logb_nonneg S (fun j : Fin m => z (Fin.natAdd l j))
  have hmul := aux_e3l_idx_mul S z
  rcases Nat.eq_zero_or_pos (Shared.index S z) with h | h
  · simp only [h, Nat.cast_zero, Real.logb_zero]; linarith
  · have hpa : 0 < Shared.index S (fun i : Fin l => z (Fin.castAdd m i)) := by
      rcases Nat.eq_zero_or_pos (Shared.index S (fun i : Fin l => z (Fin.castAdd m i))) with h' | h'
      · rw [h', zero_mul] at hmul; omega
      · exact h'
    have hpb : 0 < Shared.index S (fun j : Fin m => z (Fin.natAdd l j)) := by
      rcases Nat.eq_zero_or_pos (Shared.index S (fun j : Fin m => z (Fin.natAdd l j))) with h' | h'
      · rw [h', mul_zero] at hmul; omega
      · exact h'
    rw [← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h)
    exact_mod_cast hmul

lemma aux_e3l_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (l m : ℕ) :
    MeasurePreserving (fun p : (Fin l → X) × (Fin m → X) => (Fin.append p.1 p.2 : Fin (l + m) → X))
      ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin m => P))
      (Measure.pi fun _ : Fin (l + m) => P) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin l ⊕ Fin m => X)
    (fun _ : Fin l ⊕ Fin m => P)
  have h2 := measurePreserving_piCongrLeft (α := fun _ : Fin (l + m) => X)
    (fun _ : Fin (l + m) => P) finSumFinEquiv
  have := h2.comp h1
  convert this using 1
  funext p
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [Fin.append_left, Function.comp_apply]
    show p.1 i = (Equiv.piCongrLeft (fun _ => X) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi fun _ => X).symm p) (finSumFinEquiv (Sum.inl i))
    rw [Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [Fin.append_right, Function.comp_apply]
    show p.2 j = (Equiv.piCongrLeft (fun _ => X) finSumFinEquiv)
      ((Equiv.sumPiEquivProdPi fun _ => X).symm p) (finSumFinEquiv (Sum.inr j))
    rw [Equiv.piCongrLeft_apply_apply]
    rfl

lemma aux_e3l_meas {X : Type*} [MeasurableSpace X] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (n : ℕ) :
    Measurable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ)) :=
  (measurable_from_nat (f := fun k : ℕ => Real.logb 2 (k : ℝ))).comp (hΔ n)

lemma aux_e3l_bounds {X : Type*} [MeasurableSpace X] (S : Set (Set X)) (P : Measure X)
    [IsProbabilityMeasure P]
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (n : ℕ) :
    0 ≤ entropy S P n ∧ entropy S P n ≤ n := by
  unfold entropy
  have hint : Integrable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ))
      (Measure.pi fun _ : Fin n => P) := by
    refine Integrable.of_bound (aux_e3l_meas S hΔ n).aestronglyMeasurable n
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S x)]
    exact aux_e3l_logb_le S x
  refine ⟨integral_nonneg fun x => aux_e3l_logb_nonneg S x, ?_⟩
  calc ∫ x, Real.logb 2 (Shared.index S x : ℝ) ∂(Measure.pi fun _ : Fin n => P)
      ≤ ∫ _x, (n : ℝ) ∂(Measure.pi fun _ : Fin n => P) :=
        integral_mono hint (integrable_const _) fun x => aux_e3l_logb_le S x
    _ = n := by simp

lemma aux_e3l_subadd {X : Type*} [MeasurableSpace X] (S : Set (Set X)) (P : Measure X)
    [IsProbabilityMeasure P]
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) (l m : ℕ) :
    entropy S P (l + m) ≤ entropy S P l + entropy S P m := by
  unfold entropy
  have hmp := aux_e3l_mp P l m
  set μ := (Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin m => P) with hμ
  have hint : ∀ n : ℕ, Integrable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ))
      (Measure.pi fun _ : Fin n => P) := by
    intro n
    refine Integrable.of_bound (aux_e3l_meas S hΔ n).aestronglyMeasurable n
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S x)]
    exact aux_e3l_logb_le S x
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact (aux_e3l_meas S hΔ (l + m)).aestronglyMeasurable)]
  have hint1 : Integrable (fun p : (Fin l → X) × (Fin m → X) =>
      Real.logb 2 (Shared.index S p.1 : ℝ)) μ := by
    refine Integrable.of_bound ((aux_e3l_meas S hΔ l).comp measurable_fst).aestronglyMeasurable l
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S _)]
    exact aux_e3l_logb_le S _
  have hint2 : Integrable (fun p : (Fin l → X) × (Fin m → X) =>
      Real.logb 2 (Shared.index S p.2 : ℝ)) μ := by
    refine Integrable.of_bound ((aux_e3l_meas S hΔ m).comp measurable_snd).aestronglyMeasurable m
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S _)]
    exact aux_e3l_logb_le S _
  have hint3 : Integrable (fun p : (Fin l → X) × (Fin m → X) =>
      Real.logb 2 (Shared.index S (Fin.append p.1 p.2 : Fin (l + m) → X) : ℝ)) μ := by
    refine Integrable.of_bound ((aux_e3l_meas S hΔ (l + m)).comp
      hmp.measurable).aestronglyMeasurable (l + m : ℕ) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S _)]
    exact aux_e3l_logb_le S _
  calc ∫ p, Real.logb 2 (Shared.index S (Fin.append p.1 p.2 : Fin (l + m) → X) : ℝ) ∂μ
      ≤ ∫ p, (Real.logb 2 (Shared.index S p.1 : ℝ) + Real.logb 2 (Shared.index S p.2 : ℝ)) ∂μ := by
        refine integral_mono hint3 (hint1.add hint2) fun p => ?_
        have := aux_e3l_logb_sub S (Fin.append p.1 p.2 : Fin (l + m) → X)
        simpa only [Fin.append_left, Fin.append_right] using this
    _ = ∫ p, Real.logb 2 (Shared.index S p.1 : ℝ) ∂μ +
          ∫ p, Real.logb 2 (Shared.index S p.2 : ℝ) ∂μ := integral_add hint1 hint2
    _ = _ := by
        rw [hμ, integral_fun_fst (fun x : Fin l → X => Real.logb 2 (Shared.index S x : ℝ)),
          integral_fun_snd (fun x : Fin m → X => Real.logb 2 (Shared.index S x : ℝ))]
        simp

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem VCEntropySource.entropy_limit {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 c) := by
  have hsub : Subadditive (fun l : ℕ => entropy S P l) := fun a b => aux_e3l_subadd S P hΔ a b
  have hdiv : ∀ n : ℕ, 0 ≤ entropy S P n / (n : ℝ) ∧ entropy S P n / (n : ℝ) ≤ 1 := by
    intro n
    obtain ⟨h0, h1⟩ := aux_e3l_bounds S P hΔ n
    refine ⟨div_nonneg h0 (Nat.cast_nonneg n), ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · rw [div_le_one (by exact_mod_cast hn)]; exact h1
  have hbdd : BddBelow (Set.range fun n : ℕ => entropy S P n / (n : ℝ)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hdiv n).1⟩
  have ht := hsub.tendsto_lim hbdd
  exact ⟨hsub.lim, ge_of_tendsto' ht fun n => (hdiv n).1, le_of_tendsto' ht fun n => (hdiv n).2, ht⟩

end

/- Complete attributed source: Sol_VapnikChervonenkis_Inequality_permutation_bound.lean -/
section
-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.permutation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:41:08.745385+00:00
-- url     : https://prove2.me/submissions/64182871-7a36-4788-ae1e-02e052bdc7d8


set_option autoImplicit false

open Finset in
lemma cde_hoeff_count {l : ℕ} (hl : 1 ≤ l) (c : Fin l → ℝ) (hc : ∀ i, |c i| ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ)
      ≤ (2 : ℝ) ^ l * Real.exp (-(t ^ 2 / (2 * l))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  set lam : ℝ := t / l with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht hlpos.le
  have hmark : ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ) * Real.exp (lam * t)
      ≤ ∑ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases h : t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i
    · simp only [h, if_true, Nat.cast_one, one_mul]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hlam0)
    · simp only [h, if_false, Nat.cast_zero, zero_mul]
      exact (Real.exp_pos _).le
  have hprod : ∑ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i)
      = ∏ i : Fin l, (Real.exp (lam * c i) + Real.exp (-(lam * c i))) := by
    have h1 : ∀ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i)
        = ∏ i : Fin l, Real.exp (lam * ((if s i then (1 : ℝ) else -1) * c i)) := by
      intro s
      rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [h1]
    have := Finset.prod_univ_sum (fun _ : Fin l => (Finset.univ : Finset Bool))
      (fun i b => Real.exp (lam * ((if b then (1 : ℝ) else -1) * c i)))
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg]
  have hfac : ∀ i : Fin l, Real.exp (lam * c i) + Real.exp (-(lam * c i))
      ≤ 2 * Real.exp (lam ^ 2 / 2) := by
    intro i
    have h1 := Real.cosh_le_exp_half_sq (lam * c i)
    rw [Real.cosh_eq] at h1
    have h2 : (lam * c i) ^ 2 ≤ lam ^ 2 := by
      have : |lam * c i| ≤ lam := by
        rw [abs_mul, abs_of_nonneg hlam0]
        calc lam * |c i| ≤ lam * 1 := mul_le_mul_of_nonneg_left (hc i) hlam0
          _ = lam := mul_one _
      have h3 := sq_le_sq' (by linarith [abs_nonneg (lam * c i), neg_abs_le (lam * c i)] : -lam ≤ lam * c i)
        (le_trans (le_abs_self _) this)
      exact h3
    have h4 : Real.exp ((lam * c i) ^ 2 / 2) ≤ Real.exp (lam ^ 2 / 2) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  have hprod2 : ∏ i : Fin l, (Real.exp (lam * c i) + Real.exp (-(lam * c i)))
      ≤ (2 * Real.exp (lam ^ 2 / 2)) ^ l := by
    calc _ ≤ ∏ _i : Fin l, (2 * Real.exp (lam ^ 2 / 2)) :=
          Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hfac i)
      _ = _ := by simp
  have hexp : Real.exp (lam * t) * Real.exp (-(t ^ 2 / (2 * l))) = Real.exp (lam ^ 2 / 2 * l) := by
    rw [← Real.exp_add]
    congr 1
    rw [hlam]
    field_simp
    ring
  have hpow : (2 * Real.exp (lam ^ 2 / 2)) ^ l = 2 ^ l * Real.exp (lam ^ 2 / 2 * l) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hcount : ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ) * Real.exp (lam * t)
      ≤ 2 ^ l * Real.exp (lam ^ 2 / 2 * l) := by
    rw [← hpow]; rw [hprod] at hmark; exact hmark.trans hprod2
  rw [← hexp] at hcount
  have hpos : 0 < Real.exp (lam * t) := Real.exp_pos _
  have := hcount
  rw [show (2 : ℝ) ^ l * (Real.exp (lam * t) * Real.exp (-(t ^ 2 / (2 * l))))
      = (2 ^ l * Real.exp (-(t ^ 2 / (2 * l)))) * Real.exp (lam * t) by ring] at this
  exact le_of_mul_le_mul_right this hpos


/-- Swap the two halves at the positions where `τ` is `true`. -/
def cdeSwS (l : ℕ) (τ : Fin l → Bool) : Fin l ⊕ Fin l → Fin l ⊕ Fin l
  | Sum.inl i => if τ i then Sum.inr i else Sum.inl i
  | Sum.inr i => if τ i then Sum.inl i else Sum.inr i

lemma cdeSwS_inv (l : ℕ) (τ : Fin l → Bool) : Function.Involutive (cdeSwS l τ) := by
  intro a
  cases a with
  | inl i => by_cases h : τ i <;> simp [cdeSwS, h]
  | inr i => by_cases h : τ i <;> simp [cdeSwS, h]

def cdeSw (l : ℕ) (τ : Fin l → Bool) : Equiv.Perm (Fin (l + l)) :=
  (finSumFinEquiv.symm.trans (Function.Involutive.toPerm _ (cdeSwS_inv l τ))).trans finSumFinEquiv

lemma cdeSw_castAdd (l : ℕ) (τ : Fin l → Bool) (i : Fin l) :
    cdeSw l τ (Fin.castAdd l i) = if τ i then Fin.natAdd l i else Fin.castAdd l i := by
  by_cases h : τ i <;> simp [cdeSw, cdeSwS, h]

lemma cdeSw_natAdd (l : ℕ) (τ : Fin l → Bool) (i : Fin l) :
    cdeSw l τ (Fin.natAdd l i) = if τ i then Fin.castAdd l i else Fin.natAdd l i := by
  simp only [cdeSw, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Function.Involutive.coe_toPerm, cdeSwS]
  by_cases h : τ i <;> simp only [h, Bool.false_eq_true, ↓reduceIte,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

open VapnikChervonenkis.Shared in
lemma cde_sup_attained {X : Type*} (S : Set (Set X)) (l : ℕ) (z : Fin (l + l) → X) {r : ℝ}
    (hr : 0 < r) (h : r ≤ semiSampleDeviation S l z) :
    ∃ A ∈ S, r ≤ |relFreq A (fun i : Fin l => z (Fin.castAdd l i))
      - relFreq A (fun i : Fin l => z (Fin.natAdd l i))| := by
  classical
  unfold semiSampleDeviation at h
  set f : S → ℝ := fun A => |relFreq (A : Set X) (fun i : Fin l => z (Fin.castAdd l i))
      - relFreq (A : Set X) (fun i : Fin l => z (Fin.natAdd l i))| with hf
  by_cases hne : Nonempty S
  · set F : Finset (Fin (l + l)) → ℝ := fun t =>
      |((Finset.univ.filter (fun i : Fin l => Fin.castAdd l i ∈ t)).card : ℝ) / l
        - ((Finset.univ.filter (fun i : Fin l => Fin.natAdd l i ∈ t)).card : ℝ) / l| with hF
    have hfF : ∀ A : S, f A = F (Finset.univ.filter (fun j => z j ∈ (A : Set X))) := by
      intro A
      simp only [hf, hF, relFreq, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfin : (Set.range f).Finite := by
      refine (Set.finite_range F).subset ?_
      rintro _ ⟨A, rfl⟩
      exact ⟨_, (hfF A).symm⟩
    have hmem := Set.Nonempty.csSup_mem (Set.range_nonempty f) hfin
    obtain ⟨A, hA⟩ := hmem
    refine ⟨A, A.2, ?_⟩
    have : r ≤ f A := by rw [hA]; exact h
    exact this
  · rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at h
    linarith

open VapnikChervonenkis.Shared in
lemma cde_count {X : Type*} (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l) {ε : ℝ} (hε : 0 < ε)
    (y : Fin (l + l) → X) :
    ((Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ cdeSw l τ)).card : ℝ)
      ≤ (index S y : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl1
  set T : Finset (Finset (Fin (l + l))) :=
    Finset.univ.filter (fun t : Finset (Fin (l + l)) => ∃ A ∈ S, ∀ i, i ∈ t ↔ y i ∈ A) with hT
  have hTcard : T.card = index S y := by
    unfold index
    rfl
  set c : Finset (Fin (l + l)) → Fin l → ℝ := fun t i =>
    (if Fin.castAdd l i ∈ t then (1 : ℝ) else 0) - (if Fin.natAdd l i ∈ t then (1 : ℝ) else 0)
    with hc
  have hc1 : ∀ t i, |c t i| ≤ 1 := by
    intro t i
    simp only [hc]
    rw [abs_le]
    by_cases h1 : Fin.castAdd l i ∈ t <;> by_cases h2 : Fin.natAdd l i ∈ t <;>
      simp only [h1, h2, ↓reduceIte] <;> norm_num
  set Bad : Finset (Fin (l + l)) → Finset (Fin l → Bool) := fun t =>
    Finset.univ.filter (fun σ : Fin l → Bool =>
      (l : ℝ) * (ε / 2) ≤ |∑ i, (if σ i then (1 : ℝ) else -1) * c t i|) with hBad
  have hBadcard : ∀ t, ((Bad t).card : ℝ) ≤ 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) := by
    intro t
    have hexp : (l * (ε / 2)) ^ 2 / (2 * (l : ℝ)) = ε ^ 2 * l / 8 := by
      field_simp; ring
    have hnn : 0 ≤ (l : ℝ) * (ε / 2) := by positivity
    have h1 := cde_hoeff_count hl1 (c t) (hc1 t) hnn
    have h2 := cde_hoeff_count hl1 (fun i => - c t i)
      (fun i => by simpa [abs_neg] using hc1 t i) hnn
    beta_reduce at h2
    rw [hexp] at h1 h2
    have hsub : Bad t ⊆
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c t i) ∪
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * (- c t i)) := by
      intro σ hσ
      simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hσ ⊢
      have hneg : ∑ i, (if σ i then (1 : ℝ) else -1) * (- c t i)
          = - ∑ i, (if σ i then (1 : ℝ) else -1) * c t i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hneg]
      rcases le_abs'.1 hσ with h | h
      · right; linarith
      · left; linarith
    have := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    push_cast at this
    linarith
  have hsubset : (Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ cdeSw l τ)) ⊆ T.biUnion Bad := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨A, hAS, hA⟩ := cde_sup_attained S l (y ∘ cdeSw l σ) (by positivity) hσ
    refine Finset.mem_biUnion.2 ⟨Finset.univ.filter (fun j : Fin (l + l) => y j ∈ A), ?_, ?_⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨A, hAS, fun i => by simp⟩
    · simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
      set tA : Finset (Fin (l + l)) := Finset.univ.filter (fun j : Fin (l + l) => y j ∈ A)
        with htA
      have hci : ∀ i : Fin l, c tA i
          = (if y (Fin.castAdd l i) ∈ A then (1 : ℝ) else 0)
            - (if y (Fin.natAdd l i) ∈ A then (1 : ℝ) else 0) := by
        intro i
        simp only [hc, htA, Finset.mem_filter, Finset.mem_univ, true_and]
      have hdiff : relFreq A (fun i : Fin l => (y ∘ cdeSw l σ) (Fin.castAdd l i))
          - relFreq A (fun i : Fin l => (y ∘ cdeSw l σ) (Fin.natAdd l i))
          = - (∑ i, (if σ i then (1 : ℝ) else -1) * c tA i) / l := by
        unfold relFreq
        rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← sub_div,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hci i]
        simp only [Function.comp_apply, cdeSw_castAdd, cdeSw_natAdd]
        by_cases h : σ i <;> by_cases h1 : y (Fin.castAdd l i) ∈ A <;>
          by_cases h2 : y (Fin.natAdd l i) ∈ A <;>
          simp only [h, h1, h2, Bool.false_eq_true, ↓reduceIte] <;> norm_num
      rw [hdiff, abs_div, abs_neg, abs_of_pos hlpos, le_div_iff₀ hlpos] at hA
      linarith
  have hcard1 := Finset.card_le_card hsubset
  have hcard2 := hcard1.trans Finset.card_biUnion_le
  have hcard3 : ((Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ cdeSw l τ)).card : ℝ)
      ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := by
    exact_mod_cast hcard2
  calc _ ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := hcard3
    _ ≤ ∑ _t ∈ T, 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) :=
        Finset.sum_le_sum fun t _ => hBadcard t
    _ = (T.card : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hTcard]

open VapnikChervonenkis.Shared in
lemma cde_index_perm {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X)
    (σ : Equiv.Perm (Fin r)) : index S (x ∘ σ) = index S x := by
  classical
  unfold index
  refine Finset.card_equiv (Equiv.finsetCongr σ) ?_
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, fun j => ?_⟩
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv, ht]
    simp
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, fun i => ?_⟩
    have := ht (σ i)
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv] at this
    simpa using this

open VapnikChervonenkis in
theorem VCEntropySource.permutation_upper {X : Type*} (S : Set (Set X)) (ε : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hε : 0 < ε) (x : Fin (l + l) → X) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
        ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
      ≤ 2 * (Shared.index S x : ℝ) * Real.exp (-(ε ^ 2 * l / 8)) := by
  classical
  set K : ℝ := 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) with hK
  set Bad : Equiv.Perm (Fin (l + l)) → Prop :=
    fun σ => ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ) with hBad
  set P := Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) => Bad σ) with hP
  have hshift : ∀ τ : Fin l → Bool,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) => Bad (σ * cdeSw l τ))).card
        = P.card := by
    intro τ
    refine Finset.card_equiv (Equiv.mulRight (cdeSw l τ)) ?_
    intro σ
    simp [hP]
  have hcomp : ∀ (σ : Equiv.Perm (Fin (l + l))) (τ : Fin l → Bool),
      x ∘ ⇑(σ * cdeSw l τ) = (x ∘ ⇑σ) ∘ ⇑(cdeSw l τ) := by
    intro σ τ
    rw [Equiv.Perm.coe_mul]
    rfl
  have hsum : (2 : ℝ) ^ l * (P.card : ℝ)
      = ∑ σ : Equiv.Perm (Fin (l + l)),
          ((Finset.univ.filter fun τ : Fin l → Bool =>
            ε / 2 ≤ Shared.semiSampleDeviation S l ((x ∘ ⇑σ) ∘ cdeSw l τ)).card : ℝ) := by
    have h1 : (2 : ℝ) ^ l * (P.card : ℝ) = ∑ τ : Fin l → Bool,
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) => Bad (σ * cdeSw l τ))).card : ℝ) := by
      simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [h1]
    simp only [Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [hBad, hcomp]
  have hbound : (2 : ℝ) ^ l * (P.card : ℝ)
      ≤ ((l + l).factorial : ℝ) * ((Shared.index S x : ℝ) * K) := by
    rw [hsum]
    calc _ ≤ ∑ _σ : Equiv.Perm (Fin (l + l)), (Shared.index S x : ℝ) * K := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have := cde_count S l hl hε (x ∘ ⇑σ)
          rw [cde_index_perm] at this
          exact this
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  have hfac : (0 : ℝ) < ((l + l).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2l : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  rw [div_le_iff₀ hfac]
  have : (P.card : ℝ) ≤ ((l + l).factorial : ℝ) * (Shared.index S x : ℝ)
      * (2 * Real.exp (-(ε ^ 2 * l / 8))) := by
    have h3 : (2 : ℝ) ^ l * (P.card : ℝ) ≤ (2 : ℝ) ^ l * (((l + l).factorial : ℝ)
        * (Shared.index S x : ℝ) * (2 * Real.exp (-(ε ^ 2 * l / 8)))) := by
      calc _ ≤ _ := hbound
        _ = _ := by rw [hK]; ring
    exact le_of_mul_le_mul_left h3 h2l
  calc _ ≤ _ := this
    _ = _ := by ring

end

/- Complete attributed source: Sol_VapnikChervonenkis_Inequality_eq11_permutation_average.lean -/
section
-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.eq11_permutation_average
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:15:04.009837+00:00
-- url     : https://prove2.me/submissions/1693bcd1-a457-47ce-a610-29d9436ea7dd


open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

theorem aux_eq11_mp {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → X => x ∘ σ) (Measure.pi fun _ => P)
      (Measure.pi fun _ => P) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin n => P) σ.symm
  convert h using 1
  ext x i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

theorem aux_eq11_main {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (n : ℕ) (p : (Fin n → X) → Prop) [DecidablePred p] (hA : MeasurableSet {x | p x}) :
    Measure.pi (fun _ : Fin n => P) {x | p x}
      = ENNReal.ofReal (∫ x, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            p (x ∘ σ))).card : ℝ) / (n.factorial : ℝ)
          ∂(Measure.pi (fun _ : Fin n => P))) := by
  set μ := Measure.pi (fun _ : Fin n => P) with hμ
  set A : Set (Fin n → X) := {x | p x} with hAdef
  have hcard : ∀ x : Fin n → X, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      p (x ∘ σ))).card : ℝ) = ∑ σ : Equiv.Perm (Fin n),
        ((fun x : Fin n → X => x ∘ σ) ⁻¹' A).indicator (1 : (Fin n → X) → ℝ) x := by
    intro x
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    by_cases h : p (x ∘ σ)
    · simp [h, Set.indicator_of_mem (show x ∈ (fun x : Fin n → X => x ∘ σ) ⁻¹' A from h)]
    · simp [h, Set.indicator_of_notMem (show x ∉ (fun x : Fin n → X => x ∘ σ) ⁻¹' A from h)]
  have hmeas : ∀ σ : Equiv.Perm (Fin n), MeasurableSet ((fun x : Fin n → X => x ∘ σ) ⁻¹' A) :=
    fun σ => (aux_eq11_mp P n σ).measurable hA
  have hint : ∀ σ : Equiv.Perm (Fin n),
      ∫ x, ((fun x : Fin n → X => x ∘ σ) ⁻¹' A).indicator (1 : (Fin n → X) → ℝ) x ∂μ = μ.real A := by
    intro σ
    rw [integral_indicator_one (hmeas σ)]
    simp only [Measure.real]
    rw [(aux_eq11_mp P n σ).measure_preimage hA.nullMeasurableSet]
  simp_rw [hcard]
  rw [integral_div, integral_finsetSum]
  · simp_rw [hint]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have hf : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    rw [mul_div_cancel_left₀ _ hf, ofReal_measureReal]
  · intro σ _
    exact (integrable_const (1 : ℝ)).indicator (hmeas σ)

end VapnikChervonenkis.Inequality

open VapnikChervonenkis.Inequality
open MeasureTheory Filter Topology

theorem VCEntropySource.permutation_average {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (VapnikChervonenkis.Shared.semiSampleDeviation S l)) (ε : ℝ) (l : ℕ) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l x}
      = ENNReal.ofReal (∫ x, ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
            ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
          ∂(Measure.pi (fun _ : Fin (l + l) => P))) :=
  aux_eq11_main P (l + l) (fun x => ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l x)
    (hρ l measurableSet_Ici)

end

/- Complete attributed source: Sol_VapnikChervonenkis_Entropy_necessity_step1.lean -/
section
-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.necessity_step1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:24:25.768122+00:00
-- url     : https://prove2.me/submissions/46b0a596-879b-4880-9c2b-435c334803a9


open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

lemma aux_ns1_relFreq_nonneg {X : Type*} (A : Set X) {l : ℕ} (x : Fin l → X) :
    0 ≤ Shared.relFreq A x := by
  unfold Shared.relFreq; positivity

lemma aux_ns1_relFreq_le_one {X : Type*} (A : Set X) {l : ℕ} (x : Fin l → X) :
    Shared.relFreq A x ≤ 1 := by
  unfold Shared.relFreq
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h; simp
  · apply div_le_one_of_le₀ _ (by positivity)
    exact_mod_cast (Finset.card_le_univ _).trans (by simp)

lemma aux_ns1_abs_le {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (A : Set X) {l : ℕ} (x : Fin l → X) : |Shared.relFreq A x - P.real A| ≤ 1 := by
  have h1 := aux_ns1_relFreq_nonneg A x
  have h2 := aux_ns1_relFreq_le_one A x
  have h3 : 0 ≤ P.real A := measureReal_nonneg
  have h4 : P.real A ≤ 1 := measureReal_le_one
  rw [abs_le]; constructor <;> linarith

lemma aux_ns1_split {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (ε : ℝ) (hε : 0 < ε) (l : ℕ) (x : Fin (l + l) → X)
    (hx : 2 * ε < Shared.semiSampleDeviation S l x) :
    ε < Shared.maxDeviation S P l (fun i => x (Fin.castAdd l i)) ∨
    ε < Shared.maxDeviation S P l (fun i => x (Fin.natAdd l i)) := by
  unfold Shared.semiSampleDeviation at hx
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [Real.iSup_of_isEmpty] at hx; linarith
  obtain ⟨A, hA⟩ := exists_lt_of_lt_ciSup hx
  have hbdd : ∀ y : Fin l → X, BddAbove (Set.range fun A : S =>
      |Shared.relFreq (A : Set X) y - P.real (A : Set X)|) := by
    intro y
    refine ⟨1, ?_⟩
    rintro _ ⟨B, rfl⟩
    exact aux_ns1_abs_le P _ y
  have h1 := le_ciSup (hbdd (fun i => x (Fin.castAdd l i))) A
  have h2 := le_ciSup (hbdd (fun i => x (Fin.natAdd l i))) A
  unfold Shared.maxDeviation
  set a := Shared.relFreq (A : Set X) (fun i => x (Fin.castAdd l i))
  set b := Shared.relFreq (A : Set X) (fun i => x (Fin.natAdd l i))
  set p := P.real (A : Set X)
  have htri : |a - b| ≤ |a - p| + |b - p| := by
    have := abs_sub_le a p b
    rw [abs_sub_comm p b] at this
    exact this
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  linarith

theorem aux_ns1_mp (l : ℕ) {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] :
    MeasurePreserving (fun x : Fin (l + l) → X =>
        ((fun i => x (Fin.castAdd l i)), (fun i => x (Fin.natAdd l i))))
      (Measure.pi (fun _ : Fin (l + l) => P))
      ((Measure.pi (fun _ : Fin l => P)).prod (Measure.pi (fun _ : Fin l => P))) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (l + l) => P) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin l ⊕ Fin l => P)
  have := h2.comp h1
  convert this using 1
  funext x
  ext i
  · simp [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft]
  · simp [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft]

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem VCEntropySource.necessity_step {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l)) (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    (1 - (Measure.pi (fun _ : Fin l => P)).real {x | ε < Shared.maxDeviation S P l x}) ^ 2
      ≤ 1 - (Measure.pi (fun _ : Fin (l + l) => P)).real
          {x | 2 * ε < Shared.semiSampleDeviation S l x} := by
  set μl := Measure.pi (fun _ : Fin l => P) with hμl
  set μ2 := Measure.pi (fun _ : Fin (l + l) => P) with hμ2
  set Q := {x | ε < Shared.maxDeviation S P l x} with hQdef
  have hQ : MeasurableSet Q := measurableSet_lt measurable_const (hπ l)
  have hf := aux_ns1_mp l P
  set f := fun x : Fin (l + l) → X =>
    ((fun i => x (Fin.castAdd l i)), (fun i => x (Fin.natAdd l i))) with hfdef
  set G := f ⁻¹' (Qᶜ ×ˢ Qᶜ) with hGdef
  have hGm : MeasurableSet G := hf.measurable (hQ.compl.prod hQ.compl)
  have hG : μ2.real G = (1 - μl.real Q) ^ 2 := by
    have h : μ2 G = μl Qᶜ * μl Qᶜ := by
      rw [hf.measure_preimage (hQ.compl.prod hQ.compl).nullMeasurableSet, Measure.prod_prod]
    have h' : μ2.real G = μl.real Qᶜ * μl.real Qᶜ := by
      simp only [Measure.real, h, ENNReal.toReal_mul]
    rw [h', probReal_compl_eq_one_sub hQ]
    ring
  have hsub : {x | 2 * ε < Shared.semiSampleDeviation S l x} ⊆ Gᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, hGdef, Set.mem_preimage, Set.mem_prod, hfdef, hQdef,
      Set.mem_ofPred_eq, not_and, not_lt]
    rcases aux_ns1_split P S ε hε l x hx with h | h
    · intro h1; linarith
    · intro _; exact not_le.mpr h
  have hGc : μ2.real Gᶜ = 1 - μ2.real G := probReal_compl_eq_one_sub hGm
  have hmono : μ2.real {x | 2 * ε < Shared.semiSampleDeviation S l x} ≤ μ2.real Gᶜ :=
    measureReal_mono hsub
  linarith

end





end

/- Complete checked body: CombinatorialModel -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

noncomputable def permMeanRho {X : Type*} (S : Set (Set X)) (l : ℕ)
    (x : Fin (l + l) → X) : ℝ :=
  (((l + l).factorial : ℝ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin (l + l)), Shared.semiSampleDeviation S l (x ∘ σ)

end VapnikChervonenkis.EntropyProof
end

/- Complete checked body: WeightedSauer -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

/-- A generating-function form of the finite Sauer bound. -/
theorem weighted_sauer {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset (Finset ι))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (A.card : ℝ) * t ^ A.vcDim ≤ (1 + t) ^ Fintype.card ι := by
  classical
  have hcard : (A.card : ℝ) ≤ A.shatterer.card := by
    exact_mod_cast Finset.card_le_card_shatterer A
  calc
    (A.card : ℝ) * t ^ A.vcDim ≤ (A.shatterer.card : ℝ) * t ^ A.vcDim :=
      mul_le_mul_of_nonneg_right hcard (pow_nonneg ht _)
    _ = ∑ s ∈ A.shatterer, t ^ A.vcDim := by simp
    _ ≤ ∑ s ∈ A.shatterer, t ^ s.card := by
      apply Finset.sum_le_sum
      intro s hs
      exact pow_le_pow_of_le_one ht ht1 (Finset.mem_shatterer.mp hs).card_le_vcDim
    _ ≤ ∑ s : Finset ι, t ^ s.card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => pow_nonneg ht _)
    _ = (1 + t) ^ Fintype.card ι := by
      have h := Finset.prod_add (fun _ : ι => t) (fun _ : ι => (1 : ℝ)) Finset.univ
      simpa only [Finset.prod_const, Finset.card_univ, one_pow, mul_one,
        Finset.powerset_univ, add_comm] using h.symm

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: FiniteIncidence -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

/-- Double-count a finite incidence array with equal column sums. -/
theorem uniform_incidence_sum {Ω ι : Type*} (F : Finset Ω) (C B : Finset ι)
    (w : Ω → ι → ℝ) (k : ℝ) (hBC : B ⊆ C)
    (hrow : ∀ x ∈ F, ∑ i ∈ C, w x i = k)
    (hcol : ∀ i ∈ C, ∀ j ∈ C,
      (∑ x ∈ F, w x i) = ∑ x ∈ F, w x j) :
    (C.card : ℝ) * (∑ x ∈ F, ∑ i ∈ B, w x i) =
      (B.card : ℝ) * (F.card : ℝ) * k := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨j, hj⟩ := hC
    let q := ∑ x ∈ F, w x j
    have hsum (D : Finset ι) (hDC : D ⊆ C) :
        (∑ x ∈ F, ∑ i ∈ D, w x i) = (D.card : ℝ) * q := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ _i ∈ D, q := Finset.sum_congr rfl (fun i hi => hcol i (hDC hi) j hj)
        _ = _ := by simp
    have hall : (C.card : ℝ) * q = (F.card : ℝ) * k := by
      rw [← hsum C (Finset.Subset.refl _)]
      calc
        _ = ∑ _x ∈ F, k := Finset.sum_congr rfl hrow
        _ = _ := by simp
    rw [hsum B hBC]
    calc
      _ = (B.card : ℝ) * ((C.card : ℝ) * q) := by ring
      _ = _ := by rw [hall]; ring
  · have hC0 : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    have hB0 : B = ∅ := Finset.subset_empty.mp (hC0 ▸ hBC)
    simp [hC0, hB0]

/-- Relabeling a finite set family preserves coordinate sums. -/
theorem sum_mem_relabel {ι : Type*} [DecidableEq ι]
    (F : Finset (Finset ι)) (σ : Equiv.Perm ι)
    (hF : F.image (fun U => U.map σ.toEmbedding) = F) (i : ι) :
    (∑ U ∈ F, if σ i ∈ U then (1 : ℝ) else 0) =
      ∑ U ∈ F, if i ∈ U then (1 : ℝ) else 0 := by
  classical
  conv_lhs => rw [← hF]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro U _
    simp
  · intro U _ V _ h
    exact Finset.map_injective σ.toEmbedding h

/-- A single permutation can send either ordered pair of distinct points to the other. -/
theorem exists_perm_pair {ι : Type*} (a b c d : ι) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm ι, σ a = c ∧ σ b = d := by
  classical
  let f : Bool → ι := fun t => if t then a else b
  let g : Bool → ι := fun t => if t then c else d
  have hf : Function.Injective f := by
    intro i j hij
    cases i <;> cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j hij
    cases i <;> cases j <;> simp_all [g]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ, by simpa [f, g] using hσ true, by simpa [f, g] using hσ false⟩

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: BalancedFibers -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def balancedFamily (l : ℕ) : Finset (Finset ι) := Finset.univ.powersetCard l

def traceFiber (D I : Finset ι) (l : ℕ) : Finset (Finset ι) :=
  (balancedFamily l).filter (fun U => U ∩ D = I)

omit [DecidableEq ι] in
@[simp] theorem mem_balancedFamily {l : ℕ} {U : Finset ι} :
    U ∈ balancedFamily l ↔ U.card = l := by simp [balancedFamily]

@[simp] theorem mem_traceFiber {D I U : Finset ι} {l : ℕ} :
    U ∈ traceFiber D I l ↔ U.card = l ∧ U ∩ D = I := by simp [traceFiber]

omit [Fintype ι] [DecidableEq ι] in
theorem map_fixed (σ : Equiv.Perm ι) (D : Finset ι)
    (hfix : ∀ i ∈ D, σ i = i) : D.map σ.toEmbedding = D := by
  ext i
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa only [hfix j hj] using hj
  · intro hi
    exact ⟨i, hi, hfix i hi⟩

theorem balancedFamily_relabel (l : ℕ) (σ : Equiv.Perm ι) :
    (balancedFamily l).image (fun U => U.map σ.toEmbedding) = balancedFamily l := by
  apply Finset.eq_of_subset_of_card_le
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    simpa using hV
  · rw [Finset.card_image_of_injective _ (Finset.map_injective σ.toEmbedding)]

theorem traceFiber_relabel (D I : Finset ι) (l : ℕ) (σ : Equiv.Perm ι)
    (hID : I ⊆ D) (hfix : ∀ i ∈ D, σ i = i) :
    (traceFiber D I l).image (fun U => U.map σ.toEmbedding) = traceFiber D I l := by
  have hD := map_fixed σ D hfix
  have hI := map_fixed σ I (fun i hi => hfix i (hID hi))
  apply Finset.eq_of_subset_of_card_le
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨hc, hi⟩ := mem_traceFiber.mp hV
    apply mem_traceFiber.mpr
    refine ⟨by simpa using hc, ?_⟩
    rw [← hD, ← Finset.map_inter, hi, hI]
  · rw [Finset.card_image_of_injective _ (Finset.map_injective σ.toEmbedding)]

theorem traceFiber_column_equal (D I : Finset ι) (l : ℕ) (hID : I ⊆ D)
    (a b : ι) (ha : a ∉ D) (hb : b ∉ D) :
    (∑ U ∈ traceFiber D I l, if a ∈ U then (1 : ℝ) else 0) =
      ∑ U ∈ traceFiber D I l, if b ∈ U then (1 : ℝ) else 0 := by
  have hfix : ∀ i ∈ D, Equiv.swap a b i = i := by
    intro i hi
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun h => ha (h ▸ hi)
    · exact fun h => hb (h ▸ hi)
  have h := sum_mem_relabel (traceFiber D I l) (Equiv.swap a b)
    (traceFiber_relabel D I l (Equiv.swap a b) hID hfix) b
  simpa only [Equiv.swap_apply_right] using h

omit [Fintype ι] in
theorem sum_indicator_inter (C U : Finset ι) :
    (∑ i ∈ C, if i ∈ U then (1 : ℝ) else 0) = (C ∩ U).card := by
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter]

/-- Conditional incidence count, without a division or a nonempty-fiber assumption. -/
theorem traceFiber_incidence (D I B : Finset ι) (l : ℕ) (hID : I ⊆ D)
    (hBD : Disjoint B D) :
    ((Fintype.card ι : ℝ) - D.card) *
      (∑ U ∈ traceFiber D I l, ((U ∩ B).card : ℝ)) =
        (B.card : ℝ) * (traceFiber D I l).card * ((l : ℝ) - I.card) := by
  have hBC : B ⊆ Dᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (fun hid => Finset.disjoint_left.mp hBD hi hid)
  have hrow (U : Finset ι) (hU : U ∈ traceFiber D I l) :
      (∑ i ∈ Dᶜ, if i ∈ U then (1 : ℝ) else 0) = (l : ℝ) - I.card := by
    rw [sum_indicator_inter]
    obtain ⟨hc, hi⟩ := mem_traceFiber.mp hU
    have hsum := Finset.card_inter_add_card_sdiff U D
    rw [hi, hc] at hsum
    have he : Dᶜ ∩ U = U \ D := by ext i; simp; tauto
    rw [he]
    have hcast : (I.card : ℝ) + (U \ D).card = l := by exact_mod_cast hsum
    linarith
  have hcol (i : ι) (hi : i ∈ Dᶜ) (j : ι) (hj : j ∈ Dᶜ) :=
    traceFiber_column_equal D I l hID i j (Finset.mem_compl.mp hi) (Finset.mem_compl.mp hj)
  have h := uniform_incidence_sum (traceFiber D I l) Dᶜ B
    (fun U i => if i ∈ U then (1 : ℝ) else 0) ((l : ℝ) - I.card) hBC hrow hcol
  simp only [sum_indicator_inter, Finset.inter_comm B] at h
  rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ D)] at h
  exact h

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: BalancedMoments -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

variable {ι : Type*} [DecidableEq ι]

theorem sum_cross_incidence (D U : Finset ι) :
    (∑ ij ∈ D.offDiag, if ij.1 ∈ U ∧ ij.2 ∉ U then (1 : ℝ) else 0) =
      ((D ∩ U).card : ℝ) * (D \ U).card := by
  have he : D.offDiag.filter (fun ij => ij.1 ∈ U ∧ ij.2 ∉ U) =
      (D ∩ U) ×ˢ (D \ U) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
      Finset.mem_inter, Finset.mem_sdiff]
    aesop
  rw [Finset.sum_boole, he, Finset.card_product, Nat.cast_mul]

theorem sum_pair_relabel (F : Finset (Finset ι)) (σ : Equiv.Perm ι)
    (hF : F.image (fun U => U.map σ.toEmbedding) = F) (i j : ι) :
    (∑ U ∈ F, if σ i ∈ U ∧ σ j ∉ U then (1 : ℝ) else 0) =
      ∑ U ∈ F, if i ∈ U ∧ j ∉ U then (1 : ℝ) else 0 := by
  classical
  conv_lhs => rw [← hF]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro U _
    simp
  · intro U _ V _ h
    exact Finset.map_injective σ.toEmbedding h

variable [Fintype ι]

theorem balanced_pair_column_equal (l : ℕ) (a b c d : ι)
    (hab : a ≠ b) (hcd : c ≠ d) :
    (∑ U ∈ balancedFamily l, if a ∈ U ∧ b ∉ U then (1 : ℝ) else 0) =
      ∑ U ∈ balancedFamily l, if c ∈ U ∧ d ∉ U then (1 : ℝ) else 0 := by
  obtain ⟨σ, ha, hb⟩ := exists_perm_pair c d a b hcd hab
  have h := sum_pair_relabel (balancedFamily l) σ (balancedFamily_relabel l σ) c d
  simpa only [ha, hb] using h

/-- The cross-pair second moment of a uniform fixed-cardinality subset. -/
theorem balanced_cross_moment (l : ℕ) (D : Finset ι) :
    (((Finset.univ : Finset ι).offDiag.card : ℕ) : ℝ) *
      (∑ U ∈ balancedFamily l, ((D ∩ U).card : ℝ) * (D \ U).card) =
        (D.offDiag.card : ℝ) * (balancedFamily (ι := ι) l).card *
          ((l : ℝ) * ((Fintype.card ι : ℝ) - l)) := by
  let F := balancedFamily (ι := ι) l
  let C := (Finset.univ : Finset ι).offDiag
  let w : Finset ι → ι × ι → ℝ :=
    fun U ij => if ij.1 ∈ U ∧ ij.2 ∉ U then 1 else 0
  have hrow (U : Finset ι) (hU : U ∈ F) :
      (∑ ij ∈ C, w U ij) = (l : ℝ) * ((Fintype.card ι : ℝ) - l) := by
    have hc : U.card = l := mem_balancedFamily.mp hU
    dsimp only [C, w]
    rw [sum_cross_incidence, Finset.univ_inter]
    have he : Finset.univ \ U = Uᶜ := by ext i; simp
    rw [he, Finset.card_compl, Nat.cast_sub (Finset.card_le_univ U), hc]
  have hcol (ij : ι × ι) (hij : ij ∈ C) (pq : ι × ι) (hpq : pq ∈ C) :
      (∑ U ∈ F, w U ij) = ∑ U ∈ F, w U pq := by
    exact balanced_pair_column_equal l ij.1 ij.2 pq.1 pq.2
      (Finset.mem_offDiag.mp hij).2.2 (Finset.mem_offDiag.mp hpq).2.2
  have h := uniform_incidence_sum F C D.offDiag w
    ((l : ℝ) * ((Fintype.card ι : ℝ) - l))
    (Finset.offDiag_mono (Finset.subset_univ D)) hrow hcol
  simpa only [w, sum_cross_incidence] using h

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: ConditionalLower -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

/-- The conditional lower bound is a convex combination of two squares. -/
theorem conditional_lower_algebra {C d r b F T l R : ℝ}
    (hC : 0 < C) (hd : 0 ≤ d) (hF : 0 ≤ F) (hb : 0 ≤ b) (hbC : b ≤ C)
    (hsize : C + d = 2*l) (hinc : C*T = b*F*(l-r))
    (hscore : F*r+2*T-F*b ≤ l*R) : F*r*(d-r) ≤ d*l*R := by
  have hid : C*(d*l*R-F*r*(d-r)) =
      C*d*(l*R-(F*r+2*T-F*b)) + F*((C-b)*r^2+b*(d-r)^2) := by
    linear_combination 2*d*hinc-b*d*F*hsize
  have hfirst : 0 ≤ C*d*(l*R-(F*r+2*T-F*b)) :=
    mul_nonneg (mul_nonneg hC.le hd) (sub_nonneg.mpr hscore)
  have hsecond : 0 ≤ F*((C-b)*r^2+b*(d-r)^2) :=
    mul_nonneg hF (add_nonneg (mul_nonneg (sub_nonneg.mpr hbC) (sq_nonneg r))
      (mul_nonneg hb (sq_nonneg (d-r))))
  have hprod : 0 ≤ C*(d*l*R-F*r*(d-r)) := by rw [hid]; exact add_nonneg hfirst hsecond
  have hdiff : 0 ≤ d*l*R-F*r*(d-r) := nonneg_of_mul_nonneg_right hprod hC
  exact sub_nonneg.mp hdiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every fiber of the shattered trace contributes a cross-pair amount. -/
theorem traceFiber_score_lower (l : ℕ) (hsize : Fintype.card ι = 2*l)
    (D I A : Finset ι) (hID : I ⊆ D) (hDA : D ∩ A = I)
    (hD : D.card < Fintype.card ι) (R : Finset ι → ℝ)
    (hscore : ∀ U ∈ traceFiber D I l,
      2*((U ∩ A).card : ℝ)-(A.card : ℝ) ≤ (l : ℝ)*R U) :
    (traceFiber D I l).card * (I.card : ℝ) * ((D.card : ℝ)-I.card) ≤
      (D.card : ℝ)*(l : ℝ)*(∑ U ∈ traceFiber D I l, R U) := by
  let F := traceFiber D I l
  let B := A \ D
  have hBD : Disjoint B D := Finset.sdiff_disjoint
  have hinc := traceFiber_incidence D I B l hID hBD
  have hA : (A.card : ℝ) = I.card+B.card := by
    have h := Finset.card_inter_add_card_sdiff A D
    rw [Finset.inter_comm A D, hDA] at h
    exact_mod_cast h.symm
  have hcount (U : Finset ι) (hU : U ∈ F) :
      ((U ∩ A).card : ℝ) = I.card+(U ∩ B).card := by
    have hUD : U ∩ D = I := (mem_traceFiber.mp hU).2
    have he : (U ∩ A) ∩ D = I := by
      calc
        (U ∩ A) ∩ D = (U ∩ D) ∩ (D ∩ A) := by ext i; simp; tauto
        _ = I := by rw [hUD, hDA, Finset.inter_self]
    have hb : (U ∩ A) \ D = U ∩ B := by ext i; simp [B]; tauto
    have h := Finset.card_inter_add_card_sdiff (U ∩ A) D
    rw [he, hb] at h
    exact_mod_cast h.symm
  have hs := Finset.sum_le_sum hscore
  have hleft : (∑ U ∈ F, (2*((U ∩ A).card : ℝ)-(A.card : ℝ))) =
      (F.card : ℝ)*I.card+2*(∑ U ∈ F, ((U ∩ B).card : ℝ))-(F.card : ℝ)*B.card := by
    calc
      _ = ∑ U ∈ F, (2*((I.card : ℝ)+(U ∩ B).card)-((I.card : ℝ)+B.card)) :=
        Finset.sum_congr rfl (fun U hU => by rw [hcount U hU, hA])
      _ = _ := by simp only [mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
  have hs' : (F.card : ℝ)*I.card+2*(∑ U ∈ F, ((U ∩ B).card : ℝ))-
      (F.card : ℝ)*B.card ≤ (l : ℝ)*(∑ U ∈ F, R U) := by
    change (∑ U ∈ F, (2*((U ∩ A).card : ℝ)-(A.card : ℝ))) ≤
      ∑ U ∈ F, (l : ℝ)*R U at hs
    rwa [hleft, ← Finset.mul_sum] at hs
  have hC : 0 < (Fintype.card ι : ℝ)-D.card := by
    apply sub_pos.mpr
    exact_mod_cast hD
  have hbC : (B.card : ℝ) ≤ (Fintype.card ι : ℝ)-D.card := by
    have hbsub : B ⊆ Dᶜ := by
      intro i hi
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
    have hc := Finset.card_le_card hbsub
    rw [Finset.card_compl] at hc
    have hc' : (B.card : ℝ) ≤ ((Fintype.card ι - D.card : ℕ) : ℝ) := by exact_mod_cast hc
    simpa only [Nat.cast_sub (Finset.card_le_univ D)] using hc'
  have hsize' : ((Fintype.card ι : ℝ)-D.card)+(D.card : ℝ) = 2*(l : ℝ) := by
    have hh : (Fintype.card ι : ℝ) = 2*(l : ℝ) := by exact_mod_cast hsize
    linarith
  exact conditional_lower_algebra (d := (D.card : ℝ)) (r := (I.card : ℝ))
    (F := (F.card : ℝ)) (l := (l : ℝ)) hC (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hbC hsize' hinc hs'

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: BalancedShattering -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

theorem moment_lower_algebra {d F l S T : ℝ} (hd : 0 < d) (hl : 1 ≤ l)
    (hT : 0 ≤ T) (hm : (2*l)*(2*l-1)*S = d*(d-1)*F*l^2)
    (hs : S ≤ d*l*T) : (d-1)*F ≤ 4*l*T := by
  have hl0 : 0 < l := by linarith
  have hstrong : (d-1)*F ≤ 2*(2*l-1)*T := by
    apply (mul_le_mul_iff_of_pos_left (mul_pos hd (sq_pos_of_pos hl0))).mp
    calc
      (d*l^2)*((d-1)*F) = (2*l)*(2*l-1)*S := by nlinarith only [hm]
      _ ≤ (2*l)*(2*l-1)*(d*l*T) :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg (by positivity) (by linarith))
      _ = (d*l^2)*(2*(2*l-1)*T) := by ring
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_traceFiber (D : Finset ι) (l : ℕ) (f : Finset ι → ℝ) :
    (∑ I ∈ D.powerset, ∑ U ∈ traceFiber D I l, f U) =
      ∑ U ∈ balancedFamily l, f U := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun U (_ : U ∈ balancedFamily l) => Finset.mem_powerset.mpr (Finset.inter_subset_right (s₁ := U))) f

omit [Fintype ι] [DecidableEq ι] in
theorem offDiag_card_real (D : Finset ι) :
    (D.offDiag.card : ℝ) = (D.card : ℝ)*((D.card : ℝ)-1) := by
  rw [Finset.offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  ring

/-- A finite family with a shattered set has a uniformly large balanced discrepancy. -/
theorem balanced_shattering_lower (l : ℕ) (hl : 1 ≤ l) (hsize : Fintype.card ι = 2*l)
    (A : Finset (Finset ι)) (D : Finset ι) (hsh : A.Shatters D)
    (R : Finset ι → ℝ)
    (hR0 : ∀ U ∈ balancedFamily l, 0 ≤ R U)
    (hR : ∀ U ∈ balancedFamily l, ∀ a ∈ A,
      2*((U ∩ a).card : ℝ)-(a.card : ℝ) ≤ (l : ℝ)*R U) :
    ((D.card : ℝ)-1)*(balancedFamily (ι := ι) l).card ≤
      4*(l : ℝ)*(∑ U ∈ balancedFamily l, R U) := by
  classical
  have hT : 0 ≤ ∑ U ∈ balancedFamily l, R U := Finset.sum_nonneg hR0
  by_cases hd : D.card ≤ 1
  · have hd' : (D.card : ℝ)-1 ≤ 0 := by
      have hh : (D.card : ℝ) ≤ 1 := by exact_mod_cast hd
      linarith
    exact (mul_nonpos_of_nonpos_of_nonneg hd' (Nat.cast_nonneg _)).trans (by positivity)
  have hd0 : 0 < (D.card : ℝ) := by exact_mod_cast (show 0 < D.card by omega)
  by_cases hfull : D.card = Fintype.card ι
  · have hD : D = Finset.univ := Finset.eq_univ_of_card D hfull
    have hpoint (U : Finset ι) (hU : U ∈ balancedFamily l) : 1 ≤ R U := by
      obtain ⟨a, ha, hDa⟩ := hsh (show U ⊆ D by rw [hD]; exact Finset.subset_univ _)
      have haU : a = U := by simpa [hD] using hDa
      have hh := hR U hU a ha
      rw [haU, Finset.inter_self, mem_balancedFamily.mp hU] at hh
      have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
      nlinarith
    have hsum := Finset.sum_le_sum hpoint
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    have he : (D.card : ℝ) = 2*(l : ℝ) := by exact_mod_cast (hfull.trans hsize)
    calc
      _ ≤ 4*(l : ℝ)*(balancedFamily (ι := ι) l).card :=
        mul_le_mul_of_nonneg_right (by rw [he]; linarith) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  · have hDlt : D.card < Fintype.card ι := lt_of_le_of_ne (Finset.card_le_univ _) hfull
    have hfiber (I : Finset ι) (hI : I ∈ D.powerset) :
        (traceFiber D I l).card*(I.card : ℝ)*((D.card : ℝ)-I.card) ≤
          (D.card : ℝ)*(l : ℝ)*(∑ U ∈ traceFiber D I l, R U) := by
      have hID := Finset.mem_powerset.mp hI
      obtain ⟨a, ha, hDa⟩ := hsh hID
      exact traceFiber_score_lower l hsize D I a hID hDa hDlt R
        (fun U hU => hR U (mem_balancedFamily.mpr (mem_traceFiber.mp hU).1) a ha)
    have hsum := Finset.sum_le_sum hfiber
    have hcross : (∑ U ∈ balancedFamily l, ((D ∩ U).card : ℝ)*(D \ U).card) =
        ∑ I ∈ D.powerset, (traceFiber D I l).card*(I.card : ℝ)*((D.card : ℝ)-I.card) := by
      rw [← sum_traceFiber D l]
      apply Finset.sum_congr rfl
      intro I hI
      calc
        _ = ∑ _U ∈ traceFiber D I l, (I.card : ℝ)*((D.card : ℝ)-I.card) := by
          apply Finset.sum_congr rfl
          intro U hU
          have he : D ∩ U = I := by rw [Finset.inter_comm, (mem_traceFiber.mp hU).2]
          have hc := Finset.card_inter_add_card_sdiff D U
          rw [he] at hc
          have hc' : (I.card : ℝ)+(D \ U).card = D.card := by exact_mod_cast hc
          rw [he]
          congr 1
          linarith
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    have hs : (∑ U ∈ balancedFamily l, ((D ∩ U).card : ℝ)*(D \ U).card) ≤
        (D.card : ℝ)*(l : ℝ)*(∑ U ∈ balancedFamily l, R U) := by
      rw [hcross]
      simpa only [← Finset.mul_sum, sum_traceFiber] using hsum
    have hm := balanced_cross_moment l D
    rw [offDiag_card_real, offDiag_card_real, Finset.card_univ, hsize] at hm
    push_cast at hm
    have hm' : (2*(l : ℝ))*(2*(l : ℝ)-1)*
        (∑ U ∈ balancedFamily l, ((D ∩ U).card : ℝ)*(D \ U).card) =
          (D.card : ℝ)*((D.card : ℝ)-1)*(balancedFamily (ι := ι) l).card*(l : ℝ)^2 := by
      nlinarith only [hm]
    exact moment_lower_algebra hd0 (by exact_mod_cast hl) hT hm' hs

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: PermutationAverages -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem map_perm_mul (U : Finset ι) (σ τ : Equiv.Perm ι) :
    U.map (σ*τ).toEmbedding = (U.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

/-- Uniform permutation images have the uniform fixed-cardinality average. -/
theorem permutation_balanced_sum (l : ℕ) (T : Finset ι) (hT : T.card = l)
    (f : Finset ι → ℝ) :
    ((balancedFamily (ι := ι) l).card : ℝ) *
      (∑ σ : Equiv.Perm ι, f (T.map σ.toEmbedding)) =
        (Fintype.card (Equiv.Perm ι) : ℝ) * (∑ U ∈ balancedFamily l, f U) := by
  classical
  let F := balancedFamily (ι := ι) l
  have hmean (U : Finset ι) (hU : U ∈ F) :
      (∑ σ : Equiv.Perm ι, f (U.map σ.toEmbedding)) =
        ∑ σ : Equiv.Perm ι, f (T.map σ.toEmbedding) := by
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq T U
      (hT.trans (mem_balancedFamily.mp hU).symm)
    rw [← hτ]
    simp only [← map_perm_mul]
    exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm ι => f (T.map σ.toEmbedding))
  have hinner (σ : Equiv.Perm ι) :
      (∑ U ∈ F, f (U.map σ.toEmbedding)) = ∑ U ∈ F, f U := by
    rw [← Finset.sum_image]
    · rw [balancedFamily_relabel]
    · intro U _ V _ h
      exact Finset.map_injective σ.toEmbedding h
  calc
    (F.card : ℝ)*(∑ σ : Equiv.Perm ι, f (T.map σ.toEmbedding)) =
        ∑ U ∈ F, ∑ σ : Equiv.Perm ι, f (U.map σ.toEmbedding) := by
      calc
        _ = ∑ _U ∈ F, (∑ σ : Equiv.Perm ι, f (T.map σ.toEmbedding)) := by simp
        _ = _ := Finset.sum_congr rfl (fun U hU => (hmean U hU).symm)
    _ = ∑ σ : Equiv.Perm ι, ∑ U ∈ F, f (U.map σ.toEmbedding) := Finset.sum_comm
    _ = _ := by
      simp only [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, F]

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: FiniteDiscrepancy -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def finiteDiscrepancy (A : Finset (Finset ι)) (hA : A.Nonempty)
    (l : ℕ) (U : Finset ι) : ℝ :=
  A.sup' hA (fun a => |(2*((U ∩ a).card : ℝ)-(a.card : ℝ))/(l : ℝ)|)

omit [Fintype ι] in
theorem finiteDiscrepancy_nonneg (A : Finset (Finset ι)) (hA : A.Nonempty)
    (l : ℕ) (U : Finset ι) : 0 ≤ finiteDiscrepancy A hA l U := by
  unfold finiteDiscrepancy
  obtain ⟨a, ha⟩ := hA
  exact (abs_nonneg ((2*((U ∩ a).card : ℝ)-(a.card : ℝ))/(l : ℝ))).trans
    (Finset.le_sup' (fun b => |(2*((U ∩ b).card : ℝ)-(b.card : ℝ))/(l : ℝ)|) ha)

omit [Fintype ι] in
theorem finiteDiscrepancy_score (A : Finset (Finset ι)) (hA : A.Nonempty)
    (l : ℕ) (hl : 0 < l) (U a : Finset ι) (ha : a ∈ A) :
    2*((U ∩ a).card : ℝ)-(a.card : ℝ) ≤ (l : ℝ)*finiteDiscrepancy A hA l U := by
  have h := (le_abs_self _).trans (Finset.le_sup'
    (fun a => |(2*((U ∩ a).card : ℝ)-(a.card : ℝ))/(l : ℝ)|) ha)
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hh := (div_le_iff₀ hl').mp h
  simpa only [finiteDiscrepancy, mul_comm] using hh

/-- Deterministic VC dimension is bounded by the mean balanced discrepancy. -/
theorem dimension_le_perm_discrepancy (l : ℕ) (hl : 1 ≤ l)
    (hsize : Fintype.card ι = 2*l) (T : Finset ι) (hT : T.card = l)
    (A : Finset (Finset ι)) (hA : A.Nonempty) :
    ((A.vcDim : ℝ)-1)*(Fintype.card (Equiv.Perm ι) : ℝ) ≤
      4*(l : ℝ)*(∑ σ : Equiv.Perm ι, finiteDiscrepancy A hA l (T.map σ.toEmbedding)) := by
  classical
  have hsh : A.shatterer.Nonempty := ⟨∅, Finset.mem_shatterer.mpr
    (Finset.shatters_empty.mpr hA)⟩
  obtain ⟨D, hD, hd⟩ := Finset.exists_mem_eq_sup A.shatterer hsh Finset.card
  have hb := balanced_shattering_lower l hl hsize A D (Finset.mem_shatterer.mp hD)
    (finiteDiscrepancy A hA l)
    (fun U _ => finiteDiscrepancy_nonneg A hA l U)
    (fun U _ a ha => finiteDiscrepancy_score A hA l (by omega) U a ha)
  have he := permutation_balanced_sum l T hT (finiteDiscrepancy A hA l)
  have hF : (0 : ℝ) < (balancedFamily (ι := ι) l).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨T, mem_balancedFamily.mpr hT⟩
  have hc : 0 ≤ (Fintype.card (Equiv.Perm ι) : ℝ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_right hb hc
  have hd' : D.card = A.vcDim := hd.symm
  rw [hd'] at hm
  have hid : (4*(l : ℝ)*(∑ U ∈ balancedFamily l, finiteDiscrepancy A hA l U))*
      (Fintype.card (Equiv.Perm ι) : ℝ) =
        (balancedFamily (ι := ι) l).card *
          (4*(l : ℝ)*(∑ σ : Equiv.Perm ι, finiteDiscrepancy A hA l (T.map σ.toEmbedding))) := by
    nlinarith only [he]
  rw [hid] at hm
  apply (mul_le_mul_iff_of_pos_left hF).mp
  nlinarith only [hm]

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: SampleTrace -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

open Classical in
noncomputable def sampleTrace {X : Type*} {n : ℕ} (x : Fin n → X) (A : Set X) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ∈ A)

open Classical in
noncomputable def sampleFamily {X : Type*} {n : ℕ} (S : Set (Set X)) (x : Fin n → X) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun t => ∃ A ∈ S, ∀ i, i ∈ t ↔ x i ∈ A)

@[simp] theorem mem_sampleFamily {X : Type*} {n : ℕ} (S : Set (Set X)) (x : Fin n → X)
    (t : Finset (Fin n)) : t ∈ sampleFamily S x ↔ ∃ A ∈ S, sampleTrace x A = t := by
  classical
  simp only [sampleFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, Finset.ext (fun i => ?_)⟩
    simpa [sampleTrace] using (ht i).symm
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, fun i => by simp [sampleTrace]⟩

theorem sampleTrace_mem {X : Type*} {n : ℕ} (S : Set (Set X)) (x : Fin n → X)
    (A : Set X) (hA : A ∈ S) : sampleTrace x A ∈ sampleFamily S x :=
  (mem_sampleFamily S x _).mpr ⟨A, hA, rfl⟩

theorem sampleFamily_nonempty {X : Type*} {n : ℕ} (S : Set (Set X)) (hS : S.Nonempty)
    (x : Fin n → X) : (sampleFamily S x).Nonempty := by
  obtain ⟨A, hA⟩ := hS
  exact ⟨sampleTrace x A, sampleTrace_mem S x A hA⟩

theorem sampleFamily_card {X : Type*} {n : ℕ} (S : Set (Set X)) (x : Fin n → X) :
    (sampleFamily S x).card = Shared.index S x := rfl

def firstHalf (l : ℕ) : Finset (Fin (l+l)) := Finset.univ.map (Fin.castAddEmb l)

@[simp] theorem firstHalf_card (l : ℕ) : (firstHalf l).card = l := by simp [firstHalf]

theorem first_trace_count {X : Type*} (l : ℕ) (x : Fin (l+l) → X) (A : Set X)
    (σ : Equiv.Perm (Fin (l+l))) :
    (sampleTrace (fun i : Fin l => x (σ (Fin.castAdd l i))) A).card =
      (((firstHalf l).map σ.toEmbedding) ∩ sampleTrace x A).card := by
  classical
  have he : (sampleTrace (fun i : Fin l => x (σ (Fin.castAdd l i))) A).map
      ((Fin.castAddEmb l).trans σ.toEmbedding) =
        ((firstHalf l).map σ.toEmbedding) ∩ sampleTrace x A := by
    ext j
    simp only [sampleTrace, firstHalf, Finset.map_map, Finset.mem_map, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Fin.castAddEmb_apply]
    aesop
  simpa only [Finset.card_map] using congrArg Finset.card he

theorem trace_count_permutation {X : Type*} {n : ℕ} (x : Fin n → X) (A : Set X)
    (σ : Equiv.Perm (Fin n)) : (sampleTrace (x ∘ σ) A).card = (sampleTrace x A).card := by
  classical
  apply Finset.card_equiv σ
  intro i
  simp [sampleTrace]

theorem frequency_difference_trace {X : Type*} (l : ℕ) (x : Fin (l+l) → X) (A : Set X)
    (σ : Equiv.Perm (Fin (l+l))) :
    Shared.relFreq A (fun i : Fin l => (x ∘ σ) (Fin.castAdd l i))-
      Shared.relFreq A (fun i : Fin l => (x ∘ σ) (Fin.natAdd l i)) =
        (2*((((firstHalf l).map σ.toEmbedding) ∩ sampleTrace x A).card : ℝ)-
          (sampleTrace x A).card)/(l : ℝ) := by
  classical
  have hc := Fin.sum_univ_add (fun i : Fin (l+l) => if x (σ i) ∈ A then (1 : ℕ) else 0)
  simp only [Finset.sum_boole, Nat.cast_id] at hc
  change (sampleTrace (x ∘ σ) A).card =
    (sampleTrace (fun i : Fin l => x (σ (Fin.castAdd l i))) A).card+
      (sampleTrace (fun i : Fin l => x (σ (Fin.natAdd l i))) A).card at hc
  rw [trace_count_permutation] at hc
  have hc' : ((sampleTrace x A).card : ℝ) =
    (sampleTrace (fun i : Fin l => x (σ (Fin.castAdd l i))) A).card+
      (sampleTrace (fun i : Fin l => x (σ (Fin.natAdd l i))) A).card := by exact_mod_cast hc
  change ((sampleTrace (fun i : Fin l => x (σ (Fin.castAdd l i))) A).card : ℝ)/(l : ℝ)-
    ((sampleTrace (fun i : Fin l => x (σ (Fin.natAdd l i))) A).card : ℝ)/(l : ℝ) = _
  rw [hc', ← first_trace_count]
  ring

/-- The finite trace discrepancy is exactly the canonical semi-sample supremum. -/
theorem rho_eq_finiteDiscrepancy {X : Type*} (S : Set (Set X)) (hS : S.Nonempty)
    (l : ℕ) (x : Fin (l+l) → X) (σ : Equiv.Perm (Fin (l+l))) :
    Shared.semiSampleDeviation S l (x ∘ σ) =
      finiteDiscrepancy (sampleFamily S x) (sampleFamily_nonempty S hS x) l
        ((firstHalf l).map σ.toEmbedding) := by
  classical
  let : Nonempty S := hS.to_subtype
  let R := finiteDiscrepancy (sampleFamily S x) (sampleFamily_nonempty S hS x) l
    ((firstHalf l).map σ.toEmbedding)
  have hu (A : S) :
      |Shared.relFreq (A : Set X) (fun i : Fin l => (x ∘ σ) (Fin.castAdd l i))-
        Shared.relFreq (A : Set X) (fun i : Fin l => (x ∘ σ) (Fin.natAdd l i))| ≤ R := by
    rw [frequency_difference_trace]
    dsimp only [R, finiteDiscrepancy]
    exact Finset.le_sup' (fun a => |(2*((((firstHalf l).map σ.toEmbedding) ∩ a).card : ℝ)-
      (a.card : ℝ))/(l : ℝ)|) (sampleTrace_mem S x A A.property)
  have hbounded : BddAbove (Set.range (fun A : S =>
      |Shared.relFreq (A : Set X) (fun i : Fin l => (x ∘ σ) (Fin.castAdd l i))-
        Shared.relFreq (A : Set X) (fun i : Fin l => (x ∘ σ) (Fin.natAdd l i))|)) := by
    refine ⟨R, ?_⟩
    rintro y ⟨A, rfl⟩
    exact hu A
  apply le_antisymm
  · exact ciSup_le hu
  · unfold finiteDiscrepancy
    apply Finset.sup'_le
    intro a ha
    obtain ⟨A, hA, rfl⟩ := (mem_sampleFamily S x a).mp ha
    have h := le_ciSup hbounded (⟨A, hA⟩ : S)
    simpa only [Shared.semiSampleDeviation, frequency_difference_trace] using h

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: WeightedEntropy -/
section

set_option autoImplicit false

namespace VapnikChervonenkis.EntropyProof

theorem weighted_entropy_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (Finset ι)) (hA : A.Nonempty) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.logb 2 (A.card : ℝ) ≤ (Fintype.card ι : ℝ)*Real.logb 2 (1+t)-
      (A.vcDim : ℝ)*Real.logb 2 t := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos hc (pow_pos ht _)) (weighted_sauer A ht.le ht1)
  rw [Real.logb_mul hc.ne' (pow_pos ht _).ne', Real.logb_pow, Real.logb_pow] at h
  linarith

theorem entropy_bound_of_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset (Finset ι)) (hA : A.Nonempty) (hN : 0 < Fintype.card ι)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hd : (A.vcDim : ℝ)-1 ≤ 2*(Fintype.card ι : ℝ)*R) :
    Real.logb 2 (A.card : ℝ)/(Fintype.card ι : ℝ) ≤
      Real.logb 2 (1+t)-Real.logb 2 t*(2*R+1/(Fintype.card ι : ℝ)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hlog : Real.logb 2 t ≤ 0 := Real.logb_nonpos (by norm_num) ht.le ht1
  have hb := weighted_entropy_bound A hA ht ht1
  have hm := mul_le_mul_of_nonneg_right hd (neg_nonneg.mpr hlog)
  apply (div_le_iff₀ hn).mpr
  have he : (Real.logb 2 (1+t)-Real.logb 2 t*(2*R+1/(Fintype.card ι : ℝ)))*
      (Fintype.card ι : ℝ) = (Fintype.card ι : ℝ)*Real.logb 2 (1+t)-
        (2*(Fintype.card ι : ℝ)*R+1)*Real.logb 2 t := by
    field_simp
  rw [he]
  nlinarith

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: PointwiseEntropy -/
section

set_option autoImplicit false
open scoped BigOperators

namespace VapnikChervonenkis.EntropyProof

theorem sample_dimension_bound {X : Type*} (S : Set (Set X)) (hS : S.Nonempty)
    (l : ℕ) (hl : 1 ≤ l) (x : Fin (l+l) → X) :
    ((sampleFamily S x).vcDim : ℝ)-1 ≤ 4*(l : ℝ)*permMeanRho S l x := by
  classical
  have h := dimension_le_perm_discrepancy l hl (by simp; omega : Fintype.card (Fin (l+l)) = 2*l)
    (firstHalf l) (firstHalf_card l) (sampleFamily S x) (sampleFamily_nonempty S hS x)
  have hsum : (∑ σ : Equiv.Perm (Fin (l+l)),
      finiteDiscrepancy (sampleFamily S x) (sampleFamily_nonempty S hS x) l
        ((firstHalf l).map σ.toEmbedding)) =
      ∑ σ : Equiv.Perm (Fin (l+l)), Shared.semiSampleDeviation S l (x ∘ σ) := by
    exact Finset.sum_congr rfl (fun σ _ => (rho_eq_finiteDiscrepancy S hS l x σ).symm)
  rw [hsum, Fintype.card_perm, Fintype.card_fin] at h
  have hfac : (0 : ℝ) < (l+l).factorial := by exact_mod_cast Nat.factorial_pos (l+l)
  have hh := (le_div_iff₀ hfac).mpr h
  have he : (4*(l : ℝ)*(∑ σ : Equiv.Perm (Fin (l+l)),
      Shared.semiSampleDeviation S l (x ∘ σ)))/((l+l).factorial : ℝ) =
        4*(l : ℝ)*permMeanRho S l x := by
    simp only [permMeanRho, div_eq_mul_inv]
    ring
  rwa [he] at hh

/-- The complete finite entropy-versus-discrepancy inequality used by the root. -/
theorem pointwise_entropy_bound {X : Type*} (S : Set (Set X)) (hS : S.Nonempty)
    (l : ℕ) (hl : 1 ≤ l) (x : Fin (l+l) → X) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Real.logb 2 (Shared.index S x : ℝ)/(2*(l : ℝ)) ≤
      Real.logb 2 (1+t)-Real.logb 2 t*(2*permMeanRho S l x+1/(2*(l : ℝ))) := by
  classical
  have hc : (Fintype.card (Fin (l+l)) : ℝ) = 2*(l : ℝ) := by simp; ring
  have hd := sample_dimension_bound S hS l hl x
  have hd' : ((sampleFamily S x).vcDim : ℝ)-1 ≤
      2*(Fintype.card (Fin (l+l)) : ℝ)*permMeanRho S l x := by rw [hc]; nlinarith only [hd]
  have h := entropy_bound_of_dimension (sampleFamily S x) (sampleFamily_nonempty S hS x)
    (by simp; omega : 0 < Fintype.card (Fin (l+l))) ht ht1.le hd'
  rwa [sampleFamily_card, hc] at h

end VapnikChervonenkis.EntropyProof

end

/- Complete checked body: BoundedProbability -/
section

open MeasureTheory Filter Topology
namespace VapnikChervonenkis.EntropyProof

variable {Ω : Type*} [MeasurableSpace Ω]

theorem unit_bounded_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)

theorem integral_le_cutoff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∫ x, f x ∂μ ≤ ε + μ.real {x | ε < f x} := by
  let A := {x | ε < f x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hi := (integrable_const (1 : ℝ) (μ := μ)).indicator hA
  calc
    ∫ x, f x ∂μ ≤ ∫ x, ε + A.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_mono (unit_bounded_integrable μ f hf hb) ((integrable_const ε).add hi)
      intro x
      change f x ≤ ε + A.indicator (1 : Ω → ℝ) x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Pi.one_apply]
        linarith [(hb x).2]
      · rw [Set.indicator_of_notMem hx, add_zero]
        exact le_of_not_gt hx
    _ = ε + μ.real A := by
      have hid : ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real A :=
        integral_indicator_one hA
      rw [integral_add (integrable_const ε) hi, hid]
      simp

variable {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)]

theorem measureReal_tendsto_zero (μ : ∀ n, Measure (Ωs n)) (A : ∀ n, Set (Ωs n))
    (h : Tendsto (fun n => μ n (A n)) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real (A n)) atTop (𝓝 0) := by
  simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp h

theorem integral_tendsto_zero_of_real_tails (μ : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (μ n)] (f : ∀ n, Ωs n → ℝ)
    (hf : ∀ n, Measurable (f n)) (hb : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1)
    (ht : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {x | ε < f n x}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (tendsto_order.mp (ht (ε / 2) (by linarith))).2 (ε / 2) (by linarith)
  filter_upwards [he] with n hn
  have hlo : 0 ≤ ∫ x, f n x ∂μ n := integral_nonneg (fun x => (hb n x).1)
  have hhi := integral_le_cutoff (μ n) (f n) (hf n) (hb n) (show 0 ≤ ε / 2 by linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end VapnikChervonenkis.EntropyProof
end

/- Complete checked body: CutoffAlgebra -/
section

namespace VapnikChervonenkis.EntropyProof

theorem logarithmic_cutoff {u c : ℝ} (hc : 0 < c) (N : ℕ)
    (hu : u ≤ 1) (hupper : u ≤ 2 * (N : ℝ) * Real.exp (-(2 * c))) :
    u ≤ 2 * Real.exp (-c) + Real.logb 2 (N : ℝ) / c := by
  have hL : 0 ≤ Real.logb 2 (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
  by_cases hsmall : Real.logb 2 (N : ℝ) ≤ c
  · have hN : (N : ℝ) ≤ Real.exp c := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp only [h, Nat.cast_zero]
        exact (Real.exp_pos c).le
      · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hl21 : Real.log 2 ≤ 1 := by
          have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          norm_num at hh
          exact hh
        have hh : Real.log (N : ℝ) ≤ c * Real.log 2 :=
          (div_le_iff₀ hl2).mp hsmall
        have he : Real.log (N : ℝ) ≤ c := by nlinarith
        calc
          (N : ℝ) = Real.exp (Real.log (N : ℝ)) := (Real.exp_log (by exact_mod_cast h)).symm
          _ ≤ Real.exp c := Real.exp_le_exp.mpr he
    calc
      u ≤ 2 * (N : ℝ) * Real.exp (-(2*c)) := hupper
      _ ≤ 2 * Real.exp c * Real.exp (-(2*c)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (Real.exp_pos _).le
      _ = 2 * Real.exp (-c) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 2 * Real.exp (-c) + Real.logb 2 (N : ℝ) / c :=
        le_add_of_nonneg_right (div_nonneg hL hc.le)
  · have hdiv : 1 ≤ Real.logb 2 (N : ℝ) / c := by
      apply (le_div_iff₀ hc).mpr
      linarith
    exact hu.trans (hdiv.trans (le_add_of_nonneg_left (by positivity)))

end VapnikChervonenkis.EntropyProof
end

/- Complete checked body: DeviationMeans -/
section

open MeasureTheory Filter Topology
namespace VapnikChervonenkis.EntropyProof

open VapnikChervonenkis.Entropy
variable {X : Type*} [MeasurableSpace X]

theorem maxDeviation_bounds (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (x : Fin l → X) :
    0 ≤ Shared.maxDeviation S P l x ∧ Shared.maxDeviation S P l x ≤ 1 := by
  classical
  rcases isEmpty_or_nonempty S with hs | hs
  · simp [Shared.maxDeviation, Real.iSup_of_isEmpty]
  · have hb : BddAbove (Set.range (fun A : S => |Shared.relFreq (A : Set X) x - P.real (A : Set X)|)) :=
      ⟨1, by rintro _ ⟨A, rfl⟩; exact aux_ns1_abs_le P A x⟩
    refine ⟨?_, ciSup_le (fun A => aux_ns1_abs_le P A x)⟩
    exact (abs_nonneg _).trans (le_ciSup hb (Classical.choice hs))

omit [MeasurableSpace X] in
theorem semiSampleDeviation_bounds (S : Set (Set X)) (l : ℕ) (x : Fin (l+l) → X) :
    0 ≤ Shared.semiSampleDeviation S l x ∧ Shared.semiSampleDeviation S l x ≤ 1 := by
  classical
  have ha (A : S) : |Shared.relFreq (A : Set X) (fun i : Fin l => x (Fin.castAdd l i)) -
      Shared.relFreq (A : Set X) (fun i : Fin l => x (Fin.natAdd l i))| ≤ 1 := by
    rw [abs_le]
    have h0 := aux_ns1_relFreq_nonneg (A : Set X) (fun i : Fin l => x (Fin.castAdd l i))
    have h1 := aux_ns1_relFreq_le_one (A : Set X) (fun i : Fin l => x (Fin.castAdd l i))
    have h2 := aux_ns1_relFreq_nonneg (A : Set X) (fun i : Fin l => x (Fin.natAdd l i))
    have h3 := aux_ns1_relFreq_le_one (A : Set X) (fun i : Fin l => x (Fin.natAdd l i))
    constructor <;> linarith
  rcases isEmpty_or_nonempty S with hs | hs
  · simp [Shared.semiSampleDeviation, Real.iSup_of_isEmpty]
  · have hb : BddAbove (Set.range (fun A : S =>
        |Shared.relFreq (A : Set X) (fun i : Fin l => x (Fin.castAdd l i)) -
          Shared.relFreq (A : Set X) (fun i : Fin l => x (Fin.natAdd l i))|)) :=
      ⟨1, by rintro _ ⟨A, rfl⟩; exact ha A⟩
    refine ⟨?_, ciSup_le ha⟩
    exact (abs_nonneg _).trans (le_ciSup hb (Classical.choice hs))

theorem semiSampleDeviation_integrable (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (hρ : Measurable (Shared.semiSampleDeviation S l)) :
    Integrable (Shared.semiSampleDeviation S l) (Measure.pi (fun _ : Fin (l+l) => P)) :=
  unit_bounded_integrable _ _ hρ (semiSampleDeviation_bounds S l)

theorem semisample_real_tail_tendsto (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hUC : ∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
      {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun l : ℕ => (Measure.pi (fun _ : Fin (l+l) => P)).real
      {x | ε < Shared.semiSampleDeviation S l x}) atTop (𝓝 0) := by
  have hp := measureReal_tendsto_zero (fun l : ℕ => Measure.pi (fun _ : Fin l => P))
    (fun l => {x | ε / 2 < Shared.maxDeviation S P l x}) (hUC (ε / 2) (by linarith))
  have hb (l : ℕ) : (Measure.pi (fun _ : Fin (l+l) => P)).real
      {x | ε < Shared.semiSampleDeviation S l x} ≤
      2 * (Measure.pi (fun _ : Fin l => P)).real {x | ε / 2 < Shared.maxDeviation S P l x} := by
    have h := VCEntropySource.necessity_step P S hπ (ε / 2) (by linarith) l
    rw [show 2 * (ε / 2) = ε by ring] at h
    nlinarith [sq_nonneg ((Measure.pi (fun _ : Fin l => P)).real
      {x | ε / 2 < Shared.maxDeviation S P l x})]
  apply squeeze_zero (fun _ => measureReal_nonneg) hb
  simpa using hp.const_mul 2

theorem expected_semisample_tendsto (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hUC : ∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
      {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0)) :
    Tendsto (fun l : ℕ => ∫ x, Shared.semiSampleDeviation S l x
      ∂(Measure.pi (fun _ : Fin (l+l) => P))) atTop (𝓝 0) :=
  integral_tendsto_zero_of_real_tails (fun l => Measure.pi (fun _ : Fin (l+l) => P))
    (fun l => Shared.semiSampleDeviation S l) hρ (semiSampleDeviation_bounds S)
    (semisample_real_tail_tendsto P S hπ hUC)

theorem permMeanRho_integrable (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (hρ : Measurable (Shared.semiSampleDeviation S l)) :
    Integrable (permMeanRho S l) (Measure.pi (fun _ : Fin (l+l) => P)) := by
  have hi (σ : Equiv.Perm (Fin (l+l))) : Integrable
      (fun x : Fin (l+l) → X => Shared.semiSampleDeviation S l (x ∘ σ))
        (Measure.pi (fun _ => P)) :=
    unit_bounded_integrable _ _
      (hρ.comp (VapnikChervonenkis.Inequality.aux_eq11_mp P (l+l) σ).measurable)
      (fun x => semiSampleDeviation_bounds S l (x ∘ σ))
  exact (integrable_finsetSum Finset.univ (fun σ _ => hi σ)).const_mul _

theorem permMeanRho_integral (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (hρ : Measurable (Shared.semiSampleDeviation S l)) :
    ∫ x, permMeanRho S l x ∂(Measure.pi (fun _ : Fin (l+l) => P)) =
      ∫ x, Shared.semiSampleDeviation S l x ∂(Measure.pi (fun _ : Fin (l+l) => P)) := by
  have hmp (σ : Equiv.Perm (Fin (l+l))) := VapnikChervonenkis.Inequality.aux_eq11_mp P (l+l) σ
  have hi (σ : Equiv.Perm (Fin (l+l))) : Integrable
      (fun x : Fin (l+l) → X => Shared.semiSampleDeviation S l (x ∘ σ))
        (Measure.pi (fun _ => P)) :=
    unit_bounded_integrable _ _ (hρ.comp (hmp σ).measurable)
      (fun x => semiSampleDeviation_bounds S l (x ∘ σ))
  have he (σ : Equiv.Perm (Fin (l+l))) :
      ∫ x, Shared.semiSampleDeviation S l (x ∘ σ) ∂(Measure.pi (fun _ : Fin (l+l) => P)) =
        ∫ x, Shared.semiSampleDeviation S l x ∂(Measure.pi (fun _ : Fin (l+l) => P)) := by
    have hh := integral_map (μ := Measure.pi (fun _ : Fin (l+l) => P))
      (hmp σ).measurable.aemeasurable hρ.aestronglyMeasurable
    rw [(hmp σ).map_eq] at hh
    exact hh.symm
  simp only [permMeanRho]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hi σ)]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos (l+l)).ne'), one_mul]

end VapnikChervonenkis.EntropyProof
end

/- Complete checked body: PermutationProbability -/
section

noncomputable section
open MeasureTheory Filter Topology
namespace VapnikChervonenkis.EntropyProof

open VapnikChervonenkis.Entropy
variable {X : Type*} [MeasurableSpace X]

open Classical in
noncomputable def badFraction (S : Set (Set X)) (ε : ℝ) (l : ℕ) (x : Fin (l+l) → X) : ℝ :=
  ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l+l)) =>
    ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l+l).factorial : ℝ)

omit [MeasurableSpace X] in
theorem badFraction_bounds (S : Set (Set X)) (ε : ℝ) (l : ℕ) (x : Fin (l+l) → X) :
    0 ≤ badFraction S ε l x ∧ badFraction S ε l x ≤ 1 := by
  classical
  unfold badFraction
  refine ⟨by positivity, ?_⟩
  apply div_le_one_of_le₀ _ (by positivity)
  have hc : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (l+l)) =>
      ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card ≤ (l+l).factorial := by
    simpa [Fintype.card_perm, Fintype.card_fin] using Finset.card_le_univ
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (l+l)) =>
        ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ)))
  exact_mod_cast hc

theorem badFraction_measurable (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (ε : ℝ) (l : ℕ) (hρ : Measurable (Shared.semiSampleDeviation S l)) :
    Measurable (badFraction S ε l) := by
  classical
  have he : badFraction S ε l = fun x =>
      (∑ σ : Equiv.Perm (Fin (l+l)),
        {x : Fin (l+l) → X | ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ)}.indicator
          (1 : (Fin (l+l) → X) → ℝ) x) / ((l+l).factorial : ℝ) := by
    funext x
    unfold badFraction
    apply congrArg (fun z : ℝ => z / ((l+l).factorial : ℝ))
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ)
    · simp [h]
    · simp [h]
  rw [he]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro σ _
  apply measurable_const.indicator
  exact measurableSet_le measurable_const
    (hρ.comp (VapnikChervonenkis.Inequality.aux_eq11_mp P (l+l) σ).measurable)

theorem badFraction_integrable (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (ε : ℝ) (l : ℕ) (hρ : Measurable (Shared.semiSampleDeviation S l)) :
    Integrable (badFraction S ε l) (Measure.pi (fun _ : Fin (l+l) => P)) :=
  unit_bounded_integrable _ _ (badFraction_measurable P S ε l hρ) (badFraction_bounds S ε l)

theorem entropy_log_integrable (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (n : ℕ)
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    Integrable (fun x : Fin n → X => Real.logb 2 (Shared.index S x : ℝ))
      (Measure.pi (fun _ => P)) := by
  apply Integrable.of_bound (aux_e3l_meas S hΔ n).aestronglyMeasurable n
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (aux_e3l_logb_nonneg S x)]
    exact aux_e3l_logb_le S x)

omit [MeasurableSpace X] in
theorem badFraction_entropy_bound (S : Set (Set X)) (ε : ℝ) (l : ℕ)
    (hε : 0 < ε) (hl : 1 ≤ l) (x : Fin (l+l) → X) :
    badFraction S ε l x ≤ 2 * Real.exp (-(ε ^ 2 * l / 16)) +
      Real.logb 2 (Shared.index S x : ℝ) / (ε ^ 2 * l / 16) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hc : 0 < ε ^ 2 * l / 16 := by positivity
  have hu := VCEntropySource.permutation_upper S ε l hl hε x
  have he : -(ε ^ 2 * (l : ℝ) / 8) = -(2 * (ε ^ 2 * l / 16)) := by ring
  rw [he] at hu
  exact logarithmic_cutoff hc (Shared.index S x) (badFraction_bounds S ε l x).2 hu

theorem semisample_probability_real_eq (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) :
    (Measure.pi (fun _ : Fin (l+l) => P)).real {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} =
      ∫ x, badFraction S ε l x ∂(Measure.pi (fun _ : Fin (l+l) => P)) := by
  have he := VCEntropySource.permutation_average P S hρ ε l
  change Measure.pi (fun _ : Fin (l+l) => P) {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} =
    ENNReal.ofReal (∫ x, badFraction S ε l x ∂(Measure.pi (fun _ : Fin (l+l) => P))) at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => (badFraction_bounds S ε l x).1))] at hr
  exact hr

theorem semisample_probability_upper (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 1 ≤ l) :
    (Measure.pi (fun _ : Fin (l+l) => P)).real {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} ≤
      2 * Real.exp (-(ε ^ 2 * l / 16)) + entropy S P (l+l) / (ε ^ 2 * l / 16) := by
  rw [semisample_probability_real_eq P S hρ ε l]
  have hi := entropy_log_integrable P S (l+l) hΔ
  calc
    ∫ x, badFraction S ε l x ∂(Measure.pi (fun _ : Fin (l+l) => P)) ≤
        ∫ x, (2 * Real.exp (-(ε ^ 2 * l / 16)) +
          Real.logb 2 (Shared.index S x : ℝ) / (ε ^ 2 * l / 16))
          ∂(Measure.pi (fun _ : Fin (l+l) => P)) :=
      integral_mono (badFraction_integrable P S ε l (hρ l))
        ((integrable_const _).add (hi.div_const _)) (badFraction_entropy_bound S ε l hε hl)
    _ = _ := by
      have he := integral_add (integrable_const (2 * Real.exp (-(ε ^ 2 * (l : ℝ) / 16))))
        (hi.div_const (ε ^ 2 * l / 16))
      rw [he, integral_div]
      simp [entropy]

end VapnikChervonenkis.EntropyProof
end
end

/- Complete checked body: NecessityLimit -/
section

open MeasureTheory Filter Topology
namespace VapnikChervonenkis.EntropyProof

open VapnikChervonenkis.Entropy
variable {X : Type*} [MeasurableSpace X]

theorem integrate_entropy_perm_bound (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (l : ℕ) (t : ℝ)
    (hfinite : ∀ x : Fin (l+l) → X,
      Real.logb 2 (Shared.index S x : ℝ) / (2 * (l : ℝ)) ≤
        Real.logb 2 (1+t) - Real.logb 2 t * (2 * permMeanRho S l x + 1 / (2 * (l : ℝ)))) :
    entropy S P (l+l) / (2 * (l : ℝ)) ≤
      Real.logb 2 (1+t) - Real.logb 2 t *
        (2 * (∫ x, Shared.semiSampleDeviation S l x ∂(Measure.pi (fun _ : Fin (l+l) => P))) +
          1 / (2 * (l : ℝ))) := by
  have hi := entropy_log_integrable P S (l+l) hΔ
  have hp := permMeanRho_integrable P S l (hρ l)
  have hj := (hp.const_mul 2).add (integrable_const (1 / (2 * (l : ℝ))))
  have hm := integral_mono (hi.div_const (2 * (l : ℝ)))
    ((integrable_const (Real.logb 2 (1+t))).sub (hj.const_mul (Real.logb 2 t))) hfinite
  have he1 :
      (∫ x, 2 * permMeanRho S l x + 1 / (2 * (l : ℝ))
        ∂(Measure.pi (fun _ : Fin (l+l) => P))) =
      2 * (∫ x, Shared.semiSampleDeviation S l x ∂(Measure.pi (fun _ : Fin (l+l) => P))) +
        1 / (2 * (l : ℝ)) := by
    have he := integral_add (hp.const_mul 2) (integrable_const (1 / (2 * (l : ℝ))))
    rw [he, integral_const_mul, permMeanRho_integral P S l (hρ l)]
    simp
  have he2 :
      (∫ x, Real.logb 2 (1+t) - Real.logb 2 t *
        (2 * permMeanRho S l x + 1 / (2 * (l : ℝ)))
        ∂(Measure.pi (fun _ : Fin (l+l) => P))) =
      Real.logb 2 (1+t) - Real.logb 2 t *
        (2 * (∫ x, Shared.semiSampleDeviation S l x ∂(Measure.pi (fun _ : Fin (l+l) => P))) +
          1 / (2 * (l : ℝ))) := by
    have he := integral_sub (integrable_const (Real.logb 2 (1+t))) (hj.const_mul (Real.logb 2 t))
    simp only [Pi.add_apply] at he
    rw [he, integral_const_mul, he1]
    simp
  simp only [Pi.sub_apply, Pi.add_apply] at hm
  rw [integral_div, he2] at hm
  exact hm

theorem doubled_sample_atTop : Tendsto (fun l : ℕ => l+l) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  exact ha.trans (Nat.le_add_right a a)

theorem necessity_of_entropy_perm_bound (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (hfinite : ∀ l : ℕ, 1 ≤ l → ∀ t : ℝ, 0 < t → t < 1 → ∀ x : Fin (l+l) → X,
      Real.logb 2 (Shared.index S x : ℝ) / (2 * (l : ℝ)) ≤
        Real.logb 2 (1+t) - Real.logb 2 t * (2 * permMeanRho S l x + 1 / (2 * (l : ℝ))))
    (hUC : ∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
      {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0)) :
    Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 0) := by
  obtain ⟨c, hc0, _, hclim⟩ := VCEntropySource.entropy_limit P S hΔ
  have hrho := expected_semisample_tendsto P S hπ hρ hUC
  have hcEven : Tendsto (fun l : ℕ => entropy S P (l+l) / (2 * (l : ℝ))) atTop (𝓝 c) := by
    simpa only [Function.comp_def, Nat.cast_add, two_mul] using hclim.comp doubled_sample_atTop
  have hinv : Tendsto (fun l : ℕ => 1 / (2 * (l : ℝ))) atTop (𝓝 0) := by
    simpa only [one_div, div_eq_mul_inv, mul_inv_rev, mul_comm, zero_mul, one_mul] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have hcle (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : c ≤ Real.logb 2 (1+t) := by
    have hlim := (tendsto_const_nhds (x := Real.logb 2 (1+t))).sub
      (((hrho.const_mul 2).add hinv).const_mul (Real.logb 2 t))
    simp only [mul_zero, add_zero, sub_zero] at hlim
    apply le_of_tendsto_of_tendsto hcEven hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with l hl
    exact integrate_entropy_perm_bound P S hρ hΔ l t (hfinite l hl t ht ht1)
  let a := fun k : ℕ => 1 / ((k : ℝ) + 2)
  have ha0 (k : ℕ) : 0 < a k := by dsimp only [a]; positivity
  have ha1 (k : ℕ) : a k < 1 := by
    dsimp only [a]
    apply (div_lt_one₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have ha : Tendsto a atTop (𝓝 0) := by
    change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  have hlog : Tendsto (fun k => Real.logb 2 (1 + a k)) atTop (𝓝 0) := by
    have he := (Real.continuousAt_logb (b := 2) (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      (by simpa using ha.const_add 1)
    simpa only [Real.logb_one, Function.comp_def] using he
  have hc1 : c ≤ 0 := ge_of_tendsto' hlog (fun k => hcle (a k) (ha0 k) (ha1 k))
  have he : c = 0 := le_antisymm hc1 hc0
  rwa [he] at hclim

end VapnikChervonenkis.EntropyProof
end

/- Complete checked body: SufficiencyLimit -/
section

open MeasureTheory Filter Topology
namespace VapnikChervonenkis.EntropyProof

open VapnikChervonenkis.Entropy
variable {X : Type*} [MeasurableSpace X]

theorem uniform_convergence_of_entropy (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x))
    (hH : Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
      {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0) := by
  intro ε hε
  apply (ENNReal.tendsto_toReal_zero_iff (fun l => measure_ne_top _ _)).mp
  change Tendsto (fun l : ℕ => (Measure.pi (fun _ : Fin l => P)).real
    {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0)
  have hnat : Tendsto (fun l : ℕ => ε ^ 2 * (l : ℝ) / 16) atTop atTop := by
    have ht : Tendsto (fun l : ℕ => (ε ^ 2 / 16) * (l : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    exact ht.congr' (Eventually.of_forall (fun l => by ring))
  have hExp : Tendsto (fun l : ℕ => 2 * Real.exp (-(ε ^ 2 * l / 16))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hnat).const_mul 2
  have hid (l : ℕ) : entropy S P (l+l) / (ε ^ 2 * l / 16) =
      (32 / ε ^ 2) * (entropy S P (l+l) / ((l+l : ℕ) : ℝ)) := by
    push_cast
    by_cases hl : (l : ℝ) = 0
    · simp [hl]
    · field_simp [hl, hε.ne']
      ring
  have hR : Tendsto (fun l : ℕ => entropy S P (l+l) / (ε ^ 2 * l / 16)) atTop (𝓝 0) := by
    have ht := (hH.comp doubled_sample_atTop).const_mul (32 / ε ^ 2)
    simp only [Function.comp_def, mul_zero] at ht
    exact ht.congr' (Eventually.of_forall (fun l => (hid l).symm))
  have hlim : Tendsto (fun l : ℕ =>
      2 * (2 * Real.exp (-(ε ^ 2 * l / 16)) + entropy S P (l+l) / (ε ^ 2 * l / 16)))
      atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hExp.add hR).const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  have hlarge : ∀ᶠ l : ℕ in atTop, 2 / ε ^ 2 ≤ (l : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun l : ℕ => (l : ℝ)) atTop atTop)
      (eventually_ge_atTop (2 / ε ^ 2))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge] with l hl hb
  have hs := VCEntropySource.symmetrization P S hS hπ hρ ε l hε hb
  have hr := ENNReal.toReal_mono (by finiteness) hs
  have hreal : (Measure.pi (fun _ : Fin l => P)).real {x | ε < Shared.maxDeviation S P l x} ≤
      2 * (Measure.pi (fun _ : Fin (l+l) => P)).real
        {x | ε / 2 ≤ Shared.semiSampleDeviation S l x} := by
    simpa [Measure.real, ENNReal.toReal_mul] using hr
  exact hreal.trans (mul_le_mul_of_nonneg_left
    (semisample_probability_upper P S hρ hΔ ε l hε hl) (by norm_num))

end VapnikChervonenkis.EntropyProof
end

/- Complete checked body: EntropyRoot -/
section

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

/-- **Theorem 4** of Vapnik and Chervonenkis (1971), p. 275: a necessary and sufficient condition
for the relative frequencies to converge (in probability) to the probabilities uniformly over the
class of events `S`, i.e. `P{π^(l) > ε} → 0` for every `ε > 0` (p. 265), is that (21)
`lim_{l→∞} H^S(l)/l = 0`. `hS`, `hπ`, `hρ`, `hΔ` are the paper's standing assumptions: the events
of `S` are measurable (p. 264), and `π^(l)` (p. 265), `ρ^(l)` (p. 268) and the index `Δ^S`
(p. 273) are measurable functions of the sample. -/
theorem theorem4_entropy_criterion {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
        {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0))
      ↔ Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro hUC
    by_cases hnonempty : S.Nonempty
    · exact VapnikChervonenkis.EntropyProof.necessity_of_entropy_perm_bound P S hπ hρ hΔ
        (fun l hl t ht ht1 x => VapnikChervonenkis.EntropyProof.pointwise_entropy_bound
          S hnonempty l hl x t ht ht1) hUC
    · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
      subst S
      simp [entropy, Shared.index]
  · exact VapnikChervonenkis.EntropyProof.uniform_convergence_of_entropy P S hS hπ hρ hΔ


end VapnikChervonenkis.Entropy

end

open MeasureTheory Filter Topology VapnikChervonenkis VapnikChervonenkis.Entropy

theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (Shared.semiSampleDeviation S l))
    (hΔ : ∀ l : ℕ, Measurable (fun x : Fin l → X => Shared.index S x)) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun l : ℕ => Measure.pi (fun _ : Fin l => P)
        {x | ε < Shared.maxDeviation S P l x}) atTop (𝓝 0))
      ↔ Tendsto (fun l : ℕ => entropy S P l / (l : ℝ)) atTop (𝓝 0) := by
  exact VapnikChervonenkis.Entropy.theorem4_entropy_criterion P S hS hπ hρ hΔ

#print axioms VapnikChervonenkis.Entropy.theorem4_entropy_criterion
#print axioms solution
