-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.theorem2_uniform_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:05:20.571082+00:00
-- url     : https://prove2.me/submissions/ef24cc53-62d5-4d47-a17a-f0d8b369d86a

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

set_option autoImplicit false

open Finset in
lemma vc47_hoeff_count {l : ℕ} (hl : 1 ≤ l) (c : Fin l → ℝ) (hc : ∀ i, |c i| ≤ 1) {t : ℝ}
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

/-- Swap the coordinates where `σ` is `true`. -/
def vc47_swap {X : Type*} {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → X) × (Fin m → X)) :
    (Fin m → X) × (Fin m → X) :=
  (fun i => if σ i then p.2 i else p.1 i, fun i => if σ i then p.1 i else p.2 i)

open MeasureTheory in
lemma vc47_swap_mp {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Fin m → Bool) :
    MeasurePreserving (vc47_swap σ)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D))
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow X X (Fin m)
  have hE : MeasurePreserving E (Measure.pi fun _ : Fin m => D.prod D)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) :=
    measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ => D) (fun _ => D)
  let f : Fin m → X × X → X × X := fun i => if σ i then Prod.swap else id
  have hf : ∀ i, MeasurePreserving (f i) (D.prod D) (D.prod D) := by
    intro i
    by_cases h : σ i
    · simp only [f, h, if_true]; exact Measure.measurePreserving_swap
    · simp only [f, h]; exact MeasurePreserving.id _
  have hF := measurePreserving_pi (fun _ : Fin m => D.prod D) (fun _ : Fin m => D.prod D) hf
  have hcomp := hE.comp (hF.comp hE.symm)
  have heq : vc47_swap σ = E ∘ ((fun a i => f i (a i)) ∘ E.symm) := by
    funext p
    ext i
    · by_cases h : σ i <;> simp [vc47_swap, f, h, E, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
    · by_cases h : σ i <;> simp [vc47_swap, f, h, E, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow]
  rw [heq]; exact hcomp

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

open VapnikChervonenkis.Shared in
lemma vc47_index_le_growth {X : Type*} (S : Set (Set X)) (r : ℕ) (x : Fin r → X) :
    index S x ≤ growthFunction S r := by
  classical
  unfold growthFunction
  refine le_ciSup (f := fun x : Fin r → X => index S x) ?_ x
  refine ⟨2 ^ r, ?_⟩
  rintro _ ⟨y, rfl⟩
  show index S y ≤ 2 ^ r
  unfold index
  refine (Finset.card_filter_le _ _).trans ?_
  simp

open VapnikChervonenkis.Shared in
lemma vc47_count {X : Type*} (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l) {ε : ℝ} (hε : 0 < ε)
    (p : (Fin l → X) × (Fin l → X)) :
    ((Finset.univ.filter fun σ : Fin l → Bool =>
        ε / 2 < semiSampleDeviation S l
          (Fin.append (vc47_swap σ p).1 (vc47_swap σ p).2)).card : ℝ)
      ≤ (growthFunction S (l + l) : ℝ)
        * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl1
  set x : Fin (l + l) → X := Fin.append p.1 p.2 with hx
  set T : Finset (Finset (Fin (l + l))) :=
    Finset.univ.filter (fun t : Finset (Fin (l + l)) => ∃ A ∈ S, ∀ i, i ∈ t ↔ x i ∈ A) with hT
  have hTcard : T.card = index S x := by
    unfold index
    first | rfl | congr
  set c : Finset (Fin (l + l)) → Fin l → ℝ := fun t i =>
    (if Fin.castAdd l i ∈ t then (1 : ℝ) else 0) - (if Fin.natAdd l i ∈ t then (1 : ℝ) else 0)
    with hc
  have hc1 : ∀ t i, |c t i| ≤ 1 := by
    intro t i
    simp only [hc]
    rw [abs_le]
    by_cases h1 : Fin.castAdd l i ∈ t <;> by_cases h2 : Fin.natAdd l i ∈ t <;>
      simp only [h1, h2, if_true, if_false, ↓reduceIte] <;> norm_num
  set Bad : Finset (Fin (l + l)) → Finset (Fin l → Bool) := fun t =>
    Finset.univ.filter (fun σ : Fin l → Bool =>
      (l : ℝ) * (ε / 2) ≤ |∑ i, (if σ i then (1 : ℝ) else -1) * c t i|) with hBad
  have hBadcard : ∀ t, ((Bad t).card : ℝ) ≤ 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) := by
    intro t
    have hexp : (l * (ε / 2)) ^ 2 / (2 * (l : ℝ)) = ε ^ 2 * l / 8 := by
      field_simp; ring
    have hnn : 0 ≤ (l : ℝ) * (ε / 2) := by positivity
    have h1 := vc47_hoeff_count hl1 (c t) (hc1 t) hnn
    have h2 := vc47_hoeff_count hl1 (fun i => - c t i)
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
  have hsubset : (Finset.univ.filter fun σ : Fin l → Bool =>
        ε / 2 < semiSampleDeviation S l
          (Fin.append (vc47_swap σ p).1 (vc47_swap σ p).2)) ⊆ T.biUnion Bad := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [vc47_rho_eq S l (vc47_swap σ p)] at hσ
    have hne : Nonempty S := by
      by_contra h
      rw [not_nonempty_iff] at h
      rw [Real.iSup_of_isEmpty] at hσ
      linarith
    obtain ⟨A, hA⟩ := exists_lt_of_lt_ciSup hσ
    refine Finset.mem_biUnion.2 ⟨Finset.univ.filter (fun j : Fin (l + l) => x j ∈ (A : Set X)), ?_, ?_⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨A, A.2, fun i => by simp⟩
    · simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
      set tA : Finset (Fin (l + l)) := Finset.univ.filter (fun j : Fin (l + l) => x j ∈ (A : Set X))
        with htA
      have hmem_l : ∀ i : Fin l, Fin.castAdd l i ∈ tA ↔ p.1 i ∈ (A : Set X) := by
        intro i
        simp only [htA, Finset.mem_filter, Finset.mem_univ, true_and, hx, Fin.append_left]
      have hmem_r : ∀ i : Fin l, Fin.natAdd l i ∈ tA ↔ p.2 i ∈ (A : Set X) := by
        intro i
        simp only [htA, Finset.mem_filter, Finset.mem_univ, true_and, hx, Fin.append_right]
      have hci : ∀ i : Fin l, c tA i
          = (if p.1 i ∈ (A : Set X) then (1 : ℝ) else 0) - (if p.2 i ∈ (A : Set X) then (1 : ℝ) else 0) := by
        intro i
        simp only [hc, hmem_l i, hmem_r i]
      have hdiff : VapnikChervonenkis.Shared.relFreq (A : Set X) (vc47_swap σ p).1
          - VapnikChervonenkis.Shared.relFreq (A : Set X) (vc47_swap σ p).2
          = - (∑ i, (if σ i then (1 : ℝ) else -1) * c tA i) / l := by
        unfold VapnikChervonenkis.Shared.relFreq
        rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← sub_div,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hci i]
        by_cases h : σ i <;> by_cases h1 : p.1 i ∈ (A : Set X) <;>
          by_cases h2 : p.2 i ∈ (A : Set X) <;>
          simp [vc47_swap, h, h1, h2]
      rw [hdiff, abs_div, abs_neg, abs_of_pos hlpos, lt_div_iff₀ hlpos] at hA
      linarith
  have hcard1 := Finset.card_le_card hsubset
  have hcard2 := hcard1.trans Finset.card_biUnion_le
  have hcard3 : ((Finset.univ.filter fun σ : Fin l → Bool =>
        ε / 2 < semiSampleDeviation S l
          (Fin.append (vc47_swap σ p).1 (vc47_swap σ p).2)).card : ℝ)
      ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := by
    exact_mod_cast hcard2
  calc _ ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := hcard3
    _ ≤ ∑ _t ∈ T, 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) :=
        Finset.sum_le_sum fun t _ => hBadcard t
    _ = (T.card : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hTcard]
        exact_mod_cast vc47_index_le_growth S (l + l) x

open MeasureTheory VapnikChervonenkis.Shared in
lemma vc47_perm {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l)
    (hρ : Measurable (semiSampleDeviation S l)) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P))
        {p | ε / 2 < semiSampleDeviation S l (Fin.append p.1 p.2)}
      ≤ ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
  classical
  set μ2 := (Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P) with hμ2
  set B : Set ((Fin l → X) × (Fin l → X)) :=
    {p | ε / 2 < semiSampleDeviation S l (Fin.append p.1 p.2)} with hBdef
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (hρ.comp (vc47_append_meas l))
  have hswapm : ∀ σ : Fin l → Bool, Measurable (vc47_swap (X := X) σ) :=
    fun σ => (vc47_swap_mp P σ).measurable
  have h1 : ∀ σ : Fin l → Bool, μ2 ((vc47_swap σ) ⁻¹' B) = μ2 B :=
    fun σ => (vc47_swap_mp P σ).measure_preimage hB.nullMeasurableSet
  have hsum : ∫⁻ p, ((Finset.univ.filter fun σ : Fin l → Bool =>
        p ∈ (vc47_swap σ) ⁻¹' B).card : ENNReal) ∂μ2 = ∑ _σ : Fin l → Bool, μ2 B := by
    have : ∀ p, ((Finset.univ.filter fun σ : Fin l → Bool =>
        p ∈ (vc47_swap σ) ⁻¹' B).card : ENNReal)
        = ∑ σ : Fin l → Bool, ((vc47_swap σ) ⁻¹' B).indicator (fun _ => (1 : ENNReal)) p := by
      intro p
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : p ∈ (vc47_swap σ) ⁻¹' B <;> simp [Set.indicator_apply, h]
    simp_rw [this]
    rw [lintegral_finset_sum _ (fun σ _ => measurable_const.indicator ((hswapm σ) hB))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lintegral_indicator_const ((hswapm σ) hB), one_mul, h1 σ]
  set K : ℝ := (growthFunction S (l + l) : ℝ)
    * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) with hK
  have hint : ∫⁻ p, ((Finset.univ.filter fun σ : Fin l → Bool =>
        p ∈ (vc47_swap σ) ⁻¹' B).card : ENNReal) ∂μ2 ≤ ENNReal.ofReal K := by
    calc _ ≤ ∫⁻ _p, ENNReal.ofReal K ∂μ2 := by
          refine lintegral_mono fun p => ?_
          have := vc47_count S l hl1 hε p
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal this
      _ = ENNReal.ofReal K := by simp
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at hint
  have hK2 : ENNReal.ofReal K = (2 : ENNReal) ^ l *
      ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
    have : K = (2 : ℝ) ^ l * (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
      rw [hK]; ring
    rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [hK2] at hint
  push_cast at hint
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by simp)).1 hint

open VapnikChervonenkis.Shared in
theorem solution {X : Type*} [MeasurableSpace X] (P : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure P] (S : Set (Set X)) (hS : ∀ A ∈ S, MeasurableSet A)
    (hπ : ∀ l, Measurable (VapnikChervonenkis.Shared.maxDeviation S P l))
    (hρ : ∀ l, Measurable (VapnikChervonenkis.Shared.semiSampleDeviation S l))
    (ε : ℝ) (l : ℕ) (hε : 0 < ε) (hl : 2 / ε ^ 2 ≤ (l : ℝ)) :
    MeasureTheory.Measure.pi (fun _ : Fin l => P)
        {x | ε < VapnikChervonenkis.Shared.maxDeviation S P l x}
      ≤ ENNReal.ofReal (4 * (VapnikChervonenkis.Shared.growthFunction S (2 * l) : ℝ)
          * Real.exp (-(ε ^ 2 * l / 8))) := by
  have hl1 : 1 ≤ l := by
    have : (0 : ℝ) < l := lt_of_lt_of_le (by positivity) hl
    exact_mod_cast this
  have h1 := vc47_symm P S hS l (hπ l) (hρ l) hε hl
  have h2 := vc47_perm P S l hl1 (hρ l) hε
  rw [two_mul l]
  refine h1.trans ?_
  calc _ ≤ 2 * ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) :=
        by gcongr
    _ = _ := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
