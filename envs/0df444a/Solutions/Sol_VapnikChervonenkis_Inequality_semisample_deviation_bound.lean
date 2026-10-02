-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.semisample_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:57:17.914691+00:00
-- url     : https://prove2.me/submissions/a84621db-7999-4994-8a31-9f122b0cc9b7

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

open MeasureTheory in
lemma cfb_map_append {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (l : ℕ) :
    ((Measure.pi fun _ : Fin l => P).prod (Measure.pi fun _ : Fin l => P)).map
        (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X))
      = Measure.pi (fun _ : Fin (l + l) => P) := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (vc47_append_meas l) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin l → X) × (Fin l → X) => (Fin.append p.1 p.2 : Fin (l + l) → X)) ⁻¹'
      Set.univ.pi s = (Set.univ.pi fun i => s (Fin.castAdd l i)) ×ˢ
        (Set.univ.pi fun i => s (Fin.natAdd l i)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      exact ⟨fun i => by have := h (Fin.castAdd l i); rwa [Fin.append_left] at this,
        fun i => by have := h (Fin.natAdd l i); rwa [Fin.append_right] at this⟩
    · rintro ⟨h1, h2⟩ j
      induction j using Fin.addCases with
      | left i => rw [Fin.append_left]; exact h1 i
      | right i => rw [Fin.append_right]; exact h2 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

open MeasureTheory VapnikChervonenkis.Shared in
lemma cfb_strict {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l)
    (hρ : Measurable (semiSampleDeviation S l)) {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | δ / 2 < semiSampleDeviation S l x}
      ≤ ENNReal.ofReal (2 * (growthFunction S (l + l) : ℝ) * Real.exp (-(δ ^ 2 * l / 8))) := by
  have hm : MeasurableSet {x : Fin (l + l) → X | δ / 2 < semiSampleDeviation S l x} :=
    measurableSet_lt measurable_const hρ
  rw [← cfb_map_append P l, Measure.map_apply (vc47_append_meas l) hm]
  exact vc47_perm P S l hl1 hρ hδ

open MeasureTheory Filter Topology in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hρ : ∀ l, Measurable (VapnikChervonenkis.Shared.semiSampleDeviation S l)) (ε : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hε : 0 < ε) :
    Measure.pi (fun _ : Fin (l + l) => P) {x | ε / 2 ≤ VapnikChervonenkis.Shared.semiSampleDeviation S l x}
      ≤ ENNReal.ofReal (2 * (VapnikChervonenkis.Shared.growthFunction S (2 * l) : ℝ) * Real.exp (-(ε ^ 2 * l / 8))) := by
  rw [two_mul l]
  set f : ℝ → ENNReal := fun δ => ENNReal.ofReal
    (2 * (VapnikChervonenkis.Shared.growthFunction S (l + l) : ℝ) * Real.exp (-(δ ^ 2 * l / 8)))
    with hf
  have hcont : Continuous f := by
    refine ENNReal.continuous_ofReal.comp ?_
    fun_prop
  have htend : Tendsto f (𝓝[<] ε) (𝓝 (f ε)) :=
    (hcont.tendsto ε).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  have hmem : Set.Ioo 0 ε ∈ 𝓝[<] ε := Ioo_mem_nhdsLT hε
  filter_upwards [hmem] with δ hδ
  refine le_trans (measure_mono ?_) (cfb_strict P S l hl (hρ l) hδ.1)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  linarith [hδ.2]
