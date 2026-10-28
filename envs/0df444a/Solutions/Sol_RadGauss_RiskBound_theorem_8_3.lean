-- Prove2me | solution 3 for RadGauss.RiskBound.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:42:59.240057+00:00
-- url     : https://prove2.me/submissions/6ca0be0a-e6de-46b3-85ac-00b79a997b55

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity
import Definitions.Def_RadGauss_RiskBound_uniformDeviation
import Definitions.Def_RadGauss_RiskBound_phiTildeComp
import Theorems.Thm_RadGauss_RiskBound_mcdiarmid_inequality

-- carved verbatim out of submission e1483903-396e-4d6b-a71d-075cee0a7dd6, lines 767-787

section
open MeasureTheory
open RadGauss
open RadGauss.RiskBound

theorem rk_phi_bound {X Y A : Type*} [Zero A] (φ : Y → A → ℝ)
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1) (F : Set (X → A)) (h : X × Y → ℝ)
    (hh : h ∈ phiTildeComp φ F) (z : X × Y) : |h z| ≤ 1 := by
  obtain ⟨f, _, rfl⟩ := hh
  have h1 := hφ01 z.2 (f z.1); have h2 := hφ01 z.2 0
  rw [abs_le]; constructor <;> linarith

theorem rk_int_bound {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (h : Z → ℝ) (hb : ∀ z, |h z| ≤ 1) : |∫ z, h z ∂P| ≤ 1 := by
  have : ‖∫ z, h z ∂P‖ ≤ 1 := by
    refine (norm_integral_le_of_norm_le_const (C := 1) ?_).trans (by simp)
    exact ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hb z
  simpa [Real.norm_eq_abs] using this

theorem rk_emp_bound {Z : Type*} {n : ℕ} (S : Fin n → Z) (h : Z → ℝ) (hb : ∀ z, |h z| ≤ 1) :
    |empMean S h| ≤ 1 := by
  unfold empMean
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
  have : |∑ i, h (S i)| ≤ n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |h (S i)| ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb _
      _ = n := by simp
  calc 1 / (n:ℝ) * |∑ i, h (S i)| ≤ 1 / n * n := mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 := by field_simp

theorem rk_emp_update {Z : Type*} {n : ℕ} (S : Fin n → Z) (i : Fin n) (z : Z) (h : Z → ℝ)
    (hb : ∀ z, |h z| ≤ 1) :
    |empMean S h - empMean (Function.update S i z) h| ≤ 2 / n := by
  unfold empMean
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [Function.update_self]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / n)]
    have : |h (S i) - h z| ≤ 2 := by
      have := hb (S i); have := hb z
      rw [abs_le] at *; constructor <;> linarith
    calc 1 / (n:ℝ) * |h (S i) - h z| ≤ 1 / n * 2 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 / n := by ring
  · intro j _ hj; rw [Function.update_of_ne hj]; ring
  · simp

theorem rk_dev_bound {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {n : ℕ} (S : Fin n → Z) (h : Z → ℝ) (hb : ∀ z, |h z| ≤ 1) :
    |(∫ w, h w ∂P) - empMean S h| ≤ 2 := by
  have := rk_int_bound P h hb; have := rk_emp_bound S h hb
  rw [abs_le] at *; constructor <;> linarith

theorem rk_supDev_bdd {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {n : ℕ} (G : Set (Z → ℝ)) (hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1) (S : Fin n → Z) :
    BddAbove (Set.range fun h : G => (∫ w, (h : Z → ℝ) w ∂P) - empMean S (h : Z → ℝ)) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact (abs_le.mp (rk_dev_bound P S h (hG h h.2))).2

theorem rk_supDev_le {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {n : ℕ} (G : Set (Z → ℝ)) (hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1) (S : Fin n → Z) (i : Fin n) (z : Z) :
    supDev P n G S ≤ supDev P n G (Function.update S i z) + 2 / n := by
  rcases isEmpty_or_nonempty G with hE | hne
  · unfold supDev; simp [Real.iSup_of_isEmpty]; positivity
  unfold supDev
  refine ciSup_le fun h => ?_
  have h1 := le_ciSup (rk_supDev_bdd P G hG (Function.update S i z)) h
  have h2 := rk_emp_update S i z h (hG h h.2)
  have := (abs_le.mp h2).1
  try simp only at h1
  linarith

theorem rk_supDev_diff {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {n : ℕ} (G : Set (Z → ℝ)) (hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1) (S : Fin n → Z) (i : Fin n) (z : Z) :
    |supDev P n G S - supDev P n G (Function.update S i z)| ≤ 2 / n := by
  rw [abs_le]
  have h1 := rk_supDev_le P G hG S i z
  have h2 := rk_supDev_le P G hG (Function.update S i z) i (S i)
  rw [Function.update_idem, Function.update_eq_self] at h2
  constructor <;> linarith

theorem rk_step_gen {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (G : Set (Z → ℝ)) (hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1) (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n G)) :
    (Measure.pi fun _ : Fin n => P)
      {S | ¬ (supDev P n G S ≤
          (∫ S', supDev P n G S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (2 * Real.log (2 / δ) / n))}
      ≤ ENNReal.ofReal (δ / 2) := by
  set E := ∫ S', supDev P n G S' ∂(Measure.pi fun _ : Fin n => P) with hE
  set ε := Real.sqrt (2 * Real.log (2 / δ) / n) with hε
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : ε ^ 2 = 2 * Real.log (2 / δ) / n := Real.sq_sqrt (by positivity)
  have hsub : {S : Fin n → Z | ¬ (supDev P n G S ≤ E + ε)} ⊆ {S | ε ≤ supDev P n G S - E} := by
    intro S hS; simp only [Set.mem_setOf_eq] at *; push_neg at hS; linarith
  refine (measure_mono hsub).trans ?_
  have hm := RadGauss.RiskBound.mcdiarmid_inequality n (fun _ => P) (supDev P n G) hsup (fun _ => 2 / n)
    (fun i S z => rk_supDev_diff P G hG S i z) ε hε0
  refine hm.trans (le_of_eq ?_)
  congr 1
  have hsum : (∑ _i : Fin n, (2 / (n:ℝ)) ^ 2 : ℝ) = (4:ℝ) / n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp; ring
  rw [hsum]
  have : -2 * ε ^ 2 / (4 / n) = - Real.log (2 / δ) := by
    rw [hε2]; field_simp; ring
  rw [this, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

theorem rk_phi_meas {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A] (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f) (h : X × Y → ℝ)
    (hh : h ∈ phiTildeComp φ F) : Measurable h := by
  obtain ⟨f, hf, rfl⟩ := hh
  have m1 : Measurable (fun z : X × Y => φ z.2 (f z.1)) :=
    hφ.comp (measurable_snd.prodMk ((hF f hf).comp measurable_fst))
  have m2 : Measurable (fun z : X × Y => φ z.2 0) :=
    hφ.comp (measurable_snd.prodMk measurable_const)
  exact m1.sub m2

theorem rk_bdd_integrable {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (g : Z → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ z, |g z| ≤ C) : Integrable g μ :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hb z)

theorem rk_emp_meas {Z : Type*} [MeasurableSpace Z] (n : ℕ) (g : Z → ℝ) (hg : Measurable g) :
    Measurable (fun S : Fin n → Z => empMean S g) := by
  unfold empMean
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)

theorem rk_int_emp {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (g : Z → ℝ) (hg : Measurable g) (C : ℝ) (hb : ∀ z, |g z| ≤ C) :
    ∫ S, empMean S g ∂(Measure.pi fun _ : Fin n => P) = ∫ z, g z ∂P := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold empMean
  rw [integral_const_mul, integral_finset_sum]
  · have : ∀ i : Fin n, ∫ S, g (S i) ∂(Measure.pi fun _ : Fin n => P) = ∫ z, g z ∂P := by
      intro i
      have h1 := integral_map (μ := Measure.pi fun _ : Fin n => P) (φ := Function.eval i)
        (measurable_pi_apply i).aemeasurable (f := g)
        (by rw [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq]
            exact hg.aestronglyMeasurable)
      rw [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq] at h1
      exact h1.symm
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact rk_bdd_integrable _ _ (hg.comp (measurable_pi_apply i)) C (fun S => hb _)

theorem rk_emp_add {Z : Type*} {n : ℕ} (S : Fin n → Z) (g k : Z → ℝ) :
    empMean S (fun z => g z + k z) = empMean S g + empMean S k := by
  unfold empMean; rw [Finset.sum_add_distrib]; ring

theorem combined_bound_core {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F))) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ ((∫ z, L z.2 (f z.1) ∂P) ≤
          empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (8 * Real.log (2 / δ) / n))}
      ≤ ENNReal.ofReal δ := by
  set G := phiTildeComp φ F with hGdef
  have hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1 := fun h hh z => rk_phi_bound φ hφ01 F h hh z
  set πn := Measure.pi fun _ : Fin n => P with hπn
  set Es := ∫ S', supDev P n G S' ∂πn with hEs
  set ε := Real.sqrt (2 * Real.log (2 / δ) / n) with hε
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : ε ^ 2 = 2 * Real.log (2 / δ) / n := Real.sq_sqrt (by positivity)
  have h8 : Real.sqrt (8 * Real.log (2 / δ) / n) = 2 * ε := by
    rw [show 8 * Real.log (2 / δ) / n = (2 * ε) ^ 2 by rw [mul_pow, hε2]; ring]
    exact Real.sqrt_sq (by positivity)
  set φ0 : X × Y → ℝ := fun z => φ z.2 0 with hφ0
  have hφ0m : Measurable φ0 := hφ.comp (measurable_snd.prodMk measurable_const)
  have hφ0b : ∀ z, |φ0 z| ≤ 1 := fun z => by
    have := hφ01 z.2 0; rw [abs_le]; constructor <;> linarith
  set E0 := ∫ z, φ0 z ∂P with hE0
  have hsub : {S : Fin n → X × Y | ∃ f ∈ F, ¬ ((∫ z, L z.2 (f z.1) ∂P) ≤
          empMean S (fun z => φ z.2 (f z.1)) + Es + Real.sqrt (8 * Real.log (2 / δ) / n))}
      ⊆ {S | ¬ (supDev P n G S ≤ Es + ε)} ∪
        {S | ε ≤ (fun S => - empMean S φ0) S - ∫ S', (fun S => - empMean S φ0) S' ∂πn} := by
    rintro S ⟨f, hf, hne⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [integral_neg, rk_int_emp P n hn φ0 hφ0m 1 hφ0b] at h2
    apply hne
    set h : X × Y → ℝ := fun z => φ z.2 (f z.1) - φ z.2 0 with hhdef
    have hhG : h ∈ G := ⟨f, hf, rfl⟩
    have hhm : Measurable h := rk_phi_meas φ hφ F hF h hhG
    have hfm : Measurable (fun z : X × Y => φ z.2 (f z.1)) :=
      hφ.comp (measurable_snd.prodMk ((hF f hf).comp measurable_fst))
    have hLm : Measurable (fun z : X × Y => L z.2 (f z.1)) :=
      hL.comp (measurable_snd.prodMk ((hF f hf).comp measurable_fst))
    have hφfb : ∀ z : X × Y, |φ z.2 (f z.1)| ≤ 1 := fun z => by
      have := hφ01 z.2 (f z.1); rw [abs_le]; constructor <;> linarith
    have hLb : ∀ z : X × Y, |L z.2 (f z.1)| ≤ 1 := fun z => by
      have := hL01 z.2 (f z.1); rw [abs_le]; constructor <;> linarith
    have hLφ : (∫ z, L z.2 (f z.1) ∂P) ≤ ∫ z, φ z.2 (f z.1) ∂P :=
      integral_mono (rk_bdd_integrable P _ hLm 1 hLb) (rk_bdd_integrable P _ hfm 1 hφfb)
        (fun z => hdom _ _)
    have hsplit : (fun z : X × Y => φ z.2 (f z.1)) = fun z => h z + φ0 z := by
      funext z; simp [hhdef, hφ0]
    have hint_split : (∫ z, φ z.2 (f z.1) ∂P) = (∫ z, h z ∂P) + E0 := by
      rw [hsplit, integral_add (rk_bdd_integrable P _ hhm 1 (hG h hhG))
        (rk_bdd_integrable P _ hφ0m 1 hφ0b)]
    have hemp : empMean S (fun z => φ z.2 (f z.1)) = empMean S h + empMean S φ0 := by
      rw [hsplit, rk_emp_add]
    have hle : (∫ z, h z ∂P) - empMean S h ≤ supDev P n G S := by
      have := le_ciSup (rk_supDev_bdd P G hG S) ⟨h, hhG⟩
      exact this
    rw [h8]
    linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hA := rk_step_gen P G hG n hn δ hδ0 hδ1 hsup
  have hB : πn {S | ε ≤ (fun S => - empMean S φ0) S - ∫ S', (fun S => - empMean S φ0) S' ∂πn}
      ≤ ENNReal.ofReal (δ / 2) := by
    have hm := RadGauss.RiskBound.mcdiarmid_inequality n (fun _ => P) (fun S => - empMean S φ0)
      (rk_emp_meas n φ0 hφ0m).neg (fun _ => 2 / n)
      (fun i S z => by
        have := rk_emp_update S i z φ0 hφ0b
        rw [show -empMean S φ0 - -empMean (Function.update S i z) φ0
          = -(empMean S φ0 - empMean (Function.update S i z) φ0) by ring, abs_neg]
        exact this) ε hε0
    refine hm.trans (le_of_eq ?_)
    congr 1
    have hsum : (∑ _i : Fin n, (2 / (n:ℝ)) ^ 2 : ℝ) = (4:ℝ) / n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp; ring
    rw [hsum]
    have : -2 * ε ^ 2 / (4 / n) = - Real.log (2 / δ) := by
      rw [hε2]; field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  calc _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hA hB
    _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

theorem rk_abs_iSup {ι : Type*} (g : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i, |g i| ≤ C) :
    |⨆ i, g i| ≤ C := by
  rcases isEmpty_or_nonempty ι with hE | hne
  · simp [Real.iSup_of_isEmpty, hC]
  have hbdd : BddAbove (Set.range g) := ⟨C, by rintro _ ⟨i, rfl⟩; exact (abs_le.mp (hb i)).2⟩
  have i0 : ι := hne.some
  rw [abs_le]; constructor
  · have := le_ciSup hbdd i0; have := (abs_le.mp (hb i0)).1; linarith
  · exact ciSup_le fun i => (abs_le.mp (hb i)).2

theorem rk_ofReal_iSup_le {ι : Type*} (g : ι → ℝ) (hbdd : BddAbove (Set.range g)) (B : ENNReal)
    (hb : ∀ i, ENNReal.ofReal (g i) ≤ B) : ENNReal.ofReal (⨆ i, g i) ≤ B := by
  rcases isEmpty_or_nonempty ι with hE | hne
  · simp [Real.iSup_of_isEmpty]
  by_cases hB : B = ⊤
  · simp [hB]
  rw [ENNReal.ofReal_le_iff_le_toReal hB]
  exact ciSup_le fun i => (ENNReal.ofReal_le_iff_le_toReal hB).mp (hb i)

theorem rk_ofReal_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, a i) ≤ ∑ i ∈ s, ENNReal.ofReal (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ih)

def rkSw {Z : Type*} {n : ℕ} (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z)) :
    (Fin n → Z) × (Fin n → Z) :=
  (fun i => if σ i then p.1 i else p.2 i, fun i => if σ i then p.2 i else p.1 i)

theorem rk_sw_mp {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Fin n → Bool) :
    MeasurePreserving (rkSw σ) ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow Z Z (Fin n) (fun _ => μ) (fun _ => μ)
  have hmid : MeasurePreserving (fun (q : Fin n → Z × Z) i => (if σ i then q i else (q i).swap))
      (Measure.pi fun _ => μ.prod μ) (Measure.pi fun _ => μ.prod μ) := by
    refine measurePreserving_pi (fun _ : Fin n => μ.prod μ) (fun _ => μ.prod μ)
      (f := fun i (z : Z × Z) => if σ i then z else z.swap) fun i => ?_
    by_cases h : σ i = true
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h]; exact Measure.measurePreserving_swap
  have := he.comp (hmid.comp he.symm)
  convert this using 1
  funext p
  simp only [Function.comp, rkSw]
  ext i <;> by_cases h : σ i = true <;> simp [h, MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]

theorem rk_sw_term {Z : Type*} {n : ℕ} (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z))
    (h : Z → ℝ) :
    empMean (rkSw σ p).2 h - empMean (rkSw σ p).1 h
      = 2⁻¹ * ((2 / (n : ℝ)) * ∑ i, signVal (σ i) * h (p.2 i))
        - 2⁻¹ * ((2 / (n : ℝ)) * ∑ i, signVal (σ i) * h (p.1 i)) := by
  unfold empMean
  have : ∀ i, h ((rkSw σ p).2 i) - h ((rkSw σ p).1 i)
      = signVal (σ i) * h (p.2 i) - signVal (σ i) * h (p.1 i) := by
    intro i; by_cases hσ : σ i = true <;> simp [rkSw, signVal, hσ] <;> ring
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [this, Finset.sum_sub_distrib]
  ring

theorem rk_pointwise {Z : Type*} (n : ℕ) (G : Set (Z → ℝ)) (hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1)
    (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z)) :
    ENNReal.ofReal (doubleSupDev n G (rkSw σ p).1 (rkSw σ p).2)
      ≤ 2⁻¹ * (⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.2 i)|)
        + 2⁻¹ * (⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.1 i)|) := by
  unfold doubleSupDev
  refine rk_ofReal_iSup_le _ ⟨2, ?_⟩ _ ?_
  · rintro _ ⟨h, rfl⟩
    have h1 := rk_emp_bound (rkSw σ p).2 h (hG h h.2)
    have h2 := rk_emp_bound (rkSw σ p).1 h (hG h h.2)
    simp only
    rw [abs_le] at h1 h2; linarith
  · intro h
    rw [rk_sw_term]
    set a := (2 / (n : ℝ)) * ∑ i, signVal (σ i) * (h : Z → ℝ) (p.2 i)
    set b := (2 / (n : ℝ)) * ∑ i, signVal (σ i) * (h : Z → ℝ) (p.1 i)
    have hle : 2⁻¹ * a - 2⁻¹ * b ≤ 2⁻¹ * |a| + 2⁻¹ * |b| := by
      have := le_abs_self a; have := neg_abs_le b; linarith
    have ha : ENNReal.ofReal |a| ≤ ⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.2 i)| :=
      le_iSup₂ (f := fun g (_ : g ∈ G) => ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.2 i)|) (h : Z → ℝ) h.2
    have hb : ENNReal.ofReal |b| ≤ ⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.1 i)| :=
      le_iSup₂ (f := fun g (_ : g ∈ G) => ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.1 i)|) (h : Z → ℝ) h.2
    calc ENNReal.ofReal (2⁻¹ * a - 2⁻¹ * b) ≤ ENNReal.ofReal (2⁻¹ * |a| + 2⁻¹ * |b|) :=
          ENNReal.ofReal_le_ofReal hle
      _ ≤ ENNReal.ofReal (2⁻¹ * |a|) + ENNReal.ofReal (2⁻¹ * |b|) := ENNReal.ofReal_add_le
      _ = 2⁻¹ * ENNReal.ofReal |a| + 2⁻¹ * ENNReal.ofReal |b| := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
      _ ≤ _ := add_le_add (mul_le_mul_right ha _) (mul_le_mul_right hb _)

theorem rk_ofReal_max (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem symmetrization_gen {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (G : Set (Z → ℝ)) (hG : ∀ h ∈ G, ∀ z, |h z| ≤ 1) (hGm : ∀ h ∈ G, Measurable h)
    (n : ℕ) (hn : 0 < n)
    (hsup : Measurable (supDev P n G))
    (hrad : Measurable (empiricalRademacher n G))
    (hdbl : Measurable (fun p : (Fin n → Z) × (Fin n → Z) => doubleSupDev n G p.1 p.2)) :
    ENNReal.ofReal (∫ S, supDev P n G S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity P n G := by
  set π := Measure.pi fun _ : Fin n => P with hπ
  set ρ := π.prod π with hρ
  set D := fun p : (Fin n → Z) × (Fin n → Z) => doubleSupDev n G p.1 p.2 with hDdef
  have hdterm : ∀ (h : G) (S S' : Fin n → Z), |empMean S' (h : Z → ℝ) - empMean S (h : Z → ℝ)| ≤ 2 := by
    intro h S S'
    have h1 := rk_emp_bound S' h (hG h h.2); have h2 := rk_emp_bound S h (hG h h.2)
    rw [abs_le] at *; constructor <;> linarith
  have hDb : ∀ p, |D p| ≤ 2 := fun p => rk_abs_iSup _ 2 (by norm_num) fun h => hdterm h _ _
  have hSb : ∀ S, |supDev P n G S| ≤ 2 := fun S =>
    rk_abs_iSup _ 2 (by norm_num) fun h => rk_dev_bound P S h (hG h h.2)
  have hDint : Integrable D ρ := rk_bdd_integrable ρ D hdbl 2 hDb
  have hsec : ∀ S, Integrable (fun S' => D (S, S')) π := fun S =>
    rk_bdd_integrable π _ (hdbl.comp (measurable_const.prodMk measurable_id)) 2 (fun S' => hDb _)
  -- step 1
  have step1 : ∫ S, supDev P n G S ∂π ≤ ∫ p, D p ∂ρ := by
    rw [integral_prod D hDint]
    refine integral_mono (rk_bdd_integrable π _ hsup 2 hSb) hDint.integral_prod_left ?_
    intro S
    rcases isEmpty_or_nonempty G with hE | hne
    · have h0 : supDev P n G S = 0 := by unfold supDev; simp [Real.iSup_of_isEmpty]
      have h1 : ∀ S', D (S, S') = 0 := by intro S'; simp [hDdef, doubleSupDev, Real.iSup_of_isEmpty]
      simp only [h0, h1, integral_zero, le_refl]
    · unfold supDev
      refine ciSup_le fun h => ?_
      have hhm := hGm h h.2
      have hE : (∫ w, (h : Z → ℝ) w ∂P) - empMean S (h : Z → ℝ)
          = ∫ S', (empMean S' (h : Z → ℝ) - empMean S (h : Z → ℝ)) ∂π := by
        rw [integral_sub (rk_bdd_integrable π _ (rk_emp_meas n _ hhm) 1
            (fun S' => rk_emp_bound S' h (hG h h.2))) (integrable_const _),
          rk_int_emp P n hn _ hhm 1 (hG h h.2)]
        simp
      rw [hE]
      refine integral_mono ((rk_bdd_integrable π _ (rk_emp_meas n _ hhm) 1
            (fun S' => rk_emp_bound S' h (hG h h.2))).sub (integrable_const _)) (hsec S) ?_
      intro S'
      have hbdd : BddAbove (Set.range fun h : G => empMean S' (h : Z → ℝ) - empMean S (h : Z → ℝ)) :=
        ⟨2, by rintro _ ⟨k, rfl⟩; exact (abs_le.mp (hdterm k S S')).2⟩
      exact le_ciSup hbdd h
  -- step 2
  have hswm : ∀ σ : Fin n → Bool, Measurable (fun p => D (rkSw σ p)) := fun σ =>
    hdbl.comp (rk_sw_mp P σ).measurable
  have hsw : ∀ σ : Fin n → Bool, ∫ p, D (rkSw σ p) ∂ρ = ∫ p, D p ∂ρ := by
    intro σ
    have hmp := rk_sw_mp P (n := n) σ
    have h1 := integral_map (μ := ρ) (φ := rkSw σ) hmp.measurable.aemeasurable (f := D)
      (by rw [hmp.map_eq]; exact hdbl.aestronglyMeasurable)
    rw [hmp.map_eq] at h1
    exact h1.symm
  set W := fun p => ((2:ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Bool, D (rkSw σ p) with hW
  have hWint : Integrable W ρ := by
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun σ _ => rk_bdd_integrable ρ _ (hswm σ) 2 (fun p => hDb _)
  have step2 : ∫ p, D p ∂ρ = ∫ p, W p ∂ρ := by
    rw [hW, integral_const_mul, integral_finset_sum]
    · simp only [hsw, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    · intro σ _; exact rk_bdd_integrable ρ _ (hswm σ) 2 (fun p => hDb _)
  -- step 3
  have step3 : ENNReal.ofReal (∫ p, W p ∂ρ) ≤ ∫⁻ p, ENNReal.ofReal (W p) ∂ρ := by
    have hmax : Integrable (fun p => max (W p) 0) ρ := hWint.sup (integrable_const 0)
    calc ENNReal.ofReal (∫ p, W p ∂ρ) ≤ ENNReal.ofReal (∫ p, max (W p) 0 ∂ρ) :=
          ENNReal.ofReal_le_ofReal (integral_mono hWint hmax fun p => le_max_left _ _)
      _ = ∫⁻ p, ENNReal.ofReal (max (W p) 0) ∂ρ :=
          ofReal_integral_eq_lintegral_ofReal hmax (ae_of_all _ fun p => le_max_right _ _)
      _ = ∫⁻ p, ENNReal.ofReal (W p) ∂ρ := by simp only [rk_ofReal_max]
  -- step 4
  have step4 : ∀ p, ENNReal.ofReal (W p)
      ≤ 2⁻¹ * empiricalRademacher n G p.2 + 2⁻¹ * empiricalRademacher n G p.1 := by
    intro p
    rw [hW]; dsimp only
    rw [ENNReal.ofReal_mul (by positivity)]
    have hc : ENNReal.ofReal (((2:ℝ) ^ n)⁻¹) = ((2 : ENNReal) ^ n)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
      simp
    rw [hc]
    calc ((2 : ENNReal) ^ n)⁻¹ * ENNReal.ofReal (∑ σ : Fin n → Bool, D (rkSw σ p))
        ≤ ((2 : ENNReal) ^ n)⁻¹ * ∑ σ : Fin n → Bool, ENNReal.ofReal (D (rkSw σ p)) :=
          by gcongr; exact rk_ofReal_sum_le _ _
      _ ≤ ((2 : ENNReal) ^ n)⁻¹ * ∑ σ : Fin n → Bool,
            (2⁻¹ * (⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.2 i)|)
            + 2⁻¹ * (⨆ g ∈ G, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, signVal (σ i) * g (p.1 i)|)) :=
          by gcongr with σ _; exact rk_pointwise n G hG σ p
      _ = 2⁻¹ * empiricalRademacher n G p.2 + 2⁻¹ * empiricalRademacher n G p.1 := by
          unfold empiricalRademacher
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  -- step 5
  have hm2 : Measurable fun p : (Fin n → Z) × (Fin n → Z) => empiricalRademacher n G p.2 :=
    hrad.comp measurable_snd
  have hm1 : Measurable fun p : (Fin n → Z) × (Fin n → Z) => empiricalRademacher n G p.1 :=
    hrad.comp measurable_fst
  have hR2 : ∫⁻ p, empiricalRademacher n G p.2 ∂ρ = rademacherComplexity P n G := by
    rw [hρ, lintegral_prod _ hm2.aemeasurable]
    simp [rademacherComplexity, hπ]
  have hR1 : ∫⁻ p, empiricalRademacher n G p.1 ∂ρ = rademacherComplexity P n G := by
    rw [hρ, lintegral_prod _ hm1.aemeasurable]
    simp [rademacherComplexity, hπ]
  have step5 : ∫⁻ p, (2⁻¹ * empiricalRademacher n G p.2 + 2⁻¹ * empiricalRademacher n G p.1) ∂ρ
      = rademacherComplexity P n G := by
    rw [lintegral_add_left (hm2.const_mul _), lintegral_const_mul _ hm2,
      lintegral_const_mul _ hm1, hR1, hR2,
      ← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
  calc ENNReal.ofReal (∫ S, supDev P n G S ∂π) ≤ ENNReal.ofReal (∫ p, D p ∂ρ) :=
        ENNReal.ofReal_le_ofReal step1
    _ = ENNReal.ofReal (∫ p, W p ∂ρ) := by rw [step2]
    _ ≤ ∫⁻ p, ENNReal.ofReal (W p) ∂ρ := step3
    _ ≤ _ := lintegral_mono step4
    _ = _ := step5

theorem symmetrization_core {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (φ : Y → A → ℝ) (hφ : Measurable (Function.uncurry φ))
    (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    ENNReal.ofReal
        (∫ S, supDev P n (phiTildeComp φ F) S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity P n (phiTildeComp φ F) :=
  symmetrization_gen P _ (fun h hh z => rk_phi_bound φ hφ01 F h hh z)
    (fun h hh => rk_phi_meas φ hφ F hF h hh) n hn hsup hrad hdbl

theorem theorem_8_core {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P) ≤
          ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
            rademacherComplexity P n (phiTildeComp φ F) +
            ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)))}
      ≤ ENNReal.ofReal δ := by
  have hsym := symmetrization_core φ hφ hφ01 F hF P n hn hsup hrad hdbl
  refine le_trans (measure_mono ?_) (combined_bound_core L φ hL hφ hL01 hφ01 hdom F hF P n hn δ hδ0 hδ1 hsup)
  rintro S ⟨f, hf, hne⟩
  refine ⟨f, hf, fun hle => hne ?_⟩
  calc ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P)
      ≤ ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
            Real.sqrt (8 * Real.log (2 / δ) / n)) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1)) +
            (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P))) +
          ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
          ENNReal.ofReal (∫ S', supDev P n (phiTildeComp φ F) S' ∂(Measure.pi fun _ : Fin n => P)) +
          ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)) := by
        gcongr; exact ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr

end

section
open MeasureTheory
open RadGauss.RiskBound

theorem solution {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Zero A]
    (L φ : Y → A → ℝ) (hL : Measurable (Function.uncurry L))
    (hφ : Measurable (Function.uncurry φ))
    (hL01 : ∀ y a, 0 ≤ L y a ∧ L y a ≤ 1) (hφ01 : ∀ y a, 0 ≤ φ y a ∧ φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a)
    (F : Set (X → A)) (hF : ∀ f ∈ F, Measurable f)
    (P : Measure (X × Y)) [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hsup : Measurable (supDev P n (phiTildeComp φ F)))
    (hrad : Measurable (empiricalRademacher n (phiTildeComp φ F)))
    (hdbl : Measurable (fun p : (Fin n → X × Y) × (Fin n → X × Y) =>
      doubleSupDev n (phiTildeComp φ F) p.1 p.2)) :
    (Measure.pi fun _ : Fin n => P)
      {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (∫ z, L z.2 (f z.1) ∂P) ≤
          ENNReal.ofReal (empMean S (fun z => φ z.2 (f z.1))) +
            rademacherComplexity P n (phiTildeComp φ F) +
            ENNReal.ofReal (Real.sqrt (8 * Real.log (2 / δ) / n)))}
      ≤ ENNReal.ofReal δ := by
  exact theorem_8_core L φ hL hφ hL01 hφ01 hdom F hF P n hn δ hδ0 hδ1 hsup hrad hdbl

end
