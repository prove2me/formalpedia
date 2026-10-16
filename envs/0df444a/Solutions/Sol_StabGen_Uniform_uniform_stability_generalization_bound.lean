-- Prove2me | solution 1 for StabGen.Uniform.uniform_stability_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T15:52:57.16224+00:00
-- url     : https://prove2.me/submissions/08fae585-26d2-48c6-bea0-1df5b249980c

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

set_option autoImplicit false

open MeasureTheory FoundationsML.Stability

namespace StabGen.Uniform

section
open ProbabilityTheory

lemma mcd_int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma mcd_abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : |∫ x, F x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- Hoeffding step: a measurable function with oscillation at most `c`. -/
lemma mcd_hoeff_step {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (G : Ω → ℝ) (hG : Measurable G) (c B : ℝ) (hc : 0 ≤ c) (hB : ∀ z, |G z| ≤ B)
    (hosc : ∀ z z', G z' - G z ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 8 * t ^ 2) := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  have hbdd : BddBelow (Set.range G) := ⟨-B, by
    rintro _ ⟨z, rfl⟩; have := hB z; rw [abs_le] at this; linarith⟩
  set A := ⨅ z, G z with hA
  have hmem : ∀ z, G z ∈ Set.Icc A (A + c) := by
    intro z
    refine ⟨ciInf_le hbdd z, ?_⟩
    have : G z - c ≤ A := le_ciInf fun z' => by have := hosc z' z; linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := G) (a := A) (b := A + c)
    hG.aemeasurable (Filter.Eventually.of_forall hmem)
  have h1 := hs.mgf_le t
  have hcoe : (((‖(A + c) - A‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
    have : (A + c) - A = c := by ring
    rw [this]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    ring
  rw [hcoe] at h1
  unfold mgf at h1
  calc ∫ z, Real.exp (t * (G z - ∫ z', G z' ∂ν)) ∂ν ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) := h1
    _ = Real.exp (c ^ 2 / 8 * t ^ 2) := by ring_nf

/-- Bounded differences give a bounded range. -/
lemma mcd_range_bdd {Ω : Type*} : ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ) (c : Fin n → ℝ),
    (∀ S i z, |f (Function.update S i z) - f S| ≤ c i) →
    ∀ S S', |f S - f S'| ≤ ∑ i, c i := by
  intro n
  induction n with
  | zero =>
    intro f c _ S S'
    have : S = S' := Subsingleton.elim _ _
    subst this
    simp
  | succ n ih =>
    intro f c hdiff S S'
    have hS : S = Fin.cons (S 0) (Fin.tail S) := (Fin.cons_self_tail S).symm
    have hS' : S' = Fin.cons (S' 0) (Fin.tail S') := (Fin.cons_self_tail S').symm
    rw [Fin.sum_univ_succ]
    have h1 : |f (Fin.cons (S 0) (Fin.tail S)) - f (Fin.cons (S' 0) (Fin.tail S))| ≤ c 0 := by
      have := hdiff (Fin.cons (S 0) (Fin.tail S)) 0 (S' 0)
      rw [Fin.update_cons_zero] at this
      rw [abs_sub_comm]; exact this
    have h2 := ih (fun w => f (Fin.cons (S' 0) w)) (fun j => c j.succ) (by
      intro w j z
      have := hdiff (Fin.cons (S' 0) w) j.succ z
      rw [← Fin.cons_update] at this
      exact this) (Fin.tail S) (Fin.tail S')
    calc |f S - f S'|
        = |(f (Fin.cons (S 0) (Fin.tail S)) - f (Fin.cons (S' 0) (Fin.tail S)))
            + (f (Fin.cons (S' 0) (Fin.tail S)) - f (Fin.cons (S' 0) (Fin.tail S')))| := by
          rw [← hS, ← hS']; congr 1; ring
      _ ≤ _ := by
          refine (abs_add_le _ _).trans ?_
          linarith

/-- McDiarmid mgf bound, non-uniform differences. -/
theorem mcd_mgf_gen {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] :
    ∀ (n : ℕ) (f : (Fin n → Ω) → ℝ) (c : Fin n → ℝ) (B : ℝ), (∀ i, 0 ≤ c i) → Measurable f →
    (∀ S, |f S| ≤ B) → (∀ S i z, |f (Function.update S i z) - f S| ≤ c i) → ∀ t : ℝ,
    ∫ S, Real.exp (t * (f S - ∫ S', f S' ∂(Measure.pi fun _ => ν))) ∂(Measure.pi fun _ => ν)
      ≤ Real.exp ((∑ i, c i ^ 2) / 8 * t ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro f c B _ _ _ _ t
    have hfS : ∀ S, f S = f default := fun S => congrArg f (Subsingleton.elim _ _)
    simp [hfS]
  | succ n ih =>
    intro f c B hc0 hf hB hdiff t
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => ν)
        (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    have hmps := hmp.symm e
    set g : Ω → (Fin n → Ω) → ℝ := fun z w => f (Fin.cons z w) with hg
    have hge : ∀ p : Ω × (Fin n → Ω), f (e.symm p) = g p.1 p.2 := by
      intro p; simp [g, e]; try rfl
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = fun p => f (e.symm p) := by
        funext p; rw [hge p]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hgB : ∀ z w, |g z w| ≤ B := fun z w => hB _
    set hw : (Fin n → Ω) → ℝ := fun w => ∫ z, g z w ∂ν with hhw
    have hwm : Measurable hw :=
      (StronglyMeasurable.integral_prod_left (μ := ν) hgm.stronglyMeasurable).measurable
    have hwB : ∀ w, |hw w| ≤ B := fun w => mcd_abs_integral_le_of_bdd ν _ B fun z => hgB z w
    have hgz : ∀ w, Measurable fun z => g z w := fun w => hgm.comp (measurable_id.prodMk measurable_const)
    have hwdiff : ∀ w j y, |hw (Function.update w j y) - hw w| ≤ c j.succ := by
      intro w j y
      simp only [hw]
      rw [← integral_sub (mcd_int_of_bdd ν _ (hgz _) B fun z => hgB z _)
        (mcd_int_of_bdd ν _ (hgz _) B fun z => hgB z _)]
      refine mcd_abs_integral_le_of_bdd ν _ (c j.succ) fun z => ?_
      simp only [g, Fin.cons_update]
      exact hdiff _ _ _
    have hih := ih hw (fun j => c j.succ) B (fun j => hc0 _) hwm hwB hwdiff t
    -- the mean
    have hint_f : Integrable (fun p : Ω × (Fin n → Ω) => g p.1 p.2) (ν.prod (Measure.pi fun _ => ν)) :=
      mcd_int_of_bdd _ _ hgm B fun p => hgB p.1 p.2
    have hmean : ∫ S, f S ∂(Measure.pi fun _ => ν) = ∫ w, hw w ∂(Measure.pi fun _ => ν) := by
      rw [← hmps.integral_comp' (g := f)]
      simp_rw [hge]
      rw [integral_prod_symm _ hint_f]
    obtain ⟨m, hm⟩ : ∃ m, m = ∫ S, f S ∂(Measure.pi fun _ => ν) := ⟨_, rfl⟩
    rw [← hm]
    rw [← hm] at hmean
    have hexpm : Measurable fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)) :=
      Real.measurable_exp.comp (measurable_const.mul (hgm.sub measurable_const))
    have hint_e : Integrable (fun p : Ω × (Fin n → Ω) => Real.exp (t * (g p.1 p.2 - m)))
        (ν.prod (Measure.pi fun _ => ν)) :=
      mcd_int_of_bdd _ _ hexpm (Real.exp (|t| * (B + |m|))) fun p => by
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hgB p.1 p.2
        calc t * (g p.1 p.2 - m) ≤ |t * (g p.1 p.2 - m)| := le_abs_self _
          _ = |t| * |g p.1 p.2 - m| := abs_mul _ _
          _ ≤ |t| * (B + |m|) := by
            gcongr
            calc |g p.1 p.2 - m| ≤ |g p.1 p.2| + |m| := abs_sub _ _
              _ ≤ B + |m| := by linarith
    have hstep : ∀ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ≤
        Real.exp (t * (hw w - m)) * Real.exp (c 0 ^ 2 / 8 * t ^ 2) := by
      intro w
      have hosc : ∀ z z', g z' w - g z w ≤ c 0 := by
        intro z z'
        have := hdiff (Fin.cons z w) 0 z'
        rw [Fin.update_cons_zero] at this
        exact (abs_le.mp this).2
      have hh := mcd_hoeff_step ν (fun z => g z w) (hgz w) (c 0) B (hc0 0) (fun z => hgB z w) hosc t
      have : ∀ z, Real.exp (t * (g z w - m)) =
          Real.exp (t * (hw w - m)) * Real.exp (t * (g z w - ∫ z', g z' w ∂ν)) := by
        intro z; rw [← Real.exp_add]; congr 1; simp only [hw]; ring
      simp_rw [this]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    calc ∫ S, Real.exp (t * (f S - m)) ∂(Measure.pi fun _ => ν)
        = ∫ w, ∫ z, Real.exp (t * (g z w - m)) ∂ν ∂(Measure.pi fun _ => ν) := by
          rw [← hmps.integral_comp' (g := fun S => Real.exp (t * (f S - m)))]
          simp_rw [hge]
          rw [integral_prod_symm _ hint_e]
      _ ≤ ∫ w, Real.exp (t * (hw w - m)) * Real.exp (c 0 ^ 2 / 8 * t ^ 2)
            ∂(Measure.pi fun _ => ν) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
            integral_nonneg fun z => (Real.exp_pos _).le) ?_ (Filter.Eventually.of_forall hstep)
          refine Integrable.mul_const ?_ _
          refine mcd_int_of_bdd _ _ (Real.measurable_exp.comp
            (measurable_const.mul (hwm.sub measurable_const))) (Real.exp (|t| * (B + |m|))) fun w => ?_
          rw [abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.mpr
          have h1 := hwB w
          calc t * (hw w - m) ≤ |t * (hw w - m)| := le_abs_self _
            _ = |t| * |hw w - m| := abs_mul _ _
            _ ≤ |t| * (B + |m|) := by
              gcongr
              calc |hw w - m| ≤ |hw w| + |m| := abs_sub _ _
                _ ≤ B + |m| := by linarith
      _ = (∫ w, Real.exp (t * (hw w - ∫ w', hw w' ∂(Measure.pi fun _ => ν)))
            ∂(Measure.pi fun _ => ν)) * Real.exp (c 0 ^ 2 / 8 * t ^ 2) := by
          rw [integral_mul_const, ← hmean]
      _ ≤ Real.exp ((∑ i : Fin n, c i.succ ^ 2) / 8 * t ^ 2) * Real.exp (c 0 ^ 2 / 8 * t ^ 2) :=
          mul_le_mul_of_nonneg_right hih (Real.exp_pos _).le
      _ = Real.exp ((∑ i : Fin (n + 1), c i ^ 2) / 8 * t ^ 2) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]; congr 1; ring

/-- **McDiarmid's inequality**. -/
theorem mcdiarmid_inequality {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (F : (Fin m → Z) → ℝ) (hF : Measurable F)
    (c : Fin m → ℝ)
    (hc : ∀ (S : Fin m → Z) (i : Fin m) (z' : Z), |F S - F (StabGen.Hypothesis.replaceAt S i z')| ≤ c i)
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m => D)
        {S | ε ≤ F S - ∫ S', F S' ∂(Measure.pi fun _ : Fin m => D)}
      ≤ if (∑ i, c i ^ 2) = 0 then 0
        else ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / ∑ i, c i ^ 2)) := by
  have hdiff : ∀ (S : Fin m → Z) (i : Fin m) (z : Z), |F (Function.update S i z) - F S| ≤ c i := by
    intro S i z
    rw [abs_sub_comm]
    exact hc S i z
  have hz : Nonempty Z := nonempty_of_isProbabilityMeasure D
  obtain ⟨z0⟩ := hz
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    have := hdiff (fun _ => z0) i z0
    have h2 : Function.update (fun _ : Fin m => z0) i z0 = fun _ => z0 := by
      funext j; by_cases h : j = i <;> simp [Function.update, h]
    rw [h2] at this
    simpa using this
  set B : ℝ := |F (fun _ => z0)| + ∑ i, c i with hBdef
  have hB : ∀ S, |F S| ≤ B := by
    intro S
    have := mcd_range_bdd m F c hdiff S (fun _ => z0)
    calc |F S| = |(F S - F (fun _ => z0)) + F (fun _ => z0)| := by ring_nf
      _ ≤ |F S - F (fun _ => z0)| + |F (fun _ => z0)| := abs_add_le _ _
      _ ≤ B := by rw [hBdef]; linarith
  have hmgf := mcd_mgf_gen D m F c B hc0 hF hB hdiff
  set μ : Measure (Fin m → Z) := Measure.pi fun _ : Fin m => D with hμ
  set mm : ℝ := ∫ S', F S' ∂μ with hmm
  have hcher : ∀ t : ℝ, 0 ≤ t →
      μ {S | ε ≤ F S - mm} ≤ ENNReal.ofReal (Real.exp (-t * ε + (∑ i, c i ^ 2) / 8 * t ^ 2)) := by
    intro t ht
    have hint : Integrable (fun S => Real.exp (t * (F S - mm))) μ := by
      refine mcd_int_of_bdd μ _ (Real.measurable_exp.comp
        (measurable_const.mul (hF.sub measurable_const))) (Real.exp (|t| * (B + |mm|))) fun S => ?_
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hB S
      calc t * (F S - mm) ≤ |t * (F S - mm)| := le_abs_self _
        _ = |t| * |F S - mm| := abs_mul _ _
        _ ≤ |t| * (B + |mm|) := by
          gcongr
          calc |F S - mm| ≤ |F S| + |mm| := abs_sub _ _
            _ ≤ B + |mm| := by linarith
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun S => F S - mm) ε ht hint
    have h2 : mgf (fun S => F S - mm) μ t ≤ Real.exp ((∑ i, c i ^ 2) / 8 * t ^ 2) := hmgf t
    have h3 : μ.real {S | ε ≤ F S - mm} ≤ Real.exp (-t * ε + (∑ i, c i ^ 2) / 8 * t ^ 2) := by
      rw [Real.exp_add]
      exact h.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
    calc μ {S | ε ≤ F S - mm} = ENNReal.ofReal (μ.real {S | ε ≤ F S - mm}) := by
          rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  have hs0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  split_ifs with hs
  · rw [hs] at hcher
    have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-((n : ℝ)) * ε + 0 / 8 * (n : ℝ) ^ 2)))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * ε) Filter.atTop Filter.atTop :=
        Filter.Tendsto.atTop_mul_const hε tendsto_natCast_atTop_atTop
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      have h3 := (ENNReal.tendsto_ofReal h2)
      rw [ENNReal.ofReal_zero] at h3
      refine h3.congr fun n => ?_
      simp only [Function.comp]
      congr 2
      ring
    exact ge_of_tendsto' hlim fun n => hcher n (Nat.cast_nonneg n)
  · have hspos : 0 < ∑ i, c i ^ 2 := lt_of_le_of_ne hs0 (Ne.symm hs)
    have := hcher (4 * ε / ∑ i, c i ^ 2) (by positivity)
    refine this.trans (le_of_eq ?_)
    congr 2
    field_simp
    ring


end

section
open ProbabilityTheory

lemma b2_perm_integral {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (G : (Fin m → Z) → ℝ) :
    ∫ S, G (S ∘ σ) ∂(Measure.pi fun _ : Fin m => D) = ∫ S, G S ∂(Measure.pi fun _ : Fin m => D) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin m => D) σ.symm
  have hfun : ∀ S : Fin m → Z, MeasurableEquiv.piCongrLeft (fun _ : Fin m => Z) σ.symm S = S ∘ σ := by
    intro S
    funext b
    rw [MeasurableEquiv.coe_piCongrLeft]
    simp [Equiv.piCongrLeft_apply_eq_cast]
  have := h.integral_comp' (g := G)
  simpa [hfun] using this

lemma b2_int_of_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ x, |F x| ≤ C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma b2_key {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {n : ℕ} (j : Fin (n + 1)) (H : (Fin (n + 1) → Z) → Z → ℝ)
    (hH : Measurable (Function.uncurry H)) (B : ℝ) (hB : ∀ S z, |H S z| ≤ B) :
    ∫ S, H S (S j) ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ p : (Fin (n + 1) → Z) × Z, H (Function.update p.1 j p.2) p.2
          ∂((Measure.pi fun _ : Fin (n + 1) => D).prod D) := by
  set μ : Measure (Fin (n + 1) → Z) := Measure.pi fun _ : Fin (n + 1) => D with hμ
  set ν : Measure (Fin n → Z) := Measure.pi fun _ : Fin n => D with hν
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) j with he
  have hmp : MeasurePreserving e μ (D.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) j
  set K : Z × (Fin n → Z) → ℝ := fun q => H (e.symm q) q.1 with hK
  have hKm : Measurable K := by
    have : K = fun q => Function.uncurry H (e.symm q, q.1) := rfl
    rw [this]
    exact hH.comp (e.symm.measurable.prodMk measurable_fst)
  have hKint : Integrable K (D.prod ν) := b2_int_of_bdd _ K hKm B fun q => hB _ _
  have h1 : ∫ S, H S (S j) ∂μ = ∫ q, K q ∂(D.prod ν) := by
    rw [← hmp.integral_comp' K]
    congr 1
    funext S
    simp only [K, MeasurableEquiv.symm_apply_apply]
    rfl
  have hupd : ∀ (S : Fin (n + 1) → Z) (z : Z), Function.update S j z = e.symm (z, (e S).2) := by
    intro S z
    funext k
    by_cases hk : k = j
    · subst hk
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
  have h2 : ∀ z, ∫ S, H (Function.update S j z) z ∂μ = ∫ w, K (z, w) ∂ν := by
    intro z
    have e1 : ∀ S, H (Function.update S j z) z = (fun q : Z × (Fin n → Z) => K (z, q.2)) (e S) := by
      intro S
      simp only [K]
      rw [hupd S z]
    simp_rw [e1]
    rw [hmp.integral_comp' (fun q : Z × (Fin n → Z) => K (z, q.2))]
    have hi : Integrable (fun q : Z × (Fin n → Z) => K (z, q.2)) (D.prod ν) :=
      b2_int_of_bdd _ _ (hKm.comp (measurable_const.prodMk measurable_snd)) B fun q => hB _ _
    rw [integral_prod _ hi]
    simp
  have hRHS : ∫ p : (Fin (n + 1) → Z) × Z, H (Function.update p.1 j p.2) p.2 ∂(μ.prod D)
      = ∫ z, ∫ S, H (Function.update S j z) z ∂μ ∂D := by
    rw [integral_prod_symm]
    exact b2_int_of_bdd _ _ (hH.comp ((measurable_update' (a := j)).prodMk measurable_snd)) B fun p => hB _ _
  rw [hRHS, h1]
  simp_rw [h2]
  rw [integral_prod _ hKint]

/-- Permutation invariance of the product integral. -/
lemma b2_perm_prod {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (G : (Fin m → Z) × Z → ℝ) (hG : Measurable G) (B : ℝ)
    (hB : ∀ p, |G p| ≤ B) :
    ∫ p, G (p.1 ∘ σ, p.2) ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ p, G p ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  have hσ : Measurable (fun S : Fin m → Z => S ∘ σ) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have h1 : Integrable (fun p : (Fin m → Z) × Z => G (p.1 ∘ σ, p.2)) ((Measure.pi fun _ : Fin m => D).prod D) :=
    b2_int_of_bdd _ _ (hG.comp ((hσ.comp measurable_fst).prodMk measurable_snd)) B fun p => hB _
  have h2 : Integrable G ((Measure.pi fun _ : Fin m => D).prod D) := b2_int_of_bdd _ _ hG B hB
  have e1 : ∫ p, G (p.1 ∘ σ, p.2) ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ z, ∫ S, G (S ∘ σ, z) ∂(Measure.pi fun _ : Fin m => D) ∂D :=
    integral_prod_symm (fun p : (Fin m → Z) × Z => G (p.1 ∘ σ, p.2)) h1
  have e2 : ∫ p, G p ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ z, ∫ S, G (S, z) ∂(Measure.pi fun _ : Fin m => D) ∂D :=
    integral_prod_symm G h2
  rw [e1, e2]
  congr 1
  funext z
  exact b2_perm_integral D σ (fun S => G (S, z))

lemma b2_training_perm {Z : Type*} {m : ℕ} (S : Fin m → Z) (σ : Equiv.Perm (Fin m)) :
    StabGen.Hypothesis.trainingSet (S ∘ σ) = StabGen.Hypothesis.trainingSet S := by
  unfold StabGen.Hypothesis.trainingSet
  rw [← Multiset.map_map]
  congr 1
  have := congrArg Finset.val (Finset.map_univ_equiv σ)
  simpa [Finset.map_val] using this

lemma b2_removeAt_perm {Z : Type*} {m : ℕ} (S : Fin m → Z) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    StabGen.Hypothesis.removeAt (S ∘ σ) i = StabGen.Hypothesis.removeAt S (σ i) := by
  unfold StabGen.Hypothesis.removeAt
  rw [← Multiset.map_map]
  congr 1
  have := Finset.map_erase σ.toEmbedding (Finset.univ : Finset (Fin m)) i
  rw [Finset.map_univ_equiv] at this
  exact congrArg Finset.val this

lemma b2_removeAt_update {Z : Type*} {m : ℕ} (S : Fin m → Z) (j : Fin m) (w : Z) :
    StabGen.Hypothesis.removeAt (Function.update S j w) j = StabGen.Hypothesis.removeAt S j := by
  unfold StabGen.Hypothesis.removeAt
  refine Multiset.map_congr rfl fun k hk => ?_
  have : k ≠ j := (Finset.mem_erase.mp (Finset.mem_val.mp hk)).1
  simp [Function.update_of_ne this]

lemma b2_removeAt_eq {Z : Type*} {n : ℕ} (S : Fin (n + 1) → Z) (j : Fin (n + 1)) :
    StabGen.Hypothesis.removeAt S j
      = StabGen.Hypothesis.trainingSet (fun k : Fin n => S (j.succAbove k)) := by
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.trainingSet
  have h : (Finset.univ : Finset (Fin (n + 1))).erase j = Finset.univ.map (Fin.succAboveEmb j) := by
    conv_lhs => rw [Fin.univ_succAbove n j]
    rw [Finset.erase_cons]
  rw [h, Finset.map_val, Multiset.map_map]
  rfl

lemma b2_avg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ}
    (f : Fin (n + 1) → Ω → ℝ) (hint : ∀ j, Integrable (f j) μ) (c : ℝ)
    (h : ∀ j, ∫ x, f j x ∂μ = c) (hμ : μ Set.univ = 1) :
    ∫ x, ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, f j x ∂μ = c := by
  rw [integral_const_mul, integral_finset_sum _ (fun j _ => hint j)]
  simp_rw [h]
  simp
  field_simp

lemma b2_abstract {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D] {n : ℕ}
    (Φ1 : (Fin (n + 1) → Z) → Z → ℝ) (Φ2 : Fin (n + 1) → (Fin (n + 1) → Z) → Z → ℝ) (M : ℝ)
    (h1m : Measurable (Function.uncurry Φ1)) (h2m : ∀ j, Measurable (Function.uncurry (Φ2 j)))
    (h1B : ∀ S z, |Φ1 S z| ≤ M) (h2B : ∀ j S z, |Φ2 j S z| ≤ M)
    (s1 : ∀ S z (σ : Equiv.Perm (Fin (n + 1))), Φ1 (S ∘ σ) z = Φ1 S z)
    (s2 : ∀ S z (σ : Equiv.Perm (Fin (n + 1))) i, Φ2 i (S ∘ σ) z = Φ2 (σ i) S z)
    (s3 : ∀ S z j w, Φ2 j (Function.update S j w) z = Φ2 j S z)
    (i : Fin (n + 1)) :
    (∫ S, (∫ z, Φ1 S z ∂D - ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ1 S (S j))
        ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ p : (Fin (n + 1) → Z) × Z, (Φ1 p.1 p.2 - Φ1 (Function.update p.1 i p.2) p.2)
          ∂((Measure.pi fun _ : Fin (n + 1) => D).prod D)) ∧
    (∫ S, (∫ z, Φ2 i S z ∂D - ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ2 j S (S j))
        ∂(Measure.pi fun _ : Fin (n + 1) => D) = 0) ∧
    (∫ S, (∫ z, Φ1 S z ∂D - ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ2 j S (S j))
        ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ p : (Fin (n + 1) → Z) × Z, (Φ1 p.1 p.2 - Φ2 i p.1 p.2)
          ∂((Measure.pi fun _ : Fin (n + 1) => D).prod D)) := by
  set μ : Measure (Fin (n + 1) → Z) := Measure.pi fun _ : Fin (n + 1) => D with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set N : Measure ((Fin (n + 1) → Z) × Z) := μ.prod D with hN
  have hN1 : Integrable (fun p : (Fin (n + 1) → Z) × Z => Φ1 p.1 p.2) N :=
    b2_int_of_bdd _ _ h1m M fun p => h1B _ _
  have hN2 : ∀ j, Integrable (fun p : (Fin (n + 1) → Z) × Z => Φ2 j p.1 p.2) N := fun j =>
    b2_int_of_bdd _ _ (h2m j) M fun p => h2B _ _ _
  have hupdm : ∀ j, Measurable (fun p : (Fin (n + 1) → Z) × Z => (Function.update p.1 j p.2, p.2)) :=
    fun j => (measurable_update' (a := j)).prodMk measurable_snd
  have hU1 : ∀ j, Integrable (fun p : (Fin (n + 1) → Z) × Z => Φ1 (Function.update p.1 j p.2) p.2) N :=
    fun j => b2_int_of_bdd _ _ (h1m.comp (hupdm j)) M fun p => h1B _ _
  have hdm : ∀ j, Measurable (fun S : Fin (n + 1) → Z => (S, S j)) :=
    fun j => measurable_id.prodMk (measurable_pi_apply j)
  have hD1 : ∀ j, Integrable (fun S : Fin (n + 1) → Z => Φ1 S (S j)) μ :=
    fun j => b2_int_of_bdd _ _ (h1m.comp (hdm j)) M fun S => h1B _ _
  have hD2 : ∀ j, Integrable (fun S : Fin (n + 1) → Z => Φ2 j S (S j)) μ :=
    fun j => b2_int_of_bdd _ _ ((h2m j).comp (hdm j)) M fun S => h2B _ _ _
  have hR1 : Integrable (fun S => ∫ z, Φ1 S z ∂D) μ := hN1.integral_prod_left
  have hR2 : Integrable (fun S => ∫ z, Φ2 i S z ∂D) μ := (hN2 i).integral_prod_left
  have hR1' : ∫ S, ∫ z, Φ1 S z ∂D ∂μ = ∫ p, Φ1 p.1 p.2 ∂N := (integral_prod _ hN1).symm
  have hR2' : ∫ S, ∫ z, Φ2 i S z ∂D ∂μ = ∫ p, Φ2 i p.1 p.2 ∂N := (integral_prod _ (hN2 i)).symm
  have hunit : μ Set.univ = 1 := measure_univ
  -- the diagonal terms for Φ1
  have hdiag1 : ∀ j, ∫ S, Φ1 S (S j) ∂μ = ∫ p, Φ1 (Function.update p.1 i p.2) p.2 ∂N := by
    intro j
    rw [b2_key D j Φ1 h1m M h1B]
    have hperm := b2_perm_prod D (Equiv.swap i j)
      (fun p : (Fin (n + 1) → Z) × Z => Φ1 (Function.update p.1 i p.2) p.2)
      (h1m.comp (hupdm i)) M (fun p => h1B _ _)
    rw [← hperm]
    congr 1
    funext p
    simp only []
    have hu : Function.update (p.1 ∘ ⇑(Equiv.swap i j)) i p.2
        = (Function.update p.1 j p.2) ∘ ⇑(Equiv.swap i j) := by
      have := Function.update_comp_equiv p.1 (Equiv.swap i j) j p.2
      rw [this]
      simp [Equiv.swap_apply_right]
    rw [hu, s1]
  have hdiag2 : ∀ j, ∫ S, Φ2 j S (S j) ∂μ = ∫ p, Φ2 i p.1 p.2 ∂N := by
    intro j
    rw [b2_key D j (Φ2 j) (h2m j) M (h2B j)]
    simp_rw [s3]
    have hperm := b2_perm_prod D (Equiv.swap i j)
      (fun p : (Fin (n + 1) → Z) × Z => Φ2 i p.1 p.2) (h2m i) M (fun p => h2B _ _ _)
    rw [← hperm]
    congr 1
    funext p
    simp only []
    rw [s2]
    simp
  have hav1 : Integrable (fun S => ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ1 S (S j)) μ :=
    (integrable_finset_sum _ fun j _ => hD1 j).const_mul _
  have hav2 : Integrable (fun S => ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) * ∑ j, Φ2 j S (S j)) μ :=
    (integrable_finset_sum _ fun j _ => hD2 j).const_mul _
  have ha1 := b2_avg μ (fun j S => Φ1 S (S j)) hD1 _ hdiag1 hunit
  have ha2 := b2_avg μ (fun j S => Φ2 j S (S j)) hD2 _ hdiag2 hunit
  refine ⟨?_, ?_, ?_⟩
  · rw [integral_sub hR1 hav1, hR1', ha1, integral_sub hN1 (hU1 i)]
  · rw [integral_sub hR2 hav2, hR2', ha2, sub_self]
  · rw [integral_sub hR1 hav2, hR1', ha2, integral_sub hN1 (hN2 i)]

theorem lemma7_bias_identities {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (hbdd : ∃ M : ℝ, ∀ (T : Multiset (X × Y)) (z : X × Y), |Loss L (A T) z| ≤ M)
    (m : ℕ) (i : Fin m) :
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        ∂(Measure.pi fun _ : Fin m => D)
      = ∫ p : (Fin m → X × Y) × (X × Y),
          (Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2 - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt p.1 i p.2))) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.removeAt S i)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D) = 0) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D)
      = ∫ p : (Fin m → X × Y) × (X × Y),
          (Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2 - Loss L (A (StabGen.Hypothesis.removeAt p.1 i)) p.2)
          ∂((Measure.pi fun _ : Fin m => D).prod D)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact i.elim0)
  obtain ⟨M, hM⟩ := hbdd
  have h1m : Measurable (Function.uncurry
      (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet S)) z)) :=
    hA (n + 1)
  have h2m : ∀ j : Fin (n + 1), Measurable (Function.uncurry
      (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.removeAt S j)) z)) := by
    intro j
    have hm : Measurable (fun p : (Fin (n + 1) → X × Y) × (X × Y) =>
        ((fun k : Fin n => p.1 (j.succAbove k)), p.2)) :=
      (measurable_pi_lambda _ fun k => (measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
    have := (hA n).comp hm
    convert this using 1
    funext p
    simp [Function.uncurry, b2_removeAt_eq]
  have key := b2_abstract D
    (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet S)) z)
    (fun (j : Fin (n + 1)) (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.removeAt S j)) z)
    M h1m h2m (fun S z => hM _ _) (fun j S z => hM _ _)
    (fun S z σ => by simp only [b2_training_perm])
    (fun S z σ i => by simp only [b2_removeAt_perm])
    (fun S z j w => by simp only [b2_removeAt_update]) i
  exact key


end

theorem ab3463b8_removeAt_replaceAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) :
    StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') i =
      StabGen.Hypothesis.removeAt S i := by
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
  apply Multiset.map_congr rfl
  intro j hj
  have hji : j ≠ i := by
    have := Finset.mem_erase.mp (show j ∈ Finset.univ.erase i from hj)
    exact this.1
  exact Function.update_of_ne hji z' S

theorem rep_one {X Y Y' : Type*} (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y') (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' z : X × Y),
      |Loss L (A (StabGen.Hypothesis.trainingSet S)) z - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| ≤ 2 * β := by
  intro S i z' z
  have h1 := hstab S i z
  have h2 := hstab (StabGen.Hypothesis.replaceAt S i z') i z
  rw [ab3463b8_removeAt_replaceAt] at h2
  calc _ ≤ |Loss L (A (StabGen.Hypothesis.trainingSet S)) z - Loss L (A (StabGen.Hypothesis.removeAt S i)) z|
        + |Loss L (A (StabGen.Hypothesis.removeAt S i)) z - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| :=
          abs_sub_le _ _ _
    _ ≤ β + β := by
          refine add_le_add h1 ?_
          rw [abs_sub_comm]; exact h2
    _ = 2 * β := by ring

open MeasureTheory FoundationsML.Stability in
theorem StabGenBD01f6_removeAt_replaceAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) :
    StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') i
      = StabGen.Hypothesis.removeAt S i := by
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
  apply Multiset.map_congr rfl
  intro j hj
  have hj' : j ≠ i := by
    have := Finset.mem_val.mp hj
    exact (Finset.mem_erase.mp this).1
  simp [Function.update_of_ne hj']

open MeasureTheory FoundationsML.Stability in
theorem StabGenBD01f6_gen_diff {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ) (h h' : X → Y') (M c : ℝ)
    (hf : Measurable (fun z => Loss L h z)) (hg : Measurable (fun z => Loss L h' z))
    (hfb : ∀ z, 0 ≤ Loss L h z ∧ Loss L h z ≤ M) (hgb : ∀ z, 0 ≤ Loss L h' z ∧ Loss L h' z ≤ M)
    (hp : ∀ z, |Loss L h z - Loss L h' z| ≤ c) :
    |GeneralizationError D L h - GeneralizationError D L h'| ≤ c := by
  unfold GeneralizationError
  have hfi : Integrable (fun z => Loss L h z) D :=
    Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hfb z).1, (hfb z).2])
  have hgi : Integrable (fun z => Loss L h' z) D :=
    Integrable.of_bound hg.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hgb z).1, (hgb z).2])
  rw [← integral_sub hfi hgi]
  have h1 : ∫ z, (Loss L h z - Loss L h' z) ∂D ≤ ∫ _z, c ∂D :=
    integral_mono (hfi.sub hgi) (integrable_const c) (fun z => (abs_le.mp (hp z)).2)
  have h2 : ∫ _z, (-c) ∂D ≤ ∫ z, (Loss L h z - Loss L h' z) ∂D :=
    integral_mono (integrable_const _) (hfi.sub hgi) (fun z => (abs_le.mp (hp z)).1)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1 h2
  rw [abs_le]; constructor <;> linarith

open MeasureTheory FoundationsML.Stability in
theorem StabGenBD01f6_emp_diff {X Y Y' : Type*} {m : ℕ} (L : Y' → Y → ℝ) (h h' : X → Y') (M c : ℝ)
    (S S' : Fin m → X × Y) (i : Fin m) (hS : ∀ j, j ≠ i → S' j = S j)
    (hfb : ∀ z, 0 ≤ Loss L h z ∧ Loss L h z ≤ M) (hgb : ∀ z, 0 ≤ Loss L h' z ∧ Loss L h' z ≤ M)
    (hp : ∀ z, |Loss L h z - Loss L h' z| ≤ c) :
    |EmpiricalError L S h - EmpiricalError L S' h'| ≤ c + M / m := by
  unfold EmpiricalError
  have hm : (0:ℝ) < m := by exact_mod_cast Fin.pos i
  have hterm : ∀ j, |Loss L h (S j) - Loss L h' (S' j)| ≤ c + (if j = i then M else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      have hc : 0 ≤ c := le_trans (abs_nonneg _) (hp (S j))
      rw [if_pos rfl, abs_le]
      constructor <;> linarith [(hfb (S j)).1, (hfb (S j)).2, (hgb (S' j)).1, (hgb (S' j)).2]
    · rw [if_neg hj, hS j hj, add_zero]
      exact hp (S j)
  have hsum : |∑ j, (Loss L h (S j) - Loss L h' (S' j))| ≤ ∑ j, (c + if j = i then M else 0) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
  have hsum2 : ∑ j : Fin m, (c + if j = i then M else 0) = m * c + M := by
    simp [Finset.sum_add_distrib]
  rw [hsum2] at hsum
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / m)]
  calc 1 / (m:ℝ) * |∑ j, (Loss L h (S j) - Loss L h' (S' j))| ≤ 1 / m * (m * c + M) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = c + M / m := by field_simp

open MeasureTheory FoundationsML.Stability in
theorem bd_emp {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : StabGen.Uniform.HasUniformStability L A m β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' : X × Y),
      |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        - (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z')))
            - EmpiricalError L (StabGen.Hypothesis.replaceAt S i z') (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))))|
        ≤ 4 * β + M / m := by
  intro S i z'
  have hrem := StabGenBD01f6_removeAt_replaceAt S i z'
  have hp : ∀ z, |Loss L (A (StabGen.Hypothesis.trainingSet S)) z
      - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| ≤ 2 * β := by
    intro z
    have h1 := hstab S i z
    have h2 := hstab (StabGen.Hypothesis.replaceAt S i z') i z
    rw [hrem] at h2
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hmeas : ∀ T : Fin m → X × Y,
      Measurable (fun z => Loss L (A (StabGen.Hypothesis.trainingSet T)) z) := by
    intro T
    exact (hA m).comp measurable_prodMk_left
  have hR := StabGenBD01f6_gen_diff D L (A (StabGen.Hypothesis.trainingSet S))
    (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) M (2 * β)
    (hmeas S) (hmeas _) (hbound _) (hbound _) hp
  have hE := StabGenBD01f6_emp_diff L (A (StabGen.Hypothesis.trainingSet S))
    (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) M (2 * β)
    S (StabGen.Hypothesis.replaceAt S i z') i
    (fun j hj => by simp [StabGen.Hypothesis.replaceAt, Function.update_of_ne hj])
    (hbound _) (hbound _) hp
  rw [abs_le] at hR hE ⊢
  constructor <;> linarith [hR.1, hR.2, hE.1, hE.2]

open MeasureTheory FoundationsML.Stability in
theorem cce6_trainingSet_ofList {Z : Type*} (l : List Z) :
    ∃ U : Fin l.length → Z, StabGen.Hypothesis.trainingSet U = (l : Multiset Z) := by
  refine ⟨l.get, ?_⟩
  unfold StabGen.Hypothesis.trainingSet
  rw [Fin.univ_val_map, List.ofFn_get]

open MeasureTheory FoundationsML.Stability in
theorem cce6_removeAt_eq {Z : Type*} {n : ℕ} (U : Fin n → Z) (k : Fin n) :
    StabGen.Hypothesis.trainingSet U = U k ::ₘ StabGen.Hypothesis.removeAt U k := by
  classical
  unfold StabGen.Hypothesis.trainingSet StabGen.Hypothesis.removeAt
  rw [Finset.erase_val, ← Multiset.map_cons, Multiset.cons_erase (Finset.mem_univ k)]

open MeasureTheory FoundationsML.Stability in
theorem cce6_stab_ms {X Y Y' : Type*} (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y') (n : ℕ) (β : ℝ)
    (hstab : StabGen.Uniform.HasUniformStability L A n β)
    (a : X × Y) (V : Multiset (X × Y)) (hc : Multiset.card (a ::ₘ V) = n) (z : X × Y) :
    |Loss L (A (a ::ₘ V)) z - Loss L (A V) z| ≤ β := by
  classical
  obtain ⟨l, hl⟩ := Quot.exists_rep (a ::ₘ V)
  have hl' : ((l : Multiset (X × Y))) = a ::ₘ V := hl
  have hlen : l.length = n := by rw [← hc, ← hl']; simp
  subst hlen
  obtain ⟨U, hU⟩ := cce6_trainingSet_ofList l
  have ha : a ∈ StabGen.Hypothesis.trainingSet U := by rw [hU, hl']; simp
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 ha
  have h1 := hstab U k z
  have hT := cce6_removeAt_eq U k
  rw [hU, hl', hk] at hT
  have hV : StabGen.Hypothesis.removeAt U k = V := (Multiset.cons_inj_right a).1 hT.symm
  rw [hU, hl', hV] at h1
  exact h1

open MeasureTheory FoundationsML.Stability in
theorem cce6_removeAt_update {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) :
    StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') i
      = StabGen.Hypothesis.removeAt S i := by
  classical
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
  apply Multiset.map_congr rfl
  intro k hk
  have hk' : k ∈ (Finset.univ : Finset (Fin m)).erase i := hk
  have : k ≠ i := (Finset.mem_erase.1 hk').1
  simp [Function.update_of_ne this]

open MeasureTheory FoundationsML.Stability in
/-- For `j ≠ i`, the two leave-`j`-out sets are `S i ::ₘ V` and `z' ::ₘ V`. -/
theorem cce6_removeAt_split {Z : Type*} {m : ℕ} (S : Fin m → Z) (i j : Fin m) (z' : Z)
    (hij : j ≠ i) :
    ∃ V : Multiset Z, StabGen.Hypothesis.removeAt S j = S i ::ₘ V ∧
      StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') j = z' ::ₘ V := by
  classical
  refine ⟨((Finset.univ.erase j).erase i).val.map S, ?_, ?_⟩
  · unfold StabGen.Hypothesis.removeAt
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ i⟩
    conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase i _), Multiset.map_cons]
  · unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ i⟩
    conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase i _), Multiset.map_cons,
      Function.update_self]
    congr 1
    apply Multiset.map_congr rfl
    intro k hk
    have hk' : k ∈ ((Finset.univ : Finset (Fin m)).erase j).erase i := hk
    have : k ≠ i := (Finset.mem_erase.1 hk').1
    simp [Function.update_of_ne this]

open MeasureTheory FoundationsML.Stability in
theorem cce6_card_removeAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (j : Fin m) :
    Multiset.card (StabGen.Hypothesis.removeAt S j) = m - 1 := by
  classical
  unfold StabGen.Hypothesis.removeAt
  simp

open MeasureTheory FoundationsML.Stability in
theorem bd_loo {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : StabGen.Uniform.HasUniformStability L A m β)
    (hstab' : StabGen.Uniform.HasUniformStability L A (m - 1) β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' : X × Y),
      |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        - (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z')))
            - StabGen.Hypothesis.looError L A (StabGen.Hypothesis.replaceAt S i z'))|
        ≤ 4 * β + M / m := by
  intro S i z'
  set S' := StabGen.Hypothesis.replaceAt S i z' with hS'
  have hβ : 0 ≤ β := le_trans (abs_nonneg _) (hstab S i z')
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  -- pointwise 2β bound between the two full-sample hypotheses
  have hRR : StabGen.Hypothesis.removeAt S' i = StabGen.Hypothesis.removeAt S i :=
    cce6_removeAt_update S i z'
  have hpt : ∀ z, |Loss L (A (StabGen.Hypothesis.trainingSet S)) z
      - Loss L (A (StabGen.Hypothesis.trainingSet S')) z| ≤ 2 * β := by
    intro z
    have h1 := hstab S i z
    have h2 := hstab S' i z
    rw [hRR] at h2
    calc _ = |(Loss L (A (StabGen.Hypothesis.trainingSet S)) z
              - Loss L (A (StabGen.Hypothesis.removeAt S i)) z)
            - (Loss L (A (StabGen.Hypothesis.trainingSet S')) z
              - Loss L (A (StabGen.Hypothesis.removeAt S i)) z)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ β + β := add_le_add h1 h2
      _ = 2 * β := by ring
  have hint : ∀ T : Fin m → X × Y,
      Integrable (fun z => Loss L (A (StabGen.Hypothesis.trainingSet T)) z) D := by
    intro T
    have hmeas : Measurable (fun z => Loss L (A (StabGen.Hypothesis.trainingSet T)) z) :=
      (hA m).comp measurable_prodMk_left
    refine Integrable.of_bound hmeas.aestronglyMeasurable M (Filter.Eventually.of_forall ?_)
    intro z
    have := hbound (StabGen.Hypothesis.trainingSet T) z
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have hG : |GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
      - GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S'))| ≤ 2 * β := by
    unfold GeneralizationError
    rw [← integral_sub (hint S) (hint S')]
    have := norm_integral_le_of_norm_le_const (μ := D)
      (f := fun z => Loss L (A (StabGen.Hypothesis.trainingSet S)) z
        - Loss L (A (StabGen.Hypothesis.trainingSet S')) z)
      (C := 2 * β) (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]; exact hpt z))
    simpa [Real.norm_eq_abs] using this
  -- termwise loo bound
  have hterm : ∀ j : Fin m,
      |Loss L (A (StabGen.Hypothesis.removeAt S j)) (S j)
        - Loss L (A (StabGen.Hypothesis.removeAt S' j)) (S' j)|
        ≤ 2 * β + (if j = i then M else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, hRR]
      have h1 := hbound (StabGen.Hypothesis.removeAt S j) (S j)
      have h2 := hbound (StabGen.Hypothesis.removeAt S j) (S' j)
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [if_neg hj, add_zero]
      obtain ⟨V, h1, h2⟩ := cce6_removeAt_split S i j z' hj
      have hSj : S' j = S j := by
        rw [hS']; unfold StabGen.Hypothesis.replaceAt; exact Function.update_of_ne hj _ _
      rw [hSj]
      have hc1 : Multiset.card (S i ::ₘ V) = m - 1 := by rw [← h1]; exact cce6_card_removeAt S j
      have hc2 : Multiset.card (z' ::ₘ V) = m - 1 := by
        rw [← h2]; exact cce6_card_removeAt S' j
      have e1 := cce6_stab_ms L A (m - 1) β hstab' (S i) V hc1 (S j)
      have e2 := cce6_stab_ms L A (m - 1) β hstab' z' V hc2 (S j)
      have h2' : StabGen.Hypothesis.removeAt S' j = z' ::ₘ V := by rw [hS']; exact h2
      rw [h1, h2']
      calc _ = |(Loss L (A (S i ::ₘ V)) (S j) - Loss L (A V) (S j))
              - (Loss L (A (z' ::ₘ V)) (S j) - Loss L (A V) (S j))| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ β + β := add_le_add e1 e2
        _ = 2 * β := by ring
  have hloo : |StabGen.Hypothesis.looError L A S - StabGen.Hypothesis.looError L A S'|
      ≤ 2 * β + M / m := by
    unfold StabGen.Hypothesis.looError
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / m)]
    have hs : |∑ j, (Loss L (A (StabGen.Hypothesis.removeAt S j)) (S j)
        - Loss L (A (StabGen.Hypothesis.removeAt S' j)) (S' j))|
        ≤ ∑ j : Fin m, (2 * β + (if j = i then M else 0)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hterm j))
    have hsum : ∑ j : Fin m, (2 * β + (if j = i then M else 0)) = m * (2 * β) + M := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), nsmul_eq_mul]
    rw [hsum] at hs
    calc 1 / (m:ℝ) * _ ≤ 1 / (m:ℝ) * (m * (2 * β) + M) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * β + M / m := by field_simp
  calc _ = |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
            - GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S')))
          - (StabGen.Hypothesis.looError L A S - StabGen.Hypothesis.looError L A S')| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ 2 * β + (2 * β + M / m) := add_le_add hG hloo
    _ = 4 * β + M / m := by ring



open MeasureTheory FoundationsML.Stability in
theorem bias_bounds {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) (hm : 1 ≤ m) :
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
        ∂(Measure.pi fun _ : Fin m => D) ≤ 2 * β) ∧
    (∫ S, (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        ∂(Measure.pi fun _ : Fin m => D) ≤ β) := by
  have hbdd : ∃ M' : ℝ, ∀ (T : Multiset (X × Y)) (z : X × Y), |Loss L (A T) z| ≤ M' :=
    ⟨M, fun T z => by rw [abs_le]; constructor <;> linarith [(hbound T z).1, (hbound T z).2]⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨ha, -, hc⟩ := lemma7_bias_identities D L A hA hbdd (n + 1) 0
  refine ⟨?_, ?_⟩
  · rw [ha]
    refine (le_abs_self _).trans (mcd_abs_integral_le_of_bdd _ _ _ fun p => ?_)
    exact rep_one L A (n + 1) β hstab p.1 0 p.2 p.2
  · rw [hc]
    refine (le_abs_self _).trans (mcd_abs_integral_le_of_bdd _ _ _ fun p => ?_)
    exact hstab p.1 0 p.2

lemma tail_rhs (n : ℕ) (β M ε : ℝ) :
    (if (∑ _i : Fin (n + 1), (4 * β + M / ((n + 1 : ℕ) : ℝ)) ^ 2) = 0 then (0 : ENNReal)
      else ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / ∑ _i : Fin (n + 1), (4 * β + M / ((n + 1 : ℕ) : ℝ)) ^ 2)))
    = (if 4 * ((n + 1 : ℕ) : ℝ) * β + M = 0 then 0
      else ENNReal.ofReal (Real.exp (-(2 * ((n + 1 : ℕ) : ℝ) * ε ^ 2) / (4 * ((n + 1 : ℕ) : ℝ) * β + M) ^ 2))) := by
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs : ∑ _i : Fin (n + 1), (4 * β + M / ((n + 1 : ℕ) : ℝ)) ^ 2
      = (4 * ((n + 1 : ℕ) : ℝ) * β + M) ^ 2 / ((n + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hs]
  by_cases hK : 4 * ((n + 1 : ℕ) : ℝ) * β + M = 0
  · have hz : (4 * ((n + 1 : ℕ) : ℝ) * β + M) ^ 2 / ((n + 1 : ℕ) : ℝ) = 0 := by rw [hK]; simp
    rw [if_pos hz, if_pos hK]
  · have hne : (4 * ((n + 1 : ℕ) : ℝ) * β + M) ^ 2 / ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      div_ne_zero (pow_ne_zero 2 hK) hN.ne'
    rw [if_neg hne, if_neg hK]
    congr 2
    field_simp

open MeasureTheory FoundationsML.Stability in
theorem tail_bounds {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin m => D)
        {S | ε + 2 * β <
          GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S))}
      ≤ (if 4 * m * β + M = 0 then 0
         else ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2) / (4 * m * β + M) ^ 2))) ∧
    (HasUniformStability L A (m - 1) β →
      (Measure.pi fun _ : Fin m => D)
          {S | ε + β < GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S}
        ≤ (if 4 * m * β + M = 0 then 0
           else ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2) / (4 * m * β + M) ^ 2)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hb1, hb2⟩ := bias_bounds D L A hA M hbound (n + 1) β hstab hm
  have hR : Measurable (fun S : Fin (n + 1) → X × Y =>
      GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))) := by
    have h0 : StronglyMeasurable (Function.uncurry
        (fun (S : Fin (n + 1) → X × Y) (z : X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet S)) z)) :=
      (hA (n + 1)).stronglyMeasurable
    exact (h0.integral_prod_right (ν := D)).measurable
  have hEmp : Measurable (fun S : Fin (n + 1) → X × Y =>
      EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S))) := by
    show Measurable (fun S : Fin (n + 1) → X × Y =>
      (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, Loss L (A (StabGen.Hypothesis.trainingSet S)) (S i))
    exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      (hA (n + 1)).comp (measurable_id.prodMk (measurable_pi_apply i))) _
  have hLoo : Measurable (fun S : Fin (n + 1) → X × Y => StabGen.Hypothesis.looError L A S) := by
    show Measurable (fun S : Fin (n + 1) → X × Y =>
      (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, Loss L (A (StabGen.Hypothesis.removeAt S i)) (S i))
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    have hm : Measurable (fun S : Fin (n + 1) → X × Y => ((fun k : Fin n => S (i.succAbove k)), S i)) :=
      (measurable_pi_lambda _ fun k => measurable_pi_apply _).prodMk (measurable_pi_apply i)
    have := (hA n).comp hm
    convert this using 1
    funext S
    simp [b2_removeAt_eq]
  refine ⟨?_, fun hst' => ?_⟩
  · have c1 := mcdiarmid_inequality D
      (fun S : Fin (n + 1) → X × Y => GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
        - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
      (hR.sub hEmp) (fun _ => 4 * β + M / ((n + 1 : ℕ) : ℝ))
      (fun S i z' => bd_emp D L A hA M hbound (n + 1) β hstab S i z') ε hε
    refine (measure_mono ?_).trans (c1.trans (le_of_eq (tail_rhs n β M ε)))
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    linarith [hb1]
  · have c1 := mcdiarmid_inequality D
      (fun S : Fin (n + 1) → X × Y => GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
        - StabGen.Hypothesis.looError L A S)
      (hR.sub hLoo) (fun _ => 4 * β + M / ((n + 1 : ℕ) : ℝ))
      (fun S i z' => bd_loo D L A hA M hbound (n + 1) β hstab hst' S i z') ε hε
    refine (measure_mono ?_).trans (c1.trans (le_of_eq (tail_rhs n β M ε)))
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    linarith [hb2]

lemma glue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → ℝ) (c0 K : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hK : 0 ≤ K) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h : ∀ ε : ℝ, 0 < ε → μ {S | ε + c0 < G S}
      ≤ (if K = 0 then 0 else ENNReal.ofReal (Real.exp (-(2 * m * ε ^ 2) / K ^ 2)))) :
    μ {S | K * Real.sqrt (Real.log (1 / δ) / (2 * m)) + c0 < G S} ≤ ENNReal.ofReal δ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hK0 : K = 0
  · subst hK0
    have hnull : μ {S | c0 < G S} = 0 := by
      have hsub : {S | c0 < G S} ⊆ ⋃ k : ℕ, {S | 1 / ((k : ℝ) + 1) + c0 < G S} := by
        intro S hS
        simp only [Set.mem_setOf_eq] at hS
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hS)
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨k, by linarith⟩
      refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
      have := h (1 / ((k : ℝ) + 1)) (by positivity)
      simpa using this
    have : {S | (0 : ℝ) * Real.sqrt (Real.log (1 / δ) / (2 * m)) + c0 < G S} = {S | c0 < G S} := by
      ext S; simp
    rw [this, hnull]
    exact bot_le
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have hlog : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ0).mpr hδ1)
    have hsq : 0 < Real.sqrt (Real.log (1 / δ) / (2 * m)) := Real.sqrt_pos.mpr (by positivity)
    have hε : 0 < K * Real.sqrt (Real.log (1 / δ) / (2 * m)) := mul_pos hKpos hsq
    refine (h _ hε).trans ?_
    rw [if_neg hK0]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hsq2 : Real.sqrt (Real.log (1 / δ) / (2 * m)) ^ 2 = Real.log (1 / δ) / (2 * m) :=
      Real.sq_sqrt (by positivity)
    have : -(2 * (m : ℝ) * (K * Real.sqrt (Real.log (1 / δ) / (2 * m))) ^ 2) / K ^ 2
        = -Real.log (1 / δ) := by
      rw [mul_pow, hsq2]
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    simp

end StabGen.Uniform

open MeasureTheory FoundationsML.Stability StabGen.Uniform in
theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β)
    (hm : 1 ≤ m) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (Measure.pi fun _ : Fin m => D)
        {S | EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)) + 2 * β
              + (4 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))
            < GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))}
      ≤ ENNReal.ofReal δ ∧
    (HasUniformStability L A (m - 1) β →
      (Measure.pi fun _ : Fin m => D)
          {S | StabGen.Hypothesis.looError L A S + β + (4 * m * β + M) * Real.sqrt (Real.log (1 / δ) / (2 * m))
              < GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))}
        ≤ ENNReal.ofReal δ) := by
  have hz : Nonempty (X × Y) := nonempty_of_isProbabilityMeasure D
  obtain ⟨z0⟩ := hz
  have hM : 0 ≤ M := le_trans (hbound 0 z0).1 (hbound 0 z0).2
  have hβ : 0 ≤ β := by
    have := hstab (fun _ => z0) ⟨0, hm⟩ z0
    exact le_trans (abs_nonneg _) this
  have hK : 0 ≤ 4 * (m : ℝ) * β + M := by positivity
  refine ⟨?_, fun hst' => ?_⟩
  · have hg := glue (Measure.pi fun _ : Fin m => D)
      (fun S : Fin m → X × Y => GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
        - EmpiricalError L S (A (StabGen.Hypothesis.trainingSet S)))
      (2 * β) (4 * (m : ℝ) * β + M) m hm hK δ hδ0 hδ1
      (fun ε hε => (tail_bounds D L A hA M hbound m β hstab hm ε hε).1)
    refine le_trans (le_of_eq ?_) hg
    congr 1
    ext S
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  · have hg := glue (Measure.pi fun _ : Fin m => D)
      (fun S : Fin m → X × Y => GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
        - StabGen.Hypothesis.looError L A S)
      β (4 * (m : ℝ) * β + M) m hm hK δ hδ0 hδ1
      (fun ε hε => (tail_bounds D L A hA M hbound m β hstab hm ε hε).2 hst')
    refine le_trans (le_of_eq ?_) hg
    congr 1
    ext S
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
