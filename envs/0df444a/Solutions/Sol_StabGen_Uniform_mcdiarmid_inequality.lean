-- Prove2me | solution 1 for StabGen.Uniform.mcdiarmid_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:23:57.86306+00:00
-- url     : https://prove2.me/submissions/45fd40bd-d2a4-4dc9-93d2-167c7cef6cce

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

-- carved verbatim out of submission 08fae585-26d2-48c6-bea0-1df5b249980c, lines 199-281

section
set_option autoImplicit false
open MeasureTheory FoundationsML.Stability
open StabGen
open StabGen.Uniform
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

theorem solution {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
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
