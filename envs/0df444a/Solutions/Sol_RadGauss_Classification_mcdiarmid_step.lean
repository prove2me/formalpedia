-- Prove2me | solution 1 for RadGauss.Classification.mcdiarmid_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:06:34.780706+00:00
-- url     : https://prove2.me/submissions/61200c25-fee2-4710-900c-0530b9f47865

import Mathlib
import Definitions.Def_RadGauss_Classification_Classifier

open MeasureTheory


namespace RadGauss.Classification

theorem rg_mcd_mgf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c B t : ℝ) (hc : 0 ≤ c) : ∀ (m : ℕ) (f : (Fin m → Ω) → ℝ), Measurable f → (∀ x, |f x| ≤ B) →
    (∀ x i z, |f x - f (Function.update x i z)| ≤ c) →
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi fun _ => μ))) ∂(Measure.pi fun _ => μ)
      ≤ Real.exp (t ^ 2 * m * c ^ 2 / 8) := by
  intro m
  induction m with
  | zero =>
    intro f hf hB hbd
    have hcst : ∀ x, f x = f (fun i => i.elim0) := fun x => congrArg f (Subsingleton.elim _ _)
    simp [hcst]
  | succ m ih =>
    intro f hf hB hbd
    set πm : Measure (Fin m → Ω) := Measure.pi fun _ => μ with hπm
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ => μ) (μ.prod πm) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) 0
    have hes : ∀ p : Ω × (Fin m → Ω), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    have hint : ∀ φ : (Fin (m+1) → Ω) → ℝ, ∫ x, φ x ∂(Measure.pi fun _ => μ)
        = ∫ p, φ (Fin.cons p.1 p.2) ∂(μ.prod πm) := by
      intro φ
      rw [← hmp.symm.integral_comp' (g := φ)]
      simp only [hes]
    have hgm : Measurable (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) := by
      have : (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) = f ∘ e.symm := by
        funext p; simp [hes]
      rw [this]; exact hf.comp e.symm.measurable
    have hgint : Integrable (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) (μ.prod πm) :=
      Integrable.mono' (integrable_const B) hgm.aestronglyMeasurable
        (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB _)
    set h : Ω → ℝ := fun a => ∫ y, f (Fin.cons a y) ∂πm with hh
    have hhm : Measurable h := by
      have := StronglyMeasurable.integral_prod_right (ν := πm)
        (f := fun a y => f (Fin.cons a y)) hgm.stronglyMeasurable
      exact this.measurable
    have hhB : ∀ a, |h a| ≤ B := by
      intro a
      have : ‖h a‖ ≤ B := by
        refine (norm_integral_le_of_norm_le_const (C := B) ?_).trans (by simp)
        exact ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB _
      simpa [Real.norm_eq_abs] using this
    have hslice : ∀ a, Integrable (fun y => f (Fin.cons a y)) πm := by
      intro a
      exact Integrable.mono' (integrable_const B)
        (hgm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB _)
    have hhd : ∀ a a', h a - h a' ≤ c := by
      intro a a'
      simp only [hh]
      rw [← integral_sub (hslice a) (hslice a')]
      have : ∫ y, (f (Fin.cons a y) - f (Fin.cons a' y)) ∂πm ≤ ∫ _y, c ∂πm := by
        refine integral_mono (by exact (hslice a).sub (hslice a')) (integrable_const c) ?_
        intro y
        have := hbd (Fin.cons a y) 0 a'
        rw [Fin.update_cons_zero] at this
        exact (le_abs_self _).trans this
      simpa using this
    set E := ∫ y, f y ∂(Measure.pi fun _ => μ) with hE
    have hE' : E = ∫ a, h a ∂μ := by
      rw [hE, hint f]
      exact integral_prod _ hgint
    -- IH applied to slices
    have hK : ∀ a, ∫ y, Real.exp (t * (f (Fin.cons a y) - h a)) ∂πm
        ≤ Real.exp (t ^ 2 * m * c ^ 2 / 8) := by
      intro a
      refine ih (fun y => f (Fin.cons a y)) (hgm.comp (measurable_const.prodMk measurable_id))
        (fun y => hB _) ?_
      intro x i z
      rw [Fin.cons_update]
      exact hbd _ _ _
    set K := Real.exp (t ^ 2 * m * c ^ 2 / 8) with hKdef
    -- Hoeffding for h - E
    obtain ⟨a0⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    set lo := sInf (Set.range h) with hlo
    have hbdd : BddBelow (Set.range h) := ⟨-B, by
      rintro _ ⟨a, rfl⟩; have := hhB a; exact (abs_le.mp this).1⟩
    have hIcc : ∀ a, h a - E ∈ Set.Icc (lo - E) (lo + c - E) := by
      intro a
      constructor
      · have : lo ≤ h a := csInf_le hbdd ⟨a, rfl⟩
        linarith
      · have : h a - c ≤ lo := le_csInf ⟨h a0, a0, rfl⟩ (by
          rintro _ ⟨a', rfl⟩; have := hhd a a'; linarith)
        linarith
    have hX0 : ∫ a, (h a - E) ∂μ = 0 := by
      rw [integral_sub, hE']
      · simp
      · exact Integrable.mono' (integrable_const B) hhm.aestronglyMeasurable
          (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hhB a)
      · exact integrable_const _
    have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hhm.sub measurable_const).aemeasurable (ae_of_all _ hIcc) hX0
    have hmgf := hsg.mgf_le t
    have hcc : (((‖lo + c - E - (lo - E)‖₊ / 2) ^ 2 : NNReal) : ℝ) = c ^ 2 / 4 := by
      have : lo + c - E - (lo - E) = c := by ring
      rw [this]
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg hc]; ring
    rw [hcc] at hmgf
    unfold ProbabilityTheory.mgf at hmgf
    -- main chain
    rw [hint]
    have hexpint : Integrable (fun p : Ω × (Fin m → Ω) =>
        Real.exp (t * (f (Fin.cons p.1 p.2) - E))) (μ.prod πm) := by
      refine Integrable.mono' (integrable_const (Real.exp (|t| * (B + |E|)))) ?_ ?_
      · exact (Real.measurable_exp.comp ((hgm.sub measurable_const).const_mul t)).aestronglyMeasurable
      · refine ae_of_all _ fun p => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hB (Fin.cons p.1 p.2)
        calc t * (f (Fin.cons p.1 p.2) - E) ≤ |t * (f (Fin.cons p.1 p.2) - E)| := le_abs_self _
          _ = |t| * |f (Fin.cons p.1 p.2) - E| := abs_mul _ _
          _ ≤ |t| * (B + |E|) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (abs_sub _ _).trans (by linarith)
    rw [integral_prod _ hexpint]
    have hhint : Integrable (fun a => Real.exp (t * (h a - E))) μ := by
      refine Integrable.mono' (integrable_const (Real.exp (|t| * (B + |E|)))) ?_ ?_
      · exact (Real.measurable_exp.comp ((hhm.sub measurable_const).const_mul t)).aestronglyMeasurable
      · refine ae_of_all _ fun a => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 := hhB a
        calc t * (h a - E) ≤ |t * (h a - E)| := le_abs_self _
          _ = |t| * |h a - E| := abs_mul _ _
          _ ≤ |t| * (B + |E|) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (abs_sub _ _).trans (by linarith)
    calc ∫ a, ∫ y, Real.exp (t * (f (Fin.cons (a, y).1 (a, y).2) - E)) ∂πm ∂μ
        ≤ ∫ a, Real.exp (t * (h a - E)) * K ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun y =>
            (Real.exp_pos _).le) (hhint.mul_const K) (ae_of_all _ fun a => ?_)
          have heq : ∀ y, Real.exp (t * (f (Fin.cons (a, y).1 (a, y).2) - E))
              = Real.exp (t * (h a - E)) * Real.exp (t * (f (Fin.cons a y) - h a)) := by
            intro y; rw [← Real.exp_add]; ring_nf
          simp only [heq]
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hK a) (Real.exp_pos _).le
      _ = (∫ a, Real.exp (t * (h a - E)) ∂μ) * K := integral_mul_const _ _
      _ ≤ Real.exp (c ^ 2 / 4 * t ^ 2 / 2) * K :=
          mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * ((m + 1 : ℕ) : ℝ) * c ^ 2 / 8) := by
          rw [hKdef, ← Real.exp_add]; push_cast; ring_nf


theorem rg_classError_mem {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (f : X → ℤˣ) : 0 ≤ classError P f ∧ classError P f ≤ 1 := by
  unfold classError
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem rg_trainError_mem {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (f : X → ℤˣ) :
    0 ≤ trainError S f ∧ trainError S f ≤ 1 := by
  unfold trainError
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [div_le_one (by exact_mod_cast hn)]
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => (S i).2 ≠ f (S i).1)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this

theorem rg_gap_bdd {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) {n : ℕ} (S : Fin n → X × ℤˣ) :
    BddAbove (Set.range fun f : F => classError P f - trainError S f) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨f, rfl⟩
  have := rg_classError_mem P f; have := rg_trainError_mem S f
  simp only; linarith

theorem rg_gapSup_abs {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty) {n : ℕ}
    (S : Fin n → X × ℤˣ) : |gapSup P F S| ≤ 1 := by
  obtain ⟨f0, hf0⟩ := hFne
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  rw [abs_le]; unfold gapSup
  constructor
  · have h1 := rg_classError_mem P f0; have h2 := rg_trainError_mem S f0
    have := le_ciSup (rg_gap_bdd P F S) ⟨f0, hf0⟩
    simp only at this; linarith
  · refine ciSup_le fun f => ?_
    have := rg_classError_mem P f; have := rg_trainError_mem S f
    linarith

theorem rg_train_diff {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (i : Fin n) (z : X × ℤˣ)
    (f : X → ℤˣ) : |trainError S f - trainError (Function.update S i z) f| ≤ 1 / n := by
  unfold trainError
  rw [Finset.card_filter, Finset.card_filter]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∑ x ∈ Finset.univ.erase i, (if (Function.update S i z x).2 ≠ f (Function.update S i z x).1 then 1 else 0)
      = ∑ x ∈ Finset.univ.erase i, (if (S x).2 ≠ f (S x).1 then 1 else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hrest]
  simp only [Function.update_self]
  rw [← sub_div, abs_div, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  push_cast
  split_ifs <;> norm_num

theorem rg_gapSup_le {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty) {n : ℕ}
    (S : Fin n → X × ℤˣ) (i : Fin n) (z : X × ℤˣ) :
    gapSup P F S ≤ gapSup P F (Function.update S i z) + 1 / n := by
  obtain ⟨f0, hf0⟩ := hFne
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  unfold gapSup
  refine ciSup_le fun f => ?_
  have h1 := le_ciSup (rg_gap_bdd P F (Function.update S i z)) f
  have h2 := rg_train_diff S i z f
  have := (abs_le.mp h2).1
  linarith

theorem rg_gapSup_bd {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty) {n : ℕ}
    (S : Fin n → X × ℤˣ) (i : Fin n) (z : X × ℤˣ) :
    |gapSup P F S - gapSup P F (Function.update S i z)| ≤ 1 / n := by
  rw [abs_le]
  have h1 := rg_gapSup_le P F hFne S i z
  have h2 := rg_gapSup_le P F hFne (Function.update S i z) i (S i)
  rw [Function.update_idem, Function.update_eq_self] at h2
  constructor <;> linarith

theorem mcdiarmid_step_core {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (classError P f ≤ trainError S f
            + (∫ S', gapSup P F S' ∂(Measure.pi fun _ : Fin n => P))
            + Real.sqrt (Real.log (1 / δ) / (2 * n)))}
      ≤ ENNReal.ofReal δ := by
  set μn := Measure.pi fun _ : Fin n => P with hμn
  set E := ∫ S', gapSup P F S' ∂μn with hE
  set ε := Real.sqrt (Real.log (1 / δ) / (2 * n)) with hε
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hε2 : ε ^ 2 = Real.log (1 / δ) / (2 * n) := Real.sq_sqrt (by positivity)
  have hsub : {S : Fin n → X × ℤˣ | ∃ f ∈ F, ¬ (classError P f ≤ trainError S f + E + ε)}
      ⊆ {S : Fin n → X × ℤˣ | ε ≤ gapSup P F S - E} := by
    rintro S ⟨f, hf, hne⟩
    simp only [Set.mem_setOf_eq]
    have := le_ciSup (rg_gap_bdd P F S) ⟨f, hf⟩
    simp only at this
    unfold gapSup; push_neg at hne; linarith
  refine (measure_mono hsub).trans ?_
  set t : ℝ := 4 * ε * n with ht
  have ht0 : 0 ≤ t := by positivity
  have hmgf := rg_mcd_mgf P (1 / n) 1 t (by positivity) n (fun S => gapSup P F S) hgap
    (fun S => rg_gapSup_abs P F hFne S) (fun S i z => rg_gapSup_bd P F hFne S i z)
  have hint : Integrable (fun S => Real.exp (t * (gapSup P F S - E))) μn := by
    refine Integrable.mono' (integrable_const (Real.exp (|t| * (1 + |E|)))) ?_ ?_
    · exact (Real.measurable_exp.comp ((hgap.sub measurable_const).const_mul t)).aestronglyMeasurable
    · refine ae_of_all _ fun S => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := rg_gapSup_abs P F hFne S
      calc t * (gapSup P F S - E) ≤ |t * (gapSup P F S - E)| := le_abs_self _
        _ = |t| * |gapSup P F S - E| := abs_mul _ _
        _ ≤ |t| * (1 + |E|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (abs_sub _ _).trans (by linarith)
  have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μn)
    (X := fun S => gapSup P F S - E) ε ht0 hint
  unfold ProbabilityTheory.mgf at hch
  have hfin : Real.exp (-t * ε) * Real.exp (t ^ 2 * n * (1 / n) ^ 2 / 8) = δ := by
    rw [← Real.exp_add]
    have : -t * ε + t ^ 2 * n * (1 / n) ^ 2 / 8 = - Real.log (1 / δ) := by
      rw [ht]; field_simp; rw [hε2]; field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]; simp
  have hreal : μn.real {S | ε ≤ gapSup P F S - E} ≤ δ := by
    refine hch.trans ?_
    rw [← hfin]
    exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

end RadGauss.Classification

open RadGauss.Classification


theorem solution {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (classError P f ≤ trainError S f
            + (∫ S', gapSup P F S' ∂(Measure.pi fun _ : Fin n => P))
            + Real.sqrt (Real.log (1 / δ) / (2 * n)))}
      ≤ ENNReal.ofReal δ := by
  exact mcdiarmid_step_core P F hFne n hn δ hδ0 hδ1 hgap
