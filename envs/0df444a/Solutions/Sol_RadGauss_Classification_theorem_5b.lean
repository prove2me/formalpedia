-- Prove2me | solution 1 for RadGauss.Classification.theorem_5b
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:19:49.852521+00:00
-- url     : https://prove2.me/submissions/f5b2aece-fa11-4183-afe5-7a1e978a2288

import Mathlib
import Definitions.Def_RadGauss_Classification_Complexity
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



instance rgUnitsMSC : MeasurableSingletonClass ℤˣ := by
  constructor
  intro u
  exact ⟨{u.val}, measurableSet_singleton _, by ext v; simp [Units.ext_iff]⟩

theorem rg_int_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (g : α → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ a, |g a| ≤ C) : Integrable g μ :=
  Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
    (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hC a)

/-- 0-1 loss. -/
noncomputable def rgLoss {X : Type*} (f : X → ℤˣ) (z : X × ℤˣ) : ℝ :=
  if z.2 ≠ f z.1 then 1 else 0

theorem rg_loss_eq {X : Type*} (f : X → ℤˣ) (z : X × ℤˣ) :
    rgLoss f z = (1 - ((z.2 : ℤ) : ℝ) * ((f z.1 : ℤ) : ℝ)) / 2 := by
  unfold rgLoss
  rcases Int.units_eq_one_or z.2 with h1 | h1 <;> rcases Int.units_eq_one_or (f z.1) with h2 | h2 <;>
    simp [h1, h2] <;> norm_num

theorem rg_loss_meas {X : Type*} [MeasurableSpace X] (f : X → ℤˣ) (hf : Measurable f) :
    Measurable (rgLoss f) := by
  have : rgLoss f = (fun p : ℤˣ × ℤˣ => if p.2 ≠ p.1 then (1 : ℝ) else 0) ∘
      (fun z : X × ℤˣ => (f z.1, z.2)) := by
    funext z; rfl
  rw [this]
  exact (measurable_of_countable _).comp ((hf.comp measurable_fst).prodMk measurable_snd)

theorem rg_loss_abs {X : Type*} (f : X → ℤˣ) (z : X × ℤˣ) : |rgLoss f z| ≤ 1 := by
  unfold rgLoss; split_ifs <;> simp

theorem rg_train_eq {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (f : X → ℤˣ) :
    trainError S f = (∑ i, rgLoss f (S i)) / n := by
  unfold trainError rgLoss
  rw [Finset.card_filter]; push_cast; rfl

theorem rg_classError_eq {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (f : X → ℤˣ) (hf : Measurable f) :
    classError P f = ∫ z, rgLoss f z ∂P := by
  have hs : MeasurableSet {z : X × ℤˣ | z.2 ≠ f z.1} := by
    have : {z : X × ℤˣ | z.2 ≠ f z.1} = (fun z : X × ℤˣ => (f z.1, z.2)) ⁻¹'
        {p : ℤˣ × ℤˣ | p.2 ≠ p.1} := rfl
    rw [this]
    exact ((hf.comp measurable_fst).prodMk measurable_snd) (Set.to_countable _).measurableSet
  have : rgLoss f = {z : X × ℤˣ | z.2 ≠ f z.1}.indicator 1 := by
    funext z; unfold rgLoss; simp [Set.indicator]
  rw [this, integral_indicator_one hs]; rfl

theorem rg_train_meas {X : Type*} [MeasurableSpace X] (n : ℕ) (f : X → ℤˣ) (hf : Measurable f) :
    Measurable (fun S : Fin n → X × ℤˣ => trainError S f) := by
  simp_rw [rg_train_eq]
  exact (Finset.measurable_sum _ fun i _ => (rg_loss_meas f hf).comp (measurable_pi_apply i)).div_const _

theorem rg_trainError_mem' {X : Type*} {n : ℕ} (S : Fin n → X × ℤˣ) (f : X → ℤˣ) :
    0 ≤ trainError S f ∧ trainError S f ≤ 1 := by
  unfold trainError
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [div_le_one (by exact_mod_cast hn)]
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => (S i).2 ≠ f (S i).1)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this

theorem rg_classError_int {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (f : X → ℤˣ) (hf : Measurable f) (n : ℕ) (hn : 0 < n) :
    classError P f = ∫ S, trainError S f ∂(Measure.pi fun _ : Fin n => P) := by
  simp_rw [rg_train_eq]
  rw [integral_div, integral_finset_sum]
  · have : ∀ i : Fin n, ∫ S, rgLoss f (S i) ∂(Measure.pi fun _ : Fin n => P) = classError P f := by
      intro i
      rw [rg_classError_eq P f hf]
      have hmp := measurePreserving_eval (fun _ : Fin n => P) i
      have := integral_map (μ := Measure.pi fun _ : Fin n => P) (φ := Function.eval i)
        (measurable_pi_apply i).aemeasurable (f := rgLoss f) (rg_loss_meas f hf).aestronglyMeasurable
      rw [hmp.map_eq] at this
      exact this.symm
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · intro i _
    exact rg_int_bdd _ _ ((rg_loss_meas f hf).comp (measurable_pi_apply i)) 1 (fun S => rg_loss_abs _ _)

theorem rg_ghost_bdd {X : Type*} (F : Set (X → ℤˣ)) {n : ℕ} (S S' : Fin n → X × ℤˣ) :
    BddAbove (Set.range fun f : F => trainError S' f - trainError S f) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨f, rfl⟩
  have := rg_trainError_mem' S f; have := rg_trainError_mem' S' f
  simp only; linarith

theorem rg_ghost_abs {X : Type*} (F : Set (X → ℤˣ)) (hFne : F.Nonempty) {n : ℕ}
    (S S' : Fin n → X × ℤˣ) : |ghostGapSup F S S'| ≤ 1 := by
  obtain ⟨f0, hf0⟩ := hFne
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  rw [abs_le]; unfold ghostGapSup
  constructor
  · have h1 := rg_trainError_mem' S f0; have h2 := rg_trainError_mem' S' f0
    have := le_ciSup (rg_ghost_bdd F S S') ⟨f0, hf0⟩
    simp only at this; linarith
  · refine ciSup_le fun f => ?_
    have := rg_trainError_mem' S f; have := rg_trainError_mem' S' f
    linarith

theorem rg_gapSup_abs' {X : Type*} [MeasurableSpace X] (P : Measure (X × ℤˣ))
    [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty) {n : ℕ}
    (S : Fin n → X × ℤˣ) : |gapSup P F S| ≤ 1 := by
  obtain ⟨f0, hf0⟩ := hFne
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  have hb : BddAbove (Set.range fun f : F => classError P f - trainError S f) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨f, rfl⟩
    have : 0 ≤ classError P f ∧ classError P f ≤ 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
    have := rg_trainError_mem' S f
    simp only; linarith
  rw [abs_le]; unfold gapSup
  constructor
  · have h1 : 0 ≤ classError P f0 := measureReal_nonneg
    have h2 := rg_trainError_mem' S f0
    have := le_ciSup hb ⟨f0, hf0⟩
    simp only at this; linarith
  · refine ciSup_le fun f => ?_
    have : classError P f ≤ 1 := measureReal_le_one
    have := rg_trainError_mem' S f
    linarith

/-- coordinatewise swap. -/
def rgSw {Z : Type*} {n : ℕ} (σ : Fin n → ℤˣ) (p : (Fin n → Z) × (Fin n → Z)) :
    (Fin n → Z) × (Fin n → Z) :=
  (fun i => if σ i = 1 then p.1 i else p.2 i, fun i => if σ i = 1 then p.2 i else p.1 i)

theorem rg_sw_mp {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Fin n → ℤˣ) :
    MeasurePreserving (rgSw σ) ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow Z Z (Fin n) (fun _ => μ) (fun _ => μ)
  have hmid : MeasurePreserving (fun (q : Fin n → Z × Z) i => (if σ i = 1 then q i else (q i).swap))
      (Measure.pi fun _ => μ.prod μ) (Measure.pi fun _ => μ.prod μ) := by
    refine measurePreserving_pi (fun _ : Fin n => μ.prod μ) (fun _ => μ.prod μ)
      (f := fun i (z : Z × Z) => if σ i = 1 then z else z.swap) fun i => ?_
    by_cases h : σ i = 1
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h, if_false]; exact Measure.measurePreserving_swap
  have := he.comp (hmid.comp he.symm)
  convert this using 1
  funext p
  simp only [Function.comp, rgSw]
  ext i <;> by_cases h : σ i = 1 <;> simp [h, MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]


/-- the Rademacher summand. -/
noncomputable def rgG {X : Type*} (F : Set (X → ℤˣ)) (n : ℕ) (x : Fin n → X) (τ : Fin n → ℤˣ) :
    ENNReal :=
  ⨆ g ∈ realClass F, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, ((τ i : ℤ) : ℝ) * g (x i)|

theorem rg_loss_diff {X : Type*} (f : X → ℤˣ) (s : ℤˣ) (z z' : X × ℤˣ) (hs : s = 1 ∨ s = -1) :
    rgLoss f (if s = 1 then z' else z) - rgLoss f (if s = 1 then z else z')
      = (((s * z.2 : ℤˣ) : ℤ) : ℝ) * ((f z.1 : ℤ) : ℝ) / 2
        + (((s * -z'.2 : ℤˣ) : ℤ) : ℝ) * ((f z'.1 : ℤ) : ℝ) / 2 := by
  rcases hs with h | h
  · simp only [h, if_true, rg_loss_eq]; push_cast; ring
  · have : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [h, this, if_false, rg_loss_eq]; push_cast; ring

theorem rg_pointwise_real {X : Type*} (n : ℕ) (hn : 0 < n)
    (σ : Fin n → ℤˣ) (p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ)) (f : X → ℤˣ) :
    trainError (rgSw σ p).2 f - trainError (rgSw σ p).1 f
      = (2 / (n : ℝ)) * (∑ i, (((σ * fun i => (p.1 i).2) i : ℤ) : ℝ) * ((f (p.1 i).1 : ℤ) : ℝ)) / 4
        + (2 / (n : ℝ)) * (∑ i, (((σ * fun i => -(p.2 i).2) i : ℤ) : ℝ) * ((f (p.2 i).1 : ℤ) : ℝ)) / 4 := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rg_train_eq, rg_train_eq, ← sub_div, ← Finset.sum_sub_distrib]
  have : ∀ i, rgLoss f ((rgSw σ p).2 i) - rgLoss f ((rgSw σ p).1 i)
      = (((σ * fun i => (p.1 i).2) i : ℤ) : ℝ) * ((f (p.1 i).1 : ℤ) : ℝ) / 2
        + (((σ * fun i => -(p.2 i).2) i : ℤ) : ℝ) * ((f (p.2 i).1 : ℤ) : ℝ) / 2 := by
    intro i
    exact rg_loss_diff f (σ i) (p.1 i) (p.2 i) (Int.units_eq_one_or _)
  simp only [this, Finset.sum_add_distrib, ← Finset.sum_div]
  field_simp
  ring

theorem rg_pointwise {X : Type*} (F : Set (X → ℤˣ)) (hFne : F.Nonempty) (n : ℕ) (hn : 0 < n)
    (σ : Fin n → ℤˣ) (p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ)) :
    ENNReal.ofReal (ghostGapSup F (rgSw σ p).1 (rgSw σ p).2)
      ≤ (1 / 4) * (rgG F n (fun i => (p.1 i).1) (σ * fun i => (p.1 i).2)
          + rgG F n (fun i => (p.2 i).1) (σ * fun i => -(p.2 i).2)) := by
  obtain ⟨f0, hf0⟩ := hFne
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  have hreal : ∀ f : F, ENNReal.ofReal (trainError (rgSw σ p).2 f - trainError (rgSw σ p).1 f)
      ≤ (1 / 4) * (rgG F n (fun i => (p.1 i).1) (σ * fun i => (p.1 i).2)
          + rgG F n (fun i => (p.2 i).1) (σ * fun i => -(p.2 i).2)) := by
    intro f
    rw [rg_pointwise_real n hn σ p f.1]
    generalize hu : (2 / (n : ℝ)) * (∑ i, (((σ * fun i => (p.1 i).2) i : ℤ) : ℝ) * ((f.1 (p.1 i).1 : ℤ) : ℝ)) = u
    generalize hv : (2 / (n : ℝ)) * (∑ i, (((σ * fun i => -(p.2 i).2) i : ℤ) : ℝ) * ((f.1 (p.2 i).1 : ℤ) : ℝ)) = v
    have hgf : (fun x => ((f.1 x : ℤ) : ℝ)) ∈ realClass F := ⟨f.1, f.2, rfl⟩
    have h1 : ENNReal.ofReal |u| ≤ rgG F n (fun i => (p.1 i).1) (σ * fun i => (p.1 i).2) := by
      unfold rgG
      refine le_trans ?_ (le_iSup₂ (fun x => ((f.1 x : ℤ) : ℝ)) hgf)
      rw [← hu]
    have h2 : ENNReal.ofReal |v| ≤ rgG F n (fun i => (p.2 i).1) (σ * fun i => -(p.2 i).2) := by
      unfold rgG
      refine le_trans ?_ (le_iSup₂ (fun x => ((f.1 x : ℤ) : ℝ)) hgf)
      rw [← hv]
    have h4 : ENNReal.ofReal (1 / 4) = (1 / 4 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    calc ENNReal.ofReal (u / 4 + v / 4) ≤ ENNReal.ofReal ((1 / 4) * (|u| + |v|)) := by
          apply ENNReal.ofReal_le_ofReal
          have := le_abs_self u; have := le_abs_self v; linarith
      _ = ENNReal.ofReal (1 / 4) * (ENNReal.ofReal |u| + ENNReal.ofReal |v|) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      _ ≤ _ := by
          rw [h4]
          gcongr
  generalize (1 / 4 : ENNReal) * (rgG F n (fun i => (p.1 i).1) (σ * fun i => (p.1 i).2)
          + rgG F n (fun i => (p.2 i).1) (σ * fun i => -(p.2 i).2)) = C at hreal ⊢
  by_cases hC : C = ⊤
  · rw [hC]; exact le_top
  apply ENNReal.ofReal_le_of_le_toReal
  unfold ghostGapSup
  exact ciSup_le fun f => (ENNReal.ofReal_le_iff_le_toReal hC).mp (hreal f)

theorem rg_ofReal_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ)
    (hg : Integrable g μ) : ENNReal.ofReal (∫ a, g a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
  calc ENNReal.ofReal (∫ a, g a ∂μ) ≤ ENNReal.ofReal (∫ a, max (g a) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hg hg.pos_part fun a => le_max_left _ _)
    _ = ∫⁻ a, ENNReal.ofReal (max (g a) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hg.pos_part (ae_of_all _ fun a => le_max_right _ _)
    _ = ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
        congr 1; funext a
        rcases le_total (g a) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h]; simp
        · rw [max_eq_left h]

theorem rg_avg {X : Type*} (F : Set (X → ℤˣ)) (hFne : F.Nonempty) (n : ℕ) (hn : 0 < n)
    (p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ)) :
    (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ, ENNReal.ofReal (ghostGapSup F (rgSw σ p).1 (rgSw σ p).2)
      ≤ (1 / 4) * (empiricalRademacher (realClass F) n (fun i => (p.1 i).1)
          + empiricalRademacher (realClass F) n (fun i => (p.2 i).1)) := by
  calc (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ, ENNReal.ofReal (ghostGapSup F (rgSw σ p).1 (rgSw σ p).2)
      ≤ (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ, (1 / 4) * (rgG F n (fun i => (p.1 i).1)
          (σ * fun i => (p.1 i).2) + rgG F n (fun i => (p.2 i).1) (σ * fun i => -(p.2 i).2)) := by
        gcongr with σ
        exact rg_pointwise F hFne n hn σ p
    _ = (1 / 4) * ((2 ^ n : ENNReal)⁻¹ * ∑ τ, rgG F n (fun i => (p.1 i).1) τ
          + (2 ^ n : ENNReal)⁻¹ * ∑ τ, rgG F n (fun i => (p.2 i).1) τ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        rw [Fintype.sum_equiv (Equiv.mulRight fun i => (p.1 i).2)
          (fun σ => rgG F n (fun i => (p.1 i).1) (σ * fun i => (p.1 i).2))
          (fun τ => rgG F n (fun i => (p.1 i).1) τ) (fun σ => rfl)]
        rw [Fintype.sum_equiv (Equiv.mulRight fun i => -(p.2 i).2)
          (fun σ => rgG F n (fun i => (p.2 i).1) (σ * fun i => -(p.2 i).2))
          (fun τ => rgG F n (fun i => (p.2 i).1) τ) (fun σ => rfl)]
        ring
    _ = _ := rfl

theorem symmetrization_core {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ)) (hFne : F.Nonempty)
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    ENNReal.ofReal (∫ S, gapSup P F S ∂(Measure.pi fun _ : Fin n => P))
      ≤ rademacherComplexity (P.map Prod.fst) n (realClass F) / 2 := by
  set μn := Measure.pi fun _ : Fin n => P with hμn
  set ν := μn.prod μn with hν
  have hgi : Integrable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) => ghostGapSup F p.1 p.2) ν :=
    rg_int_bdd _ _ hghost 1 (fun p => rg_ghost_abs F hFne _ _)
  have step1 : ∀ S, gapSup P F S ≤ ∫ S', ghostGapSup F S S' ∂μn := by
    intro S
    obtain ⟨f0, hf0⟩ := hFne
    haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
    unfold gapSup
    refine ciSup_le fun f => ?_
    have hti : Integrable (fun S' => trainError S' f.1) μn :=
      rg_int_bdd _ _ (rg_train_meas n f.1 (hF f.1 f.2)) 1
        (fun S' => by have := rg_trainError_mem' S' f.1; rw [abs_le]; constructor <;> linarith)
    have : classError P f - trainError S f = ∫ S', (trainError S' f - trainError S f) ∂μn := by
      rw [integral_sub hti (integrable_const _), integral_const, rg_classError_int P f.1 (hF f.1 f.2) n hn]
      simp
      rfl
    rw [this]
    have hsm : Measurable (fun S' => ghostGapSup F S S') := by
      have := hghost.comp (measurable_prodMk_left (m := inferInstance) (x := S))
      exact this
    have hsec : Integrable (fun S' => ghostGapSup F S S') μn :=
      rg_int_bdd μn (fun S' => ghostGapSup F S S') hsm 1
        (fun S' => rg_ghost_abs F ⟨f0, hf0⟩ S S')
    refine integral_mono (hti.sub (integrable_const _)) hsec ?_
    intro S'
    have := le_ciSup (rg_ghost_bdd F S S') f
    exact this
  have step2 : ∫ S, gapSup P F S ∂μn ≤ ∫ p, ghostGapSup F p.1 p.2 ∂ν := by
    rw [hν, integral_prod _ hgi]
    exact integral_mono (rg_int_bdd _ _ hgap 1 (fun S => rg_gapSup_abs' P F hFne S))
      hgi.integral_prod_left step1
  have step3 : ∀ σ : Fin n → ℤˣ, ∫ p, ghostGapSup F p.1 p.2 ∂ν
      = ∫ p, ghostGapSup F (rgSw σ p).1 (rgSw σ p).2 ∂ν := by
    intro σ
    have hmp := rg_sw_mp P σ
    have := integral_map (μ := ν) (φ := rgSw σ) hmp.measurable.aemeasurable
      (f := fun p => ghostGapSup F p.1 p.2) hghost.aestronglyMeasurable
    rw [hmp.map_eq] at this
    exact this
  have hswm : ∀ σ : Fin n → ℤˣ, Measurable (fun p => ghostGapSup F (rgSw σ p).1 (rgSw σ p).2) :=
    fun σ => hghost.comp (rg_sw_mp P σ).measurable
  have hcard : (∑ _σ : Fin n → ℤˣ, (1 : ENNReal)) = 2 ^ n := by
    simp [Finset.card_univ, Fintype.card_fun]
  have hxm : Measurable (fun S : Fin n → X × ℤˣ => fun i => (S i).1) :=
    measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
  haveI : IsProbabilityMeasure (P.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hR : ∫⁻ S, empiricalRademacher (realClass F) n (fun i => (S i).1) ∂μn
      = rademacherComplexity (P.map Prod.fst) n (realClass F) := by
    unfold rademacherComplexity
    rw [← lintegral_map hrad hxm, hμn]
    congr 1
    exact Measure.pi_map_pi (f := fun _ => Prod.fst) (fun _ => measurable_fst.aemeasurable)
  have hm : Measurable (fun S : Fin n → X × ℤˣ =>
      empiricalRademacher (realClass F) n (fun i => (S i).1)) := hrad.comp hxm
  have hR1 : ∫⁻ p, empiricalRademacher (realClass F) n (fun i => (p.1 i).1) ∂ν
      = rademacherComplexity (P.map Prod.fst) n (realClass F) := by
    rw [← hR]
    calc ∫⁻ p, empiricalRademacher (realClass F) n (fun i => (p.1 i).1) ∂ν
        = ∫⁻ S, empiricalRademacher (realClass F) n (fun i => (S i).1) ∂(ν.map Prod.fst) :=
          (lintegral_map hm measurable_fst).symm
      _ = _ := by rw [hν, Measure.map_fst_prod]; simp
  have hR2 : ∫⁻ p, empiricalRademacher (realClass F) n (fun i => (p.2 i).1) ∂ν
      = rademacherComplexity (P.map Prod.fst) n (realClass F) := by
    rw [← hR]
    calc ∫⁻ p, empiricalRademacher (realClass F) n (fun i => (p.2 i).1) ∂ν
        = ∫⁻ S, empiricalRademacher (realClass F) n (fun i => (S i).1) ∂(ν.map Prod.snd) :=
          (lintegral_map hm measurable_snd).symm
      _ = _ := by rw [hν, Measure.map_snd_prod]; simp
  have hswm' : ∀ σ : Fin n → ℤˣ, Measurable (fun p =>
      ENNReal.ofReal (ghostGapSup F (rgSw σ p).1 (rgSw σ p).2)) :=
    fun σ => ENNReal.measurable_ofReal.comp (hswm σ)
  have hm1 : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      empiricalRademacher (realClass F) n (fun i => (p.1 i).1)) := hm.comp measurable_fst
  have hm2 : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      empiricalRademacher (realClass F) n (fun i => (p.2 i).1)) := hm.comp measurable_snd
  set R := rademacherComplexity (P.map Prod.fst) n (realClass F)
  have h2n : (2 ^ n : ENNReal) ≠ 0 := by positivity
  have h2n' : (2 ^ n : ENNReal) ≠ ⊤ := by simp
  calc ENNReal.ofReal (∫ S, gapSup P F S ∂μn)
      ≤ ENNReal.ofReal (∫ p, ghostGapSup F p.1 p.2 ∂ν) := ENNReal.ofReal_le_ofReal step2
    _ = (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ,
          ENNReal.ofReal (∫ p, ghostGapSup F (rgSw σ p).1 (rgSw σ p).2 ∂ν) := by
        simp_rw [← step3]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        have : (Fintype.card (Fin n → ℤˣ) : ENNReal) = 2 ^ n := by
          rw [← hcard]; simp
        rw [this, ← mul_assoc, ENNReal.inv_mul_cancel h2n h2n', one_mul]
    _ ≤ (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ,
          ∫⁻ p, ENNReal.ofReal (ghostGapSup F (rgSw σ p).1 (rgSw σ p).2) ∂ν := by
        gcongr with σ
        exact rg_ofReal_int_le ν _ (rg_int_bdd _ _ (hswm σ) 1 (fun p => rg_ghost_abs F hFne _ _))
    _ = ∫⁻ p, (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ,
          ENNReal.ofReal (ghostGapSup F (rgSw σ p).1 (rgSw σ p).2) ∂ν := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun σ _ => hswm' σ),
          lintegral_finset_sum _ fun σ _ => hswm' σ]
    _ ≤ ∫⁻ p, (1 / 4) * (empiricalRademacher (realClass F) n (fun i => (p.1 i).1)
          + empiricalRademacher (realClass F) n (fun i => (p.2 i).1)) ∂ν :=
        lintegral_mono fun p => rg_avg F hFne n hn p
    _ = (1 / 4) * (R + R) := by
        have hm12 : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
            empiricalRademacher (realClass F) n (fun i => (p.1 i).1)
              + empiricalRademacher (realClass F) n (fun i => (p.2 i).1)) := hm1.add hm2
        rw [lintegral_const_mul _ hm12, lintegral_add_left hm1, hR1, hR2]
    _ = R / 2 := by
        have h4 : (1 / 4 : ENNReal) * 2 = 2⁻¹ := by
          rw [one_div, show (4 : ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
            mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
        rw [← two_mul, ← mul_assoc, h4, ENNReal.div_eq_inv_mul]


theorem theorem_5b_core {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ))
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (classError P f) ≤ ENNReal.ofReal (trainError S f)
            + rademacherComplexity (P.map Prod.fst) n (realClass F) / 2
            + ENNReal.ofReal (Real.sqrt (Real.log (1 / δ) / (2 * n))))}
      ≤ ENNReal.ofReal δ := by
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · subst hFe; simp
  have hsym := symmetrization_core P F hFne hF n hn hgap hghost hrad
  have hmc := mcdiarmid_step_core P F hFne n hn δ hδ0 hδ1 hgap
  refine le_trans (measure_mono ?_) hmc
  rintro S ⟨f, hf, hne⟩
  refine ⟨f, hf, fun hle => hne ?_⟩
  calc ENNReal.ofReal (classError P f)
      ≤ ENNReal.ofReal (trainError S f + (∫ S', gapSup P F S' ∂(Measure.pi fun _ : Fin n => P))
          + Real.sqrt (Real.log (1 / δ) / (2 * n))) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (trainError S f) + ENNReal.ofReal (∫ S', gapSup P F S' ∂(Measure.pi fun _ : Fin n => P))
          + ENNReal.ofReal (Real.sqrt (Real.log (1 / δ) / (2 * n))) := by
        refine (ENNReal.ofReal_add_le).trans ?_
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ _ := by gcongr

end RadGauss.Classification

open RadGauss.Classification


theorem solution {X : Type*} [MeasurableSpace X]
    (P : Measure (X × ℤˣ)) [IsProbabilityMeasure P] (F : Set (X → ℤˣ))
    (hF : ∀ f ∈ F, Measurable f) (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hgap : Measurable (fun S : Fin n → X × ℤˣ => gapSup P F S))
    (hghost : Measurable (fun p : (Fin n → X × ℤˣ) × (Fin n → X × ℤˣ) =>
      ghostGapSup F p.1 p.2))
    (hrad : Measurable (fun x : Fin n → X => empiricalRademacher (realClass F) n x)) :
    (Measure.pi fun _ : Fin n => P)
        {S | ∃ f ∈ F, ¬ (ENNReal.ofReal (classError P f) ≤ ENNReal.ofReal (trainError S f)
            + rademacherComplexity (P.map Prod.fst) n (realClass F) / 2
            + ENNReal.ofReal (Real.sqrt (Real.log (1 / δ) / (2 * n))))}
      ≤ ENNReal.ofReal δ := by
  exact theorem_5b_core P F hF n hn δ hδ0 hδ1 hgap hghost hrad
