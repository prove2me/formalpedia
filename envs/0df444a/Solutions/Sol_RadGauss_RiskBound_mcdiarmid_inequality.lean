-- Prove2me | solution 1 for RadGauss.RiskBound.mcdiarmid_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:14:10.36709+00:00
-- url     : https://prove2.me/submissions/42a10b1f-a00d-4ce1-8e7e-1cc5b2b31588

import Mathlib

open MeasureTheory


namespace RadGauss.RiskBound

theorem rk_mcd_mgf {Ω : Type*} [MeasurableSpace Ω] (B t : ℝ) : ∀ (m : ℕ)
    (μ : Fin m → Measure Ω), (∀ i, IsProbabilityMeasure (μ i)) → ∀ (c : Fin m → ℝ)
    (f : (Fin m → Ω) → ℝ), Measurable f → (∀ x, |f x| ≤ B) →
    (∀ x i z, |f x - f (Function.update x i z)| ≤ c i) →
    ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ)
      ≤ Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro m
  induction m with
  | zero =>
    intro μ hμ c f hf hB hbd
    have hcst : ∀ x, f x = f (fun i => i.elim0) := fun x => congrArg f (Subsingleton.elim _ _)
    simp [hcst]
  | succ m ih =>
    intro μ hμ c f hf hB hbd
    set πm : Measure (Fin m → Ω) := Measure.pi fun j => μ j.succ with hπm
    haveI : IsProbabilityMeasure πm := by rw [hπm]; infer_instance
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => Ω) 0 with he
    have hmp : MeasurePreserving e (Measure.pi μ) ((μ 0).prod πm) := by
      have := measurePreserving_piFinSuccAbove μ 0
      have h2 : (fun j : Fin m => μ (Fin.succAbove 0 j)) = fun j => μ j.succ := by
        funext j; simp
      rw [h2] at this
      exact this
    have hes : ∀ p : Ω × (Fin m → Ω), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    have hint : ∀ φ : (Fin (m+1) → Ω) → ℝ, ∫ x, φ x ∂(Measure.pi μ)
        = ∫ p, φ (Fin.cons p.1 p.2) ∂((μ 0).prod πm) := by
      intro φ
      rw [← hmp.symm.integral_comp' (g := φ)]
      simp only [hes]
    obtain ⟨a0⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ 0)
    have hc : 0 ≤ c 0 := (abs_nonneg _).trans (hbd (fun _ => a0) 0 a0)
    have hgm : Measurable (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) := by
      have : (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) = f ∘ e.symm := by
        funext p; simp [hes]
      rw [this]; exact hf.comp e.symm.measurable
    have hgint : Integrable (fun p : Ω × (Fin m → Ω) => f (Fin.cons p.1 p.2)) ((μ 0).prod πm) :=
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
    have hhd : ∀ a a', h a - h a' ≤ c 0 := by
      intro a a'
      simp only [hh]
      rw [← integral_sub (hslice a) (hslice a')]
      have : ∫ y, (f (Fin.cons a y) - f (Fin.cons a' y)) ∂πm ≤ ∫ _y, c 0 ∂πm := by
        refine integral_mono (by exact (hslice a).sub (hslice a')) (integrable_const (c 0)) ?_
        intro y
        have := hbd (Fin.cons a y) 0 a'
        rw [Fin.update_cons_zero] at this
        exact (le_abs_self _).trans this
      simpa using this
    set E := ∫ y, f y ∂(Measure.pi μ) with hE
    have hE' : E = ∫ a, h a ∂(μ 0) := by
      rw [hE, hint f]
      exact integral_prod _ hgint
    have hK : ∀ a, ∫ y, Real.exp (t * (f (Fin.cons a y) - h a)) ∂πm
        ≤ Real.exp (t ^ 2 * (∑ j : Fin m, c j.succ ^ 2) / 8) := by
      intro a
      refine ih (fun j => μ j.succ) (fun j => hμ _) (fun j => c j.succ)
        (fun y => f (Fin.cons a y)) (hgm.comp (measurable_const.prodMk measurable_id))
        (fun y => hB _) ?_
      intro x i z
      rw [Fin.cons_update]
      exact hbd _ _ _
    set K := Real.exp (t ^ 2 * (∑ j : Fin m, c j.succ ^ 2) / 8) with hKdef
    set lo := sInf (Set.range h) with hlo
    have hbdd : BddBelow (Set.range h) := ⟨-B, by
      rintro _ ⟨a, rfl⟩; have := hhB a; exact (abs_le.mp this).1⟩
    have hIcc : ∀ a, h a - E ∈ Set.Icc (lo - E) (lo + c 0 - E) := by
      intro a
      constructor
      · have : lo ≤ h a := csInf_le hbdd ⟨a, rfl⟩
        linarith
      · have : h a - c 0 ≤ lo := le_csInf ⟨h a0, a0, rfl⟩ (by
          rintro _ ⟨a', rfl⟩; have := hhd a a'; linarith)
        linarith
    have hX0 : ∫ a, (h a - E) ∂(μ 0) = 0 := by
      rw [integral_sub, hE']
      · simp
      · exact Integrable.mono' (integrable_const B) hhm.aestronglyMeasurable
          (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hhB a)
      · exact integrable_const _
    have hsg := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hhm.sub measurable_const).aemeasurable (ae_of_all _ hIcc) hX0
    have hmgf := hsg.mgf_le t
    have hcc : (((‖lo + c 0 - E - (lo - E)‖₊ / 2) ^ 2 : NNReal) : ℝ) = c 0 ^ 2 / 4 := by
      have : lo + c 0 - E - (lo - E) = c 0 := by ring
      rw [this]
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg hc]; ring
    rw [hcc] at hmgf
    unfold ProbabilityTheory.mgf at hmgf
    rw [hint]
    have hexpint : Integrable (fun p : Ω × (Fin m → Ω) =>
        Real.exp (t * (f (Fin.cons p.1 p.2) - E))) ((μ 0).prod πm) := by
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
    have hhint : Integrable (fun a => Real.exp (t * (h a - E))) (μ 0) := by
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
    calc ∫ a, ∫ y, Real.exp (t * (f (Fin.cons (a, y).1 (a, y).2) - E)) ∂πm ∂(μ 0)
        ≤ ∫ a, Real.exp (t * (h a - E)) * K ∂(μ 0) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun y =>
            (Real.exp_pos _).le) (hhint.mul_const K) (ae_of_all _ fun a => ?_)
          have heq : ∀ y, Real.exp (t * (f (Fin.cons (a, y).1 (a, y).2) - E))
              = Real.exp (t * (h a - E)) * Real.exp (t * (f (Fin.cons a y) - h a)) := by
            intro y; rw [← Real.exp_add]; ring_nf
          simp only [heq]
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hK a) (Real.exp_pos _).le
      _ = (∫ a, Real.exp (t * (h a - E)) ∂(μ 0)) * K := integral_mul_const _ _
      _ ≤ Real.exp (c 0 ^ 2 / 4 * t ^ 2 / 2) * K :=
          mul_le_mul_of_nonneg_right hmgf (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [hKdef, ← Real.exp_add, Fin.sum_univ_succ]; ring_nf

theorem rk_bdd_diff {Ω : Type*} {m : ℕ} (c : Fin m → ℝ) (f : (Fin m → Ω) → ℝ)
    (hbd : ∀ x i z, |f x - f (Function.update x i z)| ≤ c i) (x y : Fin m → Ω) :
    |f x - f y| ≤ ∑ i, c i := by
  classical
  have key : ∀ s : Finset (Fin m), |f x - f (s.piecewise y x)| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert hi]
      have := hbd (s.piecewise y x) i (y i)
      calc |f x - f (Function.update (s.piecewise y x) i (y i))|
          ≤ |f x - f (s.piecewise y x)| + |f (s.piecewise y x) - f (Function.update (s.piecewise y x) i (y i))| :=
            abs_sub_le _ _ _
        _ ≤ _ := by linarith
  simpa using key Finset.univ

theorem mcdiarmid_core {A : Type*} [MeasurableSpace A] (n : ℕ)
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (c : Fin n → ℝ)
    (hc : ∀ (i : Fin n) (x : Fin n → A) (a : A), |f x - f (Function.update x i a)| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ f x - ∫ y, f y ∂(Measure.pi μ)} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2)) := by
  set πn := Measure.pi μ with hπn
  set S := ∑ i, c i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [div_zero, Real.exp_zero, ENNReal.ofReal_one]; exact prob_le_one
  obtain ⟨x0⟩ : Nonempty (Fin n → A) := ⟨fun i => (nonempty_of_isProbabilityMeasure (μ i)).some⟩
  set B := |f x0| + ∑ i, c i with hB
  have hBd : ∀ x, |f x| ≤ B := by
    intro x
    have := rk_bdd_diff c f (fun x i z => hc i x z) x x0
    have := abs_sub_abs_le_abs_sub (f x) (f x0)
    linarith
  set E := ∫ y, f y ∂πn with hE
  set s : ℝ := 4 * t / S with hs
  have hs0 : 0 ≤ s := by positivity
  have hmgf := rk_mcd_mgf B s n μ (fun i => inferInstance) c f hf hBd (fun x i z => hc i x z)
  have hint : Integrable (fun x => Real.exp (s * (f x - E))) πn := by
    refine Integrable.mono' (integrable_const (Real.exp (|s| * (B + |E|)))) ?_ ?_
    · exact (Real.measurable_exp.comp ((hf.sub measurable_const).const_mul s)).aestronglyMeasurable
    · refine ae_of_all _ fun x => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have h1 := hBd x
      calc s * (f x - E) ≤ |s * (f x - E)| := le_abs_self _
        _ = |s| * |f x - E| := abs_mul _ _
        _ ≤ |s| * (B + |E|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (abs_sub _ _).trans (by linarith)
  have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := πn)
    (X := fun x => f x - E) t hs0 hint
  unfold ProbabilityTheory.mgf at hch
  have hfin : Real.exp (-s * t) * Real.exp (s ^ 2 * S / 8) = Real.exp (-2 * t ^ 2 / S) := by
    rw [← Real.exp_add]; congr 1
    rw [hs]; field_simp; ring
  have hreal : πn.real {x | t ≤ f x - E} ≤ Real.exp (-2 * t ^ 2 / S) := by
    refine hch.trans ?_
    rw [← hfin]
    exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hreal

end RadGauss.RiskBound

open RadGauss.RiskBound


theorem solution {A : Type*} [MeasurableSpace A] (n : ℕ)
    (μ : Fin n → Measure A) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → A) → ℝ) (hf : Measurable f) (c : Fin n → ℝ)
    (hc : ∀ (i : Fin n) (x : Fin n → A) (a : A), |f x - f (Function.update x i a)| ≤ c i)
    (t : ℝ) (ht : 0 < t) :
    Measure.pi μ {x | t ≤ f x - ∫ y, f y ∂(Measure.pi μ)} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2)) := by
  exact mcdiarmid_core n μ f hf c hc t ht
