-- Prove2me | solution 2 for PrescAnalytics.ERM.theorem_13_out_of_sample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:36:57.75899+00:00
-- url     : https://prove2.me/submissions/2b5396d7-19b6-4bb8-8005-2aef6080fbc9

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic
import Theorems.Thm_EReal_coe_finset_sum
import Theorems.Thm_EReal_coe_finset_sum

-- carved verbatim out of submission b1eaa945-432c-4d9c-80c5-4ea8b186661b, lines 1741-1757

section
open PrescAnalytics
open PrescAnalytics.ERM
open MeasureTheory Filter Topology

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

end

section
open PrescAnalytics
open PrescAnalytics.ERM
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {U : Type*} [MeasurableSpace U]

noncomputable def Phi {N : ℕ} (P : Measure U) (G : Set (U → ℝ)) (s : Fin N → U) : ℝ :=
  ⨆ g : G, ((∫ u, (g : U → ℝ) u ∂P) - empMean s (g : U → ℝ))

noncomputable def Tt {N : ℕ} (G : Set (U → ℝ)) (s : Fin N → U) (σ : Fin N → Bool) : ℝ :=
  (2 / (N : ℝ)) * ⨆ g : G, ∑ i, signOf (σ i) * (g : U → ℝ) (s i)

noncomputable def Rh {N : ℕ} (G : Set (U → ℝ)) (s : Fin N → U) : ℝ :=
  ((2 : ℝ) ^ N)⁻¹ * ∑ σ : Fin N → Bool, Tt G s σ

noncomputable def DD {N : ℕ} (G : Set (U → ℝ)) (s s' : Fin N → U) : ℝ :=
  ⨆ g : G, (empMean s' (g : U → ℝ) - empMean s (g : U → ℝ))

theorem signOf_abs (b : Bool) : |signOf b| = 1 := by
  unfold signOf; split_ifs <;> simp

theorem signOf_not (b : Bool) : signOf (!b) = - signOf b := by
  cases b <;> simp [signOf]

theorem emp_bd {N : ℕ} (s : Fin N → U) (g : U → ℝ) (gbar : ℝ) (hgb : 0 ≤ gbar)
    (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) : 0 ≤ empMean s g ∧ empMean s g ≤ gbar := by
  unfold empMean
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [hgb]
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hb _).1)
  · have : ∑ i, g (s i) ≤ N * gbar := by
      calc ∑ i, g (s i) ≤ ∑ _i : Fin N, gbar := Finset.sum_le_sum fun i _ => (hb _).2
        _ = N * gbar := by simp
    calc 1 / (N:ℝ) * ∑ i, g (s i) ≤ 1 / N * (N * gbar) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = gbar := by field_simp

theorem int_bd (P : Measure U) [IsProbabilityMeasure P] (g : U → ℝ) (gbar : ℝ)
    (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) : 0 ≤ ∫ u, g u ∂P ∧ ∫ u, g u ∂P ≤ gbar := by
  refine ⟨integral_nonneg fun u => (hb u).1, ?_⟩
  have : ‖∫ u, g u ∂P‖ ≤ gbar := by
    refine (norm_integral_le_of_norm_le_const (C := gbar) ?_).trans (by simp)
    exact ae_of_all _ fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hb u).1]; exact (hb u).2
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)

theorem abs_iSup_le {ι : Type*} [Nonempty ι] (g : ι → ℝ) (C : ℝ) (hb : ∀ i, |g i| ≤ C) :
    |⨆ i, g i| ≤ C := by
  have hbdd : BddAbove (Set.range g) := ⟨C, by rintro _ ⟨i, rfl⟩; exact (abs_le.mp (hb i)).2⟩
  have i0 : ι := Classical.arbitrary ι
  rw [abs_le]; constructor
  · have := le_ciSup hbdd i0; have := (abs_le.mp (hb i0)).1; linarith
  · exact ciSup_le fun i => (abs_le.mp (hb i)).2

theorem Phi_bdd (P : Measure U) [IsProbabilityMeasure P] {N : ℕ} (G : Set (U → ℝ)) (gbar : ℝ)
    (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) :
    BddAbove (Set.range fun g : G => (∫ u, (g : U → ℝ) u ∂P) - empMean s (g : U → ℝ)) := by
  refine ⟨gbar, ?_⟩
  rintro _ ⟨g, rfl⟩
  have h1 := int_bd P g gbar (hb g g.2); have h2 := emp_bd s g gbar hgb (hb g g.2)
  simp only; linarith [h1.1, h1.2, h2.1, h2.2]

theorem emp_update {N : ℕ} (s : Fin N → U) (i : Fin N) (z : U) (g : U → ℝ) (gbar : ℝ)
    (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) :
    |empMean s g - empMean (Function.update s i z) g| ≤ gbar / N := by
  unfold empMean
  have hnr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [Function.update_self]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / N)]
    have : |g (s i) - g z| ≤ gbar := by
      have := hb (s i); have := hb z
      rw [abs_le]; constructor <;> linarith
    calc 1 / (N:ℝ) * |g (s i) - g z| ≤ 1 / N * gbar :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = gbar / N := by ring
  · intro j _ hj; rw [Function.update_of_ne hj]; ring
  · simp

theorem Phi_le_update (P : Measure U) [IsProbabilityMeasure P] {N : ℕ} (G : Set (U → ℝ))
    [Nonempty G] (gbar : ℝ) (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (s : Fin N → U) (i : Fin N) (z : U) :
    Phi P G s ≤ Phi P G (Function.update s i z) + gbar / N := by
  unfold Phi
  refine ciSup_le fun g => ?_
  have h1 := le_ciSup (Phi_bdd P G gbar hgb hb (Function.update s i z)) g
  have h2 := emp_update s i z g gbar (hb g g.2)
  have := (abs_le.mp h2).1
  try simp only at h1 ⊢
  linarith

theorem Phi_diff (P : Measure U) [IsProbabilityMeasure P] {N : ℕ} (G : Set (U → ℝ))
    [Nonempty G] (gbar : ℝ) (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (s : Fin N → U) (i : Fin N) (z : U) :
    |Phi P G s - Phi P G (Function.update s i z)| ≤ gbar / N := by
  rw [abs_le]
  have h1 := Phi_le_update P G gbar hgb hb s i z
  have h2 := Phi_le_update P G gbar hgb hb (Function.update s i z) i (s i)
  rw [Function.update_idem, Function.update_eq_self] at h2
  constructor <;> linarith

theorem Phi_abs (P : Measure U) [IsProbabilityMeasure P] {N : ℕ} (G : Set (U → ℝ))
    [Nonempty G] (gbar : ℝ) (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (s : Fin N → U) : |Phi P G s| ≤ gbar := by
  refine abs_iSup_le _ _ fun g => ?_
  have h1 := int_bd P g gbar (hb g g.2); have h2 := emp_bd s g gbar hgb (hb g g.2)
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem sg_sum_bd {N : ℕ} (s : Fin N → U) (σ : Fin N → Bool) (g : U → ℝ) (gbar : ℝ)
    (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) : |∑ i, signOf (σ i) * g (s i)| ≤ N * gbar := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |signOf (σ i) * g (s i)| ≤ ∑ _i : Fin N, gbar := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, signOf_abs, one_mul, abs_of_nonneg (hb _).1]; exact (hb _).2
    _ = N * gbar := by simp

theorem sg_sum_update {N : ℕ} (s : Fin N → U) (σ : Fin N → Bool) (i : Fin N) (z : U) (g : U → ℝ)
    (gbar : ℝ) (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) :
    |∑ j, signOf (σ j) * g (s j) - ∑ j, signOf (σ j) * g (Function.update s i z j)| ≤ gbar := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [Function.update_self]
    rw [← mul_sub, abs_mul, signOf_abs, one_mul]
    have := hb (s i); have := hb z
    rw [abs_le]; constructor <;> linarith
  · intro j _ hj; rw [Function.update_of_ne hj]; ring
  · simp

theorem Tt_bdd {N : ℕ} (G : Set (U → ℝ)) (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) (σ : Fin N → Bool) :
    BddAbove (Set.range fun g : G => ∑ i, signOf (σ i) * (g : U → ℝ) (s i)) :=
  ⟨N * gbar, by rintro _ ⟨g, rfl⟩; exact (abs_le.mp (sg_sum_bd s σ g gbar (hb g g.2))).2⟩

theorem Tt_abs {N : ℕ} (hN : 0 < N) (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) (σ : Fin N → Bool) :
    |Tt G s σ| ≤ 2 * gbar := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Tt
  have h := abs_iSup_le (fun g : G => ∑ i, signOf (σ i) * (g : U → ℝ) (s i)) (N * gbar)
    (fun g => sg_sum_bd s σ g gbar (hb g g.2))
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / N)]
  calc 2 / (N:ℝ) * |⨆ g : G, ∑ i, signOf (σ i) * (g : U → ℝ) (s i)| ≤ 2 / N * (N * gbar) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * gbar := by field_simp

theorem Tt_le_update {N : ℕ} (hN : 0 < N) (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) (σ : Fin N → Bool) (i : Fin N)
    (z : U) : Tt G s σ ≤ Tt G (Function.update s i z) σ + 2 * gbar / N := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Tt
  have h : (⨆ g : G, ∑ j, signOf (σ j) * (g : U → ℝ) (s j))
      ≤ (⨆ g : G, ∑ j, signOf (σ j) * (g : U → ℝ) (Function.update s i z j)) + gbar := by
    refine ciSup_le fun g => ?_
    have h1 := le_ciSup (Tt_bdd G gbar hb (Function.update s i z) σ) g
    have h2 := sg_sum_update s σ i z g gbar (hb g g.2)
    have := (abs_le.mp h2).2
    try simp only at h1 ⊢
    linarith
  calc 2 / (N:ℝ) * (⨆ g : G, ∑ j, signOf (σ j) * (g : U → ℝ) (s j))
      ≤ 2 / N * ((⨆ g : G, ∑ j, signOf (σ j) * (g : U → ℝ) (Function.update s i z j)) + gbar) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

theorem Rh_le_update {N : ℕ} (hN : 0 < N) (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) (i : Fin N) (z : U) :
    Rh G s ≤ Rh G (Function.update s i z) + 2 * gbar / N := by
  unfold Rh
  have h : ∑ σ : Fin N → Bool, Tt G s σ ≤
      ∑ σ : Fin N → Bool, (Tt G (Function.update s i z) σ + 2 * gbar / N) :=
    Finset.sum_le_sum fun σ _ => Tt_le_update hN G gbar hb s σ i z
  rw [Finset.sum_add_distrib] at h
  have hc : ∑ _σ : Fin N → Bool, (2 * gbar / N : ℝ) = 2 ^ N * (2 * gbar / N) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul]; push_cast; ring
  rw [hc] at h
  have h2 : (0:ℝ) < 2 ^ N := by positivity
  calc ((2:ℝ) ^ N)⁻¹ * ∑ σ : Fin N → Bool, Tt G s σ
      ≤ ((2:ℝ) ^ N)⁻¹ * (∑ σ : Fin N → Bool, Tt G (Function.update s i z) σ + 2 ^ N * (2 * gbar / N)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

theorem Rh_abs {N : ℕ} (hN : 0 < N) (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) : |Rh G s| ≤ 2 * gbar := by
  unfold Rh
  have h2 : (0:ℝ) < 2 ^ N := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.mpr h2)]
  have : |∑ σ : Fin N → Bool, Tt G s σ| ≤ 2 ^ N * (2 * gbar) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ : Fin N → Bool, |Tt G s σ| ≤ ∑ _σ : Fin N → Bool, (2 * gbar) :=
          Finset.sum_le_sum fun σ _ => Tt_abs hN G gbar hb s σ
      _ = 2 ^ N * (2 * gbar) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  calc ((2:ℝ) ^ N)⁻¹ * |∑ σ : Fin N → Bool, Tt G s σ| ≤ ((2:ℝ) ^ N)⁻¹ * (2 ^ N * (2 * gbar)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * gbar := by field_simp

theorem val_abs (g : U → ℝ) (gbar : ℝ) (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (u : U) : |g u| ≤ gbar := by
  rw [abs_of_nonneg (hb u).1]; exact (hb u).2

theorem emp_abs {N : ℕ} (s : Fin N → U) (g : U → ℝ) (gbar : ℝ) (hgb : 0 ≤ gbar)
    (hb : ∀ u, 0 ≤ g u ∧ g u ≤ gbar) : |empMean s g| ≤ gbar := by
  have := emp_bd s g gbar hgb hb
  rw [abs_of_nonneg this.1]; exact this.2

theorem meas_iSup_sep {α : Type*} [MeasurableSpace α] (G : Set (U → ℝ)) (hne : G.Nonempty)
    (hsep : IsPointwiseSeparable G) (φ : (U → ℝ) → α → ℝ) (hφm : ∀ g ∈ G, Measurable (φ g))
    (hcont : ∀ g ∈ G, ∀ u : ℕ → U → ℝ, (∀ n, u n ∈ G) →
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) →
      ∀ a, Tendsto (fun n => φ (u n) a) atTop (𝓝 (φ g a)))
    (hbdd : ∀ a, BddAbove (Set.range fun g : G => φ g a)) :
    Measurable (fun a => ⨆ g : G, φ g a) := by
  obtain ⟨F0, hF0G, hF0c, hF0⟩ := hsep
  haveI : Countable F0 := hF0c.to_subtype
  have heq : ∀ a, (⨆ g : G, φ g a) = ⨆ g : F0, φ g a := by
    intro a
    have hbdd0 : BddAbove (Set.range fun g : F0 => φ g a) := by
      obtain ⟨B, hB⟩ := hbdd a
      exact ⟨B, by rintro _ ⟨g, rfl⟩; exact hB ⟨⟨g, hF0G g.2⟩, rfl⟩⟩
    obtain ⟨g1, hg1⟩ := hne
    obtain ⟨u1, hu1, _⟩ := hF0 g1 hg1
    haveI : Nonempty G := ⟨⟨g1, hg1⟩⟩
    haveI : Nonempty F0 := ⟨⟨u1 0, hu1 0⟩⟩
    apply le_antisymm
    · refine ciSup_le fun g => ?_
      obtain ⟨u, hu, hlim⟩ := hF0 g g.2
      refine le_of_tendsto (hcont g g.2 u (fun n => hF0G (hu n)) hlim a)
        (Eventually.of_forall fun n => ?_)
      exact le_ciSup hbdd0 ⟨u n, hu n⟩
    · exact ciSup_le fun g => le_ciSup (hbdd a) ⟨g, hF0G g.2⟩
  have : (fun a => ⨆ g : G, φ g a) = fun a => ⨆ g : F0, φ g a := funext heq
  rw [this]
  exact Measurable.iSup fun g => hφm g (hF0G g.2)

theorem int_tendsto (P : Measure U) [IsProbabilityMeasure P] (G : Set (U → ℝ)) (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (hGm : ∀ g ∈ G, Measurable g) (g : U → ℝ)
    (u : ℕ → U → ℝ) (hu : ∀ n, u n ∈ G)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, u n x ∂P) atTop (𝓝 (∫ x, g x ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => gbar)
    (fun n => (hGm _ (hu n)).aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ hlim)
  rw [Real.norm_eq_abs, abs_of_nonneg (hb _ (hu n) x).1]; exact (hb _ (hu n) x).2

theorem emp_tendsto {N : ℕ} (s : Fin N → U) (g : U → ℝ) (u : ℕ → U → ℝ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => empMean s (u n)) atTop (𝓝 (empMean s g)) := by
  unfold empMean
  exact Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => hlim (s i))

theorem Phi_meas (P : Measure U) [IsProbabilityMeasure P] (G : Set (U → ℝ)) (hne : G.Nonempty)
    (gbar : ℝ) (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (hGm : ∀ g ∈ G, Measurable g) (hsep : IsPointwiseSeparable G) (N : ℕ) :
    Measurable (Phi (N := N) P G) := by
  have := meas_iSup_sep (α := Fin N → U) G hne hsep
    (fun g s => (∫ u, g u ∂P) - empMean s g)
    (fun g hg => measurable_const.sub (rk_emp_meas N g (hGm g hg)))
    (fun g hg u hu hlim s => (int_tendsto P G gbar hb hGm g u hu hlim).sub
      (emp_tendsto s g u hlim))
    (fun s => Phi_bdd P G gbar hgb hb s)
  exact this

theorem Tt_meas (G : Set (U → ℝ)) (hne : G.Nonempty) (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (hGm : ∀ g ∈ G, Measurable g) (hsep : IsPointwiseSeparable G) (N : ℕ) (σ : Fin N → Bool) :
    Measurable (fun s : Fin N → U => Tt G s σ) := by
  have := meas_iSup_sep (α := Fin N → U) G hne hsep
    (fun g s => ∑ i, signOf (σ i) * g (s i))
    (fun g hg => Finset.measurable_sum _ fun i _ =>
      (hGm g hg).comp (measurable_pi_apply i) |>.const_mul _)
    (fun g hg u hu hlim s => tendsto_finset_sum _ fun i _ => (hlim (s i)).const_mul _)
    (fun s => Tt_bdd G gbar hb s σ)
  exact this.const_mul _

theorem Rh_meas (G : Set (U → ℝ)) (hne : G.Nonempty) (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (hGm : ∀ g ∈ G, Measurable g) (hsep : IsPointwiseSeparable G) (N : ℕ) :
    Measurable (Rh (N := N) G) := by
  unfold Rh
  exact (Finset.measurable_sum _ fun σ _ => Tt_meas G hne gbar hb hGm hsep N σ).const_mul _

theorem DD_meas (G : Set (U → ℝ)) (hne : G.Nonempty) (gbar : ℝ) (hgb : 0 ≤ gbar)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (hGm : ∀ g ∈ G, Measurable g) (hsep : IsPointwiseSeparable G) (N : ℕ) :
    Measurable (fun p : (Fin N → U) × (Fin N → U) => DD G p.1 p.2) := by
  have := meas_iSup_sep (α := (Fin N → U) × (Fin N → U)) G hne hsep
    (fun g p => empMean p.2 g - empMean p.1 g)
    (fun g hg => ((rk_emp_meas N g (hGm g hg)).comp measurable_snd).sub
      ((rk_emp_meas N g (hGm g hg)).comp measurable_fst))
    (fun g hg u hu hlim p => (emp_tendsto p.2 g u hlim).sub (emp_tendsto p.1 g u hlim))
    (fun p => ⟨gbar, by
      rintro _ ⟨k, rfl⟩
      have h1 := emp_bd p.2 k gbar hgb (hb k k.2); have h2 := emp_bd p.1 k gbar hgb (hb k k.2)
      simp only; linarith [h1.1, h1.2, h2.1, h2.2]⟩)
  exact this

theorem sw_term {N : ℕ} (σ : Fin N → Bool) (p : (Fin N → U) × (Fin N → U)) (h : U → ℝ) :
    empMean (rkSw σ p).2 h - empMean (rkSw σ p).1 h
      = 2⁻¹ * ((2 / (N : ℝ)) * ∑ i, signOf (σ i) * h (p.2 i))
        - 2⁻¹ * ((2 / (N : ℝ)) * ∑ i, signOf (σ i) * h (p.1 i)) := by
  unfold empMean
  have : ∀ i, h ((rkSw σ p).2 i) - h ((rkSw σ p).1 i)
      = signOf (σ i) * h (p.2 i) - signOf (σ i) * h (p.1 i) := by
    intro i; by_cases hσ : σ i = true <;> simp [rkSw, signOf, hσ] <;> ring
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp only [this, Finset.sum_sub_distrib]
  ring

theorem DD_sw_le {N : ℕ} (hN : 0 < N) (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (σ : Fin N → Bool)
    (p : (Fin N → U) × (Fin N → U)) :
    DD G (rkSw σ p).1 (rkSw σ p).2 ≤ 2⁻¹ * Tt G p.2 σ + 2⁻¹ * Tt G p.1 (fun i => !(σ i)) := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold DD
  refine ciSup_le fun g => ?_
  rw [sw_term]
  have ha : (2 / (N : ℝ)) * ∑ i, signOf (σ i) * (g : U → ℝ) (p.2 i) ≤ Tt G p.2 σ := by
    unfold Tt
    exact mul_le_mul_of_nonneg_left (le_ciSup (Tt_bdd G gbar hb p.2 σ) g) (by positivity)
  have hb' : -((2 / (N : ℝ)) * ∑ i, signOf (σ i) * (g : U → ℝ) (p.1 i))
      ≤ Tt G p.1 (fun i => !(σ i)) := by
    have : -((2 / (N : ℝ)) * ∑ i, signOf (σ i) * (g : U → ℝ) (p.1 i))
        = (2 / (N : ℝ)) * ∑ i, signOf (!(σ i)) * (g : U → ℝ) (p.1 i) := by
      simp only [signOf_not, neg_mul, Finset.sum_neg_distrib]; ring
    rw [this]; unfold Tt
    exact mul_le_mul_of_nonneg_left (le_ciSup (Tt_bdd G gbar hb p.1 (fun i => !(σ i))) g)
      (by positivity)
  linarith

theorem sum_Tt_not {N : ℕ} (G : Set (U → ℝ)) (s : Fin N → U) :
    ∑ σ : Fin N → Bool, Tt G s (fun i => !(σ i)) = ∑ σ : Fin N → Bool, Tt G s σ :=
  Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.boolNot) _ _ (fun σ => rfl)

theorem int_snd (π : Measure U) [IsProbabilityMeasure π] (f : U → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ u, |f u| ≤ C) : ∫ p : U × U, f p.2 ∂(π.prod π) = ∫ v, f v ∂π := by
  have hint : Integrable (fun p : U × U => f p.2) (π.prod π) :=
    rk_bdd_integrable _ _ (hf.comp measurable_snd) C (fun p => hb _)
  rw [integral_prod _ hint]
  simp

theorem int_fst (π : Measure U) [IsProbabilityMeasure π] (f : U → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ u, |f u| ≤ C) : ∫ p : U × U, f p.1 ∂(π.prod π) = ∫ v, f v ∂π := by
  have hint : Integrable (fun p : U × U => f p.1) (π.prod π) :=
    rk_bdd_integrable _ _ (hf.comp measurable_fst) C (fun p => hb _)
  rw [integral_prod _ hint]
  simp

theorem sym_real (P : Measure U) [IsProbabilityMeasure P] (G : Set (U → ℝ)) [Nonempty G]
    (gbar : ℝ) (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (hGm : ∀ g ∈ G, Measurable g) (N : ℕ) (hN : 0 < N)
    (hPhi : Measurable (Phi (N := N) P G)) (hRh : Measurable (Rh (N := N) G))
    (hDD : Measurable (fun p : (Fin N → U) × (Fin N → U) => DD G p.1 p.2)) :
    ∫ S, Phi P G S ∂(Measure.pi fun _ : Fin N => P)
      ≤ ∫ S, Rh G S ∂(Measure.pi fun _ : Fin N => P) := by
  set π := Measure.pi fun _ : Fin N => P with hπ
  set ρ := π.prod π with hρ
  set D := fun p : (Fin N → U) × (Fin N → U) => DD G p.1 p.2 with hDdef
  have hdterm : ∀ (h : G) (S S' : Fin N → U),
      |empMean S' (h : U → ℝ) - empMean S (h : U → ℝ)| ≤ gbar := by
    intro h S S'
    have h1 := emp_bd S' h gbar hgb (hb h h.2); have h2 := emp_bd S h gbar hgb (hb h h.2)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hDb : ∀ p, |D p| ≤ gbar := fun p => abs_iSup_le _ _ fun h => hdterm h _ _
  have hSb : ∀ S : Fin N → U, |Phi P G S| ≤ gbar := fun S => Phi_abs P G gbar hgb hb S
  have hRb : ∀ S : Fin N → U, |Rh G S| ≤ 2 * gbar := fun S => Rh_abs hN G gbar hb S
  have hDint : Integrable D ρ := rk_bdd_integrable ρ D hDD gbar hDb
  have hsec : ∀ S, Integrable (fun S' => D (S, S')) π := fun S =>
    rk_bdd_integrable π _ (hDD.comp (measurable_const.prodMk measurable_id)) gbar
      (fun S' => hDb _)
  have step1 : ∫ S, Phi P G S ∂π ≤ ∫ p, D p ∂ρ := by
    rw [integral_prod D hDint]
    refine integral_mono (rk_bdd_integrable π _ hPhi gbar hSb) hDint.integral_prod_left ?_
    intro S
    unfold Phi
    refine ciSup_le fun h => ?_
    have hhm := hGm h h.2
    have hint := rk_bdd_integrable π _ (rk_emp_meas N _ hhm) gbar
      (fun S' => emp_abs S' h gbar hgb (hb h h.2))
    have hE : (∫ w, (h : U → ℝ) w ∂P) - empMean S (h : U → ℝ)
        = ∫ S', (empMean S' (h : U → ℝ) - empMean S (h : U → ℝ)) ∂π := by
      rw [integral_sub hint (integrable_const _),
        rk_int_emp P N hN _ hhm gbar (val_abs _ gbar (hb h h.2))]
      simp
    rw [hE]
    refine integral_mono (hint.sub (integrable_const _)) (hsec S) ?_
    intro S'
    have hbdd : BddAbove (Set.range fun h : G =>
        empMean S' (h : U → ℝ) - empMean S (h : U → ℝ)) :=
      ⟨gbar, by rintro _ ⟨k, rfl⟩; exact (abs_le.mp (hdterm k S S')).2⟩
    exact le_ciSup hbdd h
  have hswm : ∀ σ : Fin N → Bool, Measurable (fun p => D (rkSw σ p)) := fun σ =>
    hDD.comp (rk_sw_mp P σ).measurable
  have hsw : ∀ σ : Fin N → Bool, ∫ p, D (rkSw σ p) ∂ρ = ∫ p, D p ∂ρ := by
    intro σ
    have hmp := rk_sw_mp P (n := N) σ
    have h1 := integral_map (μ := ρ) (φ := rkSw σ) hmp.measurable.aemeasurable (f := D)
      (by rw [hmp.map_eq]; exact hDD.aestronglyMeasurable)
    rw [hmp.map_eq] at h1
    exact h1.symm
  set W := fun p => ((2:ℝ) ^ N)⁻¹ * ∑ σ : Fin N → Bool, D (rkSw σ p) with hW
  have hWint : Integrable W ρ := by
    refine Integrable.const_mul ?_ _
    exact integrable_finset_sum _ fun σ _ => rk_bdd_integrable ρ _ (hswm σ) gbar (fun p => hDb _)
  have step2 : ∫ p, D p ∂ρ = ∫ p, W p ∂ρ := by
    rw [hW, integral_const_mul, integral_finset_sum]
    · simp only [hsw, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
    · intro σ _; exact rk_bdd_integrable ρ _ (hswm σ) gbar (fun p => hDb _)
  have step4 : ∀ p, W p ≤ 2⁻¹ * Rh G p.2 + 2⁻¹ * Rh G p.1 := by
    intro p
    rw [hW]; dsimp only
    calc ((2:ℝ) ^ N)⁻¹ * ∑ σ : Fin N → Bool, D (rkSw σ p)
        ≤ ((2:ℝ) ^ N)⁻¹ * ∑ σ : Fin N → Bool,
            (2⁻¹ * Tt G p.2 σ + 2⁻¹ * Tt G p.1 (fun i => !(σ i))) := by
          gcongr with σ _; exact DD_sw_le hN G gbar hb σ p
      _ = 2⁻¹ * Rh G p.2 + 2⁻¹ * Rh G p.1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_Tt_not]
          unfold Rh; ring
  have hI2 : Integrable (fun p : (Fin N → U) × (Fin N → U) => Rh G p.2) ρ :=
    rk_bdd_integrable _ _ (hRh.comp measurable_snd) _ (fun p => hRb _)
  have hI1 : Integrable (fun p : (Fin N → U) × (Fin N → U) => Rh G p.1) ρ :=
    rk_bdd_integrable _ _ (hRh.comp measurable_fst) _ (fun p => hRb _)
  have step5 : ∫ p, (2⁻¹ * Rh G p.2 + 2⁻¹ * Rh G p.1) ∂ρ = ∫ S, Rh G S ∂π := by
    rw [integral_add (hI2.const_mul _) (hI1.const_mul _), integral_const_mul, integral_const_mul,
      hρ, int_snd π _ hRh _ hRb, int_fst π _ hRh _ hRb]
    ring
  calc ∫ S, Phi P G S ∂π ≤ ∫ p, D p ∂ρ := step1
    _ = ∫ p, W p ∂ρ := step2
    _ ≤ ∫ p, (2⁻¹ * Rh G p.2 + 2⁻¹ * Rh G p.1) ∂ρ :=
        integral_mono hWint ((hI2.const_mul _).add (hI1.const_mul _)) step4
    _ = _ := step5

theorem ereal_iSup_coe {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddAbove (Set.range f)) :
    (⨆ i, (f i : EReal)) = ((⨆ i, f i : ℝ) : EReal) := by
  have := Monotone.map_ciSup_of_continuousAt (f := ((↑) : ℝ → EReal)) (g := f)
    continuous_coe_real_ereal.continuousAt (fun a b h => EReal.coe_le_coe_iff.mpr h) hf
  exact this.symm

theorem signedSup_lift (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) {N : ℕ} (s : Fin N → U)
    (σ : Fin N → Fin 1 → Bool) :
    signedSup (liftClass G) s σ
      = ((⨆ g : G, ∑ i, signOf (σ i 0) * (g : U → ℝ) (s i) : ℝ) : EReal) := by
  unfold signedSup liftClass
  rw [iSup_image]
  have : ∀ g : U → ℝ, (∑ i, ∑ k : Fin 1, signOf (σ i k) * (fun (u : U) (_ : Fin 1) => g u) (s i) k)
      = ∑ i, signOf (σ i 0) * g (s i) := by
    intro g; simp
  simp only [this]
  rw [← iSup_subtype'' G (fun g => ((∑ i, signOf (σ i 0) * g (s i) : ℝ) : EReal))]
  exact ereal_iSup_coe _ (Tt_bdd G gbar hb s (fun i => σ i 0))

theorem empR_eq (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) {N : ℕ} (s : Fin N → U) :
    empRademacherR G s = ((Rh G s : ℝ) : EReal) := by
  unfold empRademacherR empRademacher
  simp only [signedSup_lift G gbar hb s]
  have e1 : ∑ σ : Fin N → Fin 1 → Bool,
      (((⨆ g : G, ∑ i, signOf (σ i 0) * (g : U → ℝ) (s i) : ℝ)) : EReal)
      = ∑ τ : Fin N → Bool, (((⨆ g : G, ∑ i, signOf (τ i) * (g : U → ℝ) (s i) : ℝ)) : EReal) :=
    Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.funUnique (Fin 1) Bool) _ _
      (fun σ => rfl)
  rw [e1, ← EReal.coe_finset_sum, ← EReal.coe_mul]
  congr 1
  unfold Rh Tt
  rw [← Finset.mul_sum]
  simp only [Nat.mul_one]
  ring

theorem ofReal_max0 (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem marg_eq (P : Measure U) [IsProbabilityMeasure P] (G : Set (U → ℝ)) [Nonempty G]
    (gbar : ℝ) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (N : ℕ) :
    margRademacherR P N G
      = ∫⁻ s, ENNReal.ofReal (Rh G s) ∂(Measure.pi fun _ : Fin N => P) := by
  unfold margRademacherR margRademacher
  refine lintegral_congr fun s => ?_
  have := empR_eq G gbar hb s
  unfold empRademacherR at this
  rw [this]; exact EReal.real_coe_toENNReal _

theorem EPhi_le (P : Measure U) [IsProbabilityMeasure P] (G : Set (U → ℝ)) [Nonempty G]
    (gbar : ℝ) (hgb : 0 ≤ gbar) (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (hGm : ∀ g ∈ G, Measurable g) (hsep : IsPointwiseSeparable G) (N : ℕ) (hN : 0 < N) :
    margRademacherR P N G ≠ ⊤ ∧
    ∫ S, Phi P G S ∂(Measure.pi fun _ : Fin N => P)
      ≤ (margRademacherR P N G).toReal := by
  have hne : G.Nonempty := ⟨Classical.arbitrary G, (Classical.arbitrary G).2⟩
  have hRh := Rh_meas G hne gbar hb hGm hsep N
  have hPhi := Phi_meas P G hne gbar hgb hb hGm hsep N
  have hDD := DD_meas G hne gbar hgb hb hGm hsep N
  have hsym := sym_real P G gbar hgb hb hGm N hN hPhi hRh hDD
  set π := Measure.pi fun _ : Fin N => P with hπ
  have hRb : ∀ S : Fin N → U, |Rh G S| ≤ 2 * gbar := fun S => Rh_abs hN G gbar hb S
  rw [marg_eq P G gbar hb N]
  refine ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top (b := ∫⁻ _s, ENNReal.ofReal (2 * gbar) ∂π) ?_ ?_
    · simp [ENNReal.mul_eq_top]
    · refine lintegral_mono fun s => ENNReal.ofReal_le_ofReal ?_
      exact (abs_le.mp (hRb s)).2
  · refine hsym.trans ?_
    have hmax : Integrable (fun s => max (Rh G s) 0) π :=
      rk_bdd_integrable π _ (hRh.max measurable_const) (2 * gbar) (fun s => by
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (abs_le.mp (hRb s)).2 (by linarith))
    have hRint : Integrable (Rh (N := N) G) π := rk_bdd_integrable π _ hRh _ hRb
    calc ∫ S, Rh G S ∂π ≤ ∫ S, max (Rh G S) 0 ∂π :=
          integral_mono hRint hmax fun S => le_max_left _ _
      _ = (∫⁻ S, ENNReal.ofReal (max (Rh G S) 0) ∂π).toReal :=
          integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun S => le_max_right _ _)
            hmax.aestronglyMeasurable
      _ = _ := by simp only [ofReal_max0]; rfl

theorem eq29_core (P : Measure U) [IsProbabilityMeasure P]
    (G : Set (U → ℝ)) (gbar : ℝ) (hG_meas : ∀ g ∈ G, Measurable g)
    (hG_sep : IsPointwiseSeparable G) (hG_bdd : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => P)
      {s | ∃ g ∈ G, margRademacherR P N G <
        ENNReal.ofReal ((∫ u, g u ∂P) - empMean s g
          - gbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ := by
  set π := Measure.pi fun _ : Fin N => P with hπ
  by_cases hδ1 : 1 ≤ δ
  · exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1)
  push_neg at hδ1
  rcases isEmpty_or_nonempty G with hGe | hne
  · have : {s : Fin N → U | ∃ g ∈ G, margRademacherR P N G <
        ENNReal.ofReal ((∫ u, g u ∂P) - empMean s g
          - gbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} = ∅ := by
      ext s; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hg, _⟩; exact hGe.false ⟨g, hg⟩
    rw [this]; simp
  obtain ⟨u0⟩ := nonempty_of_isProbabilityMeasure P
  obtain ⟨g0, hg0⟩ : G.Nonempty := ⟨(Classical.arbitrary G : G).1, (Classical.arbitrary G : G).2⟩
  have hgb : 0 ≤ gbar := le_trans (hG_bdd g0 hg0 u0).1 (hG_bdd g0 hg0 u0).2
  have hN0 : 0 < N := hN
  obtain ⟨hRfin, hE⟩ := EPhi_le P G gbar hgb hG_bdd hG_meas hG_sep N hN0
  have hPhi := Phi_meas P G ⟨g0, hg0⟩ gbar hgb hG_bdd hG_meas hG_sep N
  set ε := Real.sqrt (Real.log (1 / δ) / (2 * N)) with hε
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : ε ^ 2 = Real.log (1 / δ) / (2 * N) := Real.sq_sqrt (by positivity)
  rcases hgb.eq_or_lt with h0 | hpos
  · -- gbar = 0
    have : {s : Fin N → U | ∃ g ∈ G, margRademacherR P N G <
        ENNReal.ofReal ((∫ u, g u ∂P) - empMean s g
          - gbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} = ∅ := by
      ext s; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hg, hlt⟩
      have h1 := int_bd P g gbar (hG_bdd g hg)
      have h2 := emp_bd s g gbar hgb (hG_bdd g hg)
      rw [← h0] at h1 h2
      rw [ENNReal.ofReal_of_nonpos (by rw [← h0]; linarith [h1.1, h1.2, h2.1, h2.2])] at hlt
      exact not_lt_zero' hlt
    rw [this]; simp
  haveI : Nonempty G := ⟨⟨g0, hg0⟩⟩
  have hsub : {s : Fin N → U | ∃ g ∈ G, margRademacherR P N G <
        ENNReal.ofReal ((∫ u, g u ∂P) - empMean s g
          - gbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))}
      ⊆ {s | gbar * ε ≤ Phi P G s - ∫ S, Phi P G S ∂π} := by
    rintro s ⟨g, hg, hlt⟩
    have h1 := (ENNReal.lt_ofReal_iff_toReal_lt hRfin).mp hlt
    have h2 := le_ciSup (Phi_bdd P G gbar hgb hG_bdd s) ⟨g, hg⟩
    simp only [Set.mem_setOf_eq]
    unfold Phi at *
    simp only at h2
    rw [← hε] at h1
    linarith
  refine (measure_mono hsub).trans ?_
  have hm := mcdiarmid_core N (fun _ => P) (Phi P G) hPhi (fun _ => gbar / N)
    (fun i S z => Phi_diff P G gbar hgb hG_bdd S i z) (gbar * ε) (mul_pos hpos hε0)
  refine hm.trans (le_of_eq ?_)
  congr 1
  have hsum : (∑ _i : Fin N, (gbar / (N:ℝ)) ^ 2 : ℝ) = gbar ^ 2 / N := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  rw [hsum]
  have : -2 * (gbar * ε) ^ 2 / (gbar ^ 2 / N) = - Real.log (1 / δ) := by
    rw [mul_pow, hε2]; field_simp
  rw [this, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

theorem Rh_diff {N : ℕ} (hN : 0 < N) (G : Set (U → ℝ)) [Nonempty G] (gbar : ℝ)
    (hb : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar) (s : Fin N → U) (i : Fin N) (z : U) :
    |(-Rh G s) - (-Rh G (Function.update s i z))| ≤ 2 * gbar / N := by
  rw [abs_le]
  have h1 := Rh_le_update hN G gbar hb s i z
  have h2 := Rh_le_update hN G gbar hb (Function.update s i z) i (s i)
  rw [Function.update_idem, Function.update_eq_self] at h2
  constructor <;> linarith

theorem eq30_core (P : Measure U) [IsProbabilityMeasure P]
    (G : Set (U → ℝ)) (gbar : ℝ) (hG_meas : ∀ g ∈ G, Measurable g)
    (hG_sep : IsPointwiseSeparable G) (hG_bdd : ∀ g ∈ G, ∀ u, 0 ≤ g u ∧ g u ≤ gbar)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => P)
      {s | ∃ g ∈ G, empRademacherR G s <
        (((∫ u, g u ∂P) - empMean s g
          - 3 * gbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by
  set π := Measure.pi fun _ : Fin N => P with hπ
  by_cases hδ1 : 2 ≤ δ
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  push_neg at hδ1
  rcases isEmpty_or_nonempty G with hGe | hne
  · have : {s : Fin N → U | ∃ g ∈ G, empRademacherR G s <
        (((∫ u, g u ∂P) - empMean s g
          - 3 * gbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} = ∅ := by
      ext s; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hg, _⟩; exact hGe.false ⟨g, hg⟩
    rw [this]; simp
  obtain ⟨u0⟩ := nonempty_of_isProbabilityMeasure P
  obtain ⟨g0, hg0⟩ : G.Nonempty := ⟨(Classical.arbitrary G : G).1, (Classical.arbitrary G : G).2⟩
  have hgb : 0 ≤ gbar := le_trans (hG_bdd g0 hg0 u0).1 (hG_bdd g0 hg0 u0).2
  have hN0 : 0 < N := hN
  haveI : Nonempty G := ⟨⟨g0, hg0⟩⟩
  have hne' : G.Nonempty := ⟨g0, hg0⟩
  have hPhi := Phi_meas P G hne' gbar hgb hG_bdd hG_meas hG_sep N
  have hRh := Rh_meas G hne' gbar hG_bdd hG_meas hG_sep N
  have hDD := DD_meas G hne' gbar hgb hG_bdd hG_meas hG_sep N
  have hsym := sym_real P G gbar hgb hG_bdd hG_meas N hN0 hPhi hRh hDD
  have hRb : ∀ S : Fin N → U, |Rh G S| ≤ 2 * gbar := fun S => Rh_abs hN0 G gbar hG_bdd S
  have hcv : ∀ s : Fin N → U, empRademacherR G s = ((Rh G s : ℝ) : EReal) :=
    fun s => empR_eq G gbar hG_bdd s
  set ε := Real.sqrt (Real.log (2 / δ) / (2 * N)) with hε
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hε0 : 0 < ε := Real.sqrt_pos.mpr (by positivity)
  have hε2 : ε ^ 2 = Real.log (2 / δ) / (2 * N) := Real.sq_sqrt (by positivity)
  rcases hgb.eq_or_lt with h0 | hpos
  · have : {s : Fin N → U | ∃ g ∈ G, empRademacherR G s <
        (((∫ u, g u ∂P) - empMean s g
          - 3 * gbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} = ∅ := by
      ext s; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hg, hlt⟩
      have h1 := int_bd P g gbar (hG_bdd g hg)
      have h2 := emp_bd s g gbar hgb (hG_bdd g hg)
      rw [hcv s, EReal.coe_lt_coe_iff] at hlt
      have := (abs_le.mp (hRb s)).1
      rw [← h0] at h1 h2 this hlt
      linarith [h1.1, h1.2, h2.1, h2.2]
    rw [this]; simp
  -- main case
  set A : Set (Fin N → U) := {s | gbar * ε ≤ Phi P G s - ∫ S, Phi P G S ∂π} with hA
  set B : Set (Fin N → U) := {s | 2 * gbar * ε ≤ (-Rh G s) - ∫ S, (-Rh G S) ∂π} with hB
  have hsub : {s : Fin N → U | ∃ g ∈ G, empRademacherR G s <
        (((∫ u, g u ∂P) - empMean s g
          - 3 * gbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ⊆ A ∪ B := by
    rintro s ⟨g, hg, hlt⟩
    rw [hcv s, EReal.coe_lt_coe_iff] at hlt
    have h2 := le_ciSup (Phi_bdd P G gbar hgb hG_bdd s) ⟨g, hg⟩
    by_contra hnot
    simp only [Set.mem_union, hA, hB, Set.mem_setOf_eq, not_or, not_le] at hnot
    obtain ⟨hn1, hn2⟩ := hnot
    rw [integral_neg] at hn2
    unfold Phi at *
    simp only at h2
    rw [← hε] at hlt
    nlinarith [hsym]
  have hpA : π A ≤ ENNReal.ofReal (δ / 2) := by
    have hm := mcdiarmid_core N (fun _ => P) (Phi P G) hPhi (fun _ => gbar / N)
      (fun i S z => Phi_diff P G gbar hgb hG_bdd S i z) (gbar * ε) (mul_pos hpos hε0)
    refine hm.trans (le_of_eq ?_)
    congr 1
    have hsum : (∑ _i : Fin N, (gbar / (N:ℝ)) ^ 2 : ℝ) = gbar ^ 2 / N := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    rw [hsum]
    have : -2 * (gbar * ε) ^ 2 / (gbar ^ 2 / N) = - Real.log (2 / δ) := by
      rw [mul_pow, hε2]; field_simp
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hpB : π B ≤ ENNReal.ofReal (δ / 2) := by
    have hm := mcdiarmid_core N (fun _ => P) (fun s => - Rh G s) hRh.neg
      (fun _ => 2 * gbar / N) (fun i S z => Rh_diff hN0 G gbar hG_bdd S i z)
      (2 * gbar * ε) (by positivity)
    refine hm.trans (le_of_eq ?_)
    congr 1
    have hsum : (∑ _i : Fin N, (2 * gbar / (N:ℝ)) ^ 2 : ℝ) = 4 * gbar ^ 2 / N := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp; ring
    rw [hsum]
    have : -2 * (2 * gbar * ε) ^ 2 / (4 * gbar ^ 2 / N) = - Real.log (2 / δ) := by
      rw [mul_pow, mul_pow, hε2]; field_simp; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  calc π _ ≤ π (A ∪ B) := measure_mono hsub
    _ ≤ π A + π B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hpA hpB
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end

section
open PrescAnalytics
open PrescAnalytics.ERM
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

theorem sgn_abs (b : Bool) : |signOf b| = 1 := by
  unfold signOf; split_ifs <;> simp

theorem sgn_not (b : Bool) : signOf (!b) = - signOf b := by
  cases b <;> simp [signOf]

def flipk {d : ℕ} (k : Fin d) (ρ : Fin d → Bool) : Fin d → Bool := Function.update ρ k (!ρ k)

theorem flipk_invol {d : ℕ} (k : Fin d) : Function.Involutive (flipk k) := by
  intro ρ; funext j; unfold flipk
  by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem flipk_self {d : ℕ} (k : Fin d) (ρ : Fin d → Bool) : flipk k ρ k = !ρ k := by
  simp [flipk]

theorem flipk_ne {d : ℕ} {k j : Fin d} (h : j ≠ k) (ρ : Fin d → Bool) : flipk k ρ j = ρ j := by
  simp [flipk, Function.update_of_ne h]

theorem sg_sum_zero {d : ℕ} (k : Fin d) : ∑ ρ : Fin d → Bool, signOf (ρ k) = 0 := by
  have h := Equiv.sum_comp (flipk_invol k).toPerm (fun ρ : Fin d → Bool => signOf (ρ k))
  simp only [Function.Involutive.coe_toPerm, flipk_self, sgn_not, Finset.sum_neg_distrib] at h
  linarith

theorem card_signs (d : ℕ) : (Fintype.card (Fin d → Bool) : ℝ) = 2 ^ d := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring

theorem pair_lemma {ι : Type*} [Nonempty ι] {d : ℕ} (hd : 0 < d) (L : ℝ) (hL : 0 ≤ L)
    (a C : ι → ℝ) (w : ι → Fin d → ℝ) (B : ℝ)
    (ha : ∀ f, |a f| ≤ B) (hC : ∀ f, |C f| ≤ B) (hw : ∀ f k, |w f k| ≤ B)
    (hLip : ∀ f f', C f - C f' ≤ L * ‖w f - w f'‖) :
    (2:ℝ) ^ (d - 1) * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)))
      ≤ ∑ ρ : Fin d → Bool, ⨆ f, (a f + L * ∑ k, signOf (ρ k) * w f k) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha (Classical.arbitrary ι))
  have hbp : BddAbove (Set.range fun f => a f + C f) :=
    ⟨2 * B, by rintro _ ⟨f, rfl⟩; have := (abs_le.mp (ha f)).2; have := (abs_le.mp (hC f)).2; simp only; linarith⟩
  have hbm : BddAbove (Set.range fun f => a f - C f) :=
    ⟨2 * B, by rintro _ ⟨f, rfl⟩; have := (abs_le.mp (ha f)).2; have := (abs_le.mp (hC f)).1; simp only; linarith⟩
  have hsw : ∀ (ρ : Fin d → Bool) f, |∑ k, signOf (ρ k) * w f k| ≤ d * B := by
    intro ρ f
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |signOf (ρ k) * w f k| ≤ ∑ _k : Fin d, B := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, sgn_abs, one_mul]; exact hw f k
      _ = d * B := by simp
  have hbq : ∀ ρ : Fin d → Bool, BddAbove (Set.range fun f => a f + L * ∑ k, signOf (ρ k) * w f k) := by
    intro ρ
    refine ⟨B + L * (d * B), ?_⟩
    rintro _ ⟨f, rfl⟩
    have h1 := (abs_le.mp (ha f)).2
    have h2 := (abs_le.mp (hsw ρ f)).2
    have := mul_le_mul_of_nonneg_left h2 hL
    simp only; linarith
  set Q : (Fin d → Bool) → ℝ := fun ρ => ⨆ f, (a f + L * ∑ k, signOf (ρ k) * w f k) with hQ
  have hQge : ∀ ρ f, a f + L * ∑ k, signOf (ρ k) * w f k ≤ Q ρ :=
    fun ρ f => le_ciSup (hbq ρ) f
  have h2d : (2:ℝ) ^ d = 2 * 2 ^ (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]; ring
  have hmain : ∀ ε : ℝ, 0 < ε → (2:ℝ) ^ (d - 1) * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)))
      ≤ ∑ ρ, Q ρ + ε := by
    intro ε hε
    set δ := ε / 2 ^ d with hδ
    have hpow : (0:ℝ) < 2 ^ d := by positivity
    have hδ0 : 0 < δ := by positivity
    obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup (f := fun f => a f + C f)
      (show (⨆ f, (a f + C f)) - δ < ⨆ f, (a f + C f) by linarith)
    obtain ⟨f', hf'⟩ := exists_lt_of_lt_ciSup (f := fun f => a f - C f)
      (show (⨆ f, (a f - C f)) - δ < ⨆ f, (a f - C f) by linarith)
    obtain ⟨ks, hks⟩ := Finite.exists_max (fun k : Fin d => |w f k - w f' k|)
    have hnorm : ‖w f - w f'‖ ≤ |w f ks - w f' ks| := by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun k => ?_
      simpa [Real.norm_eq_abs] using hks k
    have hCl : C f - C f' ≤ L * |w f ks - w f' ks| :=
      (hLip f f').trans (mul_le_mul_of_nonneg_left hnorm hL)
    set Δ := w f ks - w f' ks with hΔ
    set X := (a f + C f) + (a f' - C f') with hX
    set u : Fin d → ℝ := fun k => w f k + w f' k with hu
    have key : ∀ ρ : Fin d → Bool, X + L * ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k
        ≤ Q ρ + Q (flipk ks ρ) := by
      intro ρ
      have hsplit : ∀ (σ : Fin d → Bool) (g : Fin d → ℝ),
          ∑ k, signOf (σ k) * g k = signOf (σ ks) * g ks
            + ∑ k ∈ Finset.univ.erase ks, signOf (σ k) * g k := by
        intro σ g
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ks)]
      have hflip : ∀ g : Fin d → ℝ, ∑ k ∈ Finset.univ.erase ks, signOf (flipk ks ρ k) * g k
          = ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * g k := by
        intro g
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [flipk_ne (Finset.ne_of_mem_erase hk)]
      have hsa : |signOf (ρ ks)| = 1 := sgn_abs _
      by_cases hs : 0 ≤ signOf (ρ ks) * Δ
      · have h1 := hQge ρ f
        have h2 := hQge (flipk ks ρ) f'
        rw [hsplit ρ (w f)] at h1
        rw [hsplit (flipk ks ρ) (w f'), flipk_self, sgn_not, hflip] at h2
        have habs : signOf (ρ ks) * Δ = |Δ| := by
          rw [← abs_of_nonneg hs, abs_mul, hsa, one_mul]
        have e1 : ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k
            = ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f k
              + ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f' k := by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hu]; ring
        have e2 : signOf (ρ ks) * w f ks - signOf (ρ ks) * w f' ks = |Δ| := by
          rw [← habs, hΔ]; ring
        have : L * (signOf (ρ ks) * Δ) = L * |Δ| := by rw [habs]
        nlinarith [hCl, e1, e2, mul_comm L (signOf (ρ ks) * Δ)]
      · push_neg at hs
        have h1 := hQge ρ f'
        have h2 := hQge (flipk ks ρ) f
        rw [hsplit ρ (w f')] at h1
        rw [hsplit (flipk ks ρ) (w f), flipk_self, sgn_not, hflip] at h2
        have habs : -(signOf (ρ ks) * Δ) = |Δ| := by
          rw [← abs_of_neg hs, abs_mul, hsa, one_mul]
        have e1 : ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k
            = ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f' k
              + ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f k := by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hu]; ring
        have e2 : signOf (ρ ks) * w f' ks - signOf (ρ ks) * w f ks = |Δ| := by
          rw [← habs, hΔ]; ring
        nlinarith [hCl, e1, e2]
    -- sum
    have hsumQ : ∑ ρ, (Q ρ + Q (flipk ks ρ)) = 2 * ∑ ρ, Q ρ := by
      have h := Equiv.sum_comp (flipk_invol ks).toPerm Q
      simp only [Function.Involutive.coe_toPerm] at h
      rw [Finset.sum_add_distrib, h]; ring
    have hzero : ∑ ρ : Fin d → Bool, (∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp_rw [← Finset.sum_mul]
      rw [sg_sum_zero]; ring
    have hlow : ∑ ρ : Fin d → Bool, (X + L * ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k)
        ≤ ∑ ρ, (Q ρ + Q (flipk ks ρ)) := Finset.sum_le_sum fun ρ _ => key ρ
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, card_signs, hsumQ] at hlow
    have hXl : (⨆ f, (a f + C f)) + (⨆ f, (a f - C f)) - 2 * δ < X := by
      rw [hX]; linarith
    have : (2:ℝ) ^ d * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)) - 2 * δ) ≤ 2 * ∑ ρ, Q ρ := by
      calc (2:ℝ) ^ d * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)) - 2 * δ) ≤ 2 ^ d * X :=
            mul_le_mul_of_nonneg_left hXl.le hpow.le
        _ ≤ _ := by linarith
    have hεδ : (2:ℝ) ^ d * δ = ε := by rw [hδ]; field_simp
    rw [h2d] at this hεδ
    nlinarith
  exact le_of_forall_pos_le_add fun ε hε => hmain ε hε

theorem sum_cons_fin {β : Type*} [Fintype β] (N : ℕ) (F : (Fin (N+1) → β) → ℝ) :
    ∑ σ, F σ = ∑ b : β, ∑ σ' : Fin N → β, F (Fin.cons b σ') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => β)) _ _ (fun p => rfl)).symm

theorem core_ind {ι : Type*} [Nonempty ι] {d : ℕ} (hd : 0 < d) (L : ℝ) (hL : 0 ≤ L)
    (M K : ℝ) :
    ∀ (N : ℕ) (v : ι → Fin N → Fin d → ℝ) (C : Fin N → (Fin d → ℝ) → ℝ)
      (_hv : ∀ f i k, |v f i k| ≤ M) (_hCb : ∀ f i, |C i (v f i)| ≤ K)
      (_hLip : ∀ i z z', C i z - C i z' ≤ L * ‖z - z'‖)
      (a : ι → ℝ) (K0 : ℝ) (_ha : ∀ f, |a f| ≤ K0),
      (2:ℝ) ^ (N * (d - 1)) * ∑ τ : Fin N → Bool, ⨆ f, (a f + ∑ i, signOf (τ i) * C i (v f i))
        ≤ ∑ σ : Fin N → Fin d → Bool, ⨆ f, (a f + L * ∑ i, ∑ k, signOf (σ i k) * v f i k) := by
  intro N
  induction N with
  | zero =>
    intro v C hv hCb hLip a K0 ha
    simp
  | succ N ih =>
    intro v C hv hCb hLip a K0 ha
    obtain ⟨f0⟩ := (inferInstance : Nonempty ι)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hv f0 0 ⟨0, hd⟩)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hCb f0 0)
    have hK00 : 0 ≤ K0 := (abs_nonneg _).trans (ha f0)
    -- left side decomposition
    have hLHS : ∑ τ : Fin (N+1) → Bool, ⨆ f, (a f + ∑ i, signOf (τ i) * C i (v f i))
        = ∑ b : Bool, ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i)) := by
      rw [sum_cons_fin]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun τ' _ => ?_
      congr 1; funext f
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    -- apply IH for each b
    have hIH : ∀ b : Bool, (2:ℝ) ^ (N * (d - 1)) * ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i))
        ≤ ∑ σ' : Fin N → Fin d → Bool, ⨆ f, ((a f + signOf b * C 0 (v f 0)) + L *
            ∑ i : Fin N, ∑ k, signOf (σ' i k) * (fun f (i : Fin N) => v f i.succ) f i k) := by
      intro b
      refine ih (fun f (i : Fin N) => v f i.succ) (fun (i : Fin N) z => C i.succ z)
        (fun f i k => hv f i.succ k) (fun f i => hCb f i.succ) (fun i z z' => hLip i.succ z z')
        (fun f => a f + signOf b * C 0 (v f 0)) (K0 + K) (fun f => ?_)
      calc |a f + signOf b * C 0 (v f 0)| ≤ |a f| + |signOf b * C 0 (v f 0)| := abs_add_le _ _
        _ ≤ K0 + K := by
          rw [abs_mul, sgn_abs, one_mul]; exact add_le_add (ha f) (hCb f 0)
    -- right side decomposition
    have hRHS : ∑ σ : Fin (N+1) → Fin d → Bool, ⨆ f,
          (a f + L * ∑ i, ∑ k, signOf (σ i k) * v f i k)
        = ∑ σ' : Fin N → Fin d → Bool, ∑ ρ : Fin d → Bool, ⨆ f,
          ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k)
            + L * ∑ k, signOf (ρ k) * (fun f => v f 0) f k) := by
      rw [sum_cons_fin, Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ' _ => Finset.sum_congr rfl fun ρ _ => ?_
      congr 1; funext f
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    -- per σ' inequality via pair lemma
    set B : ℝ := K0 + K + M + L * (N * (d * M)) with hB
    have hLNM : 0 ≤ L * (N * (d * M)) := by positivity
    have hpair : ∀ σ' : Fin N → Fin d → Bool,
        (2:ℝ) ^ (d - 1) * ∑ b : Bool, ⨆ f, (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
            + signOf b * C 0 (v f 0))
        ≤ ∑ ρ : Fin d → Bool, ⨆ f,
          ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k)
            + L * ∑ k, signOf (ρ k) * (fun f => v f 0) f k) := by
      intro σ'
      have hR : ∀ f, |L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k| ≤ L * (N * (d * M)) := by
        intro f
        rw [abs_mul, abs_of_nonneg hL]
        refine mul_le_mul_of_nonneg_left ?_ hL
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i : Fin N, |∑ k, signOf (σ' i k) * v f i.succ k| ≤ ∑ _i : Fin N, (d * M) := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              calc ∑ k, |signOf (σ' i k) * v f i.succ k| ≤ ∑ _k : Fin d, M := by
                    refine Finset.sum_le_sum fun k _ => ?_
                    rw [abs_mul, sgn_abs, one_mul]; exact hv f i.succ k
                _ = d * M := by simp
          _ = N * (d * M) := by simp
      have hp := pair_lemma hd L hL (fun f => a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k)
        (fun f => C 0 (v f 0)) (fun f => v f 0) B
        (fun f => (abs_add_le _ _).trans (by have := ha f; have := hR f; rw [hB]; linarith))
        (fun f => (hCb f 0).trans (by rw [hB]; linarith))
        (fun f k => (hv f 0 k).trans (by rw [hB]; linarith))
        (fun f f' => hLip 0 (v f 0) (v f' 0))
      have e : ∑ b : Bool, ⨆ f, (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
            + signOf b * C 0 (v f 0))
          = (⨆ f, ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k) + C 0 (v f 0)))
            + ⨆ f, ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k) - C 0 (v f 0)) := by
        rw [Fintype.sum_bool]
        simp only [signOf, if_true, Bool.false_eq_true, if_false]
        congr 2
        · funext f; ring
        · funext f; ring
      rw [e]; exact hp
    have hT : ∀ (b : Bool) (σ' : Fin N → Fin d → Bool), ⨆ f, ((a f + signOf b * C 0 (v f 0)) + L *
            ∑ i : Fin N, ∑ k, signOf (σ' i k) * (fun f (i : Fin N) => v f i.succ) f i k)
        = ⨆ f, (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
            + signOf b * C 0 (v f 0)) := by
      intro b σ'; congr 1; funext f; ring
    rw [hLHS, hRHS]
    have hpow : (2:ℝ) ^ ((N + 1) * (d - 1)) = 2 ^ (d - 1) * 2 ^ (N * (d - 1)) := by
      rw [← pow_add]; congr 1; ring
    calc (2:ℝ) ^ ((N + 1) * (d - 1)) * ∑ b : Bool, ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i))
        = (2:ℝ) ^ (d - 1) * ∑ b : Bool, ((2:ℝ) ^ (N * (d - 1)) * ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i))) := by
          rw [hpow, mul_assoc, Finset.mul_sum]
      _ ≤ (2:ℝ) ^ (d - 1) * ∑ b : Bool, ∑ σ' : Fin N → Fin d → Bool, ⨆ f,
            (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
              + signOf b * C 0 (v f 0)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
          refine (hIH b).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun σ' _ => hT b σ'
      _ = ∑ σ' : Fin N → Fin d → Bool, (2:ℝ) ^ (d - 1) * ∑ b : Bool, ⨆ f,
            (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
              + signOf b * C 0 (v f 0)) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun σ' _ => hpair σ'

end

section
open PrescAnalytics
open PrescAnalytics.ERM
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X Y : Type*} {d N : ℕ}

theorem S_not (F : Set (X → Fin d → ℝ)) (x : Fin N → X) (σ : Fin N → Fin d → Bool)
    (f : X → Fin d → ℝ) :
    ∑ i, ∑ k, signOf ((fun i k => !(σ i k)) i k) * f (x i) k
      = - ∑ i, ∑ k, signOf (σ i k) * f (x i) k := by
  simp only [sgn_not, neg_mul, Finset.sum_neg_distrib]

theorem S_diff (x : Fin N → X) (i : Fin N) (k : Fin d) (f : X → Fin d → ℝ) :
    ∑ i', ∑ k', signOf ((fun (_ : Fin N) (_ : Fin d) => true) i' k') * f (x i') k'
      - ∑ i', ∑ k', signOf ((Function.update (fun (_ : Fin N) (_ : Fin d) => true) i
          (Function.update (fun (_ : Fin d) => true) k false)) i' k') * f (x i') k'
      = 2 * f (x i) k := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp [signOf]; ring
    · intro k' _ hk'
      simp [Function.update_of_ne hk']
    · simp
  · intro i' _ hi'
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k' _ => ?_
    simp [Function.update_of_ne hi']
  · simp

theorem coord_bound (F : Set (X → Fin d → ℝ)) (x : Fin N → X)
    (hfin : ∀ σ : Fin N → Fin d → Bool,
      BddAbove (Set.range fun f : F => ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : F) i k, |f.1 (x i) k| ≤ M := by
  choose B hB using hfin
  set M0 : ℝ := ∑ σ : Fin N → Fin d → Bool, |B σ| with hM0
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hle : ∀ σ, |B σ| ≤ M0 := fun σ =>
    Finset.single_le_sum (f := fun σ => |B σ|) (fun σ _ => abs_nonneg _) (Finset.mem_univ σ)
  have hS : ∀ (σ : Fin N → Fin d → Bool) (f : F),
      |∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k| ≤ M0 := by
    intro σ f
    rw [abs_le]
    constructor
    · have h1 : ∑ i, ∑ k, signOf ((fun i k => !(σ i k)) i k) * f.1 (x i) k ≤ B (fun i k => !(σ i k)) :=
        hB _ ⟨f, rfl⟩
      rw [S_not F x σ f.1] at h1
      have := hle (fun i k => !(σ i k)); have := le_abs_self (B fun i k => !(σ i k))
      linarith
    · have h1 : ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k ≤ B σ := hB σ ⟨f, rfl⟩
      have := hle σ; have := le_abs_self (B σ)
      linarith
  refine ⟨M0, hM0nn, fun f i k => ?_⟩
  have hd := S_diff x i k f.1
  have h1 := hS (fun _ _ => true) f
  have h2 := hS (Function.update (fun (_ : Fin N) (_ : Fin d) => true) i
          (Function.update (fun (_ : Fin d) => true) k false)) f
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem real_step (hd : 0 < d) (F : Set (X → Fin d → ℝ)) [Nonempty F]
    (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (x : Fin N → X) (y : Fin N → Y)
    (hfin : ∀ σ : Fin N → Fin d → Bool,
      BddAbove (Set.range fun f : F => ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k)) :
    (∀ τ : Fin N → Bool,
        BddAbove (Set.range fun f : F => ∑ i, signOf (τ i) * c (f.1 (x i)) (y i))) ∧
    (2:ℝ) ^ (N * (d - 1)) * ∑ τ : Fin N → Bool, ⨆ f : F, ∑ i, signOf (τ i) * c (f.1 (x i)) (y i)
      ≤ L * ∑ σ : Fin N → Fin d → Bool, ⨆ f : F, ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k := by
  obtain ⟨M, hM0, hM⟩ := coord_bound F x hfin
  set K : ℝ := ∑ i, |c 0 (y i)| + L * M with hK
  have hnorm : ∀ (f : F) i, ‖f.1 (x i)‖ ≤ M := fun f i =>
    (pi_norm_le_iff_of_nonneg hM0).2 fun k => by simpa [Real.norm_eq_abs] using hM f i k
  have hC : ∀ (f : F) i, |c (f.1 (x i)) (y i)| ≤ K := by
    intro f i
    have h1 := hc_lip (f.1 (x i)) 0 (y i)
    rw [sub_zero] at h1
    have h2 : |c (f.1 (x i)) (y i)| ≤ |c 0 (y i)| + L * M := by
      calc |c (f.1 (x i)) (y i)| = |(c (f.1 (x i)) (y i) - c 0 (y i)) + c 0 (y i)| := by ring_nf
        _ ≤ |c (f.1 (x i)) (y i) - c 0 (y i)| + |c 0 (y i)| := abs_add_le _ _
        _ ≤ L * ‖f.1 (x i)‖ + |c 0 (y i)| := add_le_add h1 le_rfl
        _ ≤ L * M + |c 0 (y i)| := by gcongr; exact hnorm f i
        _ = _ := by ring
    have h3 : |c 0 (y i)| ≤ ∑ j, |c 0 (y j)| :=
      Finset.single_le_sum (f := fun j => |c 0 (y j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hK]; linarith
  have hT : ∀ τ : Fin N → Bool,
      BddAbove (Set.range fun f : F => ∑ i, signOf (τ i) * c (f.1 (x i)) (y i)) := by
    intro τ
    refine ⟨N * K, ?_⟩
    rintro _ ⟨f, rfl⟩
    have : |∑ i, signOf (τ i) * c (f.1 (x i)) (y i)| ≤ N * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |signOf (τ i) * c (f.1 (x i)) (y i)| ≤ ∑ _i : Fin N, K :=
            Finset.sum_le_sum fun i _ => by rw [abs_mul, sgn_abs, one_mul]; exact hC f i
        _ = N * K := by simp
    exact (abs_le.mp this).2
  refine ⟨hT, ?_⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hcore := core_ind hd L hL M K N (fun (f : F) i => f.1 (x i)) (fun i z => c z (y i))
    (fun f i k => hM f i k) (fun f i => hC f i)
    (fun i z z' => (le_abs_self _).trans (hc_lip z z' (y i))) (fun _ => 0) 0 (fun _ => by simp)
  simp only [zero_add] at hcore
  have hmul : ∀ σ : Fin N → Fin d → Bool, (⨆ f : F, L * ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k)
      = L * ⨆ f : F, ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k := fun σ =>
    (Real.mul_iSup_of_nonneg hL _).symm
  simp only [hmul, ← Finset.mul_sum] at hcore
  exact hcore

theorem iSup_coe_bdd {ι : Type*} [Nonempty ι] (g : ι → ℝ) (h : (⨆ i, (g i : EReal)) ≠ ⊤) :
    BddAbove (Set.range g) := by
  have hbot : (⨆ i, (g i : EReal)) ≠ ⊥ := by
    intro hb
    have i0 := Classical.arbitrary ι
    have := le_iSup (fun i => (g i : EReal)) i0
    rw [hb] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  refine ⟨(⨆ i, (g i : EReal)).toReal, ?_⟩
  rintro _ ⟨i, rfl⟩
  have := le_iSup (fun i => (g i : EReal)) i
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal h hbot]; exact this

theorem ereal_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact EReal.add_ne_bot_iff.mpr ⟨h j (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

theorem ereal_sum_top {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i ∈ s, f i ≠ ⊥)
    (i0 : ι) (hi0 : i0 ∈ s) (hf : f i0 = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  rw [← Finset.add_sum_erase s f hi0, hf]
  exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot _ _ fun i hi => h i (Finset.mem_of_mem_erase hi))

theorem ereal_sum_bot {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    ∑ _i ∈ s, (⊥ : EReal) = ⊥ := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih => rw [Finset.sum_cons, ih]; simp

theorem signedSup_cost (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (s : Fin N → X × Y)
    (σ : Fin N → Fin 1 → Bool) :
    signedSup (liftClass (costClass c F)) s σ
      = ⨆ f : F, ((∑ i, signOf (σ i 0) * c (f.1 (s i).1) (s i).2 : ℝ) : EReal) := by
  have himg : liftClass (costClass c F)
      = (fun f : X → Fin d → ℝ => fun (p : X × Y) (_ : Fin 1) => c (f p.1) p.2) '' F := by
    ext g'; constructor
    · rintro ⟨g, ⟨f, hf, rfl⟩, rfl⟩; exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩; exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  unfold signedSup
  rw [himg, iSup_image]
  have : ∀ f : X → Fin d → ℝ, (∑ i, ∑ k : Fin 1, signOf (σ i k) *
      (fun (p : X × Y) (_ : Fin 1) => c (f p.1) p.2) (s i) k)
      = ∑ i, signOf (σ i 0) * c (f (s i).1) (s i).2 := by intro f; simp
  simp only [this]
  exact (iSup_subtype'' F (fun f => ((∑ i, signOf (σ i 0) * c (f (s i).1) (s i).2 : ℝ) : EReal))).symm

theorem signedSup_eq' (F : Set (X → Fin d → ℝ)) (x : Fin N → X) (σ : Fin N → Fin d → Bool) :
    signedSup F x σ = ⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal) := by
  unfold signedSup
  exact (iSup_subtype'' F (fun f => ((∑ i, ∑ k, signOf (σ i k) * f (x i) k : ℝ) : EReal))).symm

theorem ereal_iSup_coe' {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddAbove (Set.range f)) :
    (⨆ i, (f i : EReal)) = ((⨆ i, f i : ℝ) : EReal) := by
  have := Monotone.map_ciSup_of_continuousAt (f := ((↑) : ℝ → EReal)) (g := f)
    continuous_coe_real_ereal.continuousAt (fun a b h => EReal.coe_le_coe_iff.mpr h) hf
  exact this.symm

theorem lemma1_i (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (s : Fin N → X × Y) :
    empRademacherR (costClass c F) s ≤ (L : EReal) * empRademacher F (fun i => (s i).1) := by
  classical
  unfold empRademacherR empRademacher
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc1 : (0 : ℝ) < 2 / N / 2 ^ (N * 1) := by positivity
  have hc2 : (0 : ℝ) < 2 / N / 2 ^ (N * d) := by positivity
  rcases F.eq_empty_or_nonempty with hF | ⟨f0, hf0⟩
  · subst hF
    have hsb : ∀ σ : Fin N → Fin 1 → Bool,
        signedSup (liftClass (costClass c (∅ : Set (X → Fin d → ℝ)))) s σ = ⊥ := by
      intro σ
      have : liftClass (costClass c (∅ : Set (X → Fin d → ℝ))) = ∅ := by
        ext g; simp [liftClass, costClass]
      rw [this]; simp [signedSup]
    simp only [hsb]
    rw [ereal_sum_bot _ Finset.univ_nonempty, EReal.coe_mul_bot_of_pos hc1]
    exact bot_le
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  set x : Fin N → X := fun i => (s i).1 with hx
  set y : Fin N → Y := fun i => (s i).2 with hy
  simp only [signedSup_cost, signedSup_eq' F x]
  -- left side as a sum over τ
  have eL : ∑ σ : Fin N → Fin 1 → Bool,
        (⨆ f : F, ((∑ i, signOf (σ i 0) * c (f.1 (s i).1) (s i).2 : ℝ) : EReal))
      = ∑ τ : Fin N → Bool,
        (⨆ f : F, ((∑ i, signOf (τ i) * c (f.1 (x i)) (y i) : ℝ) : EReal)) :=
    Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.funUnique (Fin 1) Bool) _ _
      (fun σ => rfl)
  rw [eL]
  by_cases hdeg : d = 0 ∨ L = 0
  · -- degenerate case
    have hceq : ∀ (z z' : Fin d → ℝ) (y : Y), c z y = c z' y := by
      intro z z' y
      have h := hc_lip z z' y
      have : L * ‖z - z'‖ = 0 := by
        rcases hdeg with h0 | h0
        · subst h0
          have : z - z' = 0 := Subsingleton.elim _ _
          rw [this]; simp
        · rw [h0]; ring
      rw [this] at h
      have := abs_nonneg (c z y - c z' y)
      have h0 : |c z y - c z' y| = 0 := le_antisymm h this
      linarith [abs_eq_zero.mp h0]
    have hL0 : ∀ τ : Fin N → Bool,
        (⨆ f : F, ((∑ i, signOf (τ i) * c (f.1 (x i)) (y i) : ℝ) : EReal))
          = ((∑ i, signOf (τ i) * c (f0 (x i)) (y i) : ℝ) : EReal) := by
      intro τ
      have : (fun f : F => ((∑ i, signOf (τ i) * c (f.1 (x i)) (y i) : ℝ) : EReal))
          = fun _ => ((∑ i, signOf (τ i) * c (f0 (x i)) (y i) : ℝ) : EReal) := by
        funext f; congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hceq (f.1 (x i)) (f0 (x i))]
      rw [this]; exact iSup_const
    simp only [hL0]
    have hz : ∑ τ : Fin N → Bool, ((∑ i, signOf (τ i) * c (f0 (x i)) (y i) : ℝ) : EReal) = 0 := by
      rw [← EReal.coe_finset_sum]
      have : ∑ τ : Fin N → Bool, ∑ i, signOf (τ i) * c (f0 (x i)) (y i) = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp_rw [← Finset.sum_mul]
        rw [sg_sum_zero]; ring
      rw [this]; rfl
    rw [hz, mul_zero]
    -- right side is zero
    rcases hdeg with h0 | h0
    · subst h0
      have : ∀ σ : Fin N → Fin 0 → Bool,
          (⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal)) = 0 := by
        intro σ; simp
      simp only [this]; simp
    · rw [h0]; simp
  · push_neg at hdeg
    obtain ⟨hd0, hL0⟩ := hdeg
    have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    by_cases hb : ∃ σ : Fin N → Fin d → Bool,
        (⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal)) = ⊤
    · obtain ⟨σ0, hσ0⟩ := hb
      have hnb : ∀ σ : Fin N → Fin d → Bool,
          (⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal)) ≠ ⊥ := by
        intro σ hbot
        have := le_iSup (fun f : F => ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal))
          ⟨f0, hf0⟩
        rw [hbot] at this
        exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
      rw [ereal_sum_top _ _ (fun σ _ => hnb σ) σ0 (Finset.mem_univ _) hσ0,
        EReal.coe_mul_top_of_pos hc2, EReal.coe_mul_top_of_pos hLpos]
      exact le_top
    · push_neg at hb
      have hfin : ∀ σ : Fin N → Fin d → Bool,
          BddAbove (Set.range fun f : F => ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k) :=
        fun σ => iSup_coe_bdd _ (hb σ)
      obtain ⟨hT, hineq⟩ := real_step hd F c L hL hc_lip x y hfin
      simp only [ereal_iSup_coe' _ (hfin _), ereal_iSup_coe' _ (hT _)]
      rw [← EReal.coe_finset_sum, ← EReal.coe_finset_sum, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul]
      rw [EReal.coe_le_coe_iff]
      -- real inequality
      have hnd : N * d = N + N * (d - 1) := by
        obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        rw [he, Nat.add_sub_cancel]; ring
      have hp : (2:ℝ) ^ (N * d) = 2 ^ N * 2 ^ (N * (d - 1)) := by rw [hnd, pow_add]
      have hp1 : (0:ℝ) < 2 ^ N := by positivity
      have hp2 : (0:ℝ) < 2 ^ (N * (d - 1)) := by positivity
      rw [Nat.mul_one, hp]
      set A := ∑ τ : Fin N → Bool, ⨆ f : F, ∑ i, signOf (τ i) * c (f.1 (x i)) (y i) with hA
      set Bsum := ∑ σ : Fin N → Fin d → Bool, ⨆ f : F, ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k
        with hBs
      have h1 : 2 / (N:ℝ) / 2 ^ N * A = 2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) *
          (2 ^ (N * (d - 1)) * A) := by field_simp
      rw [h1]
      calc 2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) * (2 ^ (N * (d - 1)) * A)
          ≤ 2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) * (L * Bsum) :=
            mul_le_mul_of_nonneg_left hineq (by positivity)
        _ = L * (2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) * Bsum) := by ring

end

section
open PrescAnalytics
open PrescAnalytics.ERM
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d N : ℕ}

theorem signedSup_meas (F : Set (X → Fin d → ℝ)) (hFm : ∀ f ∈ F, Measurable f)
    (hFs : IsPointwiseSeparable F) (σ : Fin N → Fin d → Bool) :
    Measurable (fun s : Fin N → X => signedSup F s σ) := by
  obtain ⟨F0, hF0G, hF0c, hF0⟩ := hFs
  have heq : ∀ s : Fin N → X, signedSup F s σ = ⨆ g ∈ F0,
      ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal) := by
    intro s
    unfold signedSup
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      obtain ⟨u, hu, hlim⟩ := hF0 g hg
      have ht : Tendsto (fun n => ((∑ i, ∑ k, signOf (σ i k) * u n (s i) k : ℝ) : EReal))
          atTop (𝓝 ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal)) := by
        refine (continuous_coe_real_ereal.tendsto _).comp ?_
        refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun k _ => ?_
        exact tendsto_const_nhds.mul (tendsto_pi_nhds.mp (hlim (s i)) k)
      refine le_of_tendsto ht (Eventually.of_forall fun n => ?_)
      exact le_iSup₂ (f := fun g (_ : g ∈ F0) =>
        ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal)) (u n) (hu n)
    · exact biSup_mono (fun g hg => hF0G hg)
  have : (fun s : Fin N → X => signedSup F s σ) = fun s => ⨆ g ∈ F0,
      ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal) := funext heq
  rw [this]
  refine Measurable.biSup F0 hF0c fun g hg => ?_
  refine continuous_coe_real_ereal.measurable.comp ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hgk : Measurable (fun u : X => g u k) := (measurable_pi_apply k).comp (hFm g (hF0G hg))
  exact (hgk.comp (measurable_pi_apply i)).const_mul _

theorem empRad_meas (F : Set (X → Fin d → ℝ)) (hFm : ∀ f ∈ F, Measurable f)
    (hFs : IsPointwiseSeparable F) :
    Measurable (fun s : Fin N → X => empRademacher F s) := by
  unfold empRademacher
  exact (Finset.measurable_sum _ fun σ _ => signedSup_meas F hFm hFs σ).const_mul _

theorem lemma1_ii (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (N : ℕ)
    (hFm : ∀ f ∈ F, Measurable f) (hFs : IsPointwiseSeparable F) :
    margRademacherR μ N (costClass c F) ≤
      ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F := by
  unfold margRademacherR margRademacher
  haveI : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hmap : (Measure.pi fun _ : Fin N => μ).map (fun (s : Fin N → X × Y) i => (s i).1)
      = Measure.pi fun _ : Fin N => μ.map Prod.fst :=
    Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)
  have hgm : Measurable (fun (s : Fin N → X × Y) i => (s i).1) :=
    measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
  have hφ : Measurable (fun t : Fin N → X => (empRademacher F t).toENNReal) :=
    (empRad_meas F hFm hFs).ereal_toENNReal
  calc ∫⁻ s, (empRademacher (liftClass (costClass c F)) s).toENNReal ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ∫⁻ s, (ENNReal.ofReal L * (empRademacher F (fun i => (s i).1)).toENNReal)
          ∂(Measure.pi fun _ : Fin N => μ) := by
        refine lintegral_mono fun s => ?_
        have h := lemma1_i F c L hL hc_lip s
        have h2 := EReal.toENNReal_le_toENNReal h
        rw [EReal.toENNReal_mul (by exact_mod_cast hL)] at h2
        exact h2
    _ = ENNReal.ofReal L * ∫⁻ s, (empRademacher F (fun i => (s i).1)).toENNReal
          ∂(Measure.pi fun _ : Fin N => μ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        congr 1
        rw [← hmap, lintegral_map hφ hgm]

end

section
open PrescAnalytics
open PrescAnalytics.ERM
open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}

theorem cost_meas (F : Set (X → Fin d → ℝ)) (hFm : ∀ f ∈ F, Measurable f)
    (c : (Fin d → ℝ) → Y → ℝ) (hc_meas : Measurable (Function.uncurry c)) :
    ∀ g ∈ costClass c F, Measurable g := by
  rintro g ⟨f, hf, rfl⟩
  exact hc_meas.comp (((hFm f hf).comp measurable_fst).prodMk measurable_snd)

theorem cost_sep (F : Set (X → Fin d → ℝ)) (hFs : IsPointwiseSeparable F)
    (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖) :
    IsPointwiseSeparable (costClass c F) := by
  obtain ⟨F0, hF0G, hF0c, hF0⟩ := hFs
  refine ⟨costClass c F0, ?_, ?_, ?_⟩
  · rintro g ⟨f, hf, rfl⟩; exact ⟨f, hF0G hf, rfl⟩
  · have : costClass c F0
        = (fun f : X → Fin d → ℝ => fun p : X × Y => c (f p.1) p.2) '' F0 := by
      ext g; constructor
      · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
      · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
    rw [this]; exact hF0c.image _
  · rintro g ⟨f, hf, rfl⟩
    obtain ⟨u, hu, hlim⟩ := hF0 f hf
    refine ⟨fun n p => c (u n p.1) p.2, fun n => ⟨u n, hu n, rfl⟩, fun p => ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n => ‖u n p.1 - f p.1‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (hlim p.1)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.const_mul L)
    rw [Real.norm_eq_abs]; exact hc_lip _ _ _

theorem thm13_core
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ]
    (F : Set (X → Fin d → ℝ)) (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_sep : IsPointwiseSeparable F)
    (c : (Fin d → ℝ) → Y → ℝ) (hc_meas : Measurable (Function.uncurry c))
    (cbar L : ℝ) (hc_bdd : ∀ (z : Fin d → ℝ) (y : Y), 0 ≤ c z y ∧ c z y ≤ cbar)
    (hL : 0 ≤ L) (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F <
          ENNReal.ofReal (expCost μ c f - empCost s c f
            - cbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, (L : EReal) * empRademacher F (fun i => (s i).1) <
          ((expCost μ c f - empCost s c f
            - 3 * cbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)}
        ≤ ENNReal.ofReal δ := by
  have hG_meas := cost_meas F hF_meas c hc_meas
  have hG_sep := cost_sep F hF_sep c L hc_lip
  have hG_bdd : ∀ g ∈ costClass c F, ∀ u, 0 ≤ g u ∧ g u ≤ cbar := by
    rintro g ⟨f, hf, rfl⟩ u; exact hc_bdd _ _
  constructor
  · refine le_trans (measure_mono ?_)
      (eq29_core μ (costClass c F) cbar hG_meas hG_sep hG_bdd N hN δ hδ)
    rintro s ⟨f, hf, hlt⟩
    refine ⟨fun p => c (f p.1) p.2, ⟨f, hf, rfl⟩, ?_⟩
    exact lt_of_le_of_lt (lemma1_ii F c L hL hc_lip μ N hF_meas hF_sep) hlt
  · refine le_trans (measure_mono ?_)
      (eq30_core μ (costClass c F) cbar hG_meas hG_sep hG_bdd N hN δ hδ)
    rintro s ⟨f, hf, hlt⟩
    refine ⟨fun p => c (f p.1) p.2, ⟨f, hf, rfl⟩, ?_⟩
    exact lt_of_le_of_lt (lemma1_i F c L hL hc_lip s) hlt

end

section
open PrescAnalytics.ERM
open MeasureTheory

theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ]
    (F : Set (X → Fin d → ℝ)) (hF_meas : ∀ f ∈ F, Measurable f) (hF_sep : IsPointwiseSeparable F)
    (c : (Fin d → ℝ) → Y → ℝ) (hc_meas : Measurable (Function.uncurry c))
    (cbar L : ℝ) (hc_bdd : ∀ (z : Fin d → ℝ) (y : Y), 0 ≤ c z y ∧ c z y ≤ cbar)
    (hL : 0 ≤ L) (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F <
          ENNReal.ofReal (expCost μ c f - empCost s c f
            - cbar * Real.sqrt (Real.log (1 / δ) / (2 * N)))} ≤ ENNReal.ofReal δ ∧
    (Measure.pi fun _ : Fin N => μ)
        {s | ∃ f ∈ F, (L : EReal) * empRademacher F (fun i => (s i).1) <
          ((expCost μ c f - empCost s c f
            - 3 * cbar * Real.sqrt (Real.log (2 / δ) / (2 * N)) : ℝ) : EReal)} ≤ ENNReal.ofReal δ := by
  exact thm13_core μ F hF_meas hF_sep c hc_meas cbar L hc_bdd hL hc_lip N hN δ hδ

end
