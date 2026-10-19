-- Prove2me | solution 1 for VarianceRegularization.Covering.sample_std_upper_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T12:59:11.580162+00:00
-- url     : https://prove2.me/submissions/8f99abca-fe14-4308-8895-6a448556eb9b

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory ProbabilityTheory Filter Topology

namespace SU3


/-- Entropy `Ent_μ(g) = E[g log g] - E[g] log E[g]`. -/
noncomputable def ent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ) : ℝ :=
  ∫ ω, g ω * Real.log (g ω) ∂μ - (∫ ω, g ω ∂μ) * Real.log (∫ ω, g ω ∂μ)

section General

variable {Ω : Type*} [MeasurableSpace Ω]

lemma intOfBdd {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

lemma abs_le_of_mem {m M x : ℝ} (h1 : m ≤ x) (h2 : x ≤ M) : |x| ≤ |m| + |M| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := neg_abs_le m; have := abs_nonneg M; linarith
  · have := le_abs_self M; have := abs_nonneg m; linarith

lemma abs_log_le {m M x : ℝ} (hm : 0 < m) (h1 : m ≤ x) (h2 : x ≤ M) :
    |Real.log x| ≤ |Real.log m| + |Real.log M| := by
  have hx : 0 < x := lt_of_lt_of_le hm h1
  exact abs_le_of_mem (Real.log_le_log hm h1) (Real.log_le_log hx h2)

lemma glog_bdd {m M x : ℝ} (hm : 0 < m) (h1 : m ≤ x) (h2 : x ≤ M) :
    |x * Real.log x| ≤ M * (|Real.log m| + |Real.log M|) := by
  have hx : 0 < x := lt_of_lt_of_le hm h1
  rw [abs_mul, abs_of_pos hx]
  exact mul_le_mul h2 (abs_log_le hm h1 h2) (abs_nonneg _) (by linarith)

lemma integral_mem_of {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {m M : ℝ} (hm : ∀ ω, m ≤ f ω) (hM : ∀ ω, f ω ≤ M) :
    m ≤ ∫ ω, f ω ∂μ ∧ ∫ ω, f ω ∂μ ≤ M := by
  have hI : Integrable f μ := intOfBdd hf (|m| + |M|) (fun ω => abs_le_of_mem (hm ω) (hM ω))
  constructor
  · have := integral_mono (integrable_const m) hI hm
    simpa using this
  · have := integral_mono hI (integrable_const M) hM
    simpa using this

lemma abs_integral_le_of {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) : |∫ ω, f ω ∂μ| ≤ C := by
  have h := integral_mem_of (μ := μ) hf (m := -C) (M := C) (fun ω => (abs_le.mp (hC ω)).1)
    (fun ω => (abs_le.mp (hC ω)).2)
  exact abs_le.mpr h

lemma young_pt {g h m0 : ℝ} (hg : 0 < g) (hm0 : 0 < m0) :
    g * h ≤ g * Real.log g - g * Real.log m0 - g + m0 * Real.exp h := by
  have h1 := Real.add_one_le_exp (h - Real.log g + Real.log m0)
  have h2 : Real.exp (h - Real.log g + Real.log m0) = Real.exp h * m0 / g := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hg, Real.exp_log hm0]; ring
  rw [h2, le_div_iff₀ hg] at h1
  linear_combination h1

lemma ent_abs_le (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Measurable g)
    {m M : ℝ} (hm : 0 < m) (hgm : ∀ ω, m ≤ g ω) (hgM : ∀ ω, g ω ≤ M) :
    |ent μ g| ≤ 2 * (M * (|Real.log m| + |Real.log M|)) := by
  have h1 := abs_integral_le_of (μ := μ) (f := fun ω => g ω * Real.log (g ω)) (hg.mul hg.log)
    (fun ω => glog_bdd hm (hgm ω) (hgM ω))
  obtain ⟨a, b⟩ := integral_mem_of (μ := μ) hg hgm hgM
  have h2 := glog_bdd hm a b
  unfold ent
  calc _ ≤ |∫ ω, g ω * Real.log (g ω) ∂μ| + |(∫ ω, g ω ∂μ) * Real.log (∫ ω, g ω ∂μ)| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-- Gibbs / duality inequality: `E[g h] ≤ Ent(g)` when `E[e^h] = 1`. -/
lemma gibbs (μ : Measure Ω) [IsProbabilityMeasure μ] {g h : Ω → ℝ} (hg : Measurable g)
    (hh : Measurable h) {m M K : ℝ} (hm : 0 < m) (hgm : ∀ ω, m ≤ g ω) (hgM : ∀ ω, g ω ≤ M)
    (hK : ∀ ω, |h ω| ≤ K) (hexp : ∫ ω, Real.exp (h ω) ∂μ = 1) :
    ∫ ω, g ω * h ω ∂μ ≤ ent μ g := by
  obtain ⟨hm0, -⟩ := integral_mem_of (μ := μ) hg hgm hgM
  set m0 := ∫ ω, g ω ∂μ with hm0def
  have hm0p : 0 < m0 := lt_of_lt_of_le hm hm0
  have hgpos : ∀ ω, 0 < g ω := fun ω => lt_of_lt_of_le hm (hgm ω)
  have gI : Integrable g μ := intOfBdd hg (|m| + |M|) (fun ω => abs_le_of_mem (hgm ω) (hgM ω))
  have glI : Integrable (fun ω => g ω * Real.log (g ω)) μ :=
    intOfBdd (hg.mul hg.log) _ (fun ω => glog_bdd hm (hgm ω) (hgM ω))
  have ghI : Integrable (fun ω => g ω * h ω) μ := intOfBdd (hg.mul hh) ((|m| + |M|) * K)
    (fun ω => by
      rw [abs_mul]
      exact mul_le_mul (abs_le_of_mem (hgm ω) (hgM ω)) (hK ω) (abs_nonneg _) (by positivity))
  have eI : Integrable (fun ω => Real.exp (h ω)) μ := intOfBdd hh.exp (Real.exp K) (fun ω => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hK ω)))
  have rI1 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log m0) μ :=
    glI.sub (gI.mul_const _)
  have rI2 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log m0 - g ω) μ := rI1.sub gI
  have rI : Integrable
      (fun ω => g ω * Real.log (g ω) - g ω * Real.log m0 - g ω + m0 * Real.exp (h ω)) μ :=
    rI2.add (eI.const_mul m0)
  have key := integral_mono ghI rI (fun ω => young_pt (h := h ω) (hgpos ω) hm0p)
  rw [integral_add rI2 (eI.const_mul m0), integral_sub rI1 gI, integral_sub glI (gI.mul_const _),
    integral_mul_const, integral_const_mul, hexp] at key
  unfold ent
  linarith

/-- Variational upper bound: `Ent(g) ≤ E[g log g - g log c - g + c]` for a constant `c > 0`. -/
lemma ent_le_var (μ : Measure Ω) [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Measurable g)
    {m M : ℝ} (hm : 0 < m) (hgm : ∀ ω, m ≤ g ω) (hgM : ∀ ω, g ω ≤ M) {c : ℝ} (hc : 0 < c) :
    ent μ g ≤ ∫ ω, (g ω * Real.log (g ω) - g ω * Real.log c - g ω + c) ∂μ := by
  obtain ⟨hm0, -⟩ := integral_mem_of (μ := μ) hg hgm hgM
  set m0 := ∫ ω, g ω ∂μ with hm0def
  have hm0p : 0 < m0 := lt_of_lt_of_le hm hm0
  have gI : Integrable g μ := intOfBdd hg (|m| + |M|) (fun ω => abs_le_of_mem (hgm ω) (hgM ω))
  have glI : Integrable (fun ω => g ω * Real.log (g ω)) μ :=
    intOfBdd (hg.mul hg.log) _ (fun ω => glog_bdd hm (hgm ω) (hgM ω))
  have rI1 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log c) μ :=
    glI.sub (gI.mul_const _)
  have rI2 : Integrable (fun ω => g ω * Real.log (g ω) - g ω * Real.log c - g ω) μ := rI1.sub gI
  rw [integral_add rI2 (integrable_const c), integral_sub rI1 gI,
    integral_sub glI (gI.mul_const _), integral_mul_const]
  have hcI : ∫ _ω, c ∂μ = c := by simp
  rw [hcI]
  unfold ent
  have hl := Real.log_le_sub_one_of_pos (div_pos hc hm0p)
  rw [Real.log_div hc.ne' hm0p.ne'] at hl
  have hl2 : m0 * (Real.log c - Real.log m0) ≤ m0 * (c / m0 - 1) :=
    mul_le_mul_of_nonneg_left hl hm0p.le
  have e : m0 * (c / m0 - 1) = c - m0 := by field_simp
  rw [e] at hl2
  nlinarith

end General

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma ent_meas_right (ν : Measure β) [IsProbabilityMeasure ν] {F : α × β → ℝ}
    (hF : Measurable F) : Measurable (fun a => ent ν (fun b => F (a, b))) := by
  unfold ent
  have h1 : Measurable (fun a => ∫ b, F (a, b) * Real.log (F (a, b)) ∂ν) :=
    ((hF.mul hF.log).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have h2 : Measurable (fun a => ∫ b, F (a, b) ∂ν) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  exact h1.sub (h2.mul h2.log)

/-- Two-factor tensorization of entropy. -/
theorem ent_prod (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {g : α × β → ℝ} (hg : Measurable g)
    {m M : ℝ} (hm : 0 < m) (hgm : ∀ p, m ≤ g p) (hgM : ∀ p, g p ≤ M) :
    ent (μ.prod ν) g ≤ ∫ b, ent μ (fun a => g (a, b)) ∂ν + ∫ a, ent ν (fun b => g (a, b)) ∂μ := by
  set L := |Real.log m| + |Real.log M| with hL
  have hgl : Measurable (fun p => g p * Real.log (g p)) := hg.mul hg.log
  set G : β → ℝ := fun b => ∫ a, g (a, b) ∂μ with hGdef
  have hGmeas : Measurable G := (hg.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable
  have hGb : ∀ b, m ≤ G b ∧ G b ≤ M := fun b =>
    integral_mem_of (μ := μ) (hg.comp (measurable_id.prodMk measurable_const))
      (fun a => hgm _) (fun a => hgM _)
  have hGpos : ∀ b, 0 < G b := fun b => lt_of_lt_of_le hm (hGb b).1
  set Mt := ∫ b, G b ∂ν with hMtdef
  have hMt : m ≤ Mt ∧ Mt ≤ M :=
    integral_mem_of (μ := ν) hGmeas (fun b => (hGb b).1) (fun b => (hGb b).2)
  have hMtp : 0 < Mt := lt_of_lt_of_le hm hMt.1
  have gI : Integrable g (μ.prod ν) := intOfBdd hg _ (fun p => abs_le_of_mem (hgm p) (hgM p))
  have glI : Integrable (fun p => g p * Real.log (g p)) (μ.prod ν) :=
    intOfBdd hgl _ (fun p => glog_bdd hm (hgm p) (hgM p))
  have e1 : ∫ p, g p ∂(μ.prod ν) = Mt := integral_prod_symm g gI
  have e2 : ∫ p, g p * Real.log (g p) ∂(μ.prod ν) =
      ∫ b, ∫ a, g (a, b) * Real.log (g (a, b)) ∂μ ∂ν := integral_prod_symm _ glI
  set h : β → ℝ := fun b => Real.log (G b) - Real.log Mt with hhdef
  have hmeas : Measurable h := hGmeas.log.sub measurable_const
  have hK : ∀ b, |h b| ≤ 2 * L := fun b => by
    have a1 := abs_log_le hm (hGb b).1 (hGb b).2
    have a2 := abs_log_le hm hMt.1 hMt.2
    calc |h b| ≤ |Real.log (G b)| + |Real.log Mt| := abs_sub _ _
      _ ≤ 2 * L := by linarith
  have hexpb : ∀ b, Real.exp (h b) = G b / Mt := fun b => by
    simp only [h, Real.exp_sub, Real.exp_log (hGpos b), Real.exp_log hMtp]
  have hexp : ∫ b, Real.exp (h b) ∂ν = 1 := by
    simp_rw [hexpb]
    rw [integral_div]
    exact div_self hMtp.ne'
  have GI : Integrable G ν := intOfBdd hGmeas _ (fun b => abs_le_of_mem (hGb b).1 (hGb b).2)
  have GlI : Integrable (fun b => G b * Real.log (G b)) ν :=
    intOfBdd (hGmeas.mul hGmeas.log) _ (fun b => glog_bdd hm (hGb b).1 (hGb b).2)
  have e3 : ∫ b, G b * h b ∂ν = ∫ b, G b * Real.log (G b) ∂ν - Mt * Real.log Mt := by
    simp only [h, mul_sub]
    rw [integral_sub GlI (GI.mul_const _), integral_mul_const]
  have e4 : ∫ b, G b * h b ∂ν = ∫ b, ∫ a, g (a, b) * h b ∂μ ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [G]
    exact (integral_mul_const (h b) _).symm
  have swapI : Integrable (Function.uncurry fun (b : β) (a : α) => g (a, b) * h b) (ν.prod μ) := by
    refine intOfBdd ((hg.comp measurable_swap).mul (hmeas.comp measurable_fst)) ((|m| + |M|) * (2 * L))
      (fun p => ?_)
    simp only [Function.uncurry]
    rw [abs_mul]
    exact mul_le_mul (abs_le_of_mem (hgm _) (hgM _)) (hK _) (abs_nonneg _) (by positivity)
  have e5 : ∫ b, ∫ a, g (a, b) * h b ∂μ ∂ν = ∫ a, ∫ b, g (a, b) * h b ∂ν ∂μ :=
    integral_integral_swap swapI
  have I1 : Integrable (fun a => ∫ b, g (a, b) * h b ∂ν) μ := by
    refine intOfBdd ((hg.mul (hmeas.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := ν)).measurable ((|m| + |M|) * (2 * L)) (fun a => ?_)
    refine abs_integral_le_of (μ := ν) ((hg.comp (measurable_const.prodMk measurable_id)).mul hmeas)
      (fun b => ?_)
    show |g (a, b) * h b| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_le_of_mem (hgm _) (hgM _)) (hK _) (abs_nonneg _) (by positivity)
  have I2 : Integrable (fun a => ent ν (fun b => g (a, b))) μ :=
    intOfBdd (ent_meas_right ν hg) _ (fun a => ent_abs_le ν (hg.comp
      (measurable_const.prodMk measurable_id)) hm (fun b => hgm _) (fun b => hgM _))
  have e6 : ∫ a, ∫ b, g (a, b) * h b ∂ν ∂μ ≤ ∫ a, ent ν (fun b => g (a, b)) ∂μ :=
    integral_mono I1 I2 (fun a => gibbs ν (hg.comp (measurable_const.prodMk measurable_id)) hmeas
      hm (fun b => hgm _) (fun b => hgM _) hK hexp)
  have J1 : Integrable (fun b => ∫ a, g (a, b) * Real.log (g (a, b)) ∂μ) ν :=
    intOfBdd (hgl.stronglyMeasurable.integral_prod_left' (μ := μ)).measurable _
      (fun b => abs_integral_le_of (μ := μ) (hgl.comp (measurable_id.prodMk measurable_const))
        (fun a => glog_bdd hm (hgm _) (hgM _)))
  have e7 : ∫ b, ent μ (fun a => g (a, b)) ∂ν =
      ∫ b, ∫ a, g (a, b) * Real.log (g (a, b)) ∂μ ∂ν - ∫ b, G b * Real.log (G b) ∂ν := by
    unfold ent
    exact integral_sub J1 GlI
  have hent : ent (μ.prod ν) g = ∫ p, g p * Real.log (g p) ∂(μ.prod ν) - Mt * Real.log Mt := by
    unfold ent; rw [e1]
  rw [hent, e2]
  linarith

end Prod

section Pi

variable {X : Type*} [MeasurableSpace X]

lemma esymm_update0 {n : ℕ} (p : X × (Fin n → X)) (y : X) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm p) 0 y =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm (y, p.2) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma esymm_update_succ {n : ℕ} (p : X × (Fin n → X)) (j : Fin n) (y : X) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm p) j.succ y =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm
        (p.1, Function.update p.2 j y) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma esymm_update_k {n : ℕ} (k : Fin (n + 1)) (p : X × (Fin n → X)) (y : X) :
    Function.update ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k).symm p) k y =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k).symm (y, p.2) := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma esymm_update0' {n : ℕ} (e : (Fin (n + 1) → X) ≃ᵐ X × (Fin n → X))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0)
    (p : X × (Fin n → X)) (y : X) : Function.update (e.symm p) 0 y = e.symm (y, p.2) := by
  subst he; exact esymm_update0 p y

lemma esymm_update_succ' {n : ℕ} (e : (Fin (n + 1) → X) ≃ᵐ X × (Fin n → X))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0)
    (p : X × (Fin n → X)) (j : Fin n) (y : X) :
    Function.update (e.symm p) j.succ y = e.symm (p.1, Function.update p.2 j y) := by
  subst he; exact esymm_update_succ p j y

lemma esymm_update_k' {n : ℕ} (k : Fin (n + 1)) (e : (Fin (n + 1) → X) ≃ᵐ X × (Fin n → X))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k)
    (p : X × (Fin n → X)) (y : X) : Function.update (e.symm p) k y = e.symm (y, p.2) := by
  subst he; exact esymm_update_k k p y

/-- Resampling one coordinate leaves the product measure invariant. -/
theorem resample (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) (k : Fin n)
    {F : (Fin n → X) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ s, |F s| ≤ C) :
    ∫ s, (∫ y, F (Function.update s k y) ∂P) ∂(Measure.pi fun _ : Fin n => P) =
      ∫ s, F s ∂(Measure.pi fun _ : Fin n => P) := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k with he
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => P)
      (P.prod (Measure.pi fun _ : Fin n => P)) := measurePreserving_piFinSuccAbove (fun _ => P) k
  have a1 := hmp.symm.integral_comp' (fun s => ∫ y, F (Function.update s k y) ∂P)
  have a2 := hmp.symm.integral_comp' F
  rw [← a1, ← a2]
  simp_rw [esymm_update_k' k e he]
  have hF' : Measurable (fun q : (X × (Fin n → X)) × X => F (e.symm (q.2, q.1.2))) :=
    hF.comp (e.symm.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have I1 : Integrable (fun p : X × (Fin n → X) => ∫ y, F (e.symm (y, p.2)) ∂P)
      (P.prod (Measure.pi fun _ : Fin n => P)) :=
    intOfBdd (hF'.stronglyMeasurable.integral_prod_right' (ν := P)).measurable C
      (fun p => abs_integral_le_of (μ := P)
        (hF.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))) (fun y => hC _))
  have I2 : Integrable (fun p : X × (Fin n → X) => F (e.symm p))
      (P.prod (Measure.pi fun _ : Fin n => P)) := intOfBdd (hF.comp e.symm.measurable) C (fun p => hC _)
  rw [integral_prod_symm _ I1, integral_prod_symm _ I2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [integral_const, probReal_univ, one_smul]

/-- Tensorization of entropy for `Pⁿ`. -/
theorem tens (P : Measure X) [IsProbabilityMeasure P] :
    ∀ (n : ℕ) (g : (Fin n → X) → ℝ), Measurable g → ∀ (m M : ℝ), 0 < m → (∀ s, m ≤ g s) →
      (∀ s, g s ≤ M) →
      ent (Measure.pi fun _ : Fin n => P) g ≤
        ∑ k : Fin n, ∫ s, ent P (fun x => g (Function.update s k x))
          ∂(Measure.pi fun _ : Fin n => P) := by
  intro n
  induction n with
  | zero =>
    intro g hg m M hm hgm hgM
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have hc : ∀ s : Fin 0 → X, g s = g (fun i => i.elim0) := fun s => by
      congr 1; funext i; exact i.elim0
    have hconst : ∀ (φ : ℝ → ℝ), ∫ s, φ (g s) ∂(Measure.pi fun _ : Fin 0 => P) =
        φ (g (fun i => i.elim0)) := by
      intro φ; simp_rw [hc]; simp
    have h1 := hconst (fun x => x * Real.log x)
    have h2 := hconst id
    simp only [id] at h2
    unfold ent
    rw [h1, h2]; simp
  | succ n ih =>
    intro g hg m M hm hgm hgM
    set L := |Real.log m| + |Real.log M| with hL
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0 with he
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => P)
        (P.prod (Measure.pi fun _ : Fin n => P)) :=
      measurePreserving_piFinSuccAbove (fun _ => P) 0
    set g' : X × (Fin n → X) → ℝ := fun p => g (e.symm p) with hg'def
    have hg' : Measurable g' := hg.comp e.symm.measurable
    have hent : ent (Measure.pi fun _ : Fin (n + 1) => P) g =
        ent (P.prod (Measure.pi fun _ : Fin n => P)) g' := by
      unfold ent
      have a1 := hmp.symm.integral_comp' (fun s => g s * Real.log (g s))
      have a2 := hmp.symm.integral_comp' g
      rw [← a1, ← a2]
    rw [hent]
    have step := ent_prod P (Measure.pi fun _ : Fin n => P) hg' hm (fun p => hgm _)
      (fun p => hgM _)
    refine le_trans step ?_
    rw [Fin.sum_univ_succ]
    -- coordinate 0
    have F0 : Measurable (fun q : (X × (Fin n → X)) × X => g' (q.2, q.1.2)) :=
      hg'.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have t0 : ∫ s, ent P (fun x => g (Function.update s 0 x)) ∂(Measure.pi fun _ => P) =
        ∫ b, ent P (fun a => g' (a, b)) ∂(Measure.pi fun _ : Fin n => P) := by
      have a := hmp.symm.integral_comp' (fun s => ent P (fun x => g (Function.update s 0 x)))
      rw [← a]
      simp_rw [esymm_update0' e he]
      have I : Integrable (fun p : X × (Fin n → X) => ent P (fun y => g' (y, p.2)))
          (P.prod (Measure.pi fun _ : Fin n => P)) :=
        intOfBdd (ent_meas_right P F0) _ (fun p => ent_abs_le P
          (hg'.comp (measurable_id.prodMk measurable_const)) hm (fun y => hgm _) (fun y => hgM _))
      rw [integral_prod_symm _ I]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [integral_const, probReal_univ, one_smul]
    -- coordinates succ j
    have ts : ∀ j : Fin n,
        ∫ s, ent P (fun x => g (Function.update s j.succ x)) ∂(Measure.pi fun _ => P) =
          ∫ a, ∫ t, ent P (fun y => g' (a, Function.update t j y))
            ∂(Measure.pi fun _ : Fin n => P) ∂P := by
      intro j
      have a := hmp.symm.integral_comp' (fun s => ent P (fun x => g (Function.update s j.succ x)))
      rw [← a]
      simp_rw [esymm_update_succ' e he]
      have Fj : Measurable (fun q : (X × (Fin n → X)) × X =>
          g' (q.1.1, Function.update q.1.2 j q.2)) :=
        hg'.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      have I : Integrable (fun p : X × (Fin n → X) => ent P (fun y => g' (p.1, Function.update p.2 j y)))
          (P.prod (Measure.pi fun _ : Fin n => P)) :=
        intOfBdd (ent_meas_right P Fj) _ (fun p => ent_abs_le P
          (Fj.comp (measurable_const.prodMk measurable_id)) hm (fun y => hgm _) (fun y => hgM _))
      rw [integral_prod _ I]
    rw [t0]
    simp_rw [ts]
    have Ij : ∀ j : Fin n, Integrable
        (fun a => ∫ t, ent P (fun y => g' (a, Function.update t j y))
          ∂(Measure.pi fun _ : Fin n => P)) P := by
      intro j
      have Fj : Measurable (fun q : (X × (Fin n → X)) × X =>
          g' (q.1.1, Function.update q.1.2 j q.2)) :=
        hg'.comp ((measurable_fst.comp measurable_fst).prodMk
          (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
      refine intOfBdd ((ent_meas_right P Fj).stronglyMeasurable.integral_prod_right'
        (ν := Measure.pi fun _ : Fin n => P)).measurable (2 * (M * L)) (fun a => ?_)
      exact abs_integral_le_of (ent_meas_right P Fj |>.comp (measurable_const.prodMk measurable_id))
        (fun t => ent_abs_le P (Fj.comp (measurable_const.prodMk measurable_id)) hm
          (fun y => hgm _) (fun y => hgM _))
    rw [← integral_finsetSum _ (fun j _ => Ij j)]
    apply add_le_add le_rfl
    apply integral_mono
      (intOfBdd (ent_meas_right _ hg') _ (fun a => ent_abs_le _
        (hg'.comp (measurable_const.prodMk measurable_id)) hm (fun y => hgm _) (fun y => hgM _)))
      (integrable_finset_sum _ (fun j _ => Ij j))
    intro a
    exact ih (fun t => g' (a, t)) (hg'.comp (measurable_const.prodMk measurable_id)) m M hm
      (fun t => hgm _) (fun t => hgM _)

end Pi



/-! ### Core: modified log-Sobolev + Herbst for a convex-Lipschitz-type function -/

lemma phi_le (y : ℝ) (hy : 0 ≤ y) : Real.exp (-y) + y - 1 ≤ y ^ 2 / 2 := by
  have hmono : Monotone (fun y : ℝ => y ^ 2 / 2 - (Real.exp (-y) + y - 1)) := by
    apply monotone_of_deriv_nonneg
    · fun_prop
    · intro x
      have h : HasDerivAt (fun y : ℝ => y ^ 2 / 2 - (Real.exp (-y) + y - 1))
          (x + Real.exp (-x) - 1) x := by
        have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
          have := (hasDerivAt_pow 2 x).div_const 2
          refine this.congr_deriv ?_
          simp
        have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
          have := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
          refine this.congr_deriv ?_
          simp
        have h3 := ((h2.add (hasDerivAt_id x)).sub_const 1)
        have h4 := h1.sub h3
        refine h4.congr_deriv ?_
        ring
      rw [h.deriv]
      linarith [Real.add_one_le_exp (-x)]
  have := hmono hy
  simp at this
  linarith

section Core

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}

noncomputable def Wd (Z : (Fin n → X) → ℝ) (Zk : Fin n → (Fin n → X) → ℝ) (l : ℝ) (k : Fin n)
    (s : Fin n → X) : ℝ :=
  Real.exp (l * Z s) * (l * (Z s - Zk k s) - 1) + Real.exp (l * Zk k s)

structure Hyp (Z : (Fin n → X) → ℝ) (Zk : Fin n → (Fin n → X) → ℝ) (B : ℝ) : Prop where
  B0 : 0 ≤ B
  mZ : Measurable Z
  mZk : ∀ k, Measurable (Zk k)
  Z0 : ∀ s, 0 ≤ Z s
  ZB : ∀ s, Z s ≤ B
  Zk0 : ∀ k s, 0 ≤ Zk k s
  ZkZ : ∀ k s, Zk k s ≤ Z s
  ind : ∀ k s y, Zk k (Function.update s k y) = Zk k s

lemma W_abs (a b y E L : ℝ) (ha1 : 1 ≤ a) (haE : a ≤ E) (hb1 : 1 ≤ b) (hbE : b ≤ E)
    (hy0 : 0 ≤ y) (hyL : y ≤ L) : |a * (y - 1) + b| ≤ E * (L + 2) := by
  have hE : 0 ≤ E := by linarith
  have hL : 0 ≤ L := by linarith
  have h1 : a * y ≤ E * L := mul_le_mul haE hyL hy0 hE
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg hE hL]

variable {Z : (Fin n → X) → ℝ} {Zk : Fin n → (Fin n → X) → ℝ} {B : ℝ}

lemma Wd_meas (H : Hyp Z Zk B) (l : ℝ) (k : Fin n) : Measurable (Wd Z Zk l k) := by
  unfold Wd
  have a := H.mZ.const_mul l
  exact (a.exp.mul (((H.mZ.sub (H.mZk k)).const_mul l).sub_const 1)).add
    ((H.mZk k).const_mul l).exp

lemma Wd_bdd (H : Hyp Z Zk B) (l : ℝ) (hl : 0 ≤ l) (k : Fin n) (s : Fin n → X) :
    |Wd Z Zk l k s| ≤ Real.exp (l * B) * (l * B + 2) := by
  unfold Wd
  have hZ := H.Z0 s
  have hZB := H.ZB s
  have hk0 := H.Zk0 k s
  have hkZ := H.ZkZ k s
  apply W_abs
  · exact Real.one_le_exp (mul_nonneg hl hZ)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hZB hl)
  · exact Real.one_le_exp (mul_nonneg hl hk0)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hkZ.trans hZB) hl)
  · exact mul_nonneg hl (sub_nonneg.mpr hkZ)
  · exact mul_le_mul_of_nonneg_left (by linarith) hl

theorem ent_le_sumW (H : Hyp Z Zk B) (l : ℝ) (hl : 0 ≤ l) :
    ent (Measure.pi fun _ : Fin n => P) (fun s => Real.exp (l * Z s)) ≤
      ∑ k, ∫ s, Wd Z Zk l k s ∂(Measure.pi fun _ : Fin n => P) := by
  set E : ℝ := Real.exp (l * B) with hE
  have glo : ∀ s, 1 ≤ Real.exp (l * Z s) := fun s => Real.one_le_exp (mul_nonneg hl (H.Z0 s))
  have ghi : ∀ s, Real.exp (l * Z s) ≤ E := fun s =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (H.ZB s) hl)
  have gmeas : Measurable (fun s => Real.exp (l * Z s)) := (H.mZ.const_mul l).exp
  have T := tens P n (fun s => Real.exp (l * Z s)) gmeas 1 E one_pos glo ghi
  refine le_trans T (Finset.sum_le_sum fun k _ => ?_)
  have Wmeas := Wd_meas H l k
  have Wbd := Wd_bdd H l hl k
  refine le_trans ?_ (le_of_eq (resample P n k Wmeas Wbd))
  have upd_meas : Measurable (fun q : (Fin n → X) × X => Function.update q.1 k q.2) :=
    measurable_update'
  have F1 : Measurable (fun q : (Fin n → X) × X => Real.exp (l * Z (Function.update q.1 k q.2))) :=
    ((H.mZ.comp upd_meas).const_mul l).exp
  have I1 : Integrable (fun s => ent P (fun x => Real.exp (l * Z (Function.update s k x))))
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd (ent_meas_right P F1) _ (fun s => ent_abs_le P
      (F1.comp (measurable_const.prodMk measurable_id)) one_pos (fun x => glo _) (fun x => ghi _))
  have I2 : Integrable (fun s => ∫ x, Wd Z Zk l k (Function.update s k x) ∂P)
      (Measure.pi fun _ : Fin n => P) :=
    intOfBdd ((Wmeas.comp upd_meas).stronglyMeasurable.integral_prod_right' (ν := P)).measurable _
      (fun s => abs_integral_le_of (Wmeas.comp (measurable_update s)) (fun x => Wbd _))
  apply integral_mono I1 I2
  intro s
  show ent P (fun x => Real.exp (l * Z (Function.update s k x))) ≤
    ∫ x, Wd Z Zk l k (Function.update s k x) ∂P
  have gm : Measurable (fun x => Real.exp (l * Z (Function.update s k x))) :=
    ((H.mZ.comp (measurable_update s)).const_mul l).exp
  have hv := ent_le_var P gm one_pos (fun x => glo _) (fun x => ghi _)
    (Real.exp_pos (l * Zk k s))
  have heq : ∀ x, Real.exp (l * Z (Function.update s k x)) *
        Real.log (Real.exp (l * Z (Function.update s k x))) -
      Real.exp (l * Z (Function.update s k x)) * Real.log (Real.exp (l * Zk k s)) -
      Real.exp (l * Z (Function.update s k x)) + Real.exp (l * Zk k s) =
      Wd Z Zk l k (Function.update s k x) := by
    intro x
    rw [Real.log_exp, Real.log_exp]
    unfold Wd
    rw [H.ind]; ring
  simp only [heq] at hv
  exact hv

lemma Wd_le (l : ℝ) (hl : 0 ≤ l) (k : Fin n) (s : Fin n → X) (hkZ : Zk k s ≤ Z s) :
    Wd Z Zk l k s ≤ Real.exp (l * Z s) * (l ^ 2 * (Z s - Zk k s) ^ 2 / 2) := by
  unfold Wd
  set y := l * (Z s - Zk k s) with hy
  have hy0 : 0 ≤ y := mul_nonneg hl (sub_nonneg.mpr hkZ)
  have hp := phi_le y hy0
  have he : Real.exp (l * Zk k s) = Real.exp (l * Z s) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; rw [hy]; ring
  rw [he]
  have hpos := Real.exp_pos (l * Z s)
  have : l ^ 2 * (Z s - Zk k s) ^ 2 / 2 = y ^ 2 / 2 := by rw [hy]; ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hp hpos.le]

/-- Entropy bound: `Ent(e^{lZ}) ≤ (l² σ² / 2) E e^{lZ}`. -/
theorem ent_bound (H : Hyp Z Zk B) (σ2 : ℝ) (hsum : ∀ s, ∑ k, (Z s - Zk k s) ^ 2 ≤ σ2)
    (l : ℝ) (hl : 0 ≤ l) :
    ent (Measure.pi fun _ : Fin n => P) (fun s => Real.exp (l * Z s)) ≤
      (l ^ 2 * σ2 / 2) * ∫ s, Real.exp (l * Z s) ∂(Measure.pi fun _ : Fin n => P) := by
  set μ := Measure.pi fun _ : Fin n => P with hμ
  have S1 := ent_le_sumW P H l hl
  have WI : ∀ k, Integrable (Wd Z Zk l k) μ := fun k =>
    intOfBdd (Wd_meas H l k) _ (Wd_bdd H l hl k)
  have mF : Measurable (fun s => Real.exp (l * Z s)) := (H.mZ.const_mul l).exp
  have EI : Integrable (fun s => Real.exp (l * Z s)) μ :=
    intOfBdd mF (Real.exp (l * B)) (fun s => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (H.ZB s) hl))
  refine le_trans S1 ?_
  rw [← integral_finsetSum _ (fun k _ => WI k)]
  have : (l ^ 2 * σ2 / 2) * ∫ s, Real.exp (l * Z s) ∂μ =
      ∫ s, (l ^ 2 * σ2 / 2) * Real.exp (l * Z s) ∂μ := by rw [integral_const_mul]
  rw [this]
  apply integral_mono (integrable_finsetSum _ (fun k _ => WI k)) (EI.const_mul _)
  intro s
  have h1 : ∑ k, Wd Z Zk l k s ≤ ∑ k, Real.exp (l * Z s) * (l ^ 2 * (Z s - Zk k s) ^ 2 / 2) :=
    Finset.sum_le_sum (fun k _ => Wd_le l hl k s (H.ZkZ k s))
  have h2 : ∑ k, Real.exp (l * Z s) * (l ^ 2 * (Z s - Zk k s) ^ 2 / 2) =
      Real.exp (l * Z s) * (l ^ 2 / 2 * ∑ k, (Z s - Zk k s) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have h3 : l ^ 2 / 2 * ∑ k, (Z s - Zk k s) ^ 2 ≤ l ^ 2 / 2 * σ2 :=
    mul_le_mul_of_nonneg_left (hsum s) (by positivity)
  have hpos := Real.exp_pos (l * Z s)
  calc ∑ k, Wd Z Zk l k s ≤ _ := h1
    _ = _ := h2
    _ ≤ Real.exp (l * Z s) * (l ^ 2 / 2 * σ2) := mul_le_mul_of_nonneg_left h3 hpos.le
    _ = _ := by ring

end Core

/-- Herbst-type comparison: `l G' - G ≤ v l²`, `G 0 = 0`, `G' 0 = 0` gives `G ≤ v l²`. -/
theorem herbst_ode (G G' : ℝ → ℝ) (v : ℝ) (hG0 : G 0 = 0)
    (hd : ∀ l, 0 ≤ l → HasDerivAt G (G' l) l) (hG'0 : G' 0 = 0)
    (hineq : ∀ l, 0 < l → l * G' l - G l ≤ l ^ 2 * v) :
    ∀ l, 0 ≤ l → G l ≤ v * l ^ 2 := by
  intro l hl0
  rcases eq_or_lt_of_le hl0 with h | hpos
  · subst h; simp [hG0]
  set Q : ℝ → ℝ := fun x => G x / x - v * x with hQ
  have hQd : ∀ x, 0 < x → HasDerivAt Q ((G' x * x - G x) / x ^ 2 - v) x := by
    intro x hx
    have h1 := (hd x hx.le).div (hasDerivAt_id x) hx.ne'
    have h2 := h1.sub ((hasDerivAt_id x).const_mul v)
    refine h2.congr_deriv ?_
    simp only [id]; ring
  have hanti : AntitoneOn Q (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx; exact (hQd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hQd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(hQd x hx).deriv]
      have hx' : 0 < x := hx
      have := hineq x hx'
      have hx2 : 0 < x ^ 2 := by positivity
      have : (G' x * x - G x) / x ^ 2 ≤ v := by
        rw [div_le_iff₀ hx2]; nlinarith
      linarith
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (G (0 + t) - G 0)) (𝓝[>] 0) (𝓝 (G' 0)) :=
    (hd 0 le_rfl).tendsto_slope_zero_right
  simp only [zero_add, hG0, sub_zero, smul_eq_mul, hG'0] at hslope
  have hv : Tendsto (fun t : ℝ => v * t) (𝓝[>] 0) (𝓝 (v * 0)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact (continuousAt_const.mul continuousAt_id).tendsto
  have hlim : Tendsto (fun t => t⁻¹ * G t - v * t) (𝓝[>] 0) (𝓝 0) := by
    have := hslope.sub hv
    simpa using this
  have hQlim : Tendsto Q (𝓝[>] 0) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [hQ]; rw [div_eq_inv_mul]
  have hQl : Q l ≤ 0 := by
    refine ge_of_tendsto hQlim ?_
    filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
    exact hanti ht.1 hpos ht.2.le
  have : G l / l ≤ v * l := by simp only [hQ] at hQl; linarith
  rw [div_le_iff₀ hpos] at this
  nlinarith


section Tail

variable {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] {n : ℕ}
  {Z : (Fin n → X) → ℝ} {Zk : Fin n → (Fin n → X) → ℝ} {B : ℝ}

theorem tail_core (H : Hyp Z Zk B) (σ2 : ℝ) (hσ : 0 < σ2)
    (hsum : ∀ s, ∑ k, (Z s - Zk k s) ^ 2 ≤ σ2) (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => P).real
      {s | (∫ s, Z s ∂(Measure.pi fun _ : Fin n => P)) + t ≤ Z s} ≤
        Real.exp (-(t ^ 2 / (2 * σ2))) := by
  set μ := Measure.pi fun _ : Fin n => P with hμ
  set m := ∫ s, Z s ∂μ with hmdef
  have mZ := H.mZ
  have hZb : ∀ s, |Z s| ≤ B := fun s => by rw [abs_of_nonneg (H.Z0 s)]; exact H.ZB s
  have hint : ∀ l : ℝ, Integrable (fun s => Real.exp (l * Z s)) μ := by
    intro l
    refine intOfBdd (mZ.const_mul l).exp (Real.exp (|l| * B)) (fun s => ?_)
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc l * Z s ≤ |l * Z s| := le_abs_self _
      _ = |l| * |Z s| := abs_mul _ _
      _ ≤ |l| * B := mul_le_mul_of_nonneg_left (hZb s) (abs_nonneg _)
  have hset : integrableExpSet Z μ = Set.univ := by
    ext l; simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact hint l
  set F : ℝ → ℝ := fun l => mgf Z μ l with hFdef
  set F1 : ℝ → ℝ := fun l => ∫ s, Z s * Real.exp (l * Z s) ∂μ with hF1def
  have hFd : ∀ l, HasDerivAt F (F1 l) l := by
    intro l
    have := hasDerivAt_mgf (X := Z) (μ := μ) (t := l) (by rw [hset]; simp)
    exact this
  have hFpos : ∀ l, 0 < F l := fun l => mgf_pos (hint l)
  have hF0 : F 0 = 1 := by simp [hFdef, mgf_zero]
  have hF10 : F1 0 = m := by simp [hF1def, hmdef]
  set G : ℝ → ℝ := fun l => Real.log (F l) - l * m with hGdef
  set G' : ℝ → ℝ := fun l => F1 l / F l - m with hG'def
  have hd : ∀ l, 0 ≤ l → HasDerivAt G (G' l) l := by
    intro l _
    have := ((hFd l).log (hFpos l).ne').sub ((hasDerivAt_id l).mul_const m)
    refine this.congr_deriv ?_
    simp [hG'def]
  have hG0 : G 0 = 0 := by simp [hGdef, hF0]
  have hG'0 : G' 0 = 0 := by simp [hG'def, hF0, hF10]
  have hineq : ∀ l, 0 < l → l * G' l - G l ≤ l ^ 2 * (σ2 / 2) := by
    intro l hl0
    have key := ent_bound P H σ2 hsum l hl0.le
    have hent : ent μ (fun s => Real.exp (l * Z s)) = l * F1 l - F l * Real.log (F l) := by
      unfold ent
      simp only [Real.log_exp, hF1def, hFdef, mgf]
      rw [← integral_const_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only; ring
    rw [hent] at key
    have r2 : ∫ s, Real.exp (l * Z s) ∂μ = F l := rfl
    rw [r2] at key
    have hFp := hFpos l
    have e : l * G' l - G l = (l * F1 l - F l * Real.log (F l)) / F l := by
      simp only [hG'def, hGdef]
      field_simp
      ring
    rw [e, div_le_iff₀ hFp]
    nlinarith
  have hode := herbst_ode G G' (σ2 / 2) hG0 hd hG'0 hineq
  set l := t / σ2 with hl
  have hl0 : 0 ≤ l := div_nonneg ht hσ.le
  have hch := measure_ge_le_exp_mul_mgf (X := Z) (μ := μ) (m + t) hl0 (hint l)
  have hGl := hode l hl0
  have hFl : F l = Real.exp (G l + l * m) := by
    simp only [hGdef]; rw [sub_add_cancel, Real.exp_log (hFpos l)]
  calc μ.real {s | m + t ≤ Z s}
      ≤ Real.exp (-l * (m + t)) * F l := hch
    _ = Real.exp (G l - l * t) := by
        rw [hFl, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (σ2 / 2 * l ^ 2 - l * t) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = Real.exp (-(t ^ 2 / (2 * σ2))) := by
        congr 1
        rw [hl]
        field_simp
        ring

end Tail


/-! ### The sample standard deviation as a convex-Lipschitz-type function -/
section Inst

lemma sqrt_ineq (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    a * (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 := by
  have ha : 0 ≤ a := hb.trans hba
  have hp := Real.sq_sqrt ha
  have hq := Real.sq_sqrt hb
  have hqp : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
  have hq0 := Real.sqrt_nonneg b
  set p := Real.sqrt a
  set q := Real.sqrt b
  have : a - b = (p - q) * (p + q) := by rw [← hp, ← hq]; ring
  rw [this, ← hp]
  have h1 : 0 ≤ (2 * p * q + q ^ 2) * (p - q) ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _); nlinarith
  nlinarith

lemma alg_delta (N x R1 R2 : ℝ) (hN : N - 1 ≠ 0) (hN0 : N ≠ 0) :
    (R2 + x ^ 2 - (R1 + x) ^ 2 / N) - (R2 - R1 ^ 2 / (N - 1)) =
      (N - 1) / N * (x - R1 / (N - 1)) ^ 2 := by
  field_simp
  ring

variable (M0 M1 : ℝ) (n : ℕ)

noncomputable def cl (x : ℝ) : ℝ := max M0 (min M1 x)

lemma cl_mem (h : M0 ≤ M1) (x : ℝ) : cl M0 M1 x ∈ Set.Icc M0 M1 := by
  unfold cl
  constructor
  · exact le_max_left _ _
  · exact max_le h (min_le_left _ _)

lemma cl_id (x : ℝ) (hx : x ∈ Set.Icc M0 M1) : cl M0 M1 x = x := by
  unfold cl
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma cl_meas : Measurable (cl M0 M1) := by
  unfold cl
  exact measurable_const.max (measurable_const.min measurable_id)

noncomputable def T1 (s : Fin n → ℝ) : ℝ := ∑ i, cl M0 M1 (s i)
noncomputable def Q1 (s : Fin n → ℝ) : ℝ := ∑ i, cl M0 M1 (s i) ^ 2
noncomputable def Dd (s : Fin n → ℝ) : ℝ := Q1 M0 M1 n s - T1 M0 M1 n s ^ 2 / n
noncomputable def Zs (s : Fin n → ℝ) : ℝ := Real.sqrt (Dd M0 M1 n s / n)
noncomputable def R1 (k : Fin n) (s : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase k, cl M0 M1 (s j)
noncomputable def R2 (k : Fin n) (s : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase k, cl M0 M1 (s j) ^ 2
noncomputable def Dk (k : Fin n) (s : Fin n → ℝ) : ℝ :=
  R2 M0 M1 n k s - R1 M0 M1 n k s ^ 2 / ((n : ℝ) - 1)
noncomputable def Zks (k : Fin n) (s : Fin n → ℝ) : ℝ := Real.sqrt (Dk M0 M1 n k s / n)

lemma T1_eq (k : Fin n) (s : Fin n → ℝ) :
    T1 M0 M1 n s = R1 M0 M1 n k s + cl M0 M1 (s k) := by
  unfold T1 R1
  rw [add_comm]
  exact (Finset.add_sum_erase Finset.univ (fun j => cl M0 M1 (s j)) (Finset.mem_univ k)).symm

lemma Q1_eq (k : Fin n) (s : Fin n → ℝ) :
    Q1 M0 M1 n s = R2 M0 M1 n k s + cl M0 M1 (s k) ^ 2 := by
  unfold Q1 R2
  rw [add_comm]
  exact (Finset.add_sum_erase Finset.univ (fun j => cl M0 M1 (s j) ^ 2) (Finset.mem_univ k)).symm

variable {M0 M1 n}

lemma R1_bounds (hM : M0 ≤ M1) (k : Fin n) (s : Fin n → ℝ) :
    ((n : ℝ) - 1) * M0 ≤ R1 M0 M1 n k s ∧ R1 M0 M1 n k s ≤ ((n : ℝ) - 1) * M1 := by
  have hc : ((Finset.univ.erase k).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp only [Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Fin.pos k
    push_cast [this]; ring
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.univ.erase k) (fun j => cl M0 M1 (s j)) M0
      (fun j _ => (cl_mem M0 M1 hM (s j)).1)
    rw [nsmul_eq_mul, hc] at this
    exact this
  · have := Finset.sum_le_card_nsmul (Finset.univ.erase k) (fun j => cl M0 M1 (s j)) M1
      (fun j _ => (cl_mem M0 M1 hM (s j)).2)
    rw [nsmul_eq_mul, hc] at this
    exact this

lemma c_mem (hM : M0 ≤ M1) (hn : 2 ≤ n) (k : Fin n) (s : Fin n → ℝ) :
    R1 M0 M1 n k s / ((n : ℝ) - 1) ∈ Set.Icc M0 M1 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) - 1 := by linarith
  obtain ⟨h1, h2⟩ := R1_bounds hM k s
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

lemma Dk_nonneg (hn : 2 ≤ n) (k : Fin n) (s : Fin n → ℝ) : 0 ≤ Dk M0 M1 n k s := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) - 1 := by linarith
  have hc : ((Finset.univ.erase k).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp only [Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Fin.pos k
    push_cast [this]; ring
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase k) (f := fun j => cl M0 M1 (s j))
  unfold Dk R1 R2
  rw [hc] at this
  rw [sub_nonneg, div_le_iff₀ hpos]
  linarith

lemma Dd_nonneg (hn : 0 < n) (s : Fin n → ℝ) : 0 ≤ Dd M0 M1 n s := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => cl M0 M1 (s j))
  simp only [Finset.card_univ, Fintype.card_fin] at this
  unfold Dd T1 Q1
  rw [sub_nonneg, div_le_iff₀ hn']
  linarith

/-- The drop of `Dd` when coordinate `k` is replaced by the mean of the others. -/
lemma delta_eq (hn : 2 ≤ n) (k : Fin n) (s : Fin n → ℝ) :
    Dd M0 M1 n s - Dk M0 M1 n k s =
      ((n : ℝ) - 1) / n * (cl M0 M1 (s k) - R1 M0 M1 n k s / ((n : ℝ) - 1)) ^ 2 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (n : ℝ) ≠ 0 := by linarith
  have := alg_delta (n : ℝ) (cl M0 M1 (s k)) (R1 M0 M1 n k s) (R2 M0 M1 n k s) h1 h0
  unfold Dd Dk
  rw [T1_eq M0 M1 n k s, Q1_eq M0 M1 n k s]
  exact this

lemma sum_sq_eq (hn : 0 < n) (s : Fin n → ℝ) :
    ∑ k, (cl M0 M1 (s k) - T1 M0 M1 n s / n) ^ 2 = Dd M0 M1 n s := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Dd
  have e : ∀ k, (cl M0 M1 (s k) - T1 M0 M1 n s / n) ^ 2 =
      cl M0 M1 (s k) ^ 2 - 2 * (T1 M0 M1 n s / n) * cl M0 M1 (s k) + (T1 M0 M1 n s / n) ^ 2 := by
    intro k; ring
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∑ i, cl M0 M1 (s i) = T1 M0 M1 n s := rfl
  rw [this]
  unfold Q1
  field_simp
  ring

end Inst


section Inst2

variable {M0 M1 : ℝ} {n : ℕ}

lemma Zs_meas : Measurable (Zs M0 M1 n) := by
  unfold Zs Dd T1 Q1
  have hc := cl_meas M0 M1
  have hT : Measurable fun s : Fin n → ℝ => ∑ i, cl M0 M1 (s i) :=
    Finset.measurable_sum _ (fun i _ => hc.comp (measurable_pi_apply i))
  have hQ : Measurable fun s : Fin n → ℝ => ∑ i, cl M0 M1 (s i) ^ 2 :=
    Finset.measurable_sum _ (fun i _ => (hc.comp (measurable_pi_apply i)).pow_const 2)
  exact Real.continuous_sqrt.measurable.comp (((hQ.sub ((hT.pow_const 2).div_const _))).div_const _)

lemma Zks_meas (k : Fin n) : Measurable (Zks M0 M1 n k) := by
  unfold Zks Dk R1 R2
  have hc := cl_meas M0 M1
  have hT : Measurable fun s : Fin n → ℝ => ∑ j ∈ Finset.univ.erase k, cl M0 M1 (s j) :=
    Finset.measurable_sum _ (fun i _ => hc.comp (measurable_pi_apply i))
  have hQ : Measurable fun s : Fin n → ℝ => ∑ j ∈ Finset.univ.erase k, cl M0 M1 (s j) ^ 2 :=
    Finset.measurable_sum _ (fun i _ => (hc.comp (measurable_pi_apply i)).pow_const 2)
  exact Real.continuous_sqrt.measurable.comp (((hQ.sub ((hT.pow_const 2).div_const _))).div_const _)

lemma Zks_ind (k : Fin n) (s : Fin n → ℝ) (y : ℝ) :
    Zks M0 M1 n k (Function.update s k y) = Zks M0 M1 n k s := by
  have e1 : R1 M0 M1 n k (Function.update s k y) = R1 M0 M1 n k s := by
    unfold R1
    exact Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  have e2 : R2 M0 M1 n k (Function.update s k y) = R2 M0 M1 n k s := by
    unfold R2
    exact Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  unfold Zks Dk
  rw [e1, e2]

lemma Dk_le_Dd (hn : 2 ≤ n) (k : Fin n) (s : Fin n → ℝ) :
    Dk M0 M1 n k s ≤ Dd M0 M1 n s := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have h := delta_eq (M0 := M0) (M1 := M1) hn k s
  have : 0 ≤ ((n : ℝ) - 1) / n * (cl M0 M1 (s k) - R1 M0 M1 n k s / ((n : ℝ) - 1)) ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    apply div_nonneg <;> linarith
  linarith

lemma Zs_le (hM : M0 ≤ M1) (hn : 0 < n) (s : Fin n → ℝ) :
    Zs M0 M1 n s ≤ |M0| + |M1| := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Zs
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn']
  have h1 : ∀ i, cl M0 M1 (s i) ^ 2 ≤ (|M0| + |M1|) ^ 2 := by
    intro i
    have := abs_le_of_mem (cl_mem M0 M1 hM (s i)).1 (cl_mem M0 M1 hM (s i)).2
    calc cl M0 M1 (s i) ^ 2 = |cl M0 M1 (s i)| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : Q1 M0 M1 n s ≤ n * (|M0| + |M1|) ^ 2 := by
    unfold Q1
    calc ∑ i, cl M0 M1 (s i) ^ 2 ≤ ∑ _i : Fin n, (|M0| + |M1|) ^ 2 :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = n * (|M0| + |M1|) ^ 2 := by simp
  unfold Dd
  have : 0 ≤ T1 M0 M1 n s ^ 2 / n := by positivity
  linarith

theorem hyp_inst (hM : M0 ≤ M1) (hn : 2 ≤ n) :
    Hyp (X := ℝ) (Zs M0 M1 n) (Zks M0 M1 n) (|M0| + |M1|) where
  B0 := by positivity
  mZ := Zs_meas
  mZk := fun k => Zks_meas k
  Z0 := fun s => Real.sqrt_nonneg _
  ZB := fun s => Zs_le hM (by omega) s
  Zk0 := fun k s => Real.sqrt_nonneg _
  ZkZ := fun k s => by
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    unfold Zs Zks
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (Dk_le_Dd hn k s) hn'.le)
  ind := fun k s y => Zks_ind k s y

theorem sum_bound (hM : M0 ≤ M1) (hn : 2 ≤ n) (s : Fin n → ℝ) :
    ∑ k, (Zs M0 M1 n s - Zks M0 M1 n k s) ^ 2 ≤ (M1 - M0) ^ 2 / n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn' : (0 : ℝ) < n := by linarith
  have hn2 : (n : ℝ) - 1 ≠ 0 := by linarith
  set a : ℝ := Dd M0 M1 n s / n with ha
  set b : Fin n → ℝ := fun k => Dk M0 M1 n k s / n with hb
  have ha0 : 0 ≤ a := div_nonneg (Dd_nonneg (by omega) s) hn'.le
  have hb0 : ∀ k, 0 ≤ b k := fun k => div_nonneg (Dk_nonneg hn k s) hn'.le
  have hba : ∀ k, b k ≤ a := fun k => div_le_div_of_nonneg_right (Dk_le_Dd hn k s) hn'.le
  have hZ : Zs M0 M1 n s = Real.sqrt a := rfl
  have hZk : ∀ k, Zks M0 M1 n k s = Real.sqrt (b k) := fun k => rfl
  simp only [hZ, hZk]
  set m : ℝ := T1 M0 M1 n s / n with hm
  have key : ∀ k, (a - b k) ^ 2 ≤ (M1 - M0) ^ 2 * (cl M0 M1 (s k) - m) ^ 2 / (n : ℝ) ^ 2 := by
    intro k
    set x := cl M0 M1 (s k) with hx
    set c := R1 M0 M1 n k s / ((n : ℝ) - 1) with hc
    have hd := delta_eq (M0 := M0) (M1 := M1) hn k s
    have hxm : x - m = ((n : ℝ) - 1) / n * (x - c) := by
      rw [hm, T1_eq M0 M1 n k s, hc]
      field_simp
      ring
    have hab : a - b k = ((n : ℝ) - 1) / n * (x - c) ^ 2 / n := by
      rw [ha, hb]
      simp only
      rw [← sub_div, hd]
    have hxc : (x - c) ^ 2 ≤ (M1 - M0) ^ 2 := by
      have h1 := cl_mem M0 M1 hM (s k)
      have h2 := c_mem hM hn k s
      rw [← hx] at h1
      rw [← hc] at h2
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    rw [hab, hxm]
    have : (((n : ℝ) - 1) / n * (x - c) ^ 2 / n) ^ 2 =
        (x - c) ^ 2 * (((n : ℝ) - 1) / n * (x - c)) ^ 2 / (n : ℝ) ^ 2 := by
      field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hxc (sq_nonneg _) |>.trans_eq (by ring)
  have per : ∀ k, a * (Real.sqrt a - Real.sqrt (b k)) ^ 2 ≤ (a - b k) ^ 2 :=
    fun k => sqrt_ineq a (b k) (hb0 k) (hba k)
  rcases eq_or_lt_of_le ha0 with h0 | hpos
  · -- a = 0
    have : ∀ k, Real.sqrt (b k) = 0 := fun k => by
      have : Real.sqrt (b k) ≤ Real.sqrt a := Real.sqrt_le_sqrt (hba k)
      rw [← h0, Real.sqrt_zero] at this
      exact le_antisymm this (Real.sqrt_nonneg _)
    simp only [this, ← h0, Real.sqrt_zero]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · have hsq : a * ∑ k, (Real.sqrt a - Real.sqrt (b k)) ^ 2 ≤ (M1 - M0) ^ 2 / n * a := by
      rw [Finset.mul_sum]
      calc ∑ k, a * (Real.sqrt a - Real.sqrt (b k)) ^ 2 ≤ ∑ k, (a - b k) ^ 2 :=
            Finset.sum_le_sum (fun k _ => per k)
        _ ≤ ∑ k, (M1 - M0) ^ 2 * (cl M0 M1 (s k) - m) ^ 2 / (n : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun k _ => key k)
        _ = (M1 - M0) ^ 2 * (∑ k, (cl M0 M1 (s k) - m) ^ 2) / (n : ℝ) ^ 2 := by
            rw [← Finset.sum_div, ← Finset.mul_sum]
        _ = (M1 - M0) ^ 2 / n * a := by
            rw [hm, sum_sq_eq (by omega) s, ha]
            field_simp
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_left hcon hpos
    linarith

end Inst2


section Final

open VarianceRegularization.Covering in
theorem main (P : Measure ℝ) [IsProbabilityMeasure P] (M0 M1 : ℝ)
    (hM : M0 < M1) (hP : ∀ᵐ z ∂P, z ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : 0 ≤ t) :
    Measure.pi (fun _ : Fin n => P)
        {Z | Real.sqrt (∫ W, sampleVar W ∂(Measure.pi (fun _ : Fin n => P))) + t
          ≤ Real.sqrt (sampleVar Z)}
      ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * t ^ 2 / (2 * (M1 - M0) ^ 2)))) := by
  set μ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => P) with hμ
  have : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases ht.eq_or_lt with h0 | htpos
  · -- t = 0: the right-hand side is 1
    subst h0
    have : ENNReal.ofReal (Real.exp (-((n : ℝ) * (0 : ℝ) ^ 2 / (2 * (M1 - M0) ^ 2)))) = 1 := by
      simp
    rw [this]
    exact prob_le_one
  by_cases h1 : n = 1
  · subst h1
    have hsv : ∀ W : Fin 1 → ℝ, sampleVar W = 0 := by
      intro W
      simp [sampleVar, VarianceRegularization.Expansion.empMean]
    have hempty : {Z : Fin 1 → ℝ | Real.sqrt (∫ W, sampleVar W ∂μ) + t ≤ Real.sqrt (sampleVar Z)}
        = ∅ := by
      ext Z
      simp only [hsv, integral_zero, Real.sqrt_zero, zero_add, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      exact htpos
    rw [hempty]; simp
  have hn2 : 2 ≤ n := by omega
  have hH := hyp_inst (M0 := M0) (M1 := M1) (n := n) hM.le hn2
  have hσ : 0 < (M1 - M0) ^ 2 / n := by
    have : 0 < M1 - M0 := by linarith
    positivity
  have tail := tail_core P hH ((M1 - M0) ^ 2 / n) hσ (sum_bound hM.le hn2) t ht
  -- a.e. facts
  have hcube : ∀ᵐ W ∂μ, ∀ i, W i ∈ Set.Icc M0 M1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => P) i).quasiMeasurePreserving.ae hP
  have hsvZ : ∀ W : Fin n → ℝ, (∀ i, W i ∈ Set.Icc M0 M1) →
      sampleVar W = Dd M0 M1 n W / n := by
    intro W hW
    have hcl : ∀ i, cl M0 M1 (W i) = W i := fun i => cl_id M0 M1 _ (hW i)
    unfold sampleVar Dd T1 Q1 VarianceRegularization.Expansion.empMean
    simp only [hcl]
    field_simp
  have hZ : ∀ᵐ W ∂μ, Real.sqrt (sampleVar W) = Zs M0 M1 n W := by
    filter_upwards [hcube] with W hW
    unfold Zs
    rw [hsvZ W hW]
  have hZ2 : ∀ᵐ W ∂μ, sampleVar W = Zs M0 M1 n W ^ 2 := by
    filter_upwards [hcube] with W hW
    unfold Zs
    rw [Real.sq_sqrt (div_nonneg (Dd_nonneg hn W) hn'.le), hsvZ W hW]
  have hmeas : Measurable (Zs M0 M1 n) := Zs_meas
  have hbd : ∀ W, ‖Zs M0 M1 n W‖ ≤ |M0| + |M1| := fun W => by
    have hz0 : 0 ≤ Zs M0 M1 n W := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hz0]
    exact Zs_le hM.le hn W
  have hmem : MemLp (Zs M0 M1 n) 2 μ :=
    MemLp.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)
  have hjens : (∫ W, Zs M0 M1 n W ∂μ) ≤ Real.sqrt (∫ W, sampleVar W ∂μ) := by
    have h1 : ∫ W, sampleVar W ∂μ = ∫ W, Zs M0 M1 n W ^ 2 ∂μ := integral_congr_ae hZ2
    have h2 := variance_nonneg (Zs M0 M1 n) μ
    rw [variance_eq_sub hmem] at h2
    have h3 : (∫ W, Zs M0 M1 n W ∂μ) ^ 2 ≤ ∫ W, sampleVar W ∂μ := by
      rw [h1]
      simpa using h2
    exact (le_abs_self _).trans (Real.abs_le_sqrt h3)
  have hsub : ∀ᵐ W ∂μ, W ∈ {Z : Fin n → ℝ | Real.sqrt (∫ W, sampleVar W ∂μ) + t
      ≤ Real.sqrt (sampleVar Z)} →
      W ∈ {s : Fin n → ℝ | (∫ s, Zs M0 M1 n s ∂μ) + t ≤ Zs M0 M1 n s} := by
    filter_upwards [hZ] with W hW hmemW
    have h1 : Real.sqrt (∫ W, sampleVar W ∂μ) + t ≤ Real.sqrt (sampleVar W) := hmemW
    rw [hW] at h1
    show (∫ s, Zs M0 M1 n s ∂μ) + t ≤ Zs M0 M1 n W
    linarith
  have hexp : t ^ 2 / (2 * ((M1 - M0) ^ 2 / n)) = (n : ℝ) * t ^ 2 / (2 * (M1 - M0) ^ 2) := by
    have : (M1 - M0) ^ 2 ≠ 0 := hσ.ne' |> fun h => by
      intro h0; apply h; rw [h0]; simp
    field_simp
  rw [hexp] at tail
  calc μ _ ≤ μ {s : Fin n → ℝ | (∫ s, Zs M0 M1 n s ∂μ) + t ≤ Zs M0 M1 n s} :=
        measure_mono_ae hsub
    _ = ENNReal.ofReal (μ.real {s : Fin n → ℝ | (∫ s, Zs M0 M1 n s ∂μ) + t ≤ Zs M0 M1 n s}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal tail

end Final

end SU3

open MeasureTheory VarianceRegularization.Covering in
theorem solution (P : Measure ℝ) [IsProbabilityMeasure P] (M0 M1 : ℝ)
    (hM : M0 < M1) (hP : ∀ᵐ z ∂P, z ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : 0 ≤ t) :
    Measure.pi (fun _ : Fin n => P)
        {Z | Real.sqrt (∫ W, sampleVar W ∂(Measure.pi (fun _ : Fin n => P))) + t
          ≤ Real.sqrt (sampleVar Z)}
      ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) * t ^ 2 / (2 * (M1 - M0) ^ 2)))) := by
  exact SU3.main P M0 M1 hM hP n hn t ht

