-- Prove2me | solution 1 for UnderstandingML.mcdiarmid_inequality_pi
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:13:38.101916+00:00
-- url     : https://prove2.me/submissions/9902e733-32ce-4ede-9846-827c76b3fae5

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory

namespace UnderstandingML.McDiarmidAux

variable {V : Type*} [MeasurableSpace V]

omit [MeasurableSpace V] in
/-- A function with bounded differences `cᵢ` varies by at most `∑ cᵢ`. -/
lemma abs_sub_le_sum {n : ℕ} (f : (Fin n → V) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ (x : Fin n → V) (i : Fin n) (v : V), |f x - f (Function.update x i v)| ≤ c i)
    (x y : Fin n → V) : |f x - f y| ≤ ∑ i, c i := by
  classical
  let z : Finset (Fin n) → Fin n → V := fun s i ↦ if i ∈ s then y i else x i
  have key : ∀ s : Finset (Fin n), |f x - f (z s)| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [z]
    | insert a s ha ih =>
      have hz : z (insert a s) = Function.update (z s) a (y a) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [z]
        · simp [z, hi]
      rw [hz, Finset.sum_insert ha]
      calc |f x - f (Function.update (z s) a (y a))|
          ≤ |f x - f (z s)| + |f (z s) - f (Function.update (z s) a (y a))| := abs_sub_le _ _ _
        _ ≤ ∑ i ∈ s, c i + c a := add_le_add ih (hc _ _ _)
        _ = c a + ∑ i ∈ s, c i := add_comm _ _
  have : z Finset.univ = y := by funext i; simp [z]
  simpa [this] using key Finset.univ

lemma nonempty_of_prob (μ : Measure V) [IsProbabilityMeasure μ] : Nonempty V := by
  by_contra hV
  rw [not_nonempty_iff] at hV
  have := measure_univ (μ := μ)
  rw [Set.univ_eq_empty_iff.2 hV, measure_empty] at this
  exact zero_ne_one this

/-- **Hoeffding's lemma for a function of one variable with range at most `c`.** -/
lemma integral_exp_le_of_range {μ : Measure V} [IsProbabilityMeasure μ] (g : V → ℝ)
    (hg : Measurable g) (c : ℝ) (hc : ∀ z z', g z - g z' ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (g z - ∫ z', g z' ∂μ)) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 8) := by
  have hne : Nonempty V := nonempty_of_prob μ
  set z0 : V := hne.some
  have hc0 : 0 ≤ c := by simpa using hc z0 z0
  have hbA : BddAbove (Set.range g) := ⟨g z0 + c, by
    rintro _ ⟨z, rfl⟩; have := hc z z0; linarith⟩
  have hbB : BddBelow (Set.range g) := ⟨g z0 - c, by
    rintro _ ⟨z, rfl⟩; have := hc z0 z; linarith⟩
  have hgi : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable (|g z0| + c) ?_
    refine Filter.Eventually.of_forall (fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hc z z0; have h2 := hc z0 z
    constructor <;> cases abs_cases (g z0) <;> linarith
  set E := ∫ z', g z' ∂μ
  set a := (⨅ z, g z) - E
  set b := (⨆ z, g z) - E
  have hab : b - a ≤ c := by
    have : (⨆ z, g z) ≤ (⨅ z, g z) + c := by
      refine ciSup_le (fun z ↦ ?_)
      have : g z - c ≤ ⨅ z, g z := le_ciInf (fun z' ↦ by have := hc z z'; linarith)
      linarith
    simp only [a, b]; linarith
  have hab0 : 0 ≤ b - a := by
    have : (⨅ z, g z) ≤ ⨆ z, g z := (ciInf_le hbB z0).trans (le_ciSup hbA z0)
    simp only [a, b]; linarith
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ)
    (X := fun z ↦ g z - E) (a := a) (b := b) (hg.sub measurable_const).aemeasurable
    (Filter.Eventually.of_forall (fun z ↦ ⟨by simp only [a]; linarith [ciInf_le hbB z],
      by simp only [b]; linarith [le_ciSup hbA z]⟩))
    (by rw [integral_sub hgi (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_self])
  have := hsub.mgf_le t
  unfold mgf at this
  refine this.trans (Real.exp_le_exp.2 ?_)
  have e : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = ((b - a) / 2) ^ 2 := by
    simp [Real.norm_of_nonneg hab0]
  rw [e]
  have : (b - a) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hab0 hab 2
  nlinarith [sq_nonneg t]

/-- **The exponential-moment bound behind McDiarmid's inequality**, by induction on the number
of coordinates. -/
theorem integral_exp_le : ∀ (n : ℕ) (μ : Fin n → Measure V) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → V) → ℝ), Measurable f → ∀ (c : Fin n → ℝ),
    (∀ (x : Fin n → V) (i : Fin n) (v : V), |f x - f (Function.update x i v)| ≤ c i) →
    ∀ t : ℝ, ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
    intro μ _ f _ c _ t
    simp [integral_unique]
  | succ n ih =>
    intro μ _ f hf c hc t
    set P := Measure.pi μ with hP
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ V) 0 with he
    set ν := Measure.pi (fun j : Fin n ↦ μ (Fin.succAbove 0 j)) with hν
    have hp : MeasurePreserving e P ((μ 0).prod ν) := measurePreserving_piFinSuccAbove μ 0
    have hsymm : ∀ p : V × (Fin n → V), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      funext j
      rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']
    have hint : ∀ φ : (Fin (n + 1) → V) → ℝ,
        ∫ x, φ x ∂P = ∫ p, φ (Fin.cons p.1 p.2) ∂((μ 0).prod ν) := by
      intro φ
      rw [← (hp.symm e).integral_comp']
      simp only [hsymm]
    -- notation for the sections
    set g : V → (Fin n → V) → ℝ := fun z y ↦ f (Fin.cons z y) with hg
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = f ∘ e.symm := by
        funext p; simp only [Function.comp, hsymm]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hne : Nonempty V := nonempty_of_prob (μ 0)
    set v0 : V := hne.some
    set x0 : Fin (n + 1) → V := fun _ ↦ v0
    have hfb : ∀ x, |f x| ≤ |f x0| + ∑ i, c i := by
      intro x
      have := abs_sub_le_sum f c hc x x0
      have h2 := abs_sub_abs_le_abs_sub (f x) (f x0)
      linarith
    set B := |f x0| + ∑ i, c i
    have hgb : ∀ z y, |g z y| ≤ B := fun z y ↦ hfb _
    have hgz : ∀ y, Measurable (fun z ↦ g z y) := fun y ↦ hgm.comp (measurable_id.prodMk measurable_const)
    have hgzi : ∀ y, Integrable (fun z ↦ g z y) (μ 0) := fun y ↦
      Integrable.of_bound (hgz y).aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs]; exact hgb z y))
    set h : (Fin n → V) → ℝ := fun y ↦ ∫ z, g z y ∂(μ 0) with hh
    have hhm : Measurable h := (hgm.stronglyMeasurable.integral_prod_left).measurable
    have hhb : ∀ y, |h y| ≤ B := by
      intro y
      have := norm_integral_le_of_norm_le_const (μ := μ 0) (f := fun z ↦ g z y) (C := B)
        (Filter.Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs]; exact hgb z y))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    -- bounded differences of `h`
    have hhc : ∀ (y : Fin n → V) (j : Fin n) (w : V),
        |h y - h (Function.update y j w)| ≤ c (Fin.succAbove 0 j) := by
      intro y j w
      simp only [hh]
      rw [← integral_sub (hgzi y) (hgzi _)]
      have := norm_integral_le_of_norm_le_const (μ := μ 0)
        (f := fun z ↦ g z y - g z (Function.update y j w)) (C := c (Fin.succAbove 0 j))
        (Filter.Eventually.of_forall (fun z ↦ by
          rw [Real.norm_eq_abs]
          simp only [hg, Fin.cons_update, Fin.succAbove_zero]
          exact hc _ _ _))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have IH := ih (fun j ↦ μ (Fin.succAbove 0 j)) h hhm (fun j ↦ c (Fin.succAbove 0 j)) hhc t
    -- integrability of bounded functions of `g`
    have hexpb : ∀ (r K : ℝ), |r| ≤ K → ‖Real.exp (t * r)‖ ≤ Real.exp (|t| * K) := by
      intro r K hr
      rw [Real.norm_eq_abs, Real.abs_exp]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hr (abs_nonneg t)
    have hEhb : ∀ E : ℝ, |E| ≤ B → ∀ z y, |g z y - E| ≤ 2 * B := by
      intro E hE z y
      have := hgb z y
      calc |g z y - E| ≤ |g z y| + |E| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    have hfi : Integrable (fun p : V × (Fin n → V) ↦ f (Fin.cons p.1 p.2)) ((μ 0).prod ν) :=
      Integrable.of_bound hgm.aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hgb p.1 p.2))
    -- the mean of `f` is the mean of `h`
    have hEf : ∫ y, f y ∂P = ∫ y, h y ∂ν := by
      rw [hint f, integral_prod_symm _ hfi]
    set Eh := ∫ y, h y ∂ν with hEh
    have hEhB : |Eh| ≤ B := by
      have := norm_integral_le_of_norm_le_const (μ := ν) (f := h) (C := B)
        (Filter.Eventually.of_forall (fun y ↦ by rw [Real.norm_eq_abs]; exact hhb y))
      have hνP : IsProbabilityMeasure ν := by rw [hν]; infer_instance
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have hFi : Integrable (fun p : V × (Fin n → V) ↦ Real.exp (t * (g p.1 p.2 - Eh)))
        ((μ 0).prod ν) :=
      Integrable.of_bound
        ((Real.measurable_exp.comp (measurable_const.mul
          (hgm.sub measurable_const))).aestronglyMeasurable) (Real.exp (|t| * (2 * B)))
        (Filter.Eventually.of_forall (fun p ↦ hexpb _ _ (hEhb Eh hEhB p.1 p.2)))
    have hνP : IsProbabilityMeasure ν := by rw [hν]; infer_instance
    have hHi : Integrable (fun y ↦ Real.exp (t * (h y - Eh)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8)) ν :=
      (Integrable.of_bound
        ((Real.measurable_exp.comp (measurable_const.mul
          (hhm.sub measurable_const))).aestronglyMeasurable) (Real.exp (|t| * (2 * B)))
        (Filter.Eventually.of_forall (fun y ↦ hexpb _ _ (by
          have := hhb y
          calc |h y - Eh| ≤ |h y| + |Eh| := abs_sub _ _
            _ ≤ 2 * B := by linarith)))).mul_const _
    -- the one-step bound
    have hstep : ∀ y, ∫ z, Real.exp (t * (g z y - Eh)) ∂(μ 0) ≤
        Real.exp (t * (h y - Eh)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) := by
      intro y
      have e1 : ∀ z, Real.exp (t * (g z y - Eh)) =
          Real.exp (t * (h y - Eh)) * Real.exp (t * (g z y - h y)) := by
        intro z; rw [← Real.exp_add]; congr 1; ring
      simp only [e1]
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine integral_exp_le_of_range (fun z ↦ g z y) (hgz y) (c 0) (fun z z' ↦ ?_) t
      have := hc (Fin.cons z y) 0 z'
      rw [Fin.update_cons_zero] at this
      exact (le_abs_self _).trans this
    calc ∫ x, Real.exp (t * (f x - ∫ y, f y ∂P)) ∂P
        = ∫ p, Real.exp (t * (g p.1 p.2 - Eh)) ∂((μ 0).prod ν) := by
          rw [hEf, hint (fun x ↦ Real.exp (t * (f x - Eh)))]
      _ = ∫ y, ∫ z, Real.exp (t * (g z y - Eh)) ∂(μ 0) ∂ν := integral_prod_symm _ hFi
      _ ≤ ∫ y, Real.exp (t * (h y - Eh)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) ∂ν := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y ↦ ?_)) hHi
            (Filter.Eventually.of_forall hstep)
          exact integral_nonneg (fun z ↦ (Real.exp_pos _).le)
      _ = Real.exp (t ^ 2 * c 0 ^ 2 / 8) * ∫ y, Real.exp (t * (h y - Eh)) ∂ν := by
          rw [integral_mul_const, mul_comm]
      _ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 8) *
            Real.exp (t ^ 2 * (∑ j : Fin n, c (Fin.succAbove 0 j) ^ 2) / 8) :=
          mul_le_mul_of_nonneg_left IH (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          simp only [Fin.succAbove_zero]
          congr 1; ring

/-- McDiarmid's one-sided tail bound, in sub-Gaussian form. -/
lemma hasSubgaussianMGF_sub_integral {m : ℕ} (μ : Fin m → Measure V)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin m → V) → ℝ) (hf : Measurable f) (c : ℝ)
    (hc : ∀ (x : Fin m → V) (i : Fin m) (v : V), |f x - f (Function.update x i v)| ≤ c) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂(Measure.pi μ)) ⟨m * c ^ 2 / 4, by positivity⟩
      (Measure.pi μ) := by
  set P := Measure.pi μ
  have hsum : ∀ x y, |f x - f y| ≤ m * c := by
    intro x y
    simpa using abs_sub_le_sum f (fun _ ↦ c) hc x y
  have hfi : ∀ x, Integrable (fun y ↦ f x - f y) P := fun x ↦
    Integrable.of_bound (measurable_const.sub hf).aestronglyMeasurable (m * c)
      (Filter.Eventually.of_forall (fun y ↦ by rw [Real.norm_eq_abs]; exact hsum x y))
  have hXb : ∀ x, |f x - ∫ y, f y ∂P| ≤ m * c := by
    intro x
    have hfint : Integrable f P := by
      have := (hfi x).sub (integrable_const (f x))
      refine this.neg.congr (Filter.Eventually.of_forall (fun y ↦ ?_))
      simp
    have e : f x - ∫ y, f y ∂P = ∫ y, (f x - f y) ∂P := by
      rw [integral_sub (integrable_const _) hfint, integral_const, probReal_univ, one_smul]
    rw [e]
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun y ↦ f x - f y) (C := m * c)
      (Filter.Eventually.of_forall (fun y ↦ by rw [Real.norm_eq_abs]; exact hsum x y))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · refine Integrable.of_bound
      ((Real.measurable_exp.comp (measurable_const.mul
        (hf.sub measurable_const))).aestronglyMeasurable) (Real.exp (|t| * (m * c))) ?_
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hXb x) (abs_nonneg t)
  · unfold mgf
    refine (integral_exp_le m μ f hf (fun _ ↦ c) hc t).trans (le_of_eq ?_)
    show Real.exp (t ^ 2 * (∑ _i : Fin m, c ^ 2) / 8) = Real.exp ((m * c ^ 2 / 4) * t ^ 2 / 2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf

end UnderstandingML.McDiarmidAux

open UnderstandingML.McDiarmidAux in
theorem solution {V : Type*} [MeasurableSpace V] (m : ℕ) (μ : Fin m → Measure V)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin m → V) → ℝ) (hf : Measurable f) (c : ℝ)
    (hc : ∀ (x : Fin m → V) (i : Fin m) (v : V), |f x - f (Function.update x i v)| ≤ c)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi μ {x | c * Real.sqrt (Real.log (2 / δ) * m / 2) <
      |f x - ∫ y, f y ∂(Measure.pi μ)|} ≤ ENNReal.ofReal δ := by
  classical
  set P := Measure.pi μ with hP
  set E := ∫ y, f y ∂P with hE
  set ε := c * Real.sqrt (Real.log (2 / δ) * m / 2) with hε
  have hsum : ∀ x y, |f x - f y| ≤ m * c := by
    intro x y
    simpa using abs_sub_le_sum f (fun _ ↦ c) hc x y
  have hlog : 0 < Real.log (2 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  by_cases hC : 0 < (m : ℝ) * c ^ 2
  · have hm : (0 : ℝ) < m := by
      rcases (Nat.cast_nonneg m : (0 : ℝ) ≤ m).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hC; exact absurd hC (lt_irrefl 0)
    have hne : Nonempty V := nonempty_of_prob (μ ⟨0, by exact_mod_cast hm⟩)
    have hc0 : 0 ≤ c := by
      have x : Fin m → V := fun _ ↦ hne.some
      exact (abs_nonneg _).trans (hc x ⟨0, by exact_mod_cast hm⟩ hne.some)
    have hε0 : 0 ≤ ε := by positivity
    -- the two one-sided bounds
    have h1 := (hasSubgaussianMGF_sub_integral μ f hf c hc).measure_ge_le hε0
    have hc' : ∀ (x : Fin m → V) (i : Fin m) (v : V),
        |(fun x ↦ -f x) x - (fun x ↦ -f x) (Function.update x i v)| ≤ c := by
      intro x i v
      show |-f x - -f (Function.update x i v)| ≤ c
      rw [show -f x - -f (Function.update x i v) = -(f x - f (Function.update x i v)) by ring,
        abs_neg]
      exact hc x i v
    have h2 := (hasSubgaussianMGF_sub_integral μ (fun x ↦ -f x) hf.neg c hc').measure_ge_le
      hε0
    have hcne : c ≠ 0 := by
      rintro rfl; simp at hC
    have hbound : Real.exp (-ε ^ 2 / (2 * (m * c ^ 2 / 4))) = δ / 2 := by
      have hε2 : ε ^ 2 = c ^ 2 * (Real.log (2 / δ) * m / 2) := by
        rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
      rw [hε2]
      have : -(c ^ 2 * (Real.log (2 / δ) * m / 2)) / (2 * (m * c ^ 2 / 4)) =
          -Real.log (2 / δ) := by
        field_simp
        ring
      rw [this, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    replace h1 := h1.trans (le_of_eq hbound)
    replace h2 := h2.trans (le_of_eq hbound)
    have hsub : {x | ε < |f x - E|} ⊆
        {x | ε ≤ f x - E} ∪ {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      rw [integral_neg]
      rcases le_or_gt 0 (f x - E) with h | h
      · left; simp only [Set.mem_setOf_eq]; rw [abs_of_nonneg h] at hx; linarith
      · right; simp only [Set.mem_setOf_eq]; rw [abs_of_neg h] at hx; linarith
    calc P {x | ε < |f x - E|}
        ≤ P ({x | ε ≤ f x - E} ∪ {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P}) :=
          measure_mono hsub
      _ ≤ P {x | ε ≤ f x - E} + P {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P} :=
          measure_union_le _ _
      _ = ENNReal.ofReal (P.real {x | ε ≤ f x - E}) + ENNReal.ofReal
            (P.real {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P}) := by
          rw [ofReal_measureReal, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  · -- degenerate case: `m c = 0`, so `f` is constant and the event is empty
    have hmc : (m : ℝ) * c = 0 := by
      have h0 : (m : ℝ) * c ^ 2 = 0 := le_antisymm (not_lt.1 hC) (by positivity)
      rcases mul_eq_zero.1 h0 with h | h
      · rw [h, zero_mul]
      · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h, mul_zero]
    have hε0 : ε = 0 := by
      rcases mul_eq_zero.1 hmc with h | h
      · rw [hε, h]; simp
      · rw [hε, h, zero_mul]
    have hconst : ∀ x, f x - E = 0 := by
      intro x
      have hfx : ∀ y, f y = f x := fun y ↦ by
        have := hsum y x; rw [hmc] at this; linarith [abs_nonneg (f y - f x), abs_le.1 this]
      rw [hE, integral_congr_ae (Filter.Eventually.of_forall hfx), integral_const, probReal_univ,
        one_smul, sub_self]
    have : {x | ε < |f x - E|} = ∅ := by
      ext x; simp [hconst x, hε0]
    rw [this, measure_empty]
    simp
