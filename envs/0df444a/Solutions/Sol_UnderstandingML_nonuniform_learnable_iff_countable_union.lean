-- Prove2me | solution 1 for UnderstandingML.nonuniform_learnable_iff_countable_union
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:36:34.822987+00:00
-- url     : https://prove2.me/submissions/1c0f7cde-00e7-402a-8912-5b83346886a5

import Definitions.Def_UnderstandingML_Nonuniform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_UnderstandingML_no_free_lunch
import Theorems.Thm_UnderstandingML_uc_implies_agnostic_pac

/-!
# Theorem 7.2: nonuniform learnability iff countable union of agnostic PAC learnable classes

Proof outline.
* Theorem 7.3 (a countable union of classes with uniform convergence is nonuniformly learnable).
* Massart's lemma and the Sauer–Shelah bound on the number of traces.
* Symmetrization with a ghost sample and Rademacher signs: a finite class all of whose
  shattered sets have at most `d` points is `ε`-representative with high probability, with a
  bound independent of the size of the class; pointwise separability passes to the whole class.
* No-Free-Lunch transported to a shattered finite set: a learner with sample size `m` that
  succeeds at accuracy `1/16` and confidence `1/8` forces shattered sets to have `≤ 2m` points.
* (⇒) `Hₙ = {h ∈ H : m^NUL(1/16, 1/8, h) ≤ max n m^NUL(1/16, 1/8, h₀)}` has bounded shattered
  sets, hence uniform convergence, hence (with an ERM learner, which exists for the 0–1 loss)
  is agnostic PAC learnable.
* (⇐) each agnostic PAC learnable `Hₙ` has bounded shattered sets, hence uniform convergence;
  conclude by Theorem 7.3.
-/

open MeasureTheory

namespace UnderstandingML

/-- The constant sample `(z, …, z)` has (outer) probability at least `μ({z})^m`. -/
theorem nuAux_const_sample_ge {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (m : ℕ) (z : Z) :
    iidLaw μ m {fun _ => z} = μ {z} ^ m := by
  have : ({fun _ => z} : Set (Fin m → Z)) = Set.univ.pi (fun _ => ({z} : Set Z)) := by
    ext S; simp [funext_iff]
  rw [this, iidLaw, Measure.pi_pi]
  simp

/-- The empirical risk of a constant sample. -/
theorem nuAux_empRisk_const {Z : Type*} {Hyp : Type*} (loss : Hyp → Z → ℝ) {m : ℕ} (hm : 0 < m)
    (z : Z) (h : Hyp) : empRisk loss (fun _ : Fin m => z) h = loss h z := by
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [empRisk]
  field_simp

/-- If the constant sample is not representative, the uniform convergence property fails:
the constant sample is representative whenever its probability exceeds `δ`. -/
theorem nuAux_const_rep {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (mUC : ℝ → ℝ → ℕ) (hUC : HasUniformConvergenceWith loss H mUC)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (μ : Measure Z)
    [IsProbabilityMeasure μ] (z : Z) (m : ℕ) (hm : mUC ε δ ≤ m)
    (hbig : ENNReal.ofReal δ < μ {z} ^ m) :
    IsRepresentative loss H μ ε (fun _ : Fin m => z) := by
  by_contra hnot
  have h1 := hUC ε δ hε0 hε1 hδ0 hδ1 μ inferInstance m hm
  have h2 : iidLaw μ m {fun _ => z} ≤ iidLaw μ m {S | ¬ IsRepresentative loss H μ ε S} :=
    measure_mono (by simpa using hnot)
  rw [nuAux_const_sample_ge] at h2
  exact absurd (h2.trans h1) (not_le.2 hbig)

/-- Under a Dirac mass the risk is the loss at the point (for a class with the uniform
convergence property). -/
theorem nuAux_risk_dirac {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (mUC : ℝ → ℝ → ℕ) (hUC : HasUniformConvergenceWith loss H mUC)
    {h : Hyp} (hh : h ∈ H) (z : Z) : risk loss (Measure.dirac z) h = loss h z := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  rcases lt_or_ge ε (1 / 2) with hε' | hε'
  · have hrep := nuAux_const_rep loss H mUC hUC hε (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) (Measure.dirac z) z (mUC ε (1 / 2) + 1) (Nat.le_succ _)
      (by rw [Measure.dirac_apply_of_mem (Set.mem_singleton z), one_pow]
          exact ENNReal.ofReal_lt_one.2 (by norm_num))
    have := hrep h hh
    rw [nuAux_empRisk_const loss (Nat.succ_pos _)] at this
    rw [Real.dist_eq, abs_sub_comm]; exact this
  · have hrep := nuAux_const_rep loss H mUC hUC (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) (Measure.dirac z) z (mUC (1 / 4) (1 / 2) + 1) (Nat.le_succ _)
      (by rw [Measure.dirac_apply_of_mem (Set.mem_singleton z), one_pow]
          exact ENNReal.ofReal_lt_one.2 (by norm_num))
    have := hrep h hh
    rw [nuAux_empRisk_const loss (Nat.succ_pos _)] at this
    rw [Real.dist_eq, abs_sub_comm]; linarith

/-- A member of a class with the uniform convergence property has risk bounded below uniformly
over all distributions. -/
theorem nuAux_risk_lower {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (mUC : ℝ → ℝ → ℕ) (hUC : HasUniformConvergenceWith loss H mUC)
    {h : Hyp} (hh : h ∈ H) :
    ∃ β : ℝ, ∀ D : Measure Z, IsProbabilityMeasure D → β ≤ risk loss D h := by
  by_cases hzero : ∀ z, loss h z = 0
  · refine ⟨0, fun D _ => ?_⟩
    simp [risk, hzero]
  push_neg at hzero
  obtain ⟨z, hz⟩ := hzero
  set c := loss h z
  have hdirac := nuAux_risk_dirac loss H mUC hUC hh z
  have hintz : Integrable (loss h) (Measure.dirac z) := by
    by_contra hni
    have := integral_undef hni
    simp only [risk] at hdirac
    exact hz (hdirac.symm.trans this)
  set m1 : ℕ := mUC (1 / 2) (1 / 2) + 1 with hm1
  have hm1pos : (0 : ℝ) < m1 := by positivity
  set p : ℝ := 1 / (4 * m1) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by
    rw [hp, div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ m1 := by exact_mod_cast Nat.succ_pos _
    linarith
  refine ⟨min 0 (c - 1 / (2 * p)), fun D hD => ?_⟩
  by_cases hr : risk loss D h = 0
  · rw [hr]; exact min_le_left _ _
  refine (min_le_right _ _).trans ?_
  set r := risk loss D h
  have hintD : Integrable (loss h) D := by
    by_contra hni; exact hr (integral_undef hni)
  set D' : Measure Z := ENNReal.ofReal (1 - p) • Measure.dirac z + ENNReal.ofReal p • D
  haveI hD' : IsProbabilityMeasure D' := by
    constructor
    simp only [D', Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hp0.le]
    simp
  have hriskD' : risk loss D' h = (1 - p) * c + p * r := by
    simp only [risk, D']
    rw [integral_add_measure (hintz.smul_measure ENNReal.ofReal_ne_top)
      (hintD.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hp0.le]
    simp only [smul_eq_mul]
    rw [show ∫ x, loss h x ∂Measure.dirac z = c from hdirac]
    rfl
  have hsing : ENNReal.ofReal (1 - p) ≤ D' {z} := by
    simp only [D', Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton z), mul_one]
    exact le_self_add
  have hbig : ENNReal.ofReal (1 / 2) < D' {z} ^ m1 := by
    refine lt_of_lt_of_le ?_ (pow_le_pow_left' hsing m1)
    rw [← ENNReal.ofReal_pow (by linarith)]
    refine (ENNReal.ofReal_lt_ofReal_iff (pow_pos (by linarith) _)).2 ?_
    have hb := one_add_mul_le_pow (a := -p) (by linarith) m1
    have : (m1 : ℝ) * p = 1 / 4 := by rw [hp]; field_simp
    have e : (1 : ℝ) + (m1 : ℝ) * -p = 3 / 4 := by linarith
    rw [e, ← sub_eq_add_neg] at hb
    linarith
  have hrep := nuAux_const_rep loss H mUC hUC (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) D' z m1 (Nat.le_succ _) hbig h hh
  rw [nuAux_empRisk_const loss (Nat.succ_pos _), hriskD'] at hrep
  have key : p * (c - r) ≤ 1 / 2 := by
    have := (abs_le.1 hrep).2
    linarith
  have : c - r ≤ 1 / (2 * p) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

/-- The first index of a member of `⋃ₙ Hₙ` contains it. -/
theorem nuAux_mem_firstIndex {Hyp : Type*} (Hn : ℕ → Set Hyp) {h : Hyp}
    (hh : h ∈ ⋃ n, Hn n) : h ∈ Hn (firstIndex Hn h) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hh
  exact Nat.sInf_mem (s := {n | h ∈ Hn n}) ⟨n, hn⟩

/-- **Theorem 7.3.** -/
theorem nuAux_main {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp) (hne : (⋃ n, Hn n).Nonempty)
    (hUC : ∀ n, HasUniformConvergence loss (Hn n)) :
    NonuniformLearnable loss (⋃ n, Hn n) := by
  classical
  choose mUC hmUC using hUC
  set H := ⋃ n, Hn n with hHdef
  obtain ⟨h₀, hh₀⟩ := hne
  -- a distribution-free lower bound on the risk of each hypothesis
  have hβex : ∀ h ∈ H, ∃ β : ℝ, ∀ D : Measure Z, IsProbabilityMeasure D → β ≤ risk loss D h :=
    fun h hh => nuAux_risk_lower loss (Hn (firstIndex Hn h)) (mUC _) (hmUC _)
      (nuAux_mem_firstIndex Hn hh)
  let β : Hyp → ℝ := fun h =>
    if hb : ∃ β : ℝ, ∀ D : Measure Z, IsProbabilityMeasure D → β ≤ risk loss D h
    then Classical.choose hb else 0
  have hβ : ∀ h ∈ H, ∀ D : Measure Z, IsProbabilityMeasure D → β h ≤ risk loss D h := by
    intro h hh D hD
    have hb := hβex h hh
    simp only [β, dif_pos hb]
    exact Classical.choose_spec hb D hD
  -- the resolution `T(m)` reached at sample size `m`
  let P : ℕ → ℕ → Prop := fun t m => 2 ≤ t ∧ ∀ k ≤ t, mUC k (1 / t) (1 / t ^ 2) ≤ m
  let T : ℕ → ℕ := fun m => Nat.findGreatest (fun t => P t m) m
  -- candidate hypotheses at sample size `m`
  let C : ℕ → Set Hyp := fun m =>
    {h' | h' ∈ H ∧ firstIndex Hn h' ≤ T m ∧ -((T m : ℕ) : ℝ) ≤ β h'}
  let Good : (m : ℕ) → (Fin m → Z) → Hyp → Prop := fun m S h' =>
    h' ∈ C m ∧ ∀ h'' ∈ C m, empRisk loss S h' ≤ empRisk loss S h'' + 1 / (T m : ℝ)
  let A : Learner Z Hyp := fun m S =>
    if hx : ∃ h', Good m S h' then Classical.choose hx else h₀
  let N : ℕ → ℕ := fun t =>
    max t ((Finset.range (t + 1)).sup fun k => mUC k (1 / t) (1 / t ^ 2))
  let t0 : ℝ → ℝ → Hyp → ℕ := fun ε δ h =>
    max (max 2 (firstIndex Hn h)) (max ⌈-β h⌉₊ (max ⌈3 / ε⌉₊ ⌈2 / δ⌉₊))
  refine ⟨A, fun ε δ h => N (t0 ε δ h), ?_, ?_⟩
  · intro m S
    by_cases hx : ∃ h', Good m S h'
    · simp only [A, dif_pos hx]
      exact (Classical.choose_spec hx).1.1
    · simp only [A, dif_neg hx]; exact hh₀
  intro ε δ hε0 hε1 hδ0 hδ1 h hh D hD m hm
  set t := t0 ε δ h with htdef
  -- the resolution at `m` is at least `t`
  have hPt : P t m := by
    refine ⟨le_trans (le_max_left _ _) (le_max_left _ _), fun k hk => ?_⟩
    refine le_trans ?_ (le_trans (le_max_right _ _) hm)
    exact Finset.le_sup (f := fun k => mUC k (1 / t) (1 / t ^ 2))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have htm : t ≤ m := le_trans (le_max_left _ _) hm
  have htT : t ≤ T m := Nat.le_findGreatest (P := fun t => P t m) htm hPt
  have hPT : P (T m) m := Nat.findGreatest_spec (P := fun t => P t m) htm hPt
  set Tm := T m with hTm
  have hT2 : (2 : ℝ) ≤ Tm := by exact_mod_cast hPT.1
  have hTpos : (0 : ℝ) < Tm := by linarith
  have htR : (t : ℝ) ≤ Tm := by exact_mod_cast htT
  have hT_eps : 3 / ε ≤ Tm := le_trans (Nat.le_ceil _) (le_trans (by
      exact_mod_cast (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_max_right _ _)))) htR)
  have hT_del : 2 / δ ≤ Tm := le_trans (Nat.le_ceil _) (le_trans (by
      exact_mod_cast (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_max_right _ _)))) htR)
  have hT_beta : -β h ≤ Tm := le_trans (Nat.le_ceil _) (le_trans (by
      exact_mod_cast (le_trans (le_max_left _ _) (le_max_right _ _))) htR)
  have hT_idx : firstIndex Hn h ≤ Tm :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htT
  -- the bad event is contained in a finite union of non-representativeness events
  have hsub : {S : Fin m → Z | risk loss D h + ε < risk loss D (A m S)} ⊆
      ⋃ k ∈ Finset.range (Tm + 1),
        {S | ¬ IsRepresentative loss (Hn k) D (1 / (Tm : ℝ)) S} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS
    by_contra hgood
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, not_exists, not_not]
      at hgood
    have hrepC : ∀ h' ∈ C m, |empRisk loss S h' - risk loss D h'| ≤ 1 / (Tm : ℝ) := by
      intro h' hh'
      exact hgood (firstIndex Hn h') (Nat.lt_succ_of_le hh'.2.1) h'
        (nuAux_mem_firstIndex Hn hh'.1)
    have hhC : h ∈ C m := ⟨hh, hT_idx, by linarith⟩
    set V := (fun h' => empRisk loss S h') '' C m
    have hVne : V.Nonempty := ⟨_, h, hhC, rfl⟩
    have hVbdd : BddBelow V := by
      refine ⟨-(Tm : ℝ) - 1 / (Tm : ℝ), ?_⟩
      rintro _ ⟨h', hh', rfl⟩
      have e1 := (abs_le.1 (hrepC h' hh')).1
      have e2 := hβ h' hh'.1 D hD
      have e3 := hh'.2.2
      linarith
    obtain ⟨_, ⟨a, haC, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hVne
      (lt_add_of_pos_right (sInf V) (one_div_pos.2 hTpos))
    have hGood : ∃ h', Good m S h' := by
      refine ⟨a, haC, fun h'' hh'' => ?_⟩
      have := csInf_le hVbdd ⟨h'', hh'', rfl⟩
      linarith
    have hA : Good m S (A m S) := by
      simp only [A, dif_pos hGood]
      exact Classical.choose_spec hGood
    have e1 := (abs_le.1 (hrepC _ hA.1)).1
    have e2 := hA.2 h hhC
    have e3 := (abs_le.1 (hrepC h hhC)).2
    have h3 : 3 / (Tm : ℝ) ≤ ε := by
      rw [div_le_iff₀ hTpos]; rw [div_le_iff₀ hε0] at hT_eps; linarith
    have : 1 / (Tm : ℝ) + 1 / Tm + 1 / Tm = 3 / Tm := by ring
    linarith
  have hinv : 1 / (Tm : ℝ) < 1 := by rw [div_lt_one hTpos]; linarith
  have hinv2 : 1 / (Tm : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  calc iidLaw D m {S | risk loss D h + ε < risk loss D (A m S)}
      ≤ iidLaw D m (⋃ k ∈ Finset.range (Tm + 1),
          {S | ¬ IsRepresentative loss (Hn k) D (1 / (Tm : ℝ)) S}) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (Tm + 1),
          iidLaw D m {S | ¬ IsRepresentative loss (Hn k) D (1 / (Tm : ℝ)) S} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (Tm + 1), ENNReal.ofReal (1 / (Tm : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ Tm := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        have := hmUC k (1 / (Tm : ℝ)) (1 / (Tm : ℝ) ^ 2) (by positivity) hinv (by positivity)
          hinv2 D hD m (hPT.2 k hk')
        simpa using this
    _ = ENNReal.ofReal (((Tm : ℝ) + 1) * (1 / (Tm : ℝ) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    _ ≤ ENNReal.ofReal δ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hδ0] at hT_del
        rw [show ((Tm : ℝ) + 1) * (1 / (Tm : ℝ) ^ 2) = ((Tm : ℝ) + 1) / (Tm : ℝ) ^ 2 by ring,
          div_le_iff₀ (by positivity)]
        nlinarith

end UnderstandingML

/-! Part 1 of the proof of Theorem 7.2: Massart's finite-class lemma for Rademacher averages,
written as a finite average over sign vectors. -/

open MeasureTheory

namespace UnderstandingML

/-- The Rademacher sign attached to a Boolean: `true ↦ -1`, `false ↦ 1`. -/
def vcSgn (b : Bool) : ℝ := if b then -1 else 1

theorem vcAux_sgn_sq (b : Bool) : vcSgn b ^ 2 = 1 := by
  cases b <;> simp [vcSgn]

/-- `∑_σ exp(λ ∑ᵢ sgn(σᵢ) vᵢ) = ∏ᵢ (e^{λvᵢ} + e^{-λvᵢ})`. -/
theorem vcAux_sum_exp_eq_prod {m : ℕ} (l : ℝ) (v : Fin m → ℝ) :
    ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, vcSgn (σ i) * v i) =
      ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i))) := by
  have h1 : ∀ σ : Fin m → Bool, Real.exp (l * ∑ i, vcSgn (σ i) * v i) =
      ∏ i, Real.exp (l * (vcSgn (σ i) * v i)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Bool) => Real.exp (l * (vcSgn b * v i)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [vcSgn]
  ring_nf

/-- The moment generating bound `2^{-m} ∑_σ exp(λ ⟨σ, v⟩) ≤ exp(λ² m / 2)` for `|vᵢ| ≤ 1`. -/
theorem vcAux_sum_exp_le {m : ℕ} (l : ℝ) (v : Fin m → ℝ) (hv : ∀ i, |v i| ≤ 1) :
    ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, vcSgn (σ i) * v i) ≤
      2 ^ m * Real.exp (l ^ 2 * m / 2) := by
  rw [vcAux_sum_exp_eq_prod]
  have hterm : ∀ i, Real.exp (l * v i) + Real.exp (-(l * v i)) ≤ 2 * Real.exp (l ^ 2 / 2) := by
    intro i
    have hc := Real.cosh_le_exp_half_sq (l * v i)
    rw [Real.cosh_eq] at hc
    have hsq : (l * v i) ^ 2 ≤ l ^ 2 := by
      rw [mul_pow]
      have : v i ^ 2 ≤ 1 := by
        have h1 := hv i; have h2 := sq_abs (v i); nlinarith [abs_nonneg (v i)]
      nlinarith [sq_nonneg l]
    have := Real.exp_le_exp.2 (by linarith : (l * v i) ^ 2 / 2 ≤ l ^ 2 / 2)
    linarith
  calc ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i)))
      ≤ ∏ _i : Fin m, 2 * Real.exp (l ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => by positivity) fun i _ => hterm i
    _ = 2 ^ m * Real.exp (l ^ 2 * m / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        ring_nf

/-- **Massart's lemma** (finite average form). For a finite nonempty set `V` of vectors with
entries in `[-1, 1]`, `2^{-m} ∑_σ max_{v ∈ V} |∑ᵢ σᵢ vᵢ| ≤ √(2 m log(2|V|))`. -/
theorem vcAux_massart {m : ℕ} (hm : 0 < m) (V : Finset (Fin m → ℝ)) (hV : V.Nonempty)
    (hb : ∀ v ∈ V, ∀ i, |v i| ≤ 1) :
    (∑ σ : Fin m → Bool, V.sup' hV (fun v => |∑ i, vcSgn (σ i) * v i|)) / 2 ^ m ≤
      Real.sqrt (2 * m * Real.log (2 * V.card)) := by
  set X : (Fin m → Bool) → ℝ := fun σ => V.sup' hV (fun v => |∑ i, vcSgn (σ i) * v i|)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcard : (1 : ℝ) ≤ V.card := by exact_mod_cast hV.card_pos
  set L := Real.log (2 * V.card) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  -- a bound valid for every `λ > 0`
  have key : ∀ l : ℝ, 0 < l → (∑ σ, X σ) / 2 ^ m ≤ L / l + l * m / 2 := by
    intro l hl
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    -- Jensen
    have hJ : Real.exp (l * ((∑ σ, X σ) / 2 ^ m)) ≤ (∑ σ, Real.exp (l * X σ)) / 2 ^ m := by
      have := (convexOn_exp).map_sum_le (t := (Finset.univ : Finset (Fin m → Bool)))
        (w := fun _ => (1 : ℝ) / 2 ^ m) (p := fun σ => l * X σ)
        (fun _ _ => by positivity)
        (by rw [Finset.sum_const, Finset.card_univ]; simp [Fintype.card_bool])
        (fun _ _ => Set.mem_univ _)
      simp only [smul_eq_mul] at this
      have e1 : l * ((∑ σ, X σ) / 2 ^ m) = ∑ σ, 1 / 2 ^ m * (l * X σ) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
      have e2 : (∑ σ, Real.exp (l * X σ)) / 2 ^ m = ∑ σ, 1 / 2 ^ m * Real.exp (l * X σ) := by
        rw [← Finset.mul_sum]; ring
      rw [e1, e2]; exact this
    -- each exponential is bounded by a sum over `V`
    have hpt : ∀ σ, Real.exp (l * X σ) ≤ ∑ v ∈ V,
        (Real.exp (l * ∑ i, vcSgn (σ i) * v i) +
          Real.exp (l * ∑ i, vcSgn (σ i) * (-v i))) := by
      intro σ
      obtain ⟨v, hvV, hXv⟩ := Finset.exists_mem_eq_sup' hV
        (fun v => |∑ i, vcSgn (σ i) * v i|)
      have hle : Real.exp (l * X σ) ≤ Real.exp (l * ∑ i, vcSgn (σ i) * v i) +
          Real.exp (l * ∑ i, vcSgn (σ i) * (-v i)) := by
        simp only [X, hXv, mul_neg, Finset.sum_neg_distrib]
        rcases abs_cases (∑ i, vcSgn (σ i) * v i) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
          (try simp only [mul_neg]) <;>
          linarith [Real.exp_pos (-(l * ∑ i, vcSgn (σ i) * v i)),
            Real.exp_pos (l * ∑ i, vcSgn (σ i) * v i)]
      refine hle.trans ?_
      exact Finset.single_le_sum (f := fun v => Real.exp (l * ∑ i, vcSgn (σ i) * v i) +
          Real.exp (l * ∑ i, vcSgn (σ i) * (-v i))) (fun _ _ => by positivity) hvV
    have hsum : ∑ σ, Real.exp (l * X σ) ≤ 2 * V.card * (2 ^ m * Real.exp (l ^ 2 * m / 2)) := by
      calc ∑ σ, Real.exp (l * X σ)
          ≤ ∑ σ : Fin m → Bool, ∑ v ∈ V, (Real.exp (l * ∑ i, vcSgn (σ i) * v i) +
              Real.exp (l * ∑ i, vcSgn (σ i) * (-v i))) := Finset.sum_le_sum fun σ _ => hpt σ
        _ = ∑ v ∈ V, (∑ σ : Fin m → Bool, Real.exp (l * ∑ i, vcSgn (σ i) * v i) +
              ∑ σ : Fin m → Bool, Real.exp (l * ∑ i, vcSgn (σ i) * (-v i))) := by
            rw [Finset.sum_comm]; simp_rw [Finset.sum_add_distrib]
        _ ≤ ∑ _v ∈ V, (2 ^ m * Real.exp (l ^ 2 * m / 2) + 2 ^ m * Real.exp (l ^ 2 * m / 2)) := by
            refine Finset.sum_le_sum fun v hv => add_le_add ?_ ?_
            · exact vcAux_sum_exp_le l v (hb v hv)
            · exact vcAux_sum_exp_le l (fun i => -v i) (fun i => by rw [abs_neg]; exact hb v hv i)
        _ = 2 * V.card * (2 ^ m * Real.exp (l ^ 2 * m / 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hexp : Real.exp (l * ((∑ σ, X σ) / 2 ^ m)) ≤ Real.exp (L + l ^ 2 * m / 2) := by
      refine hJ.trans ?_
      rw [div_le_iff₀ h2m, Real.exp_add, Real.exp_log (by linarith)]
      linarith
    have := Real.exp_le_exp.1 hexp
    rw [div_add_div _ _ hl.ne' (two_ne_zero), le_div_iff₀ (by positivity)]
    nlinarith
  set l := Real.sqrt (2 * L / m) with hl
  have hlpos : 0 < l := Real.sqrt_pos.2 (by positivity)
  have hl2 : l ^ 2 = 2 * L / m := Real.sq_sqrt (by positivity)
  refine (key l hlpos).trans (le_of_eq ?_)
  have hrhs : L / l + l * m / 2 = 2 * L / l := by
    field_simp
    rw [hl2]; field_simp; try ring
  rw [hrhs]
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  field_simp
  rw [hl2]; field_simp; try ring

end UnderstandingML

/-! Part 2 of the proof of Theorem 7.2: the Sauer–Shelah bound on the number of traces of a
finite class of VC-dimension at most `d` on `n` points. -/

open MeasureTheory

namespace UnderstandingML

/-- `∑_{k ≤ d} C(n, k) ≤ (n + 1)^d`. -/
theorem vcAux_sum_choose_le (n d : ℕ) :
    ∑ k ∈ Finset.Iic d, n.choose k ≤ (n + 1) ^ d := by
  rw [add_pow]
  simp only [one_pow, mul_one]
  have : Finset.Iic d = Finset.range (d + 1) := by
    ext k; simp
  rw [this]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  calc n.choose k ≤ n ^ k := Nat.choose_le_pow n k
    _ ≤ n ^ k * d.choose k := Nat.le_mul_of_pos_right _ (Nat.choose_pos hk')

/-- **Sauer–Shelah** for traces: a finite class all of whose shattered sets have at most `d`
elements has at most `(n + 1)^d` distinct traces on `n` points. -/
theorem vcAux_card_traces_le {X : Type*} [DecidableEq X] (F : Finset (X → Bool)) (d : ℕ)
    (hd : ∀ C : Finset X, Shatters (↑F : Set (X → Bool)) C → C.card ≤ d) {n : ℕ}
    (p : Fin n → X) :
    (F.image fun f => f ∘ p).card ≤ (n + 1) ^ d := by
  classical
  set T := F.image fun f => f ∘ p
  set 𝒜 : Finset (Finset (Fin n)) := T.image fun g => Finset.univ.filter fun i => g i = true
  have hinj : Function.Injective fun g : Fin n → Bool => Finset.univ.filter fun i => g i = true := by
    intro g g' h
    funext i
    have := congrArg (fun s => i ∈ s) h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hg : g i <;> cases hg' : g' i <;> simp_all
  have hcard : T.card = 𝒜.card := (Finset.card_image_of_injective T hinj).symm
  have hvc : 𝒜.vcDim ≤ d := by
    refine Finset.sup_le fun s hs => ?_
    rw [Finset.mem_shatterer] at hs
    -- `p` is injective on `s`
    have hpinj : Set.InjOn p s := by
      intro i hi j hj hij
      by_contra hne
      obtain ⟨u, hu𝒜, hsu⟩ := hs (t := {i}) (by simpa using hi)
      obtain ⟨g, hgT, rfl⟩ := Finset.mem_image.1 hu𝒜
      obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hgT
      have hi' : i ∈ s ∩ Finset.univ.filter fun k => (f ∘ p) k = true := by
        rw [hsu]; exact Finset.mem_singleton_self i
      have hj' : j ∈ s ∩ Finset.univ.filter fun k => (f ∘ p) k = true := by
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.comp] at hi' ⊢
        exact ⟨hj, hij ▸ hi'.2⟩
      rw [hsu, Finset.mem_singleton] at hj'
      exact hne hj'.symm
    -- the image of `s` is shattered by `F`
    have hsh : Shatters (↑F : Set (X → Bool)) (s.image p) := by
      intro g'
      let G : X → Bool := fun x => if hx : x ∈ s.image p then g' ⟨x, hx⟩ else false
      obtain ⟨u, hu𝒜, hsu⟩ := hs (t := s.filter fun i => G (p i) = true)
        (Finset.filter_subset _ _)
      obtain ⟨g, hgT, rfl⟩ := Finset.mem_image.1 hu𝒜
      obtain ⟨f, hfF, rfl⟩ := Finset.mem_image.1 hgT
      refine ⟨f, hfF, fun c => ?_⟩
      obtain ⟨c, hc⟩ := c
      obtain ⟨i, his, rfl⟩ := Finset.mem_image.1 hc
      have key : i ∈ s ∩ (Finset.univ.filter fun k => (f ∘ p) k = true) ↔
          i ∈ s.filter fun i => G (p i) = true := by rw [hsu]
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.comp, his] at key
      have hG : G (p i) = g' ⟨p i, hc⟩ := by simp only [G, dif_pos hc]
      rw [hG] at key
      cases hf : f (p i) <;> cases hg : g' ⟨p i, hc⟩ <;> simp_all
    have := hd _ hsh
    rwa [Finset.card_image_of_injOn hpinj] at this
  calc T.card = 𝒜.card := hcard
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card (Fin n)).choose k :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
        rw [Fintype.card_fin]
        exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.2 hvc)
    _ ≤ (n + 1) ^ d := vcAux_sum_choose_le n d

end UnderstandingML

/-! Part 3 of the proof of Theorem 7.2: symmetrization for a finite class of classifiers. -/

open MeasureTheory

namespace UnderstandingML

section Sym

variable {X : Type*} [MeasurableSpace X]

instance vcAux_iidLaw_isProb {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] (m : ℕ) : IsProbabilityMeasure (iidLaw D m) := by
  unfold iidLaw; infer_instance

theorem vcAux_loss01_measurable {f : X → Bool} (hf : Measurable f) :
    Measurable (loss01 f) := by
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd

theorem vcAux_loss01_mem (f : X → Bool) (z : X × Bool) : 0 ≤ loss01 f z ∧ loss01 f z ≤ 1 := by
  unfold loss01; split_ifs <;> norm_num

theorem vcAux_empRisk_measurable {f : X → Bool} (hf : Measurable f) (m : ℕ) :
    Measurable fun S : Fin m → X × Bool => empRisk loss01 S f := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _ fun i _ => (vcAux_loss01_measurable hf).comp (measurable_pi_apply i)

theorem vcAux_empRisk_bounds (f : X → Bool) {m : ℕ} (S : Fin m → X × Bool) :
    0 ≤ empRisk loss01 S f ∧ empRisk loss01 S f ≤ 1 := by
  unfold empRisk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (vcAux_loss01_mem f _).1) hmR.le
  · rw [div_le_one hmR]
    calc ∑ i, loss01 f (S i) ≤ ∑ _i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (vcAux_loss01_mem f _).2
      _ = m := by simp

/-- The expectation of the empirical risk is the risk. -/
theorem vcAux_integral_empRisk {f : X → Bool} (hf : Measurable f) (D : Measure (X × Bool))
    [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) :
    ∫ S, empRisk loss01 S f ∂(iidLaw D m) = risk loss01 D f := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hl := vcAux_loss01_measurable hf
  have hi : ∀ i : Fin m, ∫ S, loss01 f (S i) ∂(iidLaw D m) = risk loss01 D f := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin m => D) i
    unfold risk iidLaw
    rw [← integral_map (measurable_pi_apply i).aemeasurable
      (by rw [hmp.map_eq]; exact hl.aestronglyMeasurable), hmp.map_eq]
  unfold empRisk
  rw [integral_div, integral_finset_sum]
  · simp_rw [hi]; simp; field_simp
  · intro i _
    refine Integrable.of_bound (hl.comp (measurable_pi_apply i)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun S => ?_)
    have := vcAux_loss01_mem f (S i)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]

/-- The sample `S` with the coordinates in `σ` exchanged with `S'`. -/
def vcSwap {Z : Type*} {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → Z) × (Fin m → Z)) :
    (Fin m → Z) × (Fin m → Z) :=
  (fun i => if σ i then p.2 i else p.1 i, fun i => if σ i then p.1 i else p.2 i)

theorem vcAux_swap_measurePreserving {Z : Type*} [MeasurableSpace Z] (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (σ : Fin m → Bool) :
    MeasurePreserving (vcSwap σ) ((iidLaw D m).prod (iidLaw D m))
      ((iidLaw D m).prod (iidLaw D m)) := by
  classical
  let e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin m)
  have he : MeasurePreserving e (Measure.pi fun _ : Fin m => D.prod D)
      ((iidLaw D m).prod (iidLaw D m)) :=
    measurePreserving_arrowProdEquivProdArrow Z Z (Fin m) (fun _ => D) (fun _ => D)
  let swb : Bool → Z × Z → Z × Z := fun b q => if b then q.swap else q
  have hswb : ∀ b, MeasurePreserving (swb b) (D.prod D) (D.prod D) := by
    intro b
    cases b
    · exact MeasurePreserving.id (D.prod D)
    · simpa [swb] using (Measure.measurePreserving_swap (μ := D) (ν := D))
  have hphi : MeasurePreserving (fun w (i : Fin m) => swb (σ i) (w i))
      (Measure.pi fun _ : Fin m => D.prod D) (Measure.pi fun _ : Fin m => D.prod D) :=
    measurePreserving_pi _ _ fun i => hswb (σ i)
  have hcomp := (he.comp hphi).comp he.symm
  convert hcomp using 1
  funext q
  rcases q with ⟨S, S'⟩
  simp only [Function.comp, vcSwap]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    by_cases h : σ i = true <;> simp [h, swb, e, MeasurableEquiv.arrowProdEquivProdArrow]

/-- The two-sample deviation `max_f |L_S(f) − L_{S'}(f)|`. -/
noncomputable def vcDev2 (F : Finset (X → Bool)) (hF : F.Nonempty) {m : ℕ}
    (p : (Fin m → X × Bool) × (Fin m → X × Bool)) : ℝ :=
  F.sup' hF fun f => |empRisk loss01 p.1 f - empRisk loss01 p.2 f|

/-- The one-sample deviation `max_f |L_S(f) − L_D(f)|`. -/
noncomputable def vcDev1 (F : Finset (X → Bool)) (hF : F.Nonempty) (D : Measure (X × Bool))
    {m : ℕ} (S : Fin m → X × Bool) : ℝ :=
  F.sup' hF fun f => |empRisk loss01 S f - risk loss01 D f|

/-- The Rademacher bound for a fixed double sample. -/
theorem vcAux_rademacher_pointwise [DecidableEq X] (F : Finset (X → Bool)) (hF : F.Nonempty)
    (d : ℕ) (hd : ∀ C : Finset X, Shatters (↑F : Set (X → Bool)) C → C.card ≤ d) {m : ℕ}
    (hm : 0 < m) (p : (Fin m → X × Bool) × (Fin m → X × Bool)) :
    (∑ σ : Fin m → Bool, vcDev2 F hF (vcSwap σ p)) / 2 ^ m ≤
      Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m) := by
  classical
  obtain ⟨S, S'⟩ := p
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set a : (X → Bool) → Fin m → ℝ := fun f i => loss01 f (S i) - loss01 f (S' i) with ha
  set V := F.image a with hVdef
  have hV : V.Nonempty := hF.image a
  -- the swapped deviation is a Rademacher sum
  have hswap : ∀ σ : Fin m → Bool, vcDev2 F hF (vcSwap σ (S, S')) ≤
      V.sup' hV (fun v => |∑ i, vcSgn (σ i) * v i|) / m := by
    intro σ
    refine Finset.sup'_le _ _ fun f hf => ?_
    have heq : empRisk loss01 (vcSwap σ (S, S')).1 f - empRisk loss01 (vcSwap σ (S, S')).2 f =
        (∑ i, vcSgn (σ i) * a f i) / m := by
      simp only [empRisk, vcSwap, ha]
      rw [← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      cases σ i <;> simp [vcSgn]
    rw [heq, abs_div, abs_of_pos hmR]
    refine div_le_div_of_nonneg_right ?_ hmR.le
    exact Finset.le_sup' (fun v => |∑ i, vcSgn (σ i) * v i|) (Finset.mem_image_of_mem a hf)
  -- entries are bounded by one
  have hb : ∀ v ∈ V, ∀ i, |v i| ≤ 1 := by
    intro v hv i
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hv
    have h1 := vcAux_loss01_mem f (S i)
    have h2 := vcAux_loss01_mem f (S' i)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- Sauer–Shelah on the `2m` points
  let q : Fin (m + m) → X := Fin.append (fun i => (S i).1) (fun i => (S' i).1)
  let Ψ : (Fin (m + m) → Bool) → Fin m → ℝ := fun g i =>
    (if g (Fin.castAdd m i) = (S i).2 then 0 else 1) -
      (if g (Fin.natAdd m i) = (S' i).2 then 0 else 1)
  have hVeq : V = (F.image fun f => f ∘ q).image Ψ := by
    rw [Finset.image_image]
    refine Finset.image_congr fun f _ => ?_
    funext i
    simp only [Ψ, q, ha, loss01, Function.comp, Fin.append_left, Fin.append_right]
  have hcardV : (V.card : ℝ) ≤ (2 * m + 1) ^ d := by
    have h1 : V.card ≤ (m + m + 1) ^ d := by
      rw [hVeq]
      exact (Finset.card_image_le).trans (vcAux_card_traces_le F d hd q)
    have : ((m + m + 1 : ℕ) : ℝ) = 2 * m + 1 := by push_cast; ring
    calc (V.card : ℝ) ≤ ((m + m + 1) ^ d : ℕ) := by exact_mod_cast h1
      _ = (2 * m + 1) ^ d := by push_cast; ring
  have hVpos : (1 : ℝ) ≤ V.card := by exact_mod_cast hV.card_pos
  have hmass := vcAux_massart hm V hV hb
  calc (∑ σ : Fin m → Bool, vcDev2 F hF (vcSwap σ (S, S'))) / 2 ^ m
      ≤ (∑ σ : Fin m → Bool, V.sup' hV (fun v => |∑ i, vcSgn (σ i) * v i|) / m) / 2 ^ m := by
        gcongr with σ; exact hswap σ
    _ = ((∑ σ : Fin m → Bool, V.sup' hV (fun v => |∑ i, vcSgn (σ i) * v i|)) / 2 ^ m) / m := by
        rw [← Finset.sum_div]; ring
    _ ≤ Real.sqrt (2 * m * Real.log (2 * V.card)) / m := by gcongr
    _ ≤ Real.sqrt (2 * m * Real.log (2 * (2 * m + 1) ^ d)) / m := by
        gcongr
        all_goals first | positivity | linarith
    _ = Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m) := by
        have hL : 0 ≤ Real.log (2 * (2 * (m : ℝ) + 1) ^ d) :=
          Real.log_nonneg (by
            have : (1 : ℝ) ≤ (2 * m + 1) ^ d := one_le_pow₀ (by linarith)
            linarith)
        rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
        rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity)]
        field_simp

/-- Symmetrization: `E max_f |L_S(f) − L_D(f)| ≤ √(2 log(2(2m+1)^d)/m)`. -/
theorem vcAux_expected_dev_le (F : Finset (X → Bool)) (hF : F.Nonempty)
    (hFm : ∀ f ∈ F, Measurable f) (d : ℕ)
    (hd : ∀ C : Finset X, Shatters (↑F : Set (X → Bool)) C → C.card ≤ d)
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) :
    ∫ S, vcDev1 F hF D S ∂(iidLaw D m) ≤ Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m) := by
  classical
  set μ := iidLaw D m
  set R := Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m)
  have hER : ∀ f ∈ F, Measurable fun S : Fin m → X × Bool => empRisk loss01 S f :=
    fun f hf => vcAux_empRisk_measurable (hFm f hf) m
  have hG : Measurable (vcDev2 F hF (m := m)) := by
    have := Finset.measurable_sup' (α := ℝ) hF
      (f := fun f (p : (Fin m → X × Bool) × (Fin m → X × Bool)) =>
        |empRisk loss01 p.1 f - empRisk loss01 p.2 f|) fun f hf =>
      continuous_abs.measurable.comp
        (((hER f hf).comp measurable_fst).sub ((hER f hf).comp measurable_snd))
    convert this using 1
    funext p; rw [Finset.sup'_apply]; rfl
  have hGb : ∀ p, 0 ≤ vcDev2 F hF (m := m) p ∧ vcDev2 F hF (m := m) p ≤ 1 := by
    intro p
    obtain ⟨f, hf, hfeq⟩ := Finset.exists_mem_eq_sup' hF
      (fun f => |empRisk loss01 p.1 f - empRisk loss01 p.2 f|)
    unfold vcDev2; rw [hfeq]
    have h1 := vcAux_empRisk_bounds f p.1
    have h2 := vcAux_empRisk_bounds f p.2
    exact ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hbdd : ∀ {α : Type _} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
      (g : α → ℝ), Measurable g → (∀ a, 0 ≤ g a ∧ g a ≤ 1) → Integrable g ν :=
    fun ν _ g hg hgb => Integrable.of_bound hg.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgb a).1]; exact (hgb a).2)
  have hGint : Integrable (vcDev2 F hF (m := m)) (μ.prod μ) := hbdd _ _ hG hGb
  have hF1 : Measurable (vcDev1 F hF D (m := m)) := by
    have := Finset.measurable_sup' (α := ℝ) hF
      (f := fun f (S : Fin m → X × Bool) => |empRisk loss01 S f - risk loss01 D f|) fun f hf =>
      continuous_abs.measurable.comp ((hER f hf).sub_const _)
    convert this using 1
    funext S; rw [Finset.sup'_apply]; rfl
  have hrisk : ∀ f ∈ F, 0 ≤ risk loss01 D f ∧ risk loss01 D f ≤ 1 := by
    intro f hf
    rw [← vcAux_integral_empRisk (hFm f hf) D hm]
    exact ⟨integral_nonneg fun S => (vcAux_empRisk_bounds f S).1,
      (integral_mono (hbdd _ _ (hER f hf) fun S => vcAux_empRisk_bounds f S)
        (integrable_const (1 : ℝ)) fun S => (vcAux_empRisk_bounds f S).2).trans (by simp)⟩
  have hF1b : ∀ S, 0 ≤ vcDev1 F hF D (m := m) S ∧ vcDev1 F hF D (m := m) S ≤ 1 := by
    intro S
    obtain ⟨f, hf, hfeq⟩ := Finset.exists_mem_eq_sup' hF
      (fun f => |empRisk loss01 S f - risk loss01 D f|)
    unfold vcDev1; rw [hfeq]
    have h1 := vcAux_empRisk_bounds f S
    have h2 := hrisk f hf
    exact ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hF1int : Integrable (vcDev1 F hF D (m := m)) μ := hbdd _ _ hF1 hF1b
  have hsec : ∀ S, Integrable (fun S' => vcDev2 F hF (S, S')) μ :=
    fun S => hbdd _ _ (hG.comp measurable_prodMk_left) fun S' => hGb _
  -- step 1: replace the risk by an independent ghost sample
  have hstep1 : ∀ S, vcDev1 F hF D S ≤ ∫ S', vcDev2 F hF (S, S') ∂μ := by
    intro S
    unfold vcDev1
    refine Finset.sup'_le _ _ fun f hf => ?_
    have hint : Integrable (fun S' : Fin m → X × Bool => empRisk loss01 S' f) μ :=
      hbdd _ _ (hER f hf) fun S' => vcAux_empRisk_bounds f S'
    have heq : empRisk loss01 S f - risk loss01 D f =
        ∫ S', (empRisk loss01 S f - empRisk loss01 S' f) ∂μ := by
      rw [integral_sub (integrable_const _) hint, integral_const,
        vcAux_integral_empRisk (hFm f hf) D hm]
      simp
    rw [heq]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono ((integrable_const _).sub hint).abs (hsec S) fun S' => ?_
    exact Finset.le_sup' (fun f => |empRisk loss01 (S, S').1 f - empRisk loss01 (S, S').2 f|) hf
  -- step 2: symmetrize
  have hswapint : ∀ σ : Fin m → Bool,
      ∫ p, vcDev2 F hF (vcSwap σ p) ∂(μ.prod μ) = ∫ p, vcDev2 F hF p ∂(μ.prod μ) := by
    intro σ
    have hmp := vcAux_swap_measurePreserving D (m := m) σ
    rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hG.aestronglyMeasurable),
      hmp.map_eq]
  have hswapi : ∀ σ : Fin m → Bool, Integrable (fun p => vcDev2 F hF (vcSwap σ p)) (μ.prod μ) :=
    fun σ => hbdd _ _ (hG.comp (vcAux_swap_measurePreserving D (m := m) σ).measurable)
      fun p => hGb _
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hcard : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
  have hsym : ∫ p, vcDev2 F hF p ∂(μ.prod μ) =
      ∫ p, (∑ σ : Fin m → Bool, vcDev2 F hF (vcSwap σ p)) / 2 ^ m ∂(μ.prod μ) := by
    rw [integral_div, integral_finset_sum _ fun σ _ => hswapi σ]
    simp_rw [hswapint]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    field_simp
  calc ∫ S, vcDev1 F hF D S ∂μ
      ≤ ∫ S, ∫ S', vcDev2 F hF (S, S') ∂μ ∂μ :=
        integral_mono hF1int hGint.integral_prod_left hstep1
    _ = ∫ p, vcDev2 F hF p ∂(μ.prod μ) := (integral_prod _ hGint).symm
    _ = ∫ p, (∑ σ : Fin m → Bool, vcDev2 F hF (vcSwap σ p)) / 2 ^ m ∂(μ.prod μ) := hsym
    _ ≤ ∫ _p, R ∂(μ.prod μ) := by
        refine integral_mono ?_ (integrable_const R) fun p => ?_
        · exact (integrable_finset_sum _ fun σ _ => hswapi σ).div_const _
        · exact vcAux_rademacher_pointwise F hF d hd hm p
    _ = R := by simp

/-- The finite-class uniform deviation bound in probability (Markov). -/
theorem vcAux_finite_class_bound (F : Finset (X → Bool)) (hFm : ∀ f ∈ F, Measurable f) (d : ℕ)
    (hd : ∀ C : Finset X, Shatters (↑F : Set (X → Bool)) C → C.card ≤ d)
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) :
    iidLaw D m {S | ∃ f ∈ F, ε < |empRisk loss01 S f - risk loss01 D f|} ≤
      ENNReal.ofReal (Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m) / ε) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  set μ := iidLaw D m
  have hER : ∀ f ∈ F, Measurable fun S : Fin m → X × Bool => empRisk loss01 S f :=
    fun f hf => vcAux_empRisk_measurable (hFm f hf) m
  have hF1 : Measurable (vcDev1 F hF D (m := m)) := by
    have := Finset.measurable_sup' (α := ℝ) hF
      (f := fun f (S : Fin m → X × Bool) => |empRisk loss01 S f - risk loss01 D f|) fun f hf =>
      continuous_abs.measurable.comp ((hER f hf).sub_const _)
    convert this using 1
    funext S; rw [Finset.sup'_apply]; rfl
  have hrisk : ∀ f ∈ F, 0 ≤ risk loss01 D f ∧ risk loss01 D f ≤ 1 := by
    intro f hf
    have hint : Integrable (fun S : Fin m → X × Bool => empRisk loss01 S f) μ :=
      Integrable.of_bound (hER f hf).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun S => by
          rw [Real.norm_eq_abs, abs_of_nonneg (vcAux_empRisk_bounds f S).1]
          exact (vcAux_empRisk_bounds f S).2)
    rw [← vcAux_integral_empRisk (hFm f hf) D hm]
    exact ⟨integral_nonneg fun S => (vcAux_empRisk_bounds f S).1,
      (integral_mono hint (integrable_const (1 : ℝ))
        fun S => (vcAux_empRisk_bounds f S).2).trans (by simp)⟩
  have hF1b : ∀ S, 0 ≤ vcDev1 F hF D (m := m) S ∧ vcDev1 F hF D (m := m) S ≤ 1 := by
    intro S
    obtain ⟨f, hf, hfeq⟩ := Finset.exists_mem_eq_sup' hF
      (fun f => |empRisk loss01 S f - risk loss01 D f|)
    unfold vcDev1; rw [hfeq]
    have h1 := vcAux_empRisk_bounds f S
    have h2 := hrisk f hf
    exact ⟨abs_nonneg _, by rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hF1int : Integrable (vcDev1 F hF D (m := m)) μ :=
    Integrable.of_bound hF1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun S => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF1b S).1]; exact (hF1b S).2)
  have hsub : {S : Fin m → X × Bool | ∃ f ∈ F, ε < |empRisk loss01 S f - risk loss01 D f|} ⊆
      {S : Fin m → X × Bool | ε ≤ vcDev1 F hF D S} := by
    rintro S ⟨f, hf, hlt⟩
    exact hlt.le.trans (Finset.le_sup' (fun f => |empRisk loss01 S f - risk loss01 D f|) hf)
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun S => (hF1b S).1) hF1int ε
  have hexp := vcAux_expected_dev_le F hF hFm d hd D hm
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hε, mul_comm]
  exact hmk.trans hexp

end Sym

end UnderstandingML

/-! Part 4 of the proof of Theorem 7.2: a pointwise separable class of measurable classifiers
all of whose shattered sets have at most `d` points has the uniform convergence property. -/

open MeasureTheory

namespace UnderstandingML

/-- The explicit rate: for `m ≥ ⌈((2 + 8d)/(εδ)²)²⌉ + 1` the finite-class bound is at most `δ`. -/
theorem vcAux_rate_le (d : ℕ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : ⌈((2 + 8 * d) / (ε * δ) ^ 2) ^ 2⌉₊ + 1 ≤ m) :
    Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m) / ε ≤ δ := by
  set c := ε * δ with hc
  have hcpos : 0 < c := mul_pos hε hδ
  set K := (2 + 8 * (d : ℝ)) / c ^ 2 with hK
  have hKnn : 0 ≤ K := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hmK : K ^ 2 < m := by
    have h1 : K ^ 2 ≤ ⌈K ^ 2⌉₊ := Nat.le_ceil _
    have h2 : ((⌈K ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at h2; linarith
  have hsqrtm : K < Real.sqrt m := (Real.lt_sqrt hKnn).2 hmK
  have hs1 : 1 ≤ Real.sqrt m := by rw [Real.one_le_sqrt]; exact hm1
  have hspos : 0 < Real.sqrt m := by linarith
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmpos.le
  -- bound on the logarithm
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlogm : Real.log (2 * m + 1) ≤ 4 * Real.sqrt m := by
    have h := Real.log_le_rpow_div (x := 2 * m + 1) (by positivity) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    have h2 : Real.sqrt (2 * m + 1) ≤ 2 * Real.sqrt m := by
      rw [show (2 : ℝ) * Real.sqrt m = Real.sqrt (4 * m) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hL : Real.log (2 * (2 * m + 1) ^ d) ≤ (1 + 4 * d) * Real.sqrt m := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have : (d : ℝ) * Real.log (2 * m + 1) ≤ d * (4 * Real.sqrt m) :=
      mul_le_mul_of_nonneg_left hlogm (Nat.cast_nonneg d)
    nlinarith
  have hQ : 2 * Real.log (2 * (2 * m + 1) ^ d) / m ≤ c ^ 2 := by
    rw [div_le_iff₀ hmpos]
    have hKc : 2 + 8 * (d : ℝ) ≤ c ^ 2 * Real.sqrt m := by
      have := mul_lt_mul_of_pos_left hsqrtm (by positivity : (0 : ℝ) < c ^ 2)
      rw [hK, mul_div_cancel₀ _ (by positivity)] at this
      linarith
    have h1 := mul_le_mul_of_nonneg_right hKc hspos.le
    have h2 : c ^ 2 * Real.sqrt m * Real.sqrt m = c ^ 2 * m := by
      rw [mul_assoc, hsq]
    nlinarith
  rw [div_le_iff₀ hε]
  calc Real.sqrt (2 * Real.log (2 * (2 * m + 1) ^ d) / m) ≤ Real.sqrt (c ^ 2) :=
        Real.sqrt_le_sqrt hQ
    _ = c := Real.sqrt_sq hcpos.le
    _ = δ * ε := by rw [hc]; ring

/-- **Finite VC-dimension implies uniform convergence** (the uniform convergence part of the
fundamental theorem, under the measurability assumption of pointwise separability). -/
theorem vcAux_uc_of_shatter_le {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ)
    (hd : ∀ C : Finset X, Shatters H C → C.card ≤ d) :
    HasUniformConvergenceWith loss01 H
      (fun ε δ => ⌈((2 + 8 * d) / (ε * δ) ^ 2) ^ 2⌉₊ + 1) := by
  classical
  intro ε δ hε0 hε1 hδ0 hδ1 D hD m hm
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.succ_pos _) hm
  obtain ⟨H₀, hH₀H, hH₀c, happrox⟩ := hsep
  rcases H₀.eq_empty_or_nonempty with hH₀e | hH₀ne
  · -- then `H` is empty
    have hHe : ∀ h ∈ H, False := by
      intro h hh
      obtain ⟨u, hu, -⟩ := happrox h hh
      have := hu 0; rw [hH₀e] at this; exact this
    have : {S : Fin m → X × Bool | ¬ IsRepresentative loss01 H D ε S} = ∅ := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro h hh; exact (hHe h hh).elim
    rw [this, measure_empty]; exact bot_le
  obtain ⟨e, he⟩ := hH₀c.exists_eq_range hH₀ne
  set FJ : ℕ → Finset (X → Bool) := fun J => (Finset.range J).image e
  have hFJH : ∀ J, ∀ f ∈ FJ J, f ∈ H := by
    intro J f hf
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hf
    exact hH₀H (he ▸ Set.mem_range_self j)
  have hFJm : ∀ J, ∀ f ∈ FJ J, Measurable f := fun J f hf => hH f (hFJH J f hf)
  have hFJd : ∀ J, ∀ C : Finset X, Shatters (↑(FJ J) : Set (X → Bool)) C → C.card ≤ d := by
    intro J C hC
    refine hd C fun g => ?_
    obtain ⟨h, hh, hhg⟩ := hC g
    exact ⟨h, hFJH J h hh, hhg⟩
  set B : ℕ → Set (Fin m → X × Bool) := fun J =>
    {S | ∃ f ∈ FJ J, ε < |empRisk loss01 S f - risk loss01 D f|}
  have hBmono : Monotone B := by
    intro J J' hJJ' S ⟨f, hf, hlt⟩
    refine ⟨f, ?_, hlt⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hf
    exact Finset.mem_image_of_mem e (Finset.mem_range.2 (lt_of_lt_of_le
      (Finset.mem_range.1 hj) hJJ'))
  -- every bad sample for `H` is bad for some finite `F_J`
  have hsub : {S : Fin m → X × Bool | ¬ IsRepresentative loss01 H D ε S} ⊆ ⋃ J, B J := by
    intro S hS
    simp only [Set.mem_setOf_eq, IsRepresentative, not_forall, not_le] at hS
    obtain ⟨h, hh, hlt⟩ := hS
    obtain ⟨u, huH₀, hu⟩ := happrox h hh
    -- the empirical risks agree eventually
    have hev : ∀ᶠ n in Filter.atTop, ∀ i : Fin m, u n (S i).1 = h (S i).1 := by
      rw [Filter.eventually_all]
      intro i
      obtain ⟨N, hN⟩ := hu (S i).1
      exact Filter.eventually_atTop.2 ⟨N, hN⟩
    have hemp : Filter.Tendsto (fun n => empRisk loss01 S (u n)) Filter.atTop
        (nhds (empRisk loss01 S h)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp only [empRisk, loss01, hn]
    -- the risks converge by dominated convergence
    have hrisk : Filter.Tendsto (fun n => risk loss01 D (u n)) Filter.atTop
        (nhds (risk loss01 D h)) := by
      unfold risk
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun n => (vcAux_loss01_measurable (hH _ (hH₀H (huH₀ n)))).aestronglyMeasurable)
        (integrable_const _) (fun n => Filter.Eventually.of_forall fun z => ?_)
        (Filter.Eventually.of_forall fun z => ?_)
      · have := vcAux_loss01_mem (u n) z
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
      · refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := hu z.1
        filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with n hn
        simp only [loss01, hn]
    have hlim : Filter.Tendsto (fun n => |empRisk loss01 S (u n) - risk loss01 D (u n)|)
        Filter.atTop (nhds |empRisk loss01 S h - risk loss01 D h|) :=
      (hemp.sub hrisk).abs
    obtain ⟨n, hn⟩ := (hlim.eventually_const_lt hlt).exists
    obtain ⟨j, hj⟩ : u n ∈ Set.range e := he ▸ huH₀ n
    refine Set.mem_iUnion.2 ⟨j + 1, u n, ?_, hn⟩
    rw [← hj]
    exact Finset.mem_image_of_mem e (Finset.mem_range.2 (Nat.lt_succ_self j))
  calc iidLaw D m {S | ¬ IsRepresentative loss01 H D ε S}
      ≤ iidLaw D m (⋃ J, B J) := measure_mono hsub
    _ = ⨆ J, iidLaw D m (B J) := hBmono.measure_iUnion
    _ ≤ ENNReal.ofReal δ := by
        refine iSup_le fun J => ?_
        refine (vcAux_finite_class_bound (FJ J) (hFJm J) d (hFJd J) D hmpos hε0).trans ?_
        exact ENNReal.ofReal_le_ofReal (vcAux_rate_le d hε0 hδ0 hm)

end UnderstandingML

/-! Part 5 of the proof of Theorem 7.2: the No-Free-Lunch theorem transported to a shattered
finite set. -/

open MeasureTheory

namespace UnderstandingML

/-- Any real function is a.e. strongly measurable for the pushforward of a measure on a
countable type with measurable singletons. -/
theorem vcAux_aesm_map_countable {α β : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β] (φ : α → β)
    (μ : Measure α) (g : β → ℝ) : AEStronglyMeasurable g (μ.map φ) := by
  rw [← Measure.sum_smul_dirac μ, Measure.map_sum (measurable_of_countable φ).aemeasurable]
  have hφ : Measurable φ := measurable_of_countable φ
  have hd : ∀ a, (Measure.dirac a).map φ = Measure.dirac (φ a) := fun a => by
    first
    | exact Measure.map_dirac' hφ a
    | exact Measure.map_dirac hφ a
  simp only [Measure.map_smul, hd]
  rw [aestronglyMeasurable_sum_measure_iff]
  intro a
  exact aestronglyMeasurable_dirac.smul_measure _

/-- **No-Free-Lunch on a shattered set.** If `H'` shatters a finite set `C` with more than `2m`
points, then for every learner there is a distribution realized by some `h ∈ H'` under which the
learner has risk at least `1/8` with probability at least `1/7`. -/
theorem vcAux_nfl_shatter {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Learner (X × Bool) (X → Bool)) (H' : Set (X → Bool)) (C : Finset X)
    (hC : Shatters H' C) (m : ℕ) (hm : 2 * m < C.card) :
    ∃ D : Measure (X × Bool), IsProbabilityMeasure D ∧ (∃ h ∈ H', risk loss01 D h = 0) ∧
      ENNReal.ofReal (1 / 7) ≤ iidLaw D m {S | 1 / 8 ≤ risk loss01 D (A m S)} := by
  classical
  letI : MeasurableSpace C := ⊤
  haveI : MeasurableSingletonClass C := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  let A' : Learner (C × Bool) (C → Bool) :=
    fun m S c => A m (fun i => (((S i).1 : X), (S i).2)) c
  have hm' : (2 * m : ℕ∞) < ENat.card C := by
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]; exact_mod_cast hm
  obtain ⟨D', hD', ⟨f', -, hf'⟩, E', -, hE'sub, hE'⟩ := no_free_lunch A' m hm'
  let φ : C × Bool → X × Bool := fun p => ((p.1 : X), p.2)
  have hφ : Measurable φ := measurable_of_countable φ
  let D := D'.map φ
  haveI hD : IsProbabilityMeasure D := Measure.isProbabilityMeasure_map hφ.aemeasurable
  -- risks transport
  have hrisk : ∀ h : X → Bool, risk loss01 D h = risk loss01 D' (fun c : C => h c) := by
    intro h
    unfold risk
    rw [integral_map hφ.aemeasurable (vcAux_aesm_map_countable φ D' _)]
    rfl
  refine ⟨D, hD, ?_, ?_⟩
  · obtain ⟨h, hh, hhf⟩ := hC f'
    refine ⟨h, hh, ?_⟩
    rw [hrisk]
    convert hf' using 2
    funext c; exact hhf c
  · let Φ : (Fin m → C × Bool) → (Fin m → X × Bool) := fun S i => φ (S i)
    have hΦ : Measurable Φ := measurable_of_countable Φ
    have hlaw : iidLaw D m = (iidLaw D' m).map Φ := by
      unfold iidLaw
      exact (Measure.pi_map_pi (fun _ => hφ.aemeasurable)).symm
    rw [hlaw]
    refine hE'.trans ((measure_mono ?_).trans (Measure.le_map_apply hΦ.aemeasurable _))
    intro S hS
    have := hE'sub hS
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at this ⊢
    rw [hrisk]
    exact this

end UnderstandingML

open MeasureTheory

namespace UnderstandingML

/-- If a learner fails with probability at most `1/8` at accuracy `1/16` on `m` samples for every
realizable distribution, then every set shattered by the class has at most `2m` points. -/
theorem vcAux_shatter_le_of_learner {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (A : Learner (X × Bool) (X → Bool)) (H' : Set (X → Bool)) (m : ℕ)
    (hA : ∀ D : Measure (X × Bool), IsProbabilityMeasure D → ∀ h ∈ H', risk loss01 D h = 0 →
      iidLaw D m {S | risk loss01 D h + 1 / 16 < risk loss01 D (A m S)} ≤ ENNReal.ofReal (1 / 8))
    (C : Finset X) (hC : Shatters H' C) : C.card ≤ 2 * m := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨D, hD, ⟨h, hh, h0⟩, hbad⟩ := vcAux_nfl_shatter A H' C hC m hlt
  have hsub : {S : Fin m → X × Bool | 1 / 8 ≤ risk loss01 D (A m S)} ⊆
      {S | risk loss01 D h + 1 / 16 < risk loss01 D (A m S)} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS ⊢
    rw [h0]; linarith
  have := hbad.trans ((measure_mono hsub).trans (hA D hD h hh h0))
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

/-- An ERM learner exists for the 0–1 loss over any nonempty class. -/
theorem vcAux_erm_exists {X : Type*} [MeasurableSpace X] (H' : Set (X → Bool))
    (hne : H'.Nonempty) : ∃ A : Learner (X × Bool) (X → Bool), IsERMLearner loss01 H' A := by
  classical
  have key : ∀ (m : ℕ) (S : Fin m → X × Bool), ∃ h, IsERM loss01 H' S h := by
    intro m S
    set V := (fun h => empRisk loss01 S h) '' H' with hV
    have hfin : V.Finite := by
      refine (Set.finite_range (fun g : Fin m → Bool =>
        (∑ i, (if g i = (S i).2 then (0 : ℝ) else 1)) / m)).subset ?_
      rintro _ ⟨h, -, rfl⟩
      exact ⟨fun i => h (S i).1, rfl⟩
    obtain ⟨v, hv, hmin⟩ := Set.exists_min_image V id hfin (hne.image _)
    obtain ⟨h, hh, rfl⟩ := hv
    exact ⟨h, hh, fun h' hh' => hmin _ ⟨h', hh', rfl⟩⟩
  choose A hA using key
  exact ⟨A, hA⟩

/-- A nonempty, measurable, pointwise separable class whose shattered sets are bounded in size is
agnostic PAC learnable. -/
theorem vcAux_apac_of_shatter_le {X : Type*} [MeasurableSpace X] (H' : Set (X → Bool))
    (hne : H'.Nonempty) (hH : ∀ h ∈ H', Measurable h) (hsep : PointwiseSeparable H') (d : ℕ)
    (hd : ∀ C : Finset X, Shatters H' C → C.card ≤ d) : AgnosticPACLearnable loss01 H' :=
  (uc_implies_agnostic_pac loss01 H' _ (vcAux_uc_of_shatter_le H' hH hsep d hd)).2
    (vcAux_erm_exists H' hne)

/-- An agnostic PAC learnable, measurable, pointwise separable class has the uniform convergence
property. -/
theorem vcAux_uc_of_apac {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (H' : Set (X → Bool)) (hH : ∀ h ∈ H', Measurable h) (hsep : PointwiseSeparable H')
    (hA : AgnosticPACLearnable loss01 H') : HasUniformConvergence loss01 H' := by
  obtain ⟨mH, A, -, hA⟩ := hA
  refine ⟨_, vcAux_uc_of_shatter_le H' hH hsep (2 * mH (1 / 16) (1 / 8)) ?_⟩
  refine vcAux_shatter_le_of_learner A H' _ ?_
  intro D hD h hh _
  refine le_trans (measure_mono ?_) (hA (1 / 16) (1 / 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D hD _ le_rfl)
  intro S hS
  exact ⟨h, hh, hS⟩

/-- **Theorem 7.2.** -/
theorem vcAux_main {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (H : Set (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    (hsep : ∀ H' ⊆ H, PointwiseSeparable H') :
    NonuniformLearnable loss01 H ↔
      ∃ Hn : ℕ → Set (X → Bool), (⋃ n, Hn n) = H ∧
        ∀ n, AgnosticPACLearnable loss01 (Hn n) := by
  classical
  constructor
  · rintro ⟨A, mNUL, hAH, hA⟩
    have h₀H : A 0 default ∈ H := hAH 0 default
    set h₀ := A 0 default
    set M : ℕ → ℕ := fun n => max n (mNUL (1 / 16) (1 / 8) h₀) with hM
    let Hn : ℕ → Set (X → Bool) := fun n => {h | h ∈ H ∧ mNUL (1 / 16) (1 / 8) h ≤ M n}
    have hHnH : ∀ n, Hn n ⊆ H := fun n h hh => hh.1
    refine ⟨Hn, ?_, fun n => ?_⟩
    · ext h
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩; exact hn.1
      · intro hh
        exact ⟨mNUL (1 / 16) (1 / 8) h, hh, le_max_left _ _⟩
    · refine vcAux_apac_of_shatter_le (Hn n) ⟨h₀, h₀H, le_max_right _ _⟩
        (fun h hh => hH h (hHnH n hh)) (hsep _ (hHnH n)) (2 * M n) ?_
      refine vcAux_shatter_le_of_learner A (Hn n) (M n) ?_
      intro D hD h hh _
      exact hA (1 / 16) (1 / 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hh.1
        D hD (M n) hh.2
  · rintro ⟨Hn, hU, hAP⟩
    have hHnH : ∀ n, Hn n ⊆ H := fun n => hU ▸ Set.subset_iUnion Hn n
    have hne : (⋃ n, Hn n).Nonempty := by
      obtain ⟨_, A, hA, -⟩ := hAP 0
      exact ⟨A 0 default, Set.mem_iUnion.2 ⟨0, hA 0 default⟩⟩
    have := nuAux_main loss01 Hn hne fun n =>
      vcAux_uc_of_apac (Hn n) (fun h hh => hH h (hHnH n hh)) (hsep _ (hHnH n)) (hAP n)
    rwa [hU] at this

end UnderstandingML

/-- **Theorem 7.2** (p. 84). -/
theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (H : Set (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    (hsep : ∀ H' ⊆ H, UnderstandingML.PointwiseSeparable H') :
    UnderstandingML.NonuniformLearnable UnderstandingML.loss01 H ↔
      ∃ Hn : ℕ → Set (X → Bool), (⋃ n, Hn n) = H ∧
        ∀ n, UnderstandingML.AgnosticPACLearnable UnderstandingML.loss01 (Hn n) :=
  UnderstandingML.vcAux_main H hH hsep
