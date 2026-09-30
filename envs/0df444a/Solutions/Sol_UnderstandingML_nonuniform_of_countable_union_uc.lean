-- Prove2me | solution 1 for UnderstandingML.nonuniform_of_countable_union_uc
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:12:31.707604+00:00
-- url     : https://prove2.me/submissions/915b80ee-a4e7-44b0-bd71-93f014d2bd84

import Definitions.Def_UnderstandingML_Nonuniform

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

/-- **Theorem 7.3** (p. 85). -/
theorem solution {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp) (hne : (⋃ n, Hn n).Nonempty)
    (hUC : ∀ n, UnderstandingML.HasUniformConvergence loss (Hn n)) :
    UnderstandingML.NonuniformLearnable loss (⋃ n, Hn n) :=
  UnderstandingML.nuAux_main loss Hn hne hUC
