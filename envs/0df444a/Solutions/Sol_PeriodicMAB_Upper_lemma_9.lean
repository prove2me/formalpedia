-- Prove2me | solution 1 for PeriodicMAB.Upper.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:55:52.640991+00:00
-- url     : https://prove2.me/submissions/efc1e798-b135-446b-9f58-f57d2192b6c1

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal
open PeriodicMAB.Upper

/-! ## Part 1: an exponential supermartingale for predictably selected noise -/

section Supermart

variable (σ : ℝ≥0) (c : ℕ → (ℕ → ℝ) → Bool)

noncomputable def pm9S (J : ℕ) (e : ℕ → ℝ) : ℝ := ∑ j ∈ Icc 1 J, (if c j e then e j else 0)
noncomputable def pm9C (J : ℕ) (e : ℕ → ℝ) : ℝ := ∑ j ∈ Icc 1 J, (if c j e then (1 : ℝ) else 0)
noncomputable def pm9Z (lam : ℝ) (J : ℕ) (e : ℕ → ℝ) : ℝ :=
  Real.exp (lam * pm9S c J e - lam ^ 2 * (σ : ℝ) ^ 2 / 2 * pm9C c J e)

lemma pm9_meas_set (hc : ∀ j, MeasurableSet {e | c j e = true}) (j : ℕ) :
    Measurable (fun e => if c j e then (1 : ℝ) else 0) := by
  have : (fun e => if c j e then (1 : ℝ) else 0) = Set.indicator {e | c j e = true} (fun _ => 1) := by
    ext e; simp [Set.indicator]
  rw [this]; exact measurable_const.indicator (hc j)

lemma pm9_meas_S (hc : ∀ j, MeasurableSet {e | c j e = true}) (J : ℕ) :
    Measurable (pm9S c J) := by
  unfold pm9S
  apply Finset.measurable_sum
  intro j _
  have : (fun e : ℕ → ℝ => if c j e then e j else 0) =
      fun e => (if c j e then (1 : ℝ) else 0) * e j := by
    ext e; split_ifs <;> simp
  rw [this]
  exact (pm9_meas_set c hc j).mul (measurable_pi_apply j)

lemma pm9_meas_C (hc : ∀ j, MeasurableSet {e | c j e = true}) (J : ℕ) :
    Measurable (pm9C c J) := by
  unfold pm9C
  exact Finset.measurable_sum _ (fun j _ => pm9_meas_set c hc j)

lemma pm9_meas_Z (hc : ∀ j, MeasurableSet {e | c j e = true}) (lam : ℝ) (J : ℕ) :
    Measurable (pm9Z σ c lam J) := by
  unfold pm9Z
  exact Real.measurable_exp.comp (((pm9_meas_S c hc J).const_mul _).sub
    ((pm9_meas_C c hc J).const_mul _))

lemma pm9_loc_Z (hloc : ∀ j e e', (∀ i < j, e i = e' i) → c j e = c j e') (lam : ℝ) (J : ℕ)
    (e e' : ℕ → ℝ) (he : ∀ i ≤ J, e i = e' i) : pm9Z σ c lam J e = pm9Z σ c lam J e' := by
  have hcj : ∀ j ∈ Icc 1 J, c j e = c j e' := fun j hj =>
    hloc j e e' (fun i hi => he i (by rw [Finset.mem_Icc] at hj; omega))
  have hS : pm9S c J e = pm9S c J e' := by
    unfold pm9S
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcj j hj, he j (Finset.mem_Icc.mp hj).2]
  have hC : pm9C c J e = pm9C c J e' := by
    unfold pm9C
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcj j hj]
  unfold pm9Z
  rw [hS, hC]

lemma pm9_Z_succ (lam : ℝ) (J : ℕ) (e : ℕ → ℝ) :
    pm9Z σ c lam (J + 1) e = pm9Z σ c lam J e *
      (if c (J + 1) e then Real.exp (lam * e (J + 1) - lam ^ 2 * (σ : ℝ) ^ 2 / 2) else 1) := by
  unfold pm9Z pm9S pm9C
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  split_ifs with h
  · rw [← Real.exp_add]; congr 1; ring
  · simp

/-- The supermartingale bound `E[Z_J] ≤ 1`. -/
lemma pm9_lintegral_Z {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hind : iIndepFun ε P) (hX : ∀ t, HasSubgaussianMGF (ε t) (σ ^ 2) P)
    (hc : ∀ j, MeasurableSet {e | c j e = true})
    (hloc : ∀ j e e', (∀ i < j, e i = e' i) → c j e = c j e') (lam : ℝ) :
    ∀ J, ∫⁻ ω, ENNReal.ofReal (pm9Z σ c lam J (fun i => ε i ω)) ∂P ≤ 1 := by
  have hεm : ∀ i, AEMeasurable (ε i) P := fun i => (hX i).aemeasurable
  have hpath : AEMeasurable (fun ω => (fun i => ε i ω)) P := aemeasurable_pi_lambda _ hεm
  intro J
  induction J with
  | zero =>
    simp [pm9Z, pm9S, pm9C]
  | succ J ih =>
    set Z := fun ω => ENNReal.ofReal (pm9Z σ c lam J (fun i => ε i ω)) with hZ
    set b := fun ω => c (J + 1) (fun i => ε i ω) with hb
    set G := fun ω => ENNReal.ofReal (Real.exp (lam * ε (J + 1) ω)) with hG
    set κ := ENNReal.ofReal (Real.exp (-(lam ^ 2 * (σ : ℝ) ^ 2 / 2))) with hκ
    have hsplit : (fun ω => ENNReal.ofReal (pm9Z σ c lam (J + 1) (fun i => ε i ω))) =
        fun ω => (if b ω then 0 else Z ω) + κ * ((if b ω then Z ω else 0) * G ω) := by
      ext ω
      rw [pm9_Z_succ]
      simp only [hb, hZ, hG, hκ]
      split_ifs with h
      · have hz : 0 ≤ pm9Z σ c lam J (fun i => ε i ω) := (Real.exp_pos _).le
        rw [zero_add, ENNReal.ofReal_mul hz, sub_eq_add_neg, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
      · simp
    -- measurability
    have hZm : AEMeasurable Z P :=
      (ENNReal.measurable_ofReal.comp (pm9_meas_Z σ c hc lam J)).comp_aemeasurable hpath
    have hbm : MeasurableSet {e : ℕ → ℝ | c (J + 1) e = true} := hc (J + 1)
    have hF1 : AEMeasurable (fun ω => if b ω then 0 else Z ω) P := by
      have : (fun ω => if b ω then 0 else Z ω) =
          fun ω => ((fun e : ℕ → ℝ => if c (J + 1) e then (0 : ℝ≥0∞) else
            ENNReal.ofReal (pm9Z σ c lam J e))) (fun i => ε i ω) := by
        ext ω; rfl
      rw [this]
      exact (Measurable.ite hbm measurable_const
        (ENNReal.measurable_ofReal.comp (pm9_meas_Z σ c hc lam J))).comp_aemeasurable hpath
    -- independence of the past and the new noise
    set S := Finset.range (J + 1) with hS
    have hdisj : Disjoint S {J + 1} := by
      rw [Finset.disjoint_singleton_right, hS, Finset.mem_range]; omega
    have hind2 := hind.indepFun_finset₀ S {J + 1} hdisj hεm
    set ext : (S → ℝ) → (ℕ → ℝ) := fun x i => if h : i ∈ S then x ⟨i, h⟩ else 0 with hext
    have hextm : Measurable ext := by
      apply measurable_pi_lambda
      intro i
      by_cases h : i ∈ S
      · simp only [hext, h, dif_pos]; exact measurable_pi_apply _
      · simp only [hext, h, dif_neg, not_false_eq_true]; exact measurable_const
    set φ : (S → ℝ) → ℝ≥0∞ := fun x =>
      if c (J + 1) (ext x) then ENNReal.ofReal (pm9Z σ c lam J (ext x)) else 0 with hφ
    have hφm : Measurable φ := by
      apply Measurable.ite (hextm hbm) _ measurable_const
      exact (ENNReal.measurable_ofReal.comp (pm9_meas_Z σ c hc lam J)).comp hextm
    set ψ : (({J + 1} : Finset ℕ) → ℝ) → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (Real.exp (lam * y ⟨J + 1, Finset.mem_singleton_self _⟩)) with hψ
    have hψm : Measurable ψ := by
      apply ENNReal.measurable_ofReal.comp
      exact Real.measurable_exp.comp ((measurable_pi_apply _).const_mul _)
    have hindφψ := hind2.comp hφm hψm
    have hF2eq : (fun ω => if b ω then Z ω else 0) = φ ∘ (fun ω (i : S) => ε i ω) := by
      ext ω
      simp only [Function.comp, hφ, hb, hZ]
      have hpe : ∀ i ≤ J, (fun i => ε i ω) i = ext (fun (i : S) => ε i ω) i := by
        intro i hi
        have : i ∈ S := by rw [hS, Finset.mem_range]; omega
        simp [hext, this]
      have h1 : c (J + 1) (fun i => ε i ω) = c (J + 1) (ext (fun (i : S) => ε i ω)) :=
        hloc (J + 1) _ _ (fun i hi => hpe i (by omega))
      have h2 := pm9_loc_Z σ c hloc lam J _ _ hpe
      rw [h1, h2]
    have hGeq : G = ψ ∘ (fun ω (i : ({J + 1} : Finset ℕ)) => ε i ω) := by
      ext ω; rfl
    have hF2m : AEMeasurable (fun ω => if b ω then Z ω else 0) P := by
      rw [hF2eq]; exact hφm.comp_aemeasurable (aemeasurable_pi_lambda _ (fun i => hεm i))
    have hGm : AEMeasurable G P := by
      rw [hGeq]; exact hψm.comp_aemeasurable (aemeasurable_pi_lambda _ (fun i => hεm i))
    have hmul : ∫⁻ ω, (fun ω => if b ω then Z ω else 0) ω * G ω ∂P =
        (∫⁻ ω, (if b ω then Z ω else 0) ∂P) * ∫⁻ ω, G ω ∂P := by
      have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' hF2m hGm
        (by rw [hF2eq, hGeq]; exact hindφψ)
      simpa using this
    -- the mgf bound
    have hGint : ∫⁻ ω, G ω ∂P ≤ ENNReal.ofReal (Real.exp ((σ : ℝ) ^ 2 * lam ^ 2 / 2)) := by
      rw [hG, ← ofReal_integral_eq_lintegral_ofReal ((hX (J + 1)).integrable_exp_mul lam)
        (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
      apply ENNReal.ofReal_le_ofReal
      have := (hX (J + 1)).mgf_le lam
      simp only [mgf] at this
      push_cast at this
      exact this
    have hκG : κ * ∫⁻ ω, G ω ∂P ≤ 1 := by
      calc κ * ∫⁻ ω, G ω ∂P ≤ κ * ENNReal.ofReal (Real.exp ((σ : ℝ) ^ 2 * lam ^ 2 / 2)) :=
            mul_le_mul_right hGint _
        _ = 1 := by
          rw [hκ, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          simp only [ENNReal.ofReal_eq_one]
          rw [Real.exp_eq_one_iff]; ring
    rw [hsplit, lintegral_add_left' hF1, lintegral_const_mul' _ _ (by rw [hκ]; exact ENNReal.ofReal_ne_top), hmul]
    calc (∫⁻ ω, (if b ω then 0 else Z ω) ∂P) +
          κ * ((∫⁻ ω, (if b ω then Z ω else 0) ∂P) * ∫⁻ ω, G ω ∂P)
        = (∫⁻ ω, (if b ω then 0 else Z ω) ∂P) +
          (∫⁻ ω, (if b ω then Z ω else 0) ∂P) * (κ * ∫⁻ ω, G ω ∂P) := by ring
      _ ≤ (∫⁻ ω, (if b ω then 0 else Z ω) ∂P) + (∫⁻ ω, (if b ω then Z ω else 0) ∂P) * 1 := by
          gcongr
      _ = ∫⁻ ω, Z ω ∂P := by
          rw [mul_one, ← lintegral_add_left' hF1]
          congr 1; ext ω; split_ifs <;> simp
      _ ≤ 1 := ih

end Supermart

section Tail
variable (σ : ℝ≥0) (c : ℕ → (ℕ → ℝ) → Bool)

lemma pm9_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hσ : 0 < σ) (hind : iIndepFun ε P)
    (hX : ∀ t, HasSubgaussianMGF (ε t) (σ ^ 2) P)
    (hc : ∀ j, MeasurableSet {e | c j e = true})
    (hloc : ∀ j e e', (∀ i < j, e i = e' i) → c j e = c j e')
    (N m : ℕ) (hm : 0 < m) (hcount : ∀ e, pm9C c N e ≤ m) (x : ℝ) (hx : 0 ≤ x) :
    P {ω | x ≤ pm9S c N (fun i => ε i ω)} ≤
      ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * m * (σ : ℝ) ^ 2))) := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set lam := x / (m * (σ : ℝ) ^ 2) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hεm : ∀ i, AEMeasurable (ε i) P := fun i => (hX i).aemeasurable
  have hpath : AEMeasurable (fun ω => (fun i => ε i ω)) P := aemeasurable_pi_lambda _ hεm
  have hfm : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (lam * pm9S c N (fun i => ε i ω)))) P :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((pm9_meas_S c hc N).const_mul lam))).comp_aemeasurable hpath
  have hsub : {ω | x ≤ pm9S c N (fun i => ε i ω)} ⊆
      {ω | ENNReal.ofReal (Real.exp (lam * x)) ≤
        ENNReal.ofReal (Real.exp (lam * pm9S c N (fun i => ε i ω)))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hω hlam0
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (lam * pm9S c N (fun i => ε i ω))) ≤
      ENNReal.ofReal (pm9Z σ c lam N (fun i => ε i ω)) *
        ENNReal.ofReal (Real.exp (lam ^ 2 * (σ : ℝ) ^ 2 / 2 * m)) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by unfold pm9Z; exact (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    unfold pm9Z
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hcount (fun i => ε i ω)
    have h2 : 0 ≤ lam ^ 2 * (σ : ℝ) ^ 2 / 2 := by positivity
    nlinarith
  have hint : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * pm9S c N (fun i => ε i ω))) ∂P ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (σ : ℝ) ^ 2 / 2 * m)) := by
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (pm9Z σ c lam N (fun i => ε i ω)) *
          ENNReal.ofReal (Real.exp (lam ^ 2 * (σ : ℝ) ^ 2 / 2 * m)) ∂P := lintegral_mono hpt
      _ = (∫⁻ ω, ENNReal.ofReal (pm9Z σ c lam N (fun i => ε i ω)) ∂P) *
          ENNReal.ofReal (Real.exp (lam ^ 2 * (σ : ℝ) ^ 2 / 2 * m)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ 1 * ENNReal.ofReal (Real.exp (lam ^ 2 * (σ : ℝ) ^ 2 / 2 * m)) :=
          mul_le_mul_left (pm9_lintegral_Z σ c P ε hind hX hc hloc lam N) _
      _ = _ := one_mul _
  calc P {ω | x ≤ pm9S c N (fun i => ε i ω)}
      ≤ P {ω | ENNReal.ofReal (Real.exp (lam * x)) ≤
        ENNReal.ofReal (Real.exp (lam * pm9S c N (fun i => ε i ω)))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * pm9S c N (fun i => ε i ω))) ∂P) /
        ENNReal.ofReal (Real.exp (lam * x)) :=
        meas_ge_le_lintegral_div hfm (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * (σ : ℝ) ^ 2 / 2 * m)) /
        ENNReal.ofReal (Real.exp (lam * x)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * m * (σ : ℝ) ^ 2))) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
        congr 2
        rw [hlam]; field_simp; ring

/-- Two-sided version. -/
lemma pm9_tail_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (hσ : 0 < σ) (hind : iIndepFun ε P)
    (hX : ∀ t, HasSubgaussianMGF (ε t) (σ ^ 2) P)
    (hc : ∀ j, MeasurableSet {e | c j e = true})
    (hloc : ∀ j e e', (∀ i < j, e i = e' i) → c j e = c j e')
    (N m : ℕ) (hm : 0 < m) (hcount : ∀ e, pm9C c N e ≤ m) (x : ℝ) (hx : 0 ≤ x) :
    P {ω | x ≤ |pm9S c N (fun i => ε i ω)|} ≤
      2 * ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * m * (σ : ℝ) ^ 2))) := by
  set c' : ℕ → (ℕ → ℝ) → Bool := fun j e => c j (fun i => -e i) with hc'
  have hneg_m : Measurable (fun e : ℕ → ℝ => fun i => -e i) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).neg)
  have hc'm : ∀ j, MeasurableSet {e | c' j e = true} := fun j => hneg_m (hc j)
  have hc'loc : ∀ j e e', (∀ i < j, e i = e' i) → c' j e = c' j e' := by
    intro j e e' he
    exact hloc j _ _ (fun i hi => by rw [he i hi])
  have hcount' : ∀ e, pm9C c' N e ≤ m := fun e => hcount (fun i => -e i)
  have hind' : iIndepFun (fun i ω => -ε i ω) P :=
    hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hX' : ∀ t, HasSubgaussianMGF (fun ω => -ε t ω) (σ ^ 2) P := fun t => (hX t).neg
  have h1 := pm9_tail σ c P ε hσ hind hX hc hloc N m hm hcount x hx
  have h2 := pm9_tail σ c' P (fun i ω => -ε i ω) hσ hind' hX' hc'm hc'loc N m hm hcount' x hx
  have heq : ∀ ω, pm9S c' N (fun i => -ε i ω) = -pm9S c N (fun i => ε i ω) := by
    intro ω
    unfold pm9S
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hc', neg_neg]
    split_ifs <;> simp
  have hsub : {ω | x ≤ |pm9S c N (fun i => ε i ω)|} ⊆
      {ω | x ≤ pm9S c N (fun i => ε i ω)} ∪ {ω | x ≤ pm9S c' N (fun i => -ε i ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rw [heq]
    rcases le_abs'.mp hω with h | h
    · right; linarith
    · left; exact h
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := (two_mul _).symm

end Tail

/-! ## Part 2: the policy is a measurable, predictable function of the noise path -/

/-- A map into a countable type with measurable fibres. -/
def pm9PW {α : Type*} (f : (ℕ → ℝ) → α) : Prop := ∀ a, MeasurableSet {e | f e = a}

lemma pm9PW_const {α : Type*} (a0 : α) : pm9PW (fun _ => a0) := by
  intro a
  by_cases h : a0 = a
  · simp [h]
  · simp [h]

lemma pm9PW_comp {α β : Type*} [Countable α] {f : (ℕ → ℝ) → α} (hf : pm9PW f) (φ : α → β) :
    pm9PW (fun e => φ (f e)) := by
  intro b
  have : {e | φ (f e) = b} = ⋃ a : {a : α // φ a = b}, {e | f e = a.1} := by
    ext e; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h; exact ⟨⟨f e, h⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, h⟩; rw [h]; exact ha
  rw [this]
  exact MeasurableSet.iUnion (fun a => hf a.1)

lemma pm9PW_bind {α β : Type*} [Countable α] {f : (ℕ → ℝ) → α} (hf : pm9PW f)
    (G : α → (ℕ → ℝ) → β) (hG : ∀ a, pm9PW (G a)) : pm9PW (fun e => G (f e) e) := by
  intro b
  have : {e | G (f e) e = b} = ⋃ a : α, ({e | f e = a} ∩ {e | G a e = b}) := by
    ext e; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨f e, rfl, h⟩
    · rintro ⟨a, h1, h2⟩; rw [h1]; exact h2
  rw [this]
  exact MeasurableSet.iUnion (fun a => (hf a).inter (hG a b))

lemma pm9PW_bind' {α β : Type*} [Countable α] {f : (ℕ → ℝ) → α} (hf : pm9PW f)
    (G : α → (ℕ → ℝ) → β) (hG : ∀ a, pm9PW (G a)) (F : (ℕ → ℝ) → β)
    (hF : ∀ e, F e = G (f e) e) : pm9PW F := by
  have : F = fun e => G (f e) e := funext hF
  rw [this]; exact pm9PW_bind hf G hG

lemma pm9PW_comp' {α β : Type*} [Countable α] {f : (ℕ → ℝ) → α} (hf : pm9PW f) (φ : α → β)
    (F : (ℕ → ℝ) → β) (hF : ∀ e, F e = φ (f e)) : pm9PW F := by
  have : F = fun e => φ (f e) := funext hF
  rw [this]; exact pm9PW_comp hf φ

lemma pm9PW_finset {β : Type*} [DecidableEq β] (A : Finset β) (f : (ℕ → ℝ) → Finset β)
    (p : β → (ℕ → ℝ) → Prop) (hf : ∀ e b, b ∈ f e ↔ b ∈ A ∧ p b e)
    (hp : ∀ b ∈ A, MeasurableSet {e | p b e}) : pm9PW f := by
  intro B
  by_cases hBA : B ⊆ A
  · have : {e | f e = B} = ⋂ b ∈ A, {e | p b e ↔ b ∈ B} := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h b hb
        have := hf e b; rw [h] at this; tauto
      · intro h
        ext b
        rw [hf e b]
        constructor
        · rintro ⟨hb, hpb⟩; exact (h b hb).mp hpb
        · intro hb; exact ⟨hBA hb, (h b (hBA hb)).mpr hb⟩
    rw [this]
    apply Finset.measurableSet_biInter
    intro b hb
    by_cases hbB : b ∈ B
    · simp only [hbB, iff_true]; exact hp b hb
    · simp only [hbB, iff_false]; exact (hp b hb).compl
  · have : {e | f e = B} = ∅ := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hBA
      intro b hb
      rw [← h, hf] at hb
      exact hb.1
    rw [this]; exact MeasurableSet.empty

section PolicyMeas
variable {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ)

/-- The reward table as a function of the noise path. -/
def pm9Y (e : ℕ → ℝ) : Fin K → ℕ → ℝ := fun k t => μ k t + e t

lemma pm9_meas_mHat (h : List (Decision K)) (s : ℕ) (k : Fin K) (t : ℕ) :
    Measurable (fun e => mHat Phat (pm9Y μ e) h n s k t) := by
  unfold mHat pm9Y
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.add (measurable_pi_apply j)

lemma pm9_meas_le_max (h : List (Decision K)) (s : ℕ) (t : ℕ) (A : Finset (Fin K)) (k : Fin K)
    (c0 : ℝ) :
    MeasurableSet {e | maxOver A (fun k' => mHat Phat (pm9Y μ e) h n s k' t) - c0 ≤
      mHat Phat (pm9Y μ e) h n s k t} := by
  by_cases hA : A.Nonempty
  · have : {e | maxOver A (fun k' => mHat Phat (pm9Y μ e) h n s k' t) - c0 ≤
        mHat Phat (pm9Y μ e) h n s k t} =
        ⋂ k' ∈ A, {e | mHat Phat (pm9Y μ e) h n s k' t ≤ mHat Phat (pm9Y μ e) h n s k t + c0} := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_iInter, maxOver, dif_pos hA, sub_le_iff_le_add,
        Finset.sup'_le_iff]
    rw [this]
    apply Finset.measurableSet_biInter
    intro k' _
    exact measurableSet_le (pm9_meas_mHat μ n Phat h s k' t)
      ((pm9_meas_mHat μ n Phat h s k t).add_const _)
  · simp only [maxOver, dif_neg hA]
    exact measurableSet_le measurable_const (pm9_meas_mHat μ n Phat h s k t)

lemma pm9_PW_argmax (h : List (Decision K)) (s : ℕ) (t : ℕ) (A : Finset (Fin K)) :
    pm9PW (fun e => argmaxOver A (fun k => mHat Phat (pm9Y μ e) h n s k t)) := by
  classical
  unfold argmaxOver
  apply pm9PW_comp (f := fun e => A.filter
    (fun k => ∀ k' ∈ A, mHat Phat (pm9Y μ e) h n s k' t ≤ mHat Phat (pm9Y μ e) h n s k t))
  apply pm9PW_finset A _ (fun k e => ∀ k' ∈ A, mHat Phat (pm9Y μ e) h n s k' t ≤
    mHat Phat (pm9Y μ e) h n s k t)
  · intro e b; rw [Finset.mem_filter]
  · intro b _
    have : {e | ∀ k' ∈ A, mHat Phat (pm9Y μ e) h n s k' t ≤ mHat Phat (pm9Y μ e) h n s b t} =
        ⋂ k' ∈ A, {e | mHat Phat (pm9Y μ e) h n s k' t ≤ mHat Phat (pm9Y μ e) h n s b t} := by
      ext e; simp
    rw [this]
    apply Finset.measurableSet_biInter
    intro k' _
    exact measurableSet_le (pm9_meas_mHat μ n Phat h s k' t) (pm9_meas_mHat μ n Phat h s b t)

lemma pm9_PW_activeSet (h : List (Decision K)) (t : ℕ) :
    ∀ s, pm9PW (fun e => activeSet σ n Phat (pm9Y μ e) h t s) := by
  intro s
  induction s with
  | zero => exact pm9PW_const _
  | succ s ih =>
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; simp only [activeSet]; exact pm9PW_const _
    · classical
      refine pm9PW_bind' ih (fun A e => A.filter (fun k =>
            maxOver A (fun k' => mHat Phat (pm9Y μ e) h n s k' t) - 2 * σ / 2 ^ s ≤
              mHat Phat (pm9Y μ e) h n s k t)) ?_ _ ?_
      · intro A
        apply pm9PW_finset A _ (fun k e => maxOver A (fun k' => mHat Phat (pm9Y μ e) h n s k' t) -
          2 * σ / 2 ^ s ≤ mHat Phat (pm9Y μ e) h n s k t)
        · intro e b; rw [Finset.mem_filter]
        · intro b _; exact pm9_meas_le_max μ n Phat h s t A b _
      · intro e
        rw [activeSet, if_neg (by omega)]

lemma pm9_PW_tourney (h : List (Decision K)) (t : ℕ) :
    ∀ f s, pm9PW (fun e => tourney σ δ T n Phat (pm9Y μ e) h t f s) := by
  intro f
  induction f with
  | zero =>
    intro s
    refine pm9PW_bind' (pm9_PW_activeSet μ σ n Phat h t (s - 1))
      (fun A e => (argmaxOver A (fun k => mHat Phat (pm9Y μ e) h n (s - 1) k t), s - 1, false))
      (fun A => pm9PW_comp' (pm9_PW_argmax μ n Phat h (s - 1) t A) (fun x => (x, s - 1, false))
        _ (fun e => rfl)) _ ?_
    intro e; rw [tourney]
  | succ f ih =>
    intro s
    classical
    refine pm9PW_bind' (pm9_PW_activeSet μ σ n Phat h t s) (fun A e =>
          if ∃ k ∈ A, σ / 2 ^ s < wHat σ δ Phat h n s k t then
            (firstOf (A.filter (fun k => σ / 2 ^ s < wHat σ δ Phat h n s k t)), s, true)
          else if ∀ k ∈ A, wHat σ δ Phat h n s k t ≤ σ / Real.sqrt T then
            (argmaxOver A (fun k => mHat Phat (pm9Y μ e) h n s k t), s, false)
          else tourney σ δ T n Phat (pm9Y μ e) h t f (s + 1)) ?_ _ ?_
    · intro A
      by_cases h1 : ∃ k ∈ A, σ / 2 ^ s < wHat σ δ Phat h n s k t
      · simp only [if_pos h1]; exact pm9PW_const _
      · simp only [if_neg h1]
        by_cases h2 : ∀ k ∈ A, wHat σ δ Phat h n s k t ≤ σ / Real.sqrt T
        · simp only [if_pos h2]
          exact pm9PW_comp' (pm9_PW_argmax μ n Phat h s t A) (fun x => (x, s, false)) _
            (fun e => rfl)
        · simp only [if_neg h2]
          exact ih (s + 1)
    · intro e
      rw [tourney]

lemma pm9_PW_decision (h : List (Decision K)) (t : ℕ) :
    pm9PW (fun e => decision σ δ T n Phat (pm9Y μ e) h t) := by
  unfold decision
  by_cases ht : t ≤ n * K
  · simp only [ht, if_true]; exact pm9PW_const _
  · simp only [ht, if_false]; exact pm9_PW_tourney μ σ δ T n Phat h t _ _

lemma pm9_PW_runHist : ∀ m, pm9PW (fun e => runHist σ δ T n Phat (pm9Y μ e) m) := by
  intro m
  induction m with
  | zero => exact pm9PW_const _
  | succ m ih =>
    refine pm9PW_bind' ih (fun h e => h ++ [decision σ δ T n Phat (pm9Y μ e) h (m + 1)])
      (fun h => pm9PW_comp' (pm9_PW_decision μ σ δ T n Phat h (m + 1)) (fun d => h ++ [d]) _
        (fun e => rfl)) _ ?_
    intro e; rw [runHist]

lemma pm9_PW_decisionAt (j : ℕ) : pm9PW (fun e => decisionAt σ δ T n Phat (pm9Y μ e) j) := by
  exact pm9PW_bind' (pm9_PW_runHist μ σ δ T n Phat (j - 1))
    (fun h e => decision σ δ T n Phat (pm9Y μ e) h j)
    (fun h => pm9_PW_decision μ σ δ T n Phat h j) _ (fun e => rfl)

end PolicyMeas

/-! ## Part 3: the policy only reads the past -/

section PolicyLoc
variable {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ)

lemma pm9_loc_mHat (Y Y' : Fin K → ℕ → ℝ) (h : List (Decision K)) (s : ℕ) (k : Fin K) (t : ℕ)
    (ht : n * K < t) (hY : ∀ k j, 1 ≤ j → j ≤ t - 1 → Y k j = Y' k j) :
    mHat Phat Y h n s k t = mHat Phat Y' h n s k t := by
  unfold mHat
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_filter, Finset.mem_union] at hj
  rcases hj.1 with hj1 | hj1
  · unfold psiSet at hj1
    rw [Finset.mem_filter, Finset.mem_Icc] at hj1
    exact hY k j (by omega) hj1.1.2
  · rw [psiBar, Finset.mem_Icc] at hj1
    exact hY k j hj1.1 (by omega)

lemma pm9_loc_activeSet (Y Y' : Fin K → ℕ → ℝ) (h : List (Decision K)) (t : ℕ)
    (hm : ∀ s k, mHat Phat Y h n s k t = mHat Phat Y' h n s k t) :
    ∀ s, activeSet σ n Phat Y h t s = activeSet σ n Phat Y' h t s := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [activeSet]
    split_ifs
    · rfl
    · rw [ih]
      simp only [hm]

lemma pm9_loc_tourney (Y Y' : Fin K → ℕ → ℝ) (h : List (Decision K)) (t : ℕ)
    (hm : ∀ s k, mHat Phat Y h n s k t = mHat Phat Y' h n s k t) :
    ∀ f s, tourney σ δ T n Phat Y h t f s = tourney σ δ T n Phat Y' h t f s := by
  have hA := pm9_loc_activeSet σ n Phat Y Y' h t hm
  intro f
  induction f with
  | zero => intro s; simp only [tourney, hA, hm]
  | succ f ih =>
    intro s
    rw [tourney, tourney, hA s, ih (s + 1)]
    simp only [hm]

lemma pm9_loc_decision (Y Y' : Fin K → ℕ → ℝ) (h : List (Decision K)) (t : ℕ)
    (hY : ∀ k j, 1 ≤ j → j ≤ t - 1 → Y k j = Y' k j) :
    decision σ δ T n Phat Y h t = decision σ δ T n Phat Y' h t := by
  unfold decision
  split_ifs with ht
  · rfl
  · push Not at ht
    exact pm9_loc_tourney σ δ T n Phat Y Y' h t
      (fun s k => pm9_loc_mHat n Phat Y Y' h s k t ht hY) _ _

lemma pm9_loc_runHist (Y Y' : Fin K → ℕ → ℝ) :
    ∀ m, (∀ k j, 1 ≤ j → j < m → Y k j = Y' k j) →
      runHist σ δ T n Phat Y m = runHist σ δ T n Phat Y' m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hY
    rw [runHist, runHist, ih (fun k j h1 h2 => hY k j h1 (by omega))]
    congr 2
    exact pm9_loc_decision σ δ T n Phat Y Y' _ _ (fun k j h1 h2 => hY k j h1 (by omega))

lemma pm9_loc_decisionAt (Y Y' : Fin K → ℕ → ℝ) (j : ℕ)
    (hY : ∀ k i, 1 ≤ i → i < j → Y k i = Y' k i) :
    decisionAt σ δ T n Phat Y j = decisionAt σ δ T n Phat Y' j := by
  unfold decisionAt
  rw [pm9_loc_runHist σ δ T n Phat Y Y' (j - 1) (fun k i h1 h2 => hY k i h1 (by omega))]
  exact pm9_loc_decision σ δ T n Phat Y Y' _ _ (fun k i h1 h2 => hY k i h1 (by omega))

end PolicyLoc

/-! ## Part 4: the selection rules of the effective arms -/

lemma pm9PW_pair {α β : Type*} {f : (ℕ → ℝ) → α} {g : (ℕ → ℝ) → β} (hf : pm9PW f)
    (hg : pm9PW g) : pm9PW (fun e => (f e, g e)) := by
  intro ab
  have : {e | (f e, g e) = ab} = {e | f e = ab.1} ∩ {e | g e = ab.2} := by
    ext e; simp [Prod.ext_iff]
  rw [this]; exact (hf _).inter (hg _)

section Selection
variable {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (σ δ : ℝ) (T n : ℕ) (Tper : Fin K → ℕ)
  (k : Fin K) (p s : ℕ)

noncomputable def pm9sel (j : ℕ) (e : ℕ → ℝ) : Bool :=
  decide (n * K < j ∧ j ≤ T ∧ (decisionAt σ δ T n Tper (pm9Y μ e) j).1 = k ∧
    (decisionAt σ δ T n Tper (pm9Y μ e) j).2 = (s, true) ∧ j % Tper k = p)

noncomputable def pm9rank (j : ℕ) (e : ℕ → ℝ) : ℕ :=
  ((Icc 1 (j - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true)).card

noncomputable def pm9selm (m : ℕ) (j : ℕ) (e : ℕ → ℝ) : Bool :=
  pm9sel μ σ δ T n Tper k p s j e && decide (pm9rank μ σ δ T n Tper k p s j e < m)

lemma pm9_PW_sel (j : ℕ) : pm9PW (pm9sel μ σ δ T n Tper k p s j) :=
  pm9PW_comp' (pm9_PW_decisionAt μ σ δ T n Tper j)
    (fun d => decide (n * K < j ∧ j ≤ T ∧ d.1 = k ∧ d.2 = (s, true) ∧ j % Tper k = p)) _
    (fun e => rfl)

lemma pm9_PW_rank (j : ℕ) : pm9PW (pm9rank μ σ δ T n Tper k p s j) := by
  have hF : pm9PW (fun e => (Icc 1 (j - 1)).filter
      (fun i => pm9sel μ σ δ T n Tper k p s i e = true)) :=
    pm9PW_finset (Icc 1 (j - 1)) _ (fun i e => pm9sel μ σ δ T n Tper k p s i e = true)
      (fun e b => by rw [Finset.mem_filter])
      (fun b _ => pm9_PW_sel μ σ δ T n Tper k p s b true)
  exact pm9PW_comp' hF (fun A => A.card) _ (fun e => rfl)

lemma pm9_meas_selm (m j : ℕ) : MeasurableSet {e | pm9selm μ σ δ T n Tper k p s m j e = true} :=
  pm9PW_comp' (pm9PW_pair (pm9_PW_sel μ σ δ T n Tper k p s j) (pm9_PW_rank μ σ δ T n Tper k p s j))
    (fun x => x.1 && decide (x.2 < m)) _ (fun e => rfl) true

lemma pm9_loc_sel (j : ℕ) (e e' : ℕ → ℝ) (he : ∀ i < j, e i = e' i) :
    pm9sel μ σ δ T n Tper k p s j e = pm9sel μ σ δ T n Tper k p s j e' := by
  unfold pm9sel
  rw [pm9_loc_decisionAt σ δ T n Tper (pm9Y μ e) (pm9Y μ e') j
    (fun k i _ hi => by simp only [pm9Y, he i hi])]

lemma pm9_loc_selm (m j : ℕ) (e e' : ℕ → ℝ) (he : ∀ i < j, e i = e' i) :
    pm9selm μ σ δ T n Tper k p s m j e = pm9selm μ σ δ T n Tper k p s m j e' := by
  have hfil : (Icc 1 (j - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true) =
      (Icc 1 (j - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e' = true) := by
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [pm9_loc_sel μ σ δ T n Tper k p s i e e' (fun i' hi' => he i' (by omega))]
  unfold pm9selm pm9rank
  rw [pm9_loc_sel μ σ δ T n Tper k p s j e e' he, hfil]

/-- ranks of selected epochs strictly increase. -/
lemma pm9_rank_lt (e : ℕ → ℝ) (j j' : ℕ) (hj1 : 1 ≤ j) (hjj : j < j')
    (hj : pm9sel μ σ δ T n Tper k p s j e = true) :
    pm9rank μ σ δ T n Tper k p s j e < pm9rank μ σ δ T n Tper k p s j' e := by
  unfold pm9rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hj1, by omega⟩, hj⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]; omega
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    exact ⟨⟨hi.1.1, by omega⟩, hi.2⟩

lemma pm9_count_selm (m : ℕ) (e : ℕ → ℝ) :
    pm9C (pm9selm μ σ δ T n Tper k p s m) T e ≤ m := by
  unfold pm9C
  rw [Finset.sum_boole]
  set F := (Icc 1 T).filter (fun j => pm9selm μ σ δ T n Tper k p s m j e = true) with hF
  have hinj : Set.InjOn (fun j => pm9rank μ σ δ T n Tper k p s j e) (F : Set ℕ) := by
    intro j hj j' hj' heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hF, Finset.mem_Icc, pm9selm,
      Bool.and_eq_true, decide_eq_true_eq] at hj hj'
    simp only at heq
    rcases lt_trichotomy j j' with h | h | h
    · exact absurd heq (ne_of_lt (pm9_rank_lt μ σ δ T n Tper k p s e j j' hj.1.1 h hj.2.1))
    · exact h
    · exact absurd heq (ne_of_gt (pm9_rank_lt μ σ δ T n Tper k p s e j' j hj'.1.1 h hj'.2.1))
  have himg : F.image (fun j => pm9rank μ σ δ T n Tper k p s j e) ⊆ range m := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    rw [hF, Finset.mem_filter] at hj
    simp only [pm9selm, Bool.and_eq_true, decide_eq_true_eq] at hj
    exact Finset.mem_range.mpr hj.2.2
  have := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  exact_mod_cast this

/-- The selected epochs before `t` are exactly those of rank below their number. -/
lemma pm9_rank_identity (e : ℕ → ℝ) (t : ℕ) (ht : t ≤ T + 1) :
    (Icc 1 T).filter (fun j => pm9selm μ σ δ T n Tper k p s
        ((Icc 1 (t - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true)).card j e = true) =
      (Icc 1 (t - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true) := by
  generalize hD : (Icc 1 (t - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true) = D
  have hmemD : ∀ i, i ∈ D ↔ (1 ≤ i ∧ i ≤ t - 1) ∧ pm9sel μ σ δ T n Tper k p s i e = true := by
    intro i; rw [← hD, Finset.mem_filter, Finset.mem_Icc]
  have hmemR : ∀ j i, i ∈ (Icc 1 (j - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true) ↔
      (1 ≤ i ∧ i ≤ j - 1) ∧ pm9sel μ σ δ T n Tper k p s i e = true := by
    intro j i; rw [Finset.mem_filter, Finset.mem_Icc]
  ext j
  rw [Finset.mem_filter, Finset.mem_Icc, hmemD]
  simp only [pm9selm, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hjT, hsel, hrank⟩
    refine ⟨⟨hjT.1, ?_⟩, hsel⟩
    by_contra hc
    push Not at hc
    have : D ⊆ (Icc 1 (j - 1)).filter (fun i => pm9sel μ σ δ T n Tper k p s i e = true) := by
      intro i hi
      rw [hmemD] at hi
      rw [hmemR]
      exact ⟨⟨hi.1.1, by omega⟩, hi.2⟩
    have := Finset.card_le_card this
    unfold pm9rank at hrank
    omega
  · rintro ⟨hj, hsel⟩
    refine ⟨⟨hj.1, by omega⟩, hsel, ?_⟩
    unfold pm9rank
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, ?_, ?_⟩
      · rw [hmemD]; exact ⟨hj, hsel⟩
      · rw [hmemR]; omega
    · intro i hi
      rw [hmemR] at hi
      rw [hmemD]
      exact ⟨⟨hi.1.1, by omega⟩, hi.2⟩

end Selection

/-! ## Part 5: bookkeeping (as in Lemma 16) -/

section Struct
variable {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ) (Y : Fin K → ℕ → ℝ)

lemma pmab16_runHist_length : ∀ m, (runHist σ δ T n Phat Y m).length = m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp [runHist, ih]

lemma pmab16_runHist_get : ∀ m j, 1 ≤ j → j ≤ m →
    (runHist σ δ T n Phat Y m)[j - 1]? = some (decisionAt σ δ T n Phat Y j) := by
  intro m
  induction m with
  | zero => intro j h1 h2; omega
  | succ m ih =>
    intro j h1 h2
    rw [runHist]
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · rw [List.getElem?_append_left (by rw [pmab16_runHist_length]; omega)]
      exact ih j h1 (by omega)
    · have hj' : j = m + 1 := by omega
      subst hj'
      rw [List.getElem?_append_right (by rw [pmab16_runHist_length]; omega)]
      simp [pmab16_runHist_length, decisionAt]

lemma pmab16_armAt (t j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ t - 1) :
    armAt (runHist σ δ T n Phat Y (t - 1)) j = some (policy σ δ T n Phat Y j) := by
  unfold armAt
  rw [pmab16_runHist_get σ δ T n Phat Y (t - 1) j hj1 hj]
  rfl

lemma pmab16_tagAt (t j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ t - 1) :
    tagAt (runHist σ δ T n Phat Y (t - 1)) j = some (decisionAt σ δ T n Phat Y j).2 := by
  unfold tagAt
  rw [pmab16_runHist_get σ δ T n Phat Y (t - 1) j hj1 hj]
  rfl

/-- `Ψ^(s)(t)` in terms of the global records. -/
lemma pmab16_psiSet (s t : ℕ) :
    psiSet (runHist σ δ T n Phat Y (t - 1)) n s t =
      (Icc (n * K + 1) (t - 1)).filter (fun j => (decisionAt σ δ T n Phat Y j).2 = (s, true)) := by
  unfold psiSet
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [pmab16_tagAt σ δ T n Phat Y t j (by omega) hj.2]
  simp

/-- counts in terms of the global records. -/
lemma pmab16_count (k : Fin K) (t : ℕ) (X : Finset ℕ) (hX : X ⊆ Icc 1 (t - 1)) :
    count Phat (runHist σ δ T n Phat Y (t - 1)) k t X =
      (X.filter (fun j => policy σ δ T n Phat Y j = k ∧ j % Phat k = t % Phat k)).card := by
  unfold count
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_Icc.mp (hX hj)
  rw [pmab16_armAt σ δ T n Phat Y t j hj'.1 hj'.2]
  simp [Nat.ModEq]

lemma pmab16_stageOne (j : ℕ) (hj : j ≤ n * K) :
    policy σ δ T n Phat Y j = stageOneArm n j := by
  unfold policy decisionAt decision
  rw [if_pos hj]

end Struct

/-- Every phase of every arm is sampled at least twice in stage one. -/
lemma pmab16_stage_two {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ)
    (Y : Fin K → ℕ → ℝ) (P : Fin K → ℕ) (k : Fin K) (p : ℕ) (hp : p < P k)
    (hn : 2 * P k ≤ n) :
    2 ≤ ((psiBar n K).filter (fun j => policy σ δ T n Phat Y j = k ∧ j % P k = p)).card := by
  set q := P k with hq
  have hq0 : 0 < q := by omega
  set base := n * (k : ℕ) + 1 with hbase
  set x := base + q - 1 - p with hx
  set m := x / q with hm
  have h1 : q * m ≤ x := Nat.mul_div_le x q
  have h2 : x < q * m + q := by
    have := Nat.lt_div_mul_add (a := x) hq0
    rw [← hm] at this
    linarith [mul_comm q m]
  set y := q * m with hy
  have hk : (k : ℕ) < K := k.2
  have hnk : n * (k : ℕ) + n ≤ n * K := by
    have : n * ((k : ℕ) + 1) ≤ n * K := Nat.mul_le_mul_left n hk
    linarith [mul_add n (k : ℕ) 1]
  have hmem : ∀ j, base ≤ j → j ≤ n * (k : ℕ) + n → j % q = p →
      j ∈ (psiBar n K).filter (fun j => policy σ δ T n Phat Y j = k ∧ j % P k = p) := by
    intro j hj1 hj2 hjp
    rw [Finset.mem_filter, psiBar, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_, hjp⟩
    rw [pmab16_stageOne σ δ T n Phat Y j (by omega), stageOneArm]
    have hdiv : (j - 1) / n = k := by
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm]; omega
      · rw [add_mul, one_mul, mul_comm]; omega
    rw [dif_pos (by rw [hdiv]; exact hk)]
    ext; exact hdiv
  have hj1p : (p + y) % q = p := by
    rw [hy, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hp
  have hj2p : (p + y + q) % q = p := by
    rw [Nat.add_mod_right]; exact hj1p
  have hA := hmem (p + y) (by omega) (by omega) hj1p
  have hB := hmem (p + y + q) (by omega) (by omega) hj2p
  have : ({p + y, p + y + q} : Finset ℕ) ⊆
      (psiBar n K).filter (fun j => policy σ δ T n Phat Y j = k ∧ j % P k = p) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hA
    · exact hB
  have hc := Finset.card_le_card this
  rw [Finset.card_pair (by omega)] at hc
  exact hc

lemma pm9_periodic (f : ℕ → ℝ) (q : ℕ) (hf : IsMinPeriod f q) :
    ∀ a b, 1 ≤ a → 1 ≤ b → a % q = b % q → f a = f b := by
  obtain ⟨hq, hper, -⟩ := hf
  have base : ∀ a, 1 ≤ a → f a = f ((a - 1) % q + 1) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha
      by_cases hle : a ≤ q
      · rcases Nat.lt_or_ge (a - 1) q with h | h
        · rw [Nat.mod_eq_of_lt h]; congr 1; omega
        · omega
      · push Not at hle
        have h1 : f a = f (a - q) := by
          have := hper (a - q) (by omega)
          rw [show a - q + q = a by omega] at this
          exact this
        rw [h1, ih (a - q) (by omega) (by omega)]
        congr 2
        have : a - 1 = (a - q - 1) + q := by omega
        rw [this, Nat.add_mod_right]
  intro a b ha hb hab
  rw [base a ha, base b hb]
  congr 2
  have h1 : (a - 1 + 1) % q = (b - 1 + 1) % q := by
    rw [show a - 1 + 1 = a by omega, show b - 1 + 1 = b by omega]; exact hab
  exact Nat.ModEq.add_right_cancel' 1 h1

noncomputable def pm9w (σ δ : ℝ) {K : ℕ} (Tper : Fin K → ℕ) (c : ℝ) : ℝ :=
  Real.sqrt (4 * σ ^ 2 / c * Real.log (8 * (∑ k', (Tper k' : ℝ)) * c / δ))

lemma pm9_filter_arm {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ)
    (Y : Fin K → ℕ → ℝ) (k : Fin K) (t : ℕ) (X : Finset ℕ) (hX : X ⊆ Icc 1 (t - 1)) :
    X.filter (fun j => armAt (runHist σ δ T n Phat Y (t - 1)) j = some k ∧ j ≡ t [MOD Phat k]) =
      X.filter (fun j => policy σ δ T n Phat Y j = k ∧ j % Phat k = t % Phat k) := by
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_Icc.mp (hX hj)
  rw [pmab16_armAt σ δ T n Phat Y t j hj'.1 hj'.2]
  simp [Nat.ModEq]

set_option maxHeartbeats 1000000 in
lemma pm9_good {Ω : Type*} (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) {K : ℕ} [NeZero K]
    (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (h2T : ∀ k, 2 * Tper k ≤ n) (ω : Ω)
    (GB : ∀ k : Fin K, ∀ p < Tper k,
      |∑ j ∈ (psiBar n K).filter (fun j => stageOneArm n j = k ∧ j % Tper k = p), ε j ω| ≤
        ((psiBar n K).filter (fun j => stageOneArm n j = k ∧ j % Tper k = p)).card *
          pm9w σ δ Tper ((psiBar n K).filter (fun j => stageOneArm n j = k ∧ j % Tper k = p)).card)
    (GD : ∀ k : Fin K, ∀ p < Tper k, ∀ s ∈ Icc 1 (Nat.log 2 T), ∀ m ∈ Icc 1 T,
      |pm9S (pm9selm μ σ δ T n Tper k p s m) T (fun i => ε i ω)| ≤ m * pm9w σ δ Tper m) :
    ω ∈ eventE μ ε σ δ T n Tper := by
  intro k t ht s hs
  set e := fun i => ε i ω with he
  set Y := reward μ ε ω with hY
  have hYe : Y = pm9Y μ e := rfl
  set pol := policy (σ : ℝ) δ T n Tper Y with hpol
  set dec := decisionAt (σ : ℝ) δ T n Tper Y with hdec
  set p := t % Tper k with hp
  have hTk : 0 < Tper k := (hper k).1
  have hpk : p < Tper k := Nat.mod_lt _ hTk
  rw [Finset.mem_Icc] at ht
  set Ψt := (Icc (n * K + 1) (t - 1)).filter (fun j => (dec j).2 = (s, true)) with hΨt
  have hsub1 : psiBar n K ⊆ Icc 1 (t - 1) := by
    intro j hj; rw [psiBar, Finset.mem_Icc] at hj; rw [Finset.mem_Icc]; omega
  have hsub2 : Ψt ⊆ Icc 1 (t - 1) := by
    intro j hj; rw [hΨt, Finset.mem_filter, Finset.mem_Icc] at hj; rw [Finset.mem_Icc]; omega
  set D := Ψt.filter (fun j => pol j = k ∧ j % Tper k = p) with hD
  set B := (psiBar n K).filter (fun j => pol j = k ∧ j % Tper k = p) with hB
  have hdisj : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro j hjD hjB
    rw [hD, Finset.mem_filter, hΨt, Finset.mem_filter, Finset.mem_Icc] at hjD
    rw [hB, Finset.mem_filter, psiBar, Finset.mem_Icc] at hjB
    omega
  have hfilt : (Ψt ∪ psiBar n K).filter (fun j => pol j = k ∧ j % Tper k = p) = D ∪ B := by
    rw [Finset.filter_union]
  -- B is the deterministic stage-one set
  have hBdet : B = (psiBar n K).filter (fun j => stageOneArm n j = k ∧ j % Tper k = p) := by
    rw [hB]
    apply Finset.filter_congr
    intro j hj
    rw [psiBar, Finset.mem_Icc] at hj
    rw [hpol, pmab16_stageOne (σ : ℝ) δ T n Tper Y j hj.2]
  -- D is the set of selected epochs before t
  have hDsel : D = (Icc 1 (t - 1)).filter
      (fun i => pm9sel μ σ δ T n Tper k p s i e = true) := by
    ext j
    rw [hD, Finset.mem_filter, hΨt, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Icc]
    unfold pm9sel
    simp only [decide_eq_true_eq]
    have h1 : dec j = decisionAt (σ : ℝ) δ T n Tper (pm9Y μ e) j := rfl
    have h2 : pol j = (decisionAt (σ : ℝ) δ T n Tper (pm9Y μ e) j).1 := rfl
    rw [h1, h2]
    constructor
    · rintro ⟨⟨hj, htag⟩, harm, hmod⟩
      exact ⟨⟨by omega, hj.2⟩, by omega, by omega, harm, htag, hmod⟩
    · rintro ⟨hj, h1', h2', harm, htag, hmod⟩
      exact ⟨⟨⟨by omega, hj.2⟩, htag⟩, harm, hmod⟩
  have hBcard : (2 : ℝ) ≤ B.card := by
    have := pmab16_stage_two (σ : ℝ) δ T n Tper Y Tper k p hpk (h2T k)
    exact_mod_cast this
  -- the noise sums
  have hsumD : ∑ j ∈ D, ε j ω = pm9S (pm9selm μ σ δ T n Tper k p s D.card) T e := by
    unfold pm9S
    rw [← Finset.sum_filter]
    have := pm9_rank_identity μ σ δ T n Tper k p s e t (by omega)
    rw [← hDsel] at this
    rw [this]
  have hGD : |∑ j ∈ D, ε j ω| ≤ D.card * pm9w σ δ Tper D.card := by
    rcases Nat.eq_zero_or_pos D.card with h0 | hpos
    · rw [Finset.card_eq_zero] at h0; rw [h0]; simp
    · rw [hsumD]
      have hDT : D.card ≤ T := by
        have hDsub : D ⊆ Icc 1 (t - 1) := fun j hj => hsub2 (Finset.filter_subset _ _ hj)
        have := Finset.card_le_card hDsub
        rw [Nat.card_Icc] at this; omega
      exact GD k p hpk s hs D.card (Finset.mem_Icc.mpr ⟨hpos, hDT⟩)
  have hGB : |∑ j ∈ B, ε j ω| ≤ B.card * pm9w σ δ Tper B.card := by
    rw [hBdet]; exact GB k p hpk
  -- periodicity
  have hmu : ∀ j ∈ D ∪ B, Y k j = μ k t + ε j ω := by
    intro j hj
    have hj1 : 1 ≤ j := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (Finset.mem_Icc.mp (hsub2 (Finset.filter_subset _ _ hj))).1
      · exact (Finset.mem_Icc.mp (hsub1 (Finset.filter_subset _ _ hj))).1
    have hjp : j % Tper k = t % Tper k := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (Finset.mem_filter.mp hj).2.2
      · exact (Finset.mem_filter.mp hj).2.2
    rw [hY, reward, pm9_periodic (μ k) (Tper k) (hper k) j t hj1 (by omega) hjp]
  -- assemble mAt and wAt
  have hmAt : mAt (σ : ℝ) δ T n Tper Y s k t =
      (1 / ((D.card : ℝ) + B.card)) * ((D.card + B.card) * μ k t +
        (∑ j ∈ D, ε j ω + ∑ j ∈ B, ε j ω)) := by
    unfold mAt mHat
    rw [pmab16_psiSet (σ : ℝ) δ T n Tper Y s t]
    rw [pmab16_count (σ : ℝ) δ T n Tper Y k t _ (Finset.union_subset hsub2 hsub1)]
    rw [pm9_filter_arm (σ : ℝ) δ T n Tper Y k t _ (Finset.union_subset hsub2 hsub1)]
    rw [hfilt, Finset.card_union_of_disjoint hdisj, Finset.sum_congr rfl hmu,
      Finset.sum_add_distrib, Finset.sum_const, Finset.sum_union hdisj,
      Finset.card_union_of_disjoint hdisj]
    push_cast
    simp only [nsmul_eq_mul, Nat.cast_add]
  have hwAt : wAt (σ : ℝ) δ T n Tper Y s k t =
      B.card / ((D.card : ℝ) + B.card) * pm9w σ δ Tper B.card +
        D.card / ((D.card : ℝ) + B.card) * pm9w σ δ Tper D.card := by
    unfold wAt wHat pm9w
    simp only []
    rw [pmab16_psiSet (σ : ℝ) δ T n Tper Y s t]
    rw [pmab16_count (σ : ℝ) δ T n Tper Y k t _ hsub1,
      pmab16_count (σ : ℝ) δ T n Tper Y k t _ hsub2,
      pmab16_count (σ : ℝ) δ T n Tper Y k t _ (Finset.union_subset hsub2 hsub1)]
    rw [hfilt, Finset.card_union_of_disjoint hdisj]
    push_cast
    rfl
  rw [hmAt, hwAt]
  have hcu : (0 : ℝ) < D.card + B.card := by linarith [(by positivity : (0:ℝ) ≤ D.card)]
  have : (1 / ((D.card : ℝ) + B.card)) * ((D.card + B.card) * μ k t +
        (∑ j ∈ D, ε j ω + ∑ j ∈ B, ε j ω)) - μ k t =
      (∑ j ∈ D, ε j ω + ∑ j ∈ B, ε j ω) / ((D.card : ℝ) + B.card) := by
    field_simp; ring
  rw [this, abs_div, abs_of_pos hcu, div_le_iff₀ hcu]
  have e1 := abs_add_le (∑ j ∈ D, ε j ω) (∑ j ∈ B, ε j ω)
  have : (B.card / ((D.card : ℝ) + B.card) * pm9w σ δ Tper B.card +
        D.card / ((D.card : ℝ) + B.card) * pm9w σ δ Tper D.card) * ((D.card : ℝ) + B.card) =
      B.card * pm9w σ δ Tper B.card + D.card * pm9w σ δ Tper D.card := by
    field_simp
  rw [this]
  linarith

lemma pm9_exp_calc (σ δ : ℝ) {K : ℕ} (Tper : Fin K → ℕ) (hσ : 0 < σ) (hδ : 0 < δ)
    (hd : 1 ≤ ∑ k', (Tper k' : ℝ)) (hδ1 : δ < 1) (m : ℕ) (hm : 1 ≤ m) :
    2 * Real.exp (-((m : ℝ) * pm9w σ δ Tper m) ^ 2 / (2 * m * σ ^ 2)) ≤
      δ ^ 2 / (32 * (∑ k', (Tper k' : ℝ)) ^ 2 * (m : ℝ) ^ 2) := by
  set d := ∑ k', (Tper k' : ℝ) with hdd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set L := Real.log (8 * d * m / δ) with hL
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg; rw [le_div_iff₀ hδ]; nlinarith
  have hw : pm9w σ δ Tper m ^ 2 = 4 * σ ^ 2 / m * L := by
    unfold pm9w; rw [Real.sq_sqrt (by positivity)]
  have hx : -((m : ℝ) * pm9w σ δ Tper m) ^ 2 / (2 * m * σ ^ 2) = 2 * Real.log (δ / (8 * d * m)) := by
    rw [mul_pow, hw, Real.log_div hδ.ne' (by positivity), hL, Real.log_div (by positivity) hδ.ne']
    field_simp; ring
  rw [hx, show 2 * Real.log (δ / (8 * d * m)) = Real.log ((δ / (8 * d * m)) ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
  rw [div_pow, mul_pow, mul_pow]
  apply le_of_eq
  field_simp
  ring

set_option maxHeartbeats 2000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    P (eventE μ ε σ δ T n Tper)ᶜ ≤ ENNReal.ofReal (δ * Nat.log 2 T) := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  set d := ∑ k', (Tper k' : ℝ) with hdd
  have hd1 : (1 : ℝ) ≤ d := by
    rw [hdd]
    calc (1 : ℝ) ≤ Tper 0 := by exact_mod_cast (hper 0).1
      _ ≤ ∑ k, (Tper k : ℝ) :=
        Finset.single_le_sum (f := fun k => (Tper k : ℝ)) (fun k _ => by positivity) (mem_univ _)
  have h2T : ∀ k, 2 * Tper k ≤ n := by
    intro k
    obtain ⟨_, hg2, _, hTk⟩ := hA3
    have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have h1 := hTk k
    have : (Tper k : ℝ) * (2 * g) < n := by
      rwa [lt_div_iff₀ (by positivity)] at h1
    have : (2 * Tper k : ℝ) < n := by nlinarith [(by positivity : (0:ℝ) ≤ Tper k)]
    exact_mod_cast this.le
  have hT5 : 5 ≤ T := by obtain ⟨h, -⟩ := hA3; omega
  set S := Nat.log 2 T with hS
  have hS1 : 1 ≤ S := Nat.le_log_of_pow_le (by norm_num) (by omega)
  set I : Finset (Σ _ : Fin K, ℕ) := (univ : Finset (Fin K)).sigma (fun k => range (Tper k)) with hI
  have hIcard : (I.card : ℝ) = d := by
    rw [hI, Finset.card_sigma, hdd]; simp
  set path := fun ω => (fun i => ε i ω) with hpath
  set Bset := fun q : (Σ _ : Fin K, ℕ) =>
    (psiBar n K).filter (fun j => stageOneArm n j = q.1 ∧ j % Tper q.1 = q.2) with hBset
  set badB := fun q : (Σ _ : Fin K, ℕ) => {ω | ((Bset q).card : ℝ) * pm9w σ δ Tper (Bset q).card <
      |∑ j ∈ Bset q, ε j ω|} with hbadB
  set badD := fun (q : Σ _ : Fin K, ℕ) (s m : ℕ) => {ω | (m : ℝ) * pm9w σ δ Tper m <
      |pm9S (pm9selm μ σ δ T n Tper q.1 q.2 s m) T (path ω)|} with hbadD
  -- inclusion
  have hincl : (eventE μ ε σ δ T n Tper)ᶜ ⊆ (⋃ q ∈ I, badB q) ∪
      ⋃ q ∈ I, ⋃ s ∈ Icc 1 S, ⋃ m ∈ Icc 1 T, badD q s m := by
    intro ω hω
    by_contra hc
    apply hω
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hc
    obtain ⟨hcB, hcD⟩ := hc
    apply pm9_good ε σ μ Tper T n δ hper h2T ω
    · intro k p hp
      have := hcB ⟨k, p⟩ (by rw [hI, Finset.mem_sigma]; exact ⟨mem_univ _, Finset.mem_range.mpr hp⟩)
      simp only [hbadB, Set.mem_setOf_eq, not_lt] at this
      exact this
    · intro k p hp s hs m hm
      have := hcD ⟨k, p⟩ (by rw [hI, Finset.mem_sigma]; exact ⟨mem_univ _, Finset.mem_range.mpr hp⟩)
        s hs m hm
      simp only [hbadD, Set.mem_setOf_eq, not_lt] at this
      exact this
  -- bound for badB
  have hB : ∀ q ∈ I, P (badB q) ≤ ENNReal.ofReal (δ / (32 * d)) := by
    intro q hq
    rw [hI, Finset.mem_sigma, Finset.mem_range] at hq
    set B := Bset q with hBq
    have hB2 : 2 ≤ B.card := by
      have := pmab16_stage_two (σ : ℝ) δ T n Tper (fun _ _ => 0) Tper q.1 q.2 hq.2 (h2T _)
      have hsub : (psiBar n K).filter (fun j => policy (σ : ℝ) δ T n Tper (fun _ _ => 0) j = q.1 ∧
          j % Tper q.1 = q.2) ⊆ B := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [hBq, hBset, Finset.mem_filter]
        rw [psiBar, Finset.mem_Icc] at hj
        refine ⟨by rw [psiBar, Finset.mem_Icc]; exact hj.1, ?_, hj.2.2⟩
        rw [← pmab16_stageOne (σ : ℝ) δ T n Tper (fun _ _ => 0) j hj.1.2]; exact hj.2.1
      exact le_trans this (Finset.card_le_card hsub)
    have hBsub : B ⊆ Icc 1 T := by
      intro j hj
      rw [hBq, hBset, Finset.mem_filter, psiBar, Finset.mem_Icc] at hj
      rw [Finset.mem_Icc]; omega
    set c : ℕ → (ℕ → ℝ) → Bool := fun j _ => decide (j ∈ B) with hc
    have hS_eq : ∀ ω, pm9S c T (path ω) = ∑ j ∈ B, ε j ω := by
      intro ω
      unfold pm9S
      simp only [hc, decide_eq_true_eq, hpath]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBsub]
    have hcount : ∀ e, pm9C c T e ≤ B.card := by
      intro e
      unfold pm9C
      simp only [hc, decide_eq_true_eq]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBsub]
      simp
    have htail := pm9_tail_abs σ c P ε hσ hε.indep hε.mgf
      (fun j => by
        show MeasurableSet {e : ℕ → ℝ | decide (j ∈ B) = true}
        exact MeasurableSet.const _) (fun j e e' _ => rfl) T B.card (by omega) hcount
      ((B.card : ℝ) * pm9w σ δ Tper B.card) (by unfold pm9w; positivity)
    have hset : {ω | (B.card : ℝ) * pm9w σ δ Tper B.card ≤ |pm9S c T (fun i => ε i ω)|} =
        {ω | (B.card : ℝ) * pm9w σ δ Tper B.card ≤ |∑ j ∈ B, ε j ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [show (fun i => ε i ω) = path ω from rfl, hS_eq]
    rw [hset] at htail
    calc P (badB q) ≤ P {ω | ((B.card : ℝ) * pm9w σ δ Tper B.card) ≤ |∑ j ∈ B, ε j ω|} := by
          apply measure_mono
          intro ω hω
          simp only [hbadB, Set.mem_setOf_eq] at hω ⊢
          exact hω.le
      _ ≤ 2 * ENNReal.ofReal (Real.exp (-((B.card : ℝ) * pm9w σ δ Tper B.card) ^ 2 /
          (2 * B.card * (σ : ℝ) ^ 2))) := htail
      _ = ENNReal.ofReal (2 * Real.exp (-((B.card : ℝ) * pm9w σ δ Tper B.card) ^ 2 /
          (2 * B.card * (σ : ℝ) ^ 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ ≤ ENNReal.ofReal (δ / (32 * d)) := by
          apply ENNReal.ofReal_le_ofReal
          have := pm9_exp_calc (σ : ℝ) δ Tper hσR hδ hd1 hδ1 B.card (by omega)
          refine le_trans this ?_
          have hB1 : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hd2 : d ≤ d ^ 2 * (B.card : ℝ) ^ 2 := by
            have e1 : d ≤ d ^ 2 := by nlinarith
            have e2 : (1 : ℝ) ≤ (B.card : ℝ) ^ 2 := by nlinarith
            calc d ≤ d ^ 2 := e1
              _ = d ^ 2 * 1 := by ring
              _ ≤ d ^ 2 * (B.card : ℝ) ^ 2 := by gcongr
          have hδ2 : δ ^ 2 ≤ δ := by nlinarith
          calc δ ^ 2 * (32 * d) ≤ δ * (32 * d) := by gcongr
            _ ≤ δ * (32 * (d ^ 2 * (B.card : ℝ) ^ 2)) := by gcongr
            _ = δ * (32 * d ^ 2 * (B.card : ℝ) ^ 2) := by ring
  -- bound for badD
  have hD : ∀ q ∈ I, ∀ s ∈ Icc 1 S, ∀ m ∈ Icc 1 T,
      P (badD q s m) ≤ ENNReal.ofReal (δ ^ 2 / (32 * d ^ 2 * (m : ℝ) ^ 2)) := by
    intro q _ s _ m hm
    rw [Finset.mem_Icc] at hm
    have htail := pm9_tail_abs σ (pm9selm μ σ δ T n Tper q.1 q.2 s m) P ε hσ hε.indep hε.mgf
      (fun j => pm9_meas_selm μ σ δ T n Tper q.1 q.2 s m j)
      (fun j e e' he => pm9_loc_selm μ σ δ T n Tper q.1 q.2 s m j e e' he) T m (by omega)
      (pm9_count_selm μ σ δ T n Tper q.1 q.2 s m)
      ((m : ℝ) * pm9w σ δ Tper m) (by unfold pm9w; positivity)
    calc P (badD q s m) ≤ P {ω | ((m : ℝ) * pm9w σ δ Tper m) ≤
          |pm9S (pm9selm μ σ δ T n Tper q.1 q.2 s m) T (fun i => ε i ω)|} := by
          apply measure_mono
          intro ω hω
          simp only [hbadD, Set.mem_setOf_eq] at hω ⊢
          exact hω.le
      _ ≤ _ := htail
      _ = ENNReal.ofReal (2 * Real.exp (-((m : ℝ) * pm9w σ δ Tper m) ^ 2 /
          (2 * m * (σ : ℝ) ^ 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (pm9_exp_calc (σ : ℝ) δ Tper hσR hδ hd1 hδ1 m hm.1)
  -- the zeta bound
  have hzeta : ∑ m ∈ Icc 1 T, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
    have := sum_le_hasSum (Icc 1 T) (fun i _ => by positivity) hasSum_zeta_two
    have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
      have := Real.pi_lt_d2
      nlinarith [Real.pi_pos]
    linarith
  have hDsum : ∀ q ∈ I, ∀ s ∈ Icc 1 S,
      ∑ m ∈ Icc 1 T, δ ^ 2 / (32 * d ^ 2 * (m : ℝ) ^ 2) ≤ δ / (16 * d) := by
    intro q _ s _
    calc ∑ m ∈ Icc 1 T, δ ^ 2 / (32 * d ^ 2 * (m : ℝ) ^ 2)
        = δ ^ 2 / (32 * d ^ 2) * ∑ m ∈ Icc 1 T, (1 : ℝ) / (m : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          field_simp
      _ ≤ δ ^ 2 / (32 * d ^ 2) * 2 := by gcongr
      _ ≤ δ / (16 * d) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos hδ (by linarith : (0:ℝ) < d)]
  calc P (eventE μ ε σ δ T n Tper)ᶜ
      ≤ P ((⋃ q ∈ I, badB q) ∪ ⋃ q ∈ I, ⋃ s ∈ Icc 1 S, ⋃ m ∈ Icc 1 T, badD q s m) :=
        measure_mono hincl
    _ ≤ P (⋃ q ∈ I, badB q) + P (⋃ q ∈ I, ⋃ s ∈ Icc 1 S, ⋃ m ∈ Icc 1 T, badD q s m) :=
        measure_union_le _ _
    _ ≤ (∑ q ∈ I, ENNReal.ofReal (δ / (32 * d))) +
        ∑ q ∈ I, ∑ s ∈ Icc 1 S, ∑ m ∈ Icc 1 T,
          ENNReal.ofReal (δ ^ 2 / (32 * d ^ 2 * (m : ℝ) ^ 2)) := by
        gcongr
        · exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hB)
        · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun q hq => ?_))
          refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun s hs => ?_))
          exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (hD q hq s hs))
    _ ≤ (∑ q ∈ I, ENNReal.ofReal (δ / (32 * d))) +
        ∑ q ∈ I, ∑ s ∈ Icc 1 S, ENNReal.ofReal (δ / (16 * d)) := by
        gcongr with q hq s hs
        rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hDsum q hq s hs)
    _ = ENNReal.ofReal (I.card * (δ / (32 * d)) + I.card * (S * (δ / (16 * d)))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp
    _ ≤ ENNReal.ofReal (δ * S) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hIcard]
        have hdpos : (0 : ℝ) < d := by linarith
        have hS1R : (1 : ℝ) ≤ S := by exact_mod_cast hS1
        have e1 : d * (δ / (32 * d)) = δ / 32 := by field_simp
        have e2 : d * (S * (δ / (16 * d))) = S * δ / 16 := by field_simp
        rw [e1, e2]
        nlinarith
