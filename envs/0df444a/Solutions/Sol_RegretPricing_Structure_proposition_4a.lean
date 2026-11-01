-- Prove2me | solution 1 for RegretPricing.Structure.proposition_4a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:10:41.911588+00:00
-- url     : https://prove2.me/submissions/7c50069f-79af-48ea-be30-0afa77560d74

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

open RegretPricing.Structure MeasureTheory

section RPBasic

variable (D : WTP) (hD : D.Standing)
include hD

lemma rp_F_nonneg (x : ℝ) : 0 ≤ D.F x :=
  setIntegral_nonneg measurableSet_Iic (fun t _ => hD.2.2.1 t)

lemma rp_F_le_one (x : ℝ) : D.F x ≤ 1 := by
  have := setIntegral_le_integral (s := Set.Iic x) hD.2.2.2.2.1
    (Filter.Eventually.of_forall hD.2.2.1)
  unfold WTP.F; linarith [hD.2.2.2.2.2.1]

lemma rp_F_eq_one (x : ℝ) (hx : D.b ≤ x) : D.F x = 1 := by
  unfold WTP.F
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hD.2.2.2.2.2.1]
  intro t ht
  apply hD.2.2.2.1
  intro h; exact ht (Set.mem_Iic.2 (le_trans h.2 hx))

lemma rp_F_eq_zero (x : ℝ) (hx : x < D.a) : D.F x = 0 := by
  unfold WTP.F
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  apply hD.2.2.2.1
  intro h; exact absurd (lt_of_le_of_lt (le_trans h.1 ht) hx) (lt_irrefl _)

lemma rp_F_sub (y p : ℝ) : D.F p - D.F y = ∫ t in y..p, D.f t := by
  unfold WTP.F
  exact intervalIntegral.integral_Iic_sub_Iic hD.2.2.2.2.1.integrableOn
    hD.2.2.2.2.1.integrableOn

lemma rp_F_mono {y p : ℝ} (h : y ≤ p) : D.F y ≤ D.F p := by
  have := rp_F_sub D hD y p
  have h2 : 0 ≤ ∫ t in y..p, D.f t :=
    intervalIntegral.integral_nonneg h (fun t _ => hD.2.2.1 t)
  linarith

lemma rp_F_lip : ∃ M, 0 ≤ M ∧ ∀ y p, y ≤ p → D.F p - D.F y ≤ M * (p - y) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := D.a) (b := D.b)).exists_bound_of_continuousOn
    hD.2.2.2.2.2.2
  have hb : ∀ x, ‖D.f x‖ ≤ max C 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc D.a D.b
    · exact le_trans (hC x hx) (le_max_left _ _)
    · rw [hD.2.2.2.1 x hx]; simp
  refine ⟨max C 0, le_max_right _ _, fun y p hyp => ?_⟩
  rw [rp_F_sub D hD y p]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := p)
    (f := D.f) (C := max C 0) (fun x _ => hb x)
  rw [abs_of_nonneg (by linarith)] at this
  exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)

lemma rp_Fbar_sub {y p : ℝ} (h : y ≤ p) : 0 ≤ D.Fbar y - D.Fbar p ∧ D.Fbar y - D.Fbar p ≤ 1 := by
  unfold WTP.Fbar
  have := rp_F_mono D hD h
  have := rp_F_nonneg D hD y
  have := rp_F_le_one D hD p
  constructor <;> linarith

lemma rp_Fbar_bds (y : ℝ) : 0 ≤ D.Fbar y ∧ D.Fbar y ≤ 1 := by
  unfold WTP.Fbar
  have := rp_F_nonneg D hD y
  have := rp_F_le_one D hD y
  constructor <;> linarith

lemma rp_rev_le (z : ℝ) (hz : z ≤ D.b) (y : ℝ) : revenue D y z ≤ D.b - z := by
  unfold revenue
  by_cases hy : D.b ≤ y
  · rw [WTP.Fbar, rp_F_eq_one D hD y hy]; simp; linarith
  · have hy' : y < D.b := lt_of_not_ge hy
    obtain ⟨h0, h1⟩ := rp_Fbar_bds D hD y
    by_cases hyz : z ≤ y
    · nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ y - z by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ z - y by linarith) h0]

lemma rp_ro_bdd (p z : ℝ) :
    BddAbove (Set.range fun y : {y : ℝ // y < p} => (y.1 - z) * (D.Fbar y.1 - D.Fbar p)) := by
  refine ⟨max (p - z) 0, ?_⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨h0, h1⟩ := rp_Fbar_sub D hD y.2.le
  have hy := y.2
  by_cases hyz : z ≤ y.1
  · have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ y.1 - z by linarith)
    simp only
    exact le_trans (by linarith) (le_max_left _ _)
  · have := mul_nonneg (show 0 ≤ z - y.1 by linarith) h0
    simp only
    exact le_trans (by nlinarith) (le_max_right _ _)

lemma rp_ro_nonneg (p z : ℝ) : 0 ≤ ro D p z := by
  unfold ro
  by_cases hpz : z < p
  · refine le_trans ?_ (le_ciSup (rp_ro_bdd D hD p z) ⟨(z + p) / 2, by linarith⟩)
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD (show (z + p) / 2 ≤ p by linarith)
    exact mul_nonneg (by linarith) h0
  · push Not at hpz
    obtain ⟨M, hM0, hM⟩ := rp_F_lip D hD
    by_contra hneg
    push Not at hneg
    set r := ⨆ y : {y : ℝ // y < p}, (y.1 - z) * (D.Fbar y.1 - D.Fbar p) with hr
    set ε := -r with hε
    have hεpos : 0 < ε := by linarith
    set K := (z - p + 1) * (M + 1) with hK
    have hKpos : 0 < K := by positivity
    set δ := min 1 (ε / (2 * K)) with hδ
    have hδpos : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * K) := min_le_right _ _
    have hle := le_ciSup (rp_ro_bdd D hD p z) ⟨p - δ, by linarith⟩
    simp only at hle
    have hFd : D.Fbar (p - δ) - D.Fbar p ≤ M * δ := by
      have := hM (p - δ) p (by linarith)
      unfold WTP.Fbar; linarith
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD (show p - δ ≤ p by linarith)
    have h3 : (z - (p - δ)) * (D.Fbar (p - δ) - D.Fbar p) ≤ (z - p + 1) * ((M + 1) * δ) :=
      mul_le_mul (by linarith) (by nlinarith) h0 (by linarith)
    have h4 : K * δ ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left hδ2 hKpos.le
      rw [show K * (ε / (2 * K)) = ε / 2 by field_simp] at this
      exact this
    have : (z - p + 1) * ((M + 1) * δ) = K * δ := by rw [hK]; ring
    nlinarith

lemma rp_ro_anti (p : ℝ) {z z' : ℝ} (h : z ≤ z') : ro D p z' ≤ ro D p z := by
  unfold ro
  apply ciSup_mono (rp_ro_bdd D hD p z)
  intro y
  obtain ⟨h0, -⟩ := rp_Fbar_sub D hD y.2.le
  exact mul_le_mul_of_nonneg_right (by linarith) h0

lemma rp_S_bdd (p z : ℝ) (hz : z ≤ D.b) :
    BddAbove (Set.range fun y : {y : ℝ // p ≤ y} => revenue D y.1 z) :=
  ⟨D.b - z, by rintro _ ⟨y, rfl⟩; exact rp_rev_le D hD z hz y.1⟩

lemma rp_ru_nonneg (p z : ℝ) (hz : z ≤ D.b) : 0 ≤ ru D p z := by
  unfold ru
  have := le_ciSup (rp_S_bdd D hD p z hz) ⟨p, le_refl _⟩
  simp only at this
  linarith

lemma rp_ru_diff (p : ℝ) {z z' : ℝ} (h : z ≤ z') (hz' : z' ≤ D.b) :
    -(z' - z) ≤ ru D p z - ru D p z' := by
  unfold ru
  have hS : (⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z') ≤
      ⨆ y : {y : ℝ // p ≤ y}, revenue D y.1 z := by
    apply ciSup_mono (rp_S_bdd D hD p z (le_trans h hz'))
    intro y
    unfold revenue
    obtain ⟨h0, -⟩ := rp_Fbar_bds D hD y.1
    nlinarith [mul_nonneg (show 0 ≤ z' - z by linarith) h0]
  have : revenue D p z - revenue D p z' ≤ z' - z := by
    unfold revenue
    obtain ⟨h0, h1⟩ := rp_Fbar_bds D hD p
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ z' - z by linarith)]
  linarith

lemma rp_πhat_le (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (p z : ℝ) (hz : z ≤ D.b) :
    πhat D α β p z ≤ D.b - z := by
  unfold πhat
  have := rp_rev_le D hD z hz p
  nlinarith [mul_nonneg hα (rp_ro_nonneg D hD p z), mul_nonneg hβ (rp_ru_nonneg D hD p z hz)]

lemma rp_πhat_diff (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β ∧ β ≤ 1) (p : ℝ) {z z' : ℝ}
    (h : z ≤ z') (hz' : z' ≤ D.b) :
    πhat D α β p z ≤ πhat D α β p z' + 2 * (z' - z) := by
  unfold πhat
  have h1 : revenue D p z - revenue D p z' ≤ z' - z := by
    unfold revenue
    obtain ⟨h0, h1⟩ := rp_Fbar_bds D hD p
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ z' - z by linarith)]
  have h2 := rp_ro_anti D hD p h
  have h3 := rp_ru_diff D hD p h hz'
  nlinarith [mul_le_mul_of_nonneg_left h2 hα, mul_le_mul_of_nonneg_left h3 hβ.1]

lemma rp_V_le (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (z : ℝ) (hz : z ≤ D.b) :
    regretValue D α β z ≤ D.b - z :=
  ciSup_le fun p => rp_πhat_le D hD α β hα hβ p z hz

lemma rp_V_ge (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (z : ℝ) (hz : z ≤ D.b) (p : ℝ) :
    πhat D α β p z ≤ regretValue D α β z :=
  le_ciSup (f := fun p => πhat D α β p z)
    ⟨D.b - z, by rintro _ ⟨q, rfl⟩; exact rp_πhat_le D hD α β hα hβ q z hz⟩ p

lemma rp_V_lip (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β ∧ β ≤ 1) {z z' : ℝ} (h : z ≤ z')
    (hz' : z' ≤ D.b) :
    regretValue D α β z ≤ regretValue D α β z' + 2 * (z' - z) := by
  apply ciSup_le
  intro p
  have := rp_πhat_diff D hD α β hα hβ p h hz'
  have := rp_V_ge D hD α β hα hβ.1 z' hz' p
  linarith

lemma rp_V_b_nonneg (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 ≤ regretValue D α β D.b := by
  refine le_trans ?_ (rp_V_ge D hD α β hα hβ D.b le_rfl D.b)
  have hro : ro D D.b D.b ≤ 0 := by
    unfold ro
    haveI : Nonempty {y : ℝ // y < D.b} := ⟨⟨D.b - 1, by linarith⟩⟩
    apply ciSup_le
    intro y
    obtain ⟨h0, -⟩ := rp_Fbar_sub D hD y.2.le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [y.2]) h0
  have hru : ru D D.b D.b ≤ 0 := by
    unfold ru
    haveI : Nonempty {y : ℝ // D.b ≤ y} := ⟨⟨D.b, le_rfl⟩⟩
    have : (⨆ y : {y : ℝ // D.b ≤ y}, revenue D y.1 D.b) ≤ 0 := by
      apply ciSup_le
      intro y
      unfold revenue WTP.Fbar
      rw [rp_F_eq_one D hD y.1 y.2]; simp
    have : revenue D D.b D.b = 0 := by unfold revenue; simp
    linarith
  unfold πhat
  have : revenue D D.b D.b = 0 := by unfold revenue; simp
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hro, mul_nonpos_of_nonneg_of_nonpos hβ hru]

end RPBasic

theorem solution (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β lam : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (hlam : 0 ≤ lam ∧ lam ≤ 1 / 2)
    (hm : AntitoneOn (regretValue D α β) (Set.Icc 0 D.b)) :
    (∀ t x : ℕ, 1 ≤ x → dU D α β lam t x ≤ dU D α β lam (t + 1) x) ∧
      (∀ t x : ℕ, 1 ≤ x → dU D α β lam t (x + 1) ≤ dU D α β lam t x) := by
  set V := regretValue D α β with hVdef
  have ha0 : 0 ≤ D.a := hD.1
  have hab : D.a < D.b := hD.2.1
  have hb0 : 0 ≤ D.b := by linarith
  have hVnn : ∀ z, 0 ≤ z → z ≤ D.b → 0 ≤ V z := fun z h0 h1 =>
    le_trans (rp_V_b_nonneg D hD α β hα.1 hβ.1) (hm ⟨h0, h1⟩ ⟨hb0, le_rfl⟩ h1)
  have hVle : ∀ z, z ≤ D.b → V z ≤ D.b - z := fun z hz => rp_V_le D hD α β hα.1 hβ.1 z hz
  have hVlip : ∀ z z', z ≤ z' → z' ≤ D.b → V z ≤ V z' + 2 * (z' - z) :=
    fun z z' h hz' => rp_V_lip D hD α β hα.1 hβ h hz'
  -- g t k = ΔU_t(k+1)
  set g : ℕ → ℕ → ℝ := fun t k => dU D α β lam t (k + 1) with hg
  have hU0 : ∀ t, U D α β lam t 0 = 0 := by intro t; cases t <;> rfl
  have hg0 : ∀ t, g (t + 1) 0 = g t 0 + lam * V (g t 0) := by
    intro t; simp [hg, dU, hU0, U, hVdef]
  have hgs : ∀ t j, g (t + 1) (j + 1) = g t (j + 1) + lam * (V (g t (j + 1)) - V (g t j)) := by
    intro t j; simp only [hg, dU, U, hVdef, Nat.add_sub_cancel]; ring
  have hgz : ∀ k, g 0 k = 0 := by intro k; simp [hg, dU, U]
  -- invariant
  let Q : ℕ → Prop := fun t => ∀ k, 0 ≤ g t k ∧ g t k ≤ D.b ∧ g t (k + 1) ≤ g t k
  have hstep : ∀ t, Q t → ∀ k, g t k ≤ g (t + 1) k := by
    intro t hQ k
    cases k with
    | zero =>
      rw [hg0]
      have := hVnn _ (hQ 0).1 (hQ 0).2.1
      nlinarith [mul_nonneg hlam.1 this]
    | succ j =>
      rw [hgs]
      have := hm ⟨(hQ (j + 1)).1, (hQ (j + 1)).2.1⟩ ⟨(hQ j).1, (hQ j).2.1⟩ (hQ j).2.2
      nlinarith [mul_nonneg hlam.1 (sub_nonneg.2 this)]
  have hQ : ∀ t, Q t := by
    intro t
    induction t with
    | zero => intro k; simp [hgz]; exact hb0
    | succ t ih =>
      have hmono := hstep t ih
      have hxm : ∀ k, g (t + 1) (k + 1) ≤ g (t + 1) k := by
        intro k
        cases k with
        | zero =>
          rw [hg0, hgs]
          have hl := hVlip _ _ (ih 0).2.2 (ih 0).2.1
          have hn := hVnn _ (ih 0).1 (ih 0).2.1
          have e1 : lam * (V (g t (0 + 1)) - V (g t 0)) ≤ lam * (2 * (g t 0 - g t (0 + 1))) :=
            mul_le_mul_of_nonneg_left (by linarith) hlam.1
          have e2 : lam * (2 * (g t 0 - g t (0 + 1))) ≤ g t 0 - g t (0 + 1) := by
            nlinarith [(ih 0).2.2]
          nlinarith [mul_nonneg hlam.1 hn]
        | succ j =>
          rw [hgs, hgs]
          have hl := hVlip _ _ (ih (j + 1)).2.2 (ih (j + 1)).2.1
          have ha := hm ⟨(ih (j + 1)).1, (ih (j + 1)).2.1⟩ ⟨(ih j).1, (ih j).2.1⟩ (ih j).2.2
          have e1 : lam * (V (g t (j + 1 + 1)) - V (g t (j + 1))) ≤
              lam * (2 * (g t (j + 1) - g t (j + 1 + 1))) :=
            mul_le_mul_of_nonneg_left (by linarith) hlam.1
          have e2 : lam * (2 * (g t (j + 1) - g t (j + 1 + 1))) ≤ g t (j + 1) - g t (j + 1 + 1) := by
            nlinarith [(ih (j + 1)).2.2]
          nlinarith [mul_nonneg hlam.1 (sub_nonneg.2 ha)]
      have h0b : g (t + 1) 0 ≤ D.b := by
        rw [hg0]
        have := hVle _ (ih 0).2.1
        have e1 : lam * V (g t 0) ≤ lam * (D.b - g t 0) := mul_le_mul_of_nonneg_left this hlam.1
        nlinarith [(ih 0).2.1]
      have hkb : ∀ k, g (t + 1) k ≤ D.b := by
        intro k
        induction k with
        | zero => exact h0b
        | succ k ihk => exact le_trans (hxm k) ihk
      intro k
      exact ⟨le_trans (ih k).1 (hmono k), hkb k, hxm k⟩
  refine ⟨?_, ?_⟩
  · intro t x hx
    obtain ⟨k, rfl⟩ : ∃ k, x = k + 1 := ⟨x - 1, by omega⟩
    exact hstep t (hQ t) k
  · intro t x hx
    obtain ⟨k, rfl⟩ : ∃ k, x = k + 1 := ⟨x - 1, by omega⟩
    exact (hQ t k).2.2
