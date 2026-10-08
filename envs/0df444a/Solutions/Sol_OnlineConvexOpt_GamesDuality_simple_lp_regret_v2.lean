-- Prove2me | solution 1 for OnlineConvexOpt.GamesDuality.simple_lp_regret_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:52:07.236318+00:00
-- url     : https://prove2.me/submissions/947bdc3d-2879-41cb-84e8-ce9ceeba0457

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
lemma p6b_hoeff_fin {n : ℕ} (w : Fin n → ℝ) (hw : w ∈ stdSimplex ℝ (Fin n)) (ℓ : Fin n → ℝ)
    (hℓ : ∀ i, -1 ≤ ℓ i ∧ ℓ i ≤ 1) (s : ℝ) :
    ∑ i, w i * Real.exp (s * ℓ i) ≤ Real.exp (s * ∑ i, w i * ℓ i + s ^ 2 / 2) := by
  classical
  obtain ⟨hw0, hw1⟩ := hw
  let μ : Measure (Fin n) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac i
  have hμs : ∀ j, μ {j} = ENNReal.ofReal (w j) := by
    intro j
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator]
  have hμr : ∀ j, μ.real {j} = w j := by
    intro j
    rw [measureReal_def, hμs, ENNReal.toReal_ofReal (hw0 j)]
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]
  have hint : ∀ f : Fin n → ℝ, ∫ x, f x ∂μ = ∑ i, w i * f i := by
    intro f
    rw [integral_fintype (Integrable.of_finite)]
    simp [hμr]
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (a := -1) (b := 1)
    (Measurable.of_discrete).aemeasurable (Filter.Eventually.of_forall fun i => ⟨(hℓ i).1, (hℓ i).2⟩)
  have h2 := hH.mgf_le s
  have hc : ((‖(1:ℝ) - -1‖₊ / 2) ^ 2 : NNReal) = 1 := by
    have : ‖(1:ℝ) - -1‖₊ = 2 := by
      ext; simp; norm_num
    rw [this]; norm_num
  rw [hc] at h2
  simp only [mgf, hint, NNReal.coe_one, one_mul] at h2
  set m := ∑ i, w i * ℓ i
  have key : ∑ i, w i * Real.exp (s * ℓ i) =
      Real.exp (s * m) * ∑ i, w i * Real.exp (s * (ℓ i - m)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, Real.exp_sub]; field_simp
  rw [key, Real.exp_add]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

lemma p6b_closed {n : ℕ} (hn : 0 < n) (η : ℝ) (ℓ : ℕ → Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (h0 : ∀ i, x 0 i = 1 / (n : ℝ))
    (hu : ∀ t i, x (t + 1) i =
      x t i * Real.exp (-η * ℓ t i) / ∑ j, x t j * Real.exp (-η * ℓ t j)) :
    ∀ t i, x t i = Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s i) /
      ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro t
  induction t with
  | zero => intro i; simp [h0]
  | succ t ih =>
    intro i
    have hZ : 0 < ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) :=
      Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
    have hW : 0 < ∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) * Real.exp (-η * ℓ t j) :=
      Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
    have hE : ∀ j, Real.exp (-η * ∑ s ∈ Finset.range (t + 1), ℓ s j) =
        Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) * Real.exp (-η * ℓ t j) := by
      intro j; rw [Finset.sum_range_succ, mul_add, Real.exp_add]
    rw [hu, ih i]
    simp_rw [ih, hE]
    rw [show (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) /
        (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j)) * Real.exp (-η * ℓ t j)) =
        (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) * Real.exp (-η * ℓ t j)) /
        (∑ j, Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j)) by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => ?_; ring]
    field_simp

lemma p6b_regret {n T : ℕ} (hn : 0 < n) (hT : 0 < T) (η : ℝ)
    (hη : η = Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ)))
    (ℓ : ℕ → Fin n → ℝ) (hℓ : ∀ t i, -1 ≤ ℓ t i ∧ ℓ t i ≤ 1) (x : ℕ → Fin n → ℝ)
    (h0 : ∀ i, x 0 i = 1 / (n : ℝ))
    (hu : ∀ t i, x (t + 1) i =
      x t i * Real.exp (-η * ℓ t i) / ∑ j, x t j * Real.exp (-η * ℓ t j)) :
    (∀ t, x t ∈ stdSimplex ℝ (Fin n)) ∧
    ∀ i, ∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j ≤
      ∑ t ∈ Finset.range T, ℓ t i + T * η := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hc := p6b_closed hn η ℓ x h0 hu
  set E : ℕ → Fin n → ℝ := fun t j => Real.exp (-η * ∑ s ∈ Finset.range t, ℓ s j) with hEdef
  set Z : ℕ → ℝ := fun t => ∑ j, E t j with hZdef
  have hZpos : ∀ t, 0 < Z t := fun t =>
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hxs : ∀ t, x t ∈ stdSimplex ℝ (Fin n) := by
    intro t
    refine ⟨fun i => ?_, ?_⟩
    · rw [hc t i]; exact div_nonneg (Real.exp_pos _).le (hZpos t).le
    · simp_rw [hc t]; rw [← Finset.sum_div]; exact div_self (hZpos t).ne'
  refine ⟨hxs, ?_⟩
  intro i
  set m : ℕ → ℝ := fun t => ∑ j, x t j * ℓ t j with hm
  -- one-step potential bound
  have hstep : ∀ t, Z (t + 1) ≤ Z t * Real.exp (-η * m t + η ^ 2 / 2) := by
    intro t
    have hH := p6b_hoeff_fin (x t) (hxs t) (ℓ t) (hℓ t) (-η)
    rw [neg_sq] at hH
    have hEq : ∑ j, x t j * Real.exp (-η * ℓ t j) = Z (t + 1) / Z t := by
      simp_rw [hc t]
      rw [show Z (t + 1) = ∑ j, E t j * Real.exp (-η * ℓ t j) by
        simp only [hZdef, hEdef]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_range_succ, mul_add, Real.exp_add]]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hZdef, hEdef]; ring
    rw [hEq, div_le_iff₀ (hZpos t)] at hH
    calc Z (t + 1) ≤ Real.exp (-η * m t + η ^ 2 / 2) * Z t := by
          simpa [hm, mul_comm, mul_left_comm, mul_assoc] using hH
      _ = _ := by ring
  have hiter : ∀ N, Z N ≤ Z 0 * Real.exp (∑ t ∈ Finset.range N, (-η * m t + η ^ 2 / 2)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      calc Z (N + 1) ≤ Z N * Real.exp (-η * m N + η ^ 2 / 2) := hstep N
        _ ≤ Z 0 * Real.exp (∑ t ∈ Finset.range N, (-η * m t + η ^ 2 / 2)) *
              Real.exp (-η * m N + η ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add, Finset.sum_range_succ]
  have hZ0 : Z 0 = (n : ℝ) := by simp [hZdef, hEdef]
  have hlow : E T i ≤ Z T :=
    Finset.single_le_sum (f := E T) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog : -η * ∑ s ∈ Finset.range T, ℓ s i ≤
      Real.log n + ∑ t ∈ Finset.range T, (-η * m t + η ^ 2 / 2) := by
    have h := hlow.trans (hiter T)
    rw [hZ0, ← Real.exp_log hnpos, ← Real.exp_add] at h
    exact Real.exp_le_exp.mp h
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hη2 : η ^ 2 = 2 * Real.log n / T := by
    rw [hη, Real.sq_sqrt (by positivity)]
  have hlogeq : Real.log n = T * η ^ 2 / 2 := by
    rw [hη2]; field_simp
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hlogeq] at hlog
  have hη0 : 0 ≤ η := by rw [hη]; exact Real.sqrt_nonneg _
  rcases hη0.lt_or_eq with hpos | hzero
  · -- η > 0
    have : η * (∑ t ∈ Finset.range T, m t) ≤ η * (∑ s ∈ Finset.range T, ℓ s i + T * η) := by
      nlinarith
    exact le_of_mul_le_mul_left this hpos
  · -- η = 0, so log n = 0, so n = 1
    have hl0 : Real.log (n : ℝ) = 0 := by rw [hlogeq, ← hzero]; ring
    have hn1 : n = 1 := by
      rcases Real.log_eq_zero.mp hl0 with h | h | h
      · exact absurd h hnpos.ne'
      · exact_mod_cast h
      · linarith
    subst hn1
    rw [← hzero, mul_zero, add_zero]
    refine Finset.sum_le_sum fun t _ => ?_
    have hsub : ∀ j : Fin 1, j = i := fun j => Subsingleton.elim _ _
    have h1 := (hxs t).2
    rw [Fin.sum_univ_one] at h1 ⊢
    rw [hsub 0] at h1 ⊢
    rw [h1, one_mul]

open OnlineConvexOpt.GamesDuality in
theorem solution {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y) :
    ∀ y' ∈ stdSimplex ℝ (Fin m),
      rowValue A (average x T) y' ≤
        lambdaR A + Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (T : ℝ) := by
  intro y' hy'
  set η := Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ)) with hη
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hrw : Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (T : ℝ) = η := by
    rw [hη, Real.sqrt_div' _ hTpos.le]
  rw [hrw]
  set ℓ : ℕ → Fin n → ℝ := fun t => A.mulVec (y t) with hℓdef
  have hℓ : ∀ t i, -1 ≤ ℓ t i ∧ ℓ t i ≤ 1 := by
    intro t i
    obtain ⟨⟨hy0, hy1⟩, -⟩ := hrun.best_response t
    have hb : |ℓ t i| ≤ 1 := by
      simp only [hℓdef, Matrix.mulVec, dotProduct]
      calc |∑ j, A i j * y t j| ≤ ∑ j, |A i j * y t j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, y t j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (hy0 j)]
          exact mul_le_of_le_one_left (hy0 j) (hA i j)
        _ = 1 := hy1
    exact abs_le.mp hb
  obtain ⟨hxs, hreg⟩ := p6b_regret hn hT η hη ℓ hℓ x hrun.init hrun.update
  have hrv : ∀ (u : Fin n → ℝ) t, rowValue A u (y t) = ∑ j, u j * ℓ t j := by
    intro u t; simp [rowValue, dotProduct, hℓdef]
  -- average decomposition
  have h1 : rowValue A (average x T) y' =
      (∑ t ∈ Finset.range T, rowValue A (x t) y') / T := by
    rw [eq_div_iff hTpos.ne']
    simp only [rowValue, dotProduct, average]
    rw [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTpos.ne', Finset.sum_mul]
  have h2 : ∑ t ∈ Finset.range T, rowValue A (x t) y' ≤
      ∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j := by
    refine Finset.sum_le_sum fun t _ => ?_
    rw [← hrv]
    exact (hrun.best_response t).2 y' hy'
  rw [h1]
  have hgoal : (∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j) / T - η ≤ lambdaR A := by
    unfold lambdaR
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply le_csInf (Set.Nonempty.image _ ⟨x 0, hxs 0⟩)
    rintro _ ⟨xs, hxs', rfl⟩
    have hbdd : BddAbove ((fun y => rowValue A xs y) '' stdSimplex ℝ (Fin m)) := by
      apply IsCompact.bddAbove_image (isCompact_stdSimplex ℝ (Fin m))
      apply Continuous.continuousOn
      simp only [rowValue, dotProduct, Matrix.mulVec]
      fun_prop
    set S := sSup ((fun y => rowValue A xs y) '' stdSimplex ℝ (Fin m))
    have hS : ∀ t, rowValue A xs (y t) ≤ S := fun t =>
      le_csSup hbdd ⟨y t, (hrun.best_response t).1, rfl⟩
    have hsumS : ∑ t ∈ Finset.range T, rowValue A xs (y t) ≤ T * S := by
      calc ∑ t ∈ Finset.range T, rowValue A xs (y t) ≤ ∑ t ∈ Finset.range T, S :=
            Finset.sum_le_sum fun t _ => hS t
        _ = T * S := by simp
    have hmix : ∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j ≤
        ∑ t ∈ Finset.range T, rowValue A xs (y t) + T * η := by
      obtain ⟨hxs0, hxs1⟩ := hxs'
      calc ∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j
          = ∑ i, xs i * ∑ t ∈ Finset.range T, ∑ j, x t j * ℓ t j := by
            rw [← Finset.sum_mul, hxs1, one_mul]
        _ ≤ ∑ i, xs i * (∑ t ∈ Finset.range T, ℓ t i + T * η) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hreg i) (hxs0 i)
        _ = ∑ t ∈ Finset.range T, rowValue A xs (y t) + T * η := by
            simp_rw [hrv, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hxs1, one_mul,
              Finset.mul_sum]
            rw [Finset.sum_comm]
    rw [sub_le_iff_le_add, div_le_iff₀ hTpos]
    nlinarith
  have h3 := div_le_div_of_nonneg_right h2 hTpos.le
  linarith
