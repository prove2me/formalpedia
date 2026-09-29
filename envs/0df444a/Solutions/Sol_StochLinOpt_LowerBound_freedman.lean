-- Prove2me | solution 1 for StochLinOpt.LowerBound.freedman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:21:06.337838+00:00
-- url     : https://prove2.me/submissions/ed72e726-68fe-4f5b-b52f-4cf8c8c2a6af

import Mathlib

open MeasureTheory


namespace StochLinOpt.LowerBound

lemma fr_hprime_mono : Monotone (fun y : ℝ => 4 + 2*y - (4 - 2*y) * Real.exp y) := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => 4 + 2*y - (4 - 2*y) * Real.exp y)
      (2 * (1 - (1 - y) * Real.exp y)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 4 + 2*y) 2 y := by
      simpa using ((hasDerivAt_id y).const_mul 2).const_add 4
    have h2 : HasDerivAt (fun y : ℝ => 4 - 2*y) (-2) y := by
      simpa using ((hasDerivAt_id y).const_mul 2).const_sub 4
    have h3 := h2.mul (Real.hasDerivAt_exp y)
    exact (h1.sub h3).congr_deriv (by ring)
  apply monotone_of_deriv_nonneg
  · intro y; exact (hd y).differentiableAt
  · intro y
    rw [(hd y).deriv]
    have h := Real.add_one_le_exp (-y)
    have : (1 - y) * Real.exp y ≤ 1 := by
      have e := Real.exp_pos y
      calc (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y := by
            apply mul_le_mul_of_nonneg_right (by linarith) e.le
        _ = 1 := by rw [← Real.exp_add]; simp
    linarith

lemma fr_h_nonneg (y : ℝ) : (6 - 2*y) * Real.exp y ≤ 6 + 4*y + y^2 := by
  set h : ℝ → ℝ := fun y => 6 + 4*y + y^2 - (6 - 2*y) * Real.exp y with hh
  have hd : ∀ y : ℝ, HasDerivAt h (4 + 2*y - (4 - 2*y) * Real.exp y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 6 + 4*y + y^2) (4 + 2*y) y := by
      have := (((hasDerivAt_id y).const_mul 4).const_add 6).add (hasDerivAt_pow 2 y)
      exact this.congr_deriv (by simp)
    have h2 : HasDerivAt (fun y : ℝ => 6 - 2*y) (-2) y := by
      simpa using ((hasDerivAt_id y).const_mul 2).const_sub 6
    have h3 := h2.mul (Real.hasDerivAt_exp y)
    exact (h1.sub h3).congr_deriv (by ring)
  have hdiff : Differentiable ℝ h := fun y => (hd y).differentiableAt
  have h0 : h 0 = 0 := by simp [hh]
  suffices 0 ≤ h y by simp only [hh] at this; linarith
  rcases le_total 0 y with hy | hy
  · have hm : MonotoneOn h (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have := fr_hprime_mono (le_of_lt (Set.mem_Ioi.mp hx))
      simp only at this; linarith
    have := hm (Set.self_mem_Ici) hy hy
    linarith
  · have hm : AntitoneOn h (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(hd x).deriv]
      have := fr_hprime_mono (le_of_lt (Set.mem_Iio.mp hx))
      simp only at this; linarith
    have := hm hy (Set.self_mem_Iic) hy
    linarith

/-- For `y ≤ β < 3`: `exp y ≤ 1 + y + 3 y^2/(6 - 2β)`. -/
lemma fr_exp_bound (y β : ℝ) (hyβ : y ≤ β) (hβ : β < 3) :
    Real.exp y ≤ 1 + y + 3 * y^2 / (6 - 2*β) := by
  have hpos : 0 < 6 - 2*y := by linarith
  have hpos' : 0 < 6 - 2*β := by linarith
  have h := fr_h_nonneg y
  have h1 : Real.exp y ≤ 1 + y + 3 * y^2 / (6 - 2*y) := by
    rw [← sub_nonneg]
    have : 1 + y + 3 * y^2 / (6 - 2*y) - Real.exp y
        = (6 + 4*y + y^2 - (6 - 2*y) * Real.exp y) / (6 - 2*y) := by
      rw [eq_div_iff hpos.ne', sub_mul, add_mul, div_mul_cancel₀ _ hpos.ne']; ring
    rw [this]; apply div_nonneg <;> linarith
  have h2 : 3 * y^2 / (6 - 2*y) ≤ 3 * y^2 / (6 - 2*β) :=
    div_le_div_of_nonneg_left (by positivity) hpos' (by linarith)
  linarith


lemma fr_pull {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {Y f : Ω → ℝ} (hY : StronglyMeasurable[m] Y) (M : ℝ)
    (hYM : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ M) (hf : Integrable f P) :
    ∫ ω, Y ω * f ω ∂P = ∫ ω, Y ω * (P[f | m]) ω ∂P := by
  have h1 := condExp_stronglyMeasurable_mul_of_bound hm hY hf M hYM
  rw [← integral_condExp hm]
  exact integral_congr_ae h1

lemma fr_step {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {Y Xk : Ω → ℝ} (hY : StronglyMeasurable[m] Y) (hY0 : ∀ ω, 0 ≤ Y ω) (M : ℝ)
    (hYM : ∀ᵐ ω ∂P, Y ω ≤ M) (hX : Measurable Xk) (hXi : Integrable Xk P)
    (hXi2 : Integrable (fun ω => Xk ω ^ 2) P) (hmd : P[Xk | m] =ᵐ[P] 0) (b : ℝ)
    (hb : ∀ᵐ ω ∂P, Xk ω ≤ b) (l c : ℝ) (hl : 0 ≤ l)
    (hineq : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2) :
    ∫ ω, Y ω * Real.exp (l * Xk ω) ∂P
      ≤ ∫ ω, Y ω * (1 + c * (P[fun ω' => Xk ω' ^ 2 | m]) ω) ∂P := by
  have hYM' : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ M := by
    filter_upwards [hYM] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]; exact h
  have hYs : AEStronglyMeasurable Y P := (hY.mono hm).aestronglyMeasurable
  have hint1 : Integrable (fun ω => Y ω * Real.exp (l * Xk ω)) P := by
    refine Integrable.of_bound (hYs.mul ?_) (M * Real.exp (l * b)) ?_
    · exact (Real.measurable_exp.comp (hX.const_mul l)).aestronglyMeasurable
    · filter_upwards [hYM, hb] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hY0 ω) (Real.exp_pos _).le)]
      apply mul_le_mul h1 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 hl))
        (Real.exp_pos _).le (le_trans (hY0 ω) h1)
  have iY : Integrable Y P := Integrable.of_bound hYs M hYM'
  have iYX : Integrable (fun ω => Y ω * Xk ω) P := hXi.bdd_mul hYs hYM'
  have iYX2 : Integrable (fun ω => Y ω * Xk ω ^ 2) P := hXi2.bdd_mul hYs hYM'
  have iYW : Integrable (fun ω => Y ω * (P[fun ω' => Xk ω' ^ 2 | m]) ω) P :=
    (integrable_condExp).bdd_mul hYs hYM'
  calc ∫ ω, Y ω * Real.exp (l * Xk ω) ∂P
      ≤ ∫ ω, (Y ω + l * (Y ω * Xk ω) + c * (Y ω * Xk ω ^ 2)) ∂P := by
        apply integral_mono_ae hint1 ((iY.add (iYX.const_mul l)).add (iYX2.const_mul c))
        filter_upwards [hb] with ω h
        have := mul_le_mul_of_nonneg_left (hineq _ h) (hY0 ω)
        simp only [Pi.add_apply]; nlinarith
    _ = ∫ ω, Y ω ∂P + l * ∫ ω, Y ω * Xk ω ∂P + c * ∫ ω, Y ω * Xk ω ^ 2 ∂P := by
        have iA : Integrable (fun ω => Y ω + l * (Y ω * Xk ω)) P := iY.add (iYX.const_mul l)
        rw [integral_add iA (iYX2.const_mul c),
          integral_add iY (iYX.const_mul l), integral_const_mul, integral_const_mul]
    _ = ∫ ω, Y ω ∂P + c * ∫ ω, Y ω * (P[fun ω' => Xk ω' ^ 2 | m]) ω ∂P := by
        rw [fr_pull hm hY M hYM' hXi, fr_pull hm hY M hYM' hXi2]
        have : ∫ ω, Y ω * (P[Xk | m]) ω ∂P = 0 := by
          rw [integral_congr_ae (g := fun _ => (0:ℝ))]
          · simp
          · filter_upwards [hmd] with ω h
            simp [h]
        rw [this]; ring
    _ = ∫ ω, Y ω * (1 + c * (P[fun ω' => Xk ω' ^ 2 | m]) ω) ∂P := by
        rw [← integral_const_mul, ← integral_add iY (iYW.const_mul c)]
        congr 1; ext ω; ring


theorem fr_supermart {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[ℱ i] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | ℱ (i - 1)] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (l c : ℝ) (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hineq : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2) :
    ∀ k ≤ T, Integrable (fun ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω)) P ∧
      ∫ ω, Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω) ∂P ≤ 1 := by
  set W : ℕ → Ω → ℝ := fun i => P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] with hW
  set Z : ℕ → Ω → ℝ := fun k ω => Real.exp (l * ∑ i ∈ Finset.Icc 1 k, X i ω
        - c * ∑ i ∈ Finset.Icc 1 k, W i ω) with hZ
  have hWm : ∀ k i, i - 1 ≤ k → Measurable[ℱ k] (W i) := fun k i h =>
    (stronglyMeasurable_condExp.measurable).mono (ℱ.mono h) le_rfl
  have hXm : ∀ k ≤ T, ∀ i ∈ Finset.Icc 1 k, Measurable[ℱ k] (X i) := by
    intro k hk i hi
    rw [Finset.mem_Icc] at hi
    exact (hmeas i (Finset.mem_Icc.mpr ⟨hi.1, hi.2.trans hk⟩)).mono (ℱ.mono hi.2) le_rfl
  have hZm : ∀ k ≤ T, Measurable[ℱ k] (Z k) := by
    intro k hk
    apply Measurable.exp
    apply Measurable.sub
    · exact (Finset.measurable_sum _ (fun i hi => hXm k hk i hi)).const_mul l
    · refine (Finset.measurable_sum _ (fun i hi => hWm k i ?_)).const_mul c
      rw [Finset.mem_Icc] at hi; omega
  have hG : ∀ᵐ ω ∂P, (∀ i ∈ Finset.Icc 1 T, X i ω ≤ b) ∧ ∀ i, 0 ≤ W i ω := by
    have h1 : ∀ᵐ ω ∂P, ∀ i ∈ Finset.Icc 1 T, X i ω ≤ b := (Filter.eventually_all_finset _).mpr hb
    have h2 : ∀ᵐ ω ∂P, ∀ i, 0 ≤ W i ω := by
      rw [ae_all_iff]; intro i
      exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    filter_upwards [h1, h2] with ω a1 a2 using ⟨a1, a2⟩
  have hZb : ∀ k ≤ T, ∀ᵐ ω ∂P, Z k ω ≤ Real.exp (l * (k * b)) := by
    intro k hk
    filter_upwards [hG] with ω ⟨g1, g2⟩
    apply Real.exp_le_exp.mpr
    have hS : ∑ i ∈ Finset.Icc 1 k, X i ω ≤ k * b := by
      calc ∑ i ∈ Finset.Icc 1 k, X i ω ≤ ∑ i ∈ Finset.Icc 1 k, b := by
            apply Finset.sum_le_sum; intro i hi
            rw [Finset.mem_Icc] at hi
            exact g1 i (Finset.mem_Icc.mpr ⟨hi.1, hi.2.trans hk⟩)
        _ = k * b := by simp
    have hV : 0 ≤ ∑ i ∈ Finset.Icc 1 k, W i ω := Finset.sum_nonneg (fun i _ => g2 i)
    have := mul_le_mul_of_nonneg_left hS hl
    nlinarith
  have hZpos : ∀ k ω, 0 ≤ Z k ω := fun k ω => (Real.exp_pos _).le
  have hZi : ∀ k ≤ T, Integrable (Z k) P := by
    intro k hk
    refine Integrable.of_bound ((hZm k hk).mono (ℱ.le k) le_rfl).aestronglyMeasurable
      (Real.exp (l * (k * b))) ?_
    filter_upwards [hZb k hk] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (hZpos k ω)]; exact h
  intro k hk
  refine ⟨hZi k hk, ?_⟩
  show ∫ ω, Z k ω ∂P ≤ 1
  induction k with
  | zero => simp [hZ]
  | succ k ih =>
    have hk' : k ≤ T := by omega
    have hkT : k + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hk⟩
    set Y : Ω → ℝ := fun ω => Z k ω * Real.exp (-c * W (k+1) ω) with hY
    have hsplit : ∀ ω, Z (k+1) ω = Y ω * Real.exp (l * X (k+1) ω) := by
      intro ω
      simp only [hZ, hY]
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    have hWk : W (k+1) = P[fun ω' => X (k+1) ω' ^ 2 | ℱ k] := by simp [hW]
    have hYm : StronglyMeasurable[ℱ k] Y := by
      apply Measurable.stronglyMeasurable
      exact (hZm k hk').mul (((hWm k (k+1) (by omega)).const_mul (-c)).exp)
    have hYb : ∀ᵐ ω ∂P, Y ω ≤ Real.exp (l * (k * b)) := by
      filter_upwards [hZb k hk', hG] with ω h ⟨_, g2⟩
      have : Real.exp (-c * W (k+1) ω) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [g2 (k+1)]
      calc Y ω ≤ Z k ω * 1 := mul_le_mul_of_nonneg_left this (hZpos k ω)
        _ ≤ _ := by simpa using h
    have hmd : P[X (k+1) | ℱ k] =ᵐ[P] 0 := by simpa using hmds (k+1) hkT
    have hst := fr_step (ℱ.le k) hYm (fun ω => mul_nonneg (hZpos k ω) (Real.exp_pos _).le) _ hYb
      ((hmeas (k+1) hkT).mono (ℱ.le _) le_rfl) (hint _ hkT) (hint_sq _ hkT) hmd b (hb _ hkT)
      l c hl hineq
    rw [← hWk] at hst
    calc ∫ ω, Z (k+1) ω ∂P = ∫ ω, Y ω * Real.exp (l * X (k+1) ω) ∂P := by
          congr 1; ext ω; exact hsplit ω
      _ ≤ ∫ ω, Y ω * (1 + c * W (k+1) ω) ∂P := hst
      _ ≤ ∫ ω, Z k ω ∂P := by
          apply integral_mono_of_nonneg _ (hZi k hk')
          · filter_upwards [hG] with ω ⟨_, g2⟩
            simp only [hY]
            have e1 := Real.add_one_le_exp (c * W (k+1) ω)
            have e2 : Real.exp (-c * W (k+1) ω) * Real.exp (c * W (k+1) ω) = 1 := by
              rw [← Real.exp_add]; simp
            have e3 := Real.exp_pos (-c * W (k+1) ω)
            have e4 := hZpos k ω
            have : Real.exp (-c * W (k+1) ω) * (1 + c * W (k+1) ω) ≤ 1 := by
              calc _ ≤ Real.exp (-c * W (k+1) ω) * Real.exp (c * W (k+1) ω) :=
                    mul_le_mul_of_nonneg_left (by linarith) e3.le
                _ = 1 := e2
            calc Z k ω * Real.exp (-c * W (k + 1) ω) * (1 + c * W (k + 1) ω)
                = Z k ω * (Real.exp (-c * W (k+1) ω) * (1 + c * W (k+1) ω)) := by ring
              _ ≤ Z k ω * 1 := mul_le_mul_of_nonneg_left this e4
              _ = Z k ω := by ring
          · filter_upwards [hG] with ω ⟨_, g2⟩
            have := g2 (k+1)
            exact mul_nonneg (mul_nonneg (hZpos k ω) (Real.exp_pos _).le) (by nlinarith)
      _ ≤ 1 := ih hk'


theorem freedman_core {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[ℱ i] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | ℱ (i - 1)] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have : {ω | a ≤ ∑ i ∈ Finset.Icc 1 0, X i ω ∧
        ∑ i ∈ Finset.Icc 1 0, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} = ∅ := by
      ext ω; simp; intro h; linarith
    rw [this]; simp; positivity
  rcases lt_or_ge b 0 with hb0 | hb0
  · exfalso
    have h1 : (1:ℕ) ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨le_rfl, hT⟩
    have e1 : ∫ ω, X 1 ω ∂P = 0 := by
      rw [← integral_condExp (ℱ.le (1 - 1))]
      rw [integral_congr_ae (hmds 1 h1)]; simp
    have e2 : ∫ ω, X 1 ω ∂P ≤ ∫ _ω, b ∂P :=
      integral_mono_ae (hint 1 h1) (integrable_const b) (hb 1 h1)
    simp at e2; linarith
  have hD : 0 < 3 * v + a * b := by nlinarith
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 3 * a / (3 * v + a * b) := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  have hlb : l * b < 3 := by
    rw [hl, div_mul_eq_mul_div, div_lt_iff₀ hD]; nlinarith
  have hE : 0 < 6 - 2 * l * b := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 3 * l ^ 2 / (6 - 2 * l * b) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hineq : ∀ x ≤ b, Real.exp (l * x) ≤ 1 + l * x + c * x ^ 2 := by
    intro x hx
    have := fr_exp_bound (l * x) (l * b) (mul_le_mul_of_nonneg_left hx hl0) hlb
    have e : 3 * (l * x) ^ 2 / (6 - 2 * (l * b)) = c * x ^ 2 := by
      rw [hc]; ring
    linarith
  obtain ⟨hZi, hZ1⟩ := fr_supermart P ℱ X T b hmeas hint hint_sq hmds hb l c hl0 hc0 hineq T le_rfl
  set ε := Real.exp (l * a - c * v) with hε
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)) hZi ε
  have hsub : {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} ⊆
      {ω | ε ≤ Real.exp (l * ∑ i ∈ Finset.Icc 1 T, X i ω
        - c * ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω)} := by
    intro ω ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq, hε]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left h1 hl0
    have := mul_le_mul_of_nonneg_left h2 hc0
    linarith
  have hmono := measureReal_mono hsub (μ := P)
  have hεpos : 0 < ε := Real.exp_pos _
  have key : ε * P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hmono hεpos.le
    linarith
  have hid : -a ^ 2 / (2 * v + 2 * a * b / 3) = -(l * a - c * v) := by
    have hv' : v ≠ 0 := hv.ne'
    have hE' : 6 - 2 * l * b = 18 * v / (3 * v + a * b) := by
      rw [hl, eq_div_iff hD.ne']; field_simp; ring
    rw [hc, hE', hl]
    field_simp
    ring
  rw [hid, Real.exp_neg, ← hε]
  calc _ = ε⁻¹ * (ε * P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v}) := by
          rw [← mul_assoc, inv_mul_cancel₀ hεpos.ne', one_mul]
    _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hεpos.le)
    _ = ε⁻¹ := mul_one _

end StochLinOpt.LowerBound

open StochLinOpt.LowerBound


theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (T : ℕ) (b : ℝ)
    (hmeas : ∀ i ∈ Finset.Icc 1 T, Measurable[ℱ i] (X i))
    (hint : ∀ i ∈ Finset.Icc 1 T, Integrable (X i) P)
    (hint_sq : ∀ i ∈ Finset.Icc 1 T, Integrable (fun ω => X i ω ^ 2) P)
    (hmds : ∀ i ∈ Finset.Icc 1 T, P[X i | ℱ (i - 1)] =ᵐ[P] 0)
    (hb : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, X i ω ≤ b)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    P.real {ω | a ≤ ∑ i ∈ Finset.Icc 1 T, X i ω ∧
        ∑ i ∈ Finset.Icc 1 T, P[fun ω' => X i ω' ^ 2 | ℱ (i - 1)] ω ≤ v} ≤
      Real.exp (-a ^ 2 / (2 * v + 2 * a * b / 3)) := by
  exact freedman_core P ℱ X T b hmeas hint hint_sq hmds hb a v ha hv
