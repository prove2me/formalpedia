-- Prove2me | solution 1 for RelaxedIndexability.renewal_equations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T22:52:13.304856+00:00
-- url     : https://prove2.me/submissions/8aeb2016-4cc7-4d3b-bb70-343088299cac

import Definitions.Def_RelaxedIndexability_crossTime
import Definitions.Def_RelaxedIndexability_thresholdValue

open Filter Matrix

namespace _M6RenewalHelper

open RelaxedIndexability

lemma row_mem_simplex {K : ℕ} {P : Matrix (Fin K) (Fin K) ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (k : Fin K) :
    P k ∈ stdSimplex ℝ (Fin K) :=
  ⟨fun _ => Matrix.nonneg_of_mem_rowStochastic hP,
    Matrix.sum_row_of_mem_rowStochastic hP k⟩

lemma vecMul_mem_simplex {K : ℕ} {P : Matrix (Fin K) (Fin K) ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) {x : Fin K → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin K)) :
    x ᵥ* P ∈ stdSimplex ℝ (Fin K) := by
  refine ⟨Matrix.nonneg_vecMul_of_mem_rowStochastic hP hx.1, ?_⟩
  have h1 : x ⬝ᵥ (1 : Fin K → ℝ) = 1 := by
    simpa [dotProduct] using hx.2
  have h2 := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hP h1
  simpa [dotProduct] using h2

lemma vecMul_pow_mem_simplex {K : ℕ} {P : Matrix (Fin K) (Fin K) ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) {x : Fin K → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin K)) (n : ℕ) :
    x ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) :=
  vecMul_mem_simplex (Submonoid.pow_mem _ hP n) hx

lemma horizonValue_diff_le {K : ℕ} (β : ℝ) (hβ0 : 0 < β)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M) :
    ∀ (n : ℕ) (x : Fin K → ℝ), x ∈ stdSimplex ℝ (Fin K) →
      |horizonValue β P rAct rPas π (n + 1) x - horizonValue β P rAct rPas π n x| ≤ M * β ^ n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    let _ := hM
    cases hπ : π x <;> simp [horizonValue, beliefStep, hπ]
    · exact hrPas x hx
    · exact hrAct x hx
  | succ n ih =>
    intro x hx
    change |beliefStep β P rAct rPas (π x) (horizonValue β P rAct rPas π (n + 1)) x -
        beliefStep β P rAct rPas (π x) (horizonValue β P rAct rPas π n) x| ≤ M * β ^ (n + 1)
    cases hπ : π x
    · simp only [beliefStep, Bool.false_eq_true, ↓reduceIte]
      have hsub : (rPas x + β * horizonValue β P rAct rPas π (n + 1) (x ᵥ* P)) -
          (rPas x + β * horizonValue β P rAct rPas π n (x ᵥ* P)) =
          β * (horizonValue β P rAct rPas π (n + 1) (x ᵥ* P) -
            horizonValue β P rAct rPas π n (x ᵥ* P)) := by ring
      rw [hsub, abs_mul, abs_of_pos hβ0]
      calc β * |horizonValue β P rAct rPas π (n + 1) (x ᵥ* P) -
              horizonValue β P rAct rPas π n (x ᵥ* P)|
          ≤ β * (M * β ^ n) :=
            mul_le_mul_of_nonneg_left (ih (x ᵥ* P) (vecMul_mem_simplex hP hx)) hβ0.le
        _ = M * β ^ (n + 1) := by rw [pow_succ]; ring
    · simp only [beliefStep, ↓reduceIte]
      have hsum : (∑ j, x j * horizonValue β P rAct rPas π (n + 1) (P j)) -
          (∑ j, x j * horizonValue β P rAct rPas π n (P j)) =
          ∑ j, x j * (horizonValue β P rAct rPas π (n + 1) (P j) -
            horizonValue β P rAct rPas π n (P j)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => (mul_sub (x j) _ _).symm
      have hsub : (rAct x + β * ∑ j, x j * horizonValue β P rAct rPas π (n + 1) (P j)) -
          (rAct x + β * ∑ j, x j * horizonValue β P rAct rPas π n (P j)) =
          β * ∑ j, x j * (horizonValue β P rAct rPas π (n + 1) (P j) -
            horizonValue β P rAct rPas π n (P j)) := by
        rw [← hsum]
        ring
      rw [hsub, abs_mul, abs_of_pos hβ0]
      calc β * |∑ j, x j * (horizonValue β P rAct rPas π (n + 1) (P j) -
              horizonValue β P rAct rPas π n (P j))|
          ≤ β * ∑ j, |x j * (horizonValue β P rAct rPas π (n + 1) (P j) -
              horizonValue β P rAct rPas π n (P j))| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hβ0.le
        _ = β * ∑ j, x j * |horizonValue β P rAct rPas π (n + 1) (P j) -
              horizonValue β P rAct rPas π n (P j)| := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (hx.1 j)]
        _ ≤ β * ∑ j, x j * (M * β ^ n) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hβ0.le
            exact mul_le_mul_of_nonneg_left (ih (P j) (row_mem_simplex hP j)) (hx.1 j)
        _ = β * ((∑ j, x j) * (M * β ^ n)) := by rw [← Finset.sum_mul]
        _ = M * β ^ (n + 1) := by rw [hx.2, one_mul, pow_succ]; ring

lemma horizonValue_eq_sum {K : ℕ} (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool) (n : ℕ) (x : Fin K → ℝ) :
    horizonValue β P rAct rPas π n x =
      ∑ i ∈ Finset.range n,
        (horizonValue β P rAct rPas π (i + 1) x - horizonValue β P rAct rPas π i x) := by
  induction n with
  | zero => simp [horizonValue]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    ring

lemma horizonValue_tendsto {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    Tendsto (fun n => horizonValue β P rAct rPas π n x) atTop
      (nhds (policyValue β P rAct rPas π x)) := by
  let d : ℕ → ℝ := fun i =>
    horizonValue β P rAct rPas π (i + 1) x - horizonValue β P rAct rPas π i x
  have hgeom : Summable (fun i : ℕ => M * β ^ i) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_left M
  have hd_sum : Summable d :=
    Summable.of_norm_bounded hgeom fun i => by
      rw [Real.norm_eq_abs]
      exact horizonValue_diff_le β hβ0 P hP rAct rPas π M hM hrAct hrPas i x hx
  have hfun : (fun n => horizonValue β P rAct rPas π n x) =
      (fun n => ∑ i ∈ Finset.range n, d i) :=
    funext fun n => horizonValue_eq_sum β P rAct rPas π n x
  have htend : Tendsto (fun n => horizonValue β P rAct rPas π n x) atTop (nhds (∑' i, d i)) := by
    rw [hfun]
    exact hd_sum.hasSum.tendsto_sum_nat
  have hlim : policyValue β P rAct rPas π x = ∑' i, d i :=
    tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, htend⟩) htend
  exact hlim ▸ htend

lemma geom_partial_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, β ^ i ≤ 1 / (1 - β) := by
  have h1 : 0 < 1 - β := sub_pos.mpr hβ1
  have hid : (∑ i ∈ Finset.range n, β ^ i) * (1 - β) = 1 - β ^ n := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring
  rw [le_div_iff₀ h1, hid]
  linarith [pow_nonneg hβ0.le n]

lemma policyValue_abs_le {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    |policyValue β P rAct rPas π x| ≤ M / (1 - β) := by
  have htend := (horizonValue_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas hx).abs
  refine le_of_tendsto htend (Eventually.of_forall fun n => ?_)
  rw [horizonValue_eq_sum]
  calc |∑ i ∈ Finset.range n,
          (horizonValue β P rAct rPas π (i + 1) x - horizonValue β P rAct rPas π i x)|
      ≤ ∑ i ∈ Finset.range n,
          |horizonValue β P rAct rPas π (i + 1) x - horizonValue β P rAct rPas π i x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, M * β ^ i :=
        Finset.sum_le_sum fun i _ =>
          horizonValue_diff_le β hβ0 P hP rAct rPas π M hM hrAct hrPas i x hx
    _ = M * ∑ i ∈ Finset.range n, β ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (1 / (1 - β)) := mul_le_mul_of_nonneg_left (geom_partial_le hβ0 hβ1 n) hM
    _ = M / (1 - β) := mul_one_div M (1 - β)

lemma beliefStep_tendsto {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    (u : Bool) {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    Tendsto (fun n => beliefStep β P rAct rPas u (horizonValue β P rAct rPas π n) x) atTop
      (nhds (beliefStep β P rAct rPas u (policyValue β P rAct rPas π) x)) := by
  cases u
  · simp only [beliefStep, Bool.false_eq_true, ↓reduceIte]
    exact tendsto_const_nhds.add
      ((horizonValue_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas
        (vecMul_mem_simplex hP hx)).const_mul β)
  · simp only [beliefStep, ↓reduceIte]
    refine tendsto_const_nhds.add (Tendsto.const_mul β ?_)
    exact tendsto_finsetSum Finset.univ fun j _ =>
      (horizonValue_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas
        (row_mem_simplex hP j)).const_mul (x j)

lemma actionValue_eq_beliefStep {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    (u : Bool) {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    actionValue β P rAct rPas π u x =
      beliefStep β P rAct rPas u (policyValue β P rAct rPas π) x := by
  have ht := beliefStep_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas u hx
  exact tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, ht⟩) ht

lemma policyValue_eq_actionValue {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    policyValue β P rAct rPas π x = actionValue β P rAct rPas π (π x) x := by
  have ht1 : Tendsto (fun n => horizonValue β P rAct rPas π (n + 1) x) atTop
      (nhds (policyValue β P rAct rPas π x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (horizonValue_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas hx)
  have ht2 := beliefStep_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas (π x) hx
  have hbell : policyValue β P rAct rPas π x =
      beliefStep β P rAct rPas (π x) (policyValue β P rAct rPas π) x :=
    tendsto_nhds_unique ht1 ht2
  rw [hbell, actionValue_eq_beliefStep β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas (π x) hx]

lemma simplex_dot_bound {K : ℕ} (B : Fin K → ℝ) (m : ℝ) :
    0 ≤ (∑ j : Fin K, |B j|) + |m| ∧
    (∀ y ∈ stdSimplex ℝ (Fin K), |y ⬝ᵥ B| ≤ (∑ j : Fin K, |B j|) + |m|) ∧
    (∀ _ ∈ stdSimplex ℝ (Fin K), |m| ≤ (∑ j : Fin K, |B j|) + |m|) := by
  have hsum_nn : 0 ≤ ∑ j : Fin K, |B j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨add_nonneg hsum_nn (abs_nonneg m), fun y hy => ?_, fun _ _ => by linarith⟩
  have hdot : |y ⬝ᵥ B| ≤ ∑ j : Fin K, |B j| := by
    simp only [dotProduct]
    calc |∑ j : Fin K, y j * B j|
        ≤ ∑ j : Fin K, |y j * B j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin K, y j * |B j| := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (hy.1 j)]
      _ ≤ ∑ j : Fin K, 1 * |B j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_right (mem_Icc_of_mem_stdSimplex hy j).2 (abs_nonneg _)
      _ = ∑ j : Fin K, |B j| := by simp
  linarith [abs_nonneg m]

lemma thresholdValue_passive_orbit {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) (m : ℝ) {z : Fin K → ℝ} (hz : z ∈ stdSimplex ℝ (Fin K)) :
    ∀ n : ℕ, (∀ j < n, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B)) →
      thresholdValue β P B ω m z =
        (1 - β ^ n) / (1 - β) * m + β ^ n * thresholdValue β P B ω m (z ᵥ* P ^ n) := by
  obtain ⟨hM0, hrAct, hrPas⟩ := simplex_dot_bound B m
  intro n
  induction n with
  | zero =>
    intro _
    simp [Matrix.vecMul_one]
  | succ n ih =>
    intro hpas
    have hprev := ih fun j hj => hpas j (Nat.lt_succ_of_lt hj)
    have hyn : z ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) := vecMul_pow_mem_simplex hP hz n
    have hrule : thresholdRule B ω (z ᵥ* P ^ n) = false :=
      decide_eq_false (hpas n (Nat.lt_succ_self n))
    have hstep : thresholdValue β P B ω m (z ᵥ* P ^ n) =
        m + β * thresholdValue β P B ω m (z ᵥ* P ^ (n + 1)) := by
      unfold thresholdValue
      rw [policyValue_eq_actionValue β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas hyn,
        hrule,
        actionValue_eq_beliefStep β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas false hyn]
      simp [beliefStep, Matrix.vecMul_vecMul, ← pow_succ]
    rw [hprev, hstep]
    have h1 : 1 - β ≠ 0 := sub_ne_zero.mpr (ne_of_gt hβ1)
    field_simp [h1]
    ring

end _M6RenewalHelper

open RelaxedIndexability

theorem solution {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) (m : ℝ) (k : Fin K) :
    (∀ n : ℕ, crossTime P B ω (P k) = n →
      thresholdValue β P B ω m (P k) =
          (1 - β ^ n) / (1 - β) * m
            + β ^ n * thresholdActionValue β P B ω m true (P k ᵥ* P ^ n) ∧
      thresholdActionValue β P B ω m true (P k ᵥ* P ^ n) =
          (P k ᵥ* P ^ n) ⬝ᵥ B
            + β * ((P k ᵥ* P ^ n) ⬝ᵥ fun j => thresholdValue β P B ω m (P j))) ∧
    (crossTime P B ω (P k) = ⊤ → thresholdValue β P B ω m (P k) = m / (1 - β)) := by
  let _ := hω
  have hpk : P k ∈ stdSimplex ℝ (Fin K) := _M6RenewalHelper.row_mem_simplex hP k
  obtain ⟨hM0, hrAct, hrPas⟩ := _M6RenewalHelper.simplex_dot_bound B m
  refine ⟨fun n hcross => ?_, fun htop => ?_⟩
  · have hex : ∃ t : ℕ, ω ⬝ᵥ B < (P k ᵥ* P ^ t) ⬝ᵥ B := by
      by_contra hne
      have : crossTime P B ω (P k) = ⊤ := by simp [crossTime, hne]
      rw [hcross] at this
      exact ENat.natCast_ne_top n this
    have hfind_cast : ((Nat.find hex : ℕ) : ℕ∞) = n := by
      simpa [crossTime, hex] using hcross
    have hfind : Nat.find hex = n := ENat.natCast_inj.mp hfind_cast
    have hpas : ∀ j < n, ¬(ω ⬝ᵥ B < (P k ᵥ* P ^ j) ⬝ᵥ B) := by
      intro j hj
      exact Nat.find_min hex (hfind ▸ hj)
    have hact_lt : ω ⬝ᵥ B < (P k ᵥ* P ^ n) ⬝ᵥ B := hfind ▸ Nat.find_spec hex
    have hyn : P k ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) :=
      _M6RenewalHelper.vecMul_pow_mem_simplex hP hpk n
    have hrule : thresholdRule B ω (P k ᵥ* P ^ n) = true := decide_eq_true hact_lt
    have hval_eq_act : thresholdValue β P B ω m (P k ᵥ* P ^ n) =
        thresholdActionValue β P B ω m true (P k ᵥ* P ^ n) := by
      unfold thresholdValue thresholdActionValue
      rw [_M6RenewalHelper.policyValue_eq_actionValue β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas hyn,
        hrule]
    have hact_formula : thresholdActionValue β P B ω m true (P k ᵥ* P ^ n) =
        (P k ᵥ* P ^ n) ⬝ᵥ B
          + β * ((P k ᵥ* P ^ n) ⬝ᵥ fun j => thresholdValue β P B ω m (P j)) := by
      unfold thresholdActionValue thresholdValue
      rw [_M6RenewalHelper.actionValue_eq_beliefStep β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas
        true hyn]
      simp [beliefStep, dotProduct]
    refine ⟨?_, hact_formula⟩
    rw [_M6RenewalHelper.thresholdValue_passive_orbit β hβ0 hβ1 P hP B ω m hpk n hpas,
      hval_eq_act]
  · have hno : ∀ j : ℕ, ¬(ω ⬝ᵥ B < (P k ᵥ* P ^ j) ⬝ᵥ B) := by
      intro j hj
      have hex : ∃ t : ℕ, ω ⬝ᵥ B < (P k ᵥ* P ^ t) ⬝ᵥ B := ⟨j, hj⟩
      have : crossTime P B ω (P k) = ((Nat.find hex : ℕ) : ℕ∞) := by simp [crossTime, hex]
      rw [htop] at this
      exact ENat.natCast_ne_top (Nat.find hex) this.symm
    let M : ℝ := (∑ j : Fin K, |B j|) + |m|
    let C : ℝ := M / (1 - β) + |m / (1 - β)|
    have hdiff_le : ∀ n : ℕ,
        |thresholdValue β P B ω m (P k) - m / (1 - β)| ≤ β ^ n * C := by
      intro n
      have horb := _M6RenewalHelper.thresholdValue_passive_orbit β hβ0 hβ1 P hP B ω m hpk n
        (fun j _ => hno j)
      have h1 : 1 - β ≠ 0 := sub_ne_zero.mpr (ne_of_gt hβ1)
      have halg : thresholdValue β P B ω m (P k) - m / (1 - β) =
          β ^ n * (thresholdValue β P B ω m (P k ᵥ* P ^ n) - m / (1 - β)) := by
        rw [horb]
        field_simp [h1]
        ring
      rw [halg, abs_mul, abs_of_pos (pow_pos hβ0 n)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le n)
      have hyn : P k ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) :=
        _M6RenewalHelper.vecMul_pow_mem_simplex hP hpk n
      have hv_le : |thresholdValue β P B ω m (P k ᵥ* P ^ n)| ≤ M / (1 - β) :=
        _M6RenewalHelper.policyValue_abs_le β hβ0 hβ1 P hP _ _ _ M hM0 hrAct hrPas hyn
      dsimp [C]
      linarith [abs_sub (thresholdValue β P B ω m (P k ᵥ* P ^ n)) (m / (1 - β)), hv_le]
    have ht0 : Tendsto (fun n : ℕ => β ^ n * C) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const C
    have habs_le : |thresholdValue β P B ω m (P k) - m / (1 - β)| ≤ 0 :=
      ge_of_tendsto ht0 (Eventually.of_forall hdiff_le)
    have habs_eq : |thresholdValue β P B ω m (P k) - m / (1 - β)| = 0 :=
      le_antisymm habs_le (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs_eq)
