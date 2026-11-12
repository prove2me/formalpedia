-- Prove2me | solution 1 for RelaxedIndexability.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:04:07.878014+00:00
-- url     : https://prove2.me/submissions/206b2217-cbd5-430a-98cd-0ab151a278ea

import Definitions.Def_RelaxedIndexability_Arm
import Definitions.Def_RelaxedIndexability_thresholdValue
import Definitions.Def_RelaxedIndexability_passiveTime
import Definitions.Def_RelaxedIndexability_RelaxedIndexable
import Definitions.Def_RelaxedIndexability_approxWhittle
import Theorems.Thm_RelaxedIndexability_lemma_3
import Theorems.Thm_RelaxedIndexability_value_affine_in_subsidy
import Theorems.Thm_RelaxedIndexability_denominator_iff

open Filter Matrix

namespace _M6Thm3Helper

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
  have h1 : x ⬝ᵥ (1 : Fin K → ℝ) = 1 := by simpa [dotProduct] using hx.2
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
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring

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

lemma policyValue_abs_le {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    |policyValue β P rAct rPas π x| ≤ M / (1 - β) := by
  refine le_of_tendsto (horizonValue_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas hx).abs
    (Eventually.of_forall fun n => ?_)
  rw [horizonValue_eq_sum]
  have h1 : 0 < 1 - β := sub_pos.mpr hβ1
  have hid : (∑ i ∈ Finset.range n, β ^ i) * (1 - β) = 1 - β ^ n := by
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  have hgeom : ∑ i ∈ Finset.range n, β ^ i ≤ 1 / (1 - β) := by
    rw [le_div_iff₀ h1, hid]; linarith [pow_nonneg hβ0.le n]
  calc |∑ i ∈ Finset.range n,
          (horizonValue β P rAct rPas π (i + 1) x - horizonValue β P rAct rPas π i x)|
      ≤ ∑ i ∈ Finset.range n, M * β ^ i :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ =>
            horizonValue_diff_le β hβ0 P hP rAct rPas π M hM hrAct hrPas i x hx)
    _ = M * ∑ i ∈ Finset.range n, β ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (1 / (1 - β)) := mul_le_mul_of_nonneg_left hgeom hM
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

lemma policyValue_eq_beliefStep {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool)
    (M : ℝ) (hM : 0 ≤ M)
    (hrAct : ∀ y ∈ stdSimplex ℝ (Fin K), |rAct y| ≤ M)
    (hrPas : ∀ y ∈ stdSimplex ℝ (Fin K), |rPas y| ≤ M)
    {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    policyValue β P rAct rPas π x =
      beliefStep β P rAct rPas (π x) (policyValue β P rAct rPas π) x := by
  have ht1 : Tendsto (fun n => horizonValue β P rAct rPas π (n + 1) x) atTop
      (nhds (policyValue β P rAct rPas π x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr
      (horizonValue_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas hx)
  have ht2 := beliefStep_tendsto β hβ0 hβ1 P hP rAct rPas π M hM hrAct hrPas (π x) hx
  exact tendsto_nhds_unique ht1 ht2

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

lemma thresholdValue_zero_orbit {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {z : Fin K → ℝ} (hz : z ∈ stdSimplex ℝ (Fin K)) :
    ∀ n : ℕ, (∀ j < n, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B)) →
      thresholdValue β P B ω 0 z = β ^ n * thresholdValue β P B ω 0 (z ᵥ* P ^ n) := by
  obtain ⟨hM0, hrAct, hrPas⟩ := simplex_dot_bound B 0
  intro n
  induction n with
  | zero => intro _; simp [Matrix.vecMul_one]
  | succ n ih =>
    intro hpas
    have hprev := ih fun j hj => hpas j (Nat.lt_succ_of_lt hj)
    have hyn : z ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) := vecMul_pow_mem_simplex hP hz n
    have hrule : thresholdRule B ω (z ᵥ* P ^ n) = false :=
      decide_eq_false (hpas n (Nat.lt_succ_self n))
    have hstep : thresholdValue β P B ω 0 (z ᵥ* P ^ n) =
        β * thresholdValue β P B ω 0 (z ᵥ* P ^ (n + 1)) := by
      unfold thresholdValue
      rw [policyValue_eq_beliefStep β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas hyn, hrule]
      simp [beliefStep, Matrix.vecMul_vecMul, ← pow_succ]
    rw [hprev, hstep, pow_succ]
    ring

lemma thresholdValue_zero_unified {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {z : Fin K → ℝ} (hz : z ∈ stdSimplex ℝ (Fin K)) :
    thresholdValue β P B ω 0 z =
      gVec β P B ω z ⬝ᵥ fun j => B j + β * thresholdValue β P B ω 0 (P j) := by
  obtain ⟨hM0, hrAct, hrPas⟩ := simplex_dot_bound B 0
  by_cases hex : ∃ t : ℕ, ω ⬝ᵥ B < (z ᵥ* P ^ t) ⬝ᵥ B
  · let n := Nat.find hex
    have hcross : crossTime P B ω z = n := by simp [crossTime, hex, n]
    have hpas : ∀ j < n, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B) := fun j hj => Nat.find_min hex hj
    have hact_lt : ω ⬝ᵥ B < (z ᵥ* P ^ n) ⬝ᵥ B := Nat.find_spec hex
    have hyn : z ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) := vecMul_pow_mem_simplex hP hz n
    have hrule : thresholdRule B ω (z ᵥ* P ^ n) = true := decide_eq_true hact_lt
    have hact_eq : thresholdValue β P B ω 0 (z ᵥ* P ^ n) =
        (z ᵥ* P ^ n) ⬝ᵥ B + β * ((z ᵥ* P ^ n) ⬝ᵥ fun j => thresholdValue β P B ω 0 (P j)) := by
      unfold thresholdValue
      rw [policyValue_eq_beliefStep β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas hyn, hrule]
      simp [beliefStep, dotProduct]
    rw [thresholdValue_zero_orbit β hβ0 hβ1 P hP B ω hz n hpas, hact_eq]
    have hrhs : (fun j => B j + β * thresholdValue β P B ω 0 (P j)) =
        B + β • (fun j => thresholdValue β P B ω 0 (P j)) := by
      ext j; simp
    rw [hrhs]
    simp only [gVec, hcross, discPow, ENat.recTopCoe_natCast, ENat.toNat_natCast,
      smul_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  · have htop : crossTime P B ω z = ⊤ := by simp [crossTime, hex]
    have hno : ∀ j : ℕ, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B) := fun j hj => hex ⟨j, hj⟩
    let M : ℝ := (∑ j : Fin K, |B j|) + |0|
    let C : ℝ := M / (1 - β)
    have hdiff_le : ∀ n : ℕ, |thresholdValue β P B ω 0 z| ≤ β ^ n * C := by
      intro n
      rw [thresholdValue_zero_orbit β hβ0 hβ1 P hP B ω hz n (fun j _ => hno j),
        abs_mul, abs_of_pos (pow_pos hβ0 n)]
      exact mul_le_mul_of_nonneg_left
        (policyValue_abs_le β hβ0 hβ1 P hP _ _ _ M hM0 hrAct hrPas
          (vecMul_pow_mem_simplex hP hz n))
        (pow_nonneg hβ0.le n)
    have ht0 : Tendsto (fun n : ℕ => β ^ n * C) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const C
    have habs_eq : |thresholdValue β P B ω 0 z| = 0 :=
      le_antisymm (ge_of_tendsto ht0 (Eventually.of_forall hdiff_le)) (abs_nonneg _)
    rw [abs_eq_zero.mp habs_eq]
    simp [gVec, htop, discPow, ENat.recTopCoe_top]

lemma GMat_mulVec_apply {K : ℕ} (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω v : Fin K → ℝ)
    (k : Fin K) :
    (GMat β P B ω *ᵥ v) k = gVec β P B ω (P k) ⬝ᵥ v := by
  simp only [GMat, Matrix.mulVec, dotProduct, Matrix.of_apply]

lemma actionValue_diff_eq {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) (m : ℝ) :
    thresholdActionValue β P B ω m true ω - thresholdActionValue β P B ω m false ω =
      whittleNumerator β P B ω - m * whittleDenominator β P B ω := by
  obtain ⟨hM0, hrAct, hrPas⟩ := simplex_dot_bound B m
  let v₀ : Fin K → ℝ := fun k => thresholdValue β P B ω 0 (P k)
  let d : Fin K → ℝ := fun k => passiveTime β P B ω (P k)
  have haff := (value_affine_in_subsidy β hβ0 hβ1 P hP B ω hω).2.2
  have hact_true : thresholdActionValue β P B ω m true ω =
      ω ⬝ᵥ B + β * (ω ⬝ᵥ v₀) + m * (β * (ω ⬝ᵥ d)) := by
    have h1 : thresholdActionValue β P B ω m true ω =
        ω ⬝ᵥ B + β * ∑ k : Fin K, ω k * thresholdValue β P B ω m (P k) := by
      unfold thresholdActionValue
      rw [actionValue_eq_beliefStep β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas true hω]
      simp only [beliefStep, ↓reduceIte]
      rfl
    have hsum : ∑ k : Fin K, ω k * thresholdValue β P B ω m (P k) =
        (∑ k : Fin K, ω k * v₀ k) + m * ∑ k : Fin K, ω k * d k := by
      have hterm : ∀ k : Fin K,
          ω k * thresholdValue β P B ω m (P k) = ω k * v₀ k + m * (ω k * d k) := by
        intro k
        rw [haff (P k) (row_mem_simplex hP k) m]
        ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h1, hsum]
    simp only [dotProduct]
    ring
  have hact_false : thresholdActionValue β P B ω m false ω =
      β * thresholdValue β P B ω 0 (ω ᵥ* P) +
        m * (1 + β * passiveTime β P B ω (ω ᵥ* P)) := by
    have h1 : thresholdActionValue β P B ω m false ω =
        m + β * thresholdValue β P B ω m (ω ᵥ* P) := by
      unfold thresholdActionValue
      rw [actionValue_eq_beliefStep β hβ0 hβ1 P hP _ _ _ _ hM0 hrAct hrPas false hω]
      simp only [beliefStep, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [h1, haff (ω ᵥ* P) (vecMul_mem_simplex hP hω) m]
    ring
  have hunit : IsUnit (1 - β • GMat β P B ω) :=
    (lemma_3 β hβ0 hβ1 P hP B ω hω 0).2.2
  cases hunit.nonempty_invertible
  have hlin_v0 : GMat β P B ω *ᵥ B = (1 - β • GMat β P B ω) *ᵥ v₀ := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [GMat_mulVec_apply, GMat_mulVec_apply]
    have hk := thresholdValue_zero_unified β hβ0 hβ1 P hP B ω (row_mem_simplex hP k)
    have hrhs : (fun j => B j + β * thresholdValue β P B ω 0 (P j)) = B + β • v₀ := by
      ext j; simp [v₀]
    rw [hrhs, dotProduct_add, dotProduct_smul, smul_eq_mul] at hk
    dsimp [v₀] at hk ⊢
    linarith
  have hv0_eq : (HMat β P B ω * GMat β P B ω) *ᵥ B = v₀ := by
    rw [← Matrix.mulVec_mulVec]
    unfold HMat
    exact Matrix.inv_mulVec_eq_vec hlin_v0
  have hωP_zero : thresholdValue β P B ω 0 (ω ᵥ* P) =
      gVec β P B ω (ω ᵥ* P) ⬝ᵥ ((1 + β • (HMat β P B ω * GMat β P B ω)) *ᵥ B) := by
    rw [thresholdValue_zero_unified β hβ0 hβ1 P hP B ω (vecMul_mem_simplex hP hω)]
    congr 1
    ext j
    have hj : ((HMat β P B ω * GMat β P B ω) *ᵥ B) j = v₀ j := congr_fun hv0_eq j
    simp [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hj, v₀]
  have hden := (denominator_iff β hβ0 hβ1 P hP B ω hω).1
  rw [hact_true, hact_false, hden, hωP_zero]
  unfold whittleNumerator
  rw [hv0_eq]
  ring

end _M6Thm3Helper

open RelaxedIndexability

theorem solution (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) {N : ℕ} (arms : Fin N → Arm) :
    (∀ n : Fin N, ∀ ω ∈ stdSimplex ℝ (Fin (arms n).K), ∀ ω₁ ∈ stdSimplex ℝ (Fin (arms n).K),
      ∀ m : ℝ,
        HasDerivAt (fun m' => thresholdValue β (arms n).P (arms n).B ω m' ω₁)
          (passiveTime β (arms n).P (arms n).B ω ω₁) m) ∧
    (RelaxedIndexable β arms ↔
      ∀ n : Fin N, ∀ ω ∈ stdSimplex ℝ (Fin (arms n).K),
        β * (ω ⬝ᵥ fun k => passiveTime β (arms n).P (arms n).B ω ((arms n).P k)) ≠
          1 + β * passiveTime β (arms n).P (arms n).B ω (ω ᵥ* (arms n).P)) ∧
    (RelaxedIndexable β arms →
      ∀ n : Fin N, ∀ ω ∈ stdSimplex ℝ (Fin (arms n).K), ∀ m : ℝ,
        (thresholdActionValue β (arms n).P (arms n).B ω m true ω =
            thresholdActionValue β (arms n).P (arms n).B ω m false ω ↔
          m = approxWhittle β (arms n).P (arms n).B ω)) := by
  refine ⟨fun n ω hω ω₁ hω₁ m => ?_, ?_, fun hRI n ω hω m => ?_⟩
  · have haff := (value_affine_in_subsidy β hβ0 hβ1 (arms n).P (arms n).P_stochastic
      (arms n).B ω hω).2.2 ω₁ hω₁
    have hfun : (fun m' => thresholdValue β (arms n).P (arms n).B ω m' ω₁) =
        (fun m' => thresholdValue β (arms n).P (arms n).B ω 0 ω₁ +
          m' * passiveTime β (arms n).P (arms n).B ω ω₁) :=
      funext haff
    rw [hfun]
    have hd : HasDerivAt
        (fun m' : ℝ => m' * passiveTime β (arms n).P (arms n).B ω ω₁)
        (1 * passiveTime β (arms n).P (arms n).B ω ω₁) m :=
      (hasDerivAt_id m).mul_const (passiveTime β (arms n).P (arms n).B ω ω₁)
    rw [one_mul] at hd
    exact hd.const_add (thresholdValue β (arms n).P (arms n).B ω 0 ω₁)
  · constructor
    · intro hRI n ω hω
      rw [(denominator_iff β hβ0 hβ1 (arms n).P (arms n).P_stochastic (arms n).B ω hω).2]
      obtain ⟨m₀, hm₀, huniq⟩ := hRI n ω hω
      intro hden0
      have hdiff0 := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
        (arms n).P_stochastic (arms n).B ω hω m₀
      have hnum0 : whittleNumerator β (arms n).P (arms n).B ω = 0 := by
        linarith [hm₀, hdiff0, show m₀ * whittleDenominator β (arms n).P (arms n).B ω = 0 by
          rw [hden0, mul_zero]]
      have heq_for : ∀ m : ℝ,
          thresholdActionValue β (arms n).P (arms n).B ω m true ω =
            thresholdActionValue β (arms n).P (arms n).B ω m false ω := by
        intro m
        have hdm := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
          (arms n).P_stochastic (arms n).B ω hω m
        rw [hnum0, hden0] at hdm
        linarith
      have h0 : (0 : ℝ) = m₀ := huniq 0 (heq_for 0)
      have h1 : (1 : ℝ) = m₀ := huniq 1 (heq_for 1)
      exact zero_ne_one (h0.trans h1.symm)
    · intro hcond n ω hω
      have hden_ne : whittleDenominator β (arms n).P (arms n).B ω ≠ 0 :=
        (denominator_iff β hβ0 hβ1 (arms n).P (arms n).P_stochastic (arms n).B ω hω).2.mp
          (hcond n ω hω)
      refine ⟨approxWhittle β (arms n).P (arms n).B ω, ?_, fun m hm => ?_⟩
      · have hdm := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
          (arms n).P_stochastic (arms n).B ω hω (approxWhittle β (arms n).P (arms n).B ω)
        have hmul : approxWhittle β (arms n).P (arms n).B ω *
            whittleDenominator β (arms n).P (arms n).B ω =
            whittleNumerator β (arms n).P (arms n).B ω := by
          unfold approxWhittle
          exact div_mul_cancel₀ _ hden_ne
        linarith
      · have hdm := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
          (arms n).P_stochastic (arms n).B ω hω m
        have hmul : m * whittleDenominator β (arms n).P (arms n).B ω =
            whittleNumerator β (arms n).P (arms n).B ω := by linarith
        unfold approxWhittle
        exact (eq_div_iff hden_ne).mpr hmul
  · have hden_ne : whittleDenominator β (arms n).P (arms n).B ω ≠ 0 := by
      obtain ⟨m₀, hm₀, huniq⟩ := hRI n ω hω
      intro hden0
      have hdiff0 := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
        (arms n).P_stochastic (arms n).B ω hω m₀
      have hnum0 : whittleNumerator β (arms n).P (arms n).B ω = 0 := by
        linarith [hm₀, hdiff0, show m₀ * whittleDenominator β (arms n).P (arms n).B ω = 0 by
          rw [hden0, mul_zero]]
      have heq_for : ∀ m' : ℝ,
          thresholdActionValue β (arms n).P (arms n).B ω m' true ω =
            thresholdActionValue β (arms n).P (arms n).B ω m' false ω := by
        intro m'
        have hdm := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
          (arms n).P_stochastic (arms n).B ω hω m'
        rw [hnum0, hden0] at hdm
        linarith
      exact zero_ne_one ((huniq 0 (heq_for 0)).trans (huniq 1 (heq_for 1)).symm)
    have hdm := _M6Thm3Helper.actionValue_diff_eq β hβ0 hβ1 (arms n).P
      (arms n).P_stochastic (arms n).B ω hω m
    unfold approxWhittle
    rw [eq_div_iff hden_ne]
    constructor
    · intro heq; linarith
    · intro hmul; linarith
