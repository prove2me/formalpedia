-- Prove2me | solution 1 for RelaxedIndexability.denominator_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T22:58:05.392234+00:00
-- url     : https://prove2.me/submissions/7e02d6e7-692a-4bc7-b483-497bd0f74435

import Definitions.Def_RelaxedIndexability_passiveTime
import Definitions.Def_RelaxedIndexability_approxWhittle
import Theorems.Thm_RelaxedIndexability_lemma_3

open Filter Matrix

namespace _M6DenomHelper

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

lemma passive_diff_le {K : ℕ} (β : ℝ) (hβ0 : 0 < β)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) :
    ∀ (n : ℕ) (x : Fin K → ℝ), x ∈ stdSimplex ℝ (Fin K) →
      |horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) x -
        horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n x| ≤ β ^ n := by
  intro n
  induction n with
  | zero =>
    intro x _
    cases hπ : thresholdRule B ω x <;> simp [horizonValue, beliefStep, hπ]
  | succ n ih =>
    intro x hx
    change |beliefStep β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω x)
          (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1)) x -
        beliefStep β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω x)
          (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n) x| ≤ β ^ (n + 1)
    cases hπ : thresholdRule B ω x
    · simp only [beliefStep, Bool.false_eq_true, ↓reduceIte]
      have hsub : (1 + β * horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (x ᵥ* P)) -
          (1 + β * horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (x ᵥ* P)) =
          β * (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (x ᵥ* P) -
            horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (x ᵥ* P)) := by ring
      rw [hsub, abs_mul, abs_of_pos hβ0]
      calc β * |horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (x ᵥ* P) -
              horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (x ᵥ* P)|
          ≤ β * β ^ n := mul_le_mul_of_nonneg_left (ih (x ᵥ* P) (vecMul_mem_simplex hP hx)) hβ0.le
        _ = β ^ (n + 1) := by rw [pow_succ]; ring
    · simp only [beliefStep, ↓reduceIte, zero_add]
      have hsub : (β * ∑ j, x j * horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (P j)) -
          (β * ∑ j, x j * horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (P j)) =
          β * ∑ j, x j * (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (P j) -
            horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (P j)) := by
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun j _ => (mul_sub (x j) _ _).symm
      rw [hsub, abs_mul, abs_of_pos hβ0]
      calc β * |∑ j, x j * (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (P j) -
              horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (P j))|
          ≤ β * ∑ j, |x j * (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (P j) -
              horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (P j))| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hβ0.le
        _ = β * ∑ j, x j * |horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) (P j) -
              horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n (P j)| := by
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (hx.1 j)]
        _ ≤ β * ∑ j, x j * β ^ n := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hβ0.le
            exact mul_le_mul_of_nonneg_left (ih (P j) (row_mem_simplex hP j)) (hx.1 j)
        _ = β * ((∑ j, x j) * β ^ n) := by rw [← Finset.sum_mul]
        _ = β ^ (n + 1) := by rw [hx.2, one_mul, pow_succ]; ring

lemma passive_eq_sum {K : ℕ} (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (B ω : Fin K → ℝ) (n : ℕ) (x : Fin K → ℝ) :
    horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n x =
      ∑ i ∈ Finset.range n,
        (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (i + 1) x -
          horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) i x) := by
  induction n with
  | zero => simp [horizonValue]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring

lemma passive_tendsto {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    Tendsto (fun n => horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n x)
      atTop (nhds (passiveTime β P B ω x)) := by
  let d : ℕ → ℝ := fun i =>
    horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (i + 1) x -
      horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) i x
  have hd_sum : Summable d :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hβ0.le hβ1) fun i => by
      rw [Real.norm_eq_abs]
      exact passive_diff_le β hβ0 P hP B ω i x hx
  have hfun : (fun n => horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n x) =
      (fun n => ∑ i ∈ Finset.range n, d i) :=
    funext fun n => passive_eq_sum β P B ω n x
  have htend : Tendsto
      (fun n => horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n x)
      atTop (nhds (∑' i, d i)) := by
    rw [hfun]
    exact hd_sum.hasSum.tendsto_sum_nat
  have hlim : passiveTime β P B ω x = ∑' i, d i :=
    tendsto_nhds_unique (tendsto_nhds_limUnder ⟨_, htend⟩) htend
  exact hlim ▸ htend

lemma passive_abs_le {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    |passiveTime β P B ω x| ≤ 1 / (1 - β) := by
  refine le_of_tendsto (passive_tendsto β hβ0 hβ1 P hP B ω hx).abs
    (Eventually.of_forall fun n => ?_)
  rw [passive_eq_sum]
  have h1 : 0 < 1 - β := sub_pos.mpr hβ1
  have hid : (∑ i ∈ Finset.range n, β ^ i) * (1 - β) = 1 - β ^ n := by
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  have hgeom : ∑ i ∈ Finset.range n, β ^ i ≤ 1 / (1 - β) := by
    rw [le_div_iff₀ h1, hid]; linarith [pow_nonneg hβ0.le n]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun i _ => passive_diff_le β hβ0 P hP B ω i x hx).trans hgeom)

lemma passive_eq_beliefStep {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {x : Fin K → ℝ} (hx : x ∈ stdSimplex ℝ (Fin K)) :
    passiveTime β P B ω x =
      beliefStep β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω x)
        (passiveTime β P B ω) x := by
  have ht1 : Tendsto
      (fun n => horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) (n + 1) x)
      atTop (nhds (passiveTime β P B ω x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (passive_tendsto β hβ0 hβ1 P hP B ω hx)
  have ht2 : Tendsto
      (fun n => beliefStep β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω x)
        (horizonValue β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω) n) x)
      atTop (nhds (beliefStep β P (fun _ => 0) (fun _ => 1) (thresholdRule B ω x)
        (passiveTime β P B ω) x)) := by
    cases thresholdRule B ω x
    · simp only [beliefStep, Bool.false_eq_true, ↓reduceIte]
      exact tendsto_const_nhds.add
        ((passive_tendsto β hβ0 hβ1 P hP B ω (vecMul_mem_simplex hP hx)).const_mul β)
    · simp only [beliefStep, ↓reduceIte]
      refine tendsto_const_nhds.add (Tendsto.const_mul β ?_)
      exact tendsto_finsetSum Finset.univ fun j _ =>
        (passive_tendsto β hβ0 hβ1 P hP B ω (row_mem_simplex hP j)).const_mul (x j)
  exact tendsto_nhds_unique ht1 ht2

lemma passive_orbit {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {z : Fin K → ℝ} (hz : z ∈ stdSimplex ℝ (Fin K)) :
    ∀ n : ℕ, (∀ j < n, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B)) →
      passiveTime β P B ω z =
        (1 - β ^ n) / (1 - β) + β ^ n * passiveTime β P B ω (z ᵥ* P ^ n) := by
  intro n
  induction n with
  | zero => intro _; simp [Matrix.vecMul_one]
  | succ n ih =>
    intro hpas
    have hprev := ih fun j hj => hpas j (Nat.lt_succ_of_lt hj)
    have hyn : z ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) := vecMul_pow_mem_simplex hP hz n
    have hrule : thresholdRule B ω (z ᵥ* P ^ n) = false :=
      decide_eq_false (hpas n (Nat.lt_succ_self n))
    have hstep : passiveTime β P B ω (z ᵥ* P ^ n) =
        1 + β * passiveTime β P B ω (z ᵥ* P ^ (n + 1)) := by
      rw [passive_eq_beliefStep β hβ0 hβ1 P hP B ω hyn, hrule]
      simp [beliefStep, Matrix.vecMul_vecMul, ← pow_succ]
    rw [hprev, hstep]
    have h1 : 1 - β ≠ 0 := sub_ne_zero.mpr (ne_of_gt hβ1)
    field_simp [h1]
    ring

lemma passive_renewal_unified {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K))
    (B ω : Fin K → ℝ) {z : Fin K → ℝ} (hz : z ∈ stdSimplex ℝ (Fin K)) :
    passiveTime β P B ω z =
      fCoef β P B ω z + β * (gVec β P B ω z ⬝ᵥ fun j => passiveTime β P B ω (P j)) := by
  by_cases hex : ∃ t : ℕ, ω ⬝ᵥ B < (z ᵥ* P ^ t) ⬝ᵥ B
  · let n := Nat.find hex
    have hcross : crossTime P B ω z = n := by simp [crossTime, hex, n]
    have hpas : ∀ j < n, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B) := fun j hj => Nat.find_min hex hj
    have hact_lt : ω ⬝ᵥ B < (z ᵥ* P ^ n) ⬝ᵥ B := Nat.find_spec hex
    have hyn : z ᵥ* P ^ n ∈ stdSimplex ℝ (Fin K) := vecMul_pow_mem_simplex hP hz n
    have hrule : thresholdRule B ω (z ᵥ* P ^ n) = true := decide_eq_true hact_lt
    have hact_eq : passiveTime β P B ω (z ᵥ* P ^ n) =
        β * ((z ᵥ* P ^ n) ⬝ᵥ fun j => passiveTime β P B ω (P j)) := by
      rw [passive_eq_beliefStep β hβ0 hβ1 P hP B ω hyn, hrule]
      simp [beliefStep, dotProduct]
    rw [passive_orbit β hβ0 hβ1 P hP B ω hz n hpas, hact_eq]
    simp [fCoef, gVec, hcross, discPow, ENat.recTopCoe_natCast, ENat.toNat_natCast,
      smul_dotProduct, smul_eq_mul]
    ring
  · have htop : crossTime P B ω z = ⊤ := by simp [crossTime, hex]
    have hno : ∀ j : ℕ, ¬(ω ⬝ᵥ B < (z ᵥ* P ^ j) ⬝ᵥ B) := fun j hj => hex ⟨j, hj⟩
    let C : ℝ := 1 / (1 - β) + |1 / (1 - β)|
    have hdiff_le : ∀ n : ℕ, |passiveTime β P B ω z - 1 / (1 - β)| ≤ β ^ n * C := by
      intro n
      have horb := passive_orbit β hβ0 hβ1 P hP B ω hz n (fun j _ => hno j)
      have h1 : 1 - β ≠ 0 := sub_ne_zero.mpr (ne_of_gt hβ1)
      have halg : passiveTime β P B ω z - 1 / (1 - β) =
          β ^ n * (passiveTime β P B ω (z ᵥ* P ^ n) - 1 / (1 - β)) := by
        rw [horb]; field_simp [h1]; ring
      rw [halg, abs_mul, abs_of_pos (pow_pos hβ0 n)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le n)
      have hv_le := passive_abs_le β hβ0 hβ1 P hP B ω (vecMul_pow_mem_simplex hP hz n)
      dsimp [C]
      linarith [abs_sub (passiveTime β P B ω (z ᵥ* P ^ n)) (1 / (1 - β)), hv_le]
    have ht0 : Tendsto (fun n : ℕ => β ^ n * C) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const C
    have habs_eq : |passiveTime β P B ω z - 1 / (1 - β)| = 0 :=
      le_antisymm (ge_of_tendsto ht0 (Eventually.of_forall hdiff_le)) (abs_nonneg _)
    have hz_eq : passiveTime β P B ω z = 1 / (1 - β) :=
      sub_eq_zero.mp (abs_eq_zero.mp habs_eq)
    rw [hz_eq]
    simp [fCoef, gVec, htop, discPow, ENat.recTopCoe_top]

lemma GMat_mulVec_apply {K : ℕ} (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ) (B ω v : Fin K → ℝ)
    (k : Fin K) :
    (GMat β P B ω *ᵥ v) k = gVec β P B ω (P k) ⬝ᵥ v := by
  simp only [GMat, Matrix.mulVec, dotProduct, Matrix.of_apply]

end _M6DenomHelper

open RelaxedIndexability

theorem solution {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) :
    whittleDenominator β P B ω =
        1 + β * passiveTime β P B ω (ω ᵥ* P) - β * (ω ⬝ᵥ fun k => passiveTime β P B ω (P k)) ∧
    (β * (ω ⬝ᵥ fun k => passiveTime β P B ω (P k)) ≠ 1 + β * passiveTime β P B ω (ω ᵥ* P) ↔
      whittleDenominator β P B ω ≠ 0) := by
  let d : Fin K → ℝ := fun k => passiveTime β P B ω (P k)
  have hunit : IsUnit (1 - β • GMat β P B ω) :=
    (lemma_3 β hβ0 hβ1 P hP B ω hω 0).2.2
  cases hunit.nonempty_invertible
  have hlin_d : FVec β P B ω = (1 - β • GMat β P B ω) *ᵥ d := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, FVec]
    rw [_M6DenomHelper.GMat_mulVec_apply]
    have hk := _M6DenomHelper.passive_renewal_unified β hβ0 hβ1 P hP B ω
      (_M6DenomHelper.row_mem_simplex hP k)
    dsimp [d] at hk ⊢
    linarith
  have hHF_eq_d : HMat β P B ω *ᵥ FVec β P B ω = d := by
    unfold HMat
    exact Matrix.inv_mulVec_eq_vec hlin_d
  have hpas_ωP : passiveTime β P B ω (ω ᵥ* P) =
      fCoef β P B ω (ω ᵥ* P) + β * (gVec β P B ω (ω ᵥ* P) ⬝ᵥ d) :=
    _M6DenomHelper.passive_renewal_unified β hβ0 hβ1 P hP B ω
      (_M6DenomHelper.vecMul_mem_simplex hP hω)
  have hden_eq : whittleDenominator β P B ω =
      1 + β * passiveTime β P B ω (ω ᵥ* P) - β * (ω ⬝ᵥ d) := by
    unfold whittleDenominator
    rw [hHF_eq_d, hpas_ωP, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  refine ⟨hden_eq, ?_⟩
  rw [hden_eq]
  constructor
  · intro hne hzero
    exact hne (by linarith)
  · intro hne heq
    exact hne (by linarith)
