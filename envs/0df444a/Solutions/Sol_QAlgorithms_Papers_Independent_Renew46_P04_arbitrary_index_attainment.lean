-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.arbitrary_index_attainment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:16:08.749231+00:00
-- url     : https://prove2.me/submissions/a33aa96c-4a05-4dc7-873f-52abb387fc96

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_crossnorm_ball
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
import Mathlib.Tactic

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators ENNReal

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9Sequence
variable {K X Y : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

noncomputable def algebraicPair : X →ₗ[K] Y →ₗ[K] Algebraic K X Y :=
  LinearMap.mk₂ K (fun x y => PiTensorProduct.tprod K (pair x y))
    (fun x x' y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (x + x'), e x, e x']
      exact (PiTensorProduct.tprod K).map_update_add (pair 0 y) false (ULift.up x) (ULift.up x'))
    (fun c x y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (c • x), e x]
      exact (PiTensorProduct.tprod K).map_update_smul (pair 0 y) false c (ULift.up x))
    (fun x y y' => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (y + y'), e y, e y']
      exact (PiTensorProduct.tprod K).map_update_add (pair x 0) true (ULift.up y) (ULift.up y'))
    (fun c x y => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (c • y), e y]
      exact (PiTensorProduct.tprod K).map_update_smul (pair x 0) true c (ULift.up y))


def purePair : X →ₗ[K] Y →ₗ[K] Projective K X Y :=
  LinearMap.mk₂ K (fun x y => pure (K := K) x y)
    (fun x x' y => by change algebraicInclusion (algebraicPair (x + x') y) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun c x y => by change algebraicInclusion (algebraicPair (c • x) y) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun x y y' => by change algebraicInclusion (algebraicPair x (y + y')) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun c x y => by change algebraicInclusion (algebraicPair x (c • y)) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)

lemma pure_eq (x : X) (y : Y) : pure (K := K) x y = purePair x y := rfl

lemma pure_norm (x : X) (y : Y) : ‖pure (K := K) x y‖ = ‖x‖ * ‖y‖ :=
  (projective_crossnorm_ball (K := K) (X := X) (Y := Y)).1 x y

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

lemma ext_pure_general {L M : Projective K X Y →L[K] Z}
    (h : ∀ x y, L (pure x y) = M (pure x y)) : L = M := by
  have hL := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Z)).2.2.1
    (restrictBilinear M) L (fun x y => h x y)
  have hM := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := Z)).2.2.1
    (restrictBilinear M) M (fun _ _ => rfl)
  exact hL.trans hM.symm

def ofCurried (A : X →L[K] Y →L[K] Z) : Bilinear K X Y Z :=
  MultilinearMap.mkContinuous
    { toFun := fun m => A (m false).down (m true).down
      map_update_add' := by
        intro _ m i p q
        cases i
        · simp only [Function.update_self, Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change A (p.down + q.down) (m true).down = _
          simp only [map_add, ContinuousLinearMap.add_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change A (m false).down (p.down + q.down) = _
          exact map_add _ _ _
      map_update_smul' := by
        intro _ m i c p
        cases i
        · simp only [Function.update_self, Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change A (c • p.down) (m true).down = _
          simp only [map_smul, ContinuousLinearMap.smul_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change A (m false).down (c • p.down) = _
          exact map_smul _ _ _ }
    ‖A‖ (by
      intro m
      change ‖A (m false).down (m true).down‖ ≤ ‖A‖ * ∏ i : Bool, ‖m i‖
      simp only [Fintype.prod_bool]
      change _ ≤ ‖A‖ * (‖(m true).down‖ * ‖(m false).down‖)
      calc _ ≤ ‖A (m false).down‖ * ‖(m true).down‖ := (A _).le_opNorm _
        _ ≤ (‖A‖ * ‖(m false).down‖) * ‖(m true).down‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ = _ := by ring)

lemma ofCurried_norm (A : X →L[K] Y →L[K] Z) : ‖ofCurried A‖ ≤ ‖A‖ := by
  unfold ofCurried
  exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable {I : Type*}

lemma l1_norm (a : lp (fun _ : I => Y) 1) : ‖a‖ = ∑' i, ‖a i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a

lemma l1_summable (a : lp (fun _ : I => Y) 1) : Summable (fun i => ‖a i‖) := by
  simpa using a.2.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

def synth (b : I → X →L[K] Y) (hb : ∀ i x, ‖b i x‖ ≤ ‖x‖) :
    lp (fun _ : I => X) 1 →L[K] Y :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' i, b i (a i)
      map_add' := by
        intro a c
        change (∑' i, b i (a i + c i)) = _
        simp only [map_add]
        exact (Summable.tsum_add
          ((l1_summable a).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i _)).of_norm
          ((l1_summable c).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i _)).of_norm)
      map_smul' := by
        intro r a
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul]
        exact Summable.tsum_const_smul r
          ((l1_summable a).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i _)).of_norm }
    1 (by
      intro a
      have hs := (l1_summable a).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i (a i))
      change ‖∑' i, b i (a i)‖ ≤ 1 * ‖a‖
      rw [one_mul, l1_norm]
      exact
        (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun i => hb i (a i)) (l1_summable a)))

lemma synth_apply (b : I → X →L[K] Y) (hb : ∀ i x, ‖b i x‖ ≤ ‖x‖)
    (a : lp (fun _ : I => X) 1) : synth b hb a = ∑' i, b i (a i) := rfl

lemma synth_contract (b : I → X →L[K] Y) (hb : ∀ i x, ‖b i x‖ ≤ ‖x‖)
    (a : lp (fun _ : I => X) 1) : ‖synth b hb a‖ ≤ ‖a‖ := by
  rw [synth_apply]
  have hs := (l1_summable a).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hb i (a i))
  rw [l1_norm]
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (fun i => hb i (a i)) (l1_summable a))

def seqSmul (a : LOne K I) (y : Y) : lp (fun _ : I => Y) 1 :=
  ⟨fun i => a i • y, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, norm_smul] using
      (l1_summable a).mul_right ‖y‖⟩

lemma seqSmul_norm (a : LOne K I) (y : Y) : ‖seqSmul a y‖ = ‖a‖ * ‖y‖ := by
  simp only [l1_norm, seqSmul, norm_smul, tsum_mul_right]

def seqRight (a : LOne K I) : Y →L[K] lp (fun _ : I => Y) 1 :=
  LinearMap.mkContinuous
    { toFun := fun y => seqSmul a y
      map_add' := by intros; ext i; exact smul_add _ _ _
      map_smul' := by intros; ext i; exact smul_comm _ _ _ }
    ‖a‖ (fun y => by
      change ‖seqSmul a y‖ ≤ ‖a‖ * ‖y‖
      exact (seqSmul_norm a y).le)

lemma seqRight_norm (a : LOne K I) : ‖seqRight (Y := Y) a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

def seqCurried (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖) :
    X →L[K] Y →L[K] lp (fun _ : I => Y) 1 :=
  LinearMap.mkContinuous
    { toFun := fun x => seqRight (A x)
      map_add' := by
        intro x x'
        ext y i
        change (A (x + x')) i • y = (A x) i • y + (A x') i • y
        simp only [map_add, lp.coeFn_add, Pi.add_apply, add_smul]
      map_smul' := by
        intro c x
        ext y i
        change (A (c • x)) i • y = c • ((A x) i • y)
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul] }
    1 (fun x => by
      change ‖seqRight (Y := Y) (A x)‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using (seqRight_norm (Y := Y) (A x)).trans (hA x))

def extract (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖) :
    Projective K X Y →L[K] lp (fun _ : I => Y) 1 :=
  extendBilinear (ofCurried (seqCurried A hA))

lemma seqCurried_apply (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖) (x : X) (y : Y) :
    seqCurried A hA x y = seqSmul (A x) y := rfl

lemma seqCurried_norm (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖) :
    ‖seqCurried (Y := Y) A hA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ 1 * ‖x‖)
  intro y
  rw [seqCurried_apply, seqSmul_norm, one_mul]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg y)

lemma extract_pure (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖) (x : X) (y : Y) :
    extract A hA (pure x y) = seqSmul (A x) y :=
  (bilinear_extension (K := K) (X := X) (Y := Y) (Z := lp (fun _ : I => Y) 1)).2.1 _ x y

set_option maxHeartbeats 1000000 in
lemma extract_contract (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (z : Projective K X Y) : ‖extract A hA z‖ ≤ ‖z‖ := by
  have hn : ‖seqCurried (Y := Y) A hA‖ ≤ 1 := seqCurried_norm (K := K) (Y := Y) A hA
  have hb : ‖ofCurried (seqCurried (Y := Y) A hA)‖ ≤ 1 :=
    (ofCurried_norm (K := K) (X := X) (Y := Y) (Z := lp (fun _ : I => Y) 1)
      (seqCurried (K := K) (Y := Y) A hA)).trans hn
  obtain ⟨E, hE, _⟩ := (bilinear_extension (K := K) (X := X) (Y := Y)
    (Z := lp (fun _ : I => Y) 1)).1
  have he : ‖extract (Y := Y) A hA‖ ≤ 1 := by
    change ‖extendBilinear (ofCurried (seqCurried (K := K) (Y := Y) A hA))‖ ≤ 1
    rw [← hE, E.norm_map]
    exact hb
  exact ((extract (K := K) (X := X) (Y := Y) A hA).le_opNorm z).trans
    (mul_le_of_le_one_left (norm_nonneg z) he)

def pureRight (x : X) : Y →L[K] Projective K X Y :=
  (purePair x).mkContinuous ‖x‖ (fun y => (pure_norm x y).le)

def assemble (e : I → X) (he : ∀ i, ‖e i‖ = 1) :
    lp (fun _ : I => Y) 1 →L[K] Projective K X Y :=
  synth (fun i => pureRight (e i)) (fun i y => by change ‖pure (K := K) (e i) y‖ ≤ ‖y‖; rw [pure_norm, he, one_mul])

lemma assemble_contract (e : I → X) (he : ∀ i, ‖e i‖ = 1)
    (a : lp (fun _ : I => Y) 1) : ‖assemble (K := K) e he a‖ ≤ ‖a‖ :=
  synth_contract (K := K) _ _ a

lemma assemble_extract (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (e : I → X) (he : ∀ i, ‖e i‖ = 1)
    (hexp : ∀ x, HasSum (fun i => (A x) i • e i) x) (z : Projective K X Y) :
    assemble e he (extract A hA z) = z := by
  have hid : (assemble (Y := Y) e he).comp (extract A hA) = ContinuousLinearMap.id K _ := by
    apply ext_pure_general
    intro x y
    change assemble e he (extract A hA (pure x y)) = pure x y
    rw [extract_pure]
    let R : X →L[K] Projective K X Y :=
      ((purePair (Y := Y)).flip y).mkContinuous ‖y‖ (fun x => by
        change ‖pure (K := K) x y‖ ≤ ‖y‖ * ‖x‖
        rw [pure_norm, mul_comm])
    have hs := (hexp x).map R R.continuous
    change (∑' i, pure (K := K) (e i) ((A x) i • y)) = pure x y
    calc
      _ = ∑' i, R ((A x) i • e i) := by
        apply tsum_congr
        intro i
        change pure (K := K) (e i) ((A x) i • y) = pure ((A x) i • e i) y
        simp only [pure_eq, map_smul, LinearMap.smul_apply]
      _ = pure x y := hs.tsum_eq
  exact DFunLike.congr_fun hid z

lemma tensor_attains (A : X →L[K] LOne K ℕ) (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (e : ℕ → X) (he : ∀ i, ‖e i‖ = 1)
    (hexp : ∀ x, HasSum (fun i => (A x) i • e i) x) (z : Projective K X Y) : TensorAttains z := by
  let a := extract (Y := Y) A hA z
  have ha : HasSum (fun i => pure (K := K) (e i) (a i)) z := by
    have hs : Summable (fun i => pure (K := K) (e i) (a i)) := .of_norm (by
      simpa only [pure_norm, he, one_mul] using l1_summable a)
    convert hs.hasSum using 1
    exact (assemble_extract A hA e he hexp z).symm
  refine ⟨e, fun i => a i, ⟨⟨max 1 ‖a‖, fun i => ⟨?_, ?_⟩⟩, ?_, ha⟩, ?_⟩
  · rw [he]; exact le_max_left _ _
  · exact (lp.norm_apply_le_norm (by norm_num) a i).trans (le_max_right _ _)
  · simpa only [he, one_mul] using l1_summable a
  · simp only [he, one_mul, ← l1_norm]
    exact le_antisymm (by rw [← assemble_extract A hA e he hexp z]; exact assemble_contract (K := K) e he a)
      (extract_contract A hA z)

end X9Sequence



noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators ENNReal Topology Classical
open Filter

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9CZero
variable {K I : Type*} [RCLike K]

-- Coordinate vectors and evaluation functionals on the discrete c0 space.
def single (i : I) (a : K) : CZero K I := by
  classical
  exact
    { toFun := fun j => if j.ofTopology = i then a else 0
      continuous_toFun := continuous_of_discreteTopology
      zero_at_infty' := by
        rw [Filter.cocompact_eq_cofinite]
        apply tendsto_const_nhds.congr'
        filter_upwards [Filter.eventually_cofinite_ne (WithTopology.toTopology ⊥ i)] with j hj
        have hj' : j.ofTopology ≠ i := by intro h; apply hj; cases j; cases h; rfl
        simp [hj'] }

@[simp] lemma single_apply (i j : I) (a : K) :
    single i a (WithTopology.toTopology ⊥ j) = if j = i then a else 0 := by
  classical
  rfl

lemma norm_le (x : CZero K I) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖x (WithTopology.toTopology ⊥ i)‖ ≤ C) : ‖x‖ ≤ C := by
  change ‖x.toBCF‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).2
  intro i
  exact h i.ofTopology

lemma apply_le (x : CZero K I) (i : I) : ‖x (WithTopology.toTopology ⊥ i)‖ ≤ ‖x‖ :=
  x.toBCF.norm_coe_le_norm _

lemma single_norm (i : I) (a : K) : ‖single i a‖ = ‖a‖ := by
  classical
  apply le_antisymm
  · apply norm_le _ (norm_nonneg _)
    intro j
    by_cases hj : j = i <;> simp [hj]
  · simpa using apply_le (single i a) i

def eval (i : I) : CZero K I →L[K] K :=
  LinearMap.mkContinuous
    { toFun := fun x => x (WithTopology.toTopology ⊥ i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun x => by simpa using apply_le x i)

@[simp] lemma eval_apply (i : I) (x : CZero K I) :
    eval i x = x (WithTopology.toTopology ⊥ i) := rfl

lemma eval_norm (i : I) : ‖eval (K := K) i‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa using apply_le x i
  · have h := (eval (K := K) i).le_opNorm (single i 1)
    simpa [single_norm] using h

lemma single_expansion (x : CZero K I) :
    HasSum (fun i : I => x (WithTopology.toTopology ⊥ i) • single (K := K) i 1) x := by
  classical
  apply Metric.tendsto_nhds.2
  intro ε hε
  have ht := Metric.tendsto_nhds.mp x.zero_at_infty' (ε / 2) (half_pos hε)
  rw [Filter.cocompact_eq_cofinite] at ht
  have hf : {j : WithDiscreteTopology I | ¬ dist (x j) 0 < ε / 2}.Finite := ht
  let s : Finset I := hf.toFinset.image WithTopology.ofTopology
  filter_upwards [Filter.eventually_atTop.2 ⟨s, fun t ht => ht⟩] with t ht
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (norm_le _ (by positivity : 0 ≤ ε / 2) ?_) (half_lt_self hε)
  intro j
  change ‖eval j ((∑ i ∈ t, x (WithTopology.toTopology ⊥ i) • single i 1 : CZero K I) - x)‖ ≤ ε / 2
  simp only [map_sub, map_sum, map_smul, eval_apply, single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hj : j ∈ t
  · simp [Finset.sum_ite_eq', hj]
    positivity
  · have hj' : dist (x (WithTopology.toTopology ⊥ j)) 0 < ε / 2 := by
      by_contra hn
      have : j ∈ s := Finset.mem_image.2 ⟨WithTopology.toTopology ⊥ j,
        hf.mem_toFinset.2 hn, rfl⟩
      exact hj (ht this)
    simpa [Finset.sum_ite_eq', hj] using hj'.le

lemma dual_coeff_sum (f : CZero K I →L[K] K) (s : Finset I) :
    ∑ i ∈ s, ‖f (single i 1)‖ ≤ ‖f‖ := by
  classical
  choose c hc he using fun i : I => RCLike.exists_norm_eq_mul_self (f (single i 1))
  let x : CZero K I := ∑ i ∈ s, c i • single i 1
  have hx : ‖x‖ ≤ 1 := by
    apply norm_le _ zero_le_one
    intro j
    change ‖eval j (∑ i ∈ s, c i • single i 1 : CZero K I)‖ ≤ 1
    simp only [map_sum, map_smul, eval_apply, single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    by_cases hj : j ∈ s <;> simp [Finset.sum_ite_eq', hj, hc]
  have heq : f x = ((∑ i ∈ s, ‖f (single i 1)‖ : ℝ) : K) := by
    simp only [x, map_sum, map_smul, smul_eq_mul, ← he, RCLike.ofReal_sum]
  have h := (f.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg _) hx)
  rw [heq, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
  exact h

lemma dual_coeff_summable (f : CZero K I →L[K] K) : Summable (fun i => ‖f (single i 1)‖) :=
  summable_of_sum_le (fun _ => norm_nonneg _) (dual_coeff_sum f)

def dualCoeffLinear : (CZero K I →L[K] K) →ₗ[K] LOne K I where
  toFun f := ⟨fun i => f (single i 1), memℓp_gen (by simpa using dual_coeff_summable f)⟩
  map_add' := by intros; ext i; rfl
  map_smul' := by intros; ext i; rfl

lemma dualCoeffLinear_contract (f : CZero K I →L[K] K) : ‖dualCoeffLinear f‖ ≤ ‖f‖ := by
  rw [X9Sequence.l1_norm]
  change (∑' i, ‖f (single i 1)‖) ≤ ‖f‖
  exact Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (dual_coeff_sum f)

def dualCoeffs : (CZero K I →L[K] K) →L[K] LOne K I :=
  (dualCoeffLinear (K := K) (I := I)).mkContinuous 1
    (fun (f : CZero K I →L[K] K) => by
      simpa only [one_mul] using dualCoeffLinear_contract (K := K) (I := I) f)

lemma dualCoeffs_contract (f : CZero K I →L[K] K) : ‖dualCoeffs f‖ ≤ ‖f‖ := by
  exact dualCoeffLinear_contract (K := K) (I := I) f

lemma norm_smul_eval_le (c : K) (i : I) : ‖c • eval (K := K) i‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (c • eval (K := K) i) (norm_nonneg c)
  intro x
  change ‖c * x (WithTopology.toTopology ⊥ i)‖ ≤ ‖c‖ * ‖x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (apply_le x i) (norm_nonneg c)

set_option maxHeartbeats 1000000 in
lemma dual_expansion (f : CZero K I →L[K] K) :
    HasSum (fun i : I => (dualCoeffs f) i • eval (K := K) i) f := by
  classical
  have hc : Summable (fun i : I => ‖(dualCoeffs f) i‖) := by
    change Summable (fun i : I => ‖f (single i 1)‖)
    exact dual_coeff_summable f
  have hnorm : Summable (fun i : I => ‖(dualCoeffs f) i • eval (K := K) i‖) := by
    exact hc.of_nonneg_of_le
      (fun i => ContinuousLinearMap.opNorm_nonneg ((dualCoeffs f) i • eval (K := K) i))
      (fun i => norm_smul_eval_le (K := K) ((dualCoeffs f) i) i)
  have hs : Summable (fun i : I => (dualCoeffs f) i • eval (K := K) i) :=
    Summable.of_norm (f := fun i : I => (dualCoeffs f) i • eval (K := K) i) hnorm
  have heq : ∑' i : I, (dualCoeffs f) i • eval (K := K) i = f := by
    apply ContinuousLinearMap.ext
    intro x
    have hleft := hs.hasSum.map (ContinuousLinearMap.apply K K x) (by fun_prop)
    have hright := (single_expansion x).map f f.continuous
    exact hleft.unique (by
      convert hright using 1
      funext i
      change f (single i 1) * x (WithTopology.toTopology ⊥ i) =
        f (x (WithTopology.toTopology ⊥ i) • single i 1)
      rw [map_smul, smul_eq_mul, mul_comm])
  convert hs.hasSum using 1
  exact heq.symm

end X9CZero


noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators ENNReal

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9Sequence
variable {K X Y I : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

lemma tensor_attains_any (A : X →L[K] LOne K I) (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (e : I → X) (he : ∀ i, ‖e i‖ = 1)
    (hexp : ∀ x, HasSum (fun i => (A x) i • e i) x) (z : Projective K X Y) : TensorAttains z := by
  classical
  let a := extract (Y := Y) A hA z
  have ha : HasSum (fun i => pure (K := K) (e i) (a i)) z := by
    have hs : Summable (fun i => pure (K := K) (e i) (a i)) := .of_norm (by
      simpa only [pure_norm, he, one_mul] using l1_summable a)
    convert hs.hasSum using 1
    exact (assemble_extract A hA e he hexp z).symm
  have hn : ‖z‖ = ‖a‖ := le_antisymm
    (by rw [← assemble_extract A hA e he hexp z]; exact assemble_contract (K := K) e he a)
    (extract_contract A hA z)
  let S := Function.support (fun i => a i)
  have hsa : Summable (fun i => a i) := (l1_summable a).of_norm
  have hc : S.Countable := hsa.countable_support
  letI := hc.toEncodable
  let j : S → ℕ := Encodable.encode
  have hj : Function.Injective j := Encodable.encode_injective
  let xs : ℕ → X := Function.extend j (fun i : S => e i) 0
  let ys : ℕ → Y := Function.extend j (fun i : S => a i) 0
  have hxs (i : S) : xs (j i) = e i := hj.extend_apply _ _ i
  have hys (i : S) : ys (j i) = a i := hj.extend_apply _ _ i
  have hzero (n : ℕ) (hn : n ∉ Set.range j) : xs n = 0 ∧ ys n = 0 :=
    ⟨Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn⟩
  have hs : HasSum (fun n => pure (K := K) (xs n) (ys n)) z := by
    apply (hj.hasSum_iff (fun n hn => ?_)).1
    · change HasSum (fun i : S => pure (K := K) (xs (j i)) (ys (j i))) z
      simp only [hxs, hys]
      exact (hasSum_subtype_iff_of_support_subset
        (f := fun i : I => pure (K := K) (e i) (a i)) (a := z) (s := S) (by
        intro i hi
        change a i ≠ 0
        intro hai
        apply hi
        change pure (K := K) (e i) (a i) = 0
        rw [hai, pure_eq, map_zero])).2 ha
    · rw [(hzero n hn).1, (hzero n hn).2, pure_eq, map_zero]
  have hnorm : HasSum (fun n => ‖xs n‖ * ‖ys n‖) ‖a‖ := by
    apply (hj.hasSum_iff (fun n hn => ?_)).1
    · change HasSum (fun i : S => ‖xs (j i)‖ * ‖ys (j i)‖) ‖a‖
      simp only [hxs, hys, he, one_mul]
      have hna : HasSum (fun i : I => ‖a i‖) ‖a‖ := by
        rw [l1_norm a]
        exact (l1_summable a).hasSum
      exact (hasSum_subtype_iff_of_support_subset
        (f := fun i : I => ‖a i‖) (a := ‖a‖) (s := S) (by
          intro i hi
          change a i ≠ 0
          intro hai
          apply hi
          change ‖a i‖ = 0
          rw [hai, norm_zero])).2 hna
    · rw [(hzero n hn).1, (hzero n hn).2, norm_zero, zero_mul]
  refine ⟨xs, ys, ⟨⟨max 1 ‖a‖, fun n => ?_⟩, hnorm.summable, hs⟩, ?_⟩
  · by_cases h : n ∈ Set.range j
    · obtain ⟨i, rfl⟩ := h
      rw [hxs, hys, he]
      exact ⟨le_max_left _ _, (lp.norm_apply_le_norm (by norm_num) a i).trans (le_max_right _ _)⟩
    · rw [(hzero n h).1, (hzero n h).2]
      simp only [norm_zero]
      exact ⟨le_trans zero_le_one (le_max_left _ _), le_trans zero_le_one (le_max_left _ _)⟩
  · exact hn.trans hnorm.tsum_eq.symm

end X9Sequence


noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000
open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators ENNReal

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9ArbitraryBridge
open X9Sequence

structure Coordinates (K X I : Type*) [RCLike K] [NormedAddCommGroup X] [NormedSpace K X] where
  coeff : (X →L[K] K) →L[K] LOne K I
  contract : ∀ f, ‖coeff f‖ ≤ ‖f‖
  basis : I → (X →L[K] K)
  norm_basis : ∀ i, ‖basis i‖ = 1
  expansion : ∀ f, HasSum (fun i => (coeff f) i • basis i) f
  point : I → X
  coeff_eq : ∀ f i, (coeff f) i = f (point i)

variable {K X Y I : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

def coordExtract (C : Coordinates K X I) : Projective K (X →L[K] K) Y →L[K] lp (fun _ : I => Y) 1 :=
  extract (K := K) (X := X →L[K] K) (Y := Y) (I := I) C.coeff C.contract

lemma reconstruct (C : Coordinates K X I) (z : Projective K (X →L[K] K) Y) :
    assemble (K := K) (Y := Y) C.basis C.norm_basis (coordExtract C z) = z :=
  assemble_extract (K := K) (X := X →L[K] K) (Y := Y) (I := I)
    C.coeff C.contract C.basis C.norm_basis C.expansion z

lemma realization_pure (f : X →L[K] K) (y : Y) :
    projectiveRealization (K := K) (X := X) (Y := Y) (pure f y) = f.smulRight y :=
  (bilinear_extension (K := K) (X := X →L[K] K) (Y := Y) (Z := X →L[K] Y)).2.1 _ f y

lemma extract_coordinate (C : Coordinates K X I) (z : Projective K (X →L[K] K) Y) (i : I) :
    coordExtract C z i = projectiveRealization (K := K) (X := X) (Y := Y) z (C.point i) := by
  let L : lp (fun _ : I => Y) 1 →L[K] Y := lp.evalCLM K (fun _ : I => Y) 1 i
  have he : L.comp (coordExtract (Y := Y) C) =
      (ContinuousLinearMap.apply K Y (C.point i)).comp
        (projectiveRealization (K := K) (X := X) (Y := Y)) := by
    apply ext_pure_general
    intro f y
    change L (extract (K := K) (Y := Y) C.coeff C.contract (pure f y)) = _
    rw [extract_pure]
    simp only [ContinuousLinearMap.comp_apply, realization_pure,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.smulRight_apply]
    change (C.coeff f) i • y = f (C.point i) • y
    rw [C.coeff_eq]
  exact DFunLike.congr_fun he z

lemma kernel_zero (C : Coordinates K X I) (z : Projective K (X →L[K] K) Y)
    (hz : projectiveRealization (K := K) (X := X) (Y := Y) z = 0) : z = 0 := by
  have he : coordExtract (Y := Y) C z = 0 := by
    ext i
    rw [extract_coordinate, hz, ContinuousLinearMap.zero_apply]
    rfl
  rw [← reconstruct C z, he, map_zero]

lemma quotient_norm (C : Coordinates K X I) (z : Projective K (X →L[K] K) Y) :
    ‖nuclearQuotient (K := K) (X := X) (Y := Y) z‖ = ‖z‖ := by
  have hle : ‖nuclearQuotient (K := K) (X := X) (Y := Y) z‖ ≤ ‖z‖ :=
    Submodule.Quotient.norm_mk_le (projectiveRealization (K := K) (X := X) (Y := Y)).ker z
  apply le_antisymm hle
  apply le_of_forall_pos_le_add
  intro ε hε
  change ‖z‖ ≤ ‖nuclearQuotient (K := K) (X := X) (Y := Y) z‖ + ε
  obtain ⟨a, ha, han⟩ := Submodule.Quotient.norm_mk_lt
    (nuclearQuotient (K := K) (X := X) (Y := Y) z) hε
  have hqa : nuclearQuotient (K := K) (X := X) (Y := Y) a = nuclearQuotient z := ha
  have hJa : projectiveRealization (K := K) (X := X) (Y := Y) a = projectiveRealization z :=
    congrArg nuclearOperator hqa
  have haz : a = z := sub_eq_zero.mp (kernel_zero C (a - z) (by rw [map_sub, hJa, sub_self]))
  simpa only [haz] using han.le

lemma map_attains (C : Coordinates K X I) {z : Projective K (X →L[K] K) Y}
    (hz : TensorAttains z) : NuclearAttains (nuclearQuotient (K := K) (X := X) z) := by
  obtain ⟨f, y, hrep, hcost⟩ := hz
  refine ⟨f, y, ⟨hrep.1, hrep.2.1, fun x => ?_⟩, ?_⟩
  · have hs := (hrep.2.2.map (projectiveRealization (K := K) (X := X) (Y := Y))
      (projectiveRealization (K := K) (X := X) (Y := Y)).continuous).map
      (ContinuousLinearMap.apply K Y x) (ContinuousLinearMap.apply K Y x).continuous
    convert hs using 1
    · funext n
      simp [realization_pure]
    · rfl
  · rw [quotient_norm C]
    exact hcost

lemma nuclear_all (C : Coordinates K X I)
    (ht : ∀ z : Projective K (X →L[K] K) Y, TensorAttains z) (T : Nuclear K X Y) : NuclearAttains T := by
  obtain ⟨z, rfl⟩ := (projectiveRealization (K := K) (X := X) (Y := Y)).ker.mkQ_surjective T
  exact map_attains C (ht z)

lemma dual_tensor_attains_any (C : Coordinates K X I) (z : Projective K (X →L[K] K) Y) : TensorAttains z :=
  tensor_attains_any (K := K) (X := X →L[K] K) (Y := Y)
    C.coeff C.contract C.basis C.norm_basis C.expansion z

end X9ArbitraryBridge

namespace X9ArbitraryConclusion
open X9ArbitraryBridge
variable {K I Y : Type*} [RCLike K]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

def coords : Coordinates K (CZero K I) I where
  coeff := X9CZero.dualCoeffs (K := K) (I := I)
  contract := X9CZero.dualCoeffs_contract (K := K) (I := I)
  basis := X9CZero.eval (K := K) (I := I)
  norm_basis := X9CZero.eval_norm (K := K) (I := I)
  expansion := X9CZero.dual_expansion (K := K) (I := I)
  point := fun i => X9CZero.single i 1
  coeff_eq := by intros; rfl

lemma c0_attains (T : Nuclear K (CZero K I) Y) : NuclearAttains T :=
  nuclear_all (K := K) (X := CZero K I) (Y := Y) (I := I)
    (coords (K := K) (I := I))
    (dual_tensor_attains_any (K := K) (X := CZero K I) (Y := Y) (coords (K := K) (I := I))) T

lemma l1_attains (z : Projective K (LOne K I) Y) : TensorAttains z := by
  classical
  apply X9Sequence.tensor_attains_any (K := K) (X := LOne K I) (Y := Y)
    (ContinuousLinearMap.id K _) (fun _ => le_rfl) (fun i => lp.single 1 i (1 : K))
  · intro i
    simp [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  · intro x
    convert lp.hasSum_single (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) x using 1
    funext i
    simp only [ContinuousLinearMap.id_apply, ← lp.single_smul, smul_eq_mul, mul_one]

end X9ArbitraryConclusion

variable {K : Type*} [RCLike K]
variable {Y : Type*}
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution (I : Type*) :
    (∀ T : Nuclear K (CZero K I) Y, NuclearAttains T) ∧
    (∀ z : Projective K (LOne K I) Y, TensorAttains z) :=
  ⟨X9ArbitraryConclusion.c0_attains (K := K) (Y := Y), X9ArbitraryConclusion.l1_attains (K := K) (Y := Y)⟩
