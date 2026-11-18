-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:48.224041+00:00
-- url     : https://prove2.me/submissions/bf5c6eef-5c4c-4d03-a7b1-5ea2a1310176
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_regression_learning
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_regression_programs
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_proposition_C_1
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

section
-- Solutions.RootMeasurability
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RootMeasurability
lemma featureDimension_pos (d p : ℕ) : 0 < featureDimension d p := Nat.choose_pos (by omega)

lemma radius_pos (d p : ℕ) : 0 < radius d p := by
  have h : (0 : ℝ) < featureDimension d p := by exact_mod_cast featureDimension_pos d p
  unfold radius
  positivity

lemma continuous_features (d p : ℕ) : Continuous (features d p) := by
  unfold features
  apply Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Index d p => ℝ))
  apply continuous_pi
  intro κ
  unfold hermite AMPLowDeg.RankOne.hermNorm
  fun_prop

lemma continuous_clipped (d p : ℕ) : Continuous (clipped d p) := by
  unfold clipped clipScale
  have hs : Continuous (fun x : Vec d => radius d p / max (radius d p) ‖features d p x‖) := by
    apply continuous_const.div (continuous_const.max (continuous_features d p).norm)
    intro x
    exact (lt_of_lt_of_le (radius_pos d p) (le_max_left _ _)).ne'
  exact continuous_smul.comp (hs.prodMk (continuous_features d p))

lemma score_measurable_joint (d p : ℕ) : Measurable (fun q : Coeff d p × Vec d => score d p q.1 q.2) := by
  exact measurable_fst.inner ((continuous_clipped d p).measurable.comp measurable_snd)

lemma sign_measurable_grid : Measurable (sign : ℝ → Bool) := by
  apply measurable_to_bool
  have he : sign ⁻¹' {true} = Ici (0 : ℝ) := by ext z; simp [sign]
  rw [he]
  exact measurableSet_Ici

lemma classification_error_integral {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : X → Bool) (hh : Measurable h) :
    (∫ z, if h z.1 ≠ z.2 then (1 : ℝ) else 0 ∂P) = error P h := by
  have hs : MeasurableSet {z : X × Bool | h z.1 ≠ z.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  have he : (fun z : X × Bool => if h z.1 ≠ z.2 then (1 : ℝ) else 0) =
      {z : X × Bool | h z.1 ≠ z.2}.indicator (fun _ => (1 : ℝ)) := by
    funext z
    simp only [indicator_apply,mem_setOf_eq]
  rw [he,integral_indicator hs,integral_const]
  simp [error]

noncomputable def gridThreshold (M : ℕ) (l : Fin M) : ℝ := -1+(2*(l.val : ℝ)+1)/M
lemma decode_measurable_joint (d p M : ℕ) :
    Measurable (fun q : Output d p M × Vec d => decode d p M q.1 q.2) := by
  have hv : Measurable (fun q : Output d p M × Vec d => q.1.1.val) :=
    measurable_subtype_coe.comp measurable_fst.fst
  have hs : Measurable (fun q : Output d p M × Vec d => score d p q.1.1.val q.2) := by
    convert! (score_measurable_joint d p).comp (hv.prodMk measurable_snd) using 1
  have ht : Measurable (fun q : Output d p M × Vec d => gridThreshold M q.1.2) :=
    (measurable_of_countable (gridThreshold M)).comp measurable_fst.snd
  convert! sign_measurable_grid.comp (hs.sub ht) using 1

lemma decode_measurable (d p M : ℕ) (o : Output d p M) : Measurable (decode d p M o) := by
  convert! (decode_measurable_joint d p M).comp (measurable_const.prodMk measurable_id) using 1

lemma error_parametric_measurable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (h : Z × X → Bool) (hh : Measurable h) :
    Measurable (fun z => error P (fun x => h (z,x))) := by
  have hm : Measurable (fun q : Z × (X × Bool) => if h (q.1,q.2.1) ≠ q.2.2 then (1 : ℝ) else 0) := by
    have hs : MeasurableSet {q : Z × (X × Bool) | h (q.1,q.2.1) ≠ q.2.2} :=
      (measurableSet_eq_fun (hh.comp (measurable_fst.prodMk measurable_snd.fst)) measurable_snd.snd).compl
    exact measurable_const.ite hs measurable_const
  have hi : Measurable (fun z : Z => ∫ x, if h (z,x.1) ≠ x.2 then (1 : ℝ) else 0 ∂P) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  convert! hi using 1
  funext z
  symm
  have hz : Measurable (fun x : X => h (z,x)) := by
    convert! hh.comp (measurable_const.prodMk measurable_id) using 1
  exact classification_error_integral P (fun x : X => h (z,x)) hz

lemma decode_error_measurable (d p M : ℕ) (P : Measure (Example d)) [IsProbabilityMeasure P] :
    Measurable (fun o : Output d p M => error P (decode d p M o)) :=
  error_parametric_measurable P (fun q => decode d p M q.1 q.2) (decode_measurable_joint d p M)
end PrivateAgnosticHalfspace.Gaussian.RootMeasurability
end

section
-- Solutions.Sol_theorem_2_1_reduced
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open PrivateAgnosticHalfspace.Gaussian
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem solution :
    ∃ (C c Cdim A : ℝ) (O : Optimizer) (optimizerCode learnerCode : LearnerProgram),
      1 ≤ C ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 1 ≤ A ∧ 0 < Cdim ∧
      2 * (C + 1) ^ 2 / c ≤ Cdim ∧
      (∀ (d p n : ℕ), 1 ≤ p → 2 ≤ n → ∀ (ε δ : ℝ),
        0 < ε ∧ ε ≤ 1 / 2 → 0 < δ ∧ δ ≤ 1 / 2 →
        Measurable (fun S => (O d p n ε δ S : Measure (UnitBall d p))) ∧
        PrivateUniformGen.Characterization.IsDP (O d p n ε δ) ε δ ∧
        ∀ S : Fin n → Example d,
          Integrable (fun v : UnitBall d p => empiricalLoss d p S v.val -
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1))
            (O d p n ε δ S : Measure (UnitBall d p)) ∧
          (∫ v : UnitBall d p, empiricalLoss d p S v.val -
            sInf (empiricalLoss d p S '' Metric.closedBall 0 1)
            ∂(O d p n ε δ S : Measure (UnitBall d p))) ≤
              A * 2 * radius d p * Real.sqrt ((featureDimension d p : ℝ) * Real.log (1 / δ)) /
                ((n : ℝ) * ε) ∧
          ∃ fuel cost : ℕ,
            (cost : ℝ) ≤ A * ((n : ℝ) * p * featureDimension d p + n ^ 2 * featureDimension d p) ∧
            Implements optimizerCode fuel cost d p 1 (optimizerInput d p n ε δ S)
              ((O d p n ε δ S : Measure (UnitBall d p)).map (fun v => (v, (0 : Fin 1))))) ∧
      ∀ (α β ε δ : ℝ),
        0 < α ∧ α ≤ 1 / 2 → 0 < β ∧ β ≤ 1 / 2 →
        0 < ε ∧ ε ≤ 1 / 2 → 0 < δ ∧ δ ≤ 1 / 2 →
      ∀ (d : ℕ), Cdim / α ^ 5 ≤ (d : ℝ) →
      let p := scheduledDegree C α
      let D := featureDimension d p
      let k := repetitions β
      let M := thresholds C α
      let n₀ := trainingSize C c α ε δ d p
      let m := validationSize C α β ε k M
      let n := k * n₀ + m
      blockCondition C c α ε δ d p n₀ ∧
      (∀ r, blockCondition C c α ε δ d p r → n₀ ≤ r) ∧
      0 < k ∧ 0 < M ∧ 0 < m ∧
      (n : ℝ) ≤ (k : ℝ) * (3 + 4 * C ^ 2 * D / (c ^ 2 * α ^ 2) +
          4 * C * D * Real.sqrt (Real.log (1 / δ)) / (c * ε * α)) + 1 +
        C * (α⁻¹ ^ 2 + (ε * α)⁻¹) * Real.log ((k : ℝ) * M / β) ∧
      ∃ L : PrivateUniformGen.Characterization.Mechanism (Example d) (Output d p M) n,
        (∀ S, (L S : Measure (Output d p M)) = algorithmLaw O d p k M n₀ m ε δ S) ∧
        Measurable (fun S => (L S : Measure (Output d p M))) ∧
        PrivateUniformGen.Characterization.IsDP L ε δ ∧
        (∀ o, Measurable (decode d p M o)) ∧
        (∀ S, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ A * ((n : ℝ) * p * D + (k : ℝ) * n₀ ^ 2 * D + (k : ℝ) * M * m * D) ∧
          (cost : ℝ) ≤ 3 * A * (n : ℝ) ^ 3 ∧
          Implements learnerCode fuel cost d p M (learnerInput d p k M n₀ m ε δ α β S)
            (L S : Measure (Output d p M))) ∧
        ∀ P : Measure (Example d), IsProbabilityMeasure P → P.map Prod.fst = gaussian d →
          Measurable (fun o => error P (decode d p M o)) ∧
          let ν := (Measure.pi (fun _ : Fin n => P)).bind (fun S => (L S : Measure (Output d p M)))
          IsProbabilityMeasure ν ∧
          ν.real {o | error P (decode d p M o) ≤ opt d P + α} ≥ 1 - β := by
  obtain ⟨O,hReal,hOpt,C,c,Cdim,hC,hc,hc4,hCdim,hCdimBound,hStat⟩ := ordered_regression_learning
  obtain ⟨optimizerCode,learnerCode,hPrograms⟩ := ordered_regression_programs
  obtain ⟨hOptimizerCode,hLearnerCode⟩ := hPrograms O hReal
  refine ⟨C,c,Cdim,100000,O,optimizerCode,learnerCode,hC,hc,hc4,by norm_num,hCdim,hCdimBound,?_,?_⟩
  · intro d p n hp hn ε δ hε hδ
    obtain ⟨hMeas,hPrivate,hExcess⟩ := hOpt d p n (by omega) ε δ hε hδ
    refine ⟨hMeas,hPrivate,?_⟩
    intro S
    obtain ⟨hInt,hBound⟩ := hExcess S
    refine ⟨hInt,hBound.trans ?_,hOptimizerCode d p n hp hn ε δ hε hδ S⟩
    have hnon : 0 ≤ radius d p*Real.sqrt ((featureDimension d p : ℝ)*Real.log (1/δ))/((n : ℝ)*ε) := by
      apply div_nonneg
      · unfold radius; positivity
      · exact mul_nonneg (Nat.cast_nonneg n) hε.1.le
    convert mul_le_mul_of_nonneg_right (show (120 : ℝ) ≤ 100000*2 by norm_num) hnon using 1 <;> ring
  · intro α β ε δ hα hβ hε hδ d hd
    dsimp only
    let p := scheduledDegree C α
    let D := featureDimension d p
    let k := repetitions β
    let M := thresholds C α
    let n₀ := trainingSize C c α ε δ d p
    let m := validationSize C α β ε k M
    let n := k*n₀+m
    obtain ⟨hBlock,hMinimal,hk,hM,hm,hp,hDn,hpD,hMp,hmBlock,hSample,hAccuracy⟩ := hStat α β ε δ hα hβ hε hδ d hd
    refine ⟨hBlock,hMinimal,hk,hM,hm,hSample,?_⟩
    obtain ⟨hMeas,hPrivate,hExcess⟩ := hOpt d p n₀ (lt_of_lt_of_le (by decide : 0 < 2) hBlock.1) ε δ hε hδ
    obtain ⟨L,hLaw,hLMeas,hLPrivate⟩ := proposition_C_1 O d p k M n₀ m hk hM hBlock.1 hm ε δ hε hδ hMeas hPrivate
    refine ⟨L,hLaw,hLMeas,hLPrivate,RootMeasurability.decode_measurable d p M,?_,?_⟩
    · intro S
      obtain ⟨fuel,cost,hCost,hCube,hImpl⟩ := hLearnerCode d p k M n₀ m hp hk hM hm hDn hmBlock hpD hMp ε δ α β hε hδ S
      rw [← hLaw S] at hImpl
      exact ⟨fuel,cost,hCost,hCube,hImpl⟩
    · intro P hProb hGaussian
      letI := hProb
      refine ⟨RootMeasurability.decode_error_measurable d p M P,?_⟩
      have hν := congrArg (fun F : (Fin n → Example d) → Measure (Output d p M) =>
        (Measure.pi (fun _ : Fin n => P)).bind F) (funext hLaw)
      have hResult := hAccuracy P hProb hGaussian
      rw [← hν] at hResult
      exact hResult
end
