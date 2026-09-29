-- Prove2me | solution 1 for TreatmentLocality.differentiable_estimator_variance_dominance_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-21T17:46:09.569932+00:00
-- url     : https://prove2.me/submissions/2c7b9779-6016-4e8b-94a0-26d85328af79

import Definitions.Def_TreatmentLocalityEstimator
import Definitions.Def_MarkovErgodicity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Theorems.Thm_MarkovChainCLT_delta_method_of_uniformly_ergodic_of_measurable

open MeasureTheory ProbabilityTheory Filter TreatmentLocality
open scoped NNReal ENNReal Topology Matrix

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Flip the arm label of a step, but only away from the crucial state. -/
def armFlip (M : Model S) (z : Step S) : Step S :=
  if z.1 = M.crucial then z else (z.1, !z.2.1, z.2.2.1, z.2.2.2)

@[simp] lemma armFlip_fst (M : Model S) (z : Step S) : (armFlip M z).1 = z.1 := by
  unfold armFlip; split <;> rfl

@[simp] lemma armFlip_next (M : Model S) (z : Step S) : (armFlip M z).2.2.1 = z.2.2.1 := by
  unfold armFlip; split <;> rfl

@[simp] lemma armFlip_rwd (M : Model S) (z : Step S) : (armFlip M z).2.2.2 = z.2.2.2 := by
  unfold armFlip; split <;> rfl

lemma armFlip_involutive (M : Model S) : Function.Involutive (armFlip M) := by
  intro z
  unfold armFlip
  by_cases h : z.1 = M.crucial
  · simp [h]
  · simp [h]

lemma measurable_armFlip (M : Model S) : Measurable (armFlip M) := by
  unfold armFlip
  apply Measurable.ite
  · exact measurable_fst (measurableSet_singleton M.crucial)
  · exact measurable_id
  · fun_prop

section Chain
variable [Countable S]

/-- Away from the crucial state the two arms execute the same action, so the
one-step law is symmetric under flipping the arm label. -/
lemma map_flip_stepLaw (M : Model S) (s : S) (hs : s ≠ M.crucial) :
    Measure.map (Prod.map Bool.not (id : S × ℝ → S × ℝ)) (stepLaw M s) = stepLaw M s := by
  have hact : ∀ b : Bool, M.act b s = false := by
    intro b; simp [Model.act, hs]
  have hmeas : Measurable (Prod.map Bool.not (id : S × ℝ → S × ℝ)) := by fun_prop
  rw [stepLaw, hact true, hact false]
  rw [Measure.map_smul, Measure.map_add _ _ hmeas]
  have e1 : ∀ b : Bool, Measure.map (Prod.map Bool.not (id : S × ℝ → S × ℝ))
      ((Measure.dirac b).prod
        (((M.trans s false).toMeasure).prod (M.reward s false)))
      = (Measure.dirac (!b)).prod
        (((M.trans s false).toMeasure).prod (M.reward s false)) := by
    intro b
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    rw [Measure.map_dirac, Measure.map_id]
  have key : (Measure.map (Prod.map Bool.not (id : S × ℝ → S × ℝ))
        ((Measure.dirac true).prod
          (((M.trans s false).toMeasure).prod (M.reward s false)))
      + Measure.map (Prod.map Bool.not (id : S × ℝ → S × ℝ))
        ((Measure.dirac false).prod
          (((M.trans s false).toMeasure).prod (M.reward s false))))
      = ((Measure.dirac true).prod
          (((M.trans s false).toMeasure).prod (M.reward s false))
        + (Measure.dirac false).prod
          (((M.trans s false).toMeasure).prod (M.reward s false))) := by
    rw [e1 true, e1 false]
    simp only [Bool.not_true, Bool.not_false]
    exact add_comm _ _

  rw [key]

lemma expKernel_apply (M : Model S) (z : Step S) :
    expKernel M z = (Measure.dirac z.2.2.1).prod (stepLaw M z.2.2.1) := by
  rw [expKernel, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply]
  rfl

lemma map_armFlip_expKernel (M : Model S) (z : Step S) :
    Measure.map (armFlip M) (expKernel M z) = expKernel M z := by
  rw [expKernel_apply, Measure.dirac_prod,
    Measure.map_map (measurable_armFlip M) (by fun_prop)]
  by_cases h : z.2.2.1 = M.crucial
  · congr 1
    funext q
    simp [Function.comp, armFlip, h]
  · have hcomp : (armFlip M) ∘ (Prod.mk z.2.2.1)
        = (Prod.mk z.2.2.1) ∘ (Prod.map Bool.not (id : S × ℝ → S × ℝ)) := by
      funext q
      simp [Function.comp, armFlip, h, Prod.map]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      map_flip_stepLaw M _ h]

lemma expKernel_armFlip (M : Model S) (z : Step S) :
    expKernel M (armFlip M z) = expKernel M z := by
  rw [expKernel_apply, expKernel_apply, armFlip_next]

/-- Pushing a measure through the arm flip does not change it, provided every
kernel measure it is built from is flip-invariant. -/
lemma map_bind_of_map_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Measure Y) (hκ : AEMeasurable κ μ)
    (f : Y → Y) (hf : Measurable f) (h : ∀ x, Measure.map f (κ x) = κ x) :
    Measure.map f (μ.bind κ) = μ.bind κ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) hκ, Measure.bind_apply hs hκ]
  refine lintegral_congr fun x => ?_
  rw [← Measure.map_apply hf hs, h x]

lemma map_armFlip_iterKernel (M : Model S) (k : ℕ) (z : Step S) :
    Measure.map (armFlip M) (MarkovChainCLT.iterKernel (expKernel M) (k + 1) z)
      = MarkovChainCLT.iterKernel (expKernel M) (k + 1) z := by
  rw [MarkovChainCLT.iterKernel_succ, Kernel.comp_apply]
  exact map_bind_of_map_eq _ _ (Kernel.aemeasurable _) _ (measurable_armFlip M)
    (map_armFlip_expKernel M)

lemma iterKernel_armFlip (M : Model S) (k : ℕ) (z : Step S) :
    MarkovChainCLT.iterKernel (expKernel M) (k + 1) (armFlip M z)
      = MarkovChainCLT.iterKernel (expKernel M) (k + 1) z := by
  induction k with
  | zero =>
      simp only [MarkovChainCLT.iterKernel_succ, MarkovChainCLT.iterKernel_zero,
        Kernel.comp_apply, Kernel.id_apply,
        Measure.dirac_bind (Kernel.measurable (expKernel M))]
      exact expKernel_armFlip M z
  | succ k ih =>
      rw [MarkovChainCLT.iterKernel_succ, Kernel.comp_apply, Kernel.comp_apply, ih]

lemma map_armFlip_measure (M : Model S) (ν : Measure (Step S))
    (hinv : Kernel.Invariant (expKernel M) ν) :
    Measure.map (armFlip M) ν = ν := by
  conv_lhs => rw [← hinv.def]
  conv_rhs => rw [← hinv.def]
  exact map_bind_of_map_eq _ _ (Kernel.aemeasurable _) _ (measurable_armFlip M)
    (map_armFlip_expKernel M)

lemma integral_comp_armFlip (M : Model S) (μ : Measure (Step S))
    (hμ : Measure.map (armFlip M) μ = μ) (φ : Step S → ℝ) (hφ : Measurable φ) :
    ∫ z, φ (armFlip M z) ∂μ = ∫ z, φ z ∂μ := by
  conv_rhs => rw [← hμ]
  rw [integral_map (measurable_armFlip M).aemeasurable hφ.aestronglyMeasurable]

/-- **Rao-Blackwell structure.** The information-sharing statistic is exactly the
average of the A/B statistic over the arm flip: away from the crucial state the
two arms execute the same action, so the arm label carries no information and
averaging over it is what pooling the samples does. -/
lemma coordAt_estObs_IS (M : Model S) (p : EstIdx S) (z : Step S) :
    coordAt (estObs M Scheme.IS z) p
      = (coordAt (estObs M Scheme.AB z) p
          + coordAt (estObs M Scheme.AB (armFlip M z)) p) / 2 := by
  obtain ⟨a, c⟩ := p
  by_cases h : z.1 = M.crucial
  · have hf : armFlip M z = z := by simp [armFlip, h]
    rw [hf]
    cases c with
    | inl ij =>
        simp only [coordAt, estObs, schemeWeight, Step.state, Step.next, Step.arm, h,
          if_true]
        ring
    | inr i =>
        simp only [coordAt, estObs, schemeWeight, Step.state, Step.rwd, Step.arm, h,
          if_true]
        ring
  · have hf : armFlip M z = (z.1, !z.2.1, z.2.2.1, z.2.2.2) := by simp [armFlip, h]
    rw [hf]
    cases c with
    | inl ij =>
        simp only [coordAt, estObs, schemeWeight, Step.state, Step.next, Step.arm, h,
          if_false]
        rcases Bool.eq_false_or_eq_true z.2.1 with hb | hb <;>
          rcases Bool.eq_false_or_eq_true a with ha | ha <;> simp [hb, ha] <;>
          first | rfl | (split_ifs <;> norm_num) | (congr 1) | simp_all
    | inr i =>
        simp only [coordAt, estObs, schemeWeight, Step.state, Step.rwd, Step.arm, h,
          if_false]
        rcases Bool.eq_false_or_eq_true z.2.1 with hb | hb <;>
          rcases Bool.eq_false_or_eq_true a with ha | ha <;> simp [hb, ha] <;>
          first | rfl | (split_ifs <;> norm_num) | (congr 1) | simp_all

/-- Coordinates attached to the crucial state are unchanged by the arm flip. -/
lemma coordAt_estObs_AB_crucial (M : Model S) (p : EstIdx S)
    (hp : idxState p = M.crucial) (z : Step S) :
    coordAt (estObs M Scheme.AB (armFlip M z)) p = coordAt (estObs M Scheme.AB z) p := by
  obtain ⟨a, c⟩ := p
  by_cases h : z.1 = M.crucial
  · have hf : armFlip M z = z := by simp [armFlip, h]
    rw [hf]
  · have hf : armFlip M z = (z.1, !z.2.1, z.2.2.1, z.2.2.2) := by simp [armFlip, h]
    rw [hf]
    cases c with
    | inl ij =>
        simp only [idxState] at hp
        have : z.1 ≠ ij.1 := fun hc => h (by rw [hc, hp])
        simp only [coordAt, estObs, schemeWeight, Step.state, Step.next, Step.arm]
        simp [this]
    | inr i =>
        simp only [idxState] at hp
        have : z.1 ≠ i := fun hc => h (by rw [hc, hp])
        simp only [coordAt, estObs, schemeWeight, Step.state, Step.rwd, Step.arm]
        simp [this]

end Chain


section Moments

variable [Fintype S]

/-- A crude uniform bound on any moment of the reward: the sum over all
state-action pairs.  Finiteness of the state space is what makes it finite. -/
noncomputable def rewardBound (M : Model S) (h : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ s : S, ∑ a : Bool, ∫⁻ x : ℝ, h x ∂(M.reward s a)

lemma lintegral_rwd_stepLaw_le (M : Model S) (h : ℝ → ℝ≥0∞) (hh : Measurable h) (s : S) :
    ∫⁻ q : Bool × S × ℝ, h q.2.2 ∂(stepLaw M s) ≤ rewardBound M h := by
  have key : ∀ b : Bool,
      ∫⁻ q : Bool × S × ℝ, h q.2.2
        ∂((Measure.dirac b).prod
          (((M.trans s (M.act b s)).toMeasure).prod (M.reward s (M.act b s))))
        = ∫⁻ x : ℝ, h x ∂(M.reward s (M.act b s)) := by
    intro b
    rw [Measure.dirac_prod, lintegral_map (by fun_prop) (by fun_prop)]
    rw [lintegral_prod _ (by fun_prop)]
    simp
  rw [stepLaw, lintegral_smul_measure, lintegral_add_measure, key true, key false]
  have hle : ∀ b : Bool, ∫⁻ x : ℝ, h x ∂(M.reward s (M.act b s)) ≤ rewardBound M h := by
    intro b
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun s' : S => ∑ a : Bool, ∫⁻ x : ℝ, h x ∂(M.reward s' a))
      (fun _ _ => bot_le) (Finset.mem_univ s))
    exact Finset.single_le_sum
      (f := fun a : Bool => ∫⁻ x : ℝ, h x ∂(M.reward s a))
      (fun _ _ => bot_le) (Finset.mem_univ (M.act b s))
  calc (2 : ℝ≥0∞)⁻¹ * (∫⁻ x : ℝ, h x ∂(M.reward s (M.act true s))
        + ∫⁻ x : ℝ, h x ∂(M.reward s (M.act false s)))
      ≤ (2 : ℝ≥0∞)⁻¹ * (rewardBound M h + rewardBound M h) :=
        mul_le_mul' le_rfl (add_le_add (hle true) (hle false))
    _ = rewardBound M h := by
        rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

variable [Countable S]

lemma lintegral_rwd_expKernel_le (M : Model S) (h : ℝ → ℝ≥0∞) (hh : Measurable h)
    (w : Step S) :
    ∫⁻ y, h y.2.2.2 ∂(expKernel M w) ≤ rewardBound M h := by
  rw [expKernel_apply, Measure.dirac_prod, lintegral_map (by fun_prop) (by fun_prop)]
  exact lintegral_rwd_stepLaw_le M h hh _

lemma lintegral_rwd_bind_le (M : Model S) (h : ℝ → ℝ≥0∞) (hh : Measurable h)
    (μ : Measure (Step S)) [IsProbabilityMeasure μ] :
    ∫⁻ y, h y.2.2.2 ∂(μ.bind (expKernel M)) ≤ rewardBound M h := by
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) (by fun_prop)]
  calc ∫⁻ w, (∫⁻ y, h y.2.2.2 ∂(expKernel M w)) ∂μ
      ≤ ∫⁻ _ : Step S, rewardBound M h ∂μ :=
        lintegral_mono fun w => lintegral_rwd_expKernel_le M h hh w
    _ = rewardBound M h := by simp

lemma lintegral_rwd_measure_le (M : Model S) (h : ℝ → ℝ≥0∞) (hh : Measurable h)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) :
    ∫⁻ y, h y.2.2.2 ∂ν ≤ rewardBound M h := by
  conv_lhs => rw [← hinv.def]
  exact lintegral_rwd_bind_le M h hh ν

lemma lintegral_rwd_iterKernel_le (M : Model S) (h : ℝ → ℝ≥0∞) (hh : Measurable h)
    (k : ℕ) (z : Step S) :
    ∫⁻ y, h y.2.2.2 ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z)
      ≤ rewardBound M h := by
  rw [MarkovChainCLT.iterKernel_succ, Kernel.comp_apply]
  exact lintegral_rwd_bind_le M h hh _

end Moments


section Integrability

variable [Fintype S] [Countable S]

lemma rewardBound_enorm_lt_top (M : Model S) (hL2 : M.RewardL2) :
    rewardBound M (fun x : ℝ => ‖x‖ₑ) < ⊤ := by
  refine ENNReal.sum_lt_top.2 fun s _ => ENNReal.sum_lt_top.2 fun a _ => ?_
  have hi : Integrable (fun x : ℝ => x) (M.reward s a) :=
    (hL2 s a).integrable (by norm_num)
  exact hi.hasFiniteIntegral

lemma rewardBound_enorm_sq_lt_top (M : Model S) (hL2 : M.RewardL2) :
    rewardBound M (fun x : ℝ => ‖x‖ₑ ^ 2) < ⊤ := by
  refine ENNReal.sum_lt_top.2 fun s _ => ENNReal.sum_lt_top.2 fun a _ => ?_
  have hi : Integrable (fun x : ℝ => x ^ 2) (M.reward s a) := (hL2 s a).integrable_sq
  have := hi.hasFiniteIntegral
  refine lt_of_le_of_lt (le_of_eq ?_) this
  refine lintegral_congr fun x => ?_
  rw [← enorm_pow]

lemma measurable_coordAt_estObs (M : Model S) (Γ : Scheme) (p : EstIdx S) :
    Measurable (fun z : Step S => coordAt (estObs M Γ z) p) := by
  have hw : Measurable (fun z : Step S => schemeWeight M Γ p.1 z) := by
    cases Γ with
    | AB =>
        simp only [schemeWeight]
        exact (Measurable.ite (measurable_snd (measurable_fst
          (measurableSet_singleton p.1))) measurable_const measurable_const).const_mul 2
    | IS =>
        simp only [schemeWeight]
        refine Measurable.ite (measurable_fst (measurableSet_singleton M.crucial)) ?_
          measurable_const
        exact (Measurable.ite (measurable_snd (measurable_fst
          (measurableSet_singleton p.1))) measurable_const measurable_const).const_mul 2
  obtain ⟨a, c⟩ := p
  cases c with
  | inl ij =>
      simp only [coordAt, estObs]
      refine hw.mul (Measurable.ite ?_ measurable_const measurable_const)
      have h1 : MeasurableSet {z : Step S | z.1 = ij.1} :=
        measurable_fst (measurableSet_singleton ij.1)
      have h2 : MeasurableSet {z : Step S | z.2.2.1 = ij.2} :=
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton ij.2)
      exact h1.inter h2
  | inr i =>
      simp only [coordAt, estObs]
      refine hw.mul (Measurable.ite ?_ ?_ measurable_const)
      · exact measurable_fst (measurableSet_singleton i)
      · exact measurable_snd.snd.snd

lemma abs_schemeWeight_le (M : Model S) (Γ : Scheme) (a : Bool) (z : Step S) :
    |schemeWeight M Γ a z| ≤ 2 := by
  cases Γ <;> simp only [schemeWeight] <;> split_ifs <;> norm_num

lemma abs_coordAt_estObs_le (M : Model S) (Γ : Scheme) (p : EstIdx S) (z : Step S) :
    |coordAt (estObs M Γ z) p| ≤ 2 + 2 * |z.2.2.2| := by
  have hw := abs_schemeWeight_le M Γ p.1 z
  have habs : (0:ℝ) ≤ |z.2.2.2| := abs_nonneg _
  obtain ⟨a, c⟩ := p
  cases c with
  | inl ij =>
      simp only [coordAt, estObs, abs_mul]
      have h1 : |(if (z.state = ij.1 ∧ z.next = ij.2) then (1:ℝ) else 0)| ≤ 1 := by
        split_ifs <;> norm_num
      calc |schemeWeight M Γ a z| * |(if (z.state = ij.1 ∧ z.next = ij.2) then (1:ℝ) else 0)|
          ≤ 2 * 1 := by
            exact mul_le_mul hw h1 (abs_nonneg _) (by norm_num)
        _ ≤ 2 + 2 * |z.2.2.2| := by nlinarith
  | inr i =>
      simp only [coordAt, estObs, abs_mul]
      have h1 : |(if z.state = i then z.rwd else 0)| ≤ |z.2.2.2| := by
        unfold Step.state Step.rwd
        split_ifs <;> simp
      calc |schemeWeight M Γ a z| * |(if z.state = i then z.rwd else 0)|
          ≤ 2 * |z.2.2.2| := by
            exact mul_le_mul hw h1 (abs_nonneg _) (by norm_num)
        _ ≤ 2 + 2 * |z.2.2.2| := by nlinarith

end Integrability


section Bounds

variable [Fintype S] [Countable S]

lemma integrable_rwd_of_lintegral_ne_top (μ : Measure (Step S))
    (hb : ∫⁻ y : Step S, ‖y.2.2.2‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun y : Step S => y.2.2.2) μ :=
  ⟨(measurable_snd.snd.snd).aestronglyMeasurable, by
    simpa [HasFiniteIntegral] using Ne.lt_top hb⟩

/-- Every estimator coordinate is dominated by `2 + 2|r|`, so a first-moment
bound on the reward controls it. -/
lemma integrable_coordAt_of_lintegral_ne_top (M : Model S) (Γ : Scheme) (q : EstIdx S)
    (μ : Measure (Step S)) [IsFiniteMeasure μ]
    (hb : ∫⁻ y : Step S, ‖y.2.2.2‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun y : Step S => coordAt (estObs M Γ y) q) μ := by
  have hr : Integrable (fun y : Step S => y.2.2.2) μ :=
    integrable_rwd_of_lintegral_ne_top μ hb
  have hg : Integrable (fun y : Step S => 2 + 2 * |y.2.2.2|) μ :=
    (integrable_const (2:ℝ)).add (hr.abs.const_mul 2)
  refine Integrable.mono' hg (measurable_coordAt_estObs M Γ q).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun y => abs_coordAt_estObs_le M Γ q y

lemma abs_integral_coordAt_le (M : Model S) (Γ : Scheme) (q : EstIdx S)
    (μ : Measure (Step S)) [IsProbabilityMeasure μ] (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hb : ∫⁻ y : Step S, ‖y.2.2.2‖ₑ ∂μ ≤ B) :
    |∫ y, coordAt (estObs M Γ y) q ∂μ| ≤ 2 + 2 * B.toReal := by
  have hbne : ∫⁻ y : Step S, ‖y.2.2.2‖ₑ ∂μ ≠ ⊤ := ne_top_of_le_ne_top hB hb
  have hr : Integrable (fun y : Step S => y.2.2.2) μ :=
    integrable_rwd_of_lintegral_ne_top μ hbne
  have hg : Integrable (fun y : Step S => 2 + 2 * |y.2.2.2|) μ :=
    (integrable_const (2:ℝ)).add (hr.abs.const_mul 2)
  have hf : Integrable (fun y : Step S => coordAt (estObs M Γ y) q) μ :=
    integrable_coordAt_of_lintegral_ne_top M Γ q μ hbne
  have h1 : |∫ y, coordAt (estObs M Γ y) q ∂μ| ≤ ∫ y, (2 + 2 * |y.2.2.2|) ∂μ := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine integral_mono hf.abs hg ?_
    intro y
    exact abs_coordAt_estObs_le M Γ q y
  have h2 : ∫ y : Step S, (2 + 2 * |y.2.2.2|) ∂μ = 2 + 2 * ∫ y : Step S, |y.2.2.2| ∂μ := by
    rw [integral_add (integrable_const _) (hr.abs.const_mul 2), integral_const,
      integral_const_mul]
    simp
  have h3 : ∫ y : Step S, |y.2.2.2| ∂μ ≤ B.toReal := by
    have heq : ∫ y : Step S, |y.2.2.2| ∂μ = (∫⁻ y : Step S, ‖y.2.2.2‖ₑ ∂μ).toReal := by
      have := integral_norm_eq_lintegral_enorm
        (f := fun y : Step S => y.2.2.2) (μ := μ) hr.aestronglyMeasurable
      simpa [Real.norm_eq_abs] using this
    rw [heq]
    exact ENNReal.toReal_mono hB hb
  have h4 := h1.trans_eq h2
  linarith [h3, h4]

end Bounds


section CovarianceIdentities

variable [Fintype S] [Countable S]

/-- Averaging over the arm flip does not change an integral. -/
lemma integral_flipAvg (M : Model S) (μ : Measure (Step S))
    (hμ : Measure.map (armFlip M) μ = μ)
    (F : Step S → ℝ) (hF : Measurable F) (hFint : Integrable F μ) :
    ∫ z, (F z + F (armFlip M z)) / 2 ∂μ = ∫ z, F z ∂μ := by
  have hint2 : Integrable (fun z => F (armFlip M z)) μ := by
    rw [← hμ] at hFint
    exact (integrable_map_measure hF.aestronglyMeasurable
      (measurable_armFlip M).aemeasurable).1 hFint
  rw [integral_div, integral_add hFint hint2,
    integral_comp_armFlip M μ hμ F hF]
  ring

/-- An integrand that is anti-invariant under the arm flip has integral zero. -/
lemma integral_eq_zero_of_flip_anti (M : Model S) (μ : Measure (Step S))
    (hμ : Measure.map (armFlip M) μ = μ)
    (H : Step S → ℝ) (hH : Measurable H)
    (hanti : ∀ z, H (armFlip M z) = - H z) :
    ∫ z, H z ∂μ = 0 := by
  have h1 : ∫ z, H (armFlip M z) ∂μ = ∫ z, H z ∂μ :=
    integral_comp_armFlip M μ hμ H hH
  have h2 : ∫ z, H (armFlip M z) ∂μ = - ∫ z, H z ∂μ := by
    simp only [hanti]
    exact integral_neg _
  linarith [h1, h2]

end CovarianceIdentities


section L2

variable [Fintype S] [Countable S]

lemma memLp_two_rwd (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hL2 : M.RewardL2) :
    MemLp (fun z : Step S => z.2.2.2) 2 ν := by
  refine (memLp_two_iff_integrable_sq
    (measurable_snd.snd.snd).aestronglyMeasurable).2 ?_
  refine ⟨((measurable_snd.snd.snd).pow_const 2).aestronglyMeasurable, ?_⟩
  have hb := lintegral_rwd_measure_le M (fun x : ℝ => ‖x‖ₑ ^ 2) (by fun_prop) ν hinv
  have hfin := rewardBound_enorm_sq_lt_top M hL2
  have : ∫⁻ z : Step S, ‖z.2.2.2 ^ 2‖ₑ ∂ν ≤ rewardBound M (fun x : ℝ => ‖x‖ₑ ^ 2) := by
    refine le_trans (le_of_eq ?_) hb
    exact lintegral_congr fun z => by simp only [← enorm_pow]
  simpa [HasFiniteIntegral] using lt_of_le_of_lt this hfin

lemma memLp_two_coordAt (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hL2 : M.RewardL2)
    (Γ : Scheme) (p : EstIdx S) :
    MemLp (fun z => coordAt (estObs M Γ z) p) 2 ν := by
  have hr : MemLp (fun z : Step S => z.2.2.2) 2 ν := memLp_two_rwd M ν hinv hL2
  have hg : MemLp (fun z : Step S => 2 + 2 * |z.2.2.2|) 2 ν :=
    (memLp_const (2:ℝ)).add (hr.abs.const_mul 2)
  refine MemLp.of_le hg (measurable_coordAt_estObs M Γ p).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have h := abs_coordAt_estObs_le M Γ p z
  have hpos : (0:ℝ) ≤ 2 + 2 * |z.2.2.2| := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hpos] using h

end L2


section FlipDiff

variable [Fintype S] [Countable S]

/-- The part of the A/B statistic that information sharing averages away. -/
noncomputable def flipDiff (M : Model S) (p : EstIdx S) (z : Step S) : ℝ :=
  (coordAt (estObs M Scheme.AB z) p - coordAt (estObs M Scheme.AB (armFlip M z)) p) / 2

lemma coordAt_AB_eq_IS_add_flipDiff (M : Model S) (p : EstIdx S) (z : Step S) :
    coordAt (estObs M Scheme.AB z) p
      = coordAt (estObs M Scheme.IS z) p + flipDiff M p z := by
  rw [coordAt_estObs_IS M p z, flipDiff]; ring

lemma flipDiff_armFlip (M : Model S) (p : EstIdx S) (z : Step S) :
    flipDiff M p (armFlip M z) = - flipDiff M p z := by
  rw [flipDiff, flipDiff, armFlip_involutive M z]; ring

lemma coordAt_IS_armFlip (M : Model S) (p : EstIdx S) (z : Step S) :
    coordAt (estObs M Scheme.IS (armFlip M z)) p = coordAt (estObs M Scheme.IS z) p := by
  rw [coordAt_estObs_IS M p (armFlip M z), coordAt_estObs_IS M p z, armFlip_involutive M z]
  ring

lemma flipDiff_eq_zero_of_crucial (M : Model S) (p : EstIdx S)
    (hp : idxState p = M.crucial) (z : Step S) : flipDiff M p z = 0 := by
  rw [flipDiff, coordAt_estObs_AB_crucial M p hp z]; ring

lemma measurable_flipDiff (M : Model S) (p : EstIdx S) : Measurable (flipDiff M p) := by
  unfold flipDiff
  exact ((measurable_coordAt_estObs M Scheme.AB p).sub
    ((measurable_coordAt_estObs M Scheme.AB p).comp (measurable_armFlip M))).div_const 2

lemma memLp_two_flipDiff (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hL2 : M.RewardL2) (p : EstIdx S) :
    MemLp (flipDiff M p) 2 ν := by
  have hfd : flipDiff M p
      = fun z => coordAt (estObs M Scheme.AB z) p - coordAt (estObs M Scheme.IS z) p := by
    funext z; rw [coordAt_AB_eq_IS_add_flipDiff M p z]; ring
  rw [hfd]
  exact (memLp_two_coordAt M ν hinv hL2 Scheme.AB p).sub
    (memLp_two_coordAt M ν hinv hL2 Scheme.IS p)

/-- **Same asymptotic bias.** -/
lemma integral_coordAt_IS_eq_AB (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hL2 : M.RewardL2) (p : EstIdx S) :
    ∫ z, coordAt (estObs M Scheme.IS z) p ∂ν
      = ∫ z, coordAt (estObs M Scheme.AB z) p ∂ν := by
  have hmap := map_armFlip_measure M ν hinv
  have hint : Integrable (fun z => coordAt (estObs M Scheme.AB z) p) ν :=
    (memLp_two_coordAt M ν hinv hL2 Scheme.AB p).integrable (by norm_num)
  calc ∫ z, coordAt (estObs M Scheme.IS z) p ∂ν
      = ∫ z, (coordAt (estObs M Scheme.AB z) p
          + coordAt (estObs M Scheme.AB (armFlip M z)) p) / 2 ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => coordAt_estObs_IS M p z)
    _ = ∫ z, coordAt (estObs M Scheme.AB z) p ∂ν :=
        integral_flipAvg M ν hmap _ (measurable_coordAt_estObs M Scheme.AB p) hint

/-- For lags `k ≥ 1` the conditional mean of the statistic does not see the scheme. -/
lemma integral_coordAt_iterKernel_IS_eq_AB (M : Model S) (hL2 : M.RewardL2)
    (q : EstIdx S) (k : ℕ) (z : Step S) :
    ∫ y, coordAt (estObs M Scheme.IS y) q
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z)
      = ∫ y, coordAt (estObs M Scheme.AB y) q
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z) := by
  have hmap : Measure.map (armFlip M) (MarkovChainCLT.iterKernel (expKernel M) (k + 1) z)
      = MarkovChainCLT.iterKernel (expKernel M) (k + 1) z := map_armFlip_iterKernel M k z
  have hbne : ∫⁻ y : Step S, ‖y.2.2.2‖ₑ
      ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z) ≠ ⊤ :=
    ne_top_of_le_ne_top (rewardBound_enorm_lt_top M hL2).ne
      (lintegral_rwd_iterKernel_le M (fun x : ℝ => ‖x‖ₑ) (by fun_prop) k z)
  have hint : Integrable (fun y => coordAt (estObs M Scheme.AB y) q)
      (MarkovChainCLT.iterKernel (expKernel M) (k + 1) z) :=
    integrable_coordAt_of_lintegral_ne_top M Scheme.AB q _ hbne
  calc ∫ y, coordAt (estObs M Scheme.IS y) q
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z)
      = ∫ y, (coordAt (estObs M Scheme.AB y) q
          + coordAt (estObs M Scheme.AB (armFlip M y)) q) / 2
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z) :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => coordAt_estObs_IS M q y)
    _ = ∫ y, coordAt (estObs M Scheme.AB y) q
        ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z) :=
        integral_flipAvg M _ hmap _ (measurable_coordAt_estObs M Scheme.AB q) hint

end FlipDiff


section LagCov

variable [Fintype S] [Countable S]

/-- **Information sharing does not touch the covariance across time.**  For every
lag `k ≥ 1` the lagged autocovariances of the two schemes coincide. -/
lemma lagCovariance_succ_AB_eq_IS (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hL2 : M.RewardL2) (p q : EstIdx S) (k : ℕ) :
    MarkovChainCLT.lagCovariance (expKernel M) ν
        (fun z => coordAt (estObs M Scheme.AB z) p)
        (fun z => coordAt (estObs M Scheme.AB z) q) (k + 1)
      = MarkovChainCLT.lagCovariance (expKernel M) ν
        (fun z => coordAt (estObs M Scheme.IS z) p)
        (fun z => coordAt (estObs M Scheme.IS z) q) (k + 1) := by
  classical
  have hmap := map_armFlip_measure M ν hinv
  have hBne : rewardBound M (fun x : ℝ => ‖x‖ₑ) ≠ ⊤ := (rewardBound_enorm_lt_top M hL2).ne
  set G : Step S → ℝ := fun z =>
    ∫ y, coordAt (estObs M Scheme.AB y) q
      ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z) with hGdef
  have hGapp : ∀ z, (∫ y, coordAt (estObs M Scheme.AB y) q
      ∂(MarkovChainCLT.iterKernel (expKernel M) (k + 1) z)) = G z := fun _ => rfl
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel
      (κ := MarkovChainCLT.iterKernel (expKernel M) (k + 1))
      (measurable_coordAt_estObs M Scheme.AB q).stronglyMeasurable).measurable
  have hGflip : ∀ z, G (armFlip M z) = G z := by
    intro z; simp only [hGdef]; rw [iterKernel_armFlip M k z]
  have hGbdd : ∀ z, |G z| ≤ 2 + 2 * (rewardBound M (fun x : ℝ => ‖x‖ₑ)).toReal := fun z =>
    abs_integral_coordAt_le M Scheme.AB q _ _ hBne
      (lintegral_rwd_iterKernel_le M (fun x : ℝ => ‖x‖ₑ) (by fun_prop) k z)
  set mp := ∫ z, coordAt (estObs M Scheme.AB z) p ∂ν with hmp
  set mq := ∫ z, coordAt (estObs M Scheme.AB z) q ∂ν with hmq
  set H : Step S → ℝ := fun z => (coordAt (estObs M Scheme.AB z) p - mp) * (G z - mq) with hH
  have hHmeas : Measurable H :=
    ((measurable_coordAt_estObs M Scheme.AB p).sub measurable_const).mul
      (hGmeas.sub measurable_const)
  have hHint : Integrable H ν := by
    refine Integrable.mul_bdd
      (((memLp_two_coordAt M ν hinv hL2 Scheme.AB p).integrable
        (by norm_num)).sub (integrable_const mp))
      (hGmeas.sub measurable_const).aestronglyMeasurable
      (c := 2 + 2 * (rewardBound M (fun x : ℝ => ‖x‖ₑ)).toReal + |mq|) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have := hGbdd z
    have h2 : ‖G z - mq‖ = |G z - mq| := Real.norm_eq_abs _
    rw [h2]
    calc |G z - mq| ≤ |G z| + |mq| := abs_sub _ _
      _ ≤ _ := by linarith
  have hIS : MarkovChainCLT.lagCovariance (expKernel M) ν
      (fun z => coordAt (estObs M Scheme.IS z) p)
      (fun z => coordAt (estObs M Scheme.IS z) q) (k + 1)
      = ∫ z, (H z + H (armFlip M z)) / 2 ∂ν := by
    unfold MarkovChainCLT.lagCovariance
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [integral_coordAt_IS_eq_AB M ν hinv hL2 p, integral_coordAt_IS_eq_AB M ν hinv hL2 q,
      integral_coordAt_iterKernel_IS_eq_AB M hL2 q k z, hGapp z, coordAt_estObs_IS M p z]
    simp only [hH, hGflip z]
    ring
  rw [hIS, integral_flipAvg M ν hmap H hHmeas hHint]
  unfold MarkovChainCLT.lagCovariance
  rfl

lemma lagCovariance_zero_eq {X : Type*} [MeasurableSpace X] (P : Kernel X X) (π : Measure X)
    (f g : X → ℝ) (hg : Measurable g) :
    MarkovChainCLT.lagCovariance P π f g 0
      = ∫ x, (f x - ∫ y, f y ∂π) * (g x - ∫ y, g y ∂π) ∂π := by
  unfold MarkovChainCLT.lagCovariance
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hd : ∫ y, g y ∂((MarkovChainCLT.iterKernel P 0) x) = g x := by
    rw [MarkovChainCLT.iterKernel_zero, Kernel.id_apply]
    exact integral_dirac' _ x hg.stronglyMeasurable
  rw [hd]

end LagCov


section InstCov

variable [Fintype S] [Countable S]

/-- **The instantaneous variance drops by exactly the Gram matrix of the flip
difference.**  This is the conditional-variance (Rao-Blackwell) decomposition. -/
lemma lagCovariance_zero_sub_eq (M : Model S) (ν : Measure (Step S))
    [IsProbabilityMeasure ν] (hinv : Kernel.Invariant (expKernel M) ν)
    (hL2 : M.RewardL2) (p q : EstIdx S) :
    MarkovChainCLT.lagCovariance (expKernel M) ν
        (fun z => coordAt (estObs M Scheme.AB z) p)
        (fun z => coordAt (estObs M Scheme.AB z) q) 0
      - MarkovChainCLT.lagCovariance (expKernel M) ν
        (fun z => coordAt (estObs M Scheme.IS z) p)
        (fun z => coordAt (estObs M Scheme.IS z) q) 0
      = ∫ z, flipDiff M p z * flipDiff M q z ∂ν := by
  classical
  have hmap := map_armFlip_measure M ν hinv
  rw [lagCovariance_zero_eq _ _ _ _ (measurable_coordAt_estObs M Scheme.AB q),
    lagCovariance_zero_eq _ _ _ _ (measurable_coordAt_estObs M Scheme.IS q),
    integral_coordAt_IS_eq_AB M ν hinv hL2 p, integral_coordAt_IS_eq_AB M ν hinv hL2 q]
  set mp := ∫ z, coordAt (estObs M Scheme.AB z) p ∂ν with hmpdef
  set mq := ∫ z, coordAt (estObs M Scheme.AB z) q ∂ν with hmqdef
  have hLp : MemLp (fun z => coordAt (estObs M Scheme.IS z) p - mp) 2 ν :=
    (memLp_two_coordAt M ν hinv hL2 Scheme.IS p).sub (memLp_const mp)
  have hLq : MemLp (fun z => coordAt (estObs M Scheme.IS z) q - mq) 2 ν :=
    (memLp_two_coordAt M ν hinv hL2 Scheme.IS q).sub (memLp_const mq)
  have hdp : MemLp (flipDiff M p) 2 ν := memLp_two_flipDiff M ν hinv hL2 p
  have hdq : MemLp (flipDiff M q) 2 ν := memLp_two_flipDiff M ν hinv hL2 q
  have I1 : Integrable (fun z => (coordAt (estObs M Scheme.IS z) p - mp)
      * (coordAt (estObs M Scheme.IS z) q - mq)) ν := hLp.integrable_mul hLq
  have I2 : Integrable (fun z => (coordAt (estObs M Scheme.IS z) p - mp)
      * flipDiff M q z) ν := hLp.integrable_mul hdq
  have I3 : Integrable (fun z => flipDiff M p z
      * (coordAt (estObs M Scheme.IS z) q - mq)) ν := hdp.integrable_mul hLq
  have I4 : Integrable (fun z => flipDiff M p z * flipDiff M q z) ν := hdp.integrable_mul hdq
  have hZ2 : ∫ z, (coordAt (estObs M Scheme.IS z) p - mp) * flipDiff M q z ∂ν = 0 := by
    refine integral_eq_zero_of_flip_anti M ν hmap _
      (((measurable_coordAt_estObs M Scheme.IS p).sub measurable_const).mul
        (measurable_flipDiff M q)) ?_
    intro z
    rw [coordAt_IS_armFlip M p z, flipDiff_armFlip M q z]; ring
  have hZ3 : ∫ z, flipDiff M p z * (coordAt (estObs M Scheme.IS z) q - mq) ∂ν = 0 := by
    refine integral_eq_zero_of_flip_anti M ν hmap _
      ((measurable_flipDiff M p).mul
        ((measurable_coordAt_estObs M Scheme.IS q).sub measurable_const)) ?_
    intro z
    rw [coordAt_IS_armFlip M q z, flipDiff_armFlip M p z]; ring
  have hsplit : ∀ z, (coordAt (estObs M Scheme.AB z) p - mp)
        * (coordAt (estObs M Scheme.AB z) q - mq)
      = (coordAt (estObs M Scheme.IS z) p - mp) * (coordAt (estObs M Scheme.IS z) q - mq)
        + ((coordAt (estObs M Scheme.IS z) p - mp) * flipDiff M q z
          + (flipDiff M p z * (coordAt (estObs M Scheme.IS z) q - mq)
            + flipDiff M p z * flipDiff M q z)) := by
    intro z
    rw [coordAt_AB_eq_IS_add_flipDiff M p z, coordAt_AB_eq_IS_add_flipDiff M q z]
    ring
  have I34 := I3.fun_add I4
  have I234 := I2.fun_add I34
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add I1 I234, integral_add I2 I34, integral_add I3 I4, hZ2, hZ3]
  ring

/-- The Gram matrix of the flip differences: positive semidefinite, and zero on
every row and column attached to the crucial state. -/
lemma posSemidef_flipGram (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν) (hL2 : M.RewardL2) :
    Matrix.PosSemidef
      (Matrix.of fun p q : EstIdx S => ∫ z, flipDiff M p z * flipDiff M q z ∂ν) := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext fun p q => ?_
    simp only [Matrix.of_apply, star_trivial]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  · intro x
    have hint : ∀ p q : EstIdx S, Integrable
        (fun z => x p * flipDiff M p z * (x q * flipDiff M q z)) ν := by
      intro p q
      have := ((memLp_two_flipDiff M ν hinv hL2 p).const_mul (x p)).integrable_mul
        ((memLp_two_flipDiff M ν hinv hL2 q).const_mul (x q))
      exact this
    have hstep : (star x) ⬝ᵥ ((Matrix.of fun p q : EstIdx S =>
        ∫ z, flipDiff M p z * flipDiff M q z ∂ν) *ᵥ x)
        = ∫ z, (∑ p : EstIdx S, x p * flipDiff M p z) ^ 2 ∂ν := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
      have h1 : ∀ p : EstIdx S,
          x p * ∑ q : EstIdx S, (∫ z, flipDiff M p z * flipDiff M q z ∂ν) * x q
            = ∫ z, ∑ q : EstIdx S, x p * flipDiff M p z * (x q * flipDiff M q z) ∂ν := by
        intro p
        rw [integral_finset_sum _ (fun q _ => hint p q), Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        have hre : ∀ z : Step S, x p * flipDiff M p z * (x q * flipDiff M q z)
            = (x p * x q) * (flipDiff M p z * flipDiff M q z) := fun z => by ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hre), integral_const_mul]
        ring
      rw [Finset.sum_congr rfl (fun p _ => h1 p),
        ← integral_finset_sum _ (fun p _ => integrable_finset_sum _ (fun q _ => hint p q))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [sq, Finset.sum_mul_sum]
    rw [hstep]
    exact integral_nonneg fun z => sq_nonneg _

end InstCov


section Conjuncts

variable [Fintype S] [Countable S]
variable (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
  (hinv : Kernel.Invariant (expKernel M) ν) (hL2 : M.RewardL2)

include hinv hL2 in
/-- **(1) Same asymptotic bias.** -/
lemma meanObs_AB_eq_IS : meanObs M Scheme.AB ν = meanObs M Scheme.IS ν := by
  funext a
  refine Prod.ext ?_ ?_
  · funext i j
    exact (integral_coordAt_IS_eq_AB M ν hinv hL2 (a, Sum.inl (i, j))).symm
  · funext i
    exact (integral_coordAt_IS_eq_AB M ν hinv hL2 (a, Sum.inr i)).symm

include hinv hL2 in
/-- **(3) The covariance across time is untouched.** -/
lemma lagCovMatrix_AB_eq_IS : lagCovMatrix M Scheme.AB ν = lagCovMatrix M Scheme.IS ν := by
  ext p q
  simp only [lagCovMatrix, Matrix.of_apply]
  congr 1
  · exact tsum_congr fun k => lagCovariance_succ_AB_eq_IS M ν hinv hL2 p q k
  · exact tsum_congr fun k => lagCovariance_succ_AB_eq_IS M ν hinv hL2 q p k

include hinv hL2 in
lemma instCovMatrix_sub_eq_flipGram :
    instCovMatrix M Scheme.AB ν - instCovMatrix M Scheme.IS ν
      = Matrix.of fun p q : EstIdx S => ∫ z, flipDiff M p z * flipDiff M q z ∂ν := by
  ext p q
  simp only [Matrix.sub_apply, instCovMatrix, Matrix.of_apply]
  exact lagCovariance_zero_sub_eq M ν hinv hL2 p q

include hinv hL2 in
/-- **(4) The variance at the treated state cannot be reduced.** -/
lemma instCovMatrix_eq_at_crucial (p q : EstIdx S)
    (hpq : idxState p = M.crucial ∨ idxState q = M.crucial) :
    instCovMatrix M Scheme.AB ν p q = instCovMatrix M Scheme.IS ν p q := by
  have hd : ∫ z, flipDiff M p z * flipDiff M q z ∂ν = 0 := by
    rcases hpq with h | h
    · have : ∀ z, flipDiff M p z * flipDiff M q z = 0 := fun z => by
        rw [flipDiff_eq_zero_of_crucial M p h z]; ring
      simp [this]
    · have : ∀ z, flipDiff M p z * flipDiff M q z = 0 := fun z => by
        rw [flipDiff_eq_zero_of_crucial M q h z]; ring
      simp [this]
  have := congrFun (congrFun (instCovMatrix_sub_eq_flipGram M ν hinv hL2) p) q
  simp only [Matrix.sub_apply, Matrix.of_apply] at this
  rw [hd] at this
  linarith [this]

include hinv hL2 in
/-- **(5) Information sharing reduces the instantaneous variance.** -/
lemma posSemidef_instCovMatrix_sub :
    Matrix.PosSemidef (instCovMatrix M Scheme.AB ν - instCovMatrix M Scheme.IS ν) := by
  rw [instCovMatrix_sub_eq_flipGram M ν hinv hL2]
  exact posSemidef_flipGram M ν hinv hL2

include hinv hL2 in
/-- **(6) The full asymptotic covariance drops in the Loewner order.** -/
lemma posSemidef_asymCovMatrix_sub :
    Matrix.PosSemidef (asymCovMatrix M Scheme.AB ν - asymCovMatrix M Scheme.IS ν) := by
  have hlag := lagCovMatrix_AB_eq_IS M ν hinv hL2
  have : asymCovMatrix M Scheme.AB ν - asymCovMatrix M Scheme.IS ν
      = instCovMatrix M Scheme.AB ν - instCovMatrix M Scheme.IS ν := by
    simp only [asymCovMatrix, hlag]
    abel
  rw [this]
  exact posSemidef_instCovMatrix_sub M ν hinv hL2

end Conjuncts


section Flatten

variable [Fintype S]

/-- The estimator input space is just the space of functions on the flat index
set; this is the isomorphism, as a continuous linear map. -/
noncomputable def unflattenₗ : (EstIdx S → ℝ) →ₗ[ℝ] EstInput S where
  toFun v := fun a => (fun i j => v (a, Sum.inl (i, j)), fun i => v (a, Sum.inr i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S :=
  LinearMap.toContinuousLinearMap (unflattenₗ (S := S))

@[simp] lemma unflattenL_apply (v : EstIdx S → ℝ) (a : Bool) :
    (unflattenL v) a = (fun i j => v (a, Sum.inl (i, j)), fun i => v (a, Sum.inr i)) := rfl

lemma unflattenL_coordAt (w : EstInput S) :
    unflattenL (fun p => coordAt w p) = w := by
  funext a
  exact Prod.ext rfl rfl

lemma coordAt_unflattenL (v : EstIdx S → ℝ) (p : EstIdx S) :
    coordAt (unflattenL v) p = v p := by
  obtain ⟨a, c⟩ := p
  cases c <;> rfl

end Flatten

section Harris

lemma tvDist_nonneg {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ MarkovChainCLT.tvDist μ ν := by
  refine le_csSup ⟨1, ?_⟩ ⟨∅, MeasurableSet.empty, by simp⟩
  rintro r ⟨A, hA, rfl⟩
  have hμ : (μ A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by norm_num) (prob_le_one (μ := μ) (s := A))
  have hν : (ν A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by norm_num) (prob_le_one (μ := ν) (s := A))
  have hμ0 : (0:ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hν0 : (0:ℝ) ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- Uniform ergodicity of an invariant measure gives Harris ergodicity. -/
lemma harrisErgodic_of_uniformlyErgodic {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : MarkovChainCLT.UniformlyErgodic P π) :
    MarkovChainCLT.HarrisErgodic P π := by
  obtain ⟨R, t, hR, ht0, ht1, hrate⟩ := huni
  refine ⟨hinv, fun x => ?_⟩
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => tvDist_nonneg _ _)
    (Filter.eventually_atTop.2 ⟨1, fun n hn => hrate x n hn⟩) ?_
  have : Filter.Tendsto (fun n : ℕ => t ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1
  simpa using this.const_mul R

end Harris

end TreatmentLocality

open TreatmentLocality in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (huni : MarkovChainCLT.UniformlyErgodic (expKernel M) ν)
    (hL2 : M.RewardL2)
    (f : EstInput S → ℝ) (hfm : Measurable f) (f' : EstInput S →L[ℝ] ℝ)
    (hf : HasFDerivAt f f' (meanObs M .AB ν)) :
    meanObs M .AB ν = meanObs M .IS ν
    ∧ (∀ Γ : Scheme, TendstoInDistribution
        (fun (T : ℕ) (ω : ℕ → Step S) =>
          Real.sqrt T * (f (empAvg M Γ T ω) - f (meanObs M .AB ν)))
        atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure (expKernel M) ν)
        (gaussianReal 0
          (MarkovChainCLT.asymptoticVariance (expKernel M) ν
            (fun z => f' (estObs M Γ z))).toNNReal))
    ∧ lagCovMatrix M .AB ν = lagCovMatrix M .IS ν
    ∧ (∀ p q : EstIdx S, idxState p = M.crucial ∨ idxState q = M.crucial →
        instCovMatrix M .AB ν p q = instCovMatrix M .IS ν p q)
    ∧ Matrix.PosSemidef (instCovMatrix M .AB ν - instCovMatrix M .IS ν)
    ∧ Matrix.PosSemidef (asymCovMatrix M .AB ν - asymCovMatrix M .IS ν) := by
  have hmean := meanObs_AB_eq_IS M ν hinv hL2
  have hharris := harrisErgodic_of_uniformlyErgodic (expKernel M) ν hinv huni
  refine ⟨hmean, ?_, lagCovMatrix_AB_eq_IS M ν hinv hL2,
    fun p q hpq => instCovMatrix_eq_at_crucial M ν hinv hL2 p q hpq,
    posSemidef_instCovMatrix_sub M ν hinv hL2,
    posSemidef_asymCovMatrix_sub M ν hinv hL2⟩
  intro Γ
  -- the estimator, read through the flat coordinates
  have hbase : unflattenL (fun p => ∫ z, coordAt (estObs M Γ z) p ∂ν) = meanObs M Γ ν := rfl
  have hfd : HasFDerivAt (f ∘ (unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S))
      (f'.comp unflattenL) (fun p => ∫ z, coordAt (estObs M Γ z) p ∂ν) := by
    refine HasFDerivAt.comp _ ?_ (unflattenL.hasFDerivAt)
    rw [hbase]
    cases Γ with
    | AB => exact hf
    | IS => rw [← hmean]; exact hf
  have hgm : Measurable (f ∘ (unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S)) :=
    hfm.comp (unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S).continuous.measurable
  have hdelta := MarkovChainCLT.delta_method_of_uniformly_ergodic_of_measurable
    (expKernel M) ν hharris huni
    (fun z p => coordAt (estObs M Γ z) p)
    (fun p => measurable_coordAt_estObs M Γ p)
    (fun p => memLp_two_coordAt M ν hinv hL2 Γ p)
    (f ∘ (unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S)) hgm (f'.comp unflattenL) hfd
  have hvar : (fun z => (f'.comp unflattenL) (fun p => coordAt (estObs M Γ z) p))
      = fun z => f' (estObs M Γ z) := by
    funext z
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [unflattenL_coordAt]
  have hemp : ∀ (T : ℕ) (ω : ℕ → Step S),
      (f ∘ (unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S))
        (fun p => MarkovChainCLT.sampleAvg (fun z => coordAt (estObs M Γ z) p) T ω)
        = f (empAvg M Γ T ω) := fun _ _ => rfl
  have hlim : (f ∘ (unflattenL : (EstIdx S → ℝ) →L[ℝ] EstInput S))
      (fun p => ∫ z, coordAt (estObs M Γ z) p ∂ν) = f (meanObs M .AB ν) := by
    simp only [Function.comp_apply, hbase]
    cases Γ with
    | AB => rfl
    | IS => rw [← hmean]
  rw [hvar] at hdelta
  simpa only [hemp, hlim] using hdelta
