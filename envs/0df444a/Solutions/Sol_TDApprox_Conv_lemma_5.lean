-- Prove2me | solution 1 for TDApprox.Conv.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T17:25:05.515854+00:00
-- url     : https://prove2.me/submissions/27ba78cd-4a5a-4e53-96b1-65b36e32cd71

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Finset Function Preorder
open TDApprox.Conv
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace MarkovTrajectory
lemma map_left_compProd {H S : Type*} [MeasurableSpace H] [MeasurableSpace S]
    (ν : Measure H) [IsProbabilityMeasure ν] (P : Kernel S S) [IsMarkovKernel P]
    (f : H → S) (hf : Measurable f) :
    (ν ⊗ₘ P.comap f hf).map (fun x => (f x.1, x.2)) = ν.map f ⊗ₘ P := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl
lemma pair_law {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) [IsProbabilityMeasure ν] (t : ℕ) :
    (pathLawFrom P ν).map (fun ω => (ω t, ω (t+1))) =
      (pathLawFrom P ν).map (fun ω => ω t) ⊗ₘ P := by
  let h : (Π _ : Iic t, S) → S := fun x => x ⟨t, mem_Iic.mpr le_rfl⟩
  have hh : Measurable h := measurable_pi_apply _
  have hp := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => S) (μ₀ := ν) (κ := stepKernel P) (a := t)
  change (pathLawFrom P ν).map (frestrictLe t) ⊗ₘ stepKernel P t =
    (pathLawFrom P ν).map (fun ω => (frestrictLe t ω, ω (t+1))) at hp
  let : IsProbabilityMeasure ((pathLawFrom P ν).map (frestrictLe t)) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe t).aemeasurable
  have he := congrArg (fun μ : Measure ((Π _ : Iic t, S) × S) =>
    μ.map (fun x => (h x.1, x.2))) hp
  rw [show stepKernel P t = P.comap h hh from rfl, map_left_compProd,
    Measure.map_map hh (measurable_frestrictLe t),
    Measure.map_map (by fun_prop)
      (by fun_prop)] at he
  exact he.symm
lemma successor_law {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) [IsProbabilityMeasure ν] (t : ℕ) :
    (pathLawFrom P ν).map (fun ω => ω (t+1)) =
      P ∘ₘ (pathLawFrom P ν).map (fun ω => ω t) := by
  have h := congrArg (fun μ : Measure (S × S) => μ.map Prod.snd) (pair_law P ν t)
  rw [Measure.map_map measurable_snd
    (by fun_prop)] at h
  let : IsProbabilityMeasure ((pathLawFrom P ν).map (fun ω => ω t)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply t).aemeasurable
  change (pathLawFrom P ν).map (fun ω => ω (t+1)) =
    ((pathLawFrom P ν).map (fun ω => ω t) ⊗ₘ P).snd at h
  simpa only [Measure.snd_compProd] using h
lemma initial_law {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) :
    (pathLawFrom P ν).map (fun ω => ω 0) = ν := by
  calc
    _ = ((pathLawFrom P ν).map (frestrictLe 0)).map
        (fun x : Π _ : Iic 0, S => x ⟨0, mem_Iic.mpr le_rfl⟩) :=
      (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = ν := by
      rw [pathLawFrom, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      convert Measure.map_id (μ := ν) using 1
      congr 1

lemma marginal_law {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) [IsProbabilityMeasure ν] (t : ℕ) :
    (pathLawFrom P ν).map (fun ω => ω t) = (P ^ t) ∘ₘ ν := by
  induction t with
  | zero =>
    change (pathLawFrom P ν).map (fun ω => ω 0) = Kernel.id ∘ₘ ν
    rw [Measure.id_comp]; exact initial_law P ν
  | succ t ih =>
    rw [successor_law, ih, Measure.comp_assoc, pow_succ']
    rfl

lemma stationary_marginal {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (hinv : P.Invariant π) (t : ℕ) :
    (pathLawFrom P π).map (fun ω => ω t) = π := by
  induction t with
  | zero => exact initial_law P π
  | succ t ih => rw [successor_law, ih]; exact hinv

lemma stationary_pair {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (hinv : P.Invariant π) (t : ℕ) :
    (pathLawFrom P π).map (fun ω => (ω t, ω (t+1))) = π ⊗ₘ P := by
  rw [pair_law, stationary_marginal P π hinv]

noncomputable def pathKernel {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) (stepKernel P) 0).comap
    (MeasurableEquiv.piUnique (fun _ : Iic 0 => S)).symm (by fun_prop)

instance pathKernel_markov {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] : IsMarkovKernel (pathKernel P) := by
  unfold pathKernel; infer_instance

lemma pathLawFrom_eq_comp {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (ν : Measure S) :
    pathLawFrom P ν = pathKernel P ∘ₘ ν := by
  ext s hs
  rw [pathLawFrom, Kernel.trajMeasure,
    Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (by fun_prop)]
  rfl

lemma pathKernel_apply {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (i : S) :
    pathKernel P i = pathLaw P i := by
  rw [pathLaw, pathLawFrom_eq_comp]
  exact (Measure.dirac_bind (pathKernel P).measurable i).symm

lemma integrable_each_path {S : Type*} [MeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S)
    (hpos : ∀ i, π {i} ≠ 0) (F : (ℕ → S) → ℝ)
    (hF : Integrable F (pathLawFrom P π)) :
    ∀ i, Integrable F (pathLaw P i) := by
  rw [pathLawFrom_eq_comp] at hF
  have h := Measure.ae_integrable_of_integrable_comp hF
  intro i
  rw [← pathKernel_apply]
  exact (ae_iff_of_countable.mp h) i (hpos i)

lemma stationary_cost_memLp {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (hinv : P.Invariant π) (g : S → S → ℝ) (hg : Assumption1b P π g) (t : ℕ) :
    MemLp (fun ω : ℕ → S => g (ω t) (ω (t+1))) 2 (pathLawFrom P π) := by
  have hgm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
  have hsq : Integrable (fun x : S × S => (g x.1 x.2)^2)
      ((pathLawFrom P π).map (fun ω => (ω t, ω (t+1)))) := by
    rw [stationary_pair P π hinv]; exact hg
  have hsq' := hsq.comp_measurable (by fun_prop : Measurable (fun ω : ℕ → S => (ω t, ω (t+1))))
  have hm : Measurable (fun ω : ℕ → S => g (ω t) (ω (t+1))) :=
    hgm.comp (by fun_prop : Measurable (fun ω : ℕ → S => (ω t, ω (t+1))))
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  exact hsq'

lemma lintegral_each_path_lt_top {S : Type*} [MeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S)
    (hpos : ∀ i, π {i} ≠ 0) (F : (ℕ → S) → ℝ≥0∞) (hF : Measurable F)
    (hfin : ∫⁻ ω, F ω ∂pathLawFrom P π < ⊤) :
    ∀ i, ∫⁻ ω, F ω ∂pathLaw P i < ⊤ := by
  rw [pathLawFrom_eq_comp, Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable] at hfin
  have hae := ae_lt_top' (hF.lintegral_kernel (κ := pathKernel P)).aemeasurable hfin.ne
  intro i
  rw [← pathKernel_apply]
  exact (ae_iff_of_countable.mp hae) i (hpos i)

lemma absolute_discounted_finite {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    Assumption1c P g α := by
  let C := ∫⁻ x : S × S, ENNReal.ofReal |g x.1 x.2| ∂(π ⊗ₘ P)
  have hm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
  have hg : MemLp (fun x : S × S => g x.1 x.2) 2 (π ⊗ₘ P) :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr h1b
  have hC : C < ⊤ := by
    simpa [C, hasFiniteIntegral_iff_enorm, Real.enorm_eq_ofReal_abs] using
      (hg.integrable (by norm_num)).hasFiniteIntegral
  have each (t : ℕ) :
      (∫⁻ ω, ENNReal.ofReal (α ^ t * |g (ω t) (ω (t+1))|) ∂pathLawFrom P π) =
      (ENNReal.ofReal α)^t * C := by
    simp_rw [ENNReal.ofReal_mul (pow_nonneg hα0.le t), ENNReal.ofReal_pow hα0.le]
    have hmω : Measurable (fun ω : ℕ → S => ENNReal.ofReal |g (ω t) (ω (t+1))|) :=
      (hm.comp (by fun_prop : Measurable (fun ω : ℕ → S => (ω t, ω (t+1))))).abs.ennreal_ofReal
    rw [lintegral_const_mul _ hmω]
    congr 1
    calc
      _ = ∫⁻ x : S × S, ENNReal.ofReal |g x.1 x.2|
          ∂((pathLawFrom P π).map (fun ω => (ω t, ω (t+1)))) :=
        (lintegral_map hm.abs.ennreal_ofReal (by fun_prop)).symm
      _ = C := by rw [stationary_pair P π h1a.invariant]
  have hmeas (t : ℕ) : Measurable (fun ω : ℕ → S =>
      ENNReal.ofReal (α ^ t * |g (ω t) (ω (t+1))|)) := by
    exact (((hm.comp (by fun_prop : Measurable (fun ω : ℕ → S => (ω t, ω (t+1))))).abs).const_mul _).ennreal_ofReal
  apply lintegral_each_path_lt_top P π (fun i => (h1a.pos i).ne') _
    (Measurable.tsum hmeas)
  rw [lintegral_tsum (fun t => (hmeas t).aemeasurable)]
  simp_rw [each]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr (by simpa using hα1)) hC

lemma cost_integrable {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    ∀ i t, Integrable (fun ω : ℕ → S => g (ω t) (ω (t+1))) (pathLaw P i) := by
  intro i t
  exact integrable_each_path P π (fun i => (h1a.pos i).ne') _
    ((stationary_cost_memLp P π h1a.invariant g h1b t).integrable (by norm_num)) i

lemma path_marginal {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (i : S) (t : ℕ) :
    (pathLaw P i).map (fun ω => ω t) = (P ^ t) i := by
  rw [pathLaw, marginal_law]
  exact Measure.dirac_bind (P ^ t).measurable i

lemma path_pair {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (i : S) (t : ℕ) :
    (pathLaw P i).map (fun ω => (ω t, ω (t+1))) = (P ^ t) i ⊗ₘ P := by
  change (pathLawFrom P (Measure.dirac i)).map _ = _
  rw [pair_law]
  change (pathLaw P i).map _ ⊗ₘ P = _
  rw [path_marginal]

lemma pow_markov {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (t : ℕ) : IsMarkovKernel (P ^ t) := by
  induction t with
  | zero => change IsMarkovKernel (Kernel.id : Kernel S S); infer_instance
  | succ t ih =>
    let := ih
    rw [pow_succ']
    change IsMarkovKernel (P ∘ₖ (P ^ t))
    infer_instance

lemma expected_cost {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (h1a : Assumption1a P π) (h1b : Assumption1b P π g) (i : S) (t : ℕ) :
    (∫ ω, g (ω t) (ω (t+1)) ∂pathLaw P i) = ∫ j, gbar P g j ∂((P ^ t) i) := by
  have hm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
  have hi : Integrable (fun x : S × S => g x.1 x.2)
      ((pathLaw P i).map (fun ω => (ω t, ω (t+1)))) := by
    exact (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).mpr
      (cost_integrable P π g h1a h1b i t)
  have he := integral_map (by fun_prop : AEMeasurable (fun ω : ℕ → S => (ω t, ω (t+1)))
    (pathLaw P i)) hm.aestronglyMeasurable
  rw [path_pair] at hi he
  let := pow_markov P t
  rw [Measure.integral_compProd hi] at he
  exact he.symm

lemma discounted_series {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1a : Assumption1a P π) (h1b : Assumption1b P π g) (i : S) :
    HasSum (fun t : ℕ => α ^ t * ∫ j, gbar P g j ∂((P ^ t) i)) (Jstar P g α i) := by
  let F : ℕ → (ℕ → S) → ℝ := fun t ω => α ^ t * g (ω t) (ω (t+1))
  have hi (t : ℕ) : Integrable (F t) (pathLaw P i) :=
    (cost_integrable P π g h1a h1b i t).const_mul _
  have hn : ∑' t, ∫⁻ ω, ‖F t ω‖ₑ ∂pathLaw P i < ⊤ := by
    have h := absolute_discounted_finite P π g α hα0 hα1 h1a h1b i
    rw [lintegral_tsum] at h
    · simpa only [F, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (pow_nonneg hα0.le _)] using h
    · intro t
      have hm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
      exact (((hm.comp (by fun_prop : Measurable (fun ω : ℕ → S => (ω t, ω (t+1))))).abs).const_mul _).ennreal_ofReal.aemeasurable
  have hs : Summable (fun t => ∫ ω, ‖F t ω‖ ∂pathLaw P i) := by
    simpa only [integral_norm_eq_lintegral_enorm (hi _).aestronglyMeasurable] using
      (ENNReal.summable_toReal hn.ne)
  have h := hasSum_integral_of_summable_integral_norm hi hs
  simpa only [F, integral_const_mul, expected_cost P π g h1a h1b, Jstar] using h

lemma memLp_series {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (hF : ∀ t, MemLp (F t) 2 μ)
    (hs : ∑' t, eLpNorm (F t) 2 μ ≠ ⊤) :
    MemLp (fun ω => ∑' t, F t ω) 2 μ := by
  let f : ℕ → Lp ℝ 2 μ := fun t => (hF t).toLp (F t)
  have hf : ∑' t, ‖f t‖ₑ ≠ ⊤ := by simpa [f, Lp.enorm_toLp] using hs
  apply (Lp.memLp (∑' t, f t)).ae_eq
  filter_upwards [Lp.coeFn_tsum hf, ae_all_iff.mpr (fun t => (hF t).coeFn_toLp)] with ω hsum heq
  exact hsum.trans (tsum_congr (fun t => heq t))

lemma discounted_sum_memLp {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    MemLp (fun ω : ℕ → S => ∑' t, α ^ t * g (ω t) (ω (t+1))) 2 (pathLawFrom P π) := by
  let C := eLpNorm (fun x : S × S => g x.1 x.2) 2 (π ⊗ₘ P)
  have hm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
  have hC : C < ⊤ :=
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr h1b).2
  apply memLp_series
  · intro t
    exact (stationary_cost_memLp P π h1a.invariant g h1b t).const_mul _
  · have he (t : ℕ) :
        eLpNorm (fun ω : ℕ → S => α ^ t * g (ω t) (ω (t+1))) 2 (pathLawFrom P π) =
        (ENNReal.ofReal α)^t * C := by
      change eLpNorm ((α^t) • (fun ω : ℕ → S => g (ω t) (ω (t+1)))) 2 _ = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (pow_nonneg hα0.le _), ENNReal.ofReal_pow hα0.le]
      congr 1
      calc
        _ = eLpNorm (fun x : S × S => g x.1 x.2) 2
          ((pathLawFrom P π).map (fun ω => (ω t, ω (t+1)))) :=
          (eLpNorm_map_measure hm.aestronglyMeasurable (by fun_prop)).symm
        _ = C := by rw [stationary_pair P π h1a.invariant]
    simp_rw [he]
    rw [ENNReal.tsum_mul_right]
    exact (ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr (by simpa using hα1)) hC).ne

lemma kernel_mean_square_integrable {S Ω : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S] [MeasurableSpace Ω]
    (K : Kernel S Ω) [IsMarkovKernel K] (π : Measure S)
    (hpos : ∀ i, π {i} ≠ 0) (F : Ω → ℝ) (hF : MemLp F 2 (K ∘ₘ π)) :
    Integrable (fun i => (∫ ω, F ω ∂K i)^2) π := by
  have hsq := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp hF
  have hae := Measure.ae_integrable_of_integrable_comp hsq
  have hrow (i : S) : Integrable (fun ω => F ω ^ 2) (K i) :=
    (ae_iff_of_countable.mp hae) i (hpos i)
  have hmeas : ∀ᵐ i ∂π, AEStronglyMeasurable F (K i) := by
    have hm : AEStronglyMeasurable F ((K ∘ₖ Kernel.const Unit π) ()) :=
      hF.aestronglyMeasurable
    exact hm.comp
  have hLp (i : S) : MemLp F 2 (K i) := by
    apply (memLp_two_iff_integrable_sq ?_).mpr (hrow i)
    exact (ae_iff_of_countable.mp hmeas) i (hpos i)
  have houter : Integrable (fun i => ∫ ω, F ω ^ 2 ∂K i) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hsq
  apply houter.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
    (ae_of_all _ (fun i => sq_nonneg _))
  apply ae_of_all
  intro i
  have h := variance_nonneg F (K i)
  rw [variance_eq_sub (hLp i)] at h
  exact sub_nonneg.mp h

lemma value_memL2 {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    MemL2D π (Jstar P g α) := by
  have h := discounted_sum_memLp P π g α hα0 hα1 h1a h1b
  rw [pathLawFrom_eq_comp] at h
  have hj := kernel_mean_square_integrable (pathKernel P) π (fun i => (h1a.pos i).ne') _ h
  simp_rw [pathKernel_apply] at hj
  have hs := integrable_sum_dirac_iff (f := fun i => (Jstar P g α i)^2) (x := id)
    (c := fun i => π {i}) (fun i => measure_ne_top π {i})
  have he : Integrable (fun i => (Jstar P g α i)^2) π ↔ MemL2D π (Jstar P g α) := by
    simpa [Measure.sum_smul_dirac, MemL2D, Real.norm_eq_abs, abs_sq] using hs
  exact he.mp hj

lemma gbar_integrable {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    (∀ i, Integrable (g i) (P i)) ∧ (∀ i t, Integrable (gbar P g) ((P ^ t) i)) := by
  have hm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
  have hg : Integrable (fun x : S × S => g x.1 x.2) (π ⊗ₘ P) :=
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr h1b).integrable (by norm_num)
  have hrows := (Measure.integrable_compProd_iff hg.aestronglyMeasurable).mp hg
  refine ⟨fun i => (ae_iff_of_countable.mp hrows.1) i (h1a.pos i).ne', ?_⟩
  intro i t
  let := pow_markov P t
  have hi : Integrable (fun x : S × S => g x.1 x.2)
      ((pathLaw P i).map (fun ω => (ω t, ω (t+1)))) := by
    exact (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).mpr
      (cost_integrable P π g h1a h1b i t)
  rw [path_pair] at hi
  have houter := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).2
  exact houter.mono' (measurable_of_countable _).aestronglyMeasurable
    (ae_of_all _ (fun j => norm_integral_le_integral_norm (g j)))

end MarkovTrajectory




theorem accepted_lemma_two {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1a : Assumption1a P π) (h1b : Assumption1b P π g) :
    Assumption1c P g α ∧
    (∀ i, Integrable (g i) (P i)) ∧
    (∀ i t, Integrable (gbar P g) ((P ^ t) i)) ∧
    MemL2D π (Jstar P g α) ∧
    ∀ i, HasSum (fun t : ℕ => α ^ t * ∫ j, gbar P g j ∂((P ^ t) i)) (Jstar P g α i) := by
  have hr := MarkovTrajectory.gbar_integrable P π g h1a h1b
  exact ⟨MarkovTrajectory.absolute_discounted_finite P π g α hα0 hα1 h1a h1b,
    hr.1, hr.2, MarkovTrajectory.value_memL2 P π g α hα0 hα1 h1a h1b,
    MarkovTrajectory.discounted_series P π g α hα0 hα1 h1a h1b⟩

#print axioms accepted_lemma_two

namespace MarkovLambda
set_option maxHeartbeats 1000000
open MarkovTrajectory
lemma weighted_sq_iff {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Countable S] (π : Measure S) [IsProbabilityMeasure π] (J : S → ℝ) :
    Integrable (fun i => J i ^ 2) π ↔ MemL2D π J := by
  have h := integrable_sum_dirac_iff (f := fun i => J i ^ 2) (x := id)
    (c := fun i => π {i}) (fun i => measure_ne_top π {i})
  simpa [Measure.sum_smul_dirac, MemL2D, Real.norm_eq_abs, abs_sq] using h

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]

lemma stationary_value_memLp (h1a : Assumption1a P π) (J : S → ℝ)
    (hJ : MemL2D π J) (m : ℕ) :
    MemLp (fun ω : ℕ → S => J (ω m)) 2 (pathLawFrom P π) := by
  have hm := measurable_of_countable J
  have h := (weighted_sq_iff π J).mpr hJ
  have he : Integrable (fun i => J i ^ 2) ((pathLawFrom P π).map (fun ω => ω m)) := by
    rw [stationary_marginal P π h1a.invariant]; exact h
  exact (memLp_two_iff_integrable_sq (hm.comp (measurable_pi_apply m)).aestronglyMeasurable).mpr
    (he.comp_measurable (measurable_pi_apply m))

lemma value_rows (h1a : Assumption1a P π) (J : S → ℝ) (hJ : MemL2D π J) :
    ∀ i m, Integrable J ((P ^ m) i) := by
  intro i m
  have h := integrable_each_path P π (fun i => (h1a.pos i).ne') _
    ((stationary_value_memLp P π h1a J hJ m).integrable (by norm_num)) i
  have hm := measurable_of_countable J
  have he := (integrable_map_measure hm.aestronglyMeasurable
    (measurable_pi_apply m).aemeasurable).mpr h
  rwa [path_marginal] at he

lemma expectation_payoff (g : S → S → ℝ) (h1a : Assumption1a P π)
    (h1b : Assumption1b P π g) (J : S → ℝ) (hJ : MemL2D π J)
    (α : ℝ) (i : S) (m : ℕ) :
    (∫ ω, (∑ t ∈ range (m+1), α^t * g (ω t) (ω (t+1))) +
      α^(m+1)*J (ω (m+1)) ∂pathLaw P i) =
    (∑ t ∈ range (m+1), α^t * ∫ j, gbar P g j ∂((P^t) i)) +
      α^(m+1)*∫ j, J j ∂((P^(m+1)) i) := by
  have hj := integrable_each_path P π (fun i => (h1a.pos i).ne') _
    ((stationary_value_memLp P π h1a J hJ (m+1)).integrable (by norm_num)) i
  have hg (t : ℕ) := (cost_integrable P π g h1a h1b i t).const_mul (α^t)
  rw [integral_add (integrable_finsetSum _ (fun t _ => hg t)) (hj.const_mul _),
    integral_finsetSum _ (fun t _ => hg t), integral_const_mul]
  simp_rw [integral_const_mul, expected_cost P π g h1a h1b]
  congr 1
  have he := integral_map (μ := pathLaw P i) (φ := fun ω : ℕ → S => ω (m+1))
    (f := J) (measurable_pi_apply (m+1)).aemeasurable
    (measurable_of_countable J).aestronglyMeasurable
  rw [path_marginal] at he
  exact congrArg (fun x => α^(m+1)*x) he.symm

lemma series_integral (h1a : Assumption1a P π) (F : ℕ → (ℕ → S) → ℝ)
    (hm : ∀ n, Measurable (F n))
    (hF : ∀ n, MemLp (F n) 2 (pathLawFrom P π))
    (hs : ∑' n, eLpNorm (F n) 2 (pathLawFrom P π) ≠ ⊤) :
    MemL2D π (fun i => ∫ ω, ∑' n, F n ω ∂pathLaw P i) ∧
    ∀ i, HasSum (fun n => ∫ ω, F n ω ∂pathLaw P i)
      (∫ ω, ∑' n, F n ω ∂pathLaw P i) := by
  have hLp := memLp_series (pathLawFrom P π) F hF hs
  have hsq := hLp
  rw [pathLawFrom_eq_comp] at hsq
  have hb := kernel_mean_square_integrable (pathKernel P) π
    (fun i => (h1a.pos i).ne') _ hsq
  simp_rw [pathKernel_apply] at hb
  refine ⟨(weighted_sq_iff π _).mp hb, ?_⟩
  have hfin : ∫⁻ ω, ∑' n, ‖F n ω‖ₑ ∂pathLawFrom P π < ⊤ := by
    rw [lintegral_tsum (fun n => (hm n).enorm.aemeasurable)]
    apply lt_of_le_of_lt ?_ hs.lt_top
    apply ENNReal.tsum_le_tsum
    intro n
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hF n).aestronglyMeasurable
  have heach := lintegral_each_path_lt_top P π (fun i => (h1a.pos i).ne') _
    (Measurable.tsum (fun n => (hm n).enorm)) hfin
  intro i
  have hi (n : ℕ) := integrable_each_path P π (fun i => (h1a.pos i).ne') _
    ((hF n).integrable (by norm_num)) i
  have hn := heach i
  rw [lintegral_tsum (fun n => (hm n).enorm.aemeasurable)] at hn
  have hsn : Summable (fun n => ∫ ω, ‖F n ω‖ ∂pathLaw P i) := by
    simpa only [integral_norm_eq_lintegral_enorm (hi _).aestronglyMeasurable] using
      ENNReal.summable_toReal hn.ne
  exact hasSum_integral_of_summable_integral_norm hi hsn

lemma payoff_series (g : S → S → ℝ) (h1a : Assumption1a P π)
    (h1b : Assumption1b P π g) (J : S → ℝ) (hJ : MemL2D π J)
    (α lam : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    let F := fun m (ω : ℕ → S) => lam^m *
      ((∑ t ∈ range (m+1), α^t * g (ω t) (ω (t+1))) + α^(m+1)*J (ω (m+1)))
    MemL2D π (fun i => ∫ ω, ∑' m, F m ω ∂pathLaw P i) ∧
    ∀ i, HasSum (fun m => ∫ ω, F m ω ∂pathLaw P i)
      (∫ ω, ∑' m, F m ω ∂pathLaw P i) := by
  dsimp only
  let μ := pathLawFrom P π
  let A := ENNReal.ofReal α
  let C := eLpNorm (fun x : S × S => g x.1 x.2) 2 (π ⊗ₘ P)
  let D := eLpNorm J 2 π
  let K := (∑' t : ℕ, A^t)*C + D
  let X := fun t (ω : ℕ → S) => α^t*g (ω t) (ω (t+1))
  let Y := fun m (ω : ℕ → S) => α^(m+1)*J (ω (m+1))
  let B := fun m (ω : ℕ → S) => (∑ t ∈ range (m+1), X t ω) + Y m ω
  have hm : Measurable (fun x : S × S => g x.1 x.2) := measurable_of_countable _
  have hjm := measurable_of_countable J
  have hX (t : ℕ) : MemLp (X t) 2 μ :=
    (stationary_cost_memLp P π h1a.invariant g h1b t).const_mul _
  have hY (m : ℕ) : MemLp (Y m) 2 μ :=
    (stationary_value_memLp P π h1a J hJ (m+1)).const_mul _
  have hB (m : ℕ) : MemLp (B m) 2 μ := by
    exact (memLp_finsetSum _ (fun t _ => hX t)).add (hY m)
  have heX (t : ℕ) : eLpNorm (X t) 2 μ = A^t*C := by
    change eLpNorm ((α^t) • (fun ω : ℕ → S => g (ω t) (ω (t+1)))) 2 μ = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg hα0 _),
      ENNReal.ofReal_pow hα0]
    congr 1
    calc
      _ = eLpNorm (fun x : S × S => g x.1 x.2) 2
          ((pathLawFrom P π).map (fun ω => (ω t, ω (t+1)))) :=
        (eLpNorm_map_measure hm.aestronglyMeasurable (by fun_prop)).symm
      _ = C := by rw [stationary_pair P π h1a.invariant]
  have heY (m : ℕ) : eLpNorm (Y m) 2 μ ≤ D := by
    change eLpNorm ((α^(m+1)) • (fun ω : ℕ → S => J (ω (m+1)))) 2 μ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg hα0 _),
      ENNReal.ofReal_pow hα0]
    have he : eLpNorm (fun ω : ℕ → S => J (ω (m+1))) 2 μ = D := by
      calc
        _ = eLpNorm J 2 ((pathLawFrom P π).map (fun ω => ω (m+1))) :=
          (eLpNorm_map_measure hjm.aestronglyMeasurable
            (measurable_pi_apply (m+1)).aemeasurable).symm
        _ = D := by rw [stationary_marginal P π h1a.invariant]
    rw [he]
    exact mul_le_of_le_one_left' (pow_le_one₀ (by positivity) (by simpa using hα1.le))
  have hb (m : ℕ) : eLpNorm (B m) 2 μ ≤ K := by
    have hx := (memLp_finsetSum (range (m+1)) (fun t _ => hX t)).aestronglyMeasurable
    calc
      _ ≤ eLpNorm (fun ω => ∑ t ∈ range (m+1), X t ω) 2 μ + eLpNorm (Y m) 2 μ :=
        eLpNorm_add_le hx (hY m).aestronglyMeasurable (by norm_num)
      _ ≤ (∑ t ∈ range (m+1), eLpNorm (X t) 2 μ) + D :=
        add_le_add (by
          have he : (fun ω => ∑ t ∈ range (m+1), X t ω) = ∑ t ∈ range (m+1), X t := by
            ext ω; simp
          rw [he]
          exact eLpNorm_sum_le (p := 2) (μ := μ) (s := range (m+1))
            (fun t _ => (hX t).aestronglyMeasurable) (by norm_num)) (heY m)
      _ ≤ K := by
        simp_rw [heX]
        dsimp only [K]
        rw [← ENNReal.tsum_mul_right]
        exact add_le_add (ENNReal.sum_le_tsum _) le_rfl
  have hK : K < ⊤ := by
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr (by simpa [A] using hα1))
        ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr h1b).2
    · exact ((memLp_two_iff_integrable_sq hjm.aestronglyMeasurable).mpr
        ((weighted_sq_iff π J).mpr hJ)).2
  apply series_integral P π h1a
  · intro m
    exact ((Finset.measurable_sum _ (fun t _ =>
      (hm.comp (by fun_prop : Measurable (fun ω : ℕ → S => (ω t,ω (t+1))))).const_mul _)).add
      ((hjm.comp (measurable_pi_apply (m+1))).const_mul _)).const_mul _
  · intro m; exact (hB m).const_mul _
  · apply ne_of_lt
    calc
      _ ≤ ∑' m : ℕ, (ENNReal.ofReal lam)^m*K := by
        apply ENNReal.tsum_le_tsum
        intro m
        change eLpNorm ((lam^m) • B m) 2 μ ≤ _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg hl0 _),
          ENNReal.ofReal_pow hl0]
        exact mul_le_mul' le_rfl (hb m)
      _ < ⊤ := by
        rw [ENNReal.tsum_mul_right]
        exact ENNReal.mul_lt_top (tsum_geometric_lt_top.mpr (by simpa using hl1)) hK

end MarkovLambda
#print axioms MarkovLambda.payoff_series

theorem accepted_lemma_three {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1 : Assumption1 P π g α) (J : S → ℝ) (hJ : MemL2D π J)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    MemL2D π (Tlam P g α lam J) ∧
    (∀ i m, Integrable J ((P ^ m) i)) ∧
    (lam < 1 → ∀ i, HasSum
      (fun m : ℕ => (1 - lam) * lam ^ m *
        (∑ t ∈ range (m + 1), α ^ t * ∫ j, gbar P g j ∂((P ^ t) i) +
          α ^ (m + 1) * ∫ j, J j ∂((P ^ (m + 1)) i)))
      (Tlam P g α lam J i)) := by
  have hrows := MarkovLambda.value_rows P π h1.a J hJ
  by_cases he : lam = 1
  · subst lam
    refine ⟨?_, hrows, by intro h; linarith⟩
    simpa [Tlam] using
      MarkovTrajectory.value_memL2 P π g α hα0 hα1 h1.a h1.b
  have hl1 : lam < 1 := lt_of_le_of_ne hlam.2 he
  have hp := MarkovLambda.payoff_series P π g h1.a h1.b J hJ α lam hα0.le hα1 hlam.1 hl1
  dsimp only at hp
  let Q := fun i => ∫ ω, ∑' m : ℕ, lam ^ m *
    ((∑ t ∈ range (m+1), α^t * g (ω t) (ω (t+1))) + α^(m+1)*J (ω (m+1)))
    ∂pathLaw P i
  have hq : ∀ i, Tlam P g α lam J i = (1-lam)*Q i := by
    intro i
    have ht := (hp.2 i).tsum_eq
    simp only [integral_const_mul] at ht
    simpa only [Tlam, if_neg he, Q, ht]
  have hmem : MemL2D π (fun i => (1-lam)*Q i) := by
    have h := hp.1.mul_left ((1-lam)^2)
    apply h.congr
    intro i
    dsimp only [Q]
    ring
  refine ⟨by simpa only [funext hq] using hmem, hrows, ?_⟩
  intro _ i
  have ht := (hp.2 i).mul_left (1-lam)
  simp only [integral_const_mul] at ht
  simp_rw [MarkovLambda.expectation_payoff P π g h1.a h1.b J hJ α i] at ht
  simpa only [hq, Q, mul_assoc] using ht
#print axioms accepted_lemma_three

namespace MarkovContraction
open MarkovLambda MarkovTrajectory
variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (π : Measure S) [IsProbabilityMeasure π]

lemma memLp_iff (J : S → ℝ) : MemLp J 2 π ↔ MemL2D π J := by
  rw [memLp_two_iff_integrable_sq (measurable_of_countable J).aestronglyMeasurable,
    weighted_sq_iff]

lemma normD_eq_lpNorm (J : S → ℝ) (hJ : MemL2D π J) :
    normD π J = lpNorm J 2 π := by
  have hi : (∫ i, J i ^ 2 ∂π) = ∑' i, (π {i}).toReal * J i ^ 2 := by
    simpa [Measure.real, smul_eq_mul] using
      integral_countable ((weighted_sq_iff π J).mpr hJ)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (measurable_of_countable J).aestronglyMeasurable]
  simpa [Real.norm_eq_abs, Real.rpow_two, abs_sq, hi, normD, one_div] using
    (Real.sqrt_eq_rpow (∑' i, (π {i}).toReal * J i ^ 2))

lemma normD_toLp (J : S → ℝ) (hJ : MemLp J 2 π) :
    ‖hJ.toLp J‖ = normD π J := by
  rw [normD_eq_lpNorm π J ((memLp_iff π J).mp hJ), Lp.norm_toLp]
  exact toReal_eLpNorm hJ.aestronglyMeasurable

lemma normD_const_mul (J : S → ℝ) (hJ : MemL2D π J) (c : ℝ) :
    normD π (fun i => c * J i) = |c| * normD π J := by
  have hj := (memLp_iff π J).mpr hJ
  rw [normD_eq_lpNorm π _ ((memLp_iff π _).mp (hj.const_mul c)),
    normD_eq_lpNorm π J hJ]
  change lpNorm (c • J) 2 π = _
  simpa only [coe_nnnorm, Real.norm_eq_abs] using lpNorm_const_smul c J π (p := 2)

lemma kernel_contract (P : Kernel S S) [IsMarkovKernel P]
    (hstat : P ∘ₘ π = π) (hpos : ∀ i, π {i} ≠ 0)
    (J : S → ℝ) (hJ : MemL2D π J) :
    MemL2D π (Pop P J) ∧ normD π (Pop P J) ≤ normD π J := by
  have hj2 := (weighted_sq_iff π J).mpr hJ
  have hcomp : Integrable (fun i => J i ^ 2) (P ∘ₘ π) := by rwa [hstat]
  have hae := Measure.ae_integrable_of_integrable_comp hcomp
  have hrow2 (i : S) : Integrable (fun j => J j ^ 2) (P i) :=
    (ae_iff_of_countable.mp hae) i (hpos i)
  have hrowLp (i : S) : MemLp J 2 (P i) :=
    (memLp_two_iff_integrable_sq (measurable_of_countable J).aestronglyMeasurable).mpr (hrow2 i)
  have hbound (i : S) : (Pop P J i)^2 ≤ ∫ j, J j^2 ∂P i := by
    have h := variance_nonneg J (P i)
    rw [variance_eq_sub (hrowLp i)] at h
    exact sub_nonneg.mp h
  have houter : Integrable (fun i => ∫ j, J j^2 ∂P i) π := by
    simpa only [Real.norm_eq_abs, abs_sq] using
      Measure.integrable_integral_norm_of_integrable_comp hcomp
  have hpj2 : Integrable (fun i => (Pop P J i)^2) π :=
    houter.mono_nonneg (measurable_of_countable _).aestronglyMeasurable
      (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ hbound)
  have hiter : (∫ i, ∫ j, J j^2 ∂P i ∂π) = ∫ j, J j^2 ∂π := by
    have hk : Integrable (fun i => J i^2) ((P ∘ₖ Kernel.const Unit π) ()) := hcomp
    have h := Kernel.integral_comp hk
    simpa only [Kernel.comp_apply, Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
      hstat] using h.symm
  refine ⟨(weighted_sq_iff π _).mp hpj2, ?_⟩
  apply Real.sqrt_le_sqrt
  have hp := integral_countable hpj2
  have hj := integral_countable hj2
  simp only [Measure.real, smul_eq_mul] at hp hj
  change (∑' i, (π {i}).toReal * (Pop P J i)^2) ≤ ∑' i, (π {i}).toReal * J i^2
  rw [← hp, ← hj, ← hiter]
  exact integral_mono hpj2 houter hbound

lemma series_bound (F : ℕ → S → ℝ) (hF : ∀ n, MemL2D π (F n))
    (G : S → ℝ) (hG : ∀ i, HasSum (fun n => F n i) (G i))
    (b : ℕ → ℝ) (hb : Summable b) (hbound : ∀ n, normD π (F n) ≤ b n) :
    normD π G ≤ ∑' n, b n := by
  let hLp : ∀ n, MemLp (F n) 2 π := fun n => (memLp_iff π _).mpr (hF n)
  let f : ℕ → Lp ℝ 2 π := fun n => (hLp n).toLp (F n)
  have hf : Summable (fun n => ‖f n‖) := hb.of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => by
      change ‖(hLp n).toLp (F n)‖ ≤ b n
      rw [normD_toLp]
      exact hbound n)
  have he := Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hf)
  have hEq : ((∑' n, f n : Lp ℝ 2 π) : S → ℝ) =ᵐ[π] G := by
    filter_upwards [he, ae_all_iff.mpr (fun n => (hLp n).coeFn_toLp)] with i hi hj
    exact hi.trans ((tsum_congr fun n => hj n).trans (hG i).tsum_eq)
  have hg : MemLp G 2 π := (Lp.memLp (∑' n, f n)).ae_eq hEq
  have heq : hg.toLp G = ∑' n, f n := by
    apply Lp.ext
    exact hg.coeFn_toLp.trans hEq.symm
  rw [← normD_toLp π G hg, heq]
  apply (norm_tsum_le_tsum_norm hf).trans
  apply Summable.tsum_le_tsum _ hf hb
  intro n
  change ‖(hLp n).toLp (F n)‖ ≤ b n
  rw [normD_toLp]
  exact hbound n

end MarkovContraction

theorem accepted_lemma_four {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h1 : Assumption1 P π g α) (J Jb : S → ℝ) (hJ : MemL2D π J) (hJb : MemL2D π Jb)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    normD π (Tlam P g α lam J - Tlam P g α lam Jb) ≤
        α * (1 - lam) / (1 - α * lam) * normD π (J - Jb) ∧
      α * (1 - lam) / (1 - α * lam) * normD π (J - Jb) ≤ α * normD π (J - Jb) := by
  have hn : 0 ≤ normD π (J - Jb) := Real.sqrt_nonneg _
  have hal : α * lam < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hα0.le hlam.2) hα1
  have hden : 0 < 1 - α * lam := sub_pos.mpr hal
  have hcoef : α * (1 - lam) / (1 - α * lam) ≤ α := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg hα0.le hlam.1) (sub_nonneg.mpr hα1.le)]
  refine ⟨?_, mul_le_mul_of_nonneg_right hcoef hn⟩
  by_cases he : lam = 1
  · subst lam
    simp [Tlam, normD]
  have hl1 : lam < 1 := lt_of_le_of_ne hlam.2 he
  have hj := accepted_lemma_three P π g α hα0 hα1 h1 J hJ lam hlam
  have hjb := accepted_lemma_three P π g α hα0 hα1 h1 Jb hJb lam hlam
  have hd : MemL2D π (J-Jb) := (MarkovContraction.memLp_iff π _).mp
    (((MarkovContraction.memLp_iff π J).mpr hJ).sub
      ((MarkovContraction.memLp_iff π Jb).mpr hJb))
  let q := fun m : ℕ => (1-lam)*lam^m*α^(m+1)
  have hq (m : ℕ) : 0 ≤ q m :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hlam.2) (pow_nonneg hlam.1 _))
      (pow_nonneg hα0.le _)
  let F := fun m i => q m * Pop (P^(m+1)) (J-Jb) i
  have hk (m : ℕ) :
      MemL2D π (Pop (P^(m+1)) (J-Jb)) ∧
      normD π (Pop (P^(m+1)) (J-Jb)) ≤ normD π (J-Jb) := by
    letI := MarkovTrajectory.pow_markov P (m+1)
    apply MarkovContraction.kernel_contract π (P^(m+1)) _ (fun i => (h1.a.pos i).ne') _ hd
    exact (MarkovTrajectory.marginal_law P π (m+1)).symm.trans
      (MarkovTrajectory.stationary_marginal P π h1.a.invariant (m+1))
  have hF (m : ℕ) : MemL2D π (F m) := (MarkovContraction.memLp_iff π _).mp
    (((MarkovContraction.memLp_iff π _).mpr (hk m).1).const_mul (q m))
  have hbound (m : ℕ) : normD π (F m) ≤ q m * normD π (J-Jb) := by
    dsimp only [F]
    rw [MarkovContraction.normD_const_mul π _ (hk m).1, abs_of_nonneg (hq m)]
    exact mul_le_mul_of_nonneg_left (hk m).2 (hq m)
  have hsum : HasSum (fun m => q m * normD π (J-Jb))
      (α*(1-lam)/(1-α*lam)*normD π (J-Jb)) := by
    have h := ((hasSum_geometric_of_lt_one (mul_nonneg hα0.le hlam.1) hal).mul_left
      ((1-lam)*α)).mul_right (normD π (J-Jb))
    have hfun : (fun m => q m * normD π (J-Jb)) =
        (fun m => (1-lam)*α*(α*lam)^m*normD π (J-Jb)) := by
      funext m
      dsimp only [q]
      rw [mul_pow, pow_succ]
      ring
    rw [hfun]
    have heq : α*(1-lam)/(1-α*lam)*normD π (J-Jb) =
        (1-lam)*α*(1-α*lam)⁻¹*normD π (J-Jb) := by
      rw [div_eq_mul_inv]
      ring
    rw [heq]
    exact h
  have hpoint (i : S) :
      HasSum (fun m => F m i) ((Tlam P g α lam J - Tlam P g α lam Jb) i) := by
    have h := (hj.2.2 hl1 i).sub (hjb.2.2 hl1 i)
    have hfun : (fun m => F m i) =
        ((fun m => (1-lam)*lam^m *
          ((∑ t ∈ range (m+1), α^t * ∫ j, gbar P g j ∂((P^t) i)) +
            α^(m+1)*∫ j, J j ∂((P^(m+1)) i))) -
         (fun m => (1-lam)*lam^m *
          ((∑ t ∈ range (m+1), α^t * ∫ j, gbar P g j ∂((P^t) i)) +
            α^(m+1)*∫ j, Jb j ∂((P^(m+1)) i)))) := by
      funext m
      dsimp only [F, q, Pop, Pi.sub_apply]
      rw [integral_sub (hj.2.1 i (m+1)) (hjb.2.1 i (m+1))]
      ring
    rw [hfun]
    exact h
  exact (MarkovContraction.series_bound π F hF _ hpoint _ hsum.summable hbound).trans_eq
    hsum.tsum_eq
#print axioms accepted_lemma_four

namespace MarkovProjection
open MarkovContraction Matrix
open scoped NNReal
variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (π : Measure S) [IsProbabilityMeasure π]
    (hpos : ∀ i, π {i} ≠ 0)
include hpos

lemma lp_add_apply (f g : Lp ℝ 2 π) (i : S) : (f + g) i = f i + g i :=
  (ae_iff_of_countable.mp (Lp.coeFn_add f g)) i (hpos i)
lemma lp_smul_apply (r : ℝ) (f : Lp ℝ 2 π) (i : S) : (r • f) i = r * f i :=
  (ae_iff_of_countable.mp (Lp.coeFn_smul r f)) i (hpos i)
lemma lp_zero_apply (i : S) : (0 : Lp ℝ 2 π) i = 0 :=
  (ae_iff_of_countable.mp (Lp.coeFn_zero ℝ 2 π)) i (hpos i)
lemma lp_sum_apply {I : Type*} (s : Finset I) (f : I → Lp ℝ 2 π) (i : S) :
    (∑ k ∈ s, f k : Lp ℝ 2 π) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using lp_zero_apply π hpos i
  | @insert a s ha ih => rw [Finset.sum_insert ha, lp_add_apply π hpos, Finset.sum_insert ha, ih]
lemma toLp_apply (J : S → ℝ) (hJ : MemLp J 2 π) (i : S) : hJ.toLp J i = J i :=
  (ae_iff_of_countable.mp hJ.coeFn_toLp) i (hpos i)

variable {K : ℕ} (φ : S → Fin K → ℝ) (h2 : Assumption2 π φ)
include h2
omit hpos in
lemma basis_memLp (k : Fin K) : MemLp (fun i => φ i k) 2 π :=
  (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).mpr
    (h2.sq_integrable k)
noncomputable def basisLp (k : Fin K) : Lp ℝ 2 π :=
  (basis_memLp π φ h2 k).toLp (fun i => φ i k)
lemma basisLp_apply (k : Fin K) (i : S) : basisLp π φ h2 k i = φ i k :=
  toLp_apply π hpos _ _ i
noncomputable def synth (r : Fin K → ℝ) : Lp ℝ 2 π := ∑ k, r k • basisLp π φ h2 k
lemma synth_apply (r : Fin K → ℝ) (i : S) : synth π φ h2 r i = Jtilde φ r i := by
  unfold synth
  rw [lp_sum_apply π hpos]
  simp only [lp_smul_apply π hpos, basisLp_apply π hpos, Jtilde, dotProduct, mul_comm]
lemma basis_independent : LinearIndependent ℝ (basisLp π φ h2) := by
  rw [Fintype.linearIndependent_iff]
  intro r hr
  apply Fintype.linearIndependent_iff.mp h2.linIndep r
  funext i
  have he := congrArg (fun f : Lp ℝ 2 π => f i) hr
  simp only [lp_sum_apply π hpos, lp_smul_apply π hpos, basisLp_apply π hpos,
    lp_zero_apply π hpos] at he
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using he
lemma gram_eq : TDApprox.Conv.gram π φ = Matrix.gram ℝ (basisLp π φ h2) := by
  ext k l
  rw [Matrix.gram_apply, L2.inner_def]
  have hi := (basis_memLp π φ h2 k).integrable_mul (basis_memLp π φ h2 l)
  have hc := integral_countable hi
  simpa [TDApprox.Conv.gram, basisLp_apply π hpos, Measure.real, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hc.symm
lemma gram_det_ne_zero : (TDApprox.Conv.gram π φ).det ≠ 0 := by
  rw [gram_eq π hpos φ h2]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr (basis_independent π hpos φ h2)
lemma synth_memL2 (r : Fin K → ℝ) : MemL2D π (Jtilde φ r) := by
  apply (memLp_iff π _).mp
  have h := Lp.memLp (synth π φ h2 r)
  have he : (synth π φ h2 r : S → ℝ) = Jtilde φ r := funext (synth_apply π hpos φ h2 r)
  rwa [he] at h
lemma phiD_inner (J : S → ℝ) (hJ : MemLp J 2 π) (k : Fin K) :
    phiD π φ J k = inner ℝ (basisLp π φ h2 k) (hJ.toLp J) := by
  rw [L2.inner_def]
  have hc := integral_countable ((basis_memLp π φ h2 k).integrable_mul hJ)
  simpa [phiD, basisLp_apply π hpos, toLp_apply π hpos, Measure.real,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hc.symm
lemma inner_synth (k : Fin K) (r : Fin K → ℝ) :
    inner ℝ (basisLp π φ h2 k) (synth π φ h2 r) =
      ((TDApprox.Conv.gram π φ) *ᵥ r) k := by
  rw [gram_eq π hpos φ h2]
  simp [synth, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, mul_comm]
noncomputable def basisSpan : Submodule ℝ (Lp ℝ 2 π) :=
  Submodule.span ℝ (Set.range (basisLp π φ h2))
instance span_finite : FiniteDimensional ℝ (basisSpan π φ h2) := by
  unfold basisSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
lemma synth_mem_span (r : Fin K → ℝ) : synth π φ h2 r ∈ basisSpan π φ h2 := by
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
lemma projection_identity (J : S → ℝ) (hJ : MemLp J 2 π) :
    (basisSpan π φ h2).starProjection (hJ.toLp J) =
      synth π φ h2 ((TDApprox.Conv.gram π φ)⁻¹ *ᵥ phiD π φ J) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (synth_mem_span π hpos φ h2 _)
  have hn (k : Fin K) : inner ℝ (basisLp π φ h2 k)
      (hJ.toLp J - synth π φ h2 ((TDApprox.Conv.gram π φ)⁻¹ *ᵥ phiD π φ J)) = 0 := by
    rw [inner_sub_right, ← phiD_inner π hpos φ h2 J hJ k,
      inner_synth π hpos φ h2, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (gram_det_ne_zero π hpos φ h2)),
      Matrix.one_mulVec, sub_self]
  intro w hw
  change w ∈ Submodule.span ℝ (Set.range (basisLp π φ h2)) at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    rw [real_inner_comm]
    exact hn k
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul r x hx ih => simp [inner_smul_right, ih]
lemma proj_memL2 (J : S → ℝ) : MemL2D π (proj π φ J) :=
  synth_memL2 π hpos φ h2 _
lemma proj_toLp (J : S → ℝ) (hJ : MemLp J 2 π) :
    ((memLp_iff π _).mpr (proj_memL2 π hpos φ h2 J)).toLp (proj π φ J) =
      (basisSpan π φ h2).starProjection (hJ.toLp J) := by
  rw [projection_identity π hpos φ h2]
  apply Lp.ext
  exact ae_of_all _ fun i => by
    rw [toLp_apply π hpos, synth_apply π hpos]
    rfl
lemma proj_nonexpansive (J Jb : S → ℝ) (hJ : MemL2D π J) (hJb : MemL2D π Jb) :
    normD π (proj π φ J - proj π φ Jb) ≤ normD π (J - Jb) := by
  let hj := (memLp_iff π J).mpr hJ
  let hjb := (memLp_iff π Jb).mpr hJb
  let hpj := (memLp_iff π _).mpr (proj_memL2 π hpos φ h2 J)
  let hpjb := (memLp_iff π _).mpr (proj_memL2 π hpos φ h2 Jb)
  rw [← normD_toLp π _ (hpj.sub hpjb), ← normD_toLp π _ (hj.sub hjb),
    MemLp.toLp_sub hpj hpjb, MemLp.toLp_sub hj hjb, proj_toLp π hpos φ h2 J hj,
    proj_toLp π hpos φ h2 Jb hjb, ← map_sub]
  exact Submodule.norm_starProjection_apply_le _ _
lemma normD_sub_coe (f g : Lp ℝ 2 π) :
    normD π ((f : S → ℝ) - g) = ‖f - g‖ := by
  rw [← normD_toLp π _ ((Lp.memLp f).sub (Lp.memLp g)),
    MemLp.toLp_sub (Lp.memLp f) (Lp.memLp g), Lp.toLp_coeFn, Lp.toLp_coeFn]
lemma fixedPoint_of_contract (F : (S → ℝ) → (S → ℝ))
    (hF : ∀ J, MemL2D π J → MemL2D π (F J))
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∀ J Jb, MemL2D π J → MemL2D π Jb →
      normD π (F J - F Jb) ≤ c * normD π (J - Jb)) :
    ∃ X : S → ℝ, MemL2D π X ∧ F X = X ∧
      (∀ J, MemL2D π J → F J = J → J = X) ∧
      ∀ J, MemL2D π J → normD π (X - J) ≤ normD π (F J - J) / (1 - c) := by
  let L : (Lp ℝ 2 π) → (Lp ℝ 2 π) := fun f =>
    ((memLp_iff π _).mpr (hF f ((memLp_iff π _).mp (Lp.memLp f)))).toLp (F f)
  have happ (f : Lp ℝ 2 π) : (L f : S → ℝ) = F f := by
    funext i
    exact toLp_apply π hpos _ _ i
  have hl : ContractingWith (⟨c, hc0⟩ : ℝ≥0) L := by
    refine ⟨hc1, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
    simp only [dist_eq_norm]
    rw [← normD_sub_coe π hpos φ h2, ← normD_sub_coe π hpos φ h2, happ, happ]
    exact hc f g ((memLp_iff π _).mp (Lp.memLp f)) ((memLp_iff π _).mp (Lp.memLp g))
  let x : Lp ℝ 2 π := hl.fixedPoint L
  have hx : L x = x := hl.fixedPoint_isFixedPt
  have hxpoint : F (x : S → ℝ) = x := by rw [← happ, hx]
  have hinput (J : S → ℝ) (hJ : MemL2D π J) :
      (((memLp_iff π _).mpr hJ).toLp J : S → ℝ) = J :=
    funext (toLp_apply π hpos J _)
  refine ⟨x, (memLp_iff π _).mp (Lp.memLp x), hxpoint, ?_, ?_⟩
  · intro J hJ he
    let j := ((memLp_iff π _).mpr hJ).toLp J
    have hj : L j = j := by
      apply Lp.ext
      exact ae_of_all _ fun i => by
        change (L j : S → ℝ) i = (j : S → ℝ) i
        rw [happ, hinput J hJ, he]
    have heq : j = x := hl.fixedPoint_unique hj
    rw [← hinput J hJ]
    exact congrArg (fun y : Lp ℝ 2 π => (y : S → ℝ)) heq
  · intro J hJ
    let j := ((memLp_iff π _).mpr hJ).toLp J
    have hb := hl.dist_fixedPoint_le j
    rw [dist_comm j x, dist_comm j (L j)] at hb
    simp only [dist_eq_norm] at hb
    rw [← normD_sub_coe π hpos φ h2, ← normD_sub_coe π hpos φ h2] at hb
    have hjfun : (j : S → ℝ) = J := hinput J hJ
    simpa only [happ, hjfun, NNReal.toReal] using hb
lemma jtilde_injective : Function.Injective (Jtilde φ) := by
  intro r s he
  apply h2.linIndep.fintypeLinearCombination_injective
  ext i
  have hi := congrFun he i
  simpa [Fintype.linearCombination_apply, Jtilde, dotProduct, Finset.sum_apply, mul_comm] using hi
end MarkovProjection

/-- Complete local projection/fixed-point result. The final estimate is the residual estimate;
    the platform Lemma 5 additionally needs the Bellman invariance of Jstar. -/
theorem local_projection_residual {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (∀ J, MemL2D π J → MemL2D π (proj π φ (Tlam P g α lam J))) ∧
    (∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ J Jb, MemL2D π J → MemL2D π Jb →
      normD π (proj π φ (Tlam P g α lam J) - proj π φ (Tlam P g α lam Jb)) ≤
        c * normD π (J - Jb)) ∧
    ∃ rstar : Fin K → ℝ,
      proj π φ (Tlam P g α lam (Jtilde φ rstar)) = Jtilde φ rstar ∧
      (∀ J, MemL2D π J → proj π φ (Tlam P g α lam J) = J → J = Jtilde φ rstar) ∧
      (∀ r, proj π φ (Tlam P g α lam (Jtilde φ r)) = Jtilde φ r → r = rstar) ∧
      ∀ J, MemL2D π J →
        normD π (Jtilde φ rstar - J) ≤
          normD π (proj π φ (Tlam P g α lam J) - J) /
            (1 - α * (1 - lam) / (1 - α * lam)) := by
  have hpos : ∀ i, π {i} ≠ 0 := fun i => (h1.a.pos i).ne'
  let F := fun J => proj π φ (Tlam P g α lam J)
  let c := α * (1 - lam) / (1 - α * lam)
  have hmap (J : S → ℝ) (_hJ : MemL2D π J) : MemL2D π (F J) :=
    MarkovProjection.proj_memL2 π hpos φ h2 _
  have hal : α * lam < 1 := lt_of_le_of_lt (mul_le_of_le_one_right hα0.le hlam.2) hα1
  have hd : 0 < 1 - α * lam := sub_pos.mpr hal
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg hα0.le (sub_nonneg.mpr hlam.2)) hd.le
  have hc1 : c < 1 := by
    change α * (1 - lam) / (1 - α * lam) < 1
    rw [div_lt_iff₀ hd]
    nlinarith
  have hc (J Jb : S → ℝ) (hJ : MemL2D π J) (hJb : MemL2D π Jb) :
      normD π (F J - F Jb) ≤ c * normD π (J - Jb) := by
    exact (MarkovProjection.proj_nonexpansive π hpos φ h2 _ _
      (accepted_lemma_three P π g α hα0 hα1 h1 J hJ lam hlam).1
      (accepted_lemma_three P π g α hα0 hα1 h1 Jb hJb lam hlam).1).trans
      (accepted_lemma_four P π g α hα0 hα1 h1 J Jb hJ hJb lam hlam).1
  obtain ⟨X, hX, hfixed, huniq, hbound⟩ :=
    MarkovProjection.fixedPoint_of_contract π hpos φ h2 F hmap c hc0 hc1 hc
  let rstar := Matrix.mulVec (TDApprox.Conv.gram π φ)⁻¹ (phiD π φ (Tlam P g α lam X))
  have hr : Jtilde φ rstar = X := hfixed
  refine ⟨hmap, ⟨c, hc0, hc1, hc⟩, rstar, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact hfixed
  · intro J hJ he
    rw [hr]
    exact huniq J hJ he
  · intro r he
    apply MarkovProjection.jtilde_injective π hpos φ h2
    rw [hr]
    exact huniq _ (MarkovProjection.synth_memL2 π hpos φ h2 r) he
  · intro J hJ
    rw [hr]
    exact hbound J hJ
#print axioms local_projection_residual

namespace MarkovBellman
open MarkovTrajectory MarkovLambda MarkovContraction
variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]

lemma pow_invariant (h : Assumption1a P π) (n : ℕ) : (P ^ n) ∘ₘ π = π :=
  (marginal_law P π n).symm.trans (stationary_marginal P π h.invariant n)

lemma mean_memL2 (g : S → S → ℝ) (h : Assumption1a P π)
    (hg : Assumption1b P π g) : MemL2D π (gbar P g) := by
  have hm := stationary_cost_memLp P π h.invariant g hg 0
  rw [pathLawFrom_eq_comp] at hm
  have hb := kernel_mean_square_integrable (pathKernel P) π
    (fun i => (h.pos i).ne') _ hm
  simp_rw [pathKernel_apply, expected_cost P π g h hg] at hb
  change Integrable (fun i => (∫ j, gbar P g j ∂Kernel.id i)^2) π at hb
  simp only [Kernel.id_apply, integral_dirac] at hb
  exact (weighted_sq_iff π _).mp hb

lemma kernel_series (h : Assumption1a P π) (F : ℕ → S → ℝ)
    (hF : ∀ n, MemL2D π (F n))
    (b : ℕ → ℝ) (hb : Summable b) (hbound : ∀ n, normD π (F n) ≤ b n)
    (k : ℕ) (i : S) :
    HasSum (fun n => ∫ j, F n j ∂((P ^ k) i))
      (∫ j, ∑' n, F n j ∂((P ^ k) i)) := by
  letI := pow_markov P k
  let hLp := fun n => (memLp_iff π (F n)).mpr (hF n)
  let f : ℕ → Lp ℝ 2 π := fun n => (hLp n).toLp (F n)
  have hf : Summable (fun n => ‖f n‖) := hb.of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => by
      change ‖(hLp n).toLp (F n)‖ ≤ b n
      rw [normD_toLp]
      exact hbound n)
  have htop : ∑' n, eLpNorm (F n) 2 π ≠ ⊤ := by
    simpa only [f, Lp.enorm_toLp] using tsum_enorm_ne_top_iff_summable_norm.mpr hf
  have hfin : ∫⁻ j, ∑' n, ‖F n j‖ₑ ∂π < ⊤ := by
    rw [lintegral_tsum (fun n => (measurable_of_countable (F n)).enorm.aemeasurable)]
    apply lt_of_le_of_lt ?_ htop.lt_top
    apply ENNReal.tsum_le_tsum
    intro n
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hLp n).aestronglyMeasurable
  have hbind : ∫⁻ j, ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂((P ^ k) j) ∂π < ⊤ := by
    rw [← Measure.lintegral_bind (Kernel.aemeasurable _) (measurable_of_countable _).aemeasurable,
      pow_invariant P π h]
    exact hfin
  have hae := ae_lt_top' ((measurable_of_countable (fun x => ∑' n, ‖F n x‖ₑ)).lintegral_kernel
    (κ := P ^ k)).aemeasurable hbind.ne
  have hi := (ae_iff_of_countable.mp hae) i (h.pos i).ne'
  rw [lintegral_tsum (fun n => (measurable_of_countable (F n)).enorm.aemeasurable)] at hi
  have hr (n : ℕ) : Integrable (F n) ((P ^ k) i) :=
    value_rows P π h (F n) (hF n) i k
  have hs : Summable (fun n => ∫ j, ‖F n j‖ ∂((P ^ k) i)) := by
    simpa only [integral_norm_eq_lintegral_enorm (hr _).aestronglyMeasurable] using
      ENNReal.summable_toReal hi.ne
  exact hasSum_integral_of_summable_integral_norm hr hs

lemma power_mean_comp (g : S → S → ℝ) (h : Assumption1a P π)
    (hg : Assumption1b P π g) (k t : ℕ) (i : S) :
    (∫ j, ∫ z, gbar P g z ∂((P ^ t) j) ∂((P ^ k) i)) =
      ∫ z, gbar P g z ∂((P ^ (t + k)) i) := by
  letI := pow_markov P k
  letI := pow_markov P t
  have hi := (gbar_integrable P π g h hg).2 i (t+k)
  rw [pow_add] at hi ⊢
  exact (Kernel.integral_comp hi).symm

lemma value_tail (g : S → S → ℝ) (α : ℝ) (ha0 : 0 < α) (ha1 : α < 1)
    (h : Assumption1a P π) (hg : Assumption1b P π g) (k : ℕ) (i : S) :
    (∑ t ∈ range k, α^t * ∫ j, gbar P g j ∂((P^t) i)) +
      α^k * ∫ j, Jstar P g α j ∂((P^k) i) = Jstar P g α i := by
  have hmean := mean_memL2 P π g h hg
  let F := fun t j => α^t * Pop (P^t) (gbar P g) j
  have hpow (t : ℕ) :
      MemL2D π (Pop (P^t) (gbar P g)) ∧
        normD π (Pop (P^t) (gbar P g)) ≤ normD π (gbar P g) := by
    letI := pow_markov P t
    exact kernel_contract π (P^t) (pow_invariant P π h t)
      (fun j => (h.pos j).ne') _ hmean
  have hF (t : ℕ) : MemL2D π (F t) :=
    (memLp_iff π _).mp (((memLp_iff π _).mpr (hpow t).1).const_mul (α^t))
  have hb := (summable_geometric_of_lt_one ha0.le ha1).mul_right (normD π (gbar P g))
  have hbound (t : ℕ) : normD π (F t) ≤ α^t * normD π (gbar P g) := by
    dsimp only [F]
    rw [normD_const_mul π _ (hpow t).1, abs_of_nonneg (pow_nonneg ha0.le _)]
    exact mul_le_mul_of_nonneg_left (hpow t).2 (pow_nonneg ha0.le _)
  have hi := kernel_series P π h F hF _ hb hbound k i
  have he : (fun j => ∑' t, F t j) = Jstar P g α := by
    funext j
    exact (discounted_series P π g α ha0 ha1 h hg j).tsum_eq
  change HasSum (fun t => ∫ j, α^t * (∫ z, gbar P g z ∂((P^t) j)) ∂((P^k) i))
    (∫ j, (fun j => ∑' t, F t j) j ∂((P^k) i)) at hi
  rw [he] at hi
  simp_rw [integral_const_mul, power_mean_comp P π g h hg] at hi
  have ht : HasSum (fun t => α^(t+k) * ∫ j, gbar P g j ∂((P^(t+k)) i))
      (α^k * ∫ j, Jstar P g α j ∂((P^k) i)) := by
    have hfun : (fun t : ℕ => α^(t+k) * ∫ j, gbar P g j ∂((P^(t+k)) i)) =
        (fun t : ℕ => α^k * (α^t * ∫ j, gbar P g j ∂((P^(t+k)) i))) := by
      funext t
      rw [pow_add]
      ring
    rw [hfun]
    exact hi.mul_left (α^k)
  exact ht.sum_range_add.unique (discounted_series P π g α ha0 ha1 h hg i)

lemma value_fixed (g : S → S → ℝ) (α : ℝ) (ha0 : 0 < α) (ha1 : α < 1)
    (h : Assumption1 P π g α) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    Tlam P g α lam (Jstar P g α) = Jstar P g α := by
  by_cases he : lam = 1
  · simp [Tlam, he]
  have hl : lam < 1 := lt_of_le_of_ne hlam.2 he
  have hv := value_memL2 P π g α ha0 ha1 h.a h.b
  funext i
  have hs := (accepted_lemma_three P π g α ha0 ha1 h _ hv lam hlam).2.2 hl i
  simp_rw [value_tail P π g α ha0 ha1 h.a h.b] at hs
  have hg := ((hasSum_geometric_of_lt_one hlam.1 hl).mul_left (1-lam)).mul_right
    (Jstar P g α i)
  have hden : 1-lam ≠ 0 := (sub_pos.mpr hl).ne'
  simpa only [mul_inv_cancel₀ hden, one_mul] using hs.unique hg

end MarkovBellman

theorem solution {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    (∀ J, MemL2D π J → MemL2D π (proj π φ (Tlam P g α lam J))) ∧
    (∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ J Jb, MemL2D π J → MemL2D π Jb →
      normD π (proj π φ (Tlam P g α lam J) - proj π φ (Tlam P g α lam Jb)) ≤
        c * normD π (J - Jb)) ∧
    ∃ rstar : Fin K → ℝ,
      proj π φ (Tlam P g α lam (Jtilde φ rstar)) = Jtilde φ rstar ∧
      (∀ J, MemL2D π J → proj π φ (Tlam P g α lam J) = J → J = Jtilde φ rstar) ∧
      (∀ r, proj π φ (Tlam P g α lam (Jtilde φ r)) = Jtilde φ r → r = rstar) ∧
      normD π (Jtilde φ rstar - Jstar P g α) ≤
        normD π (proj π φ (Jstar P g α) - Jstar P g α) /
          (1 - α * (1 - lam) / (1 - α * lam)) := by
  obtain ⟨hm, hc, r, hr, hu, hur, hb⟩ :=
    local_projection_residual P π g α hα0 hα1 φ h1 h2 lam hlam
  refine ⟨hm, hc, r, hr, hu, hur, ?_⟩
  simpa only [MarkovBellman.value_fixed P π g α hα0 hα1 h1 lam hlam] using
    hb (Jstar P g α) (MarkovTrajectory.value_memL2 P π g α hα0 hα1 h1.a h1.b)
#print axioms solution
