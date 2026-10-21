-- Prove2me | solution 1 for TDApprox.Conv.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T14:53:50.646474+00:00
-- url     : https://prove2.me/submissions/d3a95aad-f7e6-423f-b0a3-655878223186

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

theorem solution {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
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
#print axioms solution
