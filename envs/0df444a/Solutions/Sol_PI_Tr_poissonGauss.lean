-- Prove2me | solution 1 for PI.Tr.poissonGauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:18.912603+00:00
-- url     : https://prove2.me/submissions/35979a61-d48b-471c-b5a6-d16a9c60496c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_InstIsZLatticeDualLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Poisson
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_PI_Tr_mem_dualLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open Module
open scoped Real
noncomputable section
namespace PI.Tr
private theorem summable_exp_neg_mul_norm_add_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a)
    (w : E) : Summable fun z : L => Real.exp (-a * ‖(z : E) + w‖ ^ 2) := by
  classical
  set N : ℕ := finrank ℤ L + 1 with hN
  have hr : (-(N : ℝ)) < -(finrank ℤ L : ℝ) := by
    rw [hN]
    push_cast
    linarith
  have hs := ZLattice.summable_norm_sub_rpow L (-(N : ℝ)) hr (-w)
  set C : ℝ := max 1 ((N.factorial : ℝ) / a ^ N) with hC
  have key : ∀ u : ℝ, 0 < u → Real.exp (-a * u ^ 2) ≤ C * u ^ (-(N : ℝ)) := by
    intro u hu
    rw [Real.rpow_neg hu.le, Real.rpow_natCast]
    have hinv : 0 ≤ (u ^ N)⁻¹ := by positivity
    rcases le_or_gt u 1 with h1 | h1
    · have h2 : 1 ≤ (u ^ N)⁻¹ := (one_le_inv₀ (pow_pos hu N)).2 (pow_le_one₀ hu.le h1)
      have h3 : Real.exp (-a * u ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
      calc Real.exp (-a * u ^ 2) ≤ 1 := h3
        _ ≤ 1 * (u ^ N)⁻¹ := by linarith
        _ ≤ C * (u ^ N)⁻¹ := by
          gcongr
          exact le_max_left _ _
    · have h2 : (a * u) ^ N / (N.factorial : ℝ) ≤ Real.exp (a * u) :=
        Real.pow_div_factorial_le_exp _ (by positivity) N
      have h3 : Real.exp (a * u) ≤ Real.exp (a * u ^ 2) := Real.exp_le_exp.2 (by
        have hu2 : u ≤ u ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hu2 ha.le)
      rw [show -a * u ^ 2 = -(a * u ^ 2) by ring, Real.exp_neg]
      have hpos : 0 < (a * u) ^ N / (N.factorial : ℝ) := by positivity
      calc (Real.exp (a * u ^ 2))⁻¹ ≤ ((a * u) ^ N / (N.factorial : ℝ))⁻¹ :=
            inv_anti₀ hpos (h2.trans h3)
        _ = ((N.factorial : ℝ) / a ^ N) * (u ^ N)⁻¹ := by
          rw [mul_pow]
          field_simp
        _ ≤ C * (u ^ N)⁻¹ := by
          gcongr
          exact le_max_right _ _
  refine Summable.of_nonneg_of_le (fun z => (Real.exp_pos _).le)
    (f := fun z : L => C * ‖(z : E) - -w‖ ^ (-(N : ℝ)) + (if (z : E) + w = 0 then 1 else 0)) ?_ ?_
  · intro z
    by_cases hz : (z : E) + w = 0
    · have h0 : ‖(z : E) - -w‖ ^ (-(N : ℝ)) = 0 := by
        rw [sub_neg_eq_add, hz, norm_zero, Real.zero_rpow]
        have : (0 : ℝ) < N := by positivity
        linarith
      simp [hz, h0]
    · have hu : 0 < ‖(z : E) + w‖ := norm_pos_iff.2 hz
      simp only [hz, if_false, add_zero, sub_neg_eq_add]
      exact key _ hu
  · refine (hs.mul_left C).add ?_
    apply summable_of_finite_support
    apply Set.Subsingleton.finite
    intro z1 h1 z2 h2
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at h1 h2
    apply Subtype.ext
    rw [eq_neg_of_add_eq_zero_left h1, eq_neg_of_add_eq_zero_left h2]
private theorem isQuotientMap_coe_unitAddTorus (ι : Type) [Fintype ι] :
    Topology.IsQuotientMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) := by
  have hopen : IsOpenMap (fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  refine hopen.isQuotientMap (by fun_prop) ?_
  intro θ
  refine ⟨fun i => Function.surjInv QuotientAddGroup.mk_surjective (θ i), ?_⟩
  funext i
  exact Function.surjInv_eq QuotientAddGroup.mk_surjective (θ i)
private theorem exists_continuous_torus_lift_of_periodic {ι : Type} [Fintype ι] (G : (ι → ℝ) → ℂ) (hG : Continuous G)
    (hper : ∀ (s : ι → ℝ) (k : ι → ℤ), G (s + fun i => (k i : ℝ)) = G s) :
    ∃ F : C(UnitAddTorus ι, ℂ), ∀ s : ι → ℝ,
      F (fun i => ((s i : ℝ) : UnitAddCircle)) = G s := by
  have hq := isQuotientMap_coe_unitAddTorus ι
  have hfib : ∀ x y : ι → ℝ, (fun i => ((x i : ℝ) : UnitAddCircle)) =
      (fun i => ((y i : ℝ) : UnitAddCircle)) → G x = G y := by
    intro x y hxy
    have hk : ∀ i, ∃ k : ℤ, y i = x i + k := by
      intro i
      have h := congr_fun hxy i
      rw [QuotientAddGroup.eq] at h
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
      refine ⟨k, ?_⟩
      simp only [zsmul_eq_mul, mul_one] at hk
      linarith
    choose k hk using hk
    have hy : y = x + fun i => (k i : ℝ) := funext hk
    rw [hy, hper]
  let F0 : UnitAddTorus ι → ℂ := fun θ => G (Function.surjInv hq.surjective θ)
  have hF0 : ∀ s : ι → ℝ, F0 (fun i => ((s i : ℝ) : UnitAddCircle)) = G s := fun s =>
    hfib _ _ (Function.surjInv_eq hq.surjective _)
  have hcont : Continuous F0 := by
    rw [hq.continuous_iff]
    have hcomp : (F0 ∘ fun (s : ι → ℝ) (i : ι) => ((s i : ℝ) : UnitAddCircle)) = G := funext hF0
    rw [hcomp]
    exact hG
  exact ⟨⟨F0, hcont⟩, hF0⟩
private theorem mFourierCoeff_periodization_eq_integral {ι : Type} [Fintype ι] (h : (ι → ℝ) → ℂ) (hh : MeasureTheory.Integrable h)
    (hcont : Continuous h) (F : C(UnitAddTorus ι, ℂ))
    (hF : ∀ s : ι → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, h (s + fun i => (k i : ℝ)))
    (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff F m =
      ∫ s, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) * h s := by
  set ψ : (ι → ℝ) → ℂ := fun s => UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle))
    with hψ
  have hqper : ∀ (s : ι → ℝ) (k : ι → ℤ),
      (fun i => (((s + fun i => (k i : ℝ)) i : ℝ) : UnitAddCircle)) =
        fun i => ((s i : ℝ) : UnitAddCircle) := by
    intro s k
    funext i
    rw [QuotientAddGroup.eq]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨-k i, ?_⟩
    rw [zsmul_eq_mul, mul_one, Pi.add_apply]
    push_cast
    ring
  have hψcont : Continuous ψ :=
    (UnitAddTorus.mFourier (-m)).continuous.comp (isQuotientMap_coe_unitAddTorus ι).continuous
  have hψle : ∀ s, ‖ψ s‖ ≤ 1 := by
    intro s
    have := (UnitAddTorus.mFourier (-m)).norm_coe_le_norm (fun i => ((s i : ℝ) : UnitAddCircle))
    rwa [UnitAddTorus.mFourier_norm] at this
  set S : (ι → ℤ) → Set (ι → ℝ) := fun k => {s | ∀ i, s i ∈ Set.Ioc (k i : ℝ) (k i + 1)} with hSdef
  have hSmeas : ∀ k, MeasurableSet (S k) := by
    intro k
    have hS : S k = ⋂ i, (fun s : ι → ℝ => s i) ⁻¹' Set.Ioc (k i : ℝ) (k i + 1) := by
      ext s
      simp [S]
    rw [hS]
    exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioc
  have hSmem : ∀ k s, s ∈ S k ↔ ∀ i, ⌈s i⌉ = k i + 1 := by
    intro k s
    simp only [S, Set.mem_setOf_eq, Set.mem_Ioc]
    refine forall_congr' fun i => ?_
    rw [Int.ceil_eq_iff]
    push_cast
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, h2⟩
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    intro k k' hne
    rw [Function.onFun, Set.disjoint_left]
    intro s h1 h2
    apply hne
    funext i
    have e1 := (hSmem k s).1 h1 i
    have e2 := (hSmem k' s).1 h2 i
    omega
  have hSunion : (⋃ k, S k) = Set.univ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨fun i => ⌈s i⌉ - 1, (hSmem _ s).2 fun i => by ring⟩
  have hS0 : S 0 = {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    ext s
    simp [S]
  have htrans : ∀ k : ι → ℤ, (fun s => s + fun i => (k i : ℝ)) ⁻¹' S k = S 0 := by
    intro k
    ext s
    simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc, Pi.add_apply, Pi.zero_apply,
      Int.cast_zero, zero_add]
    constructor
    · intro hs i
      have := hs i
      constructor <;> linarith [this.1, this.2]
    · intro hs i
      have := hs i
      constructor <;> linarith [this.1, this.2]
  have hmp : ∀ k : ι → ℤ, MeasureTheory.MeasurePreserving (fun s : ι → ℝ => s + fun i => (k i : ℝ))
      MeasureTheory.volume MeasureTheory.volume := fun k =>
        MeasureTheory.measurePreserving_add_right MeasureTheory.volume _
  have hme : ∀ k : ι → ℤ, MeasurableEmbedding (fun s : ι → ℝ => s + fun i => (k i : ℝ)) :=
    fun k => (Homeomorph.addRight _).measurableEmbedding
  have hfi : MeasureTheory.Integrable (fun s => ψ s * h s) := by
    refine MeasureTheory.Integrable.mono' hh.norm (hψcont.mul hcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    calc ‖ψ s‖ * ‖h s‖ ≤ 1 * ‖h s‖ := by gcongr; exact hψle s
      _ = ‖h s‖ := one_mul _
  rw [UnitAddTorus.mFourierCoeff_eq_integral F m 0, ← hS0]
  have hint : ∀ s : ι → ℝ, UnitAddTorus.mFourier (-m) (fun i => ((s i : ℝ) : UnitAddCircle)) •
      F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) := by
    intro s
    rw [hF, smul_eq_mul, ← tsum_mul_left]
    congr 1
    funext k
    simp only [ψ, hqper]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint)]
  rw [MeasureTheory.integral_tsum]
  · have hEach : ∀ k : ι → ℤ, ∫ s in S 0, ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ)) =
        ∫ s in S k, ψ s * h s := by
      intro k
      rw [← htrans k]
      exact (hmp k).setIntegral_preimage_emb (hme k) (fun s => ψ s * h s) (S k)
    simp_rw [hEach]
    have hsum := MeasureTheory.hasSum_integral_iUnion hSmeas hSdisj hfi.integrableOn
    rw [hSunion, MeasureTheory.Measure.restrict_univ] at hsum
    exact hsum.tsum_eq
  · intro k
    exact ((hψcont.mul hcont).comp (continuous_add_right _)).aestronglyMeasurable
  · have hEach : ∀ k : ι → ℤ, ∫⁻ s in S 0,
        ‖ψ (s + fun i => (k i : ℝ)) * h (s + fun i => (k i : ℝ))‖ₑ = ∫⁻ s in S k, ‖ψ s * h s‖ₑ := by
      intro k
      rw [← htrans k]
      exact (hmp k).setLIntegral_comp_preimage_emb (hme k) (fun s => ‖ψ s * h s‖ₑ) (S k)
    simp_rw [hEach]
    rw [← MeasureTheory.lintegral_iUnion hSmeas hSdisj, hSunion, MeasureTheory.Measure.restrict_univ]
    exact hfi.hasFiniteIntegral.ne
private theorem mFourier_coe_eq_exp' {ι : Type} [Fintype ι] (m : ι → ℤ) (s : ι → ℝ) :
    UnitAddTorus.mFourier m (fun i => ((s i : ℝ) : UnitAddCircle)) =
      Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (s i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring
private theorem integral_fourier_gaussian_eq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type} [Fintype ι]
    (φ : E ≃L[ℝ] (ι → ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧ (∀ t : ℝ, 0 < t → MeasureTheory.Integrable
      (fun s : ι → ℝ => (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ))) ∧ ∀ t : ℝ, 0 < t → ∀ y : E,
      ∫ s : ι → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) *
          (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) =
        ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) * Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
  haveI : (MeasureTheory.Measure.map φ.symm MeasureTheory.volume).IsAddHaarMeasure :=
    φ.symm.isAddHaarMeasure_map _
  set ν : MeasureTheory.Measure E := MeasureTheory.Measure.map φ.symm MeasureTheory.volume with hνdef
  have hν := MeasureTheory.Measure.isAddLeftInvariant_eq_smul ν (MeasureTheory.volume : MeasureTheory.Measure E)
  set c := ν.addHaarScalarFactor MeasureTheory.volume with hcdef
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hν
    exact (NeZero.ne ν) hν
  refine ⟨(c : ℝ), NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc), fun t ht => ?_, fun t ht y => ?_⟩
  · have hg : MeasureTheory.Integrable (fun x : E => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) := by
      have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
        (b := ((π * t : ℝ) : ℂ)) (by simp; positivity) 0 (0 : E)
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [zero_mul, add_zero, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    have hgν : MeasureTheory.Integrable (fun x : E => (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ)) ν := by
      rw [hν]
      exact hg.smul_measure_nnreal
    exact (MeasureTheory.integrable_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv _).1 hgν
  have step1 : ∫ s : ι → ℝ, Complex.exp (-2 * π * Complex.I * (inner ℝ y (φ.symm s) : ℂ)) *
        (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) =
      ∫ x, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
        (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) ∂ν :=
    (MeasureTheory.integral_map_equiv φ.symm.toHomeomorph.toMeasurableEquiv
      (fun x => Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
        (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ))).symm
  rw [step1, hν, MeasureTheory.integral_smul_nnreal_measure]
  have step2 : ∀ x : E, Complex.exp (-2 * π * Complex.I * (inner ℝ y x : ℂ)) *
      (Real.exp (-π * t * ‖x‖ ^ 2) : ℂ) =
      Complex.exp (-((π * t : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 + (-2 * π * Complex.I) * (inner ℝ y x : ℂ)) := by
    intro x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [step2]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simp; positivity) _ y]
  have e1 : ((π : ℂ) / ((π * t : ℝ) : ℂ)) ^ ((finrank ℝ E : ℂ) / 2) =
      ((t ^ (-(finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((π : ℂ) / ((π * t : ℝ) : ℂ)) = ((t⁻¹ : ℝ) : ℂ) by
      push_cast
      field_simp]
    rw [show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    ring_nf
  have e2 : Complex.exp ((-2 * π * Complex.I) ^ 2 * (‖y‖ : ℂ) ^ 2 / (4 * ((π * t : ℝ) : ℂ))) =
      ((Real.exp (-π * ‖y‖ ^ 2 / t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e1, e2, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring
private theorem continuous_tsum_exp_neg_mul_norm_add_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Continuous fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2) := by
  rw [continuous_iff_continuousAt]
  intro v0
  have hs := summable_exp_neg_mul_norm_add_sq L (a := a / 2) (by positivity) v0
  have hon : ContinuousOn (fun v : E => ∑' z : L, Real.exp (-a * ‖(z : E) + v‖ ^ 2))
      (Metric.ball v0 1) := by
    refine continuousOn_tsum (fun z => by fun_prop) (hs.mul_left (Real.exp a)) ?_
    intro z v hv
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : ‖(z : E) + v0‖ ≤ ‖(z : E) + v‖ + ‖v - v0‖ := by
      have hzv : (z : E) + v0 = ((z : E) + v) - (v - v0) := by abel
      rw [hzv]
      exact norm_sub_le _ _
    have h2 : ‖v - v0‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have h3 := norm_nonneg ((z : E) + v)
    have h4 := norm_nonneg (v - v0)
    have h6 := norm_nonneg ((z : E) + v0)
    have h5 : ‖(z : E) + v0‖ ^ 2 ≤ 2 * ‖(z : E) + v‖ ^ 2 + 2 := by
      nlinarith [sq_nonneg (‖(z : E) + v‖ - ‖v - v0‖)]
    nlinarith [mul_le_mul_of_nonneg_left h5 ha.le]
  exact hon.continuousAt (Metric.ball_mem_nhds v0 one_pos)
private theorem exists_coords_zLattice_dual_basis {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∃ (ι : Type) (_ : Fintype ι) (φ : E ≃L[ℝ] (ι → ℝ)) (B : (ι → ℤ) ≃ Λ)
      (D : (ι → ℤ) ≃ dualLat Λ),
      (∀ k, ((B k : Λ) : E) = φ.symm (fun i => (k i : ℝ))) ∧
      (∀ m x, inner ℝ ((D m : dualLat Λ) : E) x = ∑ i, (m i : ℝ) * φ x i) := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := b.ofZLatticeBasis ℝ Λ
  let φ : E ≃L[ℝ] (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) := bR.equivFun.toContinuousLinearEquiv
  have hφ : ∀ x i, φ x i = bR.repr x i := fun x i => rfl
  let d : Module.Free.ChooseBasisIndex ℤ Λ → E :=
    fun i => (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (bR.coord i))
  have hd : ∀ i x, inner ℝ (d i) x = φ x i := by
    intro i x
    simp [d, hφ, InnerProductSpace.toDual_symm_apply, Basis.coord_apply]
  let y : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) → E := fun m => ∑ i, (m i : ℝ) • d i
  have hy : ∀ m x, inner ℝ (y m) x = ∑ i, (m i : ℝ) * φ x i := by
    intro m x
    simp [y, sum_inner, real_inner_smul_left, hd]
  have hφΛ : ∀ (x : Λ) i, φ (x : E) i = (b.repr x i : ℝ) := by
    intro x i
    rw [hφ, Basis.ofZLatticeBasis_repr_apply]
  have hmem : ∀ m, y m ∈ dualLat Λ := by
    intro m
    rw [mem_dualLat]
    intro x hx
    refine ⟨∑ i, m i * b.repr ⟨x, hx⟩ i, ?_⟩
    rw [real_inner_comm, hy]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hφΛ ⟨x, hx⟩ i]
  have hφb : ∀ j, φ (bR j) = Pi.single j 1 := by
    intro j
    funext i
    rw [hφ, Basis.repr_self]
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hinj : Function.Injective y := by
    intro m m' h
    funext j
    have h2 := congrArg (fun z => inner ℝ z (bR j)) h
    simp only [hy, hφb] at h2
    simp [Pi.single_apply] at h2
    exact_mod_cast h2
  have hsurj : ∀ z ∈ dualLat Λ, ∃ m, y m = z := by
    intro z hz
    rw [mem_dualLat] at hz
    have hbΛ : ∀ j, bR j ∈ Λ := by
      intro j
      rw [Basis.ofZLatticeBasis_apply]
      exact (b j).2
    choose n hn using fun j => hz (bR j) (hbΛ j)
    refine ⟨n, ?_⟩
    apply InnerProductSpace.ext_inner_left_basis bR
    intro j
    rw [real_inner_comm, hy, hφb, hn j]
    simp [Pi.single_apply]
  let D : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) ≃ dualLat Λ :=
    Equiv.ofBijective (fun m => ⟨y m, hmem m⟩)
      ⟨fun m m' h => hinj (congrArg Subtype.val h), fun z => by
        obtain ⟨m, hm⟩ := hsurj z.1 z.2
        exact ⟨m, Subtype.ext hm⟩⟩
  refine ⟨Module.Free.ChooseBasisIndex ℤ Λ, inferInstance, φ, b.equivFun.symm.toEquiv, D, ?_, ?_⟩
  · intro k
    apply φ.injective
    rw [φ.apply_symm_apply]
    funext i
    rw [hφΛ]
    have h3 := congr_fun (b.equivFun.apply_symm_apply k) i
    simp only [Basis.equivFun_apply] at h3
    exact_mod_cast h3
  · intro m x
    exact hy m x
end PI.Tr
end
end

set_option autoImplicit false
open Module
open scoped Real
noncomputable section
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution : PoissonGauss := by
  intro E _ _ _ Λ _ _
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨ι, _, φ, B, D, hB, hD⟩ := exists_coords_zLattice_dual_basis Λ
  obtain ⟨κ, hκ, hInt, hG⟩ := integral_fourier_gaussian_eq φ
  have sum1 : ∀ t : ℝ, 0 < t → ∀ v : E,
      Summable fun x : Λ => Real.exp (-π * t * ‖(x : E) + v‖ ^ 2) := by
    intro t ht v
    refine (summable_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity) v).congr fun z => ?_
    ring_nf
  have sum2 : ∀ t : ℝ, 0 < t →
      Summable fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t) := by
    intro t ht
    refine (summable_exp_neg_mul_norm_add_sq (dualLat Λ) (a := π / t) (by positivity) 0).congr fun z => ?_
    rw [add_zero]
    ring_nf
  refine ⟨sum1, sum2, κ, hκ, fun t ht v => ?_⟩
  set P : E → ℝ := fun w => ∑' x : Λ, Real.exp (-π * t * ‖(x : E) + w‖ ^ 2) with hP
  have hPcont : Continuous P := by
    refine (continuous_tsum_exp_neg_mul_norm_add_sq Λ (a := π * t) (by positivity)).congr fun w => ?_
    simp only [hP]
    congr 1
    funext x
    ring_nf
  have hPper : ∀ (w : E) (z : Λ), P (w + z) = P w := by
    intro w z
    have e0 := (Equiv.addRight z).tsum_eq (fun x : Λ => Real.exp (-π * t * ‖(x : E) + w‖ ^ 2))
    simp only [hP]
    rw [← e0]
    congr 1
    funext x
    simp only [Equiv.coe_addRight, Submodule.coe_add]
    congr 3
    abel_nf
  set G : (ι → ℝ) → ℂ := fun s => ((P (φ.symm s) : ℝ) : ℂ) with hGdef
  have hGcont : Continuous G := Complex.continuous_ofReal.comp (hPcont.comp φ.symm.continuous)
  have hGper : ∀ (s : ι → ℝ) (k : ι → ℤ), G (s + fun i => (k i : ℝ)) = G s := by
    intro s k
    simp only [hGdef, map_add, ← hB k]
    rw [hPper]
  obtain ⟨F, hF⟩ := exists_continuous_torus_lift_of_periodic G hGcont hGper
  set h : (ι → ℝ) → ℂ := fun s => (Real.exp (-π * t * ‖φ.symm s‖ ^ 2) : ℂ) with hhdef
  have hhcont : Continuous h :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_norm.comp φ.symm.continuous).pow 2)))
  have hFh : ∀ s : ι → ℝ, F (fun i => ((s i : ℝ) : UnitAddCircle)) =
      ∑' k : ι → ℤ, h (s + fun i => (k i : ℝ)) := by
    intro s
    rw [hF]
    simp only [hGdef, hP]
    rw [Complex.ofReal_tsum, ← B.tsum_eq]
    congr 1
    funext k
    simp only [hhdef, map_add, hB k, add_comm]
  have hcoef : ∀ m : ι → ℤ, UnitAddTorus.mFourierCoeff F m =
      ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) *
        Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) : ℝ) : ℂ) := by
    intro m
    rw [mFourierCoeff_periodization_eq_integral h (hInt t ht) hhcont F hFh m, ← hG t ht (D m)]
    congr 1
    funext s
    rw [mFourier_coe_eq_exp', hD, φ.apply_symm_apply]
    congr 2
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  have hsumc : Summable (UnitAddTorus.mFourierCoeff F) := by
    have e1 : UnitAddTorus.mFourierCoeff F = fun m => ((κ * t ^ (-(finrank ℝ E : ℝ) / 2) *
        Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) : ℝ) : ℂ) := funext hcoef
    rw [e1]
    apply Complex.summable_ofReal.2
    apply Summable.mul_left
    exact (D.summable_iff (f := fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t))).2 (sum2 t ht)
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumc
    (fun i => ((φ v i : ℝ) : UnitAddCircle))
  rw [hF] at hs
  simp only [hGdef, ContinuousLinearEquiv.symm_apply_apply] at hs
  have hre := Complex.reCLM.hasSum hs
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  have hterm : ∀ m : ι → ℤ, (UnitAddTorus.mFourierCoeff F m •
      UnitAddTorus.mFourier m (fun i => ((φ v i : ℝ) : UnitAddCircle))).re =
      κ * t ^ (-(finrank ℝ E : ℝ) / 2) * (Real.exp (-π * ‖((D m : dualLat Λ) : E)‖ ^ 2 / t) *
        Real.cos (2 * π * inner ℝ ((D m : dualLat Λ) : E) v)) := by
    intro m
    rw [hcoef, mFourier_coe_eq_exp', smul_eq_mul, Complex.re_ofReal_mul]
    have e2 : (2 * π * Complex.I * ∑ i, (m i : ℂ) * (φ v i : ℂ)) =
        ((2 * π * inner ℝ ((D m : dualLat Λ) : E) v : ℝ) : ℂ) * Complex.I := by
      rw [hD]
      push_cast
      ring
    rw [e2, Complex.exp_ofReal_mul_I_re]
    ring
  have hre2 : HasSum (fun y : dualLat Λ => κ * t ^ (-(finrank ℝ E : ℝ) / 2) *
      (Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * inner ℝ (y : E) v))) (P v) := by
    rw [← D.hasSum_iff]
    refine hre.congr_fun ?_
    intro m
    exact (hterm m).symm
  rw [← tsum_mul_left]
  exact hre2.tsum_eq.symm
end PI.Tr
