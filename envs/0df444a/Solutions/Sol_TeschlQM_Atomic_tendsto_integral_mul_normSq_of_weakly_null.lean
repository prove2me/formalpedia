-- Prove2me | solution 1 for TeschlQM.Atomic.tendsto_integral_mul_normSq_of_weakly_null
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:45:17.319435+00:00
-- url     : https://prove2.me/submissions/c3759616-7a7a-432f-9199-2904052eb771

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian

/-! D3b (Rellich-type local compactness) infrastructure for 7ab9d8bf. -/

set_option autoImplicit false

open MeasureTheory FourierTransform SchwartzMap Filter Topology
open scoped ContDiff

namespace HVZRel

section Inv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem continuous_fourierInv_of_integrable (f : E → ℂ) (hf1 : Integrable f) :
    Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous (L := -innerₗ E) Real.continuous_fourierChar
    (continuous_inner.neg) hf1

theorem pairing_fourierInv (f : E → ℂ) (hf1 : Integrable f) (u : 𝓢(E, ℂ)) :
    ∫ x, (𝓕⁻ u) x • f x = ∫ x, u x • 𝓕⁻ f x := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E)
      Real.continuous_fourierChar (continuous_inner.neg) (u.integrable (μ := volume)) hf1
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y; simp [real_inner_comm]
  have e1 : ∀ g : E → ℂ, VectorFourier.fourierIntegral 𝐞 volume (-innerₗ E) g = 𝓕⁻ g :=
    fun g => rfl
  rw [hflip, e1, e1] at this
  rw [SchwartzMap.fourierInv_coe]
  simpa using! this

theorem Lp_fourierInv_eq_integral (f : E → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (((Lp.fourierTransformₗᵢ E ℂ).symm (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      =ᵐ[volume] 𝓕⁻ f := by
  have key : ∀ u : 𝓢(E, ℂ),
      ∫ x, u x • ((Lp.fourierTransformₗᵢ E ℂ).symm (hf2.toLp f) : E → ℂ) x
        = ∫ x, u x • 𝓕⁻ f x := by
    intro u
    have h1 := congrArg (fun T : 𝓢'(E, ℂ) => T u)
      (Lp.fourierInv_toTemperedDistribution_eq (hf2.toLp f))
    simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.fourierInv_apply] at h1
    have h2 : ∫ x, (𝓕⁻ u) x • (hf2.toLp f : E → ℂ) x = ∫ x, (𝓕⁻ u) x • f x :=
      integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
    rw [← pairing_fourierInv f hf1 u, ← h2]
    exact h1.symm
  have hL : LocallyIntegrable
      (((Lp.fourierTransformₗᵢ E ℂ).symm (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hR : LocallyIntegrable (𝓕⁻ f) volume :=
    (continuous_fourierInv_of_integrable f hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hL hR (fun g hg hgs => ?_)
  have hgc : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hgcs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgs.comp_left Complex.ofReal_zero
  have := key (hgcs.toSchwartzMap hgc)
  simp only [Complex.real_smul]
  exact this

end Inv

section L2facts

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem norm_sq_eq_integral (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖(f : X → ℂ) x‖ ^ 2 ∂μ := by
  have h1 : (inner ℂ f f : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have h2 : (inner ℂ f f : ℂ) = ((∫ x, ‖(f : X → ℂ) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  exact_mod_cast h1.symm.trans h2

theorem integrable_norm_sq (f : Lp ℂ 2 μ) : Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) μ :=
  (Lp.memLp f).integrable_norm_pow (by norm_num)

end L2facts

section Energy

variable {ι : Type} [Fintype ι]

theorem energy_eq (ψ : (TeschlQM.Atomic.freeHamiltonian ι).domain) :
    inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
        (TeschlQM.Atomic.freeHamiltonian ι ψ) =
      ((∫ ξ, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 *
        ‖((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
          (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
            Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ‖ ^ 2 : ℝ) : ℂ)
      ∧ Integrable (fun ξ : EuclideanSpace ℝ ι => 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 *
        ‖((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
          (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
            Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ‖ ^ 2) := by
  set F := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  have hmem : MemLp (fun ξ : EuclideanSpace ℝ ι => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
      (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ) 2 volume :=
    ψ.2
  have hH : TeschlQM.Atomic.freeHamiltonian ι ψ = F.symm (hmem.toLp _) := rfl
  have hpt : (fun ξ => inner ℂ ((F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
        EuclideanSpace ℝ ι → ℂ) ξ) ((hmem.toLp _ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) ξ))
      =ᵐ[volume] fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 *
        ‖(F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [hmem.coeFn_toLp] with ξ hξ
    rw [hξ]
    simp only [RCLike.inner_apply]
    rw [mul_assoc, Complex.mul_conj']
    push_cast; ring
  have hint := L2.integrable_inner (𝕜 := ℂ) (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))))
    (hmem.toLp _)
  refine ⟨?_, ?_⟩
  · rw [hH, ← F.inner_map_map, F.apply_symm_apply, L2.inner_def, ← integral_complex_ofReal]
    exact integral_congr_ae hpt
  · have h2 := (hint.congr hpt)
    have h3 := h2.re
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using h3

end Energy

section Tail

variable {ι : Type} [Fintype ι]

theorem high_freq_le (g : EuclideanSpace ℝ ι → ℂ) (hg : Integrable (fun ξ => ‖g ξ‖ ^ 2))
    (hm : Integrable (fun ξ : EuclideanSpace ℝ ι => 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2))
    (K : ℝ) (hK : 0 < K) :
    ∫ ξ, Set.indicator {ξ : EuclideanSpace ℝ ι | K ≤ ‖ξ‖} (fun ξ => ‖g ξ‖ ^ 2) ξ
      ≤ (∫ ξ, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) / (4 * Real.pi ^ 2 * K ^ 2) := by
  have hc : 0 < 4 * Real.pi ^ 2 * K ^ 2 := by positivity
  rw [← integral_div]
  refine integral_mono (hg.indicator (measurableSet_le measurable_const measurable_norm))
    (hm.div_const _) (fun ξ => ?_)
  by_cases h : K ≤ ‖ξ‖
  · rw [Set.indicator_of_mem (show ξ ∈ {ξ : EuclideanSpace ℝ ι | K ≤ ‖ξ‖} from h)]
    rw [le_div_iff₀ hc]
    have hK2 : K ^ 2 ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ hK.le h 2
    have hn : 0 ≤ ‖g ξ‖ ^ 2 := by positivity
    have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hK2 (mul_nonneg hpi hn)]
  · rw [Set.indicator_of_notMem (show ξ ∉ {ξ : EuclideanSpace ℝ ι | K ≤ ‖ξ‖} from h)]
    positivity

end Tail

section Low

variable {ι : Type} [Fintype ι]

/-- `h_x(ξ) = 1_{|ξ|<K} e^{-2πi⟨ξ,x⟩}`. -/
noncomputable def hx (K : ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι → ℂ :=
  Set.indicator (Metric.ball (0 : EuclideanSpace ℝ ι) K)
    (fun ξ => Complex.exp (((-2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I))

theorem hx_memLp (K : ℝ) (x : EuclideanSpace ℝ ι) : MemLp (hx K x) 2 volume := by
  unfold hx
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ ι) K)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  refine MemLp.of_bound (C := 1) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.cexp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const)).aestronglyMeasurable
  · rw [Complex.norm_exp_ofReal_mul_I]

theorem low_memLp (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (K : ℝ) :
    MemLp (Set.indicator (Metric.ball (0 : EuclideanSpace ℝ ι) K) (g : EuclideanSpace ℝ ι → ℂ)) 2 volume :=
  (Lp.memLp g).indicator measurableSet_ball

theorem low_integrable (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (K : ℝ) :
    Integrable (Set.indicator (Metric.ball (0 : EuclideanSpace ℝ ι) K) (g : EuclideanSpace ℝ ι → ℂ)) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ ι) K)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  rw [integrable_indicator_iff measurableSet_ball]
  exact ((Lp.memLp g).restrict _).integrable (by norm_num)

theorem low_repr (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (K : ℝ) :
    (((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).symm ((low_memLp g K).toLp _) :
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ)
      =ᵐ[volume] fun x => inner ℂ ((hx_memLp K x).toLp _) g := by
  filter_upwards [Lp_fourierInv_eq_integral _ (low_integrable g K) (low_memLp g K)] with x hx'
  rw [hx', Real.fourierInv_eq', L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hx_memLp K x).coeFn_toLp] with ξ hξ
  rw [hξ]
  unfold hx
  by_cases hb : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ ι) K
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, smul_eq_mul, RCLike.inner_apply,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_comm (g ξ)]
    congr 2
    push_cast; ring
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, smul_zero, inner_zero_left]

end Low

section Assemble

theorem sq_inner_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (h g : H)
    (M2 B : ℝ) (hh : ‖h‖ ^ 2 = M2) (hg : ‖g‖ ≤ B) : ‖inner ℂ h g‖ ^ 2 ≤ M2 * B ^ 2 := by
  have h1 := norm_inner_le_norm (𝕜 := ℂ) h g
  have h3 : ‖g‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  calc ‖inner ℂ h g‖ ^ 2 ≤ (‖h‖ * ‖g‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ‖h‖ ^ 2 * ‖g‖ ^ 2 := mul_pow _ _ _
    _ ≤ M2 * B ^ 2 := by
        rw [hh]; exact mul_le_mul_of_nonneg_left h3 (by rw [← hh]; positivity)

theorem sq_norm_le_two (u v : ℂ) : ‖u‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  have h : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by simpa using norm_add_le v (u - v)
  have h2 : ‖u‖ ^ 2 ≤ (‖v‖ + ‖u - v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖v‖ - ‖u - v‖)]

theorem local_split {X : Type*} [MeasurableSpace X] {μ : Measure X} (s : Set X)
    (u v : Lp ℂ 2 μ) :
    ∫ x in s, ‖(u : X → ℂ) x‖ ^ 2 ∂μ ≤
      2 * ∫ x in s, ‖(v : X → ℂ) x‖ ^ 2 ∂μ + 2 * ‖u - v‖ ^ 2 := by
  have hu : Integrable (fun x => ‖(u : X → ℂ) x‖ ^ 2) (μ.restrict s) :=
    (integrable_norm_sq u).restrict
  have hv : Integrable (fun x => ‖(v : X → ℂ) x‖ ^ 2) (μ.restrict s) :=
    (integrable_norm_sq v).restrict
  have hw := integrable_norm_sq (u - v)
  have hw' : Integrable (fun x => ‖((u - v : Lp ℂ 2 μ) : X → ℂ) x‖ ^ 2) (μ.restrict s) :=
    hw.restrict
  calc ∫ x in s, ‖(u : X → ℂ) x‖ ^ 2 ∂μ
      ≤ ∫ x in s, (2 * ‖(v : X → ℂ) x‖ ^ 2 + 2 * ‖((u - v : Lp ℂ 2 μ) : X → ℂ) x‖ ^ 2) ∂μ := by
        refine integral_mono_ae hu ((hv.const_mul 2).add (hw'.const_mul 2)) ?_
        refine ae_restrict_of_ae ?_
        filter_upwards [Lp.coeFn_sub u v] with x hx
        show ‖(u : X → ℂ) x‖ ^ 2 ≤
          2 * ‖(v : X → ℂ) x‖ ^ 2 + 2 * ‖((u - v : Lp ℂ 2 μ) : X → ℂ) x‖ ^ 2
        rw [hx, Pi.sub_apply]
        exact sq_norm_le_two _ _
    _ = 2 * ∫ x in s, ‖(v : X → ℂ) x‖ ^ 2 ∂μ
          + 2 * ∫ x in s, ‖((u - v : Lp ℂ 2 μ) : X → ℂ) x‖ ^ 2 ∂μ := by
        rw [integral_add (hv.const_mul 2) (hw'.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        rw [norm_sq_eq_integral (u - v)]
        have := setIntegral_le_integral (s := s) hw (ae_of_all _ fun x => sq_nonneg _)
        linarith

variable {ι : Type} [Fintype ι]

theorem hx_norm_sq (K : ℝ) (x : EuclideanSpace ℝ ι) :
    ‖((hx_memLp K x).toLp _ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))‖ ^ 2 =
      ∫ ξ, (Metric.ball (0 : EuclideanSpace ℝ ι) K).indicator (fun _ => (1 : ℝ)) ξ := by
  rw [norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [(hx_memLp K x).coeFn_toLp] with ξ hξ
  rw [hξ]
  unfold hx
  by_cases hb : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ ι) K
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb, Complex.norm_exp_ofReal_mul_I, one_pow]
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb, norm_zero]; norm_num

theorem low_local_tendsto (ψ : ℕ → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
    (hw : ∀ φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
      Tendsto (fun n => inner ℂ φ (ψ n)) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ n, ‖ψ n‖ ≤ B) (K R : ℝ) :
    Tendsto (fun n => ∫ x in Metric.ball (0 : EuclideanSpace ℝ ι) R,
      ‖(((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).symm
        ((low_memLp (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ (ψ n)) K).toLp _) :
          Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2)
      atTop (𝓝 0) := by
  set F := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  set M2 := ∫ ξ, (Metric.ball (0 : EuclideanSpace ℝ ι) K).indicator (fun _ => (1 : ℝ)) ξ
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ ι) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hrep : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ n,
      ((F.symm ((low_memLp (F (ψ n)) K).toLp _) :
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) x
        = inner ℂ ((hx_memLp K x).toLp _) (F (ψ n)) :=
    ae_all_iff.2 fun n => low_repr (F (ψ n)) K
  have hinner : ∀ x n, inner ℂ ((hx_memLp K x).toLp _ :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (F (ψ n))
      = inner ℂ (F.symm ((hx_memLp K x).toLp _)) (ψ n) := by
    intro x n
    rw [← F.inner_map_map (F.symm _) (ψ n), F.apply_symm_apply]
  have e : (∫ x in Metric.ball (0 : EuclideanSpace ℝ ι) R, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← e]
  refine tendsto_integral_of_dominated_convergence (fun _ => M2 * B ^ 2) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact ((Lp.aestronglyMeasurable _).norm.pow 2).restrict
  · refine ae_restrict_of_ae ?_
    filter_upwards [hrep] with x hx'
    rw [hx' n, norm_pow, norm_norm]
    exact sq_inner_bound _ _ M2 B (hx_norm_sq K x) (by rw [F.norm_map]; exact hB n)
  · filter_upwards [ae_restrict_of_ae hrep] with x hx'
    simp only [hx', hinner x]
    have := (hw (F.symm ((hx_memLp K x).toLp _))).norm.pow 2
    rwa [norm_zero, zero_pow two_ne_zero] at this

theorem high_norm_sq_le (ψ : (TeschlQM.Atomic.freeHamiltonian ι).domain) (B K : ℝ) (hK : 0 < K)
    (hE : (inner ℂ (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
      (TeschlQM.Atomic.freeHamiltonian ι ψ)).re ≤ B) :
    ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) -
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).symm
        ((low_memLp (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
          (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).toLp _)‖ ^ 2
      ≤ B / (4 * Real.pi ^ 2 * K ^ 2) := by
  set F := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
  obtain ⟨h1, h2⟩ := energy_eq ψ
  rw [h1, Complex.ofReal_re] at hE
  have hn : ‖(ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) -
      F.symm ((low_memLp (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).toLp _)‖
      = ‖F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) -
        (low_memLp (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).toLp _‖ := by
    rw [← F.norm_map, map_sub, F.apply_symm_apply]
  rw [hn, norm_sq_eq_integral]
  have hpt : (fun ξ => ‖((F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) -
        (low_memLp (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).toLp _ :
          Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ‖ ^ 2)
      =ᵐ[volume] Set.indicator {ξ : EuclideanSpace ℝ ι | K ≤ ‖ξ‖}
        (fun ξ => ‖((F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
          Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) ξ‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))))
      ((low_memLp (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).toLp _),
      (low_memLp (F (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).coeFn_toLp]
      with ξ hs hl
    rw [hs, Pi.sub_apply, hl]
    by_cases hb : ξ ∈ Metric.ball (0 : EuclideanSpace ℝ ι) K
    · have h' : ¬ K ≤ ‖ξ‖ := by rw [mem_ball_zero_iff] at hb; exact not_le.2 hb
      rw [Set.indicator_of_mem hb, sub_self,
        Set.indicator_of_notMem (show ξ ∉ {ξ : EuclideanSpace ℝ ι | K ≤ ‖ξ‖} from h')]
      simp
    · have h' : K ≤ ‖ξ‖ := by rw [mem_ball_zero_iff] at hb; exact not_lt.1 hb
      rw [Set.indicator_of_notMem hb, sub_zero,
        Set.indicator_of_mem (show ξ ∈ {ξ : EuclideanSpace ℝ ι | K ≤ ‖ξ‖} from h')]
  rw [integral_congr_ae hpt]
  calc _ ≤ _ := high_freq_le _ (integrable_norm_sq _) h2 K hK
    _ ≤ B / (4 * Real.pi ^ 2 * K ^ 2) := by gcongr

theorem local_tendsto (ψ : ℕ → (TeschlQM.Atomic.freeHamiltonian ι).domain)
    (hw : ∀ φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)),
      Tendsto (fun n => inner ℂ φ (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))))
        atTop (𝓝 0))
    (B : ℝ) (hB : ∀ n, ‖(ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))‖ ≤ B ∧
      (inner ℂ (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
        (TeschlQM.Atomic.freeHamiltonian ι (ψ n))).re ≤ B) (R : ℝ) :
    Tendsto (fun n => ∫ x in Metric.ball (0 : EuclideanSpace ℝ ι) R,
      ‖((ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hKt : Tendsto (fun K : ℝ => 2 * (B / (4 * Real.pi ^ 2 * K ^ 2))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := B)).div_atTop
      ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop
        (show (0 : ℝ) < 4 * Real.pi ^ 2 by positivity))
    simpa using this.const_mul 2
  obtain ⟨K, hK1, hK0⟩ :=
    ((hKt.eventually (gt_mem_nhds (half_pos hδ))).and (eventually_gt_atTop 0)).exists
  have hlow := (low_local_tendsto
    (fun n => (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) hw B
    (fun n => (hB n).1) K R).const_mul 2
  rw [mul_zero] at hlow
  filter_upwards [hlow.eventually (gt_mem_nhds (half_pos hδ))] with n hn
  have hs := local_split (Metric.ball (0 : EuclideanSpace ℝ ι) R)
    (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
    ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ).symm
        ((low_memLp (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ ι) ℂ
          (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) K).toLp _))
  have hh := high_norm_sq_le (ψ n) B K hK0 (hB n).2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)]
  linarith

theorem W_bound (W : EuclideanSpace ℝ ι → ℝ) (C ε R : ℝ) (hε : 0 ≤ ε)
    (hC : ∀ x, |W x| ≤ C) (hR : ∀ x, R ≤ ‖x‖ → |W x| ≤ ε)
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    ‖∫ x, W x * ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2‖ ≤
      (C * ∫ x in Metric.ball (0 : EuclideanSpace ℝ ι) R, ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2)
        + ε * ‖g‖ ^ 2 := by
  have hi := integrable_norm_sq g
  have hi1 := (hi.indicator (measurableSet_ball (x := (0 : EuclideanSpace ℝ ι)) (ε := R))).const_mul C
  have hi2 := hi.const_mul ε
  have hbound : ∀ x, ‖W x * ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2‖ ≤
      C * (Metric.ball (0 : EuclideanSpace ℝ ι) R).indicator
        (fun x => ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2) x
        + ε * ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2 := by
    intro x
    rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
    have hf0 : 0 ≤ ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2 := by positivity
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ ι) R
    · rw [Set.indicator_of_mem hx]
      nlinarith [mul_le_mul_of_nonneg_right (hC x) hf0, mul_nonneg hε hf0]
    · rw [Set.indicator_of_notMem hx, mul_zero, zero_add]
      have h' : R ≤ ‖x‖ := by rw [mem_ball_zero_iff, not_lt] at hx; exact hx
      exact mul_le_mul_of_nonneg_right (hR x h') hf0
  have hint : Integrable (fun x => C * (Metric.ball (0 : EuclideanSpace ℝ ι) R).indicator
        (fun x => ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2) x
        + ε * ‖(g : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2) volume := hi1.add hi2
  have h1 := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_ball, ← norm_sq_eq_integral] at h1
  exact h1

end Assemble

end HVZRel

open TeschlQM.Atomic in
theorem solution (ι : Type) [Fintype ι]
    (W : EuclideanSpace ℝ ι → ℝ) (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, |W x| ≤ C)
    (hWt : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → |W x| ≤ ε)
    (ψ : ℕ → (freeHamiltonian ι).domain)
    (hw : ∀ φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)), Tendsto (fun n => inner ℂ φ (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))) atTop (nhds 0))
    (hb : ∃ B : ℝ, ∀ n, ‖(ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))‖ ≤ B ∧
      (inner ℂ (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (freeHamiltonian ι (ψ n))).re ≤ B) :
    Tendsto (fun n => ∫ x, W x * ‖((ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) : EuclideanSpace ℝ ι → ℂ) x‖ ^ 2) atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hWb
  obtain ⟨B, hB⟩ := hb
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set ε := δ / (2 * (B ^ 2 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hεB : ε * B ^ 2 < δ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨R, hR⟩ := hWt ε hε0
  have hloc := (HVZRel.local_tendsto ψ hw B hB R).const_mul C
  rw [mul_zero] at hloc
  filter_upwards [hloc.eventually (gt_mem_nhds (half_pos hδ))] with n hn
  have h1 := HVZRel.W_bound W C ε R hε0.le hC hR
    (ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))
  have h2 : ‖(ψ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)))‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hB n).1 2
  rw [dist_zero_right]
  nlinarith [mul_le_mul_of_nonneg_left h2 hε0.le]
