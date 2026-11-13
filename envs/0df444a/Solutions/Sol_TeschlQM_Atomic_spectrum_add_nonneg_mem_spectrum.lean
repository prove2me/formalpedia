-- Prove2me | solution 1 for TeschlQM.Atomic.spectrum_add_nonneg_mem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:47:36.722198+00:00
-- url     : https://prove2.me/submissions/041d39e2-040c-4acb-85cf-f5a25e831793

import Mathlib
import Definitions.Def_TeschlQM_Atomic_atomicHamiltonian
import Definitions.Def_TeschlQM_Atomic_freeHamiltonian
import Definitions.Def_TeschlQM_Atomic_mulOp
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_resolventSet

section


/-! L¹ ∩ L² agreement of the `L²` Fourier transform with the integral Fourier transform. -/

set_option autoImplicit false

open MeasureTheory FourierTransform SchwartzMap
open scoped ContDiff

namespace HVZHyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem continuous_fourier_of_integrable (f : E → ℂ) (hf1 : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (L := innerₗ E) Real.continuous_fourierChar
    continuous_inner hf1

theorem pairing_fourier (f : E → ℂ) (hf1 : Integrable f) (u : 𝓢(E, ℂ)) :
    ∫ x, (𝓕 u) x • f x = ∫ x, u x • 𝓕 f x := by
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ E)
      Real.continuous_fourierChar continuous_inner u.integrable hf1)

theorem Lp_fourier_eq_integral (f : E → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (((Lp.fourierTransformₗᵢ E ℂ) (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      =ᵐ[volume] 𝓕 f := by
  have key : ∀ u : 𝓢(E, ℂ),
      ∫ x, u x • ((Lp.fourierTransformₗᵢ E ℂ) (hf2.toLp f) : E → ℂ) x = ∫ x, u x • 𝓕 f x := by
    intro u
    have h1 := congrArg (fun T : 𝓢'(E, ℂ) => T u)
      (Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
    simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.fourier_apply] at h1
    have h2 : ∫ x, (𝓕 u) x • (hf2.toLp f : E → ℂ) x = ∫ x, (𝓕 u) x • f x :=
      integral_congr_ae (by filter_upwards [hf2.coeFn_toLp] with x hx; rw [hx])
    rw [← pairing_fourier f hf1 u, ← h2]
    exact h1.symm
  have hL : LocallyIntegrable
      (((Lp.fourierTransformₗᵢ E ℂ) (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hR : LocallyIntegrable (𝓕 f) volume :=
    (continuous_fourier_of_integrable f hf1).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hL hR (fun g hg hgs => ?_)
  have hgc : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hgcs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := by
    have h := hgs.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
    exact h
  have := key (hgcs.toSchwartzMap hgc)
  simp only [Complex.real_smul, smul_eq_mul]
  exact this

end HVZHyd

namespace HVZTen

open MeasureTheory FourierTransform SchwartzMap

theorem norm_sq_L2 {Y : Type*} [MeasureSpace Y] (f : Lp ℂ 2 (volume : Measure Y)) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : Y → ℂ) x‖ ^ 2 := by
  rewrite [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_self_eq_norm_sq_to_K]; norm_cast

variable {A B X : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A]
  [BorelSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B]
  [BorelSpace B]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]

theorem prod_memLp (f : A → ℂ) (g : B → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun p : A × B => f p.1 * g p.2) 2 (volume : Measure (A × B)) := by
  have hm : AEStronglyMeasurable (fun p : A × B => f p.1 * g p.2) (volume : Measure (A × B)) :=
    (hf.1.comp_fst (ν := (volume : Measure B))).mul (hg.1.comp_snd (μ := (volume : Measure A)))
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  have h1 := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have h2 := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  simp [norm_mul, mul_pow]

variable (e : X ≃ᵐ A × B)

/-- the tensor product function -/
def tfun (f : A → ℂ) (g : B → ℂ) : X → ℂ := fun x => f (e x).1 * g (e x).2

variable {e}

theorem tfun_memLp (he : MeasurePreserving e) {f : A → ℂ} {g : B → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) : MemLp (tfun e f g) 2 volume :=
  (prod_memLp f g hf hg).comp_measurePreserving he

theorem tfun_integrable (he : MeasurePreserving e) {f : A → ℂ} {g : B → ℂ}
    (hf : Integrable f) (hg : Integrable g) : Integrable (tfun e f g) :=
  memLp_one_iff_integrable.1
    ((memLp_one_iff_integrable.2 (hf.mul_prod hg)).comp_measurePreserving he)

theorem tfun_congr (he : MeasurePreserving e) {f f' : A → ℂ} {g g' : B → ℂ}
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') : tfun e f g =ᵐ[volume] tfun e f' g' := by
  have h1 : (fun p : A × B => f p.1) =ᵐ[volume] (fun p => f' p.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure A))
      (ν := (volume : Measure B))).ae_eq_comp hf
  have h2 : (fun p : A × B => g p.2) =ᵐ[volume] (fun p => g' p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure A))
      (ν := (volume : Measure B))).ae_eq_comp hg
  exact he.quasiMeasurePreserving.ae_eq_comp (h1.mul h2)

theorem integral_tfun_sq (he : MeasurePreserving e) (f : A → ℂ) (g : B → ℂ) :
    ∫ x, ‖tfun e f g x‖ ^ 2 = (∫ a, ‖f a‖ ^ 2) * ∫ b, ‖g b‖ ^ 2 := by
  rw [← integral_prod_mul, ← Measure.volume_eq_prod, ← he.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [tfun, norm_mul, mul_pow]

/-- the `L²` tensor product -/
noncomputable def T (he : MeasurePreserving e) (f : Lp ℂ 2 (volume : Measure A))
    (g : Lp ℂ 2 (volume : Measure B)) : Lp ℂ 2 (volume : Measure X) :=
  (tfun_memLp he (Lp.memLp f) (Lp.memLp g)).toLp _

theorem coeFn_T (he : MeasurePreserving e) (f : Lp ℂ 2 (volume : Measure A))
    (g : Lp ℂ 2 (volume : Measure B)) : (T he f g : X → ℂ) =ᵐ[volume] tfun e f g :=
  MemLp.coeFn_toLp _

theorem norm_T (he : MeasurePreserving e) (f : Lp ℂ 2 (volume : Measure A))
    (g : Lp ℂ 2 (volume : Measure B)) : ‖T he f g‖ = ‖f‖ * ‖g‖ := by
  have h : ‖T he f g‖ ^ 2 = (‖f‖ * ‖g‖) ^ 2 := by
    rw [norm_sq_L2, mul_pow, norm_sq_L2, norm_sq_L2, ← integral_tfun_sq he]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_T he f g] with x hx
    rw [hx]
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    two_ne_zero).1 h

theorem T_sub_left (he : MeasurePreserving e) (f f' : Lp ℂ 2 (volume : Measure A))
    (g : Lp ℂ 2 (volume : Measure B)) : T he (f - f') g = T he f g - T he f' g := by
  apply Lp.ext
  filter_upwards [coeFn_T he (f - f') g, Lp.coeFn_sub (T he f g) (T he f' g), coeFn_T he f g,
    coeFn_T he f' g, tfun_congr he (Lp.coeFn_sub f f') (ae_eq_refl (g : B → ℂ))]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, h5]
  simp [tfun, sub_mul]

theorem T_sub_right (he : MeasurePreserving e) (f : Lp ℂ 2 (volume : Measure A))
    (g g' : Lp ℂ 2 (volume : Measure B)) : T he f (g - g') = T he f g - T he f g' := by
  apply Lp.ext
  filter_upwards [coeFn_T he f (g - g'), Lp.coeFn_sub (T he f g) (T he f g'), coeFn_T he f g,
    coeFn_T he f g', tfun_congr he (ae_eq_refl (f : A → ℂ)) (Lp.coeFn_sub g g')]
    with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, h3, h4, h5]
  simp [tfun, mul_sub]

theorem continuous_T_left (he : MeasurePreserving e) (g : Lp ℂ 2 (volume : Measure B)) :
    Continuous (fun f : Lp ℂ 2 (volume : Measure A) => T he f g) := by
  refine (LipschitzWith.of_dist_le_mul (K := ‖g‖₊) fun f f' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← T_sub_left, norm_T, coe_nnnorm, mul_comm]

theorem continuous_T_right (he : MeasurePreserving e) (f : Lp ℂ 2 (volume : Measure A)) :
    Continuous (fun g : Lp ℂ 2 (volume : Measure B) => T he f g) := by
  refine (LipschitzWith.of_dist_le_mul (K := ‖f‖₊) fun g g' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← T_sub_right, norm_T, coe_nnnorm]

theorem fourier_tfun (he : MeasurePreserving e)
    (hinner : ∀ x ξ : X, inner ℝ x ξ = inner ℝ (e x).1 (e ξ).1 + inner ℝ (e x).2 (e ξ).2)
    (f : A → ℂ) (g : B → ℂ) (ξ : X) :
    𝓕 (tfun e f g) ξ = 𝓕 f (e ξ).1 * 𝓕 g (e ξ).2 := by
  rw [Real.fourier_eq' (tfun e f g), Real.fourier_eq' f, Real.fourier_eq' g, ← integral_prod_mul,
    ← Measure.volume_eq_prod, ← he.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [tfun, hinner, smul_eq_mul]
  have : ((-2 * Real.pi * (inner ℝ (e x).1 (e ξ).1 + inner ℝ (e x).2 (e ξ).2) : ℝ) : ℂ) *
      Complex.I = ((-2 * Real.pi * inner ℝ (e x).1 (e ξ).1 : ℝ) : ℂ) * Complex.I +
      ((-2 * Real.pi * inner ℝ (e x).2 (e ξ).2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_add]; ring

theorem fourier_T_schwartz (he : MeasurePreserving e)
    (hinner : ∀ x ξ : X, inner ℝ x ξ = inner ℝ (e x).1 (e ξ).1 + inner ℝ (e x).2 (e ξ).2)
    (u : 𝓢(A, ℂ)) (v : 𝓢(B, ℂ)) :
    Lp.fourierTransformₗᵢ X ℂ (T he (u.toLp 2 volume) (v.toLp 2 volume)) =
      T he (Lp.fourierTransformₗᵢ A ℂ (u.toLp 2 volume)) (Lp.fourierTransformₗᵢ B ℂ (v.toLp 2 volume)) := by
  have hm : MemLp (tfun e (u : A → ℂ) (v : B → ℂ)) 2 volume :=
    tfun_memLp he (u.memLp 2 volume) (v.memLp 2 volume)
  have hu : ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure A)) : A → ℂ) =ᵐ[volume] u :=
    SchwartzMap.coeFn_toLp u 2 volume
  have hv : ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure B)) : B → ℂ) =ᵐ[volume] v :=
    SchwartzMap.coeFn_toLp v 2 volume
  have hm2 : (MemLp.toLp (tfun e (u : A → ℂ) (v : B → ℂ)) hm : X → ℂ) =ᵐ[volume]
      tfun e (u : A → ℂ) (v : B → ℂ) := MemLp.coeFn_toLp hm
  set U : Lp ℂ 2 (volume : Measure A) := u.toLp 2 volume with hU
  set V : Lp ℂ 2 (volume : Measure B) := v.toLp 2 volume with hV
  have hT : T he U V = MemLp.toLp (tfun e (u : A → ℂ) (v : B → ℂ)) hm := by
    apply Lp.ext
    have h1 : (T he U V : X → ℂ) =ᵐ[volume] tfun e (U : A → ℂ) (V : B → ℂ) := coeFn_T he U V
    have h3 := tfun_congr he hu hv
    exact h1.trans (h3.trans hm2.symm)
  have hFu : ((Lp.fourierTransformₗᵢ A ℂ U : Lp ℂ 2 (volume : Measure A)) : A → ℂ) =ᵐ[volume]
      𝓕 (u : A → ℂ) := HVZHyd.Lp_fourier_eq_integral _ u.integrable (u.memLp 2 volume)
  have hFv : ((Lp.fourierTransformₗᵢ B ℂ V : Lp ℂ 2 (volume : Measure B)) : B → ℂ) =ᵐ[volume]
      𝓕 (v : B → ℂ) := HVZHyd.Lp_fourier_eq_integral _ v.integrable (v.memLp 2 volume)
  apply Lp.ext
  rw [hT]
  have hF := HVZHyd.Lp_fourier_eq_integral _ (tfun_integrable he u.integrable v.integrable) hm
  have h2 := coeFn_T he (Lp.fourierTransformₗᵢ A ℂ U) (Lp.fourierTransformₗᵢ B ℂ V)
  have h3 := tfun_congr he hFu hFv
  refine hF.trans (Filter.EventuallyEq.trans ?_ (h2.trans h3).symm)
  exact Filter.Eventually.of_forall fun ξ => fourier_tfun he hinner _ _ ξ

theorem fourier_T (he : MeasurePreserving e)
    (hinner : ∀ x ξ : X, inner ℝ x ξ = inner ℝ (e x).1 (e ξ).1 + inner ℝ (e x).2 (e ξ).2)
    (f : Lp ℂ 2 (volume : Measure A)) (g : Lp ℂ 2 (volume : Measure B)) :
    Lp.fourierTransformₗᵢ X ℂ (T he f g) =
      T he (Lp.fourierTransformₗᵢ A ℂ f) (Lp.fourierTransformₗᵢ B ℂ g) := by
  have step1 : ∀ (f : Lp ℂ 2 (volume : Measure A)) (v : 𝓢(B, ℂ)),
      Lp.fourierTransformₗᵢ X ℂ (T he f (v.toLp 2 volume)) =
        T he (Lp.fourierTransformₗᵢ A ℂ f) (Lp.fourierTransformₗᵢ B ℂ (v.toLp 2 volume)) := by
    intro f v
    refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := A) (p := 2) (μ := volume)
      ENNReal.ofNat_ne_top).induction_on f (isClosed_eq ?_ ?_) ?_
    · exact (Lp.fourierTransformₗᵢ X ℂ).continuous.comp (continuous_T_left he _)
    · exact (continuous_T_left he _).comp (Lp.fourierTransformₗᵢ A ℂ).continuous
    · intro u
      exact fourier_T_schwartz he hinner u v
  refine (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := B) (p := 2) (μ := volume)
    ENNReal.ofNat_ne_top).induction_on g (isClosed_eq ?_ ?_) ?_
  · exact (Lp.fourierTransformₗᵢ X ℂ).continuous.comp (continuous_T_right he _)
  · exact (continuous_T_right he _).comp (Lp.fourierTransformₗᵢ B ℂ).continuous
  · intro v
    exact step1 f v

end HVZTen

open MeasureTheory TeschlQM.Atomic

namespace HVZE3

noncomputable def front {M : ℕ} (x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) :
    EuclideanSpace ℝ (Fin M × Fin 3) :=
  WithLp.toLp 2 (fun p : Fin M × Fin 3 => x (p.1.castSucc, p.2))

def E3a : Prop :=
  ∀ (M : ℕ) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))))
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))),
    ∃ F : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (M + 1) × Fin 3))),
      (F : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) → ℂ) =ᵐ[volume]
        (fun x => (f : _ → ℂ) (front x) * (g : _ → ℂ) (electron x (Fin.last M))) ∧
      ‖F‖ = ‖f‖ * ‖g‖ ∧
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) ℂ F :
          EuclideanSpace ℝ (Fin (M + 1) × Fin 3) → ℂ) =ᵐ[volume]
        (fun ξ => (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f : _ → ℂ) (front ξ) *
          (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g : _ → ℂ) (electron ξ (Fin.last M)))

end HVZE3

namespace HVZE3a

open HVZTen

noncomputable def Lmap (M : ℕ) : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) →ₗ[ℝ]
    WithLp 2 (EuclideanSpace ℝ (Fin M × Fin 3) × EuclideanSpace ℝ (Fin 3)) where
  toFun x := WithLp.toLp 2 (HVZE3.front x, electron x (Fin.last M))
  map_add' x y := rfl
  map_smul' c x := rfl

theorem Lmap_norm (M : ℕ) (x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) : ‖Lmap M x‖ = ‖x‖ := by
  have h : ‖Lmap M x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [EuclideanSpace.norm_sq_eq]
    conv_rhs => rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
    rw [Fintype.sum_prod_type]
    simp [Lmap, HVZE3.front, electron]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

noncomputable def Liso (M : ℕ) : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) ≃ₗᵢ[ℝ]
    WithLp 2 (EuclideanSpace ℝ (Fin M × Fin 3) × EuclideanSpace ℝ (Fin 3)) :=
  LinearIsometry.toLinearIsometryEquiv ⟨Lmap M, fun x => Lmap_norm M x⟩ (by
    rw [finrank_euclideanSpace, (WithLp.linearEquiv 2 ℝ
      (EuclideanSpace ℝ (Fin M × Fin 3) × EuclideanSpace ℝ (Fin 3))).finrank_eq,
      Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace]
    simp
    ring)

noncomputable def emap (M : ℕ) : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) ≃ᵐ
    EuclideanSpace ℝ (Fin M × Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (Liso M).toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm

theorem emap_apply (M : ℕ) (x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) :
    emap M x = (HVZE3.front x, electron x (Fin.last M)) := rfl

theorem emap_mp (M : ℕ) : MeasurePreserving (emap M) :=
  (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod _ _).comp (Liso M).measurePreserving

theorem emap_inner (M : ℕ) (x ξ : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) :
    inner ℝ x ξ = inner ℝ (emap M x).1 (emap M ξ).1 + inner ℝ (emap M x).2 (emap M ξ).2 := by
  rw [← (Liso M).inner_map_map x ξ, WithLp.prod_inner_apply]
  rfl

end HVZE3a

namespace HVZE3

/-- E3b kinetic energy of a tensor product -/
def E3b : Prop :=
  ∀ (M : ℕ) (f : (freeHamiltonian (Fin M × Fin 3)).domain) (g : (freeHamiltonian (Fin 3)).domain)
    (F : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)))),
    (F : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) → ℂ) =ᵐ[volume]
        (fun x => ((f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))) : _ → ℂ) (front x) *
          ((g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) : _ → ℂ) (electron x (Fin.last M))) →
    ∃ hF : F ∈ (freeHamiltonian (Fin (M + 1) × Fin 3)).domain,
      (freeHamiltonian (Fin (M + 1) × Fin 3) ⟨F, hF⟩ : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) → ℂ)
        =ᵐ[volume] fun x =>
          (freeHamiltonian (Fin M × Fin 3) f : _ → ℂ) (front x) *
            ((g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) : _ → ℂ) (electron x (Fin.last M)) +
          ((f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3)))) : _ → ℂ) (front x) *
            (freeHamiltonian (Fin 3) g : _ → ℂ) (electron x (Fin.last M))

end HVZE3

namespace HVZE3b

open HVZTen HVZE3a

theorem norm_sq_split (M : ℕ) (ξ : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) :
    ‖ξ‖ ^ 2 = ‖HVZE3.front ξ‖ ^ 2 + ‖electron ξ (Fin.last M)‖ ^ 2 := by
  rw [← Lmap_norm M ξ, WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem fourier_symm_T (M : ℕ) (a : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))))
    (b : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) ℂ).symm (T (emap_mp M) a b) =
      T (emap_mp M) ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ).symm a)
        ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ).symm b) := by
  rw [LinearIsometryEquiv.symm_apply_eq, fourier_T (emap_mp M) (emap_inner M)]
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem e3b : HVZE3.E3b := by
  intro M f g F hF
  obtain ⟨f, hfd⟩ := f
  obtain ⟨g, hgd⟩ := g
  have hfm : MemLp (fun ξ : EuclideanSpace ℝ (Fin M × Fin 3) =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f : _ → ℂ) ξ) 2 volume := hfd
  have hgm : MemLp (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g : _ → ℂ) ξ) 2 volume := hgd
  have hFT : F = T (emap_mp M) f g := by
    refine Lp.ext (hF.trans ((coeFn_T (emap_mp M) f g).trans
      (Filter.Eventually.of_forall fun x => ?_)).symm)
    simp only [tfun, emap_apply]
  subst hFT
  have hUF := fourier_T (emap_mp M) (emap_inner M) f g
  have hsum : (fun ξ : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) ℂ
          (T (emap_mp M) f g) : _ → ℂ) ξ) =ᵐ[volume]
      ((T (emap_mp M) (hfm.toLp _) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g) +
        T (emap_mp M) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f)
          (hgm.toLp _) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)))) :
        _ → ℂ) := by
    rw [hUF]
    have h1 := tfun_congr (emap_mp M) hfm.coeFn_toLp
      (Filter.EventuallyEq.refl (ae volume)
        ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g : _ → ℂ)))
    have h2 := tfun_congr (emap_mp M)
      (Filter.EventuallyEq.refl (ae volume)
        ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f : _ → ℂ)))
      hgm.coeFn_toLp
    filter_upwards [coeFn_T (emap_mp M) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f)
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g),
      Lp.coeFn_add (T (emap_mp M) (hfm.toLp _) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g))
        (T (emap_mp M) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f) (hgm.toLp _)),
      coeFn_T (emap_mp M) (hfm.toLp _) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g),
      coeFn_T (emap_mp M) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f) (hgm.toLp _),
      h1, h2] with ξ k0 k1 k2 k3 k4 k5
    rw [k0, k1, Pi.add_apply, k2, k3, k4, k5]
    simp only [tfun, emap_apply]
    rw [norm_sq_split M ξ]
    push_cast
    ring
  have hmem : MemLp (fun ξ : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) =>
      ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) *
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) ℂ
          (T (emap_mp M) f g) : _ → ℂ) ξ) 2 volume :=
    (Lp.memLp _).ae_eq hsum.symm
  refine ⟨hmem, ?_⟩
  have hval : freeHamiltonian (Fin (M + 1) × Fin 3) ⟨T (emap_mp M) f g, hmem⟩ =
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) ℂ).symm (hmem.toLp _) := rfl
  have hvf : freeHamiltonian (Fin M × Fin 3) ⟨f, hfd⟩ =
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ).symm (hfm.toLp _) := rfl
  have hvg : freeHamiltonian (Fin 3) ⟨g, hgd⟩ =
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ).symm (hgm.toLp _) := rfl
  have hP : hmem.toLp _ = T (emap_mp M) (hfm.toLp _) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ g) +
        T (emap_mp M) (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ f) (hgm.toLp _) :=
    Lp.ext (hmem.coeFn_toLp.trans hsum)
  rw [hval, hvf, hvg, hP, map_add, fourier_symm_T, fourier_symm_T,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  filter_upwards [Lp.coeFn_add
      (T (emap_mp M) ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ).symm (hfm.toLp _)) g)
      (T (emap_mp M) f ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ).symm (hgm.toLp _))),
    coeFn_T (emap_mp M) ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin M × Fin 3)) ℂ).symm (hfm.toLp _)) g,
    coeFn_T (emap_mp M) f ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin 3)) ℂ).symm (hgm.toLp _))]
    with x k1 k2 k3
  rw [k1, Pi.add_apply, k2, k3]
  simp only [tfun, emap_apply]

end HVZE3b


end

section


/-! E3d kernel decay: Coulomb-type kernel `κ v = 1/‖v‖²` on ℝ³ against L¹ ⊗ (L¹ ∩ L∞) densities. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HVZE3d

noncomputable def κ (v : EuclideanSpace ℝ (Fin 3)) : ℝ≥0∞ := ENNReal.ofReal ((‖v‖ ^ 2)⁻¹)

theorem measurable_κ : Measurable κ :=
  ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const 2).inv)

theorem integrable_radial (s : ℝ) (hs : -3 < s) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ s * Real.exp (-(b * ‖x‖))) := by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ => y ^ s * Real.exp (-(b * y)))).2 ?_
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := s + 2) (p := 1) (by linarith) one_pos hb).congr_fun
    (fun y hy => ?_) measurableSet_Ioi
  have hy' : 0 < y := hy
  beta_reduce
  rw [hV, Real.rpow_one, Real.rpow_add hy', Real.rpow_two, smul_eq_mul]
  norm_num
  ring

theorem lintegral_ball_κ_ne_top :
    ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1, κ v ≠ ∞ := by
  have hint := (integrable_radial (-2) (by norm_num) 1 one_pos).const_mul (Real.exp 1)
  refine ne_of_lt (lt_of_le_of_lt ?_ hint.lintegral_lt_top)
  refine (setLIntegral_mono' measurableSet_ball fun v hv => ?_).trans
    (lintegral_mono' Measure.restrict_le_self le_rfl)
  have hv' : ‖v‖ < 1 := by simpa using hv
  unfold κ
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.rpow_neg (norm_nonneg v), Real.rpow_two]
  have h1 : 1 ≤ Real.exp 1 * Real.exp (-(1 * ‖v‖)) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have h0 : 0 ≤ (‖v‖ ^ 2)⁻¹ := by positivity
  calc (‖v‖ ^ 2)⁻¹ = 1 * (‖v‖ ^ 2)⁻¹ := (one_mul _).symm
    _ ≤ (Real.exp 1 * Real.exp (-(1 * ‖v‖))) * (‖v‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h1 h0
    _ = Real.exp 1 * ((‖v‖ ^ 2)⁻¹ * Real.exp (-(1 * ‖v‖))) := by ring

theorem tendsto_vol_ball :
    Tendsto (fun r : ℝ => volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)) (𝓝 0) (𝓝 0) := by
  simp_rw [EuclideanSpace.volume_ball]
  have h : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0)
  have h3 : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ Fintype.card (Fin 3)) (𝓝 0) (𝓝 0) := by
    have := ((ENNReal.continuous_pow (Fintype.card (Fin 3))).tendsto 0).comp h
    rw [zero_pow (by simp)] at this
    exact this
  have := ENNReal.Tendsto.mul_const h3 (Or.inr ENNReal.ofReal_ne_top)
    (b := ENNReal.ofReal (√Real.pi ^ Fintype.card (Fin 3) /
      Real.Gamma (↑(Fintype.card (Fin 3)) / 2 + 1)))
  rw [zero_mul] at this
  exact this

theorem tendsto_I :
    Tendsto (fun r : ℝ => ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, κ v) (𝓝 0) (𝓝 0) := by
  have hf : ∫⁻ v, (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator κ v ≠ ∞ := by
    rw [lintegral_indicator measurableSet_ball]; exact lintegral_ball_κ_ne_top
  refine (tendsto_setLIntegral_zero hf tendsto_vol_ball).congr' ?_
  filter_upwards [Iio_mem_nhds (one_pos : (0 : ℝ) < 1)] with r hr
  refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
  rw [Set.indicator_of_mem (Metric.ball_subset_ball (le_of_lt hr) hv)]

theorem κ_le_split (r : ℝ) (hr : 0 < r) (v : EuclideanSpace ℝ (Fin 3)) :
    κ v ≤ min (κ v) (ENNReal.ofReal ((r ^ 2)⁻¹)) + (Metric.ball 0 r).indicator κ v := by
  by_cases hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r
  · rw [Set.indicator_of_mem hv]; exact le_add_self
  · rw [Set.indicator_of_notMem hv, add_zero]
    refine le_min le_rfl ?_
    have : r ≤ ‖v‖ := by simpa using hv
    unfold κ
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le this 2))

theorem tendsto_κ (u : EuclideanSpace ℝ (Fin 3)) :
    Tendsto (fun a : EuclideanSpace ℝ (Fin 3) => κ (u - a))
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) := by
  have h0 : Tendsto (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖ + -‖u‖)
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_comap
  have h1 : Tendsto (fun a : EuclideanSpace ℝ (Fin 3) => ‖u - a‖)
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) atTop := by
    refine tendsto_atTop_mono (fun a => ?_) h0
    have := norm_sub_norm_le a u
    rw [norm_sub_rev] at this
    linarith
  have h2 : Tendsto (fun a : EuclideanSpace ℝ (Fin 3) => (‖u - a‖ ^ 2)⁻¹)
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp h1)
  have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h2
  simpa [κ, Function.comp_def] using h3

theorem J_tendsto {A : Type*} [MeasurableSpace A] (μ : Measure A) [SFinite μ]
    (F : A → ℝ≥0∞) (hF : Measurable F) (hFi : ∫⁻ y, F y ∂μ ≠ ∞) (hFf : ∀ y, F y ≠ ∞)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hG : Measurable G) (hGi : ∫⁻ w, G w ≠ ∞)
    (hGf : ∀ w, G w ≠ ∞) (C : ℝ≥0∞) (hC : C ≠ ∞) (hGC : ∀ᵐ w, G w ≤ C)
    (p : A → EuclideanSpace ℝ (Fin 3)) (hp : Measurable p) :
    Tendsto (fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫⁻ q, F q.1 * G q.2 * κ (p q.1 - q.2 - a) ∂(μ.prod volume))
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hK : (∫⁻ y, F y ∂μ) * C ≠ ∞ := ENNReal.mul_ne_top hFi hC
  have hKI := ENNReal.Tendsto.const_mul tendsto_I (Or.inr hK)
  rw [mul_zero] at hKI
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ((∫⁻ y, F y ∂μ) * C) *
      (∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, κ v) ≤ δ / 2 ∧ r ∈ Set.Ioi 0 :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (ENNReal.tendsto_nhds_zero.1 hKI _ hδ2)).and self_mem_nhdsWithin
  obtain ⟨r, hrI, hr0⟩ := hev.exists
  have hr0' : 0 < r := hr0
  have hpq : ∀ a : EuclideanSpace ℝ (Fin 3),
      Measurable (fun q : A × EuclideanSpace ℝ (Fin 3) => p q.1 - q.2 - a) := fun a =>
    ((hp.comp measurable_fst).sub measurable_snd).sub_const a
  have hFG : Measurable (fun q : A × EuclideanSpace ℝ (Fin 3) => F q.1 * G q.2) :=
    (hF.comp measurable_fst).mul (hG.comp measurable_snd)
  have hJ1 : Tendsto (fun a : EuclideanSpace ℝ (Fin 3) => ∫⁻ q, F q.1 * G q.2 *
        min (κ (p q.1 - q.2 - a)) (ENNReal.ofReal ((r ^ 2)⁻¹)) ∂(μ.prod volume))
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence (μ := μ.prod volume)
      (l := comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop)
      (F := fun a q => F q.1 * G q.2 * min (κ (p q.1 - q.2 - a)) (ENNReal.ofReal ((r ^ 2)⁻¹)))
      (f := fun _ => 0) (fun q => F q.1 * G q.2 * ENNReal.ofReal ((r ^ 2)⁻¹)) ?_ ?_ ?_ ?_
    · simpa using this
    · exact Eventually.of_forall fun a => hFG.mul ((measurable_κ.comp (hpq a)).min measurable_const)
    · exact Eventually.of_forall fun a => Eventually.of_forall fun q =>
        mul_le_mul' le_rfl (min_le_right _ _)
    · rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        lintegral_prod_mul hF.aemeasurable hG.aemeasurable]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hFi hGi) ENNReal.ofReal_ne_top
    · refine Eventually.of_forall fun q => ?_
      have h1 : Tendsto (fun a : EuclideanSpace ℝ (Fin 3) =>
          min (κ (p q.1 - q.2 - a)) (ENNReal.ofReal ((r ^ 2)⁻¹)))
          (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_κ (p q.1 - q.2))
          (fun _ => bot_le) (fun _ => min_le_left _ _)
      have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.mul_ne_top (hFf q.1) (hGf q.2)))
      simpa using h2
  have hJ2 : ∀ a : EuclideanSpace ℝ (Fin 3), ∫⁻ q, F q.1 * G q.2 *
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p q.1 - q.2 - a) ∂(μ.prod volume) ≤
      (∫⁻ y, F y ∂μ) * C * ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, κ v := by
    intro a
    have hind : Measurable ((Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ) :=
      measurable_κ.indicator measurableSet_ball
    have hm2 : Measurable (fun q : A × EuclideanSpace ℝ (Fin 3) => F q.1 * G q.2 *
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p q.1 - q.2 - a)) :=
      hFG.mul (hind.comp (hpq a))
    rw [lintegral_prod _ hm2.aemeasurable]
    calc ∫⁻ y, ∫⁻ w, F (y, w).1 * G (y, w).2 *
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p (y, w).1 - (y, w).2 - a) ∂volume ∂μ
        ≤ ∫⁻ y, F y * (C * ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, κ v) ∂μ := by
          refine lintegral_mono fun y => ?_
          simp only [mul_assoc]
          have hm3 : Measurable (fun w : EuclideanSpace ℝ (Fin 3) => G w *
              (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p y - w - a)) :=
            hG.mul (hind.comp ((measurable_const.sub measurable_id).sub_const a))
          rw [lintegral_const_mul _ hm3]
          refine mul_le_mul' le_rfl ?_
          calc ∫⁻ w, G w * (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p y - w - a)
              ≤ ∫⁻ w, C * (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p y - a - w) :=
                lintegral_mono_ae (hGC.mono fun w hw => by
                  rw [sub_right_comm]; exact mul_le_mul' hw le_rfl)
            _ = C * ∫⁻ w, (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p y - a - w) :=
                lintegral_const_mul _ (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) =>
                  (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ (p y - a - w)) from
                  hind.comp (measurable_const.sub measurable_id))
            _ = C * ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, κ v := by
                rw [lintegral_sub_left_eq_self (fun v =>
                  (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ v) (p y - a),
                  lintegral_indicator measurableSet_ball]
      _ = (∫⁻ y, F y ∂μ) * C * ∫⁻ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r, κ v := by
          rw [lintegral_mul_const _ hF, mul_assoc]
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hJ1 (δ / 2) hδ2] with a ha
  have hm1 : Measurable (fun q : A × EuclideanSpace ℝ (Fin 3) => F q.1 * G q.2 *
      min (κ (p q.1 - q.2 - a)) (ENNReal.ofReal ((r ^ 2)⁻¹))) :=
    hFG.mul ((measurable_κ.comp (hpq a)).min measurable_const)
  calc ∫⁻ q, F q.1 * G q.2 * κ (p q.1 - q.2 - a) ∂(μ.prod volume)
      ≤ ∫⁻ q, (F q.1 * G q.2 * min (κ (p q.1 - q.2 - a)) (ENNReal.ofReal ((r ^ 2)⁻¹)) +
          F q.1 * G q.2 * (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r).indicator κ
            (p q.1 - q.2 - a)) ∂(μ.prod volume) :=
        lintegral_mono fun q => by rw [← mul_add]; exact mul_le_mul' le_rfl (κ_le_split r hr0' _)
    _ = _ := lintegral_add_left hm1 _
    _ ≤ δ / 2 + δ / 2 := add_le_add ha ((hJ2 a).trans hrI)
    _ = δ := ENNReal.add_halves δ

end HVZE3d

open TeschlQM.Atomic

namespace HVZE3

/-- the interaction of the last electron with the nucleus and the others -/
noncomputable def W (γne γee : ℝ) {M : ℕ} (x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) : ℝ :=
  -(γne / ‖electron x (Fin.last M)‖) +
    ∑ j : Fin M, γee / ‖electron x j.castSucc - electron x (Fin.last M)‖

/-- E3d decay of the interaction on a translated bounded packet -/
def E3d : Prop :=
  ∀ (γne γee : ℝ) (M : ℕ) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))))
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (C : ℝ),
    (∀ᵐ y ∂volume, ‖(g : EuclideanSpace ℝ (Fin 3) → ℂ) y‖ ≤ C) →
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a : EuclideanSpace ℝ (Fin 3), R ≤ ‖a‖ →
      Integrable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) => W γne γee x ^ 2 *
        (‖(f : _ → ℂ) (front x)‖ * ‖(g : _ → ℂ) (electron x (Fin.last M) - a)‖) ^ 2) ∧
      ∫ x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3), W γne γee x ^ 2 *
        (‖(f : _ → ℂ) (front x)‖ * ‖(g : _ → ℂ) (electron x (Fin.last M) - a)‖) ^ 2 ≤ ε

/-- E3e potential splitting -/
theorem pot_split (γne γee : ℝ) (M : ℕ) (x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3)) :
    atomicPotential γne γee (M + 1) x = atomicPotential γne γee M (front x) + W γne γee x := by
  unfold atomicPotential W
  rw [Fin.sum_univ_castSucc]
  have he : ∀ j : Fin M, electron (front x) j = electron x j.castSucc := fun j => rfl
  simp only [he]
  rw [Fin.sum_univ_castSucc]
  have hlast : (Finset.univ.filter (fun k : Fin (M + 1) => Fin.last M < k)) = ∅ := by
    ext k; simp [Fin.le_last]
  have hcs : ∀ j : Fin M, ∑ k ∈ Finset.univ.filter (fun k : Fin (M + 1) => j.castSucc < k),
      γee / ‖electron x j.castSucc - electron x k‖ =
      (∑ k ∈ Finset.univ.filter (fun k : Fin M => j < k),
        γee / ‖electron x j.castSucc - electron x k.castSucc‖) +
      γee / ‖electron x j.castSucc - electron x (Fin.last M)‖ := by
    intro j
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_last]
  rw [hlast, Finset.sum_empty, add_zero]
  simp only [hcs, Finset.sum_add_distrib]
  ring

end HVZE3


namespace HVZE3d

open TeschlQM.Atomic

theorem J_shift {A : Type*} [MeasurableSpace A] (μ : Measure A) [SFinite μ]
    (F : A → ℝ≥0∞) (hF : Measurable F) (G : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hG : Measurable G)
    (p : A → EuclideanSpace ℝ (Fin 3)) (hp : Measurable p) (a : EuclideanSpace ℝ (Fin 3)) :
    ∫⁻ q, F q.1 * G (q.2 - a) * κ (p q.1 - q.2) ∂(μ.prod volume) =
      ∫⁻ q, F q.1 * G q.2 * κ (p q.1 - q.2 - a) ∂(μ.prod volume) := by
  have h1 : Measurable (fun q : A × EuclideanSpace ℝ (Fin 3) => F q.1 * G (q.2 - a) * κ (p q.1 - q.2)) :=
    ((hF.comp measurable_fst).mul (hG.comp (measurable_snd.sub_const a))).mul
      (measurable_κ.comp ((hp.comp measurable_fst).sub measurable_snd))
  have h2 : Measurable (fun q : A × EuclideanSpace ℝ (Fin 3) => F q.1 * G q.2 * κ (p q.1 - q.2 - a)) :=
    ((hF.comp measurable_fst).mul (hG.comp measurable_snd)).mul
      (measurable_κ.comp (((hp.comp measurable_fst).sub measurable_snd).sub_const a))
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_sub_right_eq_self (μ := volume) (fun w => F y * G w * κ (p y - w - a)) a]
  refine lintegral_congr fun z => ?_
  show F y * G (z - a) * κ (p y - z) = F y * G (z - a) * κ (p y - (z - a) - a)
  rw [sub_sub (p y) (z - a) a, sub_add_cancel]

theorem pt_bound (γne γee : ℝ) (M : ℕ) (y : EuclideanSpace ℝ (Fin M × Fin 3))
    (z : EuclideanSpace ℝ (Fin 3)) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ENNReal.ofReal ((-(γne / ‖z‖) + ∑ j : Fin M, γee / ‖electron y j - z‖) ^ 2 * (s * t)) ≤
      ENNReal.ofReal (2 * ((M : ℝ) + 1)) *
        (ENNReal.ofReal (γne ^ 2) * (ENNReal.ofReal s * ENNReal.ofReal t * κ (0 - z)) +
          ∑ j : Fin M, ENNReal.ofReal (γee ^ 2) *
            (ENNReal.ofReal s * ENNReal.ofReal t * κ (electron y j - z))) := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hS : (∑ j : Fin M, γee / ‖electron y j - z‖) ^ 2 ≤
      (M : ℝ) * ∑ j : Fin M, (γee / ‖electron y j - z‖) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin M => γee / ‖electron y j - z‖)
    simpa using this
  have hsum0 : 0 ≤ ∑ j : Fin M, (γee / ‖electron y j - z‖) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : (-(γne / ‖z‖) + ∑ j : Fin M, γee / ‖electron y j - z‖) ^ 2 ≤
      2 * ((M : ℝ) + 1) * ((-(γne / ‖z‖)) ^ 2 + ∑ j : Fin M, (γee / ‖electron y j - z‖) ^ 2) := by
    nlinarith [sq_nonneg (-(γne / ‖z‖) - ∑ j : Fin M, γee / ‖electron y j - z‖),
      sq_nonneg (-(γne / ‖z‖)), mul_nonneg hM (sq_nonneg (-(γne / ‖z‖)))]
  have ht0 : (-(γne / ‖z‖)) ^ 2 = γne ^ 2 * (‖0 - z‖ ^ 2)⁻¹ := by
    rw [zero_sub, norm_neg, neg_sq, div_pow, div_eq_mul_inv]
  have hsj : ∑ j : Fin M, γee ^ 2 * (s * t * (‖electron y j - z‖ ^ 2)⁻¹) =
      (s * t) * ∑ j : Fin M, (γee / ‖electron y j - z‖) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, div_eq_mul_inv]
    ring
  have key : (-(γne / ‖z‖) + ∑ j : Fin M, γee / ‖electron y j - z‖) ^ 2 * (s * t) ≤
      2 * ((M : ℝ) + 1) * (γne ^ 2 * (s * t * (‖0 - z‖ ^ 2)⁻¹) +
        ∑ j : Fin M, γee ^ 2 * (s * t * (‖electron y j - z‖ ^ 2)⁻¹)) := by
    calc _ ≤ (2 * ((M : ℝ) + 1) * ((-(γne / ‖z‖)) ^ 2 +
            ∑ j : Fin M, (γee / ‖electron y j - z‖) ^ 2)) * (s * t) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hs ht)
      _ = _ := by rw [hsj, ht0]; ring
  have e1 : ∀ (γ : ℝ) (v : EuclideanSpace ℝ (Fin 3)), ENNReal.ofReal (γ ^ 2 * (s * t * (‖v‖ ^ 2)⁻¹)) =
      ENNReal.ofReal (γ ^ 2) * (ENNReal.ofReal s * ENNReal.ofReal t * κ v) := fun γ v => by
    rw [ENNReal.ofReal_mul (sq_nonneg γ), ENNReal.ofReal_mul (mul_nonneg hs ht), ENNReal.ofReal_mul hs]
    rfl
  refine (ENNReal.ofReal_le_ofReal key).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity)
    (Finset.sum_nonneg fun j _ => by positivity), ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  simp only [e1]

theorem continuous_electron (M : ℕ) (j : Fin M) :
    Continuous (fun y : EuclideanSpace ℝ (Fin M × Fin 3) => electron y j) := by
  unfold electron
  fun_prop

theorem e3d : HVZE3.E3d := by
  intro γne γee M f g C hgC ε hε
  have hfm : Measurable (f : EuclideanSpace ℝ (Fin M × Fin 3) → ℂ) :=
    (Lp.stronglyMeasurable f).measurable
  have hgm : Measurable (g : EuclideanSpace ℝ (Fin 3) → ℂ) := (Lp.stronglyMeasurable g).measurable
  set F : EuclideanSpace ℝ (Fin M × Fin 3) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (‖(f : _ → ℂ) y‖ ^ 2) with hFdef
  set G : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ :=
    fun w => ENNReal.ofReal (‖(g : _ → ℂ) w‖ ^ 2) with hGdef
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (hfm.norm.pow_const 2)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (hgm.norm.pow_const 2)
  have hFi : ∫⁻ y, F y ≠ ∞ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).1 (Lp.memLp f)).lintegral_lt_top.ne
  have hGi : ∫⁻ w, G w ≠ ∞ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).1 (Lp.memLp g)).lintegral_lt_top.ne
  have hGC : ∀ᵐ w, G w ≤ ENNReal.ofReal (C ^ 2) :=
    hgC.mono fun w hw => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hw 2)
  have hJ : ∀ p : EuclideanSpace ℝ (Fin M × Fin 3) → EuclideanSpace ℝ (Fin 3), Measurable p →
      Tendsto (fun a : EuclideanSpace ℝ (Fin 3) =>
        ∫⁻ q, F q.1 * G (q.2 - a) * κ (p q.1 - q.2) ∂(volume.prod volume))
        (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) := fun p hp =>
    (J_tendsto volume F hF hFi (fun _ => ENNReal.ofReal_ne_top) G hG hGi
      (fun _ => ENNReal.ofReal_ne_top) _ ENNReal.ofReal_ne_top hGC p hp).congr
      (fun a => (J_shift volume F hF G hG p hp a).symm)
  have hel := continuous_electron M
  -- the bound integrand
  have hΨ : ∀ a : EuclideanSpace ℝ (Fin 3),
      ∫⁻ q, ENNReal.ofReal (2 * ((M : ℝ) + 1)) *
        (ENNReal.ofReal (γne ^ 2) * (F q.1 * G (q.2 - a) * κ (0 - q.2)) +
          ∑ j : Fin M, ENNReal.ofReal (γee ^ 2) *
            (F q.1 * G (q.2 - a) * κ (electron q.1 j - q.2))) ∂(volume.prod volume) =
      ENNReal.ofReal (2 * ((M : ℝ) + 1)) *
        (ENNReal.ofReal (γne ^ 2) * ∫⁻ q, F q.1 * G (q.2 - a) * κ (0 - q.2) ∂(volume.prod volume) +
          ∑ j : Fin M, ENNReal.ofReal (γee ^ 2) *
            ∫⁻ q, F q.1 * G (q.2 - a) * κ (electron q.1 j - q.2) ∂(volume.prod volume)) := by
    intro a
    have hm : ∀ p : EuclideanSpace ℝ (Fin M × Fin 3) → EuclideanSpace ℝ (Fin 3), Measurable p →
        Measurable (fun q : EuclideanSpace ℝ (Fin M × Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          F q.1 * G (q.2 - a) * κ (p q.1 - q.2)) := fun p hp =>
      ((hF.comp measurable_fst).mul (hG.comp (measurable_snd.sub_const a))).mul
        (measurable_κ.comp ((hp.comp measurable_fst).sub measurable_snd))
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left (show Measurable (fun q : EuclideanSpace ℝ (Fin M × Fin 3) ×
          EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (γne ^ 2) * (F q.1 * G (q.2 - a) * κ (0 - q.2))) from
        measurable_const.mul (hm (fun _ => 0) measurable_const)),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finset_sum _ (fun j _ => show Measurable (fun q : EuclideanSpace ℝ (Fin M × Fin 3) ×
          EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (γee ^ 2) *
            (F q.1 * G (q.2 - a) * κ (electron q.1 j - q.2))) from
        measurable_const.mul (hm (fun y => electron y j) (hel j).measurable))]
    congr 2
    exact Finset.sum_congr rfl fun j _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun a : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (2 * ((M : ℝ) + 1)) *
        (ENNReal.ofReal (γne ^ 2) * ∫⁻ q, F q.1 * G (q.2 - a) * κ (0 - q.2) ∂(volume.prod volume) +
          ∑ j : Fin M, ENNReal.ofReal (γee ^ 2) *
            ∫⁻ q, F q.1 * G (q.2 - a) * κ (electron q.1 j - q.2) ∂(volume.prod volume)))
      (comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) atTop) (𝓝 0) := by
    have h0 := ENNReal.Tendsto.const_mul (hJ (fun _ => 0) measurable_const)
      (Or.inr (ENNReal.ofReal_ne_top (r := γne ^ 2)))
    have hs := tendsto_finset_sum (Finset.univ : Finset (Fin M)) (fun j _ =>
      ENNReal.Tendsto.const_mul (hJ (fun y => electron y j) (hel j).measurable)
        (Or.inr (ENNReal.ofReal_ne_top (r := γee ^ 2))))
    have ht := ENNReal.Tendsto.const_mul (h0.add hs)
      (Or.inr (ENNReal.ofReal_ne_top (r := 2 * ((M : ℝ) + 1))))
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at ht
    exact ht
  have hev := ENNReal.tendsto_nhds_zero.1 hlim (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  obtain ⟨R, -, hR⟩ := (Filter.atTop_basis.comap (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖)).eventually_iff.1 hev
  refine ⟨R, fun a ha => ?_⟩
  have hP := hR (show a ∈ (fun a : EuclideanSpace ℝ (Fin 3) => ‖a‖) ⁻¹' Set.Ici R from ha)
  rw [← hΨ a] at hP
  have hz : Measurable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) => electron x (Fin.last M)) :=
    measurable_snd.comp (HVZE3a.emap M).measurable
  have hy : Measurable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) => HVZE3.front x) :=
    measurable_fst.comp (HVZE3a.emap M).measurable
  have hW : Measurable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) => HVZE3.W γne γee x) := by
    have : Measurable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) =>
        -(γne / ‖electron x (Fin.last M)‖) +
          ∑ j : Fin M, γee / ‖electron (HVZE3.front x) j - electron x (Fin.last M)‖) :=
      (hz.norm.const_div γne).neg.add
        (Finset.measurable_sum _ fun j _ => (((hel j).measurable.comp hy).sub hz).norm.const_div γee)
    exact this
  have hΦm : Measurable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) => HVZE3.W γne γee x ^ 2 *
      (‖(f : _ → ℂ) (HVZE3.front x)‖ * ‖(g : _ → ℂ) (electron x (Fin.last M) - a)‖) ^ 2) :=
    (hW.pow_const 2).mul (((hfm.comp hy).norm.mul (hgm.comp (hz.sub_const a)).norm).pow_const 2)
  have hΦ0 : ∀ x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3), 0 ≤ HVZE3.W γne γee x ^ 2 *
      (‖(f : _ → ℂ) (HVZE3.front x)‖ * ‖(g : _ → ℂ) (electron x (Fin.last M) - a)‖) ^ 2 :=
    fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hlin : ∫⁻ x, ENNReal.ofReal (HVZE3.W γne γee x ^ 2 *
      (‖(f : _ → ℂ) (HVZE3.front x)‖ * ‖(g : _ → ℂ) (electron x (Fin.last M) - a)‖) ^ 2) ≤
      ENNReal.ofReal ε := by
    refine le_trans ?_ hP
    rw [← Measure.volume_eq_prod, ← (HVZE3a.emap_mp M).lintegral_comp_emb
      (HVZE3a.emap M).measurableEmbedding]
    refine lintegral_mono fun x => ?_
    rw [HVZE3a.emap_apply, mul_pow]
    exact pt_bound γne γee M (HVZE3.front x) (electron x (Fin.last M)) _ _ (sq_nonneg _) (sq_nonneg _)
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin (M + 1) × Fin 3) => HVZE3.W γne γee x ^ 2 *
      (‖(f : _ → ℂ) (HVZE3.front x)‖ * ‖(g : _ → ℂ) (electron x (Fin.last M) - a)‖) ^ 2) :=
    ⟨hΦm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hΦ0)).2
      (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hΦ0) hΦm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hlin

end HVZE3d


end

section


set_option autoImplicit false

open MeasureTheory FourierTransform SchwartzMap
open scoped InnerProductSpace ContDiff

/-! E3c': translated wave packets with a common bounded profile (inverse L² Fourier on L¹ ∩ L²). -/

namespace HVZHyd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem continuous_fourierInv_of_integrable (f : E → ℂ) (hf1 : Integrable f) :
    Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous (L := -innerₗ E) Real.continuous_fourierChar
    (by exact continuous_inner.neg) hf1

theorem pairing_fourierInv (f : E → ℂ) (hf1 : Integrable f) (u : 𝓢(E, ℂ)) :
    ∫ x, (𝓕⁻ u) x • f x = ∫ x, u x • 𝓕⁻ f x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E)
      Real.continuous_fourierChar (by exact continuous_inner.neg) (u.integrable (μ := volume)) hf1
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext v w; simp [real_inner_comm]
  rw [hflip] at h
  rw [SchwartzMap.fourierInv_coe]
  exact h

theorem Lp_fourierInv_eq_integral (f : E → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (((Lp.fourierTransformₗᵢ E ℂ).symm (hf2.toLp f) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
      =ᵐ[volume] 𝓕⁻ f := by
  have key : ∀ u : 𝓢(E, ℂ),
      ∫ x, u x • ((Lp.fourierTransformₗᵢ E ℂ).symm (hf2.toLp f) : E → ℂ) x = ∫ x, u x • 𝓕⁻ f x := by
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
  have hgcs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := by
    have h := hgs.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
    exact h
  have := key (hgcs.toSchwartzMap hgc)
  simp only [Complex.real_smul, smul_eq_mul]
  exact this

end HVZHyd

namespace HVZTr

abbrev E3 := EuclideanSpace ℝ (Fin 3)
noncomputable abbrev L23 := Lp ℂ 2 (volume : Measure E3)
noncomputable abbrev U3 : L23 ≃ₗᵢ[ℂ] L23 := Lp.fourierTransformₗᵢ E3 ℂ

set_option maxHeartbeats 1000000 in
theorem packetT (s : ℝ) (hs : 0 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g0 : L23) (C : ℝ), (∀ᵐ y ∂volume, ‖(g0 : E3 → ℂ) y‖ ≤ C) ∧
    ∀ a : E3, ∃ g : (TeschlQM.Atomic.freeHamiltonian (Fin 3)).domain, ‖(g : L23)‖ = 1 ∧
      ‖TeschlQM.Atomic.freeHamiltonian (Fin 3) g - (s : ℂ) • (g : L23)‖ ≤ ε ∧
      ((g : L23) : E3 → ℂ) =ᵐ[volume] fun y => (g0 : E3 → ℂ) (y - a) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : E3 → ℂ, σ = fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hσc : Continuous σ := by rw [hσ]; fun_prop
  set k : E3 := EuclideanSpace.single 0 (Real.sqrt s / (2 * Real.pi)) with hk
  have hks : σ k = (s : ℂ) := by
    rw [hσ]; simp only [hk, EuclideanSpace.norm_single, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), div_pow, Real.sq_sqrt hs]
    congr 1; field_simp; ring
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hσc.continuousAt ε hε
  set B : Set E3 := Metric.ball k δ with hB
  have hBm : MeasurableSet B := measurableSet_ball
  have hBf : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : 0 < (volume B).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume k hδ).ne' hBf
  set G0 : L23 := indicatorConstLp 2 hBm hBf (1 : ℂ) with hG0
  have hG0n : ‖G0‖ ≠ 0 := by
    rw [hG0, norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul]
    exact (Real.rpow_pos_of_pos hBpos _).ne'
  set c : ℂ := ((‖G0‖⁻¹ : ℝ) : ℂ) with hc
  set G : L23 := c • G0 with hG
  have hGn : ‖G‖ = 1 := by
    rw [hG, norm_smul, hc, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ hG0n]
  obtain ⟨Gf, hGf⟩ : ∃ Gf : E3 → ℂ, Gf = fun ξ => c * B.indicator (fun _ => (1 : ℂ)) ξ :=
    ⟨_, rfl⟩
  have hGae : (G : E3 → ℂ) =ᵐ[volume] Gf := by
    filter_upwards [Lp.coeFn_smul c G0, indicatorConstLp_coeFn (p := 2) (hs := hBm)
      (hμs := hBf) (c := (1 : ℂ))] with ξ h1 h2
    rw [hGf, hG, h1, Pi.smul_apply, smul_eq_mul, hG0, h2]
  have hGfm : AEStronglyMeasurable Gf volume := (Lp.aestronglyMeasurable G).congr hGae
  have hGf2 : MemLp Gf 2 volume := (Lp.memLp G).ae_eq hGae
  have hGf1 : Integrable Gf volume := by
    have e : Gf = B.indicator (fun _ => c) := by
      ext ξ; by_cases hm : ξ ∈ B <;> simp [hGf, hm]
    rw [e]; exact (integrableOn_const hBf).integrable_indicator hBm
  obtain ⟨h, hh⟩ : ∃ h : E3 → ℂ, h = 𝓕⁻ Gf := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : E3 → E3 → ℂ, P = fun a ξ => (Real.fourierChar (-⟪ξ, a⟫_ℝ) : ℂ) * Gf ξ :=
    ⟨_, rfl⟩
  have hPn : ∀ a ξ, ‖P a ξ‖ = ‖Gf ξ‖ := by intro a ξ; simp [hP, Circle.norm_coe]
  have hPm : ∀ a, AEStronglyMeasurable (P a) volume := fun a => by
    rw [hP]; exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hGfm
  have hP2 : ∀ a, MemLp (P a) 2 volume := fun a =>
    hGf2.of_le (hPm a) (ae_of_all _ fun ξ => (hPn a ξ).le)
  have hP1 : ∀ a, Integrable (P a) volume := fun a =>
    hGf1.mono (hPm a) (ae_of_all _ fun ξ => (hPn a ξ).le)
  have hPinv : ∀ a y, 𝓕⁻ (P a) y = h (y - a) := by
    intro a y
    rw [hh, hP]
    simp only [Real.fourierInv_eq, Circle.smul_def, smul_eq_mul]
    congr 1; ext v
    rw [inner_sub_right, sub_eq_add_neg, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  have key : ∀ a : E3, ∃ g : (TeschlQM.Atomic.freeHamiltonian (Fin 3)).domain, ‖(g : L23)‖ = 1 ∧
      ‖TeschlQM.Atomic.freeHamiltonian (Fin 3) g - (s : ℂ) • (g : L23)‖ ≤ ε ∧
      ((g : L23) : E3 → ℂ) =ᵐ[volume] fun y => h (y - a) := by
    intro a
    set Ga : L23 := (hP2 a).toLp (P a) with hGa_def
    have hGa : (Ga : E3 → ℂ) =ᵐ[volume] P a := (hP2 a).coeFn_toLp
    have hGan : ‖Ga‖ = 1 := by
      have e := eLpNorm_congr_norm_ae (μ := volume) (p := 2) (ae_of_all _ (hPn a))
      rw [← hGn, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hGa, eLpNorm_congr_ae hGae, e]
    have hpt : ∀ᵐ ξ ∂volume, ‖(σ ξ - s) * (Ga : E3 → ℂ) ξ‖ ≤ ε * ‖(Ga : E3 → ℂ) ξ‖ := by
      filter_upwards [hGa] with ξ hξ
      rw [hξ]
      by_cases hm : ξ ∈ B
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have := hball (show dist ξ k < δ from hm)
        rw [dist_eq_norm, hks] at this
        exact this.le
      · simp [hP, hGf, hm]
    have hbd : ∀ᵐ ξ ∂volume, ‖σ ξ * (Ga : E3 → ℂ) ξ‖ ≤ (s + ε) * ‖(Ga : E3 → ℂ) ξ‖ := by
      filter_upwards [hpt] with ξ hξ
      have e : σ ξ * (Ga : E3 → ℂ) ξ = (σ ξ - s) * (Ga : E3 → ℂ) ξ + (s : ℂ) * (Ga : E3 → ℂ) ξ := by
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul (s : ℂ), Complex.norm_real, Real.norm_of_nonneg hs]
      linarith
    have hmemG : MemLp (fun ξ => σ ξ * (Ga : E3 → ℂ) ξ) 2 volume :=
      MemLp.of_le_mul (Lp.memLp Ga)
        (hσc.measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable Ga)) hbd
    set g : L23 := U3.symm Ga with hgdef
    have hUg : U3 g = Ga := LinearIsometryEquiv.apply_symm_apply _ _
    have hmem : MemLp (fun ξ => σ ξ * (U3 g : E3 → ℂ) ξ) 2 volume := by rw [hUg]; exact hmemG
    subst hσ
    have hg : g ∈ (TeschlQM.Atomic.freeHamiltonian (Fin 3)).domain := hmem
    have hval : TeschlQM.Atomic.freeHamiltonian (Fin 3) ⟨g, hg⟩ = U3.symm (hmem.toLp _) := rfl
    refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
    · show ‖g‖ = 1
      rw [hgdef, LinearIsometryEquiv.norm_map, hGan]
    · show ‖TeschlQM.Atomic.freeHamiltonian (Fin 3) ⟨g, hg⟩ - (s : ℂ) • g‖ ≤ ε
      rw [← LinearIsometryEquiv.norm_map U3, map_sub, map_smul, hval,
        LinearIsometryEquiv.apply_symm_apply]
      have hUg' : ((U3 g : L23) : E3 → ℂ) = (Ga : E3 → ℂ) := by rw [hUg]
      have h1 : ‖hmem.toLp _ - (s : ℂ) • U3 g‖ ≤ ε * ‖U3 g‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [Lp.coeFn_sub (hmem.toLp _) ((s : ℂ) • U3 g), Lp.coeFn_smul (s : ℂ) (U3 g),
          hmem.coeFn_toLp, hpt] with ξ h1 h2 h3 h4
        rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, smul_eq_mul, hUg']
        rw [← sub_mul]
        exact h4
      have hn : ‖U3 g‖ = 1 := by rw [hUg, hGan]
      rw [hn, mul_one] at h1
      exact h1
    · show (g : E3 → ℂ) =ᵐ[volume] fun y => h (y - a)
      have := HVZHyd.Lp_fourierInv_eq_integral (P a) (hP1 a) (hP2 a)
      filter_upwards [this] with y hy
      rw [hgdef, hGa_def, hy, hPinv]
  obtain ⟨g0, -, -, hg0⟩ := key 0
  refine ⟨(g0 : L23), ∫ ξ, ‖Gf ξ‖, ?_, fun a => ?_⟩
  · filter_upwards [hg0] with y hy
    rw [hy, sub_zero, hh]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  · obtain ⟨g, h1, h2, h3⟩ := key a
    refine ⟨g, h1, h2, ?_⟩
    have := (measurePreserving_sub_right (volume : Measure E3) a).quasiMeasurePreserving.ae_eq_comp hg0
    filter_upwards [h3, this] with y hy1 hy2
    simp only [Function.comp_apply] at hy2
    rw [hy1, hy2, sub_zero]

end HVZTr


end

section

set_option autoImplicit false
open MeasureTheory FourierTransform SchwartzMap TeschlQM.Atomic
open scoped ContDiff

namespace HVZE3x

open TeschlQM.Atomic HVZTen

abbrev XX (M : ℕ) := EuclideanSpace ℝ (Fin M × Fin 3)
noncomputable abbrev LL (M : ℕ) := Lp ℂ 2 (volume : Measure (XX M))
noncomputable abbrev L3 := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- the translated-packet statement proved as `HVZTr.packetT` -/
def PK : Prop :=
  ∀ (s : ℝ), 0 ≤ s → ∀ (ε : ℝ), 0 < ε →
    ∃ (g0 : L3) (C : ℝ), (∀ᵐ y ∂volume, ‖(g0 : EuclideanSpace ℝ (Fin 3) → ℂ) y‖ ≤ C) ∧
    ∀ a : EuclideanSpace ℝ (Fin 3), ∃ g : (freeHamiltonian (Fin 3)).domain, ‖(g : L3)‖ = 1 ∧
      ‖freeHamiltonian (Fin 3) g - (s : ℂ) • (g : L3)‖ ≤ ε ∧
      ((g : L3) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
        fun y => (g0 : EuclideanSpace ℝ (Fin 3) → ℂ) (y - a)

theorem liftA (M : ℕ) {p : XX M → Prop} (h : ∀ᵐ y ∂volume, p y) :
    ∀ᵐ x ∂(volume : Measure (XX (M + 1))), p (HVZE3.front x) :=
  ((Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (XX M)))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))).comp
    (HVZE3a.emap_mp M).quasiMeasurePreserving).ae h

theorem liftB (M : ℕ) {p : EuclideanSpace ℝ (Fin 3) → Prop} (h : ∀ᵐ y ∂volume, p y) :
    ∀ᵐ x ∂(volume : Measure (XX (M + 1))), p (electron x (Fin.last M)) :=
  ((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (XX M)))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))))).comp
    (HVZE3a.emap_mp M).quasiMeasurePreserving).ae h

theorem measurable_W (γne γee : ℝ) (M : ℕ) :
    Measurable (fun x : XX (M + 1) => HVZE3.W γne γee x) := by
  have hc : ∀ j : Fin (M + 1), Continuous (fun y : XX (M + 1) => electron y j) := by
    intro j; unfold electron; fun_prop
  unfold HVZE3.W
  exact (measurable_const.div (hc _).norm.measurable).neg.add
    (Finset.measurable_sum _ fun j _ =>
      measurable_const.div ((hc _).sub (hc _)).norm.measurable)

set_option maxHeartbeats 1000000 in
theorem e3' (hE3b : HVZE3.E3b) (hE3d : HVZE3.E3d) (hPK : PK)
    (γne γee : ℝ) (M : ℕ) (μ s : ℝ) (hs : 0 ≤ s)
    (φ : (atomicHamiltonian γne γee M).domain)
    (hφ1 : ‖(φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))))‖ = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ : (atomicHamiltonian γne γee (M + 1)).domain,
      ‖(Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (M + 1) × Fin 3))))‖ = 1 ∧
      ‖atomicHamiltonian γne γee (M + 1) Φ - ((μ + s : ℝ) : ℂ) •
          (Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (M + 1) × Fin 3))))‖ ≤
        ‖atomicHamiltonian γne γee M φ -
          (μ : ℂ) • (φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin M × Fin 3))))‖ + ε := by
  have he := HVZE3a.emap_mp M
  obtain ⟨g0, C, hC, hpk⟩ := hPK s hs (ε / 3) (by positivity)
  obtain ⟨R, hR⟩ := hE3d γne γee M (φ : LL M) g0 C hC ((ε / 3) ^ 2) (by positivity)
  obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin 3), R ≤ ‖a‖ :=
    ⟨EuclideanSpace.single 0 |R|, by
      rw [EuclideanSpace.norm_single, Real.norm_eq_abs, abs_abs]; exact le_abs_self R⟩
  obtain ⟨hWint, hWle⟩ := hR a ha
  obtain ⟨g, hg1, hg2, hga⟩ := hpk a
  have hφd : (φ : LL M) ∈ (freeHamiltonian (Fin M × Fin 3)).domain := (Submodule.mem_inf.1 φ.2).1
  have hφv : (φ : LL M) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))).domain :=
    (Submodule.mem_inf.1 φ.2).2
  have hHφ : atomicHamiltonian γne γee M φ = freeHamiltonian (Fin M × Fin 3) ⟨φ, hφd⟩ +
      mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) ⟨φ, hφv⟩ :=
    LinearPMap.add_apply _ _ _
  have hVφ : ∀ᵐ y ∂volume, (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))
      ⟨φ, hφv⟩ : XX M → ℂ) y = ((atomicPotential γne γee M y : ℝ) : ℂ) * (φ : LL M) y :=
    MemLp.coeFn_toLp hφv
  obtain ⟨F, hFdef⟩ : ∃ F : LL (M + 1), F = T he (φ : LL M) (g : L3) := ⟨_, rfl⟩
  have hF : (F : XX (M + 1) → ℂ) =ᵐ[volume]
      fun x => (φ : LL M) (HVZE3.front x) * (g : L3) (electron x (Fin.last M)) := by
    rw [hFdef]; exact coeFn_T he _ _
  obtain ⟨hF0, hH0F⟩ := hE3b M ⟨(φ : LL M), hφd⟩ g F hF
  have hgx := liftB M hga
  have hWF2 : ∀ᵐ x ∂volume, ‖((HVZE3.W γne γee x : ℝ) : ℂ) * (F : XX (M + 1) → ℂ) x‖ ^ 2 =
      HVZE3.W γne γee x ^ 2 * (‖(φ : LL M) (HVZE3.front x)‖ *
        ‖(g0 : L3) (electron x (Fin.last M) - a)‖) ^ 2 := by
    filter_upwards [hF, hgx] with x h1 h2
    rw [h1, h2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hWFm : AEStronglyMeasurable
      (fun x => ((HVZE3.W γne γee x : ℝ) : ℂ) * (F : XX (M + 1) → ℂ) x) volume :=
    (Complex.measurable_ofReal.comp (measurable_W γne γee M)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable F)
  have hWF : MemLp (fun x => ((HVZE3.W γne γee x : ℝ) : ℂ) * (F : XX (M + 1) → ℂ) x) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hWFm).2 (hWint.congr (hWF2.mono fun x hx => hx.symm))
  have hWtn : ‖hWF.toLp _‖ ≤ ε / 3 := by
    have h1 : ‖hWF.toLp _‖ ^ 2 ≤ (ε / 3) ^ 2 := by
      rw [norm_sq_L2]
      refine le_trans (le_of_eq (integral_congr_ae ?_)) hWle
      filter_upwards [hWF.coeFn_toLp, hWF2] with x h1 h2
      rw [h1, h2]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
  have hVF : (F : LL (M + 1)) ∈
      (mulOp volume (fun x => ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ))).domain := by
    show MemLp (fun x => ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ) * (F : XX (M + 1) → ℂ) x)
      2 volume
    refine ((Lp.memLp (T he (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))
      ⟨φ, hφv⟩) (g : L3))).add hWF).ae_eq ?_
    filter_upwards [coeFn_T he (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ))
      ⟨φ, hφv⟩) (g : L3), hF, liftA M hVφ] with x h1 h2 h3
    rw [Pi.add_apply, h1]
    simp only [HVZTen.tfun, HVZE3a.emap_apply]
    rw [h3, h2, HVZE3.pot_split]
    push_cast; ring
  have hΦ : (F : LL (M + 1)) ∈ (atomicHamiltonian γne γee (M + 1)).domain :=
    Submodule.mem_inf.2 ⟨hF0, hVF⟩
  have hHΦ : atomicHamiltonian γne γee (M + 1) ⟨F, hΦ⟩ =
      freeHamiltonian (Fin (M + 1) × Fin 3) ⟨F, hF0⟩ +
      mulOp volume (fun x => ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ)) ⟨F, hVF⟩ :=
    LinearPMap.add_apply _ _ _
  have hVF' : ∀ᵐ x ∂volume, (mulOp volume
      (fun x => ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ)) ⟨F, hVF⟩ : XX (M + 1) → ℂ) x =
      ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ) * (F : XX (M + 1) → ℂ) x :=
    MemLp.coeFn_toLp hVF
  have hA : ∀ᵐ y ∂volume, ((atomicHamiltonian γne γee M φ - (μ : ℂ) • (φ : LL M) : LL M) :
      XX M → ℂ) y = (freeHamiltonian (Fin M × Fin 3) ⟨φ, hφd⟩ : XX M → ℂ) y +
        ((atomicPotential γne γee M y : ℝ) : ℂ) * (φ : LL M) y - (μ : ℂ) * (φ : LL M) y := by
    rw [hHφ]
    filter_upwards [Lp.coeFn_sub (freeHamiltonian (Fin M × Fin 3) ⟨φ, hφd⟩ +
        mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) ⟨φ, hφv⟩)
        ((μ : ℂ) • (φ : LL M)),
      Lp.coeFn_add (freeHamiltonian (Fin M × Fin 3) ⟨φ, hφd⟩)
        (mulOp volume (fun x => ((atomicPotential γne γee M x : ℝ) : ℂ)) ⟨φ, hφv⟩),
      Lp.coeFn_smul (μ : ℂ) (φ : LL M), hVφ] with y h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul, h4]
  have hB : ∀ᵐ z ∂volume, ((freeHamiltonian (Fin 3) g - (s : ℂ) • (g : L3) : L3) :
      EuclideanSpace ℝ (Fin 3) → ℂ) z =
      (freeHamiltonian (Fin 3) g : EuclideanSpace ℝ (Fin 3) → ℂ) z - (s : ℂ) * (g : L3) z := by
    filter_upwards [Lp.coeFn_sub (freeHamiltonian (Fin 3) g) ((s : ℂ) • (g : L3)),
      Lp.coeFn_smul (s : ℂ) (g : L3)] with z h1 h2
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
  obtain ⟨T1, hT1⟩ : ∃ T1 : LL (M + 1),
      T1 = T he (atomicHamiltonian γne γee M φ - (μ : ℂ) • (φ : LL M)) (g : L3) := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : LL (M + 1),
      T2 = T he (φ : LL M) (freeHamiltonian (Fin 3) g - (s : ℂ) • (g : L3)) := ⟨_, rfl⟩
  have c1 : (T1 : XX (M + 1) → ℂ) =ᵐ[volume] tfun (HVZE3a.emap M)
      (atomicHamiltonian γne γee M φ - (μ : ℂ) • (φ : LL M) : LL M) (g : L3) := by
    rw [hT1]; exact coeFn_T he _ _
  have c2 : (T2 : XX (M + 1) → ℂ) =ᵐ[volume] tfun (HVZE3a.emap M) (φ : LL M)
      (freeHamiltonian (Fin 3) g - (s : ℂ) • (g : L3) : L3) := by
    rw [hT2]; exact coeFn_T he _ _
  have hkey : atomicHamiltonian γne γee (M + 1) ⟨F, hΦ⟩ - ((μ + s : ℝ) : ℂ) • F =
      T1 + T2 + hWF.toLp _ := by
    rw [hHΦ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (freeHamiltonian (Fin (M + 1) × Fin 3) ⟨F, hF0⟩ +
        mulOp volume (fun x => ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ)) ⟨F, hVF⟩)
        (((μ + s : ℝ) : ℂ) • F),
      Lp.coeFn_add (freeHamiltonian (Fin (M + 1) × Fin 3) ⟨F, hF0⟩)
        (mulOp volume (fun x => ((atomicPotential γne γee (M + 1) x : ℝ) : ℂ)) ⟨F, hVF⟩),
      Lp.coeFn_smul ((μ + s : ℝ) : ℂ) F, hH0F, hVF', hF,
      Lp.coeFn_add (T1 + T2) (hWF.toLp _), Lp.coeFn_add T1 T2, c1, c2, hWF.coeFn_toLp,
      liftA M hA, liftB M hB] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul, h4, h5, h7,
      Pi.add_apply, h8, Pi.add_apply, h9, h10, h11]
    simp only [HVZTen.tfun, HVZE3a.emap_apply]
    rw [h12, h13, h6, HVZE3.pot_split]
    push_cast; ring
  have hFn : ‖F‖ = 1 := by rw [hFdef, norm_T, hφ1, hg1, one_mul]
  refine ⟨⟨F, hΦ⟩, hFn, ?_⟩
  show ‖atomicHamiltonian γne γee (M + 1) ⟨F, hΦ⟩ - ((μ + s : ℝ) : ℂ) • F‖ ≤ _
  rw [hkey]
  have n1 : ‖T1‖ = ‖atomicHamiltonian γne γee M φ - (μ : ℂ) • (φ : LL M)‖ := by
    rw [hT1, norm_T, hg1, mul_one]
  have n2 : ‖T2‖ ≤ ε / 3 := by rw [hT2, norm_T, hφ1, one_mul]; exact hg2
  have tri : ‖T1 + T2 + hWF.toLp _‖ ≤ ‖T1‖ + ‖T2‖ + ‖hWF.toLp _‖ :=
    (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  linarith

end HVZE3x


end

section


set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate

/-! D2 (abstract Weyl criterion) pieces: bridge between `A` and its resolvent `R` at a real point `t`. -/

namespace HVZD2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma res_symm (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (x y : H) :
    ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ := by
  obtain ⟨hx, ex⟩ := hR.1 x
  obtain ⟨hy, ey⟩ := hR.1 y
  have hs : ⟪(R x : H), A ⟨R y, hy⟩⟫_ℂ = ⟪A ⟨R x, hx⟩, R y⟫_ℂ := hA.2 ⟨R x, hx⟩ ⟨R y, hy⟩
  calc ⟪R x, y⟫_ℂ = ⟪R x, A ⟨R y, hy⟩ - (t : ℂ) • R y⟫_ℂ := by rw [ey]
    _ = ⟪A ⟨R x, hx⟩ - (t : ℂ) • R x, R y⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right, inner_sub_left, inner_smul_left, Complex.conj_ofReal, hs]
    _ = ⟪x, R y⟫_ℂ := by rw [ex]

lemma res_isSelfAdjoint (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ)
    (R : H →L[ℂ] H) (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) : IsSelfAdjoint R :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (fun x y => res_symm A hA t R hR x y)

lemma mem_resolvent_of_not_mem (A : H →ₗ.[ℂ] H) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ) (hzt : z ≠ t)
    (hμ : (z - t)⁻¹ ∉ spectrum ℂ R) : z ∈ TeschlQM.Shared.resolventSet A := by
  rw [spectrum.mem_iff, not_not] at hμ
  have hc : z - (t : ℂ) ≠ 0 := sub_ne_zero.mpr hzt
  have hS : IsUnit ((1 : H →L[ℂ] H) - (z - t) • R) := by
    have : (1 : H →L[ℂ] H) - (z - t) • R =
        (z - t) • (algebraMap ℂ (H →L[ℂ] H) (z - t)⁻¹ - R) := by
      rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [this, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr hc).map _).mul hμ
  set S : H →L[ℂ] H := (1 : H →L[ℂ] H) - (z - t) • R with hSdef
  set U : H →L[ℂ] H := ↑(hS.unit⁻¹) with hU
  have hSU : S * U = 1 := hS.mul_val_inv
  have hUS : U * S = 1 := hS.val_inv_mul
  have key : ∀ v : H, U v - (z - t) • R (U v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) hSU
    simpa [hSdef] using this
  have key2 : ∀ v : H, U (v - (z - t) • R v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) hUS
    simpa [hSdef] using this
  refine ⟨R * U, fun φ => ?_, fun ψ => ?_⟩
  · obtain ⟨h, e⟩ := hR.1 (U φ)
    refine ⟨h, ?_⟩
    calc A ⟨(R * U) φ, h⟩ - z • (R * U) φ
        = (A ⟨R (U φ), h⟩ - (t : ℂ) • R (U φ)) - (z - t) • R (U φ) := by
          rw [sub_smul]; show A ⟨R (U φ), h⟩ - z • R (U φ) = _; abel
      _ = U φ - (z - t) • R (U φ) := by rw [e]
      _ = φ := key φ
  · set w : H := A ψ - (t : ℂ) • (ψ : H) with hw
    have hRw : R w = ψ := hR.2 ψ
    have : A ψ - z • (ψ : H) = w - (z - t) • R w := by
      rw [hRw, hw, sub_smul]; abel
    show R (U (A ψ - z • (ψ : H))) = ψ
    rw [this, key2, hRw]

lemma spec_real (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ)
    (hz : z ∉ TeschlQM.Shared.resolventSet A) :
    z.im = 0 ∧ z ≠ t ∧ (z - t)⁻¹ ∈ spectrum ℂ R := by
  have hzt : z ≠ t := fun h => hz (h ▸ ⟨R, hR⟩)
  have hμ : (z - t)⁻¹ ∈ spectrum ℂ R := by
    by_contra h; exact hz (mem_resolvent_of_not_mem A t R hR z hzt h)
  refine ⟨?_, hzt, hμ⟩
  have hre := (res_isSelfAdjoint A hA t R hR).mem_spectrum_eq_re hμ
  have h1 : ((z - t)⁻¹).im = 0 := by rw [hre]; simp
  rw [Complex.inv_im, div_eq_zero_iff, neg_eq_zero] at h1
  rcases h1 with h1 | h1
  · simpa using h1
  · exact absurd (Complex.normSq_eq_zero.mp h1) (sub_ne_zero.mpr hzt)

end HVZD2



open scoped InnerProductSpace ComplexConjugate
open Filter Topology

/-! D2 (abstract Weyl criterion), generic bounded self-adjoint part (W4/W5). -/

namespace HVZW

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- triangular bump at `c` of radius `r` -/
noncomputable def bump (c r : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x - c| / r)

/-- plateau cutoff: `1` on `|x - c| ≤ r`, `0` beyond `2r` -/
noncomputable def cut (c r : ℝ) (x : ℝ) : ℝ := min 1 (max 0 (2 - |x - c| / r))

lemma bump_cont (c r : ℝ) : Continuous (bump c r) := by
  unfold bump; fun_prop

lemma cut_cont (c r : ℝ) : Continuous (cut c r) := by
  unfold cut; fun_prop

lemma bump_eq_zero {c r x : ℝ} (hr : 0 < r) (hx : r ≤ |x - c|) : bump c r x = 0 := by
  unfold bump
  have : 1 ≤ |x - c| / r := (le_div_iff₀ hr).2 (by linarith)
  exact max_eq_left (by linarith)

lemma bump_self (c r : ℝ) : bump c r c = 1 := by
  simp [bump]

lemma cut_mul_bump {c r : ℝ} (hr : 0 < r) (x : ℝ) : cut c r x * bump c r x = bump c r x := by
  by_cases hx : r ≤ |x - c|
  · rw [bump_eq_zero hr hx, mul_zero]
  · push_neg at hx
    have : 1 ≤ 2 - |x - c| / r := by
      have : |x - c| / r < 1 := (div_lt_one hr).2 hx
      linarith
    have hc : cut c r x = 1 := by
      unfold cut; rw [max_eq_right (by linarith), min_eq_left this]
    rw [hc, one_mul]

lemma cut_bound {c r μ : ℝ} (hr : 0 < r) (x : ℝ) :
    |x * cut c r x - μ * cut c r x| ≤ |c - μ| + 2 * r := by
  have h0 : 0 ≤ cut c r x := le_min zero_le_one (le_max_left _ _)
  have h1 : cut c r x ≤ 1 := min_le_left _ _
  rw [← sub_mul, abs_mul, abs_of_nonneg h0]
  by_cases hx : 2 * r ≤ |x - c|
  · have : cut c r x = 0 := by
      unfold cut
      have : 2 ≤ |x - c| / r := (le_div_iff₀ hr).2 (by linarith)
      rw [max_eq_left (by linarith), min_eq_right zero_le_one]
    rw [this, mul_zero]; positivity
  · push_neg at hx
    have : |x - μ| ≤ |c - μ| + 2 * r := by
      calc |x - μ| = |(x - c) + (c - μ)| := by ring_nf
        _ ≤ |x - c| + |c - μ| := abs_add_le _ _
        _ ≤ |c - μ| + 2 * r := by linarith
    calc |x - μ| * cut c r x ≤ |x - μ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ _ := by linarith

variable (R : H →L[ℂ] H)

lemma cfc_symm (hR : IsSelfAdjoint R) (f : ℝ → ℝ) (u v : H) :
    ⟪cfc f R u, v⟫_ℂ = ⟪u, cfc f R v⟫_ℂ :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (IsSelfAdjoint.cfc (f := f) (a := R))) u v

/-- residual of a bump vector -/
lemma bump_resid (hR : IsSelfAdjoint R) {c r : ℝ} (hr : 0 < r) (μ : ℝ) (w : H) :
    ‖R (cfc (bump c r) R w) - (μ : ℂ) • cfc (bump c r) R w‖ ≤
      (|c - μ| + 2 * r) * ‖cfc (bump c r) R w‖ := by
  have hb := bump_cont c r
  have hk := cut_cont c r
  set φ := cfc (bump c r) R w with hφ
  have hfix : cfc (cut c r) R φ = φ := by
    have : cfc (bump c r) R = cfc (cut c r) R * cfc (bump c r) R := by
      rw [← cfc_mul (cut c r) (bump c r) R]
      exact cfc_congr (fun x _ => (cut_mul_bump hr x).symm)
    rw [hφ]; conv_rhs => rw [this]
    rfl
  have hop : R (cfc (cut c r) R φ) - (μ : ℂ) • cfc (cut c r) R φ =
      cfc (fun x => x * cut c r x - μ * cut c r x) R φ := by
    rw [cfc_sub (fun x => x * cut c r x) (fun x => μ * cut c r x) R,
      cfc_mul (fun x => x) (cut c r) R, cfc_id' ℝ R, cfc_const_mul μ (cut c r) R]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply]
    rw [← Complex.coe_smul]
  rw [← hfix, hop, hfix]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  gcongr
  refine norm_cfc_le (by positivity) (fun x _ => ?_)
  rw [Real.norm_eq_abs]
  exact cut_bound hr x

lemma bump_ne_zero (hR : IsSelfAdjoint R) {c r : ℝ} (hc : c ∈ spectrum ℝ R) :
    cfc (bump c r) R ≠ 0 := by
  intro h
  have hb := bump_cont c r
  have := norm_apply_le_norm_cfc (bump c r) R hc
  rw [h, bump_self, norm_zero, norm_one] at this
  exact absurd this (by norm_num)


end HVZW

namespace HVZE

open HVZD2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- E2: a normalized approximate-eigenvector sequence puts `z` in the spectrum. -/
lemma mem_spectrum_of_approx (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : ℕ → A.domain)
    (h1 : ∀ n, ‖(ψ n : H)‖ = 1)
    (hW : Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0)) :
    z ∈ TeschlQM.Shared.spectrum A := by
  show z ∉ TeschlQM.Shared.resolventSet A
  rintro ⟨R, hR⟩
  have hle : ∀ n, (1 : ℝ) ≤ ‖R‖ * ‖A (ψ n) - z • (ψ n : H)‖ := by
    intro n
    have := R.le_opNorm (A (ψ n) - z • (ψ n : H))
    rw [hR.2 (ψ n), h1 n] at this
    exact this
  have hlim : Tendsto (fun n => ‖R‖ * ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0) := by
    simpa using hW.const_mul ‖R‖
  have := ge_of_tendsto' hlim hle
  norm_num at this

/-- approximate eigenvectors of a bounded self-adjoint operator at a spectral point -/
lemma approx_seq_R (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) {μ : ℝ} (hμ : μ ∈ spectrum ℝ R) :
    ∃ φ : ℕ → H, (∀ n, ‖φ n‖ = 1) ∧
      Tendsto (fun n => ‖R (φ n) - (μ : ℂ) • φ n‖) atTop (𝓝 0) := by
  have hex : ∀ n : ℕ, ∃ w : H, cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R w ≠ 0 := by
    intro n
    have hne := HVZW.bump_ne_zero R hR (r := 1 / ((n : ℝ) + 1)) hμ
    by_contra h; push_neg at h; exact hne (ContinuousLinearMap.ext h)
  choose w hw using hex
  refine ⟨fun n => ((‖cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n)‖⁻¹ : ℝ) : ℂ) •
      cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n), fun n => ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hw n))]
  · have hb : ∀ n : ℕ, ‖R (((‖cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n)‖⁻¹ : ℝ) : ℂ) •
          cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n)) - (μ : ℂ) •
          ((((‖cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n)‖⁻¹ : ℝ) : ℂ) •
          cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n)))‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
      intro n
      set v := cfc (HVZW.bump μ (1 / ((n : ℝ) + 1))) R (w n) with hv
      have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have h0 := HVZW.bump_resid R hR hr μ (w n) (c := μ)
      rw [sub_self, abs_zero, zero_add, ← hv] at h0
      rw [map_smul, smul_comm (μ : ℂ), ← smul_sub, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr (hw n)
      rw [inv_mul_le_iff₀ hpos]
      exact h0.trans (le_of_eq (by ring))
    refine squeeze_zero (fun n => norm_nonneg _) hb ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa using this

/-- transfer of an approximate eigenvector sequence of the resolvent to `A` -/
lemma transfer' (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (t : ℝ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A (t : ℂ) R) (z : ℂ) (hzt : z ≠ t) (φ : ℕ → H)
    (hφ1 : ∀ n, ‖φ n‖ = 1)
    (hW : Tendsto (fun n => ‖R (φ n) - (z - t)⁻¹ • φ n‖) atTop (𝓝 0)) :
    ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
      Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0) := by
  have hc : z - (t : ℂ) ≠ 0 := sub_ne_zero.mpr hzt
  set μ : ℂ := (z - t)⁻¹ with hμ
  have hμ0 : μ ≠ 0 := inv_ne_zero hc
  have hinj : ∀ v : H, R v = 0 → v = 0 := by
    intro v hv
    obtain ⟨h, e⟩ := hR.1 v
    have h0 : (⟨R v, h⟩ : A.domain) = 0 := Subtype.ext hv
    rw [h0, LinearPMap.map_zero, hv, smul_zero, sub_zero] at e
    exact e.symm
  have hRne : ∀ n, R (φ n) ≠ 0 := by
    intro n h
    have := hinj _ h
    have h1 := hφ1 n
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  have hnorm : Tendsto (fun n => ‖R (φ n)‖) atTop (𝓝 ‖μ‖) := by
    have hconst : ∀ n, ‖μ • φ n‖ = ‖μ‖ := fun n => by rw [norm_smul, hφ1, mul_one]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hW
    rw [← hconst n, Real.norm_eq_abs]
    exact abs_norm_sub_norm_le _ _
  have hinv : Tendsto (fun n => ‖R (φ n)‖⁻¹) atTop (𝓝 ‖μ‖⁻¹) :=
    hnorm.inv₀ (norm_ne_zero_iff.mpr hμ0)
  let ψ : ℕ → A.domain := fun n =>
    ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) • (⟨R (φ n), (hR.1 (φ n)).1⟩ : A.domain)
  have hψc : ∀ n, (ψ n : H) = ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) • R (φ n) := fun n => rfl
  refine ⟨ψ, fun n => ?_, ?_⟩
  · rw [hψc, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hRne n))]
  · have h2 : ∀ n, A (ψ n) - z • (ψ n : H) =
        (((‖R (φ n)‖⁻¹ : ℝ) : ℂ) * (-(z - t))) • (R (φ n) - μ • φ n) := by
      intro n
      obtain ⟨h, e⟩ := hR.1 (φ n)
      have hA' : A (ψ n) = ((‖R (φ n)‖⁻¹ : ℝ) : ℂ) • A ⟨R (φ n), h⟩ :=
        LinearPMap.map_smul _ _ _
      have e' : A ⟨R (φ n), h⟩ = φ n + (t : ℂ) • R (φ n) := sub_eq_iff_eq_add.mp e
      have hk : (-(z - t)) • (R (φ n) - μ • φ n) = φ n - (z - t) • R (φ n) := by
        rw [smul_sub, smul_smul, neg_mul, hμ, mul_inv_cancel₀ hc]
        simp only [neg_smul, one_smul]
        abel
      rw [hA', hψc, mul_smul, hk, smul_comm z, ← smul_sub]
      congr 1
      rw [e', sub_smul]; abel
    simp only [h2, norm_smul, norm_mul, norm_neg, Complex.norm_real, norm_inv, norm_norm]
    have := (hinv.mul_const ‖z - (t : ℂ)‖).mul hW
    simpa using this

/-- E1: every spectral point of a symmetric operator with a real resolvent point carries a
normalized approximate-eigenvector sequence. -/
lemma approx_eigen (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (t : ℝ) (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) (z : ℂ)
    (hz : z ∈ TeschlQM.Shared.spectrum A) :
    z.im = 0 ∧ ∃ ψ : ℕ → A.domain, (∀ n, ‖(ψ n : H)‖ = 1) ∧
      Tendsto (fun n => ‖A (ψ n) - z • (ψ n : H)‖) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := ht
  obtain ⟨him, hzt, hμC⟩ := spec_real A hA t R hR z hz
  refine ⟨him, ?_⟩
  have hRsa := res_isSelfAdjoint A hA t R hR
  set μ : ℝ := (z.re - t)⁻¹ with hμ
  have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  have hμc : (z - t)⁻¹ = (μ : ℂ) := by
    rw [hμ, Complex.ofReal_inv, Complex.ofReal_sub]
    congr 1
    exact congrArg (· - (t : ℂ)) hzre
  have hμR : μ ∈ spectrum ℝ R := by
    apply (spectrum.algebraMap_mem_iff ℂ).1
    simpa [hμc] using hμC
  obtain ⟨φ, hφ1, hW⟩ := approx_seq_R R hRsa hμR
  exact transfer' A hA t R hR z hzt φ hφ1 (by rw [hμc]; exact hW)

end HVZE

namespace HVZD1

open MeasureTheory TeschlQM.Atomic

/-- E3 (core construction, OPEN): an approximate eigenvector of `H^{N-1}` at `μ`, tensored with a
translated plane-wave packet of energy `s` for the `N`-th electron. -/
def E3 : Prop :=
  ∀ (γne γee : ℝ), 0 < γne → 0 < γee → ∀ (N : ℕ), 1 ≤ N → ∀ (μ s : ℝ), 0 ≤ s →
    ∀ (φ : (atomicHamiltonian γne γee (N - 1)).domain),
      ‖(φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (N - 1) × Fin 3))))‖ = 1 →
      ∀ ε : ℝ, 0 < ε →
      ∃ Φ : (atomicHamiltonian γne γee N).domain,
        ‖(Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ = 1 ∧
        ‖atomicHamiltonian γne γee N Φ -
            ((μ + s : ℝ) : ℂ) • (Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ≤
          ‖atomicHamiltonian γne γee (N - 1) φ -
            (μ : ℂ) • (φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (N - 1) × Fin 3))))‖ + ε

/-- D1 from E1 (`HVZE.approx_eigen`), E2 (`HVZE.mem_spectrum_of_approx`), D0 and E3. -/
theorem d1_of_e3 (hE3 : E3)
    (hD0 : ∀ (γne γee : ℝ), 0 < γne → 0 < γee → ∀ M : ℕ,
      TeschlQM.Shared.IsSymmetric (atomicHamiltonian γne γee M) ∧
      ∃ t : ℝ, (t : ℂ) ∈ TeschlQM.Shared.resolventSet (atomicHamiltonian γne γee M))
    (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ)
    (hN : 1 ≤ N) (μ : ℝ) (hμ : (μ : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)))
    (s : ℝ) (hs : 0 ≤ s) :
    ((μ + s : ℝ) : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee N) := by
  obtain ⟨hsym, t, ht⟩ := hD0 γne γee hne hee (N - 1)
  obtain ⟨-, φ, hφ1, hφW⟩ := HVZE.approx_eigen _ hsym t ht (μ : ℂ) hμ
  have hex : ∀ n : ℕ, ∃ Φ : (atomicHamiltonian γne γee N).domain,
      ‖(Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ = 1 ∧
      ‖atomicHamiltonian γne γee N Φ -
          ((μ + s : ℝ) : ℂ) • (Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ≤
        ‖atomicHamiltonian γne γee (N - 1) (φ n) -
          (μ : ℂ) • (φ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (N - 1) × Fin 3))))‖ +
          1 / ((n : ℝ) + 1) :=
    fun n => hE3 γne γee hne hee N hN μ s hs (φ n) (hφ1 n) _ (by positivity)
  choose Φ hΦ1 hΦb using hex
  refine HVZE.mem_spectrum_of_approx _ _ Φ hΦ1 ?_
  refine squeeze_zero (fun n => norm_nonneg _) hΦb ?_
  have := hφW.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using this

end HVZD1


end

set_option autoImplicit false
open MeasureTheory TeschlQM.Atomic

namespace HVZD1

theorem e3 : E3 := by
  intro γne γee _ _ N hN μ s hs φ hφ ε hε
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact HVZE3x.e3' HVZE3b.e3b HVZE3d.e3d HVZTr.packetT γne γee M μ s hs φ hφ ε hε

end HVZD1

open TeschlQM.Atomic in
theorem solution (γne γee : ℝ) (hne : 0 < γne) (hee : 0 < γee) (N : ℕ) (hN : 1 ≤ N)
    (hsym : TeschlQM.Shared.IsSymmetric (atomicHamiltonian γne γee (N - 1)))
    (hres : ∃ t : ℝ, (t : ℂ) ∈ TeschlQM.Shared.resolventSet (atomicHamiltonian γne γee (N - 1)))
    (μ : ℝ) (hμ : (μ : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee (N - 1)))
    (s : ℝ) (hs : 0 ≤ s) :
    ((μ + s : ℝ) : ℂ) ∈ TeschlQM.Shared.spectrum (atomicHamiltonian γne γee N) := by
  obtain ⟨t, ht⟩ := hres
  obtain ⟨-, φ, hφ1, hφW⟩ := HVZE.approx_eigen _ hsym t ht (μ : ℂ) hμ
  have hex : ∀ n : ℕ, ∃ Φ : (atomicHamiltonian γne γee N).domain,
      ‖(Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ = 1 ∧
      ‖atomicHamiltonian γne γee N Φ -
          ((μ + s : ℝ) : ℂ) • (Φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ≤
        ‖atomicHamiltonian γne γee (N - 1) (φ n) -
          (μ : ℂ) • (φ n : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (N - 1) × Fin 3))))‖ +
          1 / ((n : ℝ) + 1) :=
    fun n => HVZD1.e3 γne γee hne hee N hN μ s hs (φ n) (hφ1 n) _ (by positivity)
  choose Φ hΦ1 hΦb using hex
  refine HVZE.mem_spectrum_of_approx _ _ Φ hΦ1 ?_
  refine squeeze_zero (fun n => norm_nonneg _) hΦb ?_
  have := hφW.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa using this
