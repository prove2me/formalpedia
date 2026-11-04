-- Prove2me | solution 1 for TaoBR.nikodymMaximalEstimate_of_kakeyaMaximalEstimate_and_kakeyaMaximalEstimate_two_mul_of_nikodymMaximalEstimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T16:33:49.036019+00:00
-- url     : https://prove2.me/submissions/7b136b89-22d8-4506-a3da-cb76969b4564

import Mathlib
import Definitions.Def_TaoBR

section S_PartI

/-!
# Part I of the Theorem 4.10 blueprint: infrastructure (I1–I7)
-/

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR.T410

/-- The test class: `Lᵖ` functions with bounded support. -/
def IsTest {n : ℕ} (p : ℝ) (f : E n → ℝ) : Prop :=
  MemLp f (ENNReal.ofReal p) volume ∧ Bornology.IsBounded (Function.support f)

/-- The Kakeya bound at a fixed `δ` with constant `A`, for nonnegative test functions. -/
def KBound (n : ℕ) (p δ A : ℝ) : Prop :=
  ∀ f : E n → ℝ, IsTest p f → (∀ x, 0 ≤ f x) →
    eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume

/-- The Nikodym bound at a fixed `δ` with constant `A`, for nonnegative test functions. -/
def NBound (n : ℕ) (p δ A : ℝ) : Prop :=
  ∀ f : E n → ℝ, IsTest p f → (∀ x, 0 ≤ f x) →
    eLpNorm (nikodymMaximal δ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume

end TaoBR.T410

namespace TaoBR.T410.PartI

open TaoBR.T410

/-! ## Basic facts about tubes -/

theorem isClosed_tube {n : ℕ} (δ : ℝ) (ω c : E n) : IsClosed (tube δ ω c) := by
  have h1 : Continuous fun x : E n => inner ℝ (x - c) ω :=
    (continuous_id.sub continuous_const).inner continuous_const
  have h2 : Continuous fun x : E n => x - c - inner ℝ (x - c) ω • ω :=
    (continuous_id.sub continuous_const).sub (h1.smul continuous_const)
  exact (isClosed_le h1.abs continuous_const).inter (isClosed_le h2.norm continuous_const)

theorem measurableSet_tube {n : ℕ} (δ : ℝ) (ω c : E n) : MeasurableSet (tube δ ω c) :=
  (isClosed_tube δ ω c).measurableSet

theorem tube_eq_preimage {n : ℕ} (δ : ℝ) (ω c : E n) :
    tube δ ω c = (fun x => x + (-c)) ⁻¹' tube δ ω 0 := by
  ext x; simp [tube, sub_eq_add_neg]

theorem volume_tube_eq_zero_center {n : ℕ} (δ : ℝ) (ω c : E n) :
    volume (tube δ ω c) = volume (tube δ ω 0) := by
  rw [tube_eq_preimage, measure_preimage_add_right]

theorem tube_preimage_isometry {n : ℕ} (δ : ℝ) (ω : E n) (U : E n ≃ₗᵢ[ℝ] E n) :
    U ⁻¹' tube δ (U ω) 0 = tube δ ω 0 := by
  ext x
  simp only [tube, Set.mem_preimage, sub_zero, Set.mem_ofPred_eq, LinearIsometryEquiv.inner_map_map]
  have : U x - inner ℝ x ω • U ω = U (x - inner ℝ x ω • ω) := by
    rw [map_sub, map_smul]
  rw [this, LinearIsometryEquiv.norm_map]

/-- I2. The volume of a tube depends only on `δ`. -/
theorem volume_tube_eq {n : ℕ} (δ : ℝ) (ω ω' c c' : E n) (hω : ‖ω‖ = 1) (hω' : ‖ω'‖ = 1) :
    volume (tube δ ω c) = volume (tube δ ω' c') := by
  rw [volume_tube_eq_zero_center, volume_tube_eq_zero_center δ ω' c']
  set U : E n ≃ₗᵢ[ℝ] E n := (ℝ ∙ (ω - ω'))ᗮ.reflection
  have hU : U ω = ω' := Submodule.reflection_sub (hω.trans hω'.symm)
  rw [← tube_preimage_isometry δ ω U, hU]
  exact (U.measurePreserving).measure_preimage (measurableSet_tube _ _ _).nullMeasurableSet

/-! ## I1: the volume of a tube is `K δ^(n-1)` -/

/-- The diagonal map fixing the `i₀` coordinate and scaling the others by `r`. -/
noncomputable def scaleMap {n : ℕ} (i₀ : Fin n) (r : ℝ) : E n →ₗ[ℝ] E n :=
  Matrix.toEuclideanLin (Matrix.diagonal (fun i => if i = i₀ then 1 else r))

theorem scaleMap_apply {n : ℕ} (i₀ : Fin n) (r : ℝ) (x : E n) (i : Fin n) :
    scaleMap i₀ r x i = (if i = i₀ then 1 else r) * x i := by
  simp [scaleMap, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]

theorem det_scaleMap {n : ℕ} (i₀ : Fin n) (r : ℝ) :
    LinearMap.det (scaleMap i₀ r) = r ^ (n - 1) := by
  rw [scaleMap, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]

theorem inner_single_eq {n : ℕ} (i₀ : Fin n) (x : E n) :
    inner ℝ x (EuclideanSpace.single i₀ (1 : ℝ)) = x i₀ := by
  simp [EuclideanSpace.inner_single_right]

theorem scaleMap_perp {n : ℕ} (i₀ : Fin n) (r : ℝ) (x : E n) :
    scaleMap i₀ r x - inner ℝ (scaleMap i₀ r x) (EuclideanSpace.single i₀ (1 : ℝ)) •
        EuclideanSpace.single i₀ (1 : ℝ) =
      r • (x - inner ℝ x (EuclideanSpace.single i₀ (1 : ℝ)) • EuclideanSpace.single i₀ (1 : ℝ)) := by
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, inner_single_eq, scaleMap_apply, smul_eq_mul,
    PiLp.single_apply]
  by_cases h : i = i₀
  · subst h; simp
  · simp [h]

theorem scaleMap_mem_tube {n : ℕ} (i₀ : Fin n) {r : ℝ} (hr : 0 < r) (s : ℝ) (x : E n) :
    scaleMap i₀ r x ∈ tube (r * s) (EuclideanSpace.single i₀ (1 : ℝ)) 0 ↔
      x ∈ tube s (EuclideanSpace.single i₀ (1 : ℝ)) 0 := by
  have h1 : inner ℝ (scaleMap i₀ r x) (EuclideanSpace.single i₀ (1 : ℝ)) =
      inner ℝ x (EuclideanSpace.single i₀ (1 : ℝ)) := by
    simp [inner_single_eq, scaleMap_apply]
  simp only [tube, sub_zero, Set.mem_ofPred_eq]
  rw [scaleMap_perp, h1, norm_smul, Real.norm_of_nonneg hr.le, mul_le_mul_iff_right₀ hr]

theorem scaleMap_comp {n : ℕ} (i₀ : Fin n) {r : ℝ} (hr : r ≠ 0) (x : E n) :
    scaleMap i₀ r (scaleMap i₀ r⁻¹ x) = x := by
  ext i
  simp only [scaleMap_apply]
  split_ifs <;> field_simp

theorem image_scaleMap_tube {n : ℕ} (i₀ : Fin n) {δ : ℝ} (hδ : 0 < δ) :
    scaleMap i₀ δ '' tube 1 (EuclideanSpace.single i₀ (1 : ℝ)) 0 =
      tube δ (EuclideanSpace.single i₀ (1 : ℝ)) 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := (scaleMap_mem_tube i₀ hδ 1 x).2 hx
    rwa [mul_one] at this
  · intro hy
    refine ⟨scaleMap i₀ δ⁻¹ y, ?_, scaleMap_comp i₀ hδ.ne' y⟩
    rw [← scaleMap_mem_tube i₀ hδ 1, scaleMap_comp i₀ hδ.ne', mul_one]
    exact hy

theorem volume_tube_single {n : ℕ} (i₀ : Fin n) {δ : ℝ} (hδ : 0 < δ) :
    volume (tube δ (EuclideanSpace.single i₀ (1 : ℝ)) 0) =
      ENNReal.ofReal (δ ^ (n - 1)) * volume (tube 1 (EuclideanSpace.single i₀ (1 : ℝ)) 0) := by
  rw [← image_scaleMap_tube i₀ hδ, MeasureTheory.Measure.addHaar_image_linearMap, det_scaleMap,
    abs_of_nonneg (pow_nonneg hδ.le _)]

theorem tube_subset_closedBall {n : ℕ} {δ : ℝ} {ω c : E n} (hω : ‖ω‖ = 1) :
    tube δ ω c ⊆ closedBall c (1 / 2 + δ) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  rw [mem_closedBall, dist_eq_norm]
  have : x - c = (x - c - inner ℝ (x - c) ω • ω) + inner ℝ (x - c) ω • ω := by abel
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs]
  linarith

theorem ball_subset_tube {n : ℕ} {ω : E n} (hω : ‖ω‖ = 1) {r δ : ℝ} (h1 : r ≤ 1 / 2)
    (h2 : 2 * r ≤ δ) : ball (0 : E n) r ⊆ tube δ ω 0 := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have hi : |inner ℝ x ω| ≤ ‖x‖ := by
    have := abs_real_inner_le_norm x ω
    rwa [hω, mul_one] at this
  refine ⟨by rw [sub_zero]; linarith, ?_⟩
  rw [sub_zero]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs]
  linarith

theorem ball_subset_tube_one {n : ℕ} {ω : E n} (hω : ‖ω‖ = 1) :
    ball (0 : E n) (1 / 2) ⊆ tube 1 ω 0 :=
  ball_subset_tube hω le_rfl (by norm_num)

/-- I1. The volume of a `1 × δ` tube is comparable to `δ^(n-1)`. -/
theorem tube_volume_bounds (n : ℕ) (hn : 1 ≤ n) : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ω c : E n, ‖ω‖ = 1 →
      ENNReal.ofReal (c₁ * δ ^ (n - 1)) ≤ volume (tube δ ω c) ∧
      volume (tube δ ω c) ≤ ENNReal.ofReal (c₂ * δ ^ (n - 1)) := by
  set i₀ : Fin n := ⟨0, hn⟩
  set e : E n := EuclideanSpace.single i₀ (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  set K := volume (tube 1 e 0)
  have hK0 : 0 < K :=
    (measure_ball_pos volume (0 : E n) (by norm_num : (0 : ℝ) < 1 / 2)).trans_le
      (measure_mono (ball_subset_tube_one he))
  have hKt : K < ∞ :=
    (measure_mono (tube_subset_closedBall he)).trans_lt measure_closedBall_lt_top
  have hK : 0 < K.toReal := ENNReal.toReal_pos hK0.ne' hKt.ne
  have key : ∀ δ : ℝ, 0 < δ → ∀ ω c : E n, ‖ω‖ = 1 →
      volume (tube δ ω c) = ENNReal.ofReal (K.toReal * δ ^ (n - 1)) := by
    intro δ hδ ω c hω
    rw [volume_tube_eq δ ω e c 0 hω he, volume_tube_single i₀ hδ, ENNReal.ofReal_mul hK.le,
      ENNReal.ofReal_toReal hKt.ne, mul_comm]
  refine ⟨K.toReal, K.toReal, hK, hK, fun δ hδ _ ω c hω => ?_⟩
  rw [key δ hδ ω c hω]
  exact ⟨le_rfl, le_rfl⟩

/-! ## I7: polar coordinates on an annulus -/

theorem volumeIoiPow_annulus (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Measure.volumeIoiPow m {r : Set.Ioi (0 : ℝ) | a < r.1 ∧ r.1 < b} =
      ENNReal.ofReal ((b ^ (m + 1) - a ^ (m + 1)) / (m + 1)) := by
  have hS : MeasurableSet {r : Set.Ioi (0 : ℝ) | a < r.1 ∧ r.1 < b} :=
    (measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_lt measurable_subtype_coe measurable_const)
  have himg : ((↑) : Set.Ioi (0 : ℝ) → ℝ) '' {r : Set.Ioi (0 : ℝ) | a < r.1 ∧ r.1 < b} =
      Set.Ioo a b := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩; exact hr
    · intro hx; exact ⟨⟨x, ha.trans hx.1⟩, hx, rfl⟩
  rw [Measure.volumeIoiPow, withDensity_apply _ hS,
    setLIntegral_subtype measurableSet_Ioi _ fun a : ℝ ↦ .ofReal (a ^ m), himg,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_pow _).1,
    ← intervalIntegral.integral_of_le hab.le]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact pow_nonneg (ha.trans hy.1).le _

/-- I7. Polar coordinates on an annulus, for a function of the direction only. -/
theorem lintegral_annulus {n : ℕ} (hn : 2 ≤ n) (G : E n → ℝ≥0∞) (hG : Measurable G)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫⁻ x in {x : E n | a < ‖x‖ ∧ ‖x‖ < b}, G (‖x‖⁻¹ • x) =
      ENNReal.ofReal ((b ^ n - a ^ n) / n) * ∫⁻ ω, G (ω : E n) ∂(sphereMeasure n) := by
  have hdim : Module.finrank ℝ (E n) = n := finrank_euclideanSpace_fin
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set A : Set (E n) := {x : E n | a < ‖x‖ ∧ ‖x‖ < b}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  set S : Set (Set.Ioi (0 : ℝ)) := {r : Set.Ioi (0 : ℝ) | a < r.1 ∧ r.1 < b}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_lt measurable_subtype_coe measurable_const)
  set g : sphere (0 : E n) 1 × Set.Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun y => G (y.1 : E n) * S.indicator 1 y.2
  have hg : Measurable g :=
    (hG.comp (measurable_subtype_coe.comp measurable_fst)).mul
      ((measurable_one.indicator hS).comp measurable_snd)
  have hcomp : ∀ x : ({(0 : E n)}ᶜ : Set (E n)),
      A.indicator (fun x => G (‖x‖⁻¹ • x)) (x : E n) = g (homeomorphUnitSphereProd (E n) x) := by
    intro x
    simp only [g, A, S, Set.indicator, Set.mem_ofPred_eq, homeomorphUnitSphereProd_apply_snd_coe,
      homeomorphUnitSphereProd_apply_fst_coe, Pi.one_apply]
    split_ifs <;> simp
  calc ∫⁻ x in A, G (‖x‖⁻¹ • x)
      = ∫⁻ x, A.indicator (fun x => G (‖x‖⁻¹ • x)) x := (lintegral_indicator hA _).symm
    _ = ∫⁻ x in ({(0 : E n)}ᶜ : Set (E n)), A.indicator (fun x => G (‖x‖⁻¹ • x)) x := by
        rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({(0 : E n)}ᶜ : Set (E n)), A.indicator (fun x => G (‖x‖⁻¹ • x)) x.1
          ∂(volume.comap Subtype.val) :=
        (lintegral_subtype_comap (measurableSet_singleton _).compl _).symm
    _ = ∫⁻ x : ({(0 : E n)}ᶜ : Set (E n)), g (homeomorphUnitSphereProd (E n) x)
          ∂(volume.comap Subtype.val) := by
        congr 1; funext x; exact hcomp x
    _ = ∫⁻ y, g y ∂((volume : Measure (E n)).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1))) :=
        (volume.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) g
    _ = (∫⁻ ω, G (ω : E n) ∂(sphereMeasure n)) *
          Measure.volumeIoiPow (Module.finrank ℝ (E n) - 1) S := by
        show ∫⁻ y : sphere (0 : E n) 1 × Set.Ioi (0 : ℝ), (fun ω : sphere (0 : E n) 1 => G ω) y.1 * S.indicator 1 y.2 ∂_ = _
        rw [lintegral_prod_mul (f := fun ω : sphere (0 : E n) 1 => G ω) (g := S.indicator 1)
          (hG.comp measurable_subtype_coe).aemeasurable
          (measurable_one.indicator hS).aemeasurable, lintegral_indicator_one hS]
        rfl
    _ = _ := by
        rw [mul_comm, hdim, volumeIoiPow_annulus _ ha hab, Nat.sub_add_cancel (by omega : 1 ≤ n),
          Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, sub_add_cancel]

/-! ## Tube volumes, convexity and continuity of tube integrals -/

open Filter Topology

theorem mem_tube_iff_sub {n : ℕ} (δ : ℝ) (ω c x : E n) : x ∈ tube δ ω c ↔ x - c ∈ tube δ ω 0 := by
  simp [tube]

theorem volume_tube_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {ω : E n} (hω : ‖ω‖ = 1) (c : E n) :
    0 < volume (tube δ ω c) := by
  rw [volume_tube_eq_zero_center]
  have hr : 0 < min (1 / 2) (δ / 2) := lt_min (by norm_num) (by linarith)
  exact (measure_ball_pos volume (0 : E n) hr).trans_le (measure_mono
    (ball_subset_tube hω (min_le_left _ _) (by linarith [min_le_right (1 / 2 : ℝ) (δ / 2)])))

theorem volume_tube_lt_top {n : ℕ} (δ : ℝ) {ω : E n} (hω : ‖ω‖ = 1) (c : E n) :
    volume (tube δ ω c) < ∞ :=
  (measure_mono (tube_subset_closedBall hω)).trans_lt measure_closedBall_lt_top

/-- A fixed unit vector. -/
noncomputable def unitE {n : ℕ} (hn : 1 ≤ n) : E n := EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ)

theorem norm_unitE {n : ℕ} (hn : 1 ≤ n) : ‖unitE hn‖ = 1 := by simp [unitE]

/-- The common volume of the `1 × δ` tubes. -/
noncomputable def tubeVol {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : ℝ := (volume (tube δ (unitE hn) 0)).toReal

theorem toReal_volume_tube {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) {ω : E n} (hω : ‖ω‖ = 1) (c : E n) :
    (volume (tube δ ω c)).toReal = tubeVol hn δ := by
  rw [tubeVol, volume_tube_eq δ ω (unitE hn) c 0 hω (norm_unitE hn)]

theorem tubeVol_pos {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) : 0 < tubeVol hn δ :=
  ENNReal.toReal_pos (volume_tube_pos hδ (norm_unitE hn) 0).ne'
    (volume_tube_lt_top δ (norm_unitE hn) 0).ne

theorem ofReal_tubeVol {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) {ω : E n} (hω : ‖ω‖ = 1) (c : E n) :
    ENNReal.ofReal (tubeVol hn δ) = volume (tube δ ω c) := by
  rw [← toReal_volume_tube hn δ hω c, ENNReal.ofReal_toReal (volume_tube_lt_top δ hω c).ne]

theorem convex_tube {n : ℕ} (δ : ℝ) (ω c : E n) : Convex ℝ (tube δ ω c) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hxy : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    calc a • x + b • y - c = a • x + b • y - (a + b) • c := by rw [hab, one_smul]
      _ = _ := by module
  have hin : inner ℝ (a • x + b • y - c) ω = a * inner ℝ (x - c) ω + b * inner ℝ (y - c) ω := by
    rw [hxy, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  constructor
  · rw [hin]
    calc |a * inner ℝ (x - c) ω + b * inner ℝ (y - c) ω|
        ≤ |a * inner ℝ (x - c) ω| + |b * inner ℝ (y - c) ω| := abs_add_le _ _
      _ = a * |inner ℝ (x - c) ω| + b * |inner ℝ (y - c) ω| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * (1 / 2) + b * (1 / 2) := by gcongr
      _ = 1 / 2 := by rw [← add_mul, hab, one_mul]
  · have : a • x + b • y - c - inner ℝ (a • x + b • y - c) ω • ω =
        a • (x - c - inner ℝ (x - c) ω • ω) + b • (y - c - inner ℝ (y - c) ω • ω) := by
      rw [hin, hxy]; module
    rw [this]
    calc ‖a • (x - c - inner ℝ (x - c) ω • ω) + b • (y - c - inner ℝ (y - c) ω • ω)‖
        ≤ ‖a • (x - c - inner ℝ (x - c) ω • ω)‖ + ‖b • (y - c - inner ℝ (y - c) ω • ω)‖ :=
          norm_add_le _ _
      _ = a * ‖x - c - inner ℝ (x - c) ω • ω‖ + b * ‖y - c - inner ℝ (y - c) ω • ω‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * δ + b * δ := by gcongr
      _ = δ := by rw [← add_mul, hab, one_mul]

theorem strict_of_mem_interior {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {ω c y : E n} (hω : ‖ω‖ = 1)
    (hy : y ∈ interior (tube δ ω c)) :
    |inner ℝ (y - c) ω| < 1 / 2 ∧ ‖y - c - inner ℝ (y - c) ω • ω‖ < δ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hsub : ball y ε ⊆ tube δ ω c := hball.trans interior_subset
  have hωω : inner ℝ ω ω = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  set s := inner ℝ (y - c) ω with hs
  constructor
  · have key : ∀ t : ℝ, |t| < ε → |s + t| ≤ 1 / 2 := by
      intro t ht
      have hz : y + t • ω ∈ tube δ ω c := hsub (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs]
        exact ht)
      have h1 := hz.1
      have : y + t • ω - c = (y - c) + t • ω := by abel
      rwa [this, inner_add_left, real_inner_smul_left, hωω, mul_one] at h1
    have hε2 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
    have hε2' : |-(ε / 2)| < ε := by rw [abs_neg]; exact hε2
    rcases le_or_gt 0 s with h | h
    · have := key _ hε2
      rw [abs_of_nonneg (by linarith)] at this
      rw [abs_of_nonneg h]; linarith
    · have := key _ hε2'
      rw [abs_of_neg (by linarith)] at this
      rw [abs_of_neg h]; linarith
  · set v := y - c - s • ω with hv
    by_cases hv0 : v = 0
    · rw [hv0, norm_zero]; exact hδ
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set k := ε / (2 * ‖v‖)
    have hk : 0 < k := by positivity
    have hkv : k * ‖v‖ = ε / 2 := by
      simp only [k]; field_simp
    have hz : y + k • v ∈ tube δ ω c := hsub (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hk.le, hkv]
      linarith)
    have hvω : inner ℝ v ω = 0 := by
      rw [hv, inner_sub_left, real_inner_smul_left, hωω, ← hs]; ring
    have hzs : inner ℝ (y + k • v - c) ω = s := by
      have : y + k • v - c = (y - c) + k • v := by abel
      rw [this, inner_add_left, real_inner_smul_left, hvω, mul_zero, add_zero]
    have h2 := hz.2
    rw [hzs] at h2
    have : y + k • v - c - s • ω = (1 + k) • v := by rw [hv]; module
    rw [this, norm_smul, Real.norm_of_nonneg (by linarith)] at h2
    nlinarith

/-- For an integrable `f`, the tube integral is continuous in `(ω, c)` at unit `ω`. -/
theorem continuousAt_setIntegral_tube {n : ℕ} {f : E n → ℝ} (hf : Integrable f) {δ : ℝ}
    (hδ : 0 < δ) {ω₀ c₀ : E n} (hω₀ : ‖ω₀‖ = 1) :
    ContinuousAt (fun q : E n × E n => ∫ y in tube δ q.1 q.2, f y) (ω₀, c₀) := by
  have heq : (fun q : E n × E n => ∫ y in tube δ q.1 q.2, f y) =
      fun q => ∫ y, (tube δ q.1 q.2).indicator f y := by
    funext q; rw [integral_indicator (measurableSet_tube _ _ _)]
  rw [heq]
  refine continuousAt_of_dominated (bound := fun y => ‖f y‖)
    (Eventually.of_forall fun q => hf.aestronglyMeasurable.indicator (measurableSet_tube _ _ _))
    (Eventually.of_forall fun q => Eventually.of_forall fun y => norm_indicator_le_norm_self _ _)
    hf.norm ?_
  have hnull : volume (frontier (tube δ ω₀ c₀)) = 0 :=
    (convex_tube δ ω₀ c₀).addHaar_frontier volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
  have hs : Continuous fun q : E n × E n => inner ℝ (y - q.2) q.1 :=
    (continuous_const.sub continuous_snd).inner continuous_fst
  have hv : Continuous fun q : E n × E n => y - q.2 - inner ℝ (y - q.2) q.1 • q.1 :=
    (continuous_const.sub continuous_snd).sub (hs.smul continuous_fst)
  by_cases hin : y ∈ tube δ ω₀ c₀
  · have hint : y ∈ interior (tube δ ω₀ c₀) := by
      rw [frontier, (isClosed_tube _ _ _).closure_eq] at hy
      by_contra h; exact hy ⟨hin, h⟩
    obtain ⟨h1, h2⟩ := strict_of_mem_interior hδ hω₀ hint
    have ev : ∀ᶠ q in 𝓝 (ω₀, c₀), y ∈ tube δ q.1 q.2 := by
      have e1 : ∀ᶠ q in 𝓝 (ω₀, c₀), |inner ℝ (y - q.2) q.1| < 1 / 2 :=
        hs.abs.continuousAt.eventually_lt continuousAt_const h1
      have e2 : ∀ᶠ q in 𝓝 (ω₀, c₀), ‖y - q.2 - inner ℝ (y - q.2) q.1 • q.1‖ < δ :=
        hv.norm.continuousAt.eventually_lt continuousAt_const h2
      filter_upwards [e1, e2] with q hq1 hq2
      exact ⟨hq1.le, hq2.le⟩
    have : (fun _ : E n × E n => f y) =ᶠ[𝓝 (ω₀, c₀)] fun q => (tube δ q.1 q.2).indicator f y := by
      filter_upwards [ev] with q hq
      exact (Set.indicator_of_mem hq f).symm
    exact continuousAt_const.congr this
  · have hout : 1 / 2 < |inner ℝ (y - c₀) ω₀| ∨ δ < ‖y - c₀ - inner ℝ (y - c₀) ω₀ • ω₀‖ := by
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact hin ⟨h.1, h.2⟩
    have ev : ∀ᶠ q in 𝓝 (ω₀, c₀), y ∉ tube δ q.1 q.2 := by
      rcases hout with h | h
      · have e1 : ∀ᶠ q in 𝓝 (ω₀, c₀), 1 / 2 < |inner ℝ (y - q.2) q.1| :=
          continuousAt_const.eventually_lt hs.abs.continuousAt h
        filter_upwards [e1] with q hq hmem
        exact absurd hmem.1 (not_le.2 hq)
      · have e2 : ∀ᶠ q in 𝓝 (ω₀, c₀), δ < ‖y - q.2 - inner ℝ (y - q.2) q.1 • q.1‖ :=
          continuousAt_const.eventually_lt hv.norm.continuousAt h
        filter_upwards [e2] with q hq hmem
        exact absurd hmem.2 (not_le.2 hq)
    have : (fun _ : E n × E n => (0 : ℝ)) =ᶠ[𝓝 (ω₀, c₀)]
        fun q => (tube δ q.1 q.2).indicator f y := by
      filter_upwards [ev] with q hq
      exact (Set.indicator_of_notMem hq f).symm
    exact continuousAt_const.congr this

/-! ## Test functions -/

theorem integrable_of_isTest {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {f : E n → ℝ} (hf : IsTest p f) :
    Integrable f := by
  obtain ⟨R, hR⟩ := hf.2.subset_closedBall 0
  have : MemLp f 1 volume :=
    hf.1.mono_exponent_of_measure_support_ne_top (s := closedBall 0 R)
      (fun x hx => by by_contra h; exact hx (hR h)) measure_closedBall_lt_top.ne
      (ENNReal.one_le_ofReal.2 hp)
  exact memLp_one_iff_integrable.1 this

theorem abs_setIntegral_le_integral_abs {n : ℕ} {f : E n → ℝ} (hf : Integrable f) (s : Set (E n)) :
    |∫ y in s, f y| ≤ ∫ y, |f y| :=
  (abs_integral_le_integral_abs).trans
    (setIntegral_le_integral hf.abs (Eventually.of_forall fun _ => abs_nonneg _))

theorem abs_avg_le_L1 {n : ℕ} (hn : 1 ≤ n) {f : E n → ℝ} (hf : Integrable f) (δ : ℝ) (s : Set (E n)) :
    |(tubeVol hn δ)⁻¹ * ∫ y in s, f y| ≤ |(tubeVol hn δ)⁻¹| * ∫ y, |f y| := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_setIntegral_le_integral_abs hf s) (abs_nonneg _)

/-! ## I3, I4: measurability -/

theorem kakeyaMaximal_eq {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) (f : E n → ℝ) :
    kakeyaMaximal δ f =
      fun ω : sphere (0 : E n) 1 => ⨆ c : E n, (tubeVol hn δ)⁻¹ * ∫ y in tube δ ω c, f y := by
  funext ω
  simp only [kakeyaMaximal]
  congr 1; funext c
  rw [toReal_volume_tube hn δ (mem_sphere_zero_iff_norm.1 ω.2)]

/-- I3. Measurability of the Kakeya maximal function of a test function. -/
theorem kakeyaMaximal_aestronglyMeasurable {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 1 ≤ p)
    (hδ : 0 < δ) {f : E n → ℝ} (hf : IsTest p f) :
    AEStronglyMeasurable (kakeyaMaximal δ f) (sphereMeasure n) := by
  have hn1 : 1 ≤ n := by omega
  have hfi := integrable_of_isTest hp hf
  rw [kakeyaMaximal_eq hn1]
  refine (LowerSemicontinuous.measurable ?_).aestronglyMeasurable
  refine lowerSemicontinuous_ciSup (fun ω => ⟨|(tubeVol hn1 δ)⁻¹| * ∫ y, |f y|, ?_⟩) (fun c => ?_)
  · rintro _ ⟨c, rfl⟩
    exact (le_abs_self _).trans (abs_avg_le_L1 hn1 hfi δ _)
  · refine (continuous_const.mul ?_).lowerSemicontinuous
    rw [continuous_iff_continuousAt]
    intro ω
    have hc : Continuous fun ω : sphere (0 : E n) 1 => ((ω : E n), c) :=
      continuous_subtype_val.prodMk continuous_const
    exact ContinuousAt.comp (f := fun ω : sphere (0 : E n) 1 => ((ω : E n), c))
      (continuousAt_setIntegral_tube hfi hδ (mem_sphere_zero_iff_norm.1 ω.2)) hc.continuousAt

/-- Reindexing the Nikodym supremum by `(ω, x - c)`. -/
abbrev nikIdx {n : ℕ} (δ : ℝ) : Type := {P : E n × E n // ‖P.1‖ = 1 ∧ P.2 ∈ tube δ P.1 0}

def nikEquiv {n : ℕ} (δ : ℝ) (x : E n) :
    nikIdx (n := n) δ ≃ {T : E n × E n // ‖T.1‖ = 1 ∧ x ∈ tube δ T.1 T.2} where
  toFun P := ⟨(P.1.1, x - P.1.2), P.2.1, by
    rw [mem_tube_iff_sub, sub_sub_cancel]; exact P.2.2⟩
  invFun T := ⟨(T.1.1, x - T.1.2), T.2.1, by rw [← mem_tube_iff_sub]; exact T.2.2⟩
  left_inv P := by apply Subtype.ext; simp
  right_inv T := by apply Subtype.ext; simp

theorem nikodymMaximal_eq {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) (f : E n → ℝ) :
    nikodymMaximal δ f = fun x => ⨆ P : nikIdx (n := n) δ,
      (tubeVol hn δ)⁻¹ * ∫ y in tube δ P.1.1 (x - P.1.2), f y := by
  funext x
  rw [nikodymMaximal, ← (nikEquiv δ x).iSup_comp]
  congr 1; funext P
  change (volume (tube δ P.1.1 (x - P.1.2))).toReal⁻¹ * ∫ y in tube δ P.1.1 (x - P.1.2), f y = _
  rw [toReal_volume_tube hn δ P.2.1]

/-- I4. Measurability of the Nikodym maximal function of a test function. -/
theorem nikodymMaximal_aestronglyMeasurable {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 1 ≤ p)
    (hδ : 0 < δ) {f : E n → ℝ} (hf : IsTest p f) :
    AEStronglyMeasurable (nikodymMaximal δ f) volume := by
  have hn1 : 1 ≤ n := by omega
  have hfi := integrable_of_isTest hp hf
  rw [nikodymMaximal_eq hn1]
  refine (LowerSemicontinuous.measurable ?_).aestronglyMeasurable
  refine lowerSemicontinuous_ciSup (fun x => ⟨|(tubeVol hn1 δ)⁻¹| * ∫ y, |f y|, ?_⟩) (fun P => ?_)
  · rintro _ ⟨c, rfl⟩
    exact (le_abs_self _).trans (abs_avg_le_L1 hn1 hfi δ _)
  · refine (continuous_const.mul ?_).lowerSemicontinuous
    rw [continuous_iff_continuousAt]
    intro x
    have hc : Continuous fun x : E n => (P.1.1, x - P.1.2) :=
      continuous_const.prodMk (continuous_id.sub continuous_const)
    exact ContinuousAt.comp (f := fun x : E n => (P.1.1, x - P.1.2))
      (continuousAt_setIntegral_tube hfi hδ P.2.1) hc.continuousAt

/-! ## Pointwise comparison of maximal functions -/

theorem bddAbove_avg {n : ℕ} (hn : 1 ≤ n) {f : E n → ℝ} (hf : Integrable f) (δ : ℝ)
    {ι : Type*} (s : ι → Set (E n)) :
    BddAbove (Set.range fun i => (tubeVol hn δ)⁻¹ * ∫ y in s i, f y) := by
  refine ⟨|(tubeVol hn δ)⁻¹| * ∫ y, |f y|, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact (le_abs_self _).trans (abs_avg_le_L1 hn hf δ _)

theorem abs_ciSup_sub_le {ι : Type*} [Nonempty ι] {a b : ι → ℝ} (ha : BddAbove (Set.range a))
    (hb : BddAbove (Set.range b)) {M : ℝ} (h : ∀ i, |a i - b i| ≤ M) :
    |(⨆ i, a i) - ⨆ i, b i| ≤ M := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine ciSup_le fun i => ?_
    have := (abs_sub_le_iff.1 (h i)).1
    linarith [le_ciSup hb i]
  · rw [sub_le_iff_le_add]
    refine ciSup_le fun i => ?_
    have := (abs_sub_le_iff.1 (h i)).2
    linarith [le_ciSup ha i]

/-- Hölder on a tube. -/
theorem abs_avg_le_Lp {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    {h : E n → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume) {ω c : E n} (hω : ‖ω‖ = 1)
    (S : Set (E n)) (hS : tube δ ω c ⊆ S) :
    |(tubeVol hn δ)⁻¹ * ∫ y in tube δ ω c, h y| ≤
      tubeVol hn δ ^ (-(1 / p)) * (eLpNorm h (ENNReal.ofReal p) (volume.restrict S)).toReal := by
  set T := tube δ ω c
  set V := tubeVol hn δ
  have hV : 0 < V := tubeVol_pos hn hδ
  have hVT : volume T = ENNReal.ofReal V := (ofReal_tubeVol hn δ hω c).symm
  have h1 : |∫ y in T, h y| ≤ (eLpNorm h 1 (volume.restrict T)).toReal := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [integral_norm_eq_lintegral_enorm hh.aestronglyMeasurable.restrict,
      eLpNorm_one_eq_lintegral_enorm]
  have h2 : eLpNorm h 1 (volume.restrict T) ≤ eLpNorm h (ENNReal.ofReal p) (volume.restrict T) *
      (volume.restrict T Set.univ) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.one_le_ofReal.2 hp)
      hh.aestronglyMeasurable.restrict
  rw [Measure.restrict_apply_univ, hVT, ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith),
    div_one] at h2
  have h3 : eLpNorm h (ENNReal.ofReal p) (volume.restrict T) ≤
      eLpNorm h (ENNReal.ofReal p) (volume.restrict S) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hS le_rfl)
  have hfin : eLpNorm h (ENNReal.ofReal p) (volume.restrict S) < ∞ :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt hh.eLpNorm_lt_top
  have h4 : (eLpNorm h 1 (volume.restrict T)).toReal ≤
      (eLpNorm h (ENNReal.ofReal p) (volume.restrict S)).toReal * V ^ (1 - 1 / p) := by
    have h5 := h2.trans (mul_le_mul_left h3 _)
    rw [ENNReal.ofReal_rpow_of_pos hV] at h5
    have h6 := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin.ne ENNReal.ofReal_ne_top) h5
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h6
  rw [abs_mul, abs_of_pos (inv_pos.2 hV)]
  calc V⁻¹ * |∫ y in T, h y|
      ≤ V⁻¹ * ((eLpNorm h (ENNReal.ofReal p) (volume.restrict S)).toReal * V ^ (1 - 1 / p)) := by
        gcongr; exact h1.trans h4
    _ = V ^ (-(1 / p)) * (eLpNorm h (ENNReal.ofReal p) (volume.restrict S)).toReal := by
        rw [show V ^ (-(1 / p)) = V⁻¹ * V ^ (1 - 1 / p) by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hV]; ring_nf]
        ring

theorem abs_kakeyaMaximal_sub_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    {f g : E n → ℝ} (hf : IsTest p f) (hg : IsTest p g) (ω : sphere (0 : E n) 1) :
    |kakeyaMaximal δ f ω - kakeyaMaximal δ g ω| ≤
      tubeVol hn δ ^ (-(1 / p)) * (eLpNorm (f - g) (ENNReal.ofReal p) volume).toReal := by
  have hfi := integrable_of_isTest hp hf
  have hgi := integrable_of_isTest hp hg
  rw [kakeyaMaximal_eq hn, kakeyaMaximal_eq hn]
  refine abs_ciSup_sub_le (bddAbove_avg hn hfi δ _) (bddAbove_avg hn hgi δ _) fun c => ?_
  rw [← mul_sub, ← integral_sub hfi.integrableOn hgi.integrableOn]
  have := abs_avg_le_Lp hn hp hδ (hf.1.sub hg.1) (c := c) (mem_sphere_zero_iff_norm.1 ω.2) Set.univ
    (Set.subset_univ _)
  simpa only [Measure.restrict_univ, Pi.sub_apply] using this

theorem isTest_of_contDiff {n : ℕ} (p : ℝ) {g : E n → ℝ} (hg1 : HasCompactSupport g)
    (hg2 : Continuous g) : IsTest p g :=
  ⟨hg2.memLp_of_hasCompactSupport hg1, hg1.isCompact.isBounded.subset (subset_tsupport g)⟩

theorem eLpNorm_le_add_sub {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {f g : E n → ℝ} (hf : IsTest p f)
    (hg : IsTest p g) :
    eLpNorm g (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume + eLpNorm (f - g) (ENNReal.ofReal p) volume := by
  have : g = f - (f - g) := by abel
  calc eLpNorm g (ENNReal.ofReal p) volume = eLpNorm (f - (f - g)) (ENNReal.ofReal p) volume := by
        rw [← this]
    _ ≤ _ := eLpNorm_sub_le hf.1.aestronglyMeasurable (hf.1.sub hg.1).aestronglyMeasurable
        (ENNReal.one_le_ofReal.2 hp)

/-- Density step for the Kakeya maximal function at a fixed `δ`. -/
theorem kakeya_bound_of_schwartz {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ) (hA : ∀ g : 𝓢(E n, ℝ), HasCompactSupport g →
      eLpNorm (kakeyaMaximal δ g) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal p) volume)
    {f : E n → ℝ} (hf : IsTest p f) :
    eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  have hn1 : 1 ≤ n := by omega
  set P := ENNReal.ofReal p
  have hP1 : 1 ≤ P := ENNReal.one_le_ofReal.2 hp
  have hPtop : P ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := tubeVol hn1 δ
  set σ := sphereMeasure n
  have : IsFiniteMeasure σ := by simp only [σ, sphereMeasure]; infer_instance
  have hσ : σ Set.univ ≠ ⊤ := measure_ne_top _ _
  set K : ℝ≥0∞ := ENNReal.ofReal A + σ Set.univ ^ P.toReal⁻¹ * ENNReal.ofReal (V ^ (-(1 / p)))
  have hK : K ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top⟩
    exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hσ
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set η : ℝ := ε / (K.toReal + 1)
  have hK0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hη : 0 < η := div_pos (by exact_mod_cast hε) (by linarith)
  have hKη : K * ENNReal.ofReal η ≤ ε := by
    rw [← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    calc K.toReal * η = (K.toReal / (K.toReal + 1)) * ε := by simp only [η]; ring
      _ ≤ 1 * ε := by
          gcongr; rw [div_le_one (by linarith)]; linarith
      _ = ε := one_mul _
  obtain ⟨g, hg1, hg2, hg3⟩ := hf.1.exist_eLpNorm_sub_le hPtop hP1 hη
  have hgt : IsTest p g := isTest_of_contDiff p hg1 hg2.continuous
  have hA' : eLpNorm (kakeyaMaximal δ g) P σ ≤ ENNReal.ofReal A * eLpNorm g P volume :=
    hA (hg1.toSchwartzMap hg2) hg1
  have hmf := kakeyaMaximal_aestronglyMeasurable hn hp hδ hf
  have hmg := kakeyaMaximal_aestronglyMeasurable hn hp hδ hgt
  have hdiff : eLpNorm (kakeyaMaximal δ f - kakeyaMaximal δ g) P σ ≤
      σ Set.univ ^ P.toReal⁻¹ * ENNReal.ofReal (V ^ (-(1 / p))) * eLpNorm (f - g) P volume := by
    refine (eLpNorm_le_of_ae_bound (C := V ^ (-(1 / p)) * (eLpNorm (f - g) P volume).toReal)
      (Eventually.of_forall fun ω => ?_)).trans (le_of_eq ?_)
    · exact abs_kakeyaMaximal_sub_le hn1 hp hδ hf hgt ω
    · rw [ENNReal.ofReal_mul (Real.rpow_nonneg (tubeVol_pos hn1 hδ).le _),
        ENNReal.ofReal_toReal ((hf.1.sub hgt.1).eLpNorm_lt_top.ne), mul_assoc]
  have hsplit : kakeyaMaximal δ f = kakeyaMaximal δ g + (kakeyaMaximal δ f - kakeyaMaximal δ g) := by
    abel
  calc eLpNorm (kakeyaMaximal δ f) P σ
      = eLpNorm (kakeyaMaximal δ g + (kakeyaMaximal δ f - kakeyaMaximal δ g)) P σ := by
        rw [← hsplit]
    _ ≤ eLpNorm (kakeyaMaximal δ g) P σ + eLpNorm (kakeyaMaximal δ f - kakeyaMaximal δ g) P σ :=
        eLpNorm_add_le hmg (hmf.sub hmg) hP1
    _ ≤ ENNReal.ofReal A * (eLpNorm f P volume + eLpNorm (f - g) P volume) +
        σ Set.univ ^ P.toReal⁻¹ * ENNReal.ofReal (V ^ (-(1 / p))) * eLpNorm (f - g) P volume :=
        add_le_add (hA'.trans (by gcongr; exact eLpNorm_le_add_sub hp hf hgt)) hdiff
    _ = ENNReal.ofReal A * eLpNorm f P volume + K * eLpNorm (f - g) P volume := by
        simp only [K]; ring
    _ ≤ ENNReal.ofReal A * eLpNorm f P volume + K * ENNReal.ofReal η := by gcongr
    _ ≤ ENNReal.ofReal A * eLpNorm f P volume + ε := by gcongr

/-! ## The Nikodym density step -/

theorem tube_subset_closedBall_of_mem {n : ℕ} {δ : ℝ} {ω c x : E n} (hω : ‖ω‖ = 1) (hδ1 : δ ≤ 1)
    (hx : x ∈ tube δ ω c) : tube δ ω c ⊆ closedBall x 3 := by
  intro y hy
  have h1 := tube_subset_closedBall hω hy
  have h2 := tube_subset_closedBall hω hx
  rw [mem_closedBall] at h1 h2 ⊢
  linarith [dist_triangle_right y x c]

theorem nikIdx_nonempty {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) : Nonempty (nikIdx (n := n) δ) :=
  ⟨⟨(unitE hn, 0), norm_unitE hn, by simp [tube, hδ]⟩⟩

theorem abs_nikodymMaximal_sub_le {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {f g : E n → ℝ} (hf : IsTest p f) (hg : IsTest p g) (x : E n) :
    |nikodymMaximal δ f x - nikodymMaximal δ g x| ≤ tubeVol hn δ ^ (-(1 / p)) *
      (eLpNorm (f - g) (ENNReal.ofReal p) (volume.restrict (closedBall x 3))).toReal := by
  have hfi := integrable_of_isTest hp hf
  have hgi := integrable_of_isTest hp hg
  have : Nonempty (nikIdx (n := n) δ) := nikIdx_nonempty hn hδ.le
  simp only [nikodymMaximal_eq hn]
  refine abs_ciSup_sub_le (bddAbove_avg hn hfi δ _) (bddAbove_avg hn hgi δ _) fun P => ?_
  rw [← mul_sub, ← integral_sub hfi.integrableOn hgi.integrableOn]
  have hsub : tube δ P.1.1 (x - P.1.2) ⊆ closedBall x 3 :=
    tube_subset_closedBall_of_mem P.2.1 hδ1 (by rw [mem_tube_iff_sub, sub_sub_cancel]; exact P.2.2)
  have := abs_avg_le_Lp hn hp hδ (hf.1.sub hg.1) (c := x - P.1.2) P.2.1 _ hsub
  simpa only [Pi.sub_apply] using this

theorem lintegral_ball_swap {n : ℕ} {φ : E n → ℝ≥0∞} (hφ : AEMeasurable φ volume) (r : ℝ) :
    ∫⁻ x, ∫⁻ y in closedBall x r, φ y = volume (closedBall (0 : E n) r) * ∫⁻ y, φ y := by
  have h1 : ∀ x, ∫⁻ y in closedBall x r, φ y = ∫⁻ y, (closedBall x r).indicator φ y :=
    fun x => (lintegral_indicator measurableSet_closedBall _).symm
  simp_rw [h1]
  have hm : AEMeasurable (Function.uncurry fun x y => (closedBall x r).indicator φ y)
      ((volume : Measure (E n)).prod volume) := by
    have : (Function.uncurry fun x y => (closedBall x r).indicator φ y) =
        {q : E n × E n | dist q.2 q.1 ≤ r}.indicator (fun q => φ q.2) := by
      funext q; simp [Set.indicator, Function.uncurry, mem_closedBall]
    rw [this]
    exact (hφ.comp_snd).indicator
      (measurableSet_le (measurable_snd.dist measurable_fst) measurable_const)
  rw [lintegral_lintegral_swap hm]
  have h2 : ∀ y, ∫⁻ x, (closedBall x r).indicator φ y = φ y * volume (closedBall (0 : E n) r) := by
    intro y
    have : (fun x => (closedBall x r).indicator φ y) = (closedBall y r).indicator (fun _ => φ y) := by
      funext x; simp [Set.indicator, mem_closedBall, dist_comm]
    rw [this, lintegral_indicator_const measurableSet_closedBall, Measure.addHaar_closedBall_center]
  simp_rw [h2]
  rw [lintegral_mul_const' _ _ measure_closedBall_lt_top.ne, mul_comm]

theorem eLpNorm_le_of_ball_bound {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {F h : E n → ℝ}
    (hh : AEStronglyMeasurable h volume) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hF : ∀ x, ‖F x‖ₑ ≤ B * eLpNorm h (ENNReal.ofReal p) (volume.restrict (closedBall x 3))) :
    eLpNorm F (ENNReal.ofReal p) volume ≤
      B * volume (closedBall (0 : E n) 3) ^ (1 / p) * eLpNorm h (ENNReal.ofReal p) volume := by
  have hpos : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hpos
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hpos.le
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 ENNReal.ofReal_ne_top, hpr] at hF ⊢
  have hφm : AEMeasurable (fun y => ‖h y‖ₑ ^ p) volume := hh.enorm.pow_const p
  have key : ∀ x, ‖F x‖ₑ ^ p ≤ B ^ p * ∫⁻ y in closedBall x 3, ‖h y‖ₑ ^ p := by
    intro x
    calc ‖F x‖ₑ ^ p ≤ (B * (∫⁻ y in closedBall x 3, ‖h y‖ₑ ^ p) ^ (1 / p)) ^ p :=
          ENNReal.rpow_le_rpow (hF x) hpos.le
      _ = B ^ p * ∫⁻ y in closedBall x 3, ‖h y‖ₑ ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hpos.le, ← ENNReal.rpow_mul,
            one_div_mul_cancel hpos.ne', ENNReal.rpow_one]
  have h1p : (0 : ℝ) ≤ 1 / p := by positivity
  calc (∫⁻ x, ‖F x‖ₑ ^ p) ^ (1 / p)
      ≤ (∫⁻ x, B ^ p * ∫⁻ y in closedBall x 3, ‖h y‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono key) h1p
    _ = (B ^ p * (volume (closedBall (0 : E n) 3) * ∫⁻ y, ‖h y‖ₑ ^ p)) ^ (1 / p) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpos.le hB),
          lintegral_ball_swap hφm 3]
    _ = B * volume (closedBall (0 : E n) 3) ^ (1 / p) * (∫⁻ y, ‖h y‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1p, ENNReal.mul_rpow_of_nonneg _ _ h1p,
          ← ENNReal.rpow_mul, mul_one_div_cancel hpos.ne', ENNReal.rpow_one, mul_assoc]

/-- Density step for the Nikodym maximal function at a fixed `δ ≤ 1`. -/
theorem nikodym_bound_of_schwartz {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (A : ℝ) (hA : ∀ g : 𝓢(E n, ℝ), HasCompactSupport g →
      eLpNorm (nikodymMaximal δ g) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal p) volume)
    {f : E n → ℝ} (hf : IsTest p f) :
    eLpNorm (nikodymMaximal δ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  have hn1 : 1 ≤ n := by omega
  set P := ENNReal.ofReal p
  have hP1 : 1 ≤ P := ENNReal.one_le_ofReal.2 hp
  have hPtop : P ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := tubeVol hn1 δ
  set β := volume (closedBall (0 : E n) 3) ^ (1 / p)
  have hβ : β ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne
  set K : ℝ≥0∞ := ENNReal.ofReal A + ENNReal.ofReal (V ^ (-(1 / p))) * β
  have hK : K ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hβ⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set η : ℝ := ε / (K.toReal + 1)
  have hK0 : 0 ≤ K.toReal := ENNReal.toReal_nonneg
  have hη : 0 < η := div_pos (by exact_mod_cast hε) (by linarith)
  have hKη : K * ENNReal.ofReal η ≤ ε := by
    rw [← ENNReal.ofReal_toReal hK, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    calc K.toReal * η = (K.toReal / (K.toReal + 1)) * ε := by simp only [η]; ring
      _ ≤ 1 * ε := by
          gcongr; rw [div_le_one (by linarith)]; linarith
      _ = ε := one_mul _
  obtain ⟨g, hg1, hg2, hg3⟩ := hf.1.exist_eLpNorm_sub_le hPtop hP1 hη
  have hgt : IsTest p g := isTest_of_contDiff p hg1 hg2.continuous
  have hA' : eLpNorm (nikodymMaximal δ g) P volume ≤ ENNReal.ofReal A * eLpNorm g P volume :=
    hA (hg1.toSchwartzMap hg2) hg1
  have hmf := nikodymMaximal_aestronglyMeasurable hn hp hδ hf
  have hmg := nikodymMaximal_aestronglyMeasurable hn hp hδ hgt
  have hdiff : eLpNorm (nikodymMaximal δ f - nikodymMaximal δ g) P volume ≤
      ENNReal.ofReal (V ^ (-(1 / p))) * β * eLpNorm (f - g) P volume := by
    refine eLpNorm_le_of_ball_bound hp (hf.1.sub hgt.1).aestronglyMeasurable _
      ENNReal.ofReal_ne_top fun x => ?_
    have hb := abs_nikodymMaximal_sub_le hn1 hp hδ hδ1 hf hgt x
    have hfin : eLpNorm (f - g) P (volume.restrict (closedBall x 3)) ≠ ⊤ :=
      ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt
        (hf.1.sub hgt.1).eLpNorm_lt_top).ne
    rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs]
    refine (ENNReal.ofReal_le_ofReal hb).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (tubeVol_pos hn1 hδ).le _), ENNReal.ofReal_toReal hfin]
  have hsplit : nikodymMaximal δ f =
      nikodymMaximal δ g + (nikodymMaximal δ f - nikodymMaximal δ g) := by
    abel
  calc eLpNorm (nikodymMaximal δ f) P volume
      = eLpNorm (nikodymMaximal δ g + (nikodymMaximal δ f - nikodymMaximal δ g)) P volume := by
        rw [← hsplit]
    _ ≤ eLpNorm (nikodymMaximal δ g) P volume +
          eLpNorm (nikodymMaximal δ f - nikodymMaximal δ g) P volume :=
        eLpNorm_add_le hmg (hmf.sub hmg) hP1
    _ ≤ ENNReal.ofReal A * (eLpNorm f P volume + eLpNorm (f - g) P volume) +
        ENNReal.ofReal (V ^ (-(1 / p))) * β * eLpNorm (f - g) P volume :=
        add_le_add (hA'.trans (by gcongr; exact eLpNorm_le_add_sub hp hf hgt)) hdiff
    _ = ENNReal.ofReal A * eLpNorm f P volume + K * eLpNorm (f - g) P volume := by
        simp only [K]; ring
    _ ≤ ENNReal.ofReal A * eLpNorm f P volume + K * ENNReal.ofReal η := by gcongr
    _ ≤ ENNReal.ofReal A * eLpNorm f P volume + ε := by gcongr

/-! ## Reduction to `|f|` for Schwartz functions -/

theorem kakeyaMaximal_nonneg {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ1 : δ ≤ 1) {f : E n → ℝ}
    (hf : Integrable f) (hfb : Bornology.IsBounded (Function.support f))
    (ω : sphere (0 : E n) 1) : 0 ≤ kakeyaMaximal δ f ω := by
  obtain ⟨R, hR⟩ := hfb.subset_closedBall 0
  have hω : ‖(ω : E n)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  set c : E n := (|R| + 2) • (ω : E n)
  have hc : ‖c‖ = |R| + 2 := by
    rw [norm_smul, hω, mul_one, Real.norm_of_nonneg (by positivity)]
  simp only [kakeyaMaximal_eq hn]
  refine le_ciSup_of_le (bddAbove_avg hn hf δ _) c (le_of_eq ?_)
  rw [setIntegral_eq_zero_of_forall_eq_zero (fun y hy => ?_), mul_zero]
  by_contra hne
  have h1 : ‖y‖ ≤ R := mem_closedBall_zero_iff.1 (hR hne)
  have h2 := tube_subset_closedBall hω hy
  rw [mem_closedBall, dist_eq_norm] at h2
  have h3 : ‖c‖ ≤ ‖y‖ + ‖y - c‖ := by
    calc ‖c‖ = ‖y - (y - c)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖y‖ + ‖y - c‖ := norm_sub_le _ _
  rw [hc] at h3
  linarith [le_abs_self R]

theorem kakeyaMaximal_le_abs {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) {f : E n → ℝ}
    (hf : Integrable f) (ω : sphere (0 : E n) 1) :
    kakeyaMaximal δ f ω ≤ kakeyaMaximal δ (fun x => |f x|) ω := by
  simp only [kakeyaMaximal_eq hn]
  exact ciSup_mono (bddAbove_avg hn hf.abs δ _) fun c => mul_le_mul_of_nonneg_left
    (setIntegral_mono hf.integrableOn hf.abs.integrableOn fun y => le_abs_self _)
    (inv_nonneg.2 (tubeVol_pos hn hδ).le)

theorem abs_nikodymMaximal_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) {f : E n → ℝ}
    (hf : Integrable f) (x : E n) :
    |nikodymMaximal δ f x| ≤ nikodymMaximal δ (fun x => |f x|) x := by
  have : Nonempty (nikIdx (n := n) δ) := nikIdx_nonempty hn hδ.le
  have hV := inv_nonneg.2 (tubeVol_pos hn hδ).le
  simp only [nikodymMaximal_eq hn]
  rw [abs_le]
  constructor
  · obtain P₀ := Classical.arbitrary (nikIdx (n := n) δ)
    have h1 := le_ciSup (bddAbove_avg hn hf.abs δ
      (fun P : nikIdx (n := n) δ => tube δ P.1.1 (x - P.1.2))) P₀
    have h2 := le_ciSup (bddAbove_avg hn hf δ
      (fun P : nikIdx (n := n) δ => tube δ P.1.1 (x - P.1.2))) P₀
    have h3 : -∫ y in tube δ P₀.1.1 (x - P₀.1.2), |f y| ≤ ∫ y in tube δ P₀.1.1 (x - P₀.1.2), f y :=
      neg_le_of_abs_le abs_integral_le_integral_abs
    have h4 := mul_le_mul_of_nonneg_left h3 hV
    beta_reduce at h1 h2
    linarith
  · exact ciSup_mono (bddAbove_avg hn hf.abs δ _) fun P => mul_le_mul_of_nonneg_left
      (setIntegral_mono hf.integrableOn hf.abs.integrableOn fun y => le_abs_self _) hV

theorem isTest_abs_schwartz {n : ℕ} (p : ℝ) (f : 𝓢(E n, ℝ)) (hfc : HasCompactSupport f) :
    IsTest p (fun x => |f x|) :=
  isTest_of_contDiff p hfc.abs (continuous_abs.comp f.continuous)

theorem eLpNorm_abs_eq {n : ℕ} (P : ℝ≥0∞) (f : E n → ℝ) :
    eLpNorm (fun x => |f x|) P volume = eLpNorm f P volume := by
  simp only [← Real.norm_eq_abs]; exact eLpNorm_norm _

/-! ## I5, I6 -/

/-- I5. `K(p, α)` is equivalent to the class form of the bound (nonnegative test functions). -/
theorem kakeyaMaximalEstimate_iff {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) (α : ℝ) :
    KakeyaMaximalEstimate n p α ↔ ∃ C δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ, 0 < δ → δ < δ₀ → KBound n p δ (C * δ ^ (1 - (n : ℝ) / p - α)) := by
  have hn1 : 1 ≤ n := by omega
  constructor
  · rintro ⟨C, δ₀, hδ₀, H⟩
    refine ⟨C, min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _, fun δ hδ hδlt f hf _ => ?_⟩
    exact kakeya_bound_of_schwartz hn hp hδ _
      (fun g hg => H δ hδ (hδlt.trans_le (min_le_left _ _)) g hg) hf
  · rintro ⟨C, δ₀, hδ₀, hδ₀1, H⟩
    refine ⟨C, δ₀, hδ₀, fun δ hδ hδlt f hfc => ?_⟩
    have hft : IsTest p f := isTest_of_contDiff p hfc f.continuous
    have hfi := integrable_of_isTest hp hft
    have hb := H δ hδ hδlt (fun x => |f x|) (isTest_abs_schwartz p f hfc) (fun x => abs_nonneg _)
    rw [eLpNorm_abs_eq] at hb
    refine le_trans (eLpNorm_mono_real fun ω => ?_) hb
    rw [Real.norm_eq_abs, abs_le]
    have h0 := kakeyaMaximal_nonneg hn1 (hδlt.le.trans hδ₀1) hfi hft.2 ω
    have h1 := kakeyaMaximal_le_abs hn1 hδ hfi ω
    constructor <;> linarith

/-- I6. `N(p, α)` is equivalent to the class form of the bound (nonnegative test functions). -/
theorem nikodymMaximalEstimate_iff {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) (α : ℝ) :
    NikodymMaximalEstimate n p α ↔ ∃ C δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ, 0 < δ → δ < δ₀ → NBound n p δ (C * δ ^ (1 - (n : ℝ) / p - α)) := by
  have hn1 : 1 ≤ n := by omega
  constructor
  · rintro ⟨C, δ₀, hδ₀, H⟩
    refine ⟨C, min δ₀ 1, lt_min hδ₀ one_pos, min_le_right _ _, fun δ hδ hδlt f hf _ => ?_⟩
    exact nikodym_bound_of_schwartz hn hp hδ (hδlt.le.trans (min_le_right _ _)) _
      (fun g hg => H δ hδ (hδlt.trans_le (min_le_left _ _)) g hg) hf
  · rintro ⟨C, δ₀, hδ₀, hδ₀1, H⟩
    refine ⟨C, δ₀, hδ₀, fun δ hδ hδlt f hfc => ?_⟩
    have hft : IsTest p f := isTest_of_contDiff p hfc f.continuous
    have hfi := integrable_of_isTest hp hft
    have hb := H δ hδ hδlt (fun x => |f x|) (isTest_abs_schwartz p f hfc) (fun x => abs_nonneg _)
    rw [eLpNorm_abs_eq] at hb
    refine le_trans (eLpNorm_mono_real fun x => ?_) hb
    rw [Real.norm_eq_abs]
    exact abs_nikodymMaximal_le hn1 hδ hfi x

end TaoBR.T410.PartI

end S_PartI

namespace TaoBR.T410
alias tube_volume_bounds := TaoBR.T410.PartI.tube_volume_bounds
alias volume_tube_eq := TaoBR.T410.PartI.volume_tube_eq
alias kakeyaMaximal_aestronglyMeasurable := TaoBR.T410.PartI.kakeyaMaximal_aestronglyMeasurable
alias kakeyaMaximalEstimate_iff := TaoBR.T410.PartI.kakeyaMaximalEstimate_iff
alias nikodymMaximalEstimate_iff := TaoBR.T410.PartI.nikodymMaximalEstimate_iff
alias lintegral_annulus := TaoBR.T410.PartI.lintegral_annulus
end TaoBR.T410

section S_PartN2K

/-! # Theorem 4.10, Part N2K: `N(p, α) ⟹ K(p, 2α)` -/

open MeasureTheory Metric
open scoped ENNReal NNReal SchwartzMap RealInnerProductSpace Pointwise


namespace TaoBR.T410.PartN2K

theorem norm_normalize_sub_le {n : ℕ} (u v : E n) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ / ‖u‖ := by
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h1 : ‖u‖⁻¹ • u - ‖v‖⁻¹ • v = ‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v := by
    rw [smul_sub, sub_smul]; abel
  rw [h1]
  calc ‖‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v‖
      ≤ ‖‖u‖⁻¹ • (u - v)‖ + ‖(‖u‖⁻¹ - ‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖u - v‖ / ‖u‖ + |‖u‖⁻¹ - ‖v‖⁻¹| * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hu')]; ring
    _ ≤ ‖u - v‖ / ‖u‖ + ‖u - v‖ / ‖u‖ := by
        gcongr
        have : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖v‖ = |‖v‖ - ‖u‖| / ‖u‖ := by
          rw [inv_sub_inv hu'.ne' hv'.ne', abs_div, abs_of_pos (mul_pos hu' hv')]
          field_simp
        rw [this]
        gcongr
        rw [abs_sub_comm]; exact abs_norm_sub_norm_le u v
    _ = 2 * ‖u - v‖ / ‖u‖ := by ring

/-- `‖w - ⟪w, e⟫ e‖ ≤ ‖w‖` for a unit vector `e`. -/
theorem norm_perp_le {n : ℕ} (w e : E n) (he : ‖e‖ = 1) : ‖w - ⟪w, e⟫ • e‖ ≤ ‖w‖ := by
  have h : ‖w - ⟪w, e⟫ • e‖ ^ 2 = ‖w‖ ^ 2 - ⟪w, e⟫ ^ 2 := by
    rw [@norm_sub_sq_real, inner_smul_right, norm_smul, he, Real.norm_eq_abs, mul_one, sq_abs]; ring
  have : ‖w - ⟪w, e⟫ • e‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ⟪w, e⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- `‖w - ⟪w, e⟫ e‖ ≤ ‖w - e‖` for unit vectors `w`, `e`. -/
theorem norm_perp_le_sub {n : ℕ} (w e : E n) (hw : ‖w‖ = 1) (he : ‖e‖ = 1) :
    ‖w - ⟪w, e⟫ • e‖ ≤ ‖w - e‖ := by
  have h : ‖w - ⟪w, e⟫ • e‖ ^ 2 = 1 - ⟪w, e⟫ ^ 2 := by
    rw [@norm_sub_sq_real, inner_smul_right, norm_smul, he, Real.norm_eq_abs, hw, mul_one, sq_abs]; ring
  have h2 : ‖w - e‖ ^ 2 = 2 - 2 * ⟪w, e⟫ := by rw [@norm_sub_sq_real, hw, he]; ring
  have : ‖w - ⟪w, e⟫ • e‖ ^ 2 ≤ ‖w - e‖ ^ 2 := by
    rw [h, h2]; nlinarith [sq_nonneg (1 - ⟪w, e⟫)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- The geometric heart of Part N2K: the `δ`-dilate of a `1 × δ` tube `T` in direction `x/|x|`
centred within `1` of the origin lies in a `1 × 9δ²` tube through `x`. -/
theorem smul_mem_tube {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64) {x c z : E n}
    (hx1 : 1 / 8 < ‖x‖) (hx2 : ‖x‖ < 1 / 4) (hc : ‖c‖ ≤ 2)
    (hz : z ∈ tube δ (‖x‖⁻¹ • x) c) :
    δ • z ∈ tube (17 * δ ^ 2) (‖x - δ • c‖⁻¹ • (x - δ • c)) ((1 / 2 : ℝ) • (x + δ • c)) := by
  set d := x - δ • c with hd
  set ω := ‖x‖⁻¹ • x with hω
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx1; linarith
  have hδc : ‖δ • c‖ ≤ 2 * δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]; nlinarith [norm_nonneg c]
  have hdn : ‖x‖ - 2 * δ ≤ ‖d‖ := by
    have := norm_sub_norm_le x (δ • c); rw [← hd] at this; linarith [norm_sub_le x (δ • c)]
  have hdn' : ‖d‖ ≤ ‖x‖ + 2 * δ := by
    have := norm_sub_le x (δ • c); rw [← hd] at this; linarith
  have hd0 : d ≠ 0 := by intro h; rw [h, norm_zero] at hdn; linarith
  set ω' := ‖d‖⁻¹ • d with hω'
  have hωn : ‖ω‖ = 1 := by rw [hω, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  have hω'n : ‖ω'‖ = 1 := by rw [hω', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hd0)]
  obtain ⟨hs, hw⟩ := hz
  set s := ⟪z - c, ω⟫ with hs_def
  set w := z - c - s • ω with hw_def
  have hzdec : δ • z - (1 / 2 : ℝ) • (x + δ • c) = -((1 / 2 : ℝ) • d) + (δ * s) • ω + δ • w := by
    rw [hw_def, hd]; module
  have hdω' : ⟪d, ω'⟫ = ‖d‖ := by
    rw [hω', inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
    try ring
  have hωω' : ‖ω - ω'‖ ≤ 32 * δ := by
    have := norm_normalize_sub_le x d hx0 hd0
    have hxd : x - d = δ • c := by rw [hd]; abel
    rw [hxd] at this
    calc ‖ω - ω'‖ ≤ 2 * ‖δ • c‖ / ‖x‖ := this
      _ ≤ 2 * (2 * δ) / (1 / 8) := by gcongr
      _ = 32 * δ := by ring
  clear_value ω ω' s w d
  have hax : ⟪δ • z - (1 / 2 : ℝ) • (x + δ • c), ω'⟫ =
      -(1 / 2 * ‖d‖) + δ * s * ⟪ω, ω'⟫ + δ * ⟪w, ω'⟫ := by
    rw [hzdec, inner_add_left, inner_add_left, inner_neg_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, hdω']
  have h1 : |⟪ω, ω'⟫| ≤ 1 := by
    have := abs_real_inner_le_norm ω ω'; rw [hωn, hω'n] at this; linarith
  have h2 : |⟪w, ω'⟫| ≤ δ := by
    have := abs_real_inner_le_norm w ω'; rw [hω'n] at this; nlinarith [norm_nonneg w]
  have h3 : |s| ≤ 1 / 2 := hs
  have hhd : (1 / 2 : ℝ) • d = (1 / 2 * ‖d‖) • ω' := by
    rw [hω', smul_smul]; congr 1; field_simp
  refine ⟨?_, ?_⟩
  · rw [hax]
    have hA : |-(1 / 2 * ‖d‖)| ≤ 1 / 2 * (1 / 4 + 2 * δ) := by
      rw [abs_neg, abs_of_nonneg (by positivity)]; linarith
    have hB : |δ * s * ⟪ω, ω'⟫| ≤ δ * (1 / 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hδ]
      calc δ * |s| * |⟪ω, ω'⟫| ≤ δ * (1 / 2) * 1 := by gcongr
        _ = δ * (1 / 2) := by ring
    have hC : |δ * ⟪w, ω'⟫| ≤ δ * δ := by
      rw [abs_mul, abs_of_pos hδ]; gcongr
    calc _ ≤ |-(1 / 2 * ‖d‖)| + |δ * s * ⟪ω, ω'⟫| + |δ * ⟪w, ω'⟫| := abs_add_three _ _ _
      _ ≤ 1 / 2 * (1 / 4 + 2 * δ) + δ * (1 / 2) + δ * δ := by linarith
      _ ≤ 1 / 2 := by nlinarith
  · -- perpendicular part
    have key : δ • z - (1 / 2 : ℝ) • (x + δ • c) -
        ⟪δ • z - (1 / 2 : ℝ) • (x + δ • c), ω'⟫ • ω' =
        (δ * s) • (ω - ⟪ω, ω'⟫ • ω') + δ • (w - ⟪w, ω'⟫ • ω') := by
      rw [hax, hzdec, hhd]; module
    rw [key]
    have hwn : ‖w‖ ≤ δ := hw
    clear hax hzdec
    calc ‖(δ * s) • (ω - ⟪ω, ω'⟫ • ω') + δ • (w - ⟪w, ω'⟫ • ω')‖
        ≤ ‖(δ * s) • (ω - ⟪ω, ω'⟫ • ω')‖ + ‖δ • (w - ⟪w, ω'⟫ • ω')‖ := norm_add_le _ _
      _ = δ * |s| * ‖ω - ⟪ω, ω'⟫ • ω'‖ + δ * ‖w - ⟪w, ω'⟫ • ω'‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
      _ ≤ δ * (1 / 2) * (32 * δ) + δ * δ := by
          have p1 := (norm_perp_le_sub ω ω' hωn hω'n).trans hωω'
          have p2 := (norm_perp_le w ω' hω'n).trans hwn
          exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hs hδ.le) p1 (norm_nonneg _)
            (by positivity)) (mul_le_mul_of_nonneg_left p2 hδ.le)
      _ = 17 * δ ^ 2 := by ring

theorem mem_tube_self {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {x a : E n} (hxa : x ≠ a) (hd : ‖x - a‖ ≤ 1) :
    x ∈ tube δ (‖x - a‖⁻¹ • (x - a)) ((1 / 2 : ℝ) • (x + a)) := by
  have hd0 : x - a ≠ 0 := sub_ne_zero.2 hxa
  have hn : 0 < ‖x - a‖ := norm_pos_iff.2 hd0
  have e1 : x - (1 / 2 : ℝ) • (x + a) = (1 / 2 : ℝ) • (x - a) := by module
  have e2 : ⟪(1 / 2 : ℝ) • (x - a), ‖x - a‖⁻¹ • (x - a)⟫ = 1 / 2 * ‖x - a‖ := by
    rw [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]; simp only [conj_trivial]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [e1, e2, abs_of_nonneg (by positivity)]; linarith
  · rw [e1, e2, smul_smul]
    have : (1 / 2 : ℝ) • (x - a) - (1 / 2 * ‖x - a‖ * ‖x - a‖⁻¹) • (x - a) = 0 := by
      rw [mul_assoc, mul_inv_cancel₀ hn.ne', mul_one, sub_self]
    rw [this, norm_zero]; exact hδ


theorem isTest_integrable {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {f : E n → ℝ} (hf : IsTest p f) :
    Integrable f := by
  obtain ⟨hm, hb⟩ := hf
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hfin : volume (closedBall (0 : E n) R) < ∞ := measure_closedBall_lt_top
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have : IntegrableOn f (closedBall 0 R) := (hm.restrict (closedBall (0 : E n) R)).integrable hp'
  exact (integrableOn_iff_integrable_of_support_subset hR).1 this

theorem isClosed_tube {n : ℕ} (δ : ℝ) (ω c : E n) : IsClosed (tube δ ω c) := by
  have h1 : Continuous fun x : E n => ⟪x - c, ω⟫ := by fun_prop
  have h2 : Continuous fun x : E n => ‖x - c - ⟪x - c, ω⟫ • ω‖ := by fun_prop
  exact (isClosed_le (continuous_abs.comp h1) continuous_const).inter
    (isClosed_le h2 continuous_const)

theorem measurableSet_tube {n : ℕ} (δ : ℝ) (ω c : E n) : MeasurableSet (tube δ ω c) :=
  (isClosed_tube δ ω c).measurableSet

theorem tube_subset_closedBall {n : ℕ} {δ : ℝ} (hδ : δ ≤ 1) {ω c : E n} (hω : ‖ω‖ = 1) :
    tube δ ω c ⊆ closedBall c (3 / 2) := by
  intro z ⟨hs, hw⟩
  rw [mem_closedBall, dist_eq_norm]
  have : z - c = ⟪z - c, ω⟫ • ω + (z - c - ⟪z - c, ω⟫ • ω) := by abel
  rw [this]
  calc ‖⟪z - c, ω⟫ • ω + (z - c - ⟪z - c, ω⟫ • ω)‖
      ≤ ‖⟪z - c, ω⟫ • ω‖ + ‖z - c - ⟪z - c, ω⟫ • ω‖ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 := by
        rw [norm_smul, hω, mul_one, Real.norm_eq_abs]; exact add_le_add hs (hw.trans hδ)
    _ = 3 / 2 := by norm_num

/-- `f(δ⁻¹ x)`. -/
noncomputable def dil {n : ℕ} (δ : ℝ) (f : E n → ℝ) : E n → ℝ := fun y => f (δ⁻¹ • y)

theorem setIntegral_dil {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (f : E n → ℝ) (s : Set (E n)) :
    ∫ y in δ • s, dil δ f y = δ ^ n * ∫ z in s, f z := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (E n)) (dil δ f) s hδ
  simp only [dil, smul_smul, inv_mul_cancel₀ hδ.ne', one_smul, finrank_euclideanSpace_fin] at h
  rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_pos hδ n).ne', one_mul]
  rfl

theorem dil_integrable {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {f : E n → ℝ} (hf : Integrable f) :
    Integrable (dil δ f) :=
  hf.comp_smul (inv_ne_zero hδ.ne')

theorem unit_exists {n : ℕ} (hn : 1 ≤ n) : ∃ e : E n, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩

/-- Averages of a nonnegative integrable function over tubes of a fixed radius are bounded. -/
theorem nikodym_bddAbove {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) {g : E n → ℝ} (hg : Integrable g) (x : E n) :
    BddAbove (Set.range fun T : {T : E n × E n // ‖T.1‖ = 1 ∧ x ∈ tube δ T.1 T.2} =>
      (volume (tube δ T.1.1 T.1.2)).toReal⁻¹ * ∫ y in tube δ T.1.1 T.1.2, g y) := by
  obtain ⟨e, he⟩ := unit_exists hn
  refine ⟨(volume (tube δ e 0)).toReal⁻¹ * ∫ y, |g y|, ?_⟩
  rintro _ ⟨T, rfl⟩
  dsimp only
  rw [volume_tube_eq δ T.1.1 e T.1.2 0 T.2.1 he]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ENNReal.toReal_nonneg)
  calc ∫ y in tube δ T.1.1 T.1.2, g y ≤ ∫ y in tube δ T.1.1 T.1.2, |g y| :=
        setIntegral_mono hg.integrableOn hg.abs.integrableOn (fun y => le_abs_self _)
    _ ≤ ∫ y, |g y| := setIntegral_le_integral hg.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)

theorem vol_toReal_bounds {n : ℕ} {c₁ c₂ δ : ℝ} {T : Set (E n)} (hc₁ : 0 < c₁) (hδ : 0 < δ)
    (h : ENNReal.ofReal (c₁ * δ ^ (n - 1)) ≤ volume T ∧ volume T ≤ ENNReal.ofReal (c₂ * δ ^ (n - 1))) :
    c₁ * δ ^ (n - 1) ≤ (volume T).toReal ∧ (volume T).toReal ≤ c₂ * δ ^ (n - 1) ∧
      0 < (volume T).toReal := by
  have hne : volume T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h.2
  have h1 : c₁ * δ ^ (n - 1) ≤ (volume T).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hne).1 h.1
  have h2 : (volume T).toReal ≤ c₂ * δ ^ (n - 1) := by
    have hc : 0 ≤ c₂ * δ ^ (n - 1) := by
      by_contra hneg
      push Not at hneg
      have := h.2; rw [ENNReal.ofReal_of_nonpos hneg.le, nonpos_iff_eq_zero] at this
      have h0 := h.1; rw [this, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h0
      have : 0 < c₁ * δ ^ (n - 1) := by positivity
      linarith
    exact ENNReal.toReal_le_of_le_ofReal hc h.2
  exact ⟨h1, h2, lt_of_lt_of_le (by positivity) h1⟩

/-- Step 2 of Part N2K: the pointwise comparison `δ f*_δ(x/|x|) ≤ K₁ (f_δ)**_{17δ²}(x)`. -/
theorem pointwise {n : ℕ} (hn : 2 ≤ n) : ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 64 →
    ∀ f : E n → ℝ, Integrable f → (∀ x, 0 ≤ f x) → Function.support f ⊆ closedBall 0 (1 / 8) →
    ∀ (x : E n) (ω : sphere (0 : E n) 1), (ω : E n) = ‖x‖⁻¹ • x → 1 / 8 < ‖x‖ → ‖x‖ < 1 / 4 →
      δ * kakeyaMaximal δ f ω ≤ K₁ * nikodymMaximal (17 * δ ^ 2) (dil δ f) x := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hvol⟩ := tube_volume_bounds n (by omega)
  refine ⟨c₂ * 17 ^ (n - 1) / c₁, by positivity, ?_⟩
  intro δ hδ hδ1 f hfi hf0 hsupp x ω hωx hx1 hx2
  set δ' := 17 * δ ^ 2 with hδ'
  have hδ'pos : 0 < δ' := by positivity
  have hδ'1 : δ' ≤ 1 := by nlinarith
  have hωn : ‖(ω : E n)‖ = 1 := by simp
  have hgi : Integrable (dil δ f) := dil_integrable hδ hfi
  have hg0 : ∀ y, 0 ≤ dil δ f y := fun y => hf0 _
  have hbdd := nikodym_bddAbove (by omega) δ' hgi x
  have hN0 : 0 ≤ nikodymMaximal δ' (dil δ f) x := by
    have hmem : x ∈ tube δ' (ω : E n) x := by
      refine ⟨by simp, by simp [hδ'pos.le]⟩
    refine le_trans ?_ (le_ciSup hbdd ⟨((ω : E n), x), hωn, hmem⟩)
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (setIntegral_nonneg (measurableSet_tube _ _ _) fun y _ => hg0 y)
  unfold kakeyaMaximal
  rw [Real.mul_iSup_of_nonneg hδ.le]
  apply ciSup_le
  intro c
  by_cases hc : ‖c‖ ≤ 2
  · set a := δ • c with ha
    have han : ‖a‖ ≤ 2 * δ := by
      rw [ha, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]; nlinarith [norm_nonneg c]
    have hxa : x ≠ a := by intro h; rw [h] at hx1; linarith
    have hxa1 : ‖x - a‖ ≤ 1 := by linarith [norm_sub_le x a]
    have hd0 : x - a ≠ 0 := sub_ne_zero.2 hxa
    set ω' := ‖x - a‖⁻¹ • (x - a) with hω'
    have hω'n : ‖ω'‖ = 1 := by
      rw [hω', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hd0)]
    set m := (1 / 2 : ℝ) • (x + a) with hm
    have hxT' : x ∈ tube δ' ω' m := mem_tube_self hδ'pos.le hxa hxa1
    have hle := le_ciSup hbdd ⟨(ω', m), hω'n, hxT'⟩
    simp only at hle
    have hsub : δ • tube δ (ω : E n) c ⊆ tube δ' ω' m := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hωx] at hz
      exact smul_mem_tube hδ hδ1 hx1 hx2 hc hz
    have hI' : δ ^ n * ∫ z in tube δ (ω : E n) c, f z ≤ ∫ y in tube δ' ω' m, dil δ f y := by
      rw [← setIntegral_dil hδ f]
      exact setIntegral_mono_set hgi.integrableOn
        (Filter.Eventually.of_forall fun y => hg0 y) hsub.eventuallyLE
    obtain ⟨hT1, -, hT3⟩ := vol_toReal_bounds hc₁ hδ (hvol δ hδ (by linarith) (ω : E n) c hωn)
    obtain ⟨-, hT'2, hT'3⟩ := vol_toReal_bounds hc₁ hδ'pos (hvol δ' hδ'pos hδ'1 ω' m hω'n)
    set VT := (volume (tube δ (ω : E n) c)).toReal
    set VT' := (volume (tube δ' ω' m)).toReal
    set I := ∫ z in tube δ (ω : E n) c, f z
    set I' := ∫ y in tube δ' ω' m, dil δ f y
    have hI0 : 0 ≤ I := setIntegral_nonneg (measurableSet_tube _ _ _) fun y _ => hf0 y
    have hK0 : 0 ≤ c₂ * 17 ^ (n - 1) / c₁ := by positivity
    calc δ * (VT⁻¹ * I) ≤ δ * ((c₁ * δ ^ (n - 1))⁻¹ * I) := by
          gcongr
      _ = c₂ * 17 ^ (n - 1) / c₁ * ((c₂ * δ' ^ (n - 1))⁻¹ * (δ ^ n * I)) := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          simp only [Nat.add_sub_cancel, hδ']
          field_simp
          ring
      _ ≤ c₂ * 17 ^ (n - 1) / c₁ * (VT'⁻¹ * (δ ^ n * I)) := by
          gcongr
      _ ≤ c₂ * 17 ^ (n - 1) / c₁ * (VT'⁻¹ * I') := by
          gcongr
      _ ≤ c₂ * 17 ^ (n - 1) / c₁ * nikodymMaximal δ' (dil δ f) x := by
          gcongr
          exact hle
  · have hzero : ∫ z in tube δ (ω : E n) c, f z = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      by_contra hne
      have h1 : ‖y‖ ≤ 1 / 8 := by simpa using hsupp hne
      have h2 := tube_subset_closedBall (by linarith : δ ≤ 1) hωn hy
      rw [mem_closedBall, dist_eq_norm] at h2
      have := norm_sub_norm_le c y
      rw [norm_sub_rev] at h2
      linarith
    rw [hzero, mul_zero, mul_zero]
    exact mul_nonneg (by positivity) hN0

theorem map_dil_volume {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Measure.map (fun y : E n => δ⁻¹ • y) volume = ENNReal.ofReal (δ ^ n) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hδ.ne'), finrank_euclideanSpace_fin, inv_pow,
    inv_inv, abs_of_pos (pow_pos hδ n)]

theorem eLpNorm_dil {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {f : E n → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (dil δ f) (ENNReal.ofReal p) volume =
      ENNReal.ofReal (δ ^ ((n : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hm : AEMeasurable (fun y : E n => δ⁻¹ • y) volume := (measurable_const_smul _).aemeasurable
  have hf' : AEStronglyMeasurable f (Measure.map (fun y : E n => δ⁻¹ • y) volume) := by
    rw [map_dil_volume hδ]; exact hf.smul_measure _
  have : dil δ f = f ∘ fun y : E n => δ⁻¹ • y := rfl
  rw [this, ← eLpNorm_map_measure hf' hm, map_dil_volume hδ,
    eLpNorm_smul_measure_of_ne_top ENNReal.ofReal_ne_top, smul_eq_mul]
  congr 1
  have hp0 : 0 < p := by linarith
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le,
    ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hδ.le n) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hδ.le]
  congr 2; ring

theorem isTest_dil {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) {f : E n → ℝ}
    (hf : IsTest p f) : IsTest p (dil δ f) := by
  obtain ⟨hm, hb⟩ := hf
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : dil δ f = f ∘ fun y : E n => δ⁻¹ • y := rfl
    rw [this]
    refine hm.1.comp_quasiMeasurePreserving ?_
    exact ⟨measurable_const_smul _, by rw [map_dil_volume hδ]; exact Measure.smul_absolutelyContinuous⟩
  · rw [eLpNorm_dil hp hδ hm.1]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm.2
  · obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    refine (isBounded_closedBall (x := (0 : E n)) (r := δ * R)).subset ?_
    intro y hy
    have h := hR hy
    simp only [mem_closedBall, dist_zero_right] at h ⊢
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hδ] at h
    have := (inv_mul_le_iff₀ hδ).1 h
    linarith

theorem kakeyaMaximal_nonneg {n : ℕ} {δ : ℝ} {f : E n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (ω : sphere (0 : E n) 1) : 0 ≤ kakeyaMaximal δ f ω :=
  Real.iSup_nonneg fun c => mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (setIntegral_nonneg (measurableSet_tube _ _ _) fun y _ => hf y)

theorem measurableSet_annulus {n : ℕ} (a b : ℝ) :
    MeasurableSet {x : E n | a < ‖x‖ ∧ ‖x‖ < b} :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- Polar transfer: an `Lᵖ` bound on the annulus `1/8 < |x| < 1/4` for a function dominating
`F(x/|x|)` bounds the `Lᵖ(σ)` norm of `F`. -/
theorem sphere_le_annulus {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 < p) (F : sphere (0 : E n) 1 → ℝ)
    (hF : AEStronglyMeasurable F (sphereMeasure n)) (N : E n → ℝ)
    (hFN : ∀ (x : E n) (ω : sphere (0 : E n) 1), (ω : E n) = ‖x‖⁻¹ • x → 1 / 8 < ‖x‖ →
      ‖x‖ < 1 / 4 → ‖F ω‖ ≤ ‖N x‖) :
    ENNReal.ofReal (((1 / 4 : ℝ) ^ n - (1 / 8) ^ n) / n) *
        ∫⁻ ω, ‖F ω‖ₑ ^ p ∂(sphereMeasure n) ≤ ∫⁻ x, ‖N x‖ₑ ^ p := by
  set A := {x : E n | 1 / 8 < ‖x‖ ∧ ‖x‖ < 1 / 4} with hA
  have hAm : MeasurableSet A := measurableSet_annulus _ _
  set F₀ := hF.mk F
  have hF₀ : StronglyMeasurable F₀ := hF.stronglyMeasurable_mk
  have hae : F =ᵐ[sphereMeasure n] F₀ := hF.ae_eq_mk
  have emb : MeasurableEmbedding (Subtype.val : sphere (0 : E n) 1 → E n) :=
    MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet
  set Fh : E n → ℝ := Function.extend Subtype.val F₀ (fun _ => 0)
  have hFh : Measurable Fh := emb.measurable_extend hF₀.measurable measurable_const
  have hFh_apply : ∀ ω : sphere (0 : E n) 1, Fh ω = F₀ ω := fun ω =>
    Subtype.val_injective.extend_apply _ _ ω
  set G : E n → ℝ≥0∞ := fun y => ‖Fh y‖ₑ ^ p
  have hG : Measurable G := hFh.enorm.pow_const p
  -- the bad set
  set S := {ω : sphere (0 : E n) 1 | F ω ≠ F₀ ω}
  have hS : sphereMeasure n S = 0 := by
    have := hae; rw [Filter.EventuallyEq, ae_iff] at this; exact this
  set B := toMeasurable (sphereMeasure n) S
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : sphereMeasure n B = 0 := by rw [measure_toMeasurable]; exact hS
  have hSB : S ⊆ B := subset_toMeasurable _ _
  set Bh := Subtype.val '' B
  have hBhm : MeasurableSet Bh := emb.measurableSet_image' hBm
  have hbad := lintegral_annulus hn (Bh.indicator 1) (measurable_one.indicator hBhm)
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  have hind : ∀ ω : sphere (0 : E n) 1, Bh.indicator (1 : E n → ℝ≥0∞) ω = B.indicator 1 ω := by
    intro ω
    by_cases h : ω ∈ B
    · rw [Set.indicator_of_mem (Set.mem_image_of_mem _ h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
      rintro ⟨ω', hω', he⟩; exact h (Subtype.val_injective he ▸ hω')
  simp_rw [hind] at hbad
  rw [lintegral_indicator_one hBm, hB0, mul_zero, ← hA] at hbad
  have hgood : ∀ᵐ x ∂(volume.restrict A), ‖x‖⁻¹ • x ∉ Bh := by
    have := (lintegral_eq_zero_iff ((measurable_one.indicator hBhm).comp
      ((measurable_norm.inv).smul measurable_id))).1 hbad
    filter_upwards [this] with x hx
    intro hmem
    simp [Function.comp, Set.indicator_of_mem hmem] at hx
  have hmain := lintegral_annulus hn G hG (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  rw [← hA] at hmain
  have hsph : ∫⁻ ω, G (ω : E n) ∂(sphereMeasure n) = ∫⁻ ω, ‖F ω‖ₑ ^ p ∂(sphereMeasure n) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with ω hω
    simp only [G, hFh_apply, hω]
  rw [← hsph, ← hmain]
  calc ∫⁻ x in A, G (‖x‖⁻¹ • x) ≤ ∫⁻ x in A, ‖N x‖ₑ ^ p := by
        apply lintegral_mono_ae
        filter_upwards [hgood, ae_restrict_mem hAm] with x hx hxA
        have hx0 : x ≠ 0 := by
          intro h; have := hxA.1; rw [h, norm_zero] at this; linarith
        have hun : ‖‖x‖⁻¹ • x‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
        set ω : sphere (0 : E n) 1 := ⟨‖x‖⁻¹ • x, by simpa using hun⟩
        have hωB : ω ∉ B := fun h => hx (Set.mem_image_of_mem _ h)
        have hωS : F ω = F₀ ω := by
          by_contra h; exact hωB (hSB h)
        have : G (‖x‖⁻¹ • x) = ‖F ω‖ₑ ^ p := by
          show ‖Fh (ω : E n)‖ₑ ^ p = _
          rw [hFh_apply, hωS]
        rw [this]
        gcongr
        have h := hFN x ω rfl hxA.1 hxA.2
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal h
    _ ≤ ∫⁻ x, ‖N x‖ₑ ^ p := setLIntegral_le_lintegral _ _

theorem eLpNorm_eq_rpow {α : Type*} [MeasurableSpace α] {p : ℝ} (hp : 1 ≤ p) {μ : Measure α}
    (g : α → ℝ) :
    eLpNorm g (ENNReal.ofReal p) μ = (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]

/-- Step 3 of Part N2K: the Kakeya bound for nonnegative test functions supported in `B(0, 1/8)`. -/
theorem small_support {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) : ∃ K₃ : ℝ, 0 < K₃ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 64 → ∀ A' : ℝ, NBound n p (17 * δ ^ 2) A' →
    ∀ f : E n → ℝ, IsTest p f → (∀ x, 0 ≤ f x) → Function.support f ⊆ closedBall 0 (1 / 8) →
      eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal (K₃ * δ⁻¹ * max A' 0 * δ ^ ((n : ℝ) / p)) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨K₁, hK₁, hpt⟩ := pointwise hn
  have hp0 : 0 < p := by linarith
  set c : ℝ := ((1 / 4 : ℝ) ^ n - (1 / 8) ^ n) / n with hc
  have hcpos : 0 < c := by
    have : (1 / 8 : ℝ) ^ n < (1 / 4) ^ n :=
      pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [hc]; apply div_pos <;> linarith
  refine ⟨(c ^ (1 / p))⁻¹ * K₁, by positivity, ?_⟩
  intro δ hδ hδ1 A' hN f hf hf0 hsupp
  set nik := nikodymMaximal (17 * δ ^ 2) (dil δ f)
  set N : E n → ℝ := fun x => (K₁ / δ) * nik x
  have hfi := isTest_integrable hp hf
  have hFN : ∀ (x : E n) (ω : sphere (0 : E n) 1), (ω : E n) = ‖x‖⁻¹ • x → 1 / 8 < ‖x‖ →
      ‖x‖ < 1 / 4 → ‖kakeyaMaximal δ f ω‖ ≤ ‖N x‖ := by
    intro x ω hωx hx1 hx2
    have h1 := hpt δ hδ hδ1 f hfi hf0 hsupp x ω hωx hx1 hx2
    have hF0 := kakeyaMaximal_nonneg (δ := δ) hf0 ω
    have hle : kakeyaMaximal δ f ω ≤ N x := by
      simp only [N]; rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; linarith
    rw [Real.norm_of_nonneg hF0, Real.norm_of_nonneg (hF0.trans hle)]; exact hle
  have hmeas := kakeyaMaximal_aestronglyMeasurable hn hp hδ hf
  have hann := sphere_le_annulus hn hp0 _ hmeas N hFN
  rw [← hc] at hann
  -- take p-th roots
  have hroot : ENNReal.ofReal (c ^ (1 / p)) *
      eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
      eLpNorm N (ENNReal.ofReal p) volume := by
    rw [eLpNorm_eq_rpow hp (μ := sphereMeasure n), eLpNorm_eq_rpow hp (μ := volume),
      ← ENNReal.ofReal_rpow_of_nonneg hcpos.le (by positivity),
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    exact ENNReal.rpow_le_rpow hann (by positivity)
  have hNn : eLpNorm N (ENNReal.ofReal p) volume =
      ENNReal.ofReal (K₁ / δ) * eLpNorm nik (ENNReal.ofReal p) volume := by
    have : N = (K₁ / δ) • nik := rfl
    rw [this, eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  have hnik : eLpNorm nik (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (max A' 0) * (ENNReal.ofReal (δ ^ ((n : ℝ) / p)) *
        eLpNorm f (ENNReal.ofReal p) volume) := by
    have := hN (dil δ f) (isTest_dil hp hδ hf) (fun x => hf0 _)
    rw [eLpNorm_dil hp hδ hf.1.1] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rcases le_total A' 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have hcp : 0 < c ^ (1 / p) := by positivity
  have key : eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
      ENNReal.ofReal ((c ^ (1 / p))⁻¹) * (ENNReal.ofReal (K₁ / δ) * (ENNReal.ofReal (max A' 0) *
        (ENNReal.ofReal (δ ^ ((n : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) volume))) := by
    have h2 : ENNReal.ofReal (c ^ (1 / p)) *
        eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal (K₁ / δ) * (ENNReal.ofReal (max A' 0) *
          (ENNReal.ofReal (δ ^ ((n : ℝ) / p)) * eLpNorm f (ENNReal.ofReal p) volume)) := by
      calc _ ≤ eLpNorm N (ENNReal.ofReal p) volume := hroot
        _ = _ := hNn
        _ ≤ _ := by gcongr
    rw [ENNReal.ofReal_inv_of_pos hcp]
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hcp).ne')
      (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact h2
  refine key.trans (le_of_eq ?_)
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

/-! ### Step 1: decomposition into small cubes -/

theorem tubeAvg_comp_add {n : ℕ} (δ : ℝ) (f : E n → ℝ) (ω c v : E n) (hω : ‖ω‖ = 1) :
    (volume (tube δ ω c)).toReal⁻¹ * ∫ y in tube δ ω c, f (y + v) =
      (volume (tube δ ω (c + v))).toReal⁻¹ * ∫ y in tube δ ω (c + v), f y := by
  rw [volume_tube_eq δ ω ω c (c + v) hω hω]
  congr 1
  have hmem : ∀ y, y ∈ tube δ ω c ↔ y + v ∈ tube δ ω (c + v) := by
    intro y; simp only [tube, Set.mem_setOf_eq, add_sub_add_right_eq_sub]
  rw [← integral_indicator (measurableSet_tube _ _ _),
    ← integral_indicator (measurableSet_tube _ _ _)]
  conv_rhs => rw [← integral_add_right_eq_self (μ := volume) _ v]
  congr 1; ext y
  by_cases h : y ∈ tube δ ω c
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem y).1 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem y).2 h'))]

theorem kakeyaMaximal_comp_add {n : ℕ} (δ : ℝ) (f : E n → ℝ) (v : E n)
    (ω : sphere (0 : E n) 1) :
    kakeyaMaximal δ (fun y => f (y + v)) ω = kakeyaMaximal δ f ω := by
  have hω : ‖(ω : E n)‖ = 1 := by simp
  unfold kakeyaMaximal
  simp_rw [tubeAvg_comp_add δ f (ω : E n) _ v hω]
  exact (Equiv.addRight v).iSup_comp (g := fun c =>
    (volume (tube δ (ω : E n) c)).toReal⁻¹ * ∫ y in tube δ (ω : E n) c, f y)

theorem kakeya_bddAbove {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) {g : E n → ℝ} (hg : Integrable g)
    (ω : sphere (0 : E n) 1) :
    BddAbove (Set.range fun c : E n =>
      (volume (tube δ (ω : E n) c)).toReal⁻¹ * ∫ y in tube δ (ω : E n) c, g y) := by
  have hω : ‖(ω : E n)‖ = 1 := by simp
  refine ⟨(volume (tube δ (ω : E n) 0)).toReal⁻¹ * ∫ y, |g y|, ?_⟩
  rintro _ ⟨c, rfl⟩
  dsimp only
  rw [volume_tube_eq δ (ω : E n) (ω : E n) c 0 hω hω]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ENNReal.toReal_nonneg)
  calc ∫ y in tube δ (ω : E n) c, g y ≤ ∫ y in tube δ (ω : E n) c, |g y| :=
        setIntegral_mono hg.integrableOn hg.abs.integrableOn (fun y => le_abs_self _)
    _ ≤ ∫ y, |g y| := setIntegral_le_integral hg.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)

/-- The cube side `1/(8n)`. -/
noncomputable def side (n : ℕ) : ℝ := 1 / (8 * n)

/-- The index of the cube containing `y`. -/
noncomputable def idx {n : ℕ} (y : E n) : Fin n → ℤ := fun i => ⌊y i / side n⌋

/-- The part of `f` in the `k`-th cube. -/
noncomputable def piece {n : ℕ} (f : E n → ℝ) (k : Fin n → ℤ) : E n → ℝ :=
  Set.indicator {y | idx y = k} f

/-- The corner `side • k` of the `k`-th cube. -/
noncomputable def corner {n : ℕ} (k : Fin n → ℤ) : E n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => side n * k i)

theorem side_pos {n : ℕ} (hn : 1 ≤ n) : 0 < side n := by
  unfold side; have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem measurable_idx {n : ℕ} : Measurable (idx : E n → Fin n → ℤ) := by
  apply measurable_pi_lambda
  intro i
  exact Int.measurable_floor.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.div_const _)

theorem measurableSet_cube {n : ℕ} (k : Fin n → ℤ) : MeasurableSet {y : E n | idx y = k} :=
  measurable_idx (measurableSet_singleton k)

theorem abs_coord_le {n : ℕ} (y : E n) (i : Fin n) : |y i| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y i
  rwa [Real.norm_eq_abs] at this

theorem norm_le_of_coord {n : ℕ} (hn : 1 ≤ n) (y : E n) (h : ∀ i, 0 ≤ y i ∧ y i < side n) :
    ‖y‖ ≤ 1 / 8 := by
  rw [EuclideanSpace.norm_eq]
  have hs := side_pos hn
  have hsum : ∑ i, ‖y i‖ ^ 2 ≤ n * side n ^ 2 := by
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin n, side n ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have := h i; nlinarith
      _ = n * side n ^ 2 := by simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) * side n ^ 2 ≤ (1 / 8) ^ 2 := by
    unfold side
    rw [div_pow, mul_pow]
    field_simp
    nlinarith
  calc √(∑ i, ‖y i‖ ^ 2) ≤ √((1 / 8) ^ 2) := Real.sqrt_le_sqrt (hsum.trans this)
    _ = 1 / 8 := Real.sqrt_sq (by norm_num)

theorem translated_piece_support {n : ℕ} (hn : 1 ≤ n) (f : E n → ℝ) (k : Fin n → ℤ) :
    Function.support (fun y => piece f k (y + corner k)) ⊆ closedBall 0 (1 / 8) := by
  intro y hy
  simp only [Function.mem_support, piece] at hy
  have hk : idx (y + corner k) = k := by
    by_contra h
    exact hy (Set.indicator_of_notMem (show y + corner k ∉ {y | idx y = k} from h) f)
  rw [mem_closedBall, dist_zero_right]
  apply norm_le_of_coord hn
  intro i
  have hi := congrFun hk i
  simp only [idx, corner] at hi
  have hs := side_pos hn
  have e : (y + (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => side n * k i)) i / side n =
      y i / side n + k i := by
    simp [PiLp.add_apply, EuclideanSpace.equiv]
    field_simp
  rw [e, Int.floor_add_intCast, add_eq_right, Int.floor_eq_zero_iff] at hi
  obtain ⟨h1, h2⟩ := hi
  constructor
  · exact (div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hs))
  · rwa [div_lt_one hs] at h2

theorem rpow_le_of_le_mul_pow {X Y c : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (h : X ≤ c ^ p * Y) :
    X ^ (1 / p) ≤ c * Y ^ (1 / p) := by
  calc X ^ (1 / p) ≤ (c ^ p * Y) ^ (1 / p) := ENNReal.rpow_le_rpow h (by positivity)
    _ = c * Y ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem le_mul_pow_of_rpow_le {X Y c : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (h : X ^ (1 / p) ≤ c * Y ^ (1 / p)) :
    X ≤ c ^ p * Y := by
  have := ENNReal.rpow_le_rpow h hp.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
    ENNReal.rpow_one] at this
  exact this

theorem isTest_piece {n : ℕ} {p : ℝ} {f : E n → ℝ} (hf : IsTest p f) (k : Fin n → ℤ) :
    IsTest p (piece f k) :=
  ⟨hf.1.indicator (measurableSet_cube k), hf.2.subset fun y hy => by
    by_contra h; exact hy (by simp [piece, Set.indicator_apply, show f y = 0 by simpa using h])⟩

theorem isTest_comp_add {n : ℕ} {p : ℝ} {g : E n → ℝ} (hg : IsTest p g) (v : E n) :
    IsTest p (fun y => g (y + v)) := by
  refine ⟨hg.1.comp_measurePreserving (measurePreserving_add_right volume v), ?_⟩
  obtain ⟨R, hR⟩ := hg.2.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : E n)) (r := R + ‖v‖)).subset ?_
  intro y hy
  have h := hR hy
  simp only [mem_closedBall, dist_zero_right] at h ⊢
  have := norm_sub_le (y + v) v
  simp only [add_sub_cancel_right] at this
  linarith

theorem eLpNorm_comp_add {n : ℕ} {p : ℝ} {g : E n → ℝ} (hg : AEStronglyMeasurable g volume)
    (v : E n) : eLpNorm (fun y => g (y + v)) (ENNReal.ofReal p) volume =
      eLpNorm g (ENNReal.ofReal p) volume :=
  eLpNorm_comp_measurePreserving hg (measurePreserving_add_right volume v)

theorem piece_nonneg {n : ℕ} {f : E n → ℝ} (hf : ∀ x, 0 ≤ f x) (k : Fin n → ℤ) (y : E n) :
    0 ≤ piece f k y := Set.indicator_nonneg (fun y _ => hf y) y

theorem sum_piece_eq {n : ℕ} (f : E n → ℝ) (J : Finset (Fin n → ℤ)) (y : E n) (hy : idx y ∈ J) :
    ∑ k ∈ J, piece f k y = f y := by
  rw [Finset.sum_eq_single (idx y)]
  · exact Set.indicator_of_mem (show y ∈ {y | idx y = idx y} from rfl) f
  · intro k _ hk
    exact Set.indicator_of_notMem (show y ∉ {y | idx y = k} from fun h => hk h.symm) f
  · intro h; exact absurd hy h

theorem floor_sub_floor_le (a b : ℝ) : (⌊b⌋ : ℝ) + 1 - ⌊a⌋ ≤ b - a + 2 := by
  have h1 := Int.floor_le b
  have h2 := Int.lt_floor_add_one a
  linarith

/-- The cube indices near a centre `c`. -/
noncomputable def nearIdx {n : ℕ} (c : E n) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc ⌊(c i - 2) / side n⌋ ⌊(c i + 2) / side n⌋

theorem card_nearIdx_le {n : ℕ} (hn : 1 ≤ n) (c : E n) :
    ((nearIdx c).card : ℝ) ≤ ((⌈4 / side n⌉₊ + 2 : ℕ) : ℝ) ^ n := by
  rw [nearIdx, Fintype.card_piFinset]
  push_cast
  rw [← Fin.prod_const]
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i _
  rw [Int.card_Icc]
  have hs := side_pos hn
  have h := floor_sub_floor_le ((c i - 2) / side n) ((c i + 2) / side n)
  have e : (c i + 2) / side n - (c i - 2) / side n = 4 / side n := by field_simp; ring
  rw [e] at h
  have hc := Nat.le_ceil (4 / side n)
  have hlt : ((⌊(c i + 2) / side n⌋ + 1 - ⌊(c i - 2) / side n⌋ : ℤ) : ℝ) ≤
      ((⌈4 / side n⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hz : (⌊(c i + 2) / side n⌋ + 1 - ⌊(c i - 2) / side n⌋ : ℤ) ≤ ((⌈4 / side n⌉₊ + 2 : ℕ) : ℤ) := by
    exact_mod_cast hlt
  have := Int.toNat_le_toNat hz
  simp only [Int.toNat_natCast] at this
  exact_mod_cast this

theorem idx_mem_nearIdx {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : δ ≤ 1) {ω c y : E n} (hω : ‖ω‖ = 1)
    (hy : y ∈ tube δ ω c) : idx y ∈ nearIdx c := by
  have h := tube_subset_closedBall hδ hω hy
  rw [mem_closedBall, dist_eq_norm] at h
  have hs := side_pos hn
  rw [nearIdx, Fintype.mem_piFinset]
  intro i
  have hi : |y i - c i| ≤ 3 / 2 := by
    have := abs_coord_le (y - c) i; simp only [PiLp.sub_apply] at this; linarith
  rw [abs_le] at hi
  rw [Finset.mem_Icc]
  constructor
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le)
  · exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hs.le)

/-- The cube box containing the support of `f`. -/
noncomputable def boxIdx (n : ℕ) (R : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc ⌊-R / side n⌋ ⌊R / side n⌋

theorem idx_mem_boxIdx {n : ℕ} (hn : 1 ≤ n) {R : ℝ} {y : E n} (hy : ‖y‖ ≤ R) :
    idx y ∈ boxIdx n R := by
  have hs := side_pos hn
  rw [boxIdx, Fintype.mem_piFinset]
  intro i
  have hi := (abs_coord_le y i).trans hy
  rw [abs_le] at hi
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right hi.1 hs.le),
    Int.floor_le_floor (div_le_div_of_nonneg_right hi.2 hs.le)⟩

theorem kakeyaMaximal_zero {n : ℕ} (δ : ℝ) (ω : sphere (0 : E n) 1) :
    kakeyaMaximal δ (fun _ => (0 : ℝ)) ω = 0 := by
  simp [kakeyaMaximal]

/-- Step 1 of Part N2K: a bound for test functions supported in `B(0, 1/8)` gives one for all
nonnegative test functions, with a loss depending only on `n`. -/
theorem decomp {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) : ∃ M : ℝ, 0 < M ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ B : ℝ, 0 ≤ B →
    (∀ g : E n → ℝ, IsTest p g → (∀ x, 0 ≤ g x) → Function.support g ⊆ closedBall 0 (1 / 8) →
      eLpNorm (kakeyaMaximal δ g) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal p) volume) →
    ∀ f : E n → ℝ, IsTest p f → (∀ x, 0 ≤ f x) →
      eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal (M * B) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hn1 : 1 ≤ n := by omega
  have hp0 : 0 < p := by linarith
  set M : ℝ := ((⌈4 / side n⌉₊ + 2 : ℕ) : ℝ) ^ n with hM
  refine ⟨M, by positivity, ?_⟩
  intro δ hδ hδ1 B hB hsmall f hf hf0
  obtain ⟨R, hR⟩ := hf.2.subset_closedBall 0
  set S := boxIdx n R
  set a : (Fin n → ℤ) → sphere (0 : E n) 1 → ℝ := fun k ω => kakeyaMaximal δ (piece f k) ω
  have ha0 : ∀ k ω, 0 ≤ a k ω := fun k ω => kakeyaMaximal_nonneg (piece_nonneg hf0 k) ω
  set Λ : sphere (0 : E n) 1 → ℝ := fun ω => (∑ k ∈ S, a k ω ^ p) ^ (1 / p)
  have hpiece0 : ∀ k ∉ S, piece f k = fun _ => 0 := by
    intro k hk; funext y
    by_cases hy : idx y = k
    · have : f y = 0 := by
        by_contra hne
        have : ‖y‖ ≤ R := by simpa using hR hne
        exact hk (hy ▸ idx_mem_boxIdx hn1 this)
      simp [piece, Set.indicator_apply, hy, this]
    · exact Set.indicator_of_notMem (show y ∉ {y | idx y = k} from hy) f
  have hak : ∀ k ω, a k ω ≤ Λ ω := by
    intro k ω
    by_cases hk : k ∈ S
    · have h1 : a k ω ^ p ≤ ∑ k ∈ S, a k ω ^ p :=
        Finset.single_le_sum (f := fun k => a k ω ^ p)
          (fun k _ => Real.rpow_nonneg (ha0 k ω) p) hk
      calc a k ω = (a k ω ^ p) ^ (1 / p) := by
            rw [← Real.rpow_mul (ha0 k ω), mul_one_div_cancel hp0.ne', Real.rpow_one]
        _ ≤ Λ ω := Real.rpow_le_rpow (Real.rpow_nonneg (ha0 k ω) p) h1 (by positivity)
    · simp only [a]; rw [hpiece0 k hk, kakeyaMaximal_zero]
      exact Real.rpow_nonneg (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (ha0 k ω) p) _
  have hΛ0 : ∀ ω, 0 ≤ Λ ω := fun ω =>
    Real.rpow_nonneg (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (ha0 k ω) p) _
  have hpt : ∀ ω, kakeyaMaximal δ f ω ≤ M * Λ ω := by
    intro ω
    have hω : ‖(ω : E n)‖ = 1 := by simp
    apply ciSup_le
    intro c
    set T := tube δ (ω : E n) c
    have hsum : ∫ y in T, f y = ∑ k ∈ nearIdx c, ∫ y in T, piece f k y := by
      rw [← integral_finsetSum _ fun k _ =>
        (isTest_integrable hp (isTest_piece hf k)).integrableOn]
      apply setIntegral_congr_fun (measurableSet_tube _ _ _)
      intro y hy
      exact (sum_piece_eq f _ y (idx_mem_nearIdx hn1 hδ1 hω hy)).symm
    rw [hsum, Finset.mul_sum]
    calc ∑ k ∈ nearIdx c, (volume T).toReal⁻¹ * ∫ y in T, piece f k y
        ≤ ∑ k ∈ nearIdx c, a k ω := by
          apply Finset.sum_le_sum; intro k _
          exact le_ciSup (kakeya_bddAbove hn1 δ (isTest_integrable hp (isTest_piece hf k)) ω) c
      _ ≤ ∑ _k ∈ nearIdx c, Λ ω := Finset.sum_le_sum fun k _ => hak k ω
      _ = (nearIdx c).card * Λ ω := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M * Λ ω := mul_le_mul_of_nonneg_right (card_nearIdx_le hn1 c) (hΛ0 ω)
  -- pointwise ENNReal bound
  have hptE : ∀ ω, ‖kakeyaMaximal δ f ω‖ₑ ^ p ≤
      ENNReal.ofReal M ^ p * ∑ k ∈ S, ‖a k ω‖ₑ ^ p := by
    intro ω
    have hF0 := kakeyaMaximal_nonneg (δ := δ) hf0 ω
    rw [← ofReal_norm, Real.norm_of_nonneg hF0]
    calc ENNReal.ofReal (kakeyaMaximal δ f ω) ^ p ≤ ENNReal.ofReal (M * Λ ω) ^ p :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hpt ω)) hp0.le
      _ = ENNReal.ofReal M ^ p * ∑ k ∈ S, ‖a k ω‖ₑ ^ p := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          congr 1
          rw [ENNReal.ofReal_rpow_of_nonneg (hΛ0 ω) hp0.le, ← Real.rpow_mul
            (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (ha0 k ω) p),
            one_div_mul_cancel hp0.ne', Real.rpow_one,
            ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg (ha0 k ω) p)]
          apply Finset.sum_congr rfl; intro k _
          rw [← ofReal_norm, Real.norm_of_nonneg (ha0 k ω),
            ENNReal.ofReal_rpow_of_nonneg (ha0 k ω) hp0.le]
  -- each piece
  have hpieceB : ∀ k, ∫⁻ ω, ‖a k ω‖ₑ ^ p ∂(sphereMeasure n) ≤
      ENNReal.ofReal B ^ p * ∫⁻ y, ‖piece f k y‖ₑ ^ p := by
    intro k
    have hg := isTest_comp_add (isTest_piece hf k) (corner k)
    have h1 := hsmall _ hg (fun y => piece_nonneg hf0 k _) (translated_piece_support hn1 f k)
    have hfe : kakeyaMaximal δ (fun y => piece f k (y + corner k)) = a k :=
      funext (kakeyaMaximal_comp_add δ (piece f k) (corner k))
    rw [hfe, eLpNorm_comp_add (isTest_piece hf k).1.1,
      eLpNorm_eq_rpow hp, eLpNorm_eq_rpow hp] at h1
    exact le_mul_pow_of_rpow_le hp0 (by simpa [a] using h1)
  have hmeas : ∀ k, AEMeasurable (fun ω => ‖a k ω‖ₑ ^ p) (sphereMeasure n) := fun k =>
    ((kakeyaMaximal_aestronglyMeasurable hn hp hδ (isTest_piece hf k)).enorm).pow_const p
  have hsumf : ∑ k ∈ S, ∫⁻ y, ‖piece f k y‖ₑ ^ p = ∫⁻ y, ‖f y‖ₑ ^ p := by
    rw [← lintegral_finsetSum' _ fun k _ =>
      ((isTest_piece hf k).1.1.enorm).pow_const p]
    apply lintegral_congr; intro y
    by_cases hy : f y = 0
    · have : ∀ k, piece f k y = 0 := fun k => by simp [piece, Set.indicator_apply, hy]
      simp [this, hy, ENNReal.zero_rpow_of_pos hp0]
    · have hyS : idx y ∈ S := idx_mem_boxIdx hn1 (by simpa using hR hy)
      rw [Finset.sum_eq_single (idx y)]
      · rw [show piece f (idx y) y = f y from
          Set.indicator_of_mem (show y ∈ {y | idx y = idx y} from rfl) f]
      · intro k _ hk
        rw [show piece f k y = 0 from
          Set.indicator_of_notMem (show y ∉ {y | idx y = k} from fun h => hk h.symm) f]
        simp [ENNReal.zero_rpow_of_pos hp0]
      · intro h; exact absurd hyS h
  have htotal : ∫⁻ ω, ‖kakeyaMaximal δ f ω‖ₑ ^ p ∂(sphereMeasure n) ≤
      ENNReal.ofReal (M * B) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
    calc ∫⁻ ω, ‖kakeyaMaximal δ f ω‖ₑ ^ p ∂(sphereMeasure n)
        ≤ ∫⁻ ω, ENNReal.ofReal M ^ p * ∑ k ∈ S, ‖a k ω‖ₑ ^ p ∂(sphereMeasure n) :=
          lintegral_mono hptE
      _ = ENNReal.ofReal M ^ p * ∑ k ∈ S, ∫⁻ ω, ‖a k ω‖ₑ ^ p ∂(sphereMeasure n) := by
          rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum S fun k _ => hmeas k),
            lintegral_finsetSum' _ fun k _ => hmeas k]
      _ ≤ ENNReal.ofReal M ^ p * ∑ k ∈ S, ENNReal.ofReal B ^ p * ∫⁻ y, ‖piece f k y‖ₑ ^ p := by
          gcongr with k; exact hpieceB k
      _ = ENNReal.ofReal (M * B) ^ p * ∫⁻ y, ‖f y‖ₑ ^ p := by
          rw [← Finset.mul_sum, hsumf, ← mul_assoc, ENNReal.ofReal_mul (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  rw [eLpNorm_eq_rpow hp, eLpNorm_eq_rpow hp]
  exact rpow_le_of_le_mul_pow hp0 htotal

theorem exponent_identity {δ C e α : ℝ} (hδ : 0 < δ) (n p : ℝ) (he : e = 1 - n / p - α) :
    δ⁻¹ * (C * (17 * δ ^ 2) ^ e) * δ ^ (n / p) = C * 17 ^ e * δ ^ (1 - n / p - 2 * α) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast δ 2,
    ← Real.rpow_mul hδ.le, ← Real.rpow_neg_one δ]
  have : δ ^ (-1 : ℝ) * (C * (17 ^ e * δ ^ ((2 : ℕ) * e))) * δ ^ (n / p) =
      C * 17 ^ e * (δ ^ (-1 : ℝ) * δ ^ ((2 : ℕ) * e) * δ ^ (n / p)) := by ring
  rw [this, ← Real.rpow_add hδ, ← Real.rpow_add hδ, he]
  congr 2
  push_cast; ring

/-- Part N2K: `N(p, α) ⟹ K(p, 2α)`. -/
theorem kakeya_two_mul_of_nikodym (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp1 : 1 ≤ p) (hpn : p ≤ n)
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < ((n : ℝ) + 1) / p) :
    NikodymMaximalEstimate n p α → KakeyaMaximalEstimate n p (2 * α) := by
  intro hN
  obtain ⟨C, δ₀, hδ₀, hδ₀1, hNB⟩ := (nikodymMaximalEstimate_iff hn hp1 α).1 hN
  obtain ⟨K₃, hK₃, hsmall⟩ := small_support hn hp1
  obtain ⟨M, hM, hdec⟩ := decomp hn hp1
  set e := 1 - (n : ℝ) / p - α with he
  refine (kakeyaMaximalEstimate_iff hn hp1 (2 * α)).2
    ⟨M * K₃ * (max C 0 * 17 ^ e), min (1 / 64) (Real.sqrt (δ₀ / 17)),
      lt_min (by norm_num) (Real.sqrt_pos.2 (by positivity)),
      (min_le_left _ _).trans (by norm_num), ?_⟩
  intro δ hδ hδ1 f hf hf0
  have hδ64 : δ ≤ 1 / 64 := (lt_of_lt_of_le hδ1 (min_le_left _ _)).le
  have hδs : δ < Real.sqrt (δ₀ / 17) := lt_of_lt_of_le hδ1 (min_le_right _ _)
  have hδ' : 17 * δ ^ 2 < δ₀ := by
    have h1 : δ ^ 2 < δ₀ / 17 := by
      have := (Real.lt_sqrt hδ.le).1 hδs; linarith
    linarith
  set A' := C * (17 * δ ^ 2) ^ e
  have hNB' := hNB (17 * δ ^ 2) (by positivity) hδ'
  set B := K₃ * δ⁻¹ * max A' 0 * δ ^ ((n : ℝ) / p)
  have hB0 : 0 ≤ B := by positivity
  have h := hdec δ hδ (by linarith) B hB0
    (fun g hg hg0 hgs => hsmall δ hδ hδ64 A' hNB' g hg hg0 hgs) f hf hf0
  refine h.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) (by positivity))
  have hmax : max A' 0 = max C 0 * (17 * δ ^ 2) ^ e := by
    have hx : 0 < (17 * δ ^ 2) ^ e := by positivity
    rcases le_total C 0 with hC | hC
    · rw [max_eq_right hC, zero_mul, max_eq_right (mul_nonpos_of_nonpos_of_nonneg hC hx.le)]
    · rw [max_eq_left hC, max_eq_left (mul_nonneg hC hx.le)]
  simp only [B, hmax]
  have := exponent_identity (C := max C 0) hδ n p he (α := α)
  rw [show M * (K₃ * δ⁻¹ * (max C 0 * (17 * δ ^ 2) ^ e) * δ ^ ((n : ℝ) / p)) =
    M * K₃ * (δ⁻¹ * (max C 0 * (17 * δ ^ 2) ^ e) * δ ^ ((n : ℝ) / p)) by ring, this]
  ring

end TaoBR.T410.PartN2K

end S_PartN2K

section S_K2NDefs

open MeasureTheory Metric Set
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR.T410.K2N

open TaoBR.T410

variable {n : ℕ}

/-! ## Definitions -/

/-- The unit far piece of width `ε` from the base point `x` in the direction `ω`:
`{y : 1/4 < ⟪y - x, ω⟫ < 2, ‖perp‖ < ε}` (open). -/
def piece (ε : ℝ) (x ω : E n) : Set (E n) :=
  {y | 1 / 4 < inner ℝ (y - x) ω ∧ inner ℝ (y - x) ω < 2 ∧
    ‖y - x - inner ℝ (y - x) ω • ω‖ < ε}

/-- The cap of unit directions making an angle with `e` whose cosine is at least `1/√n`. -/
def capDirs (e : E n) : Set (E n) :=
  {ω | ‖ω‖ = 1 ∧ (Real.sqrt n)⁻¹ ≤ inner ℝ ω e}

/-- The cap far maximal function (unnormalised integrals over unit far pieces). -/
noncomputable def capMax (e : E n) (ε : ℝ) (g : E n → ℝ≥0∞) (x : E n) : ℝ≥0∞ :=
  ⨆ ω ∈ capDirs e, ∫⁻ y in piece ε x ω, g y

/-- The last basis vector `(0, …, 0, 1)` of `ℝ^{m+1}`. -/
noncomputable def eLast (m : ℕ) : E (m + 1) := mkPoint 0 1


end TaoBR.T410.K2N

end S_K2NDefs

section S_PartB1a

/-!
# Theorem 4.10, Part K2N, Part B1: `lintegral_mkPoint` and `capMax_le`

Fubini in the coordinates `ℝ^{m+1} = ℝ^m × ℝ`, and the cap estimate on all of `ℝⁿ` from the
frozen estimate (isometry to the last coordinate, freezing the height, horizontal
localisation by averaging over unit balls). Assumes `frozen_le` (Part B2) and the Part I lemmas.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal SchwartzMap



namespace TaoBR.T410.K2N.PartB1

open TaoBR.T410 TaoBR.T410.K2N Filter
open scoped RealInnerProductSpace Topology

/-! ## Coordinates `ℝ^{m+1} = ℝ^m × ℝ` -/

section Coords

variable {m : ℕ}

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp [horiz]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

@[simp] theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

@[simp] theorem horiz_add (y y' : E (m + 1)) : horiz (y + y') = horiz y + horiz y' := by
  ext i; simp
@[simp] theorem horiz_sub (y y' : E (m + 1)) : horiz (y - y') = horiz y - horiz y' := by
  ext i; simp
@[simp] theorem horiz_smul (r : ℝ) (y : E (m + 1)) : horiz (r • y) = r • horiz y := by
  ext i; simp
@[simp] theorem vert_add (y y' : E (m + 1)) : vert (y + y') = vert y + vert y' := by
  simp [vert]
@[simp] theorem vert_sub (y y' : E (m + 1)) : vert (y - y') = vert y - vert y' := by
  simp [vert]
@[simp] theorem vert_smul (r : ℝ) (y : E (m + 1)) : vert (r • y) = r * vert y := by
  simp [vert]

theorem norm_sq_hv (y : E (m + 1)) : ‖y‖ ^ 2 = ‖horiz y‖ ^ 2 + vert y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [vert]

theorem norm_mkPoint_sq (u : E m) (t : ℝ) : ‖mkPoint u t‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [norm_sq_hv]; simp

theorem abs_vert_le (y : E (m + 1)) : |vert y| ≤ ‖y‖ := by
  have := norm_sq_hv y
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg y)]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖horiz y‖])

theorem norm_le_horiz_add_vert (y : E (m + 1)) : ‖y‖ ≤ ‖horiz y‖ + |vert y| := by
  have := norm_sq_hv y
  have h : ‖y‖ ^ 2 ≤ (‖horiz y‖ + |vert y|) ^ 2 := by
    rw [this]; nlinarith [norm_nonneg (horiz y), abs_nonneg (vert y), sq_abs (vert y)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem inner_eLast (y : E (m + 1)) : ⟪y, eLast m⟫ = vert y := by
  have : eLast m = EuclideanSpace.single (Fin.last m) 1 := by
    apply ext_hv
    · ext i; simp [eLast]
    · simp [eLast, vert]
  rw [this, EuclideanSpace.inner_single_right]; simp [vert]

theorem continuous_vert : Continuous (vert : E (m + 1) → ℝ) := by
  unfold vert; fun_prop

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurable_mkPoint : Measurable fun q : E m × ℝ => mkPoint q.1 q.2 :=
  continuous_mkPoint.measurable

end Coords

/-! ## Fubini in `ℝ^{m+1} = ℝ^m × ℝ` -/

theorem measurePreserving_mkPoint (m : ℕ) :
    MeasurePreserving (fun q : E m × ℝ => mkPoint q.1 q.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ))
      ((volume : Measure (E m)).prod (volume : Measure ℝ)) (volume.prod volume) :=
    (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
  have h2 := (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
    (ν := (volume : Measure ℝ)))
  have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
  have h := h4.comp (h3.comp (h2.comp h1))
  have heq : (fun q : E m × ℝ => mkPoint q.1 q.2) = (WithLp.toLp 2 ∘
      ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm ∘
        Prod.swap ∘ Prod.map (WithLp.ofLp (p := 2) (V := Fin m → ℝ)) (id : ℝ → ℝ)) := by
    funext q
    apply ext_hv
    · ext i; simp [Function.comp]
    · simp [vert, Function.comp]
  rw [heq]; exact h

/-- (Part B1) Fubini in the coordinates `ℝ^{m+1} = ℝ^m × ℝ`. -/
theorem lintegral_mkPoint (m : ℕ) (F : E (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x = ∫⁻ u, ∫⁻ h, F (mkPoint u h) := by
  rw [← (measurePreserving_mkPoint m).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp measurable_mkPoint).aemeasurable



end TaoBR.T410.K2N.PartB1

end S_PartB1a

namespace TaoBR.T410.K2N
alias lintegral_mkPoint := TaoBR.T410.K2N.PartB1.lintegral_mkPoint
end TaoBR.T410.K2N

section S_PartB2

/-!
# Theorem 4.10, Part K2N, Part B2: `frozen_le`

The projective-map comparison of the frozen cap far maximal function with the Kakeya maximal
function. Assumes `lintegral_mkPoint` (Part B1) and the Part I lemmas.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal SchwartzMap



namespace TaoBR.T410.K2N.PartB2

open TaoBR.T410 TaoBR.T410.K2N
open scoped RealInnerProductSpace

/-! ## Coordinates `ℝ^{m+1} = ℝ^m × ℝ` -/

section Coords

variable {m : ℕ}

@[simp] theorem mkPoint_castSucc (u : E m) (t : ℝ) (i : Fin m) :
    mkPoint u t (Fin.castSucc i) = u i := by
  simp [mkPoint]

@[simp] theorem mkPoint_last (u : E m) (t : ℝ) : mkPoint u t (Fin.last m) = t := by
  simp [mkPoint]

@[simp] theorem vert_mkPoint (u : E m) (t : ℝ) : vert (mkPoint u t) = t := by
  simp [vert]

@[simp] theorem horiz_mkPoint (u : E m) (t : ℝ) : horiz (mkPoint u t) = u := by
  ext i; simp [horiz]

@[simp] theorem horiz_apply (y : E (m + 1)) (i : Fin m) : horiz y i = y (Fin.castSucc i) := by
  simp [horiz]

theorem ext_hv {y y' : E (m + 1)} (h1 : horiz y = horiz y') (h2 : vert y = vert y') : y = y' := by
  ext i
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => have := congrArg (fun z : E m => z j) h1; simpa using this

@[simp] theorem mkPoint_horiz_vert (y : E (m + 1)) : mkPoint (horiz y) (vert y) = y :=
  ext_hv (by simp) (by simp)

@[simp] theorem horiz_add (y y' : E (m + 1)) : horiz (y + y') = horiz y + horiz y' := by
  ext i; simp
@[simp] theorem horiz_sub (y y' : E (m + 1)) : horiz (y - y') = horiz y - horiz y' := by
  ext i; simp
@[simp] theorem horiz_smul (r : ℝ) (y : E (m + 1)) : horiz (r • y) = r • horiz y := by
  ext i; simp
@[simp] theorem vert_add (y y' : E (m + 1)) : vert (y + y') = vert y + vert y' := by
  simp [vert]
@[simp] theorem vert_sub (y y' : E (m + 1)) : vert (y - y') = vert y - vert y' := by
  simp [vert]
@[simp] theorem vert_smul (r : ℝ) (y : E (m + 1)) : vert (r • y) = r * vert y := by
  simp [vert]

theorem norm_sq_hv (y : E (m + 1)) : ‖y‖ ^ 2 = ‖horiz y‖ ^ 2 + vert y ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [vert]

theorem norm_mkPoint_sq (u : E m) (t : ℝ) : ‖mkPoint u t‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [norm_sq_hv]; simp

theorem norm_horiz_le (y : E (m + 1)) : ‖horiz y‖ ≤ ‖y‖ := by
  have := norm_sq_hv y
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg (vert y)])

theorem abs_vert_le (y : E (m + 1)) : |vert y| ≤ ‖y‖ := by
  have := norm_sq_hv y
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (norm_nonneg y)]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖horiz y‖])

theorem norm_le_horiz_add_vert (y : E (m + 1)) : ‖y‖ ≤ ‖horiz y‖ + |vert y| := by
  have := norm_sq_hv y
  have h : ‖y‖ ^ 2 ≤ (‖horiz y‖ + |vert y|) ^ 2 := by
    rw [this]; nlinarith [norm_nonneg (horiz y), abs_nonneg (vert y), sq_abs (vert y)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

theorem continuous_horiz : Continuous (horiz : E (m + 1) → E m) := by
  unfold horiz; fun_prop

theorem continuous_vert : Continuous (vert : E (m + 1) → ℝ) := by
  unfold vert; fun_prop

theorem continuous_mkPoint : Continuous fun q : E m × ℝ => mkPoint q.1 q.2 := by
  unfold mkPoint
  apply (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  induction i using Fin.lastCases with
  | last => simp; fun_prop
  | cast j => simp; fun_prop

theorem measurable_mkPoint : Measurable fun q : E m × ℝ => mkPoint q.1 q.2 :=
  continuous_mkPoint.measurable

end Coords


/-! ## The projective map -/

section Proj

variable {m : ℕ}

/-- The projective map `(ȳ, t) ↦ (ȳ/t, 1/t)`. -/
noncomputable def phi (y : E (m + 1)) : E (m + 1) :=
  mkPoint ((vert y)⁻¹ • horiz y) (vert y)⁻¹

@[simp] theorem vert_phi (y : E (m + 1)) : vert (phi y) = (vert y)⁻¹ := by simp [phi]
@[simp] theorem horiz_phi (y : E (m + 1)) : horiz (phi y) = (vert y)⁻¹ • horiz y := by simp [phi]

theorem phi_mkPoint (u : E m) (t : ℝ) : phi (mkPoint u t) = mkPoint (t⁻¹ • u) t⁻¹ := by
  simp [phi]

theorem phi_phi {y : E (m + 1)} (hy : vert y ≠ 0) : phi (phi y) = y := by
  apply ext_hv
  · simp [smul_smul, inv_inv, mul_inv_cancel₀ hy]
  · simp

theorem measurable_phi : Measurable (phi : E (m + 1) → E (m + 1)) := by
  have h1 : Measurable fun y : E (m + 1) => (vert y)⁻¹ :=
    continuous_vert.measurable.inv
  have h2 : Measurable fun y : E (m + 1) => ((vert y)⁻¹ • horiz y, (vert y)⁻¹) :=
    (h1.smul continuous_horiz.measurable).prodMk h1
  exact measurable_mkPoint.comp h2

theorem norm_mkPoint_le (u : E m) (t : ℝ) : ‖mkPoint u t‖ ≤ ‖u‖ + |t| := by
  simpa using norm_le_horiz_add_vert (mkPoint u t)

/-- `φ` is Lipschitz on `{t ≥ a}` near a point of norm `≤ R`. -/
theorem norm_phi_sub_le {a R : ℝ} (ha : 0 < a) {y y' : E (m + 1)} (hy : a ≤ vert y)
    (hy' : a ≤ vert y') (hR : ‖y'‖ ≤ R) :
    ‖phi y - phi y'‖ ≤ (1 / a + (R + 1) / a ^ 2) * ‖y - y'‖ := by
  set t := vert y
  set t' := vert y'
  have ht : 0 < t := ha.trans_le hy
  have ht' : 0 < t' := ha.trans_le hy'
  set d := ‖y - y'‖
  have hd : 0 ≤ d := norm_nonneg _
  have hdh : ‖horiz y - horiz y'‖ ≤ d := by rw [← horiz_sub]; exact norm_horiz_le _
  have hdv : |t - t'| ≤ d := by
    have := abs_vert_le (y - y'); rwa [vert_sub] at this
  have hh' : ‖horiz y'‖ ≤ R := (norm_horiz_le y').trans hR
  have hinv : |t⁻¹ - t'⁻¹| ≤ d / a ^ 2 := by
    rw [inv_sub_inv ht.ne' ht'.ne', abs_div, abs_of_pos (mul_pos ht ht'), abs_sub_comm]
    rw [div_le_div_iff₀ (mul_pos ht ht') (by positivity)]
    have : a ^ 2 ≤ t * t' := by nlinarith
    nlinarith [abs_nonneg (t - t')]
  have heq : phi y - phi y' = mkPoint (t⁻¹ • (horiz y - horiz y') + (t⁻¹ - t'⁻¹) • horiz y')
      (t⁻¹ - t'⁻¹) := by
    apply ext_hv
    · simp only [horiz_sub, horiz_phi, horiz_mkPoint]; rw [smul_sub, sub_smul]; abel
    · simp [t, t']
  rw [heq]
  refine (norm_mkPoint_le _ _).trans ?_
  have h1 : ‖t⁻¹ • (horiz y - horiz y')‖ ≤ d / a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht), inv_mul_eq_div]
    calc ‖horiz y - horiz y'‖ / t ≤ d / t := by gcongr
      _ ≤ d / a := by gcongr
  have h2 : ‖(t⁻¹ - t'⁻¹) • horiz y'‖ ≤ d / a ^ 2 * R := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hinv hh' (norm_nonneg _) (by positivity)
  calc ‖t⁻¹ • (horiz y - horiz y') + (t⁻¹ - t'⁻¹) • horiz y'‖ + |t⁻¹ - t'⁻¹|
      ≤ (d / a + d / a ^ 2 * R) + d / a ^ 2 := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = (1 / a + (R + 1) / a ^ 2) * d := by field_simp; ring

end Proj


/-! ## Geometry: the image of a far piece lies in a few tubes -/

section Geom

variable {m : ℕ}

/-- The common direction `ν(u)` of the images of lines through `(u, 0)`. -/
noncomputable def nu (u : E m) : E (m + 1) := ‖mkPoint u 1‖⁻¹ • mkPoint u 1

theorem one_le_norm_mkPoint_one (u : E m) : 1 ≤ ‖mkPoint u 1‖ := by
  have h := norm_mkPoint_sq u 1
  have : (1 : ℝ) ^ 2 ≤ ‖mkPoint u 1‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖u‖]
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) two_ne_zero).1 this

theorem norm_mkPoint_one_le {u : E m} (hu : ‖u‖ ≤ 1) : ‖mkPoint u 1‖ ≤ 2 := by
  have h := norm_mkPoint_sq u 1
  have : ‖mkPoint u 1‖ ^ 2 ≤ 2 ^ 2 := by rw [h]; nlinarith [norm_nonneg u]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 this

theorem norm_nu (u : E m) : ‖nu u‖ = 1 := by
  have h := one_le_norm_mkPoint_one u
  rw [nu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

/-- The Lipschitz constant of `φ` used for the tubes. -/
noncomputable def Lam (c : ℝ) : ℝ := 1 / (c / 2) + (3 + 1) / (c / 2) ^ 2

/-- The number of tubes. -/
noncomputable def Mn (c : ℝ) : ℕ := ⌈16 / c⌉₊ + 1

/-- The centres of the tubes. -/
noncomputable def ctr (u : E m) (ω : E (m + 1)) (j : ℕ) : E (m + 1) :=
  mkPoint ((vert ω)⁻¹ • horiz ω) 0 + ((j : ℝ) / 4) • nu u

theorem Lam_pos {c : ℝ} (hc : 0 < c) : 0 < Lam c := by unfold Lam; positivity

theorem geom {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c / 2) (hΛε : Lam c * ε ≤ 3 / 8)
    {u : E m} (hu : ‖u‖ ≤ 1) {ω y : E (m + 1)} (hω : ‖ω‖ = 1)
    (hy : y ∈ piece ε (mkPoint u 0) ω) (hyv : c ≤ vert y) :
    ∃ j < Mn c, phi y ∈ tube (Lam c * ε) (nu u) (ctr u ω j) := by
  obtain ⟨hτ1, hτ2, hw⟩ := hy
  set x := mkPoint u 0 with hx
  set τ := ⟪y - x, ω⟫ with hτ
  set w := y - x - τ • ω with hw_def
  set y' := x + τ • ω with hy'
  set s := vert ω with hs
  have hyy' : y - y' = w := by rw [hw_def, hy']; abel
  have hxn : ‖x‖ ≤ 1 := by rw [hx]; simpa using (norm_mkPoint_le u 0).trans (by simpa using hu)
  have hvw : |vert w| ≤ ‖w‖ := abs_vert_le w
  have hvy' : vert y' = τ * s := by simp [hy', hx, hs]
  have hvy : vert y = τ * s + vert w := by
    have : y = y' + w := by rw [← hyy']; abel
    rw [this, vert_add, hvy']
  have hτs : c / 2 ≤ τ * s := by
    have := le_abs_self (vert w); linarith
  have hτs0 : 0 < τ * s := by linarith
  have hτ0 : 0 < τ := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, mul_zero] at hτs0; exact lt_irrefl _ hτs0
  have hy'n : ‖y'‖ ≤ 3 := by
    calc ‖y'‖ ≤ ‖x‖ + ‖τ • ω‖ := norm_add_le _ _
      _ = ‖x‖ + τ := by rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hτ0]
      _ ≤ 3 := by linarith
  -- Lipschitz
  have hlip := norm_phi_sub_le (half_pos hc) (by linarith : c / 2 ≤ vert y)
    (by rw [hvy']; exact hτs) hy'n
  rw [hyy'] at hlip
  set e := phi y - phi y' with he
  have hen : ‖e‖ ≤ Lam c * ε := by
    refine hlip.trans ?_
    rw [show (1 / (c / 2) + (3 + 1) / (c / 2) ^ 2) = Lam c from rfl]
    exact mul_le_mul_of_nonneg_left hw.le (Lam_pos hc).le
  -- the image of the axis point
  set V := mkPoint u 1 with hV
  have hV1 : 1 ≤ ‖V‖ := one_le_norm_mkPoint_one u
  have hV2 : ‖V‖ ≤ 2 := norm_mkPoint_one_le hu
  set lam := (τ * s)⁻¹ * ‖V‖ with hlam
  have hphiy' : phi y' = mkPoint (s⁻¹ • horiz ω) 0 + lam • nu u := by
    rw [hlam, nu, ← hV, smul_smul, mul_assoc, mul_inv_cancel₀ (by linarith : ‖V‖ ≠ 0), mul_one]
    apply ext_hv
    · rw [horiz_phi, hvy']
      simp only [hy', hx, hV, horiz_add, horiz_smul, horiz_mkPoint]
      rw [smul_add, smul_smul, show (τ * s)⁻¹ * τ = s⁻¹ by field_simp]; abel
    · simp [hvy', hV]
  have hlam0 : 0 ≤ lam := by positivity
  have hlamL : lam ≤ 4 / c := by
    have h1 : (τ * s)⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ hτs0 (by positivity)]; rw [inv_div]; exact hτs
    calc lam ≤ 2 / c * 2 := mul_le_mul h1 hV2 (norm_nonneg _) (by positivity)
      _ = 4 / c := by ring
  set j := ⌊4 * lam + 1 / 2⌋₊ with hj
  have hj1 : (j : ℝ) ≤ 4 * lam + 1 / 2 := Nat.floor_le (by positivity)
  have hj2 : 4 * lam + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · have : (j : ℝ) < (⌈16 / c⌉₊ : ℝ) + 1 := by
      have := Nat.le_ceil (16 / c)
      have h4 : 4 * lam ≤ 16 / c := by
        calc 4 * lam ≤ 4 * (4 / c) := by gcongr
          _ = 16 / c := by ring
      linarith
    unfold Mn; exact_mod_cast this
  · have hz : phi y - ctr u ω j = (lam - j / 4) • nu u + e := by
      rw [he, hphiy', ctr, sub_smul]; abel
    have hnu := norm_nu u
    have hin : ⟪phi y - ctr u ω j, nu u⟫ = (lam - j / 4) + ⟪e, nu u⟫ := by
      rw [hz, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hnu]; ring
    refine ⟨?_, ?_⟩
    · rw [hin]
      have h1 : |lam - j / 4| ≤ 1 / 8 := by rw [abs_le]; constructor <;> linarith
      have h2 : |⟪e, nu u⟫| ≤ Lam c * ε := by
        have := abs_real_inner_le_norm e (nu u); rw [hnu, mul_one] at this; linarith
      calc |lam - j / 4 + ⟪e, nu u⟫| ≤ |lam - j / 4| + |⟪e, nu u⟫| := abs_add_le _ _
        _ ≤ 1 / 2 := by linarith
    · have : phi y - ctr u ω j - ⟪phi y - ctr u ω j, nu u⟫ • nu u = e - ⟪e, nu u⟫ • nu u := by
        rw [hin, hz, add_smul]; abel
      rw [this]
      have h := norm_sub_sq_real e (⟪e, nu u⟫ • nu u)
      rw [inner_smul_right, norm_smul, hnu, Real.norm_eq_abs, mul_one, sq_abs] at h
      have : ‖e - ⟪e, nu u⟫ • nu u‖ ≤ ‖e‖ := by
        have h' : ‖e - ⟪e, nu u⟫ • nu u‖ ^ 2 ≤ ‖e‖ ^ 2 := by
          rw [h]; nlinarith [sq_nonneg ⟪e, nu u⟫]
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'
      linarith

end Geom


/-! ## Change of variables -/

section CoV

variable {m : ℕ}

theorem map_dil_volume {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Measure.map (fun y : E k => δ⁻¹ • y) volume = ENNReal.ofReal (δ ^ k) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hδ.ne'), finrank_euclideanSpace_fin, inv_pow,
    inv_inv, abs_of_pos (pow_pos hδ k)]

/-- Scaling in `ℝ^k`. -/
theorem lintegral_comp_inv_smul {k : ℕ} {t : ℝ} (ht : 0 < t) (K : E k → ℝ≥0∞) :
    ∫⁻ z, K (t⁻¹ • z) = ENNReal.ofReal (t ^ k) * ∫⁻ z, K z := by
  have h := lintegral_map_equiv K (MeasurableEquiv.smul₀ (G₀ := ℝ) (α := E k) t⁻¹
    (inv_ne_zero ht.ne')) (μ := volume)
  have hc : ⇑(MeasurableEquiv.smul₀ (G₀ := ℝ) (α := E k) t⁻¹ (inv_ne_zero ht.ne')) =
      fun y : E k => t⁻¹ • y := rfl
  rw [hc, map_dil_volume ht, lintegral_smul_measure] at h
  rw [← h]; rfl

/-- The one-dimensional substitution `t ↦ 1/t` on `(0, ∞)`. -/
theorem lintegral_Ioi_inv (H : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((t⁻¹) ^ 2) * H t⁻¹ = ∫⁻ s in Ioi (0 : ℝ), H s := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := fun t => t⁻¹)
    (f' := fun t => -(t ^ 2)⁻¹) measurableSet_Ioi
    (fun t ht => (hasDerivAt_inv (ne_of_gt ht)).hasDerivWithinAt)
    (fun a _ b _ hab => inv_injective hab) H
  have himg : (fun t : ℝ => t⁻¹) '' Ioi 0 = Ioi 0 := by
    ext z; constructor
    · rintro ⟨t, ht, rfl⟩; exact mem_Ioi.2 (inv_pos.2 (mem_Ioi.1 ht))
    · intro hz; exact ⟨z⁻¹, mem_Ioi.2 (inv_pos.2 (mem_Ioi.1 hz)), inv_inv z⟩
  rw [himg] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  simp only [abs_neg, inv_pow]
  rw [abs_of_pos (by positivity)]

theorem indicator_mkPoint (F : E (m + 1) → ℝ≥0∞) (u : E m) :
    (fun h => {z : E (m + 1) | 0 < vert z}.indicator F (mkPoint u h)) =
      (Ioi (0 : ℝ)).indicator (fun h => F (mkPoint u h)) := by
  funext h; by_cases hh : 0 < h <;> simp [hh]

theorem measurableSet_vert_pos : MeasurableSet {z : E (m + 1) | 0 < vert z} :=
  measurableSet_lt measurable_const continuous_vert.measurable

/-- The change of variables `y = φ(z)` on the upper half-space, with Jacobian `t^{-(m+2)}`. -/
theorem cov (G : E (m + 1) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, {z : E (m + 1) | 0 < vert z}.indicator
        (fun z => ENNReal.ofReal ((vert z)⁻¹ ^ (m + 2)) * G (phi z)) z =
      ∫⁻ y, {y : E (m + 1) | 0 < vert y}.indicator G y := by
  have hm1 : Measurable fun z : E (m + 1) => ENNReal.ofReal ((vert z)⁻¹ ^ (m + 2)) * G (phi z) :=
    ((continuous_vert.measurable.inv.pow_const _).ennreal_ofReal).mul (hG.comp measurable_phi)
  rw [lintegral_mkPoint m _ (hm1.indicator measurableSet_vert_pos),
    lintegral_mkPoint m _ (hG.indicator measurableSet_vert_pos)]
  simp_rw [indicator_mkPoint]
  simp only [vert_mkPoint, phi_mkPoint]
  have hmeas1 : Measurable (Function.uncurry fun (u : E m) (h : ℝ) => (Ioi (0 : ℝ)).indicator
      (fun h => ENNReal.ofReal (h⁻¹ ^ (m + 2)) * G (mkPoint (h⁻¹ • u) h⁻¹)) h) := by
    have : Measurable fun q : E m × ℝ =>
        ENNReal.ofReal (q.2⁻¹ ^ (m + 2)) * G (mkPoint (q.2⁻¹ • q.1) q.2⁻¹) := by
      refine ((measurable_snd.inv.pow_const _).ennreal_ofReal).mul (hG.comp ?_)
      exact measurable_mkPoint.comp ((measurable_snd.inv.smul measurable_fst).prodMk
        measurable_snd.inv)
    exact this.indicator (measurableSet_Ioi.preimage measurable_snd)
  have hmeas2 : Measurable (Function.uncurry fun (u : E m) (h : ℝ) => (Ioi (0 : ℝ)).indicator
      (fun h => G (mkPoint u h)) h) := by
    have : Measurable fun q : E m × ℝ => G (mkPoint q.1 q.2) := hG.comp measurable_mkPoint
    exact this.indicator (measurableSet_Ioi.preimage measurable_snd)
  rw [lintegral_lintegral_swap hmeas1.aemeasurable, lintegral_lintegral_swap hmeas2.aemeasurable]
  have e1 : ∀ h : ℝ, ∫⁻ u : E m, (Ioi (0 : ℝ)).indicator
      (fun h => ENNReal.ofReal (h⁻¹ ^ (m + 2)) * G (mkPoint (h⁻¹ • u) h⁻¹)) h =
      (Ioi (0 : ℝ)).indicator (fun h => ENNReal.ofReal ((h⁻¹) ^ 2) *
        ∫⁻ u : E m, G (mkPoint u h⁻¹)) h := by
    intro h
    by_cases hh : 0 < h
    · simp only [indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_comp_inv_smul hh (fun z => G (mkPoint z h⁻¹)), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      simp only [pow_add, inv_pow]
      field_simp
    · simp [indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh)]
  have e2 : ∀ h : ℝ, ∫⁻ u : E m, (Ioi (0 : ℝ)).indicator (fun h => G (mkPoint u h)) h =
      (Ioi (0 : ℝ)).indicator (fun h => ∫⁻ u : E m, G (mkPoint u h)) h := by
    intro h
    by_cases hh : 0 < h
    · simp only [indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh)]
    · simp [indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh)]
  simp_rw [e1, e2]
  rw [lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi]
  exact lintegral_Ioi_inv (fun s => ∫⁻ u : E m, G (mkPoint u s))

end CoV


/-! ## Gnomonic integration -/

section Gnomonic

variable {m : ℕ}

/-- The constant of the gnomonic bound. -/
noncomputable def K2 (m : ℕ) : ℝ := ((3 : ℝ) ^ (m + 1) - 1 ^ (m + 1)) / ((m + 1 : ℕ) : ℝ)

theorem K2_pos (m : ℕ) : 0 < K2 m := by
  unfold K2
  apply div_pos _ (by positivity)
  have : (1 : ℝ) ^ (m + 1) < 3 ^ (m + 1) := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith

theorem normalize_smul {k : ℕ} {r : ℝ} (hr : 0 < r) (v : E k) :
    ‖r • v‖⁻¹ • (r • v) = ‖v‖⁻¹ • v := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul]
  by_cases hv : v = 0
  · simp [hv]
  · congr 1; field_simp

theorem mkPoint_inv_smul_one {s : ℝ} (hs : s ≠ 0) (z : E m) :
    mkPoint (s⁻¹ • z) 1 = s⁻¹ • mkPoint z s :=
  ext_hv (by simp) (by simp [inv_mul_cancel₀ hs])

/-- The annulus `{a < ‖x‖ < b}`. -/
def annulus (k : ℕ) (a b : ℝ) : Set (E k) := {x : E k | a < ‖x‖ ∧ ‖x‖ < b}

theorem measurableSet_annulus' (k : ℕ) (a b : ℝ) : MeasurableSet (annulus k a b) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem gnomonic (hm : 1 ≤ m) (G : E (m + 1) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ u in closedBall (0 : E m) 1, G (nu u) ≤
      ENNReal.ofReal (K2 m) * ∫⁻ ω, G (ω : E (m + 1)) ∂(sphereMeasure (m + 1)) := by
  set K : E m → ℝ≥0∞ := (closedBall (0 : E m) 1).indicator (fun u => G (nu u)) with hK
  set Q : E (m + 1) → ℝ≥0∞ := (annulus (m + 1) 1 3).indicator (fun y => G (‖y‖⁻¹ • y)) with hQ
  have hQm : Measurable Q := by
    refine Measurable.indicator ?_ (measurableSet_annulus' _ _ _)
    exact hG.comp (measurable_norm.inv.smul measurable_id)
  have hstep : ∀ s ∈ Ioo (1 : ℝ) 2, ∫⁻ u, K u ≤ ∫⁻ z, Q (mkPoint z s) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (s ^ m) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hs.1.le)
    calc ∫⁻ u, K u ≤ ENNReal.ofReal (s ^ m) * ∫⁻ u, K u := le_mul_of_one_le_left zero_le h1
      _ = ∫⁻ z, K (s⁻¹ • z) := (lintegral_comp_inv_smul hs0 K).symm
      _ ≤ ∫⁻ z, Q (mkPoint z s) := by
        apply lintegral_mono; intro z
        by_cases hz : s⁻¹ • z ∈ closedBall (0 : E m) 1
        · show K (s⁻¹ • z) ≤ Q (mkPoint z s)
          rw [hK, indicator_of_mem hz]
          have hzs : ‖z‖ ≤ s := by
            rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
              abs_of_pos hs0, inv_mul_le_iff₀ hs0, mul_one] at hz
            exact hz
          have hA : mkPoint z s ∈ annulus (m + 1) 1 3 := by
            have h := norm_mkPoint_sq z s
            have hn := norm_nonneg (mkPoint z s)
            have hz0 := norm_nonneg z
            constructor
            · by_contra hc; push Not at hc; nlinarith [hs.1]
            · by_contra hc; push Not at hc; nlinarith [hs.2]
          rw [hQ, indicator_of_mem hA, nu, mkPoint_inv_smul_one hs0.ne',
            normalize_smul (inv_pos.2 hs0)]
        · show K (s⁻¹ • z) ≤ Q (mkPoint z s)
          rw [hK, indicator_of_notMem hz]; exact zero_le
  have hvol : volume (Ioo (1 : ℝ) 2) = 1 := by rw [Real.volume_Ioo]; norm_num
  have hswap : Measurable (Function.uncurry fun (z : E m) (s : ℝ) => Q (mkPoint z s)) :=
    hQm.comp measurable_mkPoint
  calc ∫⁻ u in closedBall (0 : E m) 1, G (nu u) = ∫⁻ u, K u :=
        (lintegral_indicator measurableSet_closedBall _).symm
    _ = ∫⁻ _ in Ioo (1 : ℝ) 2, ∫⁻ u, K u := by rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ s in Ioo (1 : ℝ) 2, ∫⁻ z, Q (mkPoint z s) :=
        setLIntegral_mono' measurableSet_Ioo hstep
    _ ≤ ∫⁻ s, ∫⁻ z, Q (mkPoint z s) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, ∫⁻ s, Q (mkPoint z s) := (lintegral_lintegral_swap hswap.aemeasurable).symm
    _ = ∫⁻ y, Q y := (lintegral_mkPoint m Q hQm).symm
    _ = ∫⁻ y in annulus (m + 1) 1 3, G (‖y‖⁻¹ • y) :=
        lintegral_indicator (measurableSet_annulus' _ _ _) _
    _ = ENNReal.ofReal (K2 m) * ∫⁻ ω, G (ω : E (m + 1)) ∂(sphereMeasure (m + 1)) := by
        have := lintegral_annulus (n := m + 1) (by omega) G hG (by norm_num : (0 : ℝ) < 1)
          (by norm_num : (1 : ℝ) < 3)
        rw [annulus, this]; rfl

/-- `ν(u)` as a point of the sphere. -/
noncomputable def nuS (u : E m) : sphere (0 : E (m + 1)) 1 :=
  ⟨nu u, by rw [mem_sphere, dist_zero_right, norm_nu]⟩

/-- Gnomonic transfer for an a.e.-strongly measurable function on the sphere. -/
theorem sphere_gnomonic (hm : 1 ≤ m) {p : ℝ} (F : sphere (0 : E (m + 1)) 1 → ℝ)
    (hF : AEStronglyMeasurable F (sphereMeasure (m + 1))) :
    ∫⁻ u in closedBall (0 : E m) 1, ‖F (nuS u)‖ₑ ^ p ≤
      ENNReal.ofReal (K2 m) * ∫⁻ ω, ‖F ω‖ₑ ^ p ∂(sphereMeasure (m + 1)) := by
  set F₀ := hF.mk F
  have hF₀ : StronglyMeasurable F₀ := hF.stronglyMeasurable_mk
  have hae : F =ᵐ[sphereMeasure (m + 1)] F₀ := hF.ae_eq_mk
  have emb : MeasurableEmbedding (Subtype.val : sphere (0 : E (m + 1)) 1 → E (m + 1)) :=
    MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet
  set Fh : E (m + 1) → ℝ := Function.extend Subtype.val F₀ (fun _ => 0)
  have hFh : Measurable Fh := emb.measurable_extend hF₀.measurable measurable_const
  have hFh_apply : ∀ ω : sphere (0 : E (m + 1)) 1, Fh ω = F₀ ω := fun ω =>
    Subtype.val_injective.extend_apply _ _ ω
  set G : E (m + 1) → ℝ≥0∞ := fun y => ‖Fh y‖ₑ ^ p
  have hG : Measurable G := hFh.enorm.pow_const p
  set S := {ω : sphere (0 : E (m + 1)) 1 | F ω ≠ F₀ ω}
  have hS : sphereMeasure (m + 1) S = 0 := by
    have := hae; rw [Filter.EventuallyEq, ae_iff] at this; exact this
  set B := toMeasurable (sphereMeasure (m + 1)) S
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : sphereMeasure (m + 1) B = 0 := by rw [measure_toMeasurable]; exact hS
  have hSB : S ⊆ B := subset_toMeasurable _ _
  set Bh := Subtype.val '' B
  have hBhm : MeasurableSet Bh := emb.measurableSet_image' hBm
  have hbad := gnomonic hm (Bh.indicator 1) (measurable_one.indicator hBhm)
  have hind : ∀ ω : sphere (0 : E (m + 1)) 1,
      Bh.indicator (1 : E (m + 1) → ℝ≥0∞) ω = B.indicator 1 ω := by
    intro ω
    by_cases h : ω ∈ B
    · rw [Set.indicator_of_mem (Set.mem_image_of_mem _ h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
      rintro ⟨ω', hω', he⟩; exact h (Subtype.val_injective he ▸ hω')
  simp_rw [hind] at hbad
  rw [lintegral_indicator_one hBm, hB0, mul_zero, nonpos_iff_eq_zero] at hbad
  have hgood : ∀ᵐ u ∂(volume.restrict (closedBall (0 : E m) 1)), nu u ∉ Bh := by
    have hmeas : Measurable fun u : E m => Bh.indicator (1 : E (m + 1) → ℝ≥0∞) (nu u) := by
      refine (measurable_one.indicator hBhm).comp ?_
      unfold nu
      have : Measurable fun u : E m => mkPoint u 1 :=
        measurable_mkPoint.comp (measurable_id.prodMk measurable_const)
      exact (this.norm.inv).smul this
    have := (lintegral_eq_zero_iff hmeas).1 hbad
    filter_upwards [this] with u hu
    intro hmem
    simp [Set.indicator_of_mem hmem] at hu
  have hsph : ∫⁻ ω, G (ω : E (m + 1)) ∂(sphereMeasure (m + 1)) =
      ∫⁻ ω, ‖F ω‖ₑ ^ p ∂(sphereMeasure (m + 1)) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with ω hω
    simp only [G, hFh_apply, hω]
  rw [← hsph]
  calc ∫⁻ u in closedBall (0 : E m) 1, ‖F (nuS u)‖ₑ ^ p
      = ∫⁻ u in closedBall (0 : E m) 1, G (nu u) := by
        apply lintegral_congr_ae
        filter_upwards [hgood] with u hu
        have hωB : nuS u ∉ B := fun h => hu (Set.mem_image_of_mem _ h)
        have hωS : F (nuS u) = F₀ (nuS u) := by
          by_contra h; exact hωB (hSB h)
        show _ = ‖Fh ((nuS u : sphere (0 : E (m + 1)) 1) : E (m + 1))‖ₑ ^ p
        rw [hFh_apply, hωS]
    _ ≤ _ := gnomonic hm G hG

end Gnomonic


/-! ## Tools copied from Part N2K -/

section Tools

theorem isTest_integrable {k : ℕ} {p : ℝ} (hp : 1 ≤ p) {f : E k → ℝ} (hf : IsTest p f) :
    Integrable f := by
  obtain ⟨hm, hb⟩ := hf
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hfin : volume (closedBall (0 : E k) R) < ∞ := measure_closedBall_lt_top
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E k) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have : IntegrableOn f (closedBall 0 R) := (hm.restrict (closedBall (0 : E k) R)).integrable hp'
  exact (integrableOn_iff_integrable_of_support_subset hR).1 this

theorem isClosed_tube {k : ℕ} (δ : ℝ) (ω c : E k) : IsClosed (tube δ ω c) := by
  have h1 : Continuous fun x : E k => ⟪x - c, ω⟫ := by fun_prop
  have h2 : Continuous fun x : E k => ‖x - c - ⟪x - c, ω⟫ • ω‖ := by fun_prop
  exact (isClosed_le (continuous_abs.comp h1) continuous_const).inter
    (isClosed_le h2 continuous_const)

theorem measurableSet_tube {k : ℕ} (δ : ℝ) (ω c : E k) : MeasurableSet (tube δ ω c) :=
  (isClosed_tube δ ω c).measurableSet

theorem kakeyaMaximal_nonneg {k : ℕ} {δ : ℝ} {f : E k → ℝ} (hf : ∀ x, 0 ≤ f x)
    (ω : sphere (0 : E k) 1) : 0 ≤ kakeyaMaximal δ f ω :=
  Real.iSup_nonneg fun _ => mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (setIntegral_nonneg (measurableSet_tube _ _ _) fun y _ => hf y)

theorem kakeya_bddAbove {k : ℕ} (δ : ℝ) {g : E k → ℝ} (hg : Integrable g)
    (ω : sphere (0 : E k) 1) :
    BddAbove (Set.range fun c : E k =>
      (volume (tube δ (ω : E k) c)).toReal⁻¹ * ∫ y in tube δ (ω : E k) c, g y) := by
  have hω : ‖(ω : E k)‖ = 1 := by simp
  refine ⟨(volume (tube δ (ω : E k) 0)).toReal⁻¹ * ∫ y, |g y|, ?_⟩
  rintro _ ⟨c, rfl⟩
  dsimp only
  rw [volume_tube_eq δ (ω : E k) (ω : E k) c 0 hω hω]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ENNReal.toReal_nonneg)
  calc ∫ y in tube δ (ω : E k) c, g y ≤ ∫ y in tube δ (ω : E k) c, |g y| :=
        setIntegral_mono hg.integrableOn hg.abs.integrableOn (fun y => le_abs_self _)
    _ ≤ ∫ y, |g y| :=
        setIntegral_le_integral hg.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)

theorem eLpNorm_eq_rpow {α : Type*} [MeasurableSpace α] {p : ℝ} (hp : 1 ≤ p) {μ : Measure α}
    (g : α → ℝ) :
    eLpNorm g (ENNReal.ofReal p) μ = (∫⁻ x, ‖g x‖ₑ ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]

/-- Integral over a tube in the direction `ω` against the Kakeya maximal function. -/
theorem lintegral_tube_le {k : ℕ} {δ c₂ : ℝ} {g : E k → ℝ} (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) (ω : sphere (0 : E k) 1) (c : E k)
    (hpos : 0 < volume (tube δ (ω : E k) c))
    (hvol : volume (tube δ (ω : E k) c) ≤ ENNReal.ofReal c₂) :
    ∫⁻ z in tube δ (ω : E k) c, ENNReal.ofReal (g z) ≤
      ENNReal.ofReal (c₂ * kakeyaMaximal δ g ω) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrableOn
    (Filter.Eventually.of_forall fun z => hg0 z)]
  apply ENNReal.ofReal_le_ofReal
  have hne : volume (tube δ (ω : E k) c) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  set V := (volume (tube δ (ω : E k) c)).toReal
  have hV : 0 < V := ENNReal.toReal_pos hpos.ne' hne
  have hVc : V ≤ c₂ := by
    have : 0 ≤ c₂ := by
      by_contra h; push Not at h
      rw [ENNReal.ofReal_of_nonpos h.le, nonpos_iff_eq_zero] at hvol
      exact hpos.ne' hvol
    exact ENNReal.toReal_le_of_le_ofReal this hvol
  have hle : V⁻¹ * ∫ y in tube δ (ω : E k) c, g y ≤ kakeyaMaximal δ g ω :=
    le_ciSup (kakeya_bddAbove δ hg ω) c
  have hK0 := kakeyaMaximal_nonneg (δ := δ) hg0 ω
  calc ∫ y in tube δ (ω : E k) c, g y = V * (V⁻¹ * ∫ y in tube δ (ω : E k) c, g y) := by
        field_simp
    _ ≤ V * kakeyaMaximal δ g ω := by gcongr
    _ ≤ c₂ * kakeyaMaximal δ g ω := by gcongr

end Tools

/-! ## The comparison function `g = f ∘ φ` -/

section G

variable {m : ℕ}

/-- The support region `D_c = {c ≤ t, ‖y‖ ≤ 5}`. -/
def D (m : ℕ) (c : ℝ) : Set (E (m + 1)) := {y | c ≤ vert y ∧ ‖y‖ ≤ 5}

theorem measurableSet_D (c : ℝ) : MeasurableSet (D m c) :=
  (measurableSet_le measurable_const continuous_vert.measurable).inter
    (measurableSet_le measurable_norm measurable_const)

theorem phi_mem_D {c : ℝ} (hc : 0 < c) {z : E (m + 1)} (h : phi z ∈ D m c) :
    0 < vert z ∧ vert z ≤ c⁻¹ ∧ (vert z)⁻¹ ≤ 5 ∧ ‖z‖ ≤ 6 * c⁻¹ := by
  obtain ⟨h1, h2⟩ := h
  rw [vert_phi] at h1
  have hv : 0 < vert z := inv_pos.1 (hc.trans_le h1)
  have hv2 : vert z ≤ c⁻¹ := by rw [le_inv_comm₀ hc hv] at h1; exact h1
  have hv3 : (vert z)⁻¹ ≤ 5 := by
    have := abs_vert_le (phi z); rw [vert_phi] at this; linarith [le_abs_self (vert z)⁻¹]
  refine ⟨hv, hv2, hv3, ?_⟩
  have hh : ‖horiz z‖ ≤ 5 * c⁻¹ := by
    have h := (norm_horiz_le (phi z)).trans h2
    rw [horiz_phi, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hv),
      inv_mul_le_iff₀ hv] at h
    calc ‖horiz z‖ ≤ vert z * 5 := h
      _ ≤ c⁻¹ * 5 := by gcongr
      _ = 5 * c⁻¹ := by ring
  calc ‖z‖ ≤ ‖horiz z‖ + |vert z| := norm_le_horiz_add_vert z
    _ ≤ 5 * c⁻¹ + c⁻¹ := by rw [abs_of_pos hv]; linarith
    _ = 6 * c⁻¹ := by ring

/-- The `Lᵖ` bound (b) for `g = f ∘ φ`. -/
theorem lintegral_comp_phi_le {c : ℝ} (hc : 0 < c) (G : E (m + 1) → ℝ≥0∞) (hG : Measurable G)
    (hsupp : ∀ y, G y ≠ 0 → y ∈ D m c) :
    ∫⁻ z, G (phi z) ≤ ENNReal.ofReal (c⁻¹ ^ (m + 2)) * ∫⁻ y, G y := by
  calc ∫⁻ z, G (phi z) ≤ ∫⁻ z, ENNReal.ofReal (c⁻¹ ^ (m + 2)) *
        {z : E (m + 1) | 0 < vert z}.indicator
          (fun z => ENNReal.ofReal ((vert z)⁻¹ ^ (m + 2)) * G (phi z)) z := by
        apply lintegral_mono; intro z; dsimp only
        by_cases hz : G (phi z) = 0
        · rw [hz]; exact zero_le
        obtain ⟨hv, hv2, -, -⟩ := phi_mem_D hc (hsupp _ hz)
        rw [indicator_of_mem (show z ∈ {z : E (m + 1) | 0 < vert z} from hv), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        have : 1 ≤ c⁻¹ ^ (m + 2) * (vert z)⁻¹ ^ (m + 2) := by
          rw [← mul_pow]
          apply one_le_pow₀
          rw [← mul_inv, one_le_inv₀ (by positivity)]
          calc c * vert z ≤ c * c⁻¹ := by gcongr
            _ = 1 := mul_inv_cancel₀ hc.ne'
        calc G (phi z) = 1 * G (phi z) := (one_mul _).symm
          _ ≤ _ := by
            gcongr
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal this
    _ = ENNReal.ofReal (c⁻¹ ^ (m + 2)) * ∫⁻ z, {z : E (m + 1) | 0 < vert z}.indicator
          (fun z => ENNReal.ofReal ((vert z)⁻¹ ^ (m + 2)) * G (phi z)) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (c⁻¹ ^ (m + 2)) * ∫⁻ y, {y : E (m + 1) | 0 < vert y}.indicator G y := by
        rw [cov G hG]
    _ ≤ ENNReal.ofReal (c⁻¹ ^ (m + 2)) * ∫⁻ y, G y := by
        gcongr with y; exact indicator_le_self _ _ y

/-- `g = f ∘ φ` is a test function. -/
theorem isTest_comp_phi {c p : ℝ} (hc : 0 < c) (hp : 1 ≤ p) {f : E (m + 1) → ℝ}
    (hfm : Measurable f) (hf : IsTest p f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : Function.support f ⊆ D m c) :
    IsTest p (fun z => f (phi z)) ∧
      ∫⁻ z, ENNReal.ofReal (f (phi z)) ^ p ≤
        ENNReal.ofReal (c⁻¹ ^ (m + 2)) * ∫⁻ y, ENNReal.ofReal (f y) ^ p := by
  have hp0 : 0 < p := by linarith
  have hgm : Measurable fun z => f (phi z) := hfm.comp measurable_phi
  have hb := lintegral_comp_phi_le hc (fun y => ENNReal.ofReal (f y) ^ p)
    (hfm.ennreal_ofReal.pow_const p) (by
      intro y hy
      apply hsupp
      intro h0; apply hy; simp [h0, ENNReal.zero_rpow_of_pos hp0])
  refine ⟨⟨⟨hgm.aestronglyMeasurable, ?_⟩, ?_⟩, hb⟩
  · rw [eLpNorm_eq_rpow hp]
    have hfin : ∫⁻ y, ‖f y‖ₑ ^ p < ∞ := by
      have := hf.1.2
      rw [eLpNorm_eq_rpow hp] at this
      exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 this
    apply ENNReal.rpow_lt_top_of_nonneg (by positivity)
    apply ne_top_of_le_ne_top _ (le_of_eq_of_le _ hb)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
        simp_rw [← Real.enorm_eq_ofReal (hf0 _)]; exact hfin.ne)
    · apply lintegral_congr; intro z; rw [Real.enorm_eq_ofReal (hf0 _)]
  · refine (isBounded_closedBall (x := (0 : E (m + 1))) (r := 6 * c⁻¹)).subset ?_
    intro z hz
    have := (phi_mem_D hc (hsupp hz)).2.2.2
    simpa using this

end G


/-! ## The pointwise bound and the assembly -/

section Main

variable {m : ℕ}

theorem measurableSet_piece {k : ℕ} (ε : ℝ) (x ω : E k) : MeasurableSet (piece ε x ω) := by
  have h1 : Measurable fun y : E k => ⟪y - x, ω⟫ := by fun_prop
  have h2 : Measurable fun y : E k => ‖y - x - ⟪y - x, ω⟫ • ω‖ := by fun_prop
  exact (measurableSet_lt measurable_const h1).inter
    ((measurableSet_lt h1 measurable_const).inter (measurableSet_lt h2 measurable_const))

/-- A far piece, pushed through `φ`, is covered by `Mn c` tubes in the direction `ν(u)`. -/
theorem lintegral_piece_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c / 2)
    (hΛε : Lam c * ε ≤ 3 / 8) {f : E (m + 1) → ℝ} (hfm : Measurable f)
    (hsupp : Function.support f ⊆ D m c) {u : E m} (hu : ‖u‖ ≤ 1) {ω : E (m + 1)}
    (hω : ‖ω‖ = 1) :
    ∫⁻ y in piece ε (mkPoint u 0) ω, ENNReal.ofReal (f y) ≤
      ENNReal.ofReal (5 ^ (m + 2)) * ∑ j ∈ Finset.range (Mn c),
        ∫⁻ z in tube (Lam c * ε) (nu u) (ctr u ω j), ENNReal.ofReal (f (phi z)) := by
  set P := piece ε (mkPoint u 0) ω
  set F : E (m + 1) → ℝ≥0∞ := fun y => ENNReal.ofReal (f y)
  have hFm : Measurable F := hfm.ennreal_ofReal
  have hPm : MeasurableSet P := measurableSet_piece _ _ _
  have hF0 : ∀ y, F y ≠ 0 → y ∈ D m c := by
    intro y hy; apply hsupp; intro h0; apply hy; simp [F, h0]
  set T : ℕ → Set (E (m + 1)) := fun j => tube (Lam c * ε) (nu u) (ctr u ω j)
  calc ∫⁻ y in P, F y = ∫⁻ y, P.indicator F y := (lintegral_indicator hPm _).symm
    _ = ∫⁻ y, {y : E (m + 1) | 0 < vert y}.indicator (P.indicator F) y := by
        apply lintegral_congr; intro y
        by_cases hy : 0 < vert y
        · rw [indicator_of_mem (show y ∈ {y : E (m + 1) | 0 < vert y} from hy)]
        · rw [indicator_of_notMem (show y ∉ {y : E (m + 1) | 0 < vert y} from hy)]
          by_contra hne
          have : F y ≠ 0 := by
            intro h0; apply hne; by_cases hyP : y ∈ P
            · rw [indicator_of_mem hyP, h0]
            · rw [indicator_of_notMem hyP]
          exact hy (lt_of_lt_of_le hc (hF0 y this).1)
    _ = ∫⁻ z, {z : E (m + 1) | 0 < vert z}.indicator
          (fun z => ENNReal.ofReal ((vert z)⁻¹ ^ (m + 2)) * P.indicator F (phi z)) z :=
        (cov _ (hFm.indicator hPm)).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (5 ^ (m + 2)) *
          ∑ j ∈ Finset.range (Mn c), (T j).indicator (fun z => ENNReal.ofReal (f (phi z))) z := by
        apply lintegral_mono; intro z; dsimp only
        by_cases hz : 0 < vert z
        swap
        · rw [indicator_of_notMem (show z ∉ {z : E (m + 1) | 0 < vert z} from hz)]
          exact zero_le
        rw [indicator_of_mem (show z ∈ {z : E (m + 1) | 0 < vert z} from hz)]
        by_cases hzP : phi z ∈ P
        swap
        · rw [indicator_of_notMem hzP, mul_zero]; exact zero_le
        rw [indicator_of_mem hzP]
        by_cases hF : F (phi z) = 0
        · rw [hF, mul_zero]; exact zero_le
        have hD := hF0 _ hF
        obtain ⟨-, -, hv5, -⟩ := phi_mem_D hc hD
        obtain ⟨j, hj, hjT⟩ := geom hc hε hεc hΛε hu hω hzP hD.1
        rw [phi_phi hz.ne'] at hjT
        have hle : (T j).indicator (fun z => ENNReal.ofReal (f (phi z))) z ≤
            ∑ j ∈ Finset.range (Mn c), (T j).indicator (fun z => ENNReal.ofReal (f (phi z))) z :=
          Finset.single_le_sum (f := fun j => (T j).indicator
            (fun z => ENNReal.ofReal (f (phi z))) z) (fun _ _ => zero_le)
            (Finset.mem_range.2 hj)
        rw [indicator_of_mem hjT] at hle
        gcongr
    _ = ENNReal.ofReal (5 ^ (m + 2)) * ∑ j ∈ Finset.range (Mn c),
          ∫⁻ z, (T j).indicator (fun z => ENNReal.ofReal (f (phi z))) z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro j _
        exact ((hfm.comp measurable_phi).ennreal_ofReal.indicator
          (measurableSet_tube _ _ _)).aemeasurable
    _ = _ := by
        congr 1; apply Finset.sum_congr rfl; intro j _
        exact lintegral_indicator (measurableSet_tube _ _ _) _

end Main


section Assembly

variable {m : ℕ}

/-- The pointwise bound `capMax ≲ ε^m g*(ν(u))`. -/
theorem capMax_le_kakeya {c ε c₁ c₂ : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c / 2)
    (hΛε : Lam c * ε ≤ 3 / 8) (hc₁ : 0 < c₁)
    (hvol : ∀ ω c' : E (m + 1), ‖ω‖ = 1 →
      ENNReal.ofReal (c₁ * (Lam c * ε) ^ m) ≤ volume (tube (Lam c * ε) ω c') ∧
      volume (tube (Lam c * ε) ω c') ≤ ENNReal.ofReal (c₂ * (Lam c * ε) ^ m))
    {f : E (m + 1) → ℝ} (hfm : Measurable f) (hsupp : Function.support f ⊆ D m c)
    (hgi : Integrable fun z => f (phi z)) (hg0 : ∀ z, 0 ≤ f (phi z)) {u : E m} (hu : ‖u‖ ≤ 1) :
    capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) (mkPoint u 0) ≤
      ENNReal.ofReal (5 ^ (m + 2) * (Mn c : ℝ) * (c₂ * (Lam c * ε) ^ m *
        kakeyaMaximal (Lam c * ε) (fun z => f (phi z)) (nuS u))) := by
  have hδ : 0 < Lam c * ε := mul_pos (Lam_pos hc) hε
  unfold capMax
  refine iSup₂_le fun ω hω => ?_
  have hω1 : ‖ω‖ = 1 := hω.1
  have htube : ∀ j, ∫⁻ z in tube (Lam c * ε) (nu u) (ctr u ω j), ENNReal.ofReal (f (phi z)) ≤
      ENNReal.ofReal (c₂ * (Lam c * ε) ^ m *
        kakeyaMaximal (Lam c * ε) (fun z => f (phi z)) (nuS u)) := by
    intro j
    have hn : ‖((nuS u : sphere (0 : E (m + 1)) 1) : E (m + 1))‖ = 1 := norm_nu u
    obtain ⟨hlo, hhi⟩ := hvol (nuS u) (ctr u ω j) hn
    have hpos : 0 < volume (tube (Lam c * ε) ((nuS u : sphere (0 : E (m + 1)) 1) : E (m + 1))
        (ctr u ω j)) := lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hlo
    exact lintegral_tube_le (g := fun z => f (phi z)) hgi hg0 (nuS u) (ctr u ω j) hpos hhi
  calc ∫⁻ y in piece ε (mkPoint u 0) ω, ENNReal.ofReal (f y)
      ≤ ENNReal.ofReal (5 ^ (m + 2)) * ∑ j ∈ Finset.range (Mn c),
        ∫⁻ z in tube (Lam c * ε) (nu u) (ctr u ω j), ENNReal.ofReal (f (phi z)) :=
        lintegral_piece_le hc hε hεc hΛε hfm hsupp hu hω1
    _ ≤ ENNReal.ofReal (5 ^ (m + 2)) * ∑ j ∈ Finset.range (Mn c),
        ENNReal.ofReal (c₂ * (Lam c * ε) ^ m *
          kakeyaMaximal (Lam c * ε) (fun z => f (phi z)) (nuS u)) := by
        gcongr with j; exact htube j
    _ = _ := by
        have hk := kakeyaMaximal_nonneg (δ := Lam c * ε) hg0 (nuS u)
        have hc₂ : 0 ≤ c₂ := by
          have h := hvol (nuS u) 0 (norm_nu u)
          by_contra hneg; push Not at hneg
          have h2 := h.1.trans h.2
          rw [ENNReal.ofReal_le_ofReal_iff'] at h2
          rcases h2 with h2 | h2
          · have : 0 < c₁ * (Lam c * ε) ^ m := by positivity
            have : c₂ * (Lam c * ε) ^ m < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
            linarith
          · have : 0 < c₁ * (Lam c * ε) ^ m := by positivity
            linarith
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

theorem const_algebra {a A k j p : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hj : 0 ≤ j)
    (hp : 0 < p) (I : ℝ≥0∞) :
    ENNReal.ofReal a ^ p * (ENNReal.ofReal k * (ENNReal.ofReal A ^ p * (ENNReal.ofReal j * I))) =
      ENNReal.ofReal (a * (k * j) ^ (1 / p) * A) ^ p * I := by
  have hkj : 0 ≤ k * j := mul_nonneg hk hj
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le (x := (k * j) ^ (1 / p)),
    ← Real.rpow_mul hkj, one_div_mul_cancel hp.ne', Real.rpow_one, ENNReal.ofReal_mul hk]
  ring

/-- The frozen estimate for a measurable `f`, with explicit constants. -/
theorem frozen_meas (hm : 1 ≤ m) {p : ℝ} (hp : 1 ≤ p) {c c₁ c₂ ε A : ℝ} (hc : 0 < c)
    (hc₁ : 0 < c₁)
    (hvol : ∀ ω c' : E (m + 1), ‖ω‖ = 1 →
      ENNReal.ofReal (c₁ * (Lam c * ε) ^ m) ≤ volume (tube (Lam c * ε) ω c') ∧
      volume (tube (Lam c * ε) ω c') ≤ ENNReal.ofReal (c₂ * (Lam c * ε) ^ m))
    (hε : 0 < ε) (hεc : ε ≤ c / 2) (hΛε : Lam c * ε ≤ 3 / 8)
    (hK : KBound (m + 1) p (Lam c * ε) A)
    {f : E (m + 1) → ℝ} (hfm : Measurable f) (hf : IsTest p f) (hf0 : ∀ x, 0 ≤ f x)
    (hsupp : Function.support f ⊆ D m c) :
    ∫⁻ u in closedBall (0 : E m) 1,
        capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) (mkPoint u 0) ^ p ≤
      ENNReal.ofReal (5 ^ (m + 2) * (Mn c : ℝ) * c₂ * Lam c ^ m * ε ^ m) ^ p *
        (ENNReal.ofReal (K2 m) * (ENNReal.ofReal A ^ p *
          (ENNReal.ofReal (c⁻¹ ^ (m + 2)) * ∫⁻ y, ENNReal.ofReal (f y) ^ p))) := by
  have hp0 : 0 < p := by linarith
  have hδ : 0 < Lam c * ε := mul_pos (Lam_pos hc) hε
  set g : E (m + 1) → ℝ := fun z => f (phi z) with hg
  obtain ⟨hgT, hgb⟩ := isTest_comp_phi hc hp hfm hf hf0 hsupp
  have hgi : Integrable g := isTest_integrable hp hgT
  have hg0 : ∀ z, 0 ≤ g z := fun z => hf0 _
  set gs := kakeyaMaximal (Lam c * ε) g
  set K1 := 5 ^ (m + 2) * (Mn c : ℝ) * c₂ * Lam c ^ m
  have hc₂ : 0 ≤ c₂ := by
    obtain ⟨e, he⟩ : ∃ e : E (m + 1), ‖e‖ = 1 :=
      ⟨EuclideanSpace.single 0 1, by simp⟩
    have h := (hvol e 0 he).1.trans (hvol e 0 he).2
    by_contra hneg; push Not at hneg
    rw [ENNReal.ofReal_le_ofReal_iff'] at h
    have : 0 < c₁ * (Lam c * ε) ^ m := by positivity
    rcases h with h | h
    · have : c₂ * (Lam c * ε) ^ m < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    · linarith
  have hK1 : 0 ≤ K1 * ε ^ m := by have := (Lam_pos hc).le; positivity
  have hpt : ∀ u ∈ closedBall (0 : E m) 1,
      capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) (mkPoint u 0) ^ p ≤
        ENNReal.ofReal (K1 * ε ^ m) ^ p * ‖gs (nuS u)‖ₑ ^ p := by
    intro u hu
    have hu1 : ‖u‖ ≤ 1 := by simpa using hu
    have h := capMax_le_kakeya hc hε hεc hΛε hc₁ hvol hfm hsupp hgi hg0 hu1
    have hgs0 : 0 ≤ gs (nuS u) := kakeyaMaximal_nonneg hg0 _
    have heq : 5 ^ (m + 2) * (Mn c : ℝ) * (c₂ * (Lam c * ε) ^ m *
        kakeyaMaximal (Lam c * ε) (fun z => f (phi z)) (nuS u)) =
        (K1 * ε ^ m) * gs (nuS u) := by
      simp only [K1, gs, hg, mul_pow]; ring
    rw [heq, ENNReal.ofReal_mul hK1, ← Real.enorm_eq_ofReal hgs0] at h
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    exact ENNReal.rpow_le_rpow h hp0.le
  have hsig : ∫⁻ ω, ‖gs ω‖ₑ ^ p ∂(sphereMeasure (m + 1)) ≤
      ENNReal.ofReal A ^ p * (ENNReal.ofReal (c⁻¹ ^ (m + 2)) *
        ∫⁻ y, ENNReal.ofReal (f y) ^ p) := by
    have hK' := hK g hgT hg0
    rw [eLpNorm_eq_rpow hp, eLpNorm_eq_rpow hp] at hK'
    have h := ENNReal.rpow_le_rpow hK' hp0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one] at h
    refine h.trans ?_
    gcongr
    calc ∫⁻ z, ‖g z‖ₑ ^ p = ∫⁻ z, ENNReal.ofReal (f (phi z)) ^ p := by
          apply lintegral_congr; intro z; rw [Real.enorm_eq_ofReal (hg0 z)]
      _ ≤ _ := hgb
  calc ∫⁻ u in closedBall (0 : E m) 1,
        capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) (mkPoint u 0) ^ p
      ≤ ∫⁻ u in closedBall (0 : E m) 1, ENNReal.ofReal (K1 * ε ^ m) ^ p * ‖gs (nuS u)‖ₑ ^ p :=
        setLIntegral_mono' measurableSet_closedBall hpt
    _ = ENNReal.ofReal (K1 * ε ^ m) ^ p * ∫⁻ u in closedBall (0 : E m) 1, ‖gs (nuS u)‖ₑ ^ p :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (K1 * ε ^ m) ^ p *
          (ENNReal.ofReal (K2 m) * ∫⁻ ω, ‖gs ω‖ₑ ^ p ∂(sphereMeasure (m + 1))) := by
        gcongr
        exact sphere_gnomonic hm gs (kakeyaMaximal_aestronglyMeasurable (by omega) hp hδ hgT)
    _ ≤ _ := by gcongr

end Assembly


/-- (Part B2) The frozen estimate: base points on the hyperplane `{x_n = 0}`, `|x̲| ≤ 1`, and
`f` supported above height `1/(8√n)` in the ball `B(0, 5)`. -/
theorem frozen_le (m : ℕ) (hm : 1 ≤ m) {p : ℝ} (hp : 1 ≤ p) : ∃ Λ K κ : ℝ, 0 < Λ ∧ 0 < K ∧ 0 < κ ∧
    ∀ ε, 0 < ε → ε ≤ κ → ∀ A : ℝ, 0 ≤ A → KBound (m + 1) p (Λ * ε) A →
    ∀ f : E (m + 1) → ℝ, IsTest p f → (∀ x, 0 ≤ f x) →
      Function.support f ⊆ {y | (8 * Real.sqrt (m + 1))⁻¹ ≤ vert y ∧ ‖y‖ ≤ 5} →
      ∫⁻ u in closedBall (0 : E m) 1,
          capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) (mkPoint u 0) ^ p ≤
        ENNReal.ofReal (K * ε ^ m * A) ^ p * ∫⁻ y, ENNReal.ofReal (f y) ^ p := by
  have hp0 : 0 < p := by linarith
  obtain ⟨c₁, c₂, hc₁, hc₂, hvol⟩ := tube_volume_bounds (m + 1) (by omega)
  set c : ℝ := (8 * Real.sqrt (m + 1))⁻¹ with hc_def
  have hc : 0 < c := by positivity
  set K1 := 5 ^ (m + 2) * (Mn c : ℝ) * c₂ * Lam c ^ m
  set J := K2 m * c⁻¹ ^ (m + 2)
  have hJ : 0 < J := mul_pos (K2_pos m) (by positivity)
  have hM : (0 : ℝ) < Mn c := by unfold Mn; positivity
  have hK1 : 0 < K1 :=
    mul_pos (mul_pos (mul_pos (by positivity) hM) hc₂) (pow_pos (Lam_pos hc) _)
  refine ⟨Lam c, K1 * J ^ (1 / p), min (c / 2) (3 / 8 / Lam c), Lam_pos hc,
    mul_pos hK1 (Real.rpow_pos_of_pos hJ _),
    lt_min (by positivity) (div_pos (by norm_num) (Lam_pos hc)), ?_⟩
  intro ε hε hεκ A hA hKB f hf hf0 hsupp
  have hεc : ε ≤ c / 2 := hεκ.trans (min_le_left _ _)
  have hΛε : Lam c * ε ≤ 3 / 8 := by
    have h := hεκ.trans (min_le_right _ _)
    rw [le_div_iff₀ (Lam_pos hc)] at h; linarith
  have hδ : 0 < Lam c * ε := mul_pos (Lam_pos hc) hε
  have hvol' : ∀ ω c' : E (m + 1), ‖ω‖ = 1 →
      ENNReal.ofReal (c₁ * (Lam c * ε) ^ m) ≤ volume (tube (Lam c * ε) ω c') ∧
      volume (tube (Lam c * ε) ω c') ≤ ENNReal.ofReal (c₂ * (Lam c * ε) ^ m) := by
    intro ω c' hω
    have := hvol (Lam c * ε) hδ (by linarith) ω c' hω
    simpa using this
  -- a measurable representative supported in `D`
  have hsupp' : Function.support f ⊆ D m c := hsupp
  have hfa := hf.1.1
  set f₀ : E (m + 1) → ℝ := (D m c).indicator (fun y => max (hfa.mk f y) 0) with hf₀
  have hf₀m : Measurable f₀ :=
    (hfa.stronglyMeasurable_mk.measurable.max measurable_const).indicator (measurableSet_D c)
  have hae : f =ᵐ[volume] f₀ := by
    filter_upwards [hfa.ae_eq_mk] with y hy
    by_cases hyD : y ∈ D m c
    · rw [hf₀, indicator_of_mem hyD, ← hy, max_eq_left (hf0 y)]
    · rw [hf₀, indicator_of_notMem hyD]
      by_contra hne; exact hyD (hsupp' hne)
  have hf₀0 : ∀ y, 0 ≤ f₀ y := by
    intro y; rw [hf₀]; by_cases hyD : y ∈ D m c
    · rw [indicator_of_mem hyD]; exact le_max_right _ _
    · rw [indicator_of_notMem hyD]
  have hsupp₀ : Function.support f₀ ⊆ D m c := Set.support_indicator_subset
  have hf₀T : IsTest p f₀ := by
    refine ⟨hf.1.ae_eq hae, ?_⟩
    refine (isBounded_closedBall (x := (0 : E (m + 1))) (r := 5)).subset ?_
    intro y hy; have := (hsupp₀ hy).2; simpa using this
  have haeF : (fun y => ENNReal.ofReal (f y)) =ᵐ[volume] fun y => ENNReal.ofReal (f₀ y) := by
    filter_upwards [hae] with y hy; rw [hy]
  have hcap : ∀ u : E m, capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) (mkPoint u 0) =
      capMax (eLast m) ε (fun y => ENNReal.ofReal (f₀ y)) (mkPoint u 0) := by
    intro u; unfold capMax
    congr 1; ext ω; congr 1; ext _
    exact lintegral_congr_ae (ae_restrict_of_ae haeF)
  have hint : ∫⁻ y, ENNReal.ofReal (f y) ^ p = ∫⁻ y, ENNReal.ofReal (f₀ y) ^ p := by
    apply lintegral_congr_ae; filter_upwards [haeF] with y hy; rw [hy]
  simp_rw [hcap]
  rw [hint]
  refine (frozen_meas hm hp hc hc₁ hvol' hε hεc hΛε hKB hf₀m hf₀T hf₀0 hsupp₀).trans
    (le_of_eq ?_)
  have hring : K1 * J ^ (1 / p) * ε ^ m * A = (K1 * ε ^ m) * (K2 m * c⁻¹ ^ (m + 2)) ^ (1 / p) * A := by
    simp only [J]; ring
  rw [hring]
  exact const_algebra (by positivity) (K2_pos m).le (by positivity) hp0 _

end TaoBR.T410.K2N.PartB2

end S_PartB2

namespace TaoBR.T410.K2N
alias frozen_le := TaoBR.T410.K2N.PartB2.frozen_le
end TaoBR.T410.K2N

section S_PartB1b

open MeasureTheory Metric Set
open scoped ENNReal NNReal SchwartzMap

namespace TaoBR.T410.K2N.PartB1

open TaoBR.T410 TaoBR.T410.K2N Filter
open scoped RealInnerProductSpace Topology

theorem isOpen_piece {n : ℕ} (ε : ℝ) (x ω : E n) : IsOpen (piece ε x ω) := by
  have h1 : Continuous fun y : E n => ⟪y - x, ω⟫ := by fun_prop
  have h2 : Continuous fun y : E n => ‖y - x - ⟪y - x, ω⟫ • ω‖ := by fun_prop
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
    (isOpen_lt h2 continuous_const))

theorem measurableSet_piece {n : ℕ} (ε : ℝ) (x ω : E n) : MeasurableSet (piece ε x ω) :=
  (isOpen_piece ε x ω).measurableSet

/-! ### Measurability of `capMax` -/

/-- The integral over a piece, as a function of the base point, is measurable (Tonelli). -/
theorem measurable_pieceIntegral {n : ℕ} (ε : ℝ) (ω : E n) {g : E n → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => ∫⁻ y in piece ε x ω, g y := by
  set S : Set (E n × E n) := {q | q.2 ∈ piece ε q.1 ω}
  have hS : MeasurableSet S := by
    have h1 : Continuous fun q : E n × E n => ⟪q.2 - q.1, ω⟫ := by fun_prop
    have h2 : Continuous fun q : E n × E n => ‖q.2 - q.1 - ⟪q.2 - q.1, ω⟫ • ω‖ := by fun_prop
    exact ((isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
      (isOpen_lt h2 continuous_const))).measurableSet
  have : (fun x => ∫⁻ y in piece ε x ω, g y) =
      fun x => ∫⁻ y, S.indicator (fun q => g q.2) (x, y) := by
    funext x
    rw [← lintegral_indicator (measurableSet_piece ε x ω)]
    rfl
  rw [this]
  exact ((hg.comp measurable_snd).indicator hS).lintegral_prod_right'

theorem eventually_mem_piece {n : ℕ} {ε : ℝ} {x ω y : E n} (hy : y ∈ piece ε x ω) {u : ℕ → E n}
    (hu : Tendsto u atTop (𝓝 ω)) : ∀ᶠ k in atTop, y ∈ piece ε x (u k) := by
  have h1 : Continuous fun w : E n => ⟪y - x, w⟫ := by fun_prop
  have h2 : Continuous fun w : E n => ‖y - x - ⟪y - x, w⟫ • w‖ := by fun_prop
  have hU : IsOpen {w : E n | 1 / 4 < ⟪y - x, w⟫ ∧ ⟪y - x, w⟫ < 2 ∧
      ‖y - x - ⟪y - x, w⟫ • w‖ < ε} :=
    (isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
      (isOpen_lt h2 continuous_const))
  exact hu.eventually (hU.mem_nhds hy)

/-- Fatou: the integral over `piece ε x ω` is at most the supremum of the integrals over
`piece ε x (u k)` when `u k → ω` (the pieces are open in the direction). -/
theorem pieceIntegral_le_iSup {n : ℕ} {ε : ℝ} {x ω : E n} {g : E n → ℝ≥0∞} (hg : Measurable g)
    {u : ℕ → E n} (hu : Tendsto u atTop (𝓝 ω)) :
    ∫⁻ y in piece ε x ω, g y ≤ ⨆ k, ∫⁻ y in piece ε x (u k), g y := by
  rw [← lintegral_indicator (measurableSet_piece ε x ω)]
  simp_rw [← lintegral_indicator (measurableSet_piece ε x _)]
  calc ∫⁻ y, (piece ε x ω).indicator g y
      ≤ ∫⁻ y, liminf (fun k => (piece ε x (u k)).indicator g y) atTop := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ piece ε x ω
        · rw [indicator_of_mem hy]
          apply le_liminf_of_le (by isBoundedDefault)
          filter_upwards [eventually_mem_piece hy hu] with k hk
          rw [indicator_of_mem hk]
        · rw [indicator_of_notMem hy]; exact zero_le
    _ ≤ liminf (fun k => ∫⁻ y, (piece ε x (u k)).indicator g y) atTop :=
        lintegral_liminf_le fun k => hg.indicator (measurableSet_piece ε x (u k))
    _ ≤ ⨆ k, ∫⁻ y, (piece ε x (u k)).indicator g y :=
        (liminf_le_limsup).trans limsup_le_iSup

/-- Measurability of the cap far maximal function (copied from Part A). -/
theorem capMax_meas {n : ℕ} (e : E n) (ε : ℝ) (g : E n → ℝ≥0∞) (hg : Measurable g) :
    Measurable (capMax e ε g) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (capDirs e)
  set D' : Set (E n) := Subtype.val '' D
  have hD'c : D'.Countable := hDc.image _
  have hD'sub : D' ⊆ capDirs e := by rintro _ ⟨d, -, rfl⟩; exact d.2
  have hcl : capDirs e ⊆ closure D' := Subtype.dense_iff.1 hDd
  have heq : capMax e ε g = fun x => ⨆ d ∈ D', ∫⁻ y in piece ε x d, g y := by
    funext x
    unfold capMax
    apply le_antisymm
    · apply iSup₂_le
      intro ω hω
      obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 (hcl hω)
      refine (pieceIntegral_le_iSup hg hu).trans (iSup_le fun k => ?_)
      exact le_iSup₂ (f := fun d (_ : d ∈ D') => ∫⁻ y in piece ε x d, g y) (u k) (huD k)
    · exact iSup_le_iSup_of_subset hD'sub
  rw [heq]
  exact Measurable.biSup D' hD'c fun d _ => measurable_pieceIntegral ε d hg

/-! ### `Lᵖ` norms of `ℝ≥0∞`-valued functions -/


/-! ## Isometries -/

section Iso

variable {n : ℕ}

theorem mem_piece_map (U : E n ≃ₗᵢ[ℝ] E n) (ε : ℝ) (x ω y : E n) :
    y ∈ piece ε (U x) (U ω) ↔ U.symm y ∈ piece ε x ω := by
  have h1 : ⟪y - U x, U ω⟫ = ⟪U.symm y - x, ω⟫ := by
    rw [← U.symm.inner_map_map]; simp
  have h2 : ∀ t : ℝ, ‖y - U x - t • U ω‖ = ‖U.symm y - x - t • ω‖ := by
    intro t; rw [← U.symm.norm_map]; simp
  simp only [piece, mem_ofPred_eq, h1, h2]

theorem mem_capDirs_map (U : E n ≃ₗᵢ[ℝ] E n) (e ω : E n) :
    U ω ∈ capDirs (U e) ↔ ω ∈ capDirs e := by
  simp only [capDirs, mem_ofPred_eq, U.norm_map, U.inner_map_map]

theorem setLIntegral_piece_map (U : E n ≃ₗᵢ[ℝ] E n) (ε : ℝ) (x ω : E n) (G : E n → ℝ≥0∞) :
    ∫⁻ y in piece ε (U x) (U ω), G (U.symm y) = ∫⁻ y in piece ε x ω, G y := by
  have hs : piece ε (U x) (U ω) = U.symm ⁻¹' piece ε x ω := by
    ext y; exact mem_piece_map U ε x ω y
  rw [hs]
  exact U.symm.measurePreserving.setLIntegral_comp_preimage_emb
    U.symm.toHomeomorph.measurableEmbedding G _

theorem capMax_map (U : E n ≃ₗᵢ[ℝ] E n) (e : E n) (ε : ℝ) (G : E n → ℝ≥0∞) (x : E n) :
    capMax e ε G x = capMax (U e) ε (fun y => G (U.symm y)) (U x) := by
  unfold capMax
  apply le_antisymm
  · refine iSup₂_le fun ω hω => ?_
    rw [← setLIntegral_piece_map U ε x ω G]
    exact le_iSup₂ (f := fun ω' (_ : ω' ∈ capDirs (U e)) =>
      ∫⁻ y in piece ε (U x) ω', G (U.symm y)) (U ω) ((mem_capDirs_map U e ω).2 hω)
  · refine iSup₂_le fun ω' hω' => ?_
    obtain ⟨ω, rfl⟩ := U.surjective ω'
    rw [setLIntegral_piece_map U ε x ω G]
    exact le_iSup₂ (f := fun ω (_ : ω ∈ capDirs e) => ∫⁻ y in piece ε x ω, G y) ω
      ((mem_capDirs_map U e ω).1 hω')

theorem setLIntegral_piece_add (ε : ℝ) (x a ω : E n) (G : E n → ℝ≥0∞) :
    ∫⁻ y in piece ε (x + a) ω, G y = ∫⁻ y in piece ε x ω, G (y + a) := by
  have hs : piece ε x ω = (fun y => y + a) ⁻¹' piece ε (x + a) ω := by
    ext y; simp [piece, add_sub_add_right_eq_sub]
  rw [hs]
  exact ((measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight a) G _).symm

end Iso

/-! ## Localisation to the window above the base point -/

section Local

variable {m : ℕ}

theorem norm_mkPoint_le (u : E m) (t : ℝ) : ‖mkPoint u t‖ ≤ ‖u‖ + |t| := by
  simpa using norm_le_horiz_add_vert (mkPoint u t)

theorem norm_eLast : ‖eLast m‖ = 1 := by
  have h := norm_mkPoint_sq (0 : E m) 1
  norm_num at h
  rcases h with h | h
  · exact h
  · linarith [norm_nonneg (mkPoint (0 : E m) 1)]

/-- The window `{1/(8√n) ≤ vert y, ‖y‖ ≤ 5}` of `frozen_le`. -/
def Dw (m : ℕ) : Set (E (m + 1)) := {y | (8 * Real.sqrt (m + 1))⁻¹ ≤ vert y ∧ ‖y‖ ≤ 5}

theorem measurableSet_Dw : MeasurableSet (Dw m) :=
  ((isClosed_le continuous_const continuous_vert).inter
    (isClosed_le continuous_norm continuous_const)).measurableSet

theorem Dw_subset : Dw m ⊆ closedBall 0 5 := by
  intro y hy; simpa using hy.2

theorem mem_Dw_of_mem_piece {ε : ℝ} (hε : ε ≤ (8 * Real.sqrt (m + 1))⁻¹) {v : E m}
    (hv : ‖v‖ ≤ 1) {ω y : E (m + 1)} (hω : ω ∈ capDirs (eLast m))
    (hy : y ∈ piece ε (mkPoint v 0) ω) : y ∈ Dw m := by
  obtain ⟨hω1, hω2⟩ := hω
  obtain ⟨ht1, ht2, hw⟩ := hy
  set x := mkPoint v 0 with hx
  set t := ⟪y - x, ω⟫ with ht
  set w := y - x - t • ω with hw_def
  have hyx : y = x + t • ω + w := by rw [hw_def]; abel
  have hω2' : (Real.sqrt (m + 1))⁻¹ ≤ vert ω := by
    have := hω2; rw [inner_eLast] at this; push_cast at this; exact this
  set s := Real.sqrt (m + 1) with hs_def
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hs0 : 0 < s := by linarith
  have hca : (8 * s)⁻¹ = s⁻¹ / 8 := by rw [mul_inv]; ring
  have hsi : 0 < s⁻¹ := inv_pos.2 hs0
  have hsi1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hvw : |vert w| ≤ ‖w‖ := abs_vert_le w
  have hvy : vert y = t * vert ω + vert w := by
    rw [hyx]; simp [hx]
  have hxn : ‖x‖ ≤ 1 := by
    have := norm_mkPoint_le v 0; simp at this; linarith
  have hny : ‖y‖ ≤ ‖x‖ + |t| * ‖ω‖ + ‖w‖ := by
    rw [hyx]
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  rw [hω1] at hny
  have hta : |t| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · rw [hvy, hca]
    rw [hca] at hε
    have : vert ω / 4 ≤ t * vert ω := by nlinarith
    have := abs_le.1 hvw
    nlinarith
  · rw [hca] at hε
    nlinarith

theorem capMax_shift_le {ε : ℝ} (hε : ε ≤ (8 * Real.sqrt (m + 1))⁻¹) (G : E (m + 1) → ℝ≥0∞)
    {v : E m} (hv : ‖v‖ ≤ 1) (z : E m) (h : ℝ) :
    capMax (eLast m) ε G (mkPoint (v + z) h) ≤
      capMax (eLast m) ε ((Dw m).indicator fun y => G (y + mkPoint z h)) (mkPoint v 0) := by
  have hx : mkPoint (v + z) h = mkPoint v 0 + mkPoint z h := ext_hv (by simp) (by simp)
  rw [hx]
  unfold capMax
  refine iSup₂_le fun ω hω => ?_
  rw [setLIntegral_piece_add]
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun ω (_ : ω ∈ capDirs (eLast m)) =>
      ∫⁻ y in piece ε (mkPoint v 0) ω, (Dw m).indicator (fun y => G (y + mkPoint z h)) y) ω hω)
  refine setLIntegral_congr_fun (measurableSet_piece ε _ ω) fun y hy => ?_
  rw [indicator_of_mem (mem_Dw_of_mem_piece hε hv hω hy)]

end Local

/-! ## Freezing the height and averaging over unit balls -/

section Main

variable {m : ℕ}

/-- The localised translate `1_D · f(· + a)`. -/
noncomputable def fa (f : E (m + 1) → ℝ) (a : E (m + 1)) : E (m + 1) → ℝ :=
  (Dw m).indicator fun y => f (y + a)

theorem isTest_fa {p : ℝ} {f : E (m + 1) → ℝ} (hf : IsTest p f) (a : E (m + 1)) :
    IsTest p (fa f a) := by
  refine ⟨(hf.1.comp_measurePreserving (measurePreserving_add_right volume a)).indicator
    measurableSet_Dw, ?_⟩
  refine (isBounded_closedBall (x := (0 : E (m + 1))) (r := 5)).subset ?_
  intro y hy
  exact Dw_subset (support_indicator_subset hy)

theorem fa_nonneg {f : E (m + 1) → ℝ} (hf0 : ∀ x, 0 ≤ f x) (a y : E (m + 1)) : 0 ≤ fa f a y := by
  unfold fa; by_cases hy : y ∈ Dw m
  · rw [indicator_of_mem hy]; exact hf0 _
  · rw [indicator_of_notMem hy]

theorem ofReal_fa (f : E (m + 1) → ℝ) (a : E (m + 1)) :
    (fun y => ENNReal.ofReal (fa f a y)) =
      (Dw m).indicator fun y => ENNReal.ofReal (f (y + a)) := by
  funext y; unfold fa; by_cases hy : y ∈ Dw m
  · rw [indicator_of_mem hy, indicator_of_mem hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero]

theorem lintegral_fa_rpow {p : ℝ} (hp : 0 < p) (f : E (m + 1) → ℝ) (a : E (m + 1)) :
    ∫⁻ y, ENNReal.ofReal (fa f a y) ^ p =
      ∫⁻ y, (Dw m).indicator (fun y => ENNReal.ofReal (f (y + a)) ^ p) y := by
  congr 1; funext y; unfold fa; by_cases hy : y ∈ Dw m
  · rw [indicator_of_mem hy, indicator_of_mem hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos hp]

theorem measurable_Psi {p : ℝ} {F : E (m + 1) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun a : E (m + 1) => ∫⁻ y, (Dw m).indicator (fun y => F (y + a) ^ p) y := by
  have h : (Function.uncurry fun (a y : E (m + 1)) => (Dw m).indicator (fun y => F (y + a) ^ p) y)
      = (Prod.snd ⁻¹' Dw m).indicator fun q : E (m + 1) × E (m + 1) => F (q.2 + q.1) ^ p := by
    funext q; by_cases hq : q.2 ∈ Dw m
    · simp [Function.uncurry, hq]
    · simp [Function.uncurry, hq]
  have hm : Measurable (Function.uncurry fun (a y : E (m + 1)) =>
      (Dw m).indicator (fun y => F (y + a) ^ p) y) := by
    rw [h]
    exact ((hF.comp (measurable_snd.add measurable_fst)).pow_const p).indicator
      (measurableSet_Dw.preimage measurable_snd)
  exact hm.lintegral_prod_right'

/-- The integral of the localised translates over all translations. -/
theorem lintegral_Psi {p : ℝ} {F : E (m + 1) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ a, ∫⁻ y, (Dw m).indicator (fun y => F (y + a) ^ p) y =
      volume (Dw m) * ∫⁻ y, F y ^ p := by
  have hm : AEMeasurable (Function.uncurry fun (a y : E (m + 1)) =>
      (Dw m).indicator (fun y => F (y + a) ^ p) y) (volume.prod volume) := by
    have h : (Function.uncurry fun (a y : E (m + 1)) =>
        (Dw m).indicator (fun y => F (y + a) ^ p) y)
        = (Prod.snd ⁻¹' Dw m).indicator fun q : E (m + 1) × E (m + 1) => F (q.2 + q.1) ^ p := by
      funext q; by_cases hq : q.2 ∈ Dw m
      · simp [Function.uncurry, hq]
      · simp [Function.uncurry, hq]
    rw [h]
    exact (((hF.comp (measurable_snd.add measurable_fst)).pow_const p).indicator
      (measurableSet_Dw.preimage measurable_snd)).aemeasurable
  rw [lintegral_lintegral_swap hm]
  have e : ∀ y : E (m + 1), ∫⁻ a, (Dw m).indicator (fun y => F (y + a) ^ p) y =
      (Dw m).indicator (fun _ => ∫⁻ y, F y ^ p) y := by
    intro y; by_cases hy : y ∈ Dw m
    · simp only [indicator_of_mem hy]
      simp_rw [add_comm y]
      exact lintegral_add_right_eq_self (fun a => F a ^ p) y
    · simp [indicator_of_notMem hy]
  simp_rw [e]
  rw [lintegral_indicator_const measurableSet_Dw, mul_comm]

/-- The main estimate for `e = eLast m` and measurable `f`. -/
theorem capMax_eLast_le {p : ℝ} (hp : 0 < p) {ε : ℝ} (hεc : ε ≤ (8 * Real.sqrt (m + 1))⁻¹)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {f : E (m + 1) → ℝ} (hf : IsTest p f) (hf0 : ∀ x, 0 ≤ f x)
    (hfm : Measurable f)
    (hfr : ∀ g : E (m + 1) → ℝ, IsTest p g → (∀ x, 0 ≤ g x) → Function.support g ⊆ Dw m →
      ∫⁻ u in closedBall (0 : E m) 1,
          capMax (eLast m) ε (fun y => ENNReal.ofReal (g y)) (mkPoint u 0) ^ p ≤
        C * ∫⁻ y, ENNReal.ofReal (g y) ^ p) :
    ∫⁻ x, capMax (eLast m) ε (fun y => ENNReal.ofReal (f y)) x ^ p ≤
      (volume (closedBall (0 : E m) 1))⁻¹ * C *
        (volume (Dw m) * ∫⁻ y, ENNReal.ofReal (f y) ^ p) := by
  set F : E (m + 1) → ℝ≥0∞ := fun y => ENNReal.ofReal (f y) with hF_def
  have hF : Measurable F := hfm.ennreal_ofReal
  set β := volume (closedBall (0 : E m) 1) with hβ_def
  have hβ0 : β ≠ 0 := (measure_closedBall_pos volume (0 : E m) one_pos).ne'
  have hβt : β ≠ ⊤ := measure_closedBall_lt_top.ne
  set Φ : E (m + 1) → ℝ≥0∞ := fun x => capMax (eLast m) ε F x ^ p with hΦ_def
  have hΦ : Measurable Φ := (capMax_meas _ _ _ hF).pow_const p
  set Ψ : E (m + 1) → ℝ≥0∞ := fun a => ∫⁻ y, (Dw m).indicator (fun y => F (y + a) ^ p) y
    with hΨ_def
  have hΨ : Measurable Ψ := measurable_Psi hF
  -- the frozen estimate for each translate
  have hz : ∀ (z : E m) (h : ℝ),
      ∫⁻ v in closedBall (0 : E m) 1, Φ (mkPoint (v + z) h) ≤ C * Ψ (mkPoint z h) := by
    intro z h
    set a := mkPoint z h
    have h1 := hfr (fa f a) (isTest_fa hf a) (fa_nonneg hf0 a) support_indicator_subset
    rw [lintegral_fa_rpow hp, ofReal_fa] at h1
    refine le_trans ?_ h1
    refine setLIntegral_mono' measurableSet_closedBall fun v hv => ?_
    have hv' : ‖v‖ ≤ 1 := by simpa using hv
    exact ENNReal.rpow_le_rpow (capMax_shift_le hεc F hv' z h) hp.le
  -- averaging over unit balls, for a fixed height
  have hh : ∀ h : ℝ, ∫⁻ u, Φ (mkPoint u h) ≤ β⁻¹ * ∫⁻ z, C * Ψ (mkPoint z h) := by
    intro h
    set B : E m → ℝ≥0∞ := (closedBall (0 : E m) 1).indicator 1 with hB_def
    have hB : Measurable B := measurable_one.indicator measurableSet_closedBall
    have hΦh : Measurable fun u : E m => Φ (mkPoint u h) :=
      hΦ.comp (measurable_mkPoint.comp (measurable_id.prodMk measurable_const))
    have hball : ∀ u : E m, ∫⁻ z, B (z - u) = β := by
      intro u
      rw [lintegral_sub_right_eq_self B u, hB_def, lintegral_indicator_one measurableSet_closedBall]
    calc ∫⁻ u, Φ (mkPoint u h)
        = β⁻¹ * ∫⁻ u, ∫⁻ z, B (z - u) * Φ (mkPoint u h) := by
          rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hβ0)]
          congr 1; funext u
          rw [lintegral_mul_const (f := fun z => B (z - u)) _
              (hB.comp (measurable_id.sub measurable_const)), hball,
            ← mul_assoc, ENNReal.inv_mul_cancel hβ0 hβt, one_mul]
      _ = β⁻¹ * ∫⁻ z, ∫⁻ u, B (z - u) * Φ (mkPoint u h) := by
          congr 1
          refine lintegral_lintegral_swap ?_
          exact ((hB.comp (measurable_snd.sub measurable_fst)).mul
            (hΦh.comp measurable_fst)).aemeasurable
      _ ≤ β⁻¹ * ∫⁻ z, C * Ψ (mkPoint z h) := by
          gcongr with z
          rw [← lintegral_add_right_eq_self _ z]
          have e : ∀ v : E m, B (z - (v + z)) * Φ (mkPoint (v + z) h) =
              (closedBall (0 : E m) 1).indicator (fun v => Φ (mkPoint (v + z) h)) v := by
            intro v
            by_cases hv : v ∈ closedBall (0 : E m) 1
            · have hv' : z - (v + z) ∈ closedBall (0 : E m) 1 := by
                simpa [sub_add_cancel_right, norm_neg] using hv
              rw [hB_def, indicator_of_mem hv', indicator_of_mem hv]; simp
            · have hv' : z - (v + z) ∉ closedBall (0 : E m) 1 := by
                simpa [sub_add_cancel_right, norm_neg] using hv
              rw [hB_def, indicator_of_notMem hv', indicator_of_notMem hv]; simp
          simp_rw [e]
          rw [lintegral_indicator measurableSet_closedBall]
          exact hz z h
  have hCt : β⁻¹ * C ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hβ0) hC
  calc ∫⁻ x, Φ x = ∫⁻ u, ∫⁻ h, Φ (mkPoint u h) := lintegral_mkPoint m Φ hΦ
    _ = ∫⁻ h, ∫⁻ u, Φ (mkPoint u h) :=
        lintegral_lintegral_swap (hΦ.comp measurable_mkPoint).aemeasurable
    _ ≤ ∫⁻ h, β⁻¹ * ∫⁻ z, C * Ψ (mkPoint z h) := lintegral_mono hh
    _ = β⁻¹ * C * ∫⁻ h, ∫⁻ z, Ψ (mkPoint z h) := by
        rw [← lintegral_const_mul' _ _ hCt]
        congr 1; funext h
        rw [lintegral_const_mul' _ _ hC, mul_assoc]
    _ = β⁻¹ * C * ∫⁻ z, ∫⁻ h, Ψ (mkPoint z h) := by
        congr 1
        exact lintegral_lintegral_swap
          ((hΨ.comp measurable_mkPoint).comp measurable_swap).aemeasurable
    _ = β⁻¹ * C * (volume (Dw m) * ∫⁻ y, F y ^ p) := by
        rw [← lintegral_mkPoint m Ψ hΨ, hΨ_def, lintegral_Psi hF]

end Main

/-! ## The cap estimate -/

section Final

variable {n : ℕ}

/-- (Part B1) The cap estimate on all of `ℝⁿ`, any unit axis `e`. -/
theorem capMax_le (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) : ∃ Λ K κ : ℝ, 0 < Λ ∧ 0 < K ∧ 0 < κ ∧
    ∀ e : E n, ‖e‖ = 1 → ∀ ε, 0 < ε → ε ≤ κ → ∀ A : ℝ, 0 ≤ A → KBound n p (Λ * ε) A →
    ∀ f : E n → ℝ, IsTest p f → (∀ x, 0 ≤ f x) →
      ∫⁻ x, capMax e ε (fun y => ENNReal.ofReal (f y)) x ^ p ≤
        ENNReal.ofReal (K * ε ^ (n - 1) * A) ^ p * ∫⁻ y, ENNReal.ofReal (f y) ^ p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hp0 : 0 < p := by linarith
  obtain ⟨Λ, K, κ, hΛ, hK, hκ, hfrozen⟩ := frozen_le m hm hp
  set c : ℝ := (8 * Real.sqrt (m + 1))⁻¹ with hc_def
  have hc : 0 < c := by positivity
  set β := volume (closedBall (0 : E m) 1) with hβ_def
  set V := volume (Dw m) with hV_def
  have hβ0 : β ≠ 0 := (measure_closedBall_pos volume (0 : E m) one_pos).ne'
  have hVt : V ≠ ⊤ := ((measure_mono Dw_subset).trans_lt measure_closedBall_lt_top).ne
  set γ : ℝ := (β⁻¹ * V).toReal + 1 with hγ_def
  have hγ : 0 < γ := by positivity
  have hγle : β⁻¹ * V ≤ ENNReal.ofReal γ := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hβ0) hVt)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨Λ, K * γ ^ (1 / p), min κ c, hΛ, by positivity, lt_min hκ hc, ?_⟩
  intro e he ε hε hεκ A hA hKB f hf hf0
  simp only [Nat.add_sub_cancel]
  have hεκ' : ε ≤ κ := hεκ.trans (min_le_left _ _)
  have hεc : ε ≤ c := hεκ.trans (min_le_right _ _)
  set C : ℝ≥0∞ := ENNReal.ofReal (K * ε ^ m * A) ^ p with hC_def
  have hCt : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  -- a measurable representative with bounded support
  obtain ⟨R, hR⟩ := hf.2.subset_closedBall 0
  have hfa := hf.1.1
  set f₀ : E (m + 1) → ℝ := (closedBall 0 R).indicator (fun y => max (hfa.mk f y) 0) with hf₀
  have hf₀m : Measurable f₀ :=
    (hfa.stronglyMeasurable_mk.measurable.max measurable_const).indicator measurableSet_closedBall
  have hae : f =ᵐ[volume] f₀ := by
    filter_upwards [hfa.ae_eq_mk] with y hy
    by_cases hyD : y ∈ closedBall (0 : E (m + 1)) R
    · rw [hf₀, indicator_of_mem hyD, ← hy, max_eq_left (hf0 y)]
    · rw [hf₀, indicator_of_notMem hyD]
      by_contra hne; exact hyD (hR hne)
  have hf₀0 : ∀ y, 0 ≤ f₀ y := by
    intro y; rw [hf₀]; by_cases hyD : y ∈ closedBall (0 : E (m + 1)) R
    · rw [indicator_of_mem hyD]; exact le_max_right _ _
    · rw [indicator_of_notMem hyD]
  have haeF : (fun y => ENNReal.ofReal (f y)) =ᵐ[volume] fun y => ENNReal.ofReal (f₀ y) := by
    filter_upwards [hae] with y hy; rw [hy]
  have hcap : ∀ x, capMax e ε (fun y => ENNReal.ofReal (f y)) x =
      capMax e ε (fun y => ENNReal.ofReal (f₀ y)) x := by
    intro x; unfold capMax
    congr 1; ext ω; congr 1; ext _
    exact lintegral_congr_ae (ae_restrict_of_ae haeF)
  have hint : ∫⁻ y, ENNReal.ofReal (f y) ^ p = ∫⁻ y, ENNReal.ofReal (f₀ y) ^ p := by
    apply lintegral_congr_ae; filter_upwards [haeF] with y hy; rw [hy]
  simp_rw [hcap]
  rw [hint]
  -- the isometry taking `e` to `eLast m`
  set U : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1) := Submodule.reflection (ℝ ∙ (e - eLast m))ᗮ with hU_def
  have hU : U e = eLast m := Submodule.reflection_sub (by rw [he, norm_eLast])
  set f₁ : E (m + 1) → ℝ := fun y => f₀ (U.symm y) with hf₁
  have hf₁m : Measurable f₁ := hf₀m.comp U.symm.continuous.measurable
  have hf₁T : IsTest p f₁ := by
    refine ⟨(hf.1.ae_eq hae).comp_measurePreserving U.symm.measurePreserving, ?_⟩
    refine (isBounded_closedBall (x := (0 : E (m + 1))) (r := R)).subset ?_
    intro y hy
    have h1 : U.symm y ∈ closedBall (0 : E (m + 1)) R := by
      by_contra hn'; exact hy (by simp [hf₁, hf₀, indicator_of_notMem hn'])
    simpa [U.symm.norm_map] using h1
  have hf₁0 : ∀ y, 0 ≤ f₁ y := fun y => hf₀0 _
  have h1 : ∫⁻ x, capMax e ε (fun y => ENNReal.ofReal (f₀ y)) x ^ p =
      ∫⁻ x, capMax (eLast m) ε (fun y => ENNReal.ofReal (f₁ y)) x ^ p := by
    simp_rw [capMax_map U e ε (fun y => ENNReal.ofReal (f₀ y)), hU]
    exact U.measurePreserving.lintegral_comp_emb U.toHomeomorph.measurableEmbedding
      (fun x => capMax (eLast m) ε (fun y => ENNReal.ofReal (f₁ y)) x ^ p)
  have h2 : ∫⁻ y, ENNReal.ofReal (f₁ y) ^ p = ∫⁻ y, ENNReal.ofReal (f₀ y) ^ p :=
    U.symm.measurePreserving.lintegral_comp_emb U.symm.toHomeomorph.measurableEmbedding
      (fun y => ENNReal.ofReal (f₀ y) ^ p)
  have hfr : ∀ g : E (m + 1) → ℝ, IsTest p g → (∀ x, 0 ≤ g x) → Function.support g ⊆ Dw m →
      ∫⁻ u in closedBall (0 : E m) 1,
          capMax (eLast m) ε (fun y => ENNReal.ofReal (g y)) (mkPoint u 0) ^ p ≤
        C * ∫⁻ y, ENNReal.ofReal (g y) ^ p :=
    fun g hg hg0 hgs => hfrozen ε hε hεκ' A hA hKB g hg hg0 hgs
  rw [h1, ← h2]
  refine (capMax_eLast_le hp0 hεc hCt hf₁T hf₁0 hf₁m hfr).trans ?_
  have halg : ENNReal.ofReal (K * γ ^ (1 / p) * ε ^ m * A) ^ p = ENNReal.ofReal γ * C := by
    have : K * γ ^ (1 / p) * ε ^ m * A = γ ^ (1 / p) * (K * ε ^ m * A) := by ring
    rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← Real.rpow_mul hγ.le,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  rw [halg]
  calc β⁻¹ * C * (V * ∫⁻ y, ENNReal.ofReal (f₁ y) ^ p)
      = (β⁻¹ * V) * C * ∫⁻ y, ENNReal.ofReal (f₁ y) ^ p := by ring
    _ ≤ ENNReal.ofReal γ * C * ∫⁻ y, ENNReal.ofReal (f₁ y) ^ p := by gcongr

end Final

end TaoBR.T410.K2N.PartB1

end S_PartB1b

namespace TaoBR.T410.K2N
alias capMax_le := TaoBR.T410.K2N.PartB1.capMax_le
end TaoBR.T410.K2N

section S_PartA

/-! # Theorem 4.10, Part K2N, Part A: `capMax_measurable` and `nikodym_of_kakeya` -/

open MeasureTheory Metric Set
open scoped ENNReal NNReal SchwartzMap



namespace TaoBR.T410.K2N.PartA

open TaoBR.T410 TaoBR.T410.K2N Filter
open scoped RealInnerProductSpace Topology

variable {n : ℕ}

/-! ### Basic facts about tubes and pieces -/

theorem isClosed_tube (δ : ℝ) (ω c : E n) : IsClosed (tube δ ω c) := by
  have h1 : Continuous fun x : E n => ⟪x - c, ω⟫ := by fun_prop
  have h2 : Continuous fun x : E n => ‖x - c - ⟪x - c, ω⟫ • ω‖ := by fun_prop
  exact (isClosed_le (continuous_abs.comp h1) continuous_const).inter
    (isClosed_le h2 continuous_const)

theorem measurableSet_tube (δ : ℝ) (ω c : E n) : MeasurableSet (tube δ ω c) :=
  (isClosed_tube δ ω c).measurableSet

theorem isTest_integrable {p : ℝ} (hp : 1 ≤ p) {f : E n → ℝ} (hf : IsTest p f) :
    Integrable f := by
  obtain ⟨hm, hb⟩ := hf
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hfin : volume (closedBall (0 : E n) R) < ∞ := measure_closedBall_lt_top
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E n) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have : IntegrableOn f (closedBall 0 R) := (hm.restrict (closedBall (0 : E n) R)).integrable hp'
  exact (integrableOn_iff_integrable_of_support_subset hR).1 this

theorem isOpen_piece (ε : ℝ) (x ω : E n) : IsOpen (piece ε x ω) := by
  have h1 : Continuous fun y : E n => ⟪y - x, ω⟫ := by fun_prop
  have h2 : Continuous fun y : E n => ‖y - x - ⟪y - x, ω⟫ • ω‖ := by fun_prop
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
    (isOpen_lt h2 continuous_const))

theorem measurableSet_piece (ε : ℝ) (x ω : E n) : MeasurableSet (piece ε x ω) :=
  (isOpen_piece ε x ω).measurableSet

/-! ### Measurability of `capMax` -/

/-- The integral over a piece, as a function of the base point, is measurable (Tonelli). -/
theorem measurable_pieceIntegral (ε : ℝ) (ω : E n) {g : E n → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => ∫⁻ y in piece ε x ω, g y := by
  set S : Set (E n × E n) := {q | q.2 ∈ piece ε q.1 ω}
  have hS : MeasurableSet S := by
    have h1 : Continuous fun q : E n × E n => ⟪q.2 - q.1, ω⟫ := by fun_prop
    have h2 : Continuous fun q : E n × E n => ‖q.2 - q.1 - ⟪q.2 - q.1, ω⟫ • ω‖ := by fun_prop
    exact ((isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
      (isOpen_lt h2 continuous_const))).measurableSet
  have : (fun x => ∫⁻ y in piece ε x ω, g y) =
      fun x => ∫⁻ y, S.indicator (fun q => g q.2) (x, y) := by
    funext x
    rw [← lintegral_indicator (measurableSet_piece ε x ω)]
    rfl
  rw [this]
  exact ((hg.comp measurable_snd).indicator hS).lintegral_prod_right'

theorem eventually_mem_piece {ε : ℝ} {x ω y : E n} (hy : y ∈ piece ε x ω) {u : ℕ → E n}
    (hu : Tendsto u atTop (𝓝 ω)) : ∀ᶠ k in atTop, y ∈ piece ε x (u k) := by
  have h1 : Continuous fun w : E n => ⟪y - x, w⟫ := by fun_prop
  have h2 : Continuous fun w : E n => ‖y - x - ⟪y - x, w⟫ • w‖ := by fun_prop
  have hU : IsOpen {w : E n | 1 / 4 < ⟪y - x, w⟫ ∧ ⟪y - x, w⟫ < 2 ∧
      ‖y - x - ⟪y - x, w⟫ • w‖ < ε} :=
    (isOpen_lt continuous_const h1).inter ((isOpen_lt h1 continuous_const).inter
      (isOpen_lt h2 continuous_const))
  exact hu.eventually (hU.mem_nhds hy)

/-- Fatou: the integral over `piece ε x ω` is at most the supremum of the integrals over
`piece ε x (u k)` when `u k → ω` (the pieces are open in the direction). -/
theorem pieceIntegral_le_iSup {ε : ℝ} {x ω : E n} {g : E n → ℝ≥0∞} (hg : Measurable g)
    {u : ℕ → E n} (hu : Tendsto u atTop (𝓝 ω)) :
    ∫⁻ y in piece ε x ω, g y ≤ ⨆ k, ∫⁻ y in piece ε x (u k), g y := by
  rw [← lintegral_indicator (measurableSet_piece ε x ω)]
  simp_rw [← lintegral_indicator (measurableSet_piece ε x _)]
  calc ∫⁻ y, (piece ε x ω).indicator g y
      ≤ ∫⁻ y, liminf (fun k => (piece ε x (u k)).indicator g y) atTop := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ piece ε x ω
        · rw [indicator_of_mem hy]
          apply le_liminf_of_le (by isBoundedDefault)
          filter_upwards [eventually_mem_piece hy hu] with k hk
          rw [indicator_of_mem hk]
        · rw [indicator_of_notMem hy]; exact zero_le
    _ ≤ liminf (fun k => ∫⁻ y, (piece ε x (u k)).indicator g y) atTop :=
        lintegral_liminf_le fun k => hg.indicator (measurableSet_piece ε x (u k))
    _ ≤ ⨆ k, ∫⁻ y, (piece ε x (u k)).indicator g y :=
        (liminf_le_limsup).trans limsup_le_iSup

/-- (Part A) Measurability of the cap far maximal function. -/
theorem capMax_measurable (e : E n) (ε : ℝ) (g : E n → ℝ≥0∞) (hg : Measurable g) :
    Measurable (capMax e ε g) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (capDirs e)
  set D' : Set (E n) := Subtype.val '' D
  have hD'c : D'.Countable := hDc.image _
  have hD'sub : D' ⊆ capDirs e := by rintro _ ⟨d, -, rfl⟩; exact d.2
  have hcl : capDirs e ⊆ closure D' := Subtype.dense_iff.1 hDd
  have heq : capMax e ε g = fun x => ⨆ d ∈ D', ∫⁻ y in piece ε x d, g y := by
    funext x
    unfold capMax
    apply le_antisymm
    · apply iSup₂_le
      intro ω hω
      obtain ⟨u, huD, hu⟩ := mem_closure_iff_seq_limit.1 (hcl hω)
      refine (pieceIntegral_le_iSup hg hu).trans (iSup_le fun k => ?_)
      exact le_iSup₂ (f := fun d (_ : d ∈ D') => ∫⁻ y in piece ε x d, g y) (u k) (huD k)
    · exact iSup_le_iSup_of_subset hD'sub
  rw [heq]
  exact Measurable.biSup D' hD'c fun d _ => measurable_pieceIntegral ε d hg

/-! ### `Lᵖ` norms of `ℝ≥0∞`-valued functions -/

/-- `(∫⁻ G^p)^{1/p}`. -/
noncomputable def lpn (p : ℝ) (G : E n → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ x, G x ^ p) ^ (1 / p)

theorem lpn_mono {p : ℝ} (hp : 0 < p) {G H : E n → ℝ≥0∞} (h : ∀ x, G x ≤ H x) :
    lpn p G ≤ lpn p H :=
  ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow (h x) hp.le) (by positivity)

theorem lpn_const_mul {p : ℝ} (hp : 0 < p) (c : ℝ≥0∞) (hc : c ≠ ⊤) (G : E n → ℝ≥0∞) :
    lpn p (fun x => c * G x) = c * lpn p G := by
  unfold lpn
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le hc),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne',
    ENNReal.rpow_one]

theorem lpn_add_le {p : ℝ} (hp : 1 ≤ p) {G H : E n → ℝ≥0∞} (hG : AEMeasurable G)
    (hH : AEMeasurable H) : lpn p (fun x => G x + H x) ≤ lpn p G + lpn p H :=
  ENNReal.lintegral_Lp_add_le hG hH hp

theorem lpn_sum_le {p : ℝ} (hp : 1 ≤ p) {ι : Type*} (s : Finset ι) (G : ι → E n → ℝ≥0∞)
    (hG : ∀ i ∈ s, AEMeasurable (G i)) :
    lpn p (fun x => ∑ i ∈ s, G i x) ≤ ∑ i ∈ s, lpn p (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hp0 : (0 : ℝ) < p := by linarith
    simp only [Finset.sum_empty, lpn, ENNReal.zero_rpow_of_pos hp0, lintegral_const, zero_mul]
    rw [ENNReal.zero_rpow_of_pos (by positivity)]
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    refine (lpn_add_le hp (hG a (Finset.mem_insert_self a s))
      (Finset.aemeasurable_fun_sum s fun i hi => hG i (Finset.mem_insert_of_mem hi))).trans ?_
    gcongr
    exact ih fun i hi => hG i (Finset.mem_insert_of_mem hi)

theorem rpow_le_of_le_mul_pow {X Y c : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (h : X ≤ c ^ p * Y) :
    X ^ (1 / p) ≤ c * Y ^ (1 / p) := by
  calc X ^ (1 / p) ≤ (c ^ p * Y) ^ (1 / p) := ENNReal.rpow_le_rpow h (by positivity)
    _ = c * Y ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem eLpNorm_eq_lpn {p : ℝ} (hp : 1 ≤ p) (g : E n → ℝ) :
    eLpNorm g (ENNReal.ofReal p) volume = lpn p (fun x => ‖g x‖ₑ) := by
  have hp0 : 0 < p := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  rfl

/-! ### Scaling -/

theorem map_smul_volume {r : ℝ} (hr : 0 < r) :
    Measure.map (fun y : E n => r⁻¹ • y) volume = ENNReal.ofReal (r ^ n) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), finrank_euclideanSpace_fin, inv_pow,
    inv_inv, abs_of_pos (pow_pos hr n)]

theorem lintegral_comp_inv_smul {r : ℝ} (hr : 0 < r) (G : E n → ℝ≥0∞) :
    ∫⁻ x, G (r⁻¹ • x) = ENNReal.ofReal (r ^ n) * ∫⁻ x, G x := by
  have h := lintegral_map_equiv G
    (MeasurableEquiv.smul₀ (α := E n) r⁻¹ (inv_ne_zero hr.ne')) (μ := volume)
  have hm : ⇑(MeasurableEquiv.smul₀ (α := E n) r⁻¹ (inv_ne_zero hr.ne')) =
      fun y : E n => r⁻¹ • y := rfl
  rw [hm, map_smul_volume hr, lintegral_smul_measure] at h
  exact h.symm

theorem lpn_comp_inv_smul {p : ℝ} (hp : 0 < p) {r : ℝ} (hr : 0 < r) (G : E n → ℝ≥0∞) :
    lpn p (fun x => G (r⁻¹ • x)) = ENNReal.ofReal ((r ^ n) ^ (1 / p)) * lpn p G := by
  unfold lpn
  rw [lintegral_comp_inv_smul hr (fun x => G x ^ p), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

/-- Rescaled function `F(r ·)`. -/
def Fr (r : ℝ) (F : E n → ℝ≥0∞) : E n → ℝ≥0∞ := fun z => F (r • z)

theorem lpn_Fr {p : ℝ} (hp : 0 < p) {r : ℝ} (hr : 0 < r) (F : E n → ℝ≥0∞) :
    lpn p (Fr r F) = ENNReal.ofReal (((r⁻¹) ^ n) ^ (1 / p)) * lpn p F := by
  have := lpn_comp_inv_smul hp (inv_pos.2 hr) F
  simp only [inv_inv] at this
  exact this

/-- The `Lᵖ` norm of a rescaled cap maximal function. -/
theorem lpn_capTerm {p : ℝ} (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) (e : E n) (ε : ℝ)
    (F : E n → ℝ≥0∞) {B : ℝ}
    (hB : ∫⁻ x, capMax e ε (Fr r F) x ^ p ≤ ENNReal.ofReal B ^ p * ∫⁻ y, Fr r F y ^ p) :
    lpn p (fun x => capMax e ε (Fr r F) (r⁻¹ • x)) ≤ ENNReal.ofReal B * lpn p F := by
  have hp0 : 0 < p := by linarith
  rw [lpn_comp_inv_smul hp0 hr]
  have h1 : lpn p (capMax e ε (Fr r F)) ≤ ENNReal.ofReal B * lpn p (Fr r F) :=
    rpow_le_of_le_mul_pow hp0 hB
  have h3 : (r ^ n) ^ (1 / p) * ((r⁻¹) ^ n) ^ (1 / p) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity), inv_pow,
      mul_inv_cancel₀ (by positivity), Real.one_rpow]
  calc ENNReal.ofReal ((r ^ n) ^ (1 / p)) * lpn p (capMax e ε (Fr r F))
      ≤ ENNReal.ofReal ((r ^ n) ^ (1 / p)) * (ENNReal.ofReal B *
          (ENNReal.ofReal (((r⁻¹) ^ n) ^ (1 / p)) * lpn p F)) := by
        rw [← lpn_Fr hp0 hr]; gcongr
    _ = ENNReal.ofReal B * (ENNReal.ofReal ((r ^ n) ^ (1 / p)) *
          ENNReal.ofReal (((r⁻¹) ^ n) ^ (1 / p))) * lpn p F := by ring
    _ = ENNReal.ofReal B * lpn p F := by
        rw [← ENNReal.ofReal_mul (by positivity), h3, ENNReal.ofReal_one, mul_one]

/-! ### Geometry of a tube through `x` -/

theorem inner_sub_eq (ω c x y : E n) : ⟪y - x, ω⟫ = ⟪y - c, ω⟫ - ⟪x - c, ω⟫ := by
  rw [← inner_sub_left]; congr 1; abel

theorem perp_sub_le {δ : ℝ} {ω c x y : E n} (hx : x ∈ tube δ ω c) (hy : y ∈ tube δ ω c) :
    ‖y - x - ⟪y - x, ω⟫ • ω‖ ≤ 2 * δ := by
  have e : y - x - ⟪y - x, ω⟫ • ω =
      (y - c - ⟪y - c, ω⟫ • ω) - (x - c - ⟪x - c, ω⟫ • ω) := by
    rw [inner_sub_eq ω c x y, sub_smul]; abel
  rw [e]
  calc _ ≤ ‖y - c - ⟪y - c, ω⟫ • ω‖ + ‖x - c - ⟪x - c, ω⟫ • ω‖ := norm_sub_le _ _
    _ ≤ δ + δ := add_le_add hy.2 hx.2
    _ = 2 * δ := by ring

theorem abs_inner_sub_le {δ : ℝ} {ω c x y : E n} (hx : x ∈ tube δ ω c) (hy : y ∈ tube δ ω c) :
    |⟪y - x, ω⟫| ≤ 1 := by
  rw [inner_sub_eq ω c x y]
  have h1 := abs_le.1 hy.1
  have h2 := abs_le.1 hx.1
  exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

theorem smul_mem_piece {δ r : ℝ} (hr : 0 < r) {x y s : E n}
    (h1 : r / 4 < ⟪y - x, s⟫) (h2 : ⟪y - x, s⟫ < 2 * r) (h3 : ‖y - x - ⟪y - x, s⟫ • s‖ < 3 * δ) :
    r⁻¹ • y ∈ piece (3 * δ / r) (r⁻¹ • x) s := by
  have e1 : r⁻¹ • y - r⁻¹ • x = r⁻¹ • (y - x) := (smul_sub _ _ _).symm
  have e2 : ⟪r⁻¹ • (y - x), s⟫ = r⁻¹ * ⟪y - x, s⟫ := real_inner_smul_left _ _ _
  refine ⟨?_, ?_, ?_⟩
  · show 1 / 4 < ⟪r⁻¹ • y - r⁻¹ • x, s⟫
    rw [e1, e2, inv_mul_eq_div, lt_div_iff₀ hr]; linarith
  · show ⟪r⁻¹ • y - r⁻¹ • x, s⟫ < 2
    rw [e1, e2, inv_mul_eq_div, div_lt_iff₀ hr]; linarith
  · show ‖r⁻¹ • y - r⁻¹ • x - ⟪r⁻¹ • y - r⁻¹ • x, s⟫ • s‖ < 3 * δ / r
    rw [e1, e2, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
      inv_mul_eq_div]
    exact div_lt_div_of_pos_right h3 hr

theorem exists_dyadic {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) {N : ℕ} (hN : (1 / 2 : ℝ) ^ N < u) :
    ∃ k < N, (1 / 2 : ℝ) ^ k / 4 < u ∧ u < 2 * (1 / 2 : ℝ) ^ k := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hu hu1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hpos : (0 : ℝ) < (1 / 2) ^ k := by positivity
  refine ⟨k, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) h
    linarith
  · rw [pow_succ] at hk1; linarith
  · linarith

/-- Every point of a tube through `x` is near `x` or, after rescaling by `2^k`, lies in a unit
far piece of width `3δ 2^k` in the direction `ω` or `-ω`. -/
theorem cover {δ : ℝ} (hδ : 0 < δ) {ω c x y : E n} (hω : ‖ω‖ = 1) (hx : x ∈ tube δ ω c)
    (hy : y ∈ tube δ ω c) (N : ℕ) :
    ‖y - x‖ ≤ (1 / 2 : ℝ) ^ N + 2 * δ ∨ ∃ k < N,
      (((1 / 2 : ℝ) ^ k)⁻¹ • y ∈ piece (3 * δ / (1 / 2) ^ k) (((1 / 2 : ℝ) ^ k)⁻¹ • x) ω ∨
        ((1 / 2 : ℝ) ^ k)⁻¹ • y ∈ piece (3 * δ / (1 / 2) ^ k) (((1 / 2 : ℝ) ^ k)⁻¹ • x) (-ω)) := by
  have hperp := perp_sub_le hx hy
  have ht1 := abs_inner_sub_le hx hy
  set t := ⟪y - x, ω⟫ with ht
  have hperp' : ‖y - x - t • ω‖ < 3 * δ := by linarith
  by_cases hsmall : |t| ≤ (1 / 2 : ℝ) ^ N
  · left
    have e : y - x = t • ω + (y - x - t • ω) := by abel
    calc ‖y - x‖ = ‖t • ω + (y - x - t • ω)‖ := by rw [← e]
      _ ≤ ‖t • ω‖ + ‖y - x - t • ω‖ := norm_add_le _ _
      _ ≤ (1 / 2) ^ N + 2 * δ := by
          rw [norm_smul, hω, mul_one, Real.norm_eq_abs]; linarith
  · right
    push Not at hsmall
    have hNpos : (0 : ℝ) < (1 / 2) ^ N := by positivity
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at hsmall ht1
      obtain ⟨k, hk, hk1, hk2⟩ := exists_dyadic (by linarith) ht1 hsmall
      exact ⟨k, hk, Or.inl (smul_mem_piece (by positivity) hk1 hk2 hperp')⟩
    · rw [abs_of_neg h0] at hsmall ht1
      obtain ⟨k, hk, hk1, hk2⟩ := exists_dyadic (by linarith) ht1 hsmall
      have e1 : ⟪y - x, -ω⟫ = -t := inner_neg_right _ _
      have e2 : y - x - ⟪y - x, -ω⟫ • (-ω) = y - x - t • ω := by rw [e1, neg_smul_neg]
      refine ⟨k, hk, Or.inr (smul_mem_piece (by positivity) ?_ ?_ ?_)⟩
      · rw [e1]; exact hk1
      · rw [e1]; exact hk2
      · rw [e2]; exact hperp'

/-! ### The `2n` caps -/

/-- The cap axes `±eᵢ`. -/
noncomputable def capVec (j : Fin n × Bool) : E n :=
  if j.2 then EuclideanSpace.single j.1 1 else -EuclideanSpace.single j.1 1

theorem norm_capVec (j : Fin n × Bool) : ‖capVec j‖ = 1 := by
  unfold capVec; split_ifs <;> simp

theorem exists_cap {ω : E n} (hω : ‖ω‖ = 1) :
    ∃ j j' : Fin n × Bool, ω ∈ capDirs (capVec j) ∧ -ω ∈ capDirs (capVec j') := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : ω = 0 := Subsingleton.elim _ _
      rw [this, norm_zero] at hω; norm_num at hω
    · exact h
  have hsum : ∑ i, ω i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hω, one_pow]
  obtain ⟨i, hi⟩ : ∃ i, (n : ℝ)⁻¹ ≤ ω i ^ 2 := by
    by_contra h
    push Not at h
    have : ∑ i, ω i ^ 2 < ∑ _i : Fin n, (n : ℝ)⁻¹ :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ => h i
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ (by positivity)] at this
    linarith
  have habs : (Real.sqrt n)⁻¹ ≤ |ω i| := by
    rw [← Real.sqrt_inv, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hi
  have hin : ∀ v : E n, ⟪v, EuclideanSpace.single i (1 : ℝ)⟫ = v i := by
    intro v; rw [EuclideanSpace.inner_single_right]; simp
  have hω' : ‖-ω‖ = 1 := by rw [norm_neg, hω]
  rcases le_or_gt 0 (ω i) with h | h
  · rw [abs_of_nonneg h] at habs
    refine ⟨(i, true), (i, false), ⟨hω, ?_⟩, ⟨hω', ?_⟩⟩
    · simp only [capVec, if_true]; rw [hin]; exact habs
    · simp only [capVec, Bool.false_eq_true, if_false, inner_neg_left, inner_neg_right, neg_neg]
      rw [hin]; exact habs
  · rw [abs_of_neg h] at habs
    refine ⟨(i, false), (i, true), ⟨hω, ?_⟩, ⟨hω', ?_⟩⟩
    · simp only [capVec, Bool.false_eq_true, if_false, inner_neg_right]
      rw [hin]; exact habs
    · simp only [capVec, if_true, inner_neg_left]
      rw [hin]; exact habs

/-! ### The pointwise bound -/

/-- The dyadic far term at scale `r`: the sum over the `2n` caps. -/
noncomputable def Phi (δ r : ℝ) (F : E n → ℝ≥0∞) (x : E n) : ℝ≥0∞ :=
  ∑ j : Fin n × Bool, capMax (capVec j) (3 * δ / r) (Fr r F) (r⁻¹ • x)

/-- The dominating function: a ball term plus the dyadic far terms. -/
noncomputable def RHS (δ R : ℝ) (N : ℕ) (F : E n → ℝ≥0∞) (x : E n) : ℝ≥0∞ :=
  (∫⁻ y in closedBall x R, F y) + ∑ k ∈ Finset.range N,
    2 * (ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ n) * Phi δ ((1 / 2 : ℝ) ^ k) F x)

theorem tube_lintegral_le {δ R : ℝ} (hδ : 0 < δ) {N : ℕ} (hR : (1 / 2 : ℝ) ^ N + 2 * δ ≤ R)
    {F : E n → ℝ≥0∞} (hF : Measurable F) {ω c x : E n} (hω : ‖ω‖ = 1) (hx : x ∈ tube δ ω c) :
    ∫⁻ y in tube δ ω c, F y ≤ RHS δ R N F x := by
  obtain ⟨j, j', hj, hj'⟩ := exists_cap hω
  set r : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k with hr
  have hrpos : ∀ k, 0 < r k := fun k => by simp only [hr]; positivity
  set h : ℕ → E n → E n → ℝ≥0∞ := fun k s y =>
    (piece (3 * δ / r k) ((r k)⁻¹ • x) s).indicator (Fr (r k) F) ((r k)⁻¹ • y) with hh
  have hhm : ∀ k s, Measurable (h k s) := fun k s =>
    ((hF.comp (measurable_const_smul (r k))).indicator (measurableSet_piece _ _ _)).comp
      (measurable_const_smul _)
  have hpt : ∀ y, (tube δ ω c).indicator F y ≤ (closedBall x R).indicator F y +
      ∑ k ∈ Finset.range N, (h k ω y + h k (-ω) y) := by
    intro y
    by_cases hy : y ∈ tube δ ω c
    · rw [indicator_of_mem hy]
      rcases cover hδ hω hx hy N with hb | ⟨k, hk, hk'⟩
      · have : y ∈ closedBall x R := by rw [mem_closedBall, dist_eq_norm]; linarith
        rw [indicator_of_mem this]; exact le_self_add
      · have hval : ∀ s, (r k)⁻¹ • y ∈ piece (3 * δ / r k) ((r k)⁻¹ • x) s → h k s y = F y := by
          intro s hs
          simp only [hh, indicator_of_mem hs, Fr, smul_smul, mul_inv_cancel₀ (hrpos k).ne',
            one_smul]
        refine le_trans ?_ le_add_self
        refine le_trans ?_ (Finset.single_le_sum (f := fun k => h k ω y + h k (-ω) y)
          (fun _ _ => zero_le) (Finset.mem_range.2 hk))
        rcases hk' with hs | hs
        · rw [hval ω hs]; exact le_self_add
        · rw [hval (-ω) hs]; exact le_add_self
    · rw [indicator_of_notMem hy]; exact zero_le
  have hterm : ∀ k (s : E n) (j : Fin n × Bool), s ∈ capDirs (capVec j) →
      ∫⁻ y, h k s y ≤ ENNReal.ofReal (r k ^ n) * Phi δ (r k) F x := by
    intro k s j hs
    simp only [hh]
    rw [lintegral_comp_inv_smul (hrpos k)
      (fun z => (piece (3 * δ / r k) ((r k)⁻¹ • x) s).indicator (Fr (r k) F) z),
      lintegral_indicator (measurableSet_piece _ _ _)]
    gcongr
    refine le_trans ?_ (Finset.single_le_sum (f := fun j =>
      capMax (capVec j) (3 * δ / r k) (Fr (r k) F) ((r k)⁻¹ • x)) (fun _ _ => zero_le)
      (Finset.mem_univ j))
    exact le_iSup₂ (f := fun ω (_ : ω ∈ capDirs (capVec j)) =>
      ∫⁻ y in piece (3 * δ / r k) ((r k)⁻¹ • x) ω, Fr (r k) F y) s hs
  calc ∫⁻ y in tube δ ω c, F y = ∫⁻ y, (tube δ ω c).indicator F y :=
        (lintegral_indicator (measurableSet_tube _ _ _) _).symm
    _ ≤ ∫⁻ y, ((closedBall x R).indicator F y +
          ∑ k ∈ Finset.range N, (h k ω y + h k (-ω) y)) := lintegral_mono hpt
    _ = (∫⁻ y in closedBall x R, F y) +
          ∑ k ∈ Finset.range N, ((∫⁻ y, h k ω y) + ∫⁻ y, h k (-ω) y) := by
        rw [lintegral_add_left (hF.indicator measurableSet_closedBall),
          lintegral_indicator measurableSet_closedBall,
          lintegral_finsetSum (Finset.range N) (f := fun k y => h k ω y + h k (-ω) y)
            (fun k _ => (hhm k ω).add (hhm k (-ω)))]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_add_left (hhm k ω) _
    _ ≤ RHS δ R N F x := by
        unfold RHS
        refine add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_)
        rw [two_mul]
        exact add_le_add (hterm k ω j hj) (hterm k (-ω) j' hj')

/-- The Nikodym maximal function is dominated by `|T|⁻¹ · RHS`. -/
theorem nikodym_le {δ R : ℝ} (hδ : 0 < δ) {N : ℕ} (hR : (1 / 2 : ℝ) ^ N + 2 * δ ≤ R)
    {a b : ℝ} (ha : 0 < a)
    (hvol : ∀ ω c : E n, ‖ω‖ = 1 → ENNReal.ofReal a ≤ volume (tube δ ω c) ∧
      volume (tube δ ω c) ≤ ENNReal.ofReal b)
    {f : E n → ℝ} (hfm : Measurable f) (hfi : Integrable f) (hf0 : ∀ x, 0 ≤ f x) (x : E n) :
    ‖nikodymMaximal δ f x‖ₑ ≤
      (ENNReal.ofReal a)⁻¹ * RHS δ R N (fun y => ENNReal.ofReal (f y)) x := by
  set M := (ENNReal.ofReal a)⁻¹ * RHS δ R N (fun y => ENNReal.ofReal (f y)) x with hMdef
  have hterm0 : ∀ T : {T : E n × E n // ‖T.1‖ = 1 ∧ x ∈ tube δ T.1 T.2},
      0 ≤ (volume (tube δ T.1.1 T.1.2)).toReal⁻¹ * ∫ y in tube δ T.1.1 T.1.2, f y := fun T =>
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (setIntegral_nonneg (measurableSet_tube _ _ _) fun y _ => hf0 y)
  have hN0 : 0 ≤ nikodymMaximal δ f x := Real.iSup_nonneg hterm0
  rw [Real.enorm_eq_ofReal hN0]
  by_cases hM : M = ⊤
  · rw [hM]; exact le_top
  have hle : nikodymMaximal δ f x ≤ M.toReal := by
    apply Real.iSup_le _ ENNReal.toReal_nonneg
    rintro ⟨⟨ω, c⟩, hω, hxT⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal hM]
    simp only
    obtain ⟨hV1, hV2⟩ := hvol ω c hω
    have hVpos : 0 < volume (tube δ ω c) := lt_of_lt_of_le (ENNReal.ofReal_pos.2 ha) hV1
    have hVtop : volume (tube δ ω c) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV2
    rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg),
      ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hVpos.ne' hVtop), ENNReal.ofReal_toReal hVtop,
      ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (ae_of_all _ hf0)]
    exact mul_le_mul' (ENNReal.inv_le_inv.2 hV1)
      (tube_lintegral_le hδ hR (ENNReal.measurable_ofReal.comp hfm) hω hxT)
  calc ENNReal.ofReal (nikodymMaximal δ f x) ≤ ENNReal.ofReal M.toReal :=
        ENNReal.ofReal_le_ofReal hle
    _ = M := ENNReal.ofReal_toReal hM

/-! ### The ball term -/

theorem lintegral_ball_swap {φ : E n → ℝ≥0∞} (hφ : AEMeasurable φ volume) (r : ℝ) :
    ∫⁻ x, ∫⁻ y in closedBall x r, φ y = volume (closedBall (0 : E n) r) * ∫⁻ y, φ y := by
  have h1 : ∀ x, ∫⁻ y in closedBall x r, φ y = ∫⁻ y, (closedBall x r).indicator φ y :=
    fun x => (lintegral_indicator measurableSet_closedBall _).symm
  simp_rw [h1]
  have hm : AEMeasurable (Function.uncurry fun x y => (closedBall x r).indicator φ y)
      ((volume : Measure (E n)).prod volume) := by
    have : (Function.uncurry fun x y => (closedBall x r).indicator φ y) =
        {q : E n × E n | dist q.2 q.1 ≤ r}.indicator (fun q => φ q.2) := by
      funext q; simp [Set.indicator, Function.uncurry, mem_closedBall]
    rw [this]
    exact (hφ.comp_snd).indicator
      (measurableSet_le (measurable_snd.dist measurable_fst) measurable_const)
  rw [lintegral_lintegral_swap hm]
  have h2 : ∀ y, ∫⁻ x, (closedBall x r).indicator φ y = φ y * volume (closedBall (0 : E n) r) := by
    intro y
    have : (fun x => (closedBall x r).indicator φ y) =
        (closedBall y r).indicator (fun _ => φ y) := by
      funext x; simp [Set.indicator, mem_closedBall, dist_comm]
    rw [this, lintegral_indicator_const measurableSet_closedBall,
      Measure.addHaar_closedBall_center]
  simp_rw [h2]
  rw [lintegral_mul_const' _ _ measure_closedBall_lt_top.ne, mul_comm]

theorem measurable_ballIntegral {F : E n → ℝ≥0∞} (hF : Measurable F) (R : ℝ) :
    Measurable fun x => ∫⁻ y in closedBall x R, F y := by
  have : (fun x => ∫⁻ y in closedBall x R, F y) = fun x =>
      ∫⁻ y, {q : E n × E n | dist q.2 q.1 ≤ R}.indicator (fun q => F q.2) (x, y) := by
    funext x; rw [← lintegral_indicator measurableSet_closedBall]; rfl
  rw [this]
  exact ((hF.comp measurable_snd).indicator
    (measurableSet_le (measurable_snd.dist measurable_fst) measurable_const)).lintegral_prod_right'

/-- Hölder on a ball. -/
theorem ball_holder {p : ℝ} (hp : 1 ≤ p) {F : E n → ℝ≥0∞} (hF : Measurable F) (x : E n)
    (R : ℝ) : (∫⁻ y in closedBall x R, F y) ^ p ≤
      volume (closedBall (0 : E n) R) ^ (p - 1) * ∫⁻ y in closedBall x R, F y ^ p := by
  have hp0 : 0 < p := by linarith
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict (closedBall x R)) (p := 1) (q := ENNReal.ofReal p)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp) hF.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by simpa using hp0) ENNReal.ofReal_ne_top, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall_center] at h
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_one] at h
  calc (∫⁻ y in closedBall x R, F y) ^ p
      ≤ ((∫⁻ y in closedBall x R, F y ^ p) ^ (1 / p) *
          volume (closedBall (0 : E n) R) ^ (1 / 1 - 1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = volume (closedBall (0 : E n) R) ^ (p - 1) * ∫⁻ y in closedBall x R, F y ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one, mul_comm]
        congr 2
        field_simp

theorem lpn_ball_le {p : ℝ} (hp : 1 ≤ p) {F : E n → ℝ≥0∞} (hF : Measurable F) {R : ℝ}
    (hR : 0 < R) :
    lpn p (fun x => ∫⁻ y in closedBall x R, F y) ≤ volume (closedBall (0 : E n) R) * lpn p F := by
  have hp0 : 0 < p := by linarith
  set V := volume (closedBall (0 : E n) R) with hVdef
  have hV0 : V ≠ 0 := (measure_closedBall_pos volume 0 hR).ne'
  have hVt : V ≠ ⊤ := measure_closedBall_lt_top.ne
  apply rpow_le_of_le_mul_pow hp0
  calc ∫⁻ x, (∫⁻ y in closedBall x R, F y) ^ p
      ≤ ∫⁻ x, V ^ (p - 1) * ∫⁻ y in closedBall x R, F y ^ p :=
        lintegral_mono fun x => ball_holder hp hF x R
    _ = V ^ (p - 1) * (V * ∫⁻ y, F y ^ p) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hVt),
          lintegral_ball_swap (hF.pow_const p).aemeasurable R]
    _ = V ^ p * ∫⁻ y, F y ^ p := by
        rw [← mul_assoc]
        congr 1
        conv_rhs => rw [show p = (p - 1) + 1 by ring]
        rw [ENNReal.rpow_add _ _ hV0 hVt, ENNReal.rpow_one]

/-! ### `Lᵖ` bound for the dominating function -/

theorem lpn_RHS_le {p : ℝ} (hp : 1 ≤ p) {δ R : ℝ} (hR : 0 < R) {N : ℕ} {F : E n → ℝ≥0∞}
    (hF : Measurable F) (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k ∈ Finset.range N, ∀ j : Fin n × Bool,
      ∫⁻ x, capMax (capVec j) (3 * δ / (1 / 2 : ℝ) ^ k) (Fr ((1 / 2 : ℝ) ^ k) F) x ^ p ≤
        ENNReal.ofReal (B k) ^ p * ∫⁻ y, Fr ((1 / 2 : ℝ) ^ k) F y ^ p) :
    lpn p (RHS δ R N F) ≤ ENNReal.ofReal (R ^ n * (volume (ball (0 : E n) 1)).toReal +
      ∑ k ∈ Finset.range N, 4 * n * (((1 / 2 : ℝ) ^ k) ^ n * B k)) * lpn p F := by
  have hp0 : 0 < p := by linarith
  have hmc : ∀ r : ℝ, ∀ j : Fin n × Bool,
      Measurable fun x => capMax (capVec j) (3 * δ / r) (Fr r F) (r⁻¹ • x) := fun r j =>
    (capMax_measurable _ _ _ (hF.comp (measurable_const_smul r))).comp (measurable_const_smul _)
  have hPhi : ∀ k ∈ Finset.range N, lpn p (Phi δ ((1 / 2 : ℝ) ^ k) F) ≤
      (2 * n : ℝ≥0∞) * (ENNReal.ofReal (B k) * lpn p F) := by
    intro k hk
    have hr : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have hsum := lpn_sum_le hp Finset.univ
      (fun j x => capMax (capVec j) (3 * δ / (1 / 2 : ℝ) ^ k) (Fr ((1 / 2 : ℝ) ^ k) F)
        (((1 / 2 : ℝ) ^ k)⁻¹ • x)) fun j _ => (hmc _ j).aemeasurable
    refine hsum.trans ?_
    calc ∑ j : Fin n × Bool, lpn p (fun x => capMax (capVec j) (3 * δ / (1 / 2 : ℝ) ^ k)
          (Fr ((1 / 2 : ℝ) ^ k) F) (((1 / 2 : ℝ) ^ k)⁻¹ • x))
        ≤ ∑ _j : Fin n × Bool, ENNReal.ofReal (B k) * lpn p F :=
          Finset.sum_le_sum fun j _ => lpn_capTerm hp hr _ _ F (hB k hk j)
      _ = (2 * n : ℝ≥0∞) * (ENNReal.ofReal (B k) * lpn p F) := by
          rw [Finset.sum_const, Finset.card_univ]
          simp [Fintype.card_prod, nsmul_eq_mul]
          ring
  have hmeasPhi : ∀ k, Measurable (fun x => 2 * (ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ n) *
      Phi δ ((1 / 2 : ℝ) ^ k) F x)) := by
    intro k
    refine measurable_const.mul (measurable_const.mul ?_)
    unfold Phi
    exact Finset.measurable_fun_sum _ fun j _ => hmc _ j
  set V := volume (closedBall (0 : E n) R) with hVdef
  have hV : V = ENNReal.ofReal (R ^ n * (volume (ball (0 : E n) 1)).toReal) := by
    rw [hVdef, Measure.addHaar_closedBall _ _ hR.le, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  calc lpn p (RHS δ R N F)
      ≤ lpn p (fun x => ∫⁻ y in closedBall x R, F y) + lpn p (fun x => ∑ k ∈ Finset.range N,
          2 * (ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ n) * Phi δ ((1 / 2 : ℝ) ^ k) F x)) :=
        lpn_add_le hp (measurable_ballIntegral hF R).aemeasurable
          (Finset.measurable_fun_sum (Finset.range N) fun k _ => hmeasPhi k).aemeasurable
    _ ≤ V * lpn p F + ∑ k ∈ Finset.range N, lpn p (fun x => 2 *
          (ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ n) * Phi δ ((1 / 2 : ℝ) ^ k) F x)) :=
        add_le_add (lpn_ball_le hp hF hR)
          (lpn_sum_le hp _ _ fun k _ => (hmeasPhi k).aemeasurable)
    _ ≤ V * lpn p F + ∑ k ∈ Finset.range N, 2 * (ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ n) *
          ((2 * n : ℝ≥0∞) * (ENNReal.ofReal (B k) * lpn p F))) := by
        gcongr with k hk
        rw [lpn_const_mul hp0 _ (by norm_num), lpn_const_mul hp0 _ ENNReal.ofReal_ne_top]
        gcongr
        exact hPhi k hk
    _ = _ := by
        have hnn : ∀ k, 0 ≤ 4 * (n : ℝ) * (((1 / 2 : ℝ) ^ k) ^ n * B k) := fun k => by
          have := hB0 k; positivity
        rw [hV, ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun k _ => hnn k),
          ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k), add_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have := hB0 k
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        ring

/-! ### Test functions -/

theorem isTest_comp_smul {p : ℝ} (hp : 1 ≤ p) {r : ℝ} (hr : 0 < r) {f : E n → ℝ}
    (hf : IsTest p f) (hfm : Measurable f) : IsTest p (fun z => f (r • z)) := by
  have hp0 : 0 < p := by linarith
  refine ⟨⟨(hfm.comp (measurable_const_smul r)).aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [eLpNorm_eq_lpn hp]
    have := lpn_Fr hp0 hr (fun x => ‖f x‖ₑ)
    unfold Fr at this
    rw [this, ← eLpNorm_eq_lpn hp]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.1.2
  · obtain ⟨R, hR⟩ := hf.2.subset_closedBall 0
    refine (isBounded_closedBall (x := (0 : E n)) (r := R / r)).subset ?_
    intro y hy
    have h := hR (show r • y ∈ Function.support f from hy)
    simp only [mem_closedBall, dist_zero_right] at h ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr] at h
    rw [le_div_iff₀ hr]; linarith [mul_comm r ‖y‖]

theorem kBound_mono {p δ A A' : ℝ} (h : KBound n p δ A) (hA : A ≤ A') : KBound n p δ A' := by
  intro f hf hf0
  exact (h f hf hf0).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hA) _)

theorem measurable_version {p : ℝ} {f : E n → ℝ} (hf : IsTest p f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ g : E n → ℝ, Measurable g ∧ IsTest p g ∧ (∀ x, 0 ≤ g x) ∧ f =ᵐ[volume] g := by
  obtain ⟨R, hR⟩ := hf.2.subset_closedBall 0
  set h := hf.1.1.mk f
  have hh : StronglyMeasurable h := hf.1.1.stronglyMeasurable_mk
  set g := (closedBall (0 : E n) R).indicator (fun x => max (h x) 0) with hg
  have hgm : Measurable g := (hh.measurable.max measurable_const).indicator measurableSet_closedBall
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hf.1.1.ae_eq_mk] with x hx
    by_cases hxR : x ∈ closedBall (0 : E n) R
    · simp only [hg, indicator_of_mem hxR]
      rw [show h x = f x from hx.symm]; exact (max_eq_left (hf0 x)).symm
    · simp only [hg, indicator_of_notMem hxR]
      by_contra hne; exact hxR (hR hne)
  refine ⟨g, hgm, ⟨MemLp.ae_eq hfg hf.1, ?_⟩, fun x => ?_, hfg⟩
  · refine (isBounded_closedBall (x := (0 : E n)) (r := R)).subset ?_
    intro x hx; by_contra hxR; exact hx (indicator_of_notMem hxR _)
  · simp only [hg]
    by_cases hxR : x ∈ closedBall (0 : E n) R
    · rw [indicator_of_mem hxR]; exact le_max_right _ _
    · rw [indicator_of_notMem hxR]

theorem nikodymMaximal_congr {δ : ℝ} {f g : E n → ℝ} (h : f =ᵐ[volume] g) :
    nikodymMaximal δ f = nikodymMaximal δ g := by
  funext x; unfold nikodymMaximal; congr 1; funext T; congr 1
  exact integral_congr_ae (ae_restrict_of_ae h)

/-! ### Constants -/

/-- The `(k, j)` term: `r^n K ε^m A ≲ δ^m δ^e r^t` with `ε = 3δ/r`, `A = M (Λε)^e`. -/
theorem term_bound {m : ℕ} {K M Λ δ r e t : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hΛ : 0 < Λ)
    (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1) (het : t ≤ 1 - e) :
    r ^ (m + 1) * (K * (3 * δ / r) ^ m * (M * (Λ * (3 * δ / r)) ^ e)) ≤
      K * M * 3 ^ m * (3 * Λ) ^ e * δ ^ m * δ ^ e * r ^ t := by
  have h1 : (Λ * (3 * δ / r)) ^ e = (3 * Λ) ^ e * δ ^ e / r ^ e := by
    rw [show Λ * (3 * δ / r) = (3 * Λ) * δ / r by ring,
      Real.div_rpow (by positivity) hr.le, Real.mul_rpow (by positivity) hδ.le]
  have h2 : r / r ^ e ≤ r ^ t := by
    have : r / r ^ e = r ^ (1 - e) := by rw [Real.rpow_sub hr, Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 het
  have hre : 0 < r ^ e := Real.rpow_pos_of_pos hr e
  calc r ^ (m + 1) * (K * (3 * δ / r) ^ m * (M * (Λ * (3 * δ / r)) ^ e))
      = K * M * 3 ^ m * (3 * Λ) ^ e * δ ^ m * δ ^ e * (r / r ^ e) := by
        rw [h1, div_pow, mul_pow]
        field_simp
        ring
    _ ≤ K * M * 3 ^ m * (3 * Λ) ^ e * δ ^ m * δ ^ e * r ^ t := by gcongr

/-! ### The main estimate -/

theorem main_estimate (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p) {α : ℝ} (hα : 0 ≤ α) {C δ₀ : ℝ}
    (hδ₀ : 0 < δ₀)
    (hK : ∀ δ, 0 < δ → δ < δ₀ → KBound n p δ (C * δ ^ (1 - (n : ℝ) / p - α))) :
    ∃ C' δ₀' : ℝ, 0 < δ₀' ∧ δ₀' ≤ 1 ∧ ∀ δ, 0 < δ → δ < δ₀' → ∀ f : E n → ℝ, IsTest p f →
      (∀ x, 0 ≤ f x) → Measurable f →
      eLpNorm (nikodymMaximal δ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C' * δ ^ (1 - (n : ℝ) / p - α)) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Λ, K, κ, hΛ, hK0, hκ, hcap⟩ := capMax_le hn hp
  obtain ⟨c₁, c₂, hc₁, hc₂, hvol⟩ := tube_volume_bounds (m + 1) (by omega)
  have hp0 : 0 < p := by linarith
  set e := 1 - ((m + 1 : ℕ) : ℝ) / p - α with he
  set t := ((m + 1 : ℕ) : ℝ) / p with ht
  have ht0 : 0 < t := by positivity
  have het : t ≤ 1 - e := by rw [he]; linarith
  have he1 : e ≤ 1 := by rw [he]; linarith
  set M := max C 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  set ρ := 3 / κ + 6 * Λ / δ₀ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρκ : 3 ≤ ρ * κ := by
    rw [hρ, add_mul, div_mul_cancel₀ _ hκ.ne']
    have : 0 ≤ 6 * Λ / δ₀ * κ := by positivity
    linarith
  have hρδ₀ : 6 * Λ ≤ ρ * δ₀ := by
    rw [hρ, add_mul, div_mul_cancel₀ _ hδ₀.ne']
    have : 0 ≤ 3 / κ * δ₀ := by positivity
    linarith
  set β := (volume (ball (0 : E (m + 1)) 1)).toReal with hβ
  have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
  set q := (1 / 2 : ℝ) ^ t with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ht0
  set Q0 := K * M * 3 ^ m * (3 * Λ) ^ e with hQ0def
  have hQ0 : 0 ≤ Q0 := by positivity
  set C' := ((2 * ρ + 2) ^ (m + 1) * β + 4 * ((m + 1 : ℕ) : ℝ) * Q0 / (1 - q)) / c₁ with hC'
  refine ⟨C', min (1 / ρ) 1, lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
  intro δ hδ hδ' f hf hf0 hfm
  have hδ1 : δ ≤ 1 := (lt_of_lt_of_le hδ' (min_le_right _ _)).le
  have hρδ : ρ * δ ≤ 1 := by
    have := lt_of_lt_of_le hδ' (min_le_left _ _)
    rw [lt_div_iff₀ hρ0] at this; linarith
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near (x := 1 / (ρ * δ)) (y := (2 : ℝ))
    (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num)
  have hN1' : (2 : ℝ) ^ N * (ρ * δ) ≤ 1 := (le_div_iff₀ (by positivity)).1 hN1
  set R := (2 * ρ + 2) * δ with hRdef
  have hRpos : 0 < R := by positivity
  have hR : (1 / 2 : ℝ) ^ N + 2 * δ ≤ R := by
    have h1 : 1 < 2 ^ (N + 1) * (ρ * δ) := (div_lt_iff₀ (by positivity)).1 hN2
    have h2 : (1 / 2 : ℝ) ^ N * 2 ^ N = 1 := by rw [← mul_pow]; norm_num
    have hpos : (0 : ℝ) < (1 / 2) ^ N := by positivity
    have h4 : (1 / 2 : ℝ) ^ N * (2 ^ (N + 1) * (ρ * δ)) = 2 * ρ * δ := by
      rw [pow_succ, show (1 / 2 : ℝ) ^ N * (2 ^ N * 2 * (ρ * δ)) =
        ((1 / 2) ^ N * 2 ^ N) * (2 * ρ * δ) by ring, h2, one_mul]
    have h3 := mul_lt_mul_of_pos_left h1 hpos
    rw [h4, mul_one] at h3
    have h9 : (2 * ρ + 2) * δ = 2 * ρ * δ + 2 * δ := by ring
    rw [hRdef, h9]; linarith
  -- the cap estimates at each dyadic scale
  set F : E (m + 1) → ℝ≥0∞ := fun y => ENNReal.ofReal (f y) with hFdef
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hfm
  set B : ℕ → ℝ := fun k => K * (3 * δ / (1 / 2 : ℝ) ^ k) ^ m *
    (M * (Λ * (3 * δ / (1 / 2 : ℝ) ^ k)) ^ e) with hBdef
  have hB0 : ∀ k, 0 ≤ B k := fun k => by simp only [hBdef]; positivity
  have hB : ∀ k ∈ Finset.range N, ∀ j : Fin (m + 1) × Bool,
      ∫⁻ x, capMax (capVec j) (3 * δ / (1 / 2 : ℝ) ^ k) (Fr ((1 / 2 : ℝ) ^ k) F) x ^ p ≤
        ENNReal.ofReal (B k) ^ p * ∫⁻ y, Fr ((1 / 2 : ℝ) ^ k) F y ^ p := by
    intro k hk j
    have hk' : k < N := Finset.mem_range.1 hk
    have hr : (0 : ℝ) < (1 / 2) ^ k := by positivity
    set ε := 3 * δ / (1 / 2 : ℝ) ^ k with hε
    have hεeq : ε = 3 * δ * 2 ^ k := by
      rw [hε, one_div_pow, div_div_eq_mul_div, div_one]
    have h2k : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk'.le
    have hερ : ρ * ε ≤ 3 := by
      have h5 := mul_le_mul_of_nonneg_right h2k (by positivity : (0 : ℝ) ≤ ρ * δ)
      have h6 : ρ * ε = 3 * (2 ^ k * (ρ * δ)) := by rw [hεeq]; ring
      rw [h6]; linarith
    have hε0 : 0 < ε := by positivity
    have hεκ : ε ≤ κ := le_of_mul_le_mul_left (by linarith) hρ0
    have hΛε : Λ * ε < δ₀ := by
      have h7 : ρ * (Λ * ε) = Λ * (ρ * ε) := by ring
      have h8 : Λ * (ρ * ε) ≤ Λ * 3 := mul_le_mul_of_nonneg_left hερ hΛ.le
      have : ρ * (Λ * ε) < ρ * δ₀ := by linarith
      exact lt_of_mul_lt_mul_left this hρ0.le
    have hKB := kBound_mono (hK (Λ * ε) (by positivity) hΛε)
      (show C * (Λ * ε) ^ e ≤ M * (Λ * ε) ^ e from
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have := hcap (capVec j) (norm_capVec j) ε hε0 hεκ (M * (Λ * ε) ^ e) (by positivity) hKB
      (fun z => f ((1 / 2 : ℝ) ^ k • z)) (isTest_comp_smul hp hr hf hfm) (fun z => hf0 _)
    simp only [Nat.add_sub_cancel] at this
    exact this
  -- pointwise and `Lᵖ` bounds
  have hapos : 0 < c₁ * δ ^ m := by positivity
  have hpt : ∀ x, ‖nikodymMaximal δ f x‖ₑ ≤
      (ENNReal.ofReal (c₁ * δ ^ m))⁻¹ * RHS δ R N F x := by
    intro x
    have := nikodym_le hδ hR hapos (b := c₂ * δ ^ m)
      (fun ω c hω => by simpa using hvol δ hδ hδ1 ω c hω) hfm (isTest_integrable hp hf) hf0 x
    exact this
  have hL := lpn_RHS_le hp hRpos hFm B hB0 hB
  have hfL : eLpNorm f (ENNReal.ofReal p) volume = lpn p F := by
    rw [eLpNorm_eq_lpn hp]; congr 1; funext x; exact Real.enorm_eq_ofReal (hf0 x)
  -- the real inequality
  set Tr := R ^ (m + 1) * β + ∑ k ∈ Finset.range N,
    4 * ((m + 1 : ℕ) : ℝ) * (((1 / 2 : ℝ) ^ k) ^ (m + 1) * B k) with hTr
  have hreal : (c₁ * δ ^ m)⁻¹ * Tr ≤ C' * δ ^ e := by
    have hterm : ∀ k ∈ Finset.range N, ((1 / 2 : ℝ) ^ k) ^ (m + 1) * B k ≤
        Q0 * δ ^ m * δ ^ e * q ^ k := by
      intro k _
      have h := term_bound (m := m) hK0.le hM hΛ hδ (by positivity : (0 : ℝ) < (1 / 2) ^ k)
        (pow_le_one₀ (by norm_num) (by norm_num)) het
      rw [hq, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      simp only [hBdef, hQ0def]
      exact h
    have hsum : ∑ k ∈ Finset.range N, 4 * ((m + 1 : ℕ) : ℝ) *
        (((1 / 2 : ℝ) ^ k) ^ (m + 1) * B k) ≤
        4 * ((m + 1 : ℕ) : ℝ) * (Q0 * δ ^ m * δ ^ e) * (1 / (1 - q)) := by
      calc ∑ k ∈ Finset.range N, 4 * ((m + 1 : ℕ) : ℝ) * (((1 / 2 : ℝ) ^ k) ^ (m + 1) * B k)
          ≤ ∑ k ∈ Finset.range N, 4 * ((m + 1 : ℕ) : ℝ) * (Q0 * δ ^ m * δ ^ e * q ^ k) :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hterm k hk) (by positivity)
        _ = 4 * ((m + 1 : ℕ) : ℝ) * (Q0 * δ ^ m * δ ^ e) * ∑ k ∈ Finset.range N, q ^ k := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
        _ ≤ 4 * ((m + 1 : ℕ) : ℝ) * (Q0 * δ ^ m * δ ^ e) * (1 / (1 - q)) := by
            gcongr
            have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq0 hq1
            rwa [pow_zero, ← Finset.range_eq_Ico] at this
    have hball : R ^ (m + 1) * β = (2 * ρ + 2) ^ (m + 1) * β * δ ^ m * δ := by
      rw [hRdef, mul_pow, pow_succ δ]; ring
    have hδe : δ ≤ δ ^ e := by
      have := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 he1
      rwa [Real.rpow_one] at this
    have hq1' : 0 < 1 - q := by linarith
    calc (c₁ * δ ^ m)⁻¹ * Tr
        ≤ (c₁ * δ ^ m)⁻¹ * ((2 * ρ + 2) ^ (m + 1) * β * δ ^ m * δ ^ e +
            4 * ((m + 1 : ℕ) : ℝ) * (Q0 * δ ^ m * δ ^ e) * (1 / (1 - q))) := by
          rw [hTr, hball]
          gcongr
      _ = C' * δ ^ e := by
          rw [hC']
          field_simp
  -- assemble
  rw [eLpNorm_eq_lpn hp, hfL]
  have hVinv : (ENNReal.ofReal (c₁ * δ ^ m))⁻¹ = ENNReal.ofReal ((c₁ * δ ^ m)⁻¹) :=
    (ENNReal.ofReal_inv_of_pos hapos).symm
  calc lpn p (fun x => ‖nikodymMaximal δ f x‖ₑ)
      ≤ lpn p (fun x => (ENNReal.ofReal (c₁ * δ ^ m))⁻¹ * RHS δ R N F x) := lpn_mono hp0 hpt
    _ = (ENNReal.ofReal (c₁ * δ ^ m))⁻¹ * lpn p (RHS δ R N F) :=
        lpn_const_mul hp0 _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hapos).ne') _
    _ ≤ ENNReal.ofReal ((c₁ * δ ^ m)⁻¹) * (ENNReal.ofReal Tr * lpn p F) := by
        rw [hVinv]; gcongr
    _ ≤ ENNReal.ofReal (C' * δ ^ e) * lpn p F := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        gcongr

/-- (Part A) `K(p, α) ⟹ N(p, α)`. -/
theorem nikodym_of_kakeya (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp1 : 1 ≤ p) (hpn : p ≤ n) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α < ((n : ℝ) + 1) / p) :
    KakeyaMaximalEstimate n p α → NikodymMaximalEstimate n p α := by
  intro hK
  obtain ⟨C, δ₀, hδ₀, -, hKB⟩ := (kakeyaMaximalEstimate_iff hn hp1 α).1 hK
  obtain ⟨C', δ₀', h1, h2, hmain⟩ := main_estimate hn hp1 hα hδ₀ hKB
  refine (nikodymMaximalEstimate_iff hn hp1 α).2 ⟨C', δ₀', h1, h2, ?_⟩
  intro δ hδ hδ' f hf hf0
  obtain ⟨g, hgm, hg, hg0, hfg⟩ := measurable_version hf hf0
  rw [nikodymMaximal_congr hfg, eLpNorm_congr_ae hfg]
  exact hmain δ hδ hδ' g hg hg0 hgm

end TaoBR.T410.K2N.PartA

end S_PartA


open TaoBR in
theorem solution (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp1 : 1 ≤ p) (hpn : p ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hα' : α < ((n : ℝ) + 1) / p) :
    (KakeyaMaximalEstimate n p α → NikodymMaximalEstimate n p α) ∧
    (NikodymMaximalEstimate n p α → KakeyaMaximalEstimate n p (2 * α)) :=
  ⟨TaoBR.T410.K2N.PartA.nikodym_of_kakeya n hn p hp1 hpn α hα hα',
    TaoBR.T410.PartN2K.kakeya_two_mul_of_nikodym n hn p hp1 hpn α hα hα'⟩
