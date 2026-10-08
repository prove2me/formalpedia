-- Prove2me | solution 1 for PalmQueueing.Ordering.strassen_st
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T11:24:45.376905+00:00
-- url     : https://prove2.me/submissions/4850e8f4-11a8-4e4a-bc95-c025ba56bf40

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
namespace StrassenStTransform
lemma st_map_of_monotone {d : ℕ} (F G : Measure (Fin d → ℝ))
    (horder : StLe F G) (A : (Fin d → ℝ) → Fin d → ℝ)
    (hmA : Measurable A)
    (hmono : ∀ x y, CoordLe x y → CoordLe (A x) (A y)) :
    StLe (F.map A) (G.map A) := by
  intro f hf hiF hiG
  have hiFA := (integrable_map_measure hiF.aestronglyMeasurable hmA.aemeasurable).mp hiF
  have hiGA := (integrable_map_measure hiG.aestronglyMeasurable hmA.aemeasurable).mp hiG
  have hh := horder (f ∘ A) (fun x y hxy => hf _ _ (hmono x y hxy)) hiFA hiGA
  rw [integral_map hmA.aemeasurable hiF.aestronglyMeasurable,
    integral_map hmA.aemeasurable hiG.aestronglyMeasurable]
  exact hh

noncomputable def boundedTransform {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun k => Real.arctan (x k)
noncomputable def inverseTransform {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun k => Real.tan (x k)
lemma boundedTransform_continuous {d : ℕ} : Continuous (@boundedTransform d) :=
  continuous_pi (fun k => Real.continuous_arctan.comp (continuous_apply k))
lemma boundedTransform_monotone {d : ℕ} (x y : Fin d → ℝ) (hxy : CoordLe x y) :
    CoordLe (boundedTransform x) (boundedTransform y) :=
  fun k => Real.arctan_mono (hxy k)
lemma inverse_boundedTransform {d : ℕ} (x : Fin d → ℝ) :
    inverseTransform (boundedTransform x) = x := by
  funext k
  exact Real.tan_arctan (x k)
lemma boundedTransform_norm {d : ℕ} (x : Fin d → ℝ) :
    ‖boundedTransform x‖ ≤ Real.pi / 2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan (x k)).le,
    (Real.arctan_lt_pi_div_two (x k)).le⟩
lemma boundedTransform_integrable {d : ℕ} (P : Measure (Fin d → ℝ)) [IsFiniteMeasure P] :
    Integrable (@boundedTransform d) P := by
  apply Integrable.of_bound boundedTransform_continuous.aestronglyMeasurable (Real.pi / 2)
  exact ae_of_all _ boundedTransform_norm
lemma bounded_transform_st {d : ℕ} (F G : Measure (Fin d → ℝ))
    (horder : StLe F G) : StLe (F.map boundedTransform) (G.map boundedTransform) :=
  st_map_of_monotone F G horder boundedTransform boundedTransform_continuous.measurable
    boundedTransform_monotone
lemma inverseTransform_measurable {d : ℕ} : Measurable (@inverseTransform d) := by
  apply measurable_pi_lambda
  intro k
  unfold inverseTransform Real.tan
  fun_prop
lemma inverse_transformed_law {d : ℕ} (F : Measure (Fin d → ℝ)) :
    (F.map boundedTransform).map inverseTransform = F := by
  rw [Measure.map_map inverseTransform_measurable boundedTransform_continuous.measurable]
  have hh : (@inverseTransform d ∘ boundedTransform) = id := by
    funext x
    exact inverse_boundedTransform x
  rw [hh, Measure.map_id]
lemma transformed_roundtrip_ae {d : ℕ} (F : Measure (Fin d → ℝ)) :
    ∀ᵐ x ∂F.map boundedTransform, boundedTransform (inverseTransform x) = x := by
  apply (ae_map_iff boundedTransform_continuous.measurable.aemeasurable
    (measurableSet_eq_fun (boundedTransform_continuous.measurable.comp inverseTransform_measurable)
      measurable_id)).mpr
  exact ae_of_all _ (fun x => by simp only [Function.comp_apply, id_eq, inverse_boundedTransform])
lemma recover_original_coupling {d : ℕ} (F G : Measure (Fin d → ℝ))
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hf : μ.map Prod.fst = F.map boundedTransform)
    (hg : μ.map Prod.snd = G.map boundedTransform)
    (horder : ∀ᵐ z ∂μ, CoordLe z.1 z.2) :
    μ.map (inverseTransform ∘ Prod.fst) = F ∧
    μ.map (inverseTransform ∘ Prod.snd) = G ∧
    ∀ᵐ z ∂μ, CoordLe (inverseTransform z.1) (inverseTransform z.2) := by
  have heq : MeasurableSet {x : Fin d → ℝ | boundedTransform (inverseTransform x) = x} :=
    measurableSet_eq_fun (boundedTransform_continuous.measurable.comp inverseTransform_measurable)
      measurable_id
  have hrf : ∀ᵐ z ∂μ, boundedTransform (inverseTransform z.1) = z.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable heq).mp
    rw [hf]
    exact transformed_roundtrip_ae F
  have hrg : ∀ᵐ z ∂μ, boundedTransform (inverseTransform z.2) = z.2 := by
    apply (ae_map_iff measurable_snd.aemeasurable heq).mp
    rw [hg]
    exact transformed_roundtrip_ae G
  refine ⟨?_,?_,?_⟩
  · rw [← Measure.map_map inverseTransform_measurable measurable_fst,hf]
    exact inverse_transformed_law F
  · rw [← Measure.map_map inverseTransform_measurable measurable_snd,hg]
    exact inverse_transformed_law G
  · filter_upwards [horder,hrf,hrg] with z hz h₁ h₂
    intro k
    apply Real.arctan_le_arctan_iff.mp
    have hh := hz k
    rw [← h₁,← h₂] at hh
    exact hh
end StrassenStTransform
#print axioms StrassenStTransform.st_map_of_monotone
#print axioms StrassenStTransform.boundedTransform_continuous
#print axioms StrassenStTransform.boundedTransform_monotone
#print axioms StrassenStTransform.inverse_boundedTransform
#print axioms StrassenStTransform.boundedTransform_norm
#print axioms StrassenStTransform.boundedTransform_integrable
#print axioms StrassenStTransform.bounded_transform_st
#print axioms StrassenStTransform.inverseTransform_measurable
#print axioms StrassenStTransform.inverse_transformed_law
#print axioms StrassenStTransform.transformed_roundtrip_ae
#print axioms StrassenStTransform.recover_original_coupling

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
namespace StrassenStQuantization
noncomputable def scalarQuantizer (n : ℕ) (x : ℝ) : ℝ :=
  (Int.floor (((n : ℝ)+1) * max (-2) (min 2 x)) : ℝ) / ((n : ℝ)+1)
noncomputable def quantizer {d : ℕ} (n : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun k => scalarQuantizer n (x k)
lemma scalarQuantizer_measurable (n : ℕ) : Measurable (scalarQuantizer n) := by
  unfold scalarQuantizer
  fun_prop
lemma quantizer_measurable {d : ℕ} (n : ℕ) : Measurable (@quantizer d n) :=
  measurable_pi_lambda _ (fun k => (scalarQuantizer_measurable n).comp (measurable_pi_apply k))
lemma scalarQuantizer_monotone (n : ℕ) : Monotone (scalarQuantizer n) := by
  intro x y hxy
  unfold scalarQuantizer
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Int.cast_le.mpr (Int.floor_mono (mul_le_mul_of_nonneg_left
    (max_le_max le_rfl (min_le_min le_rfl hxy)) (by positivity)))
lemma quantizer_monotone {d : ℕ} (n : ℕ) (x y : Fin d → ℝ) (hxy : CoordLe x y) :
    CoordLe (quantizer n x) (quantizer n y) :=
  fun k => scalarQuantizer_monotone n (hxy k)
lemma quantizer_finiteRange {d : ℕ} (n : ℕ) : (Set.range (@quantizer d n)).Finite := by
  classical
  let lo : ℤ := Int.floor (((n : ℝ)+1) * (-2))
  let hi : ℤ := Int.floor (((n : ℝ)+1) * 2)
  let S : Set (Fin d → ℤ) := {v | ∀ k, v k ∈ Set.Icc lo hi}
  have hS : S.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc lo hi)
  apply (hS.image (fun v : Fin d → ℤ => fun k => (v k : ℝ)/((n : ℝ)+1))).subset
  rintro _ ⟨x,rfl⟩
  refine ⟨fun k => Int.floor (((n : ℝ)+1) * max (-2) (min 2 (x k))),?_,rfl⟩
  intro k
  constructor
  · exact Int.floor_mono (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
  · exact Int.floor_mono (mul_le_mul_of_nonneg_left
      (max_le (by norm_num) (min_le_left _ _)) (by positivity))
lemma scalarQuantizer_error (n : ℕ) (x : ℝ) (hx : |x| ≤ 2) :
    |x - scalarQuantizer n x| ≤ 1 / ((n : ℝ)+1) := by
  have hs : 0 < (n : ℝ)+1 := by positivity
  have hc : max (-2) (min 2 x) = x := by
    rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]
  unfold scalarQuantizer
  rw [hc]
  have hle := Int.floor_le (((n : ℝ)+1)*x)
  have hlt := Int.lt_floor_add_one (((n : ℝ)+1)*x)
  have he : 0 ≤ x - (Int.floor (((n : ℝ)+1)*x) : ℝ)/((n : ℝ)+1) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hs).mpr (by nlinarith)
  rw [abs_of_nonneg he]
  apply (le_div_iff₀ hs).mpr
  have hmul : ((Int.floor (((n : ℝ)+1)*x) : ℝ)/((n : ℝ)+1))*((n : ℝ)+1) =
      (Int.floor (((n : ℝ)+1)*x) : ℝ) := div_mul_cancel₀ _ hs.ne'
  nlinarith
lemma quantizer_error {d : ℕ} (n : ℕ) (x : Fin d → ℝ) (hx : ‖x‖ ≤ 2) :
    ‖x - quantizer n x‖ ≤ 1 / ((n : ℝ)+1) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  have hk : |x k| ≤ 2 := (norm_le_pi_norm x k).trans hx
  exact scalarQuantizer_error n (x k) hk
lemma quantizer_integrable {d : ℕ} (n : ℕ) (P : Measure (Fin d → ℝ))
    [IsFiniteMeasure P] : Integrable (@quantizer d n) P := by
  let s : SimpleFunc (Fin d → ℝ) (Fin d → ℝ) :=
    ⟨quantizer n,fun a => quantizer_measurable n (measurableSet_singleton a),quantizer_finiteRange n⟩
  exact s.integrable_of_isFiniteMeasure
lemma bounded_identity_integrable {d : ℕ} (P : Measure (Fin d → ℝ)) [IsFiniteMeasure P]
    (hb : ∀ᵐ x ∂P, ‖x‖ ≤ 2) : Integrable (fun x : Fin d → ℝ => x) P :=
  Integrable.of_bound measurable_id.aestronglyMeasurable 2 hb
lemma quantizer_L1_error {d : ℕ} (n : ℕ) (P : Measure (Fin d → ℝ))
    [IsProbabilityMeasure P] (hb : ∀ᵐ x ∂P, ‖x‖ ≤ 2) :
    (∫ x, ‖x - quantizer n x‖ ∂P) ≤ 1 / ((n : ℝ)+1) := by
  have hi := (bounded_identity_integrable P hb).sub (quantizer_integrable n P)
  have hh := integral_mono_ae hi.norm (integrable_const (1 / ((n : ℝ)+1)))
    (hb.mono (fun x hx => quantizer_error n x hx))
  simpa using hh
end StrassenStQuantization
#print axioms StrassenStQuantization.scalarQuantizer_measurable
#print axioms StrassenStQuantization.quantizer_measurable
#print axioms StrassenStQuantization.scalarQuantizer_monotone
#print axioms StrassenStQuantization.quantizer_monotone
#print axioms StrassenStQuantization.quantizer_finiteRange
#print axioms StrassenStQuantization.scalarQuantizer_error
#print axioms StrassenStQuantization.quantizer_error
#print axioms StrassenStQuantization.quantizer_integrable
#print axioms StrassenStQuantization.bounded_identity_integrable
#print axioms StrassenStQuantization.quantizer_L1_error

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators Classical
/- Adapted from the accepted scalar convex-risk Strassen solution in the sibling workspace.
   The first five finite-law definitions/proofs are unchanged; representation and payoff
   are generalized from ℝ to an arbitrary measurable singleton space. -/
namespace MultivariateStrassenLaw
noncomputable def finiteLaw {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (x : ι → α) (p : ι → ℝ) : Measure α :=
  Measure.sum (fun i => ENNReal.ofReal (p i) • Measure.dirac (x i))

lemma finiteLaw_apply {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (s : Set α) :
    finiteLaw x p s = ∑ i, if x i ∈ s then ENNReal.ofReal (p i) else 0 := by
  classical
  simp [finiteLaw, Measure.sum_apply_of_countable, tsum_fintype, indicator_apply]

lemma finiteLaw_integrable {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (f : α → ℝ) : Integrable f (finiteLaw x p) := by
  apply integrable_sum_dirac (fun i => ENNReal.ofReal_ne_top)
  exact summable_of_hasFiniteSupport (Set.toFinite _)

lemma finiteLaw_integral {α ι : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype ι] (x : ι → α) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (f : α → ℝ) :
    (∫ z, f z ∂finiteLaw x p) = ∑ i, p i * f (x i) := by
  rw [finiteLaw, integral_sum_dirac (fun i => ENNReal.ofReal_ne_top), tsum_fintype]
  simp [ENNReal.toReal_ofReal (hp _), smul_eq_mul]

lemma finiteLaw_probability {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (x : ι → α) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteLaw x p) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hp
  rw [← hsum]
  exact hasSum_fintype p

lemma positive_atomic_representation {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : Finset α) (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ T : Finset α, T.Nonempty ∧
      (∀ a ∈ T, 0 < (μ {a}).toReal) ∧
      (∑ a ∈ T, (μ {a}).toReal) = 1 ∧
      μ = finiteLaw (fun a : T => (a : α)) (fun a : T => (μ {(a : α)}).toReal) := by
  classical
  let T := S.filter (fun a => 0 < μ {a})
  have he : μ = ∑ a ∈ T, μ {a} • Measure.dirac a := by
    calc
      μ = ∑ a ∈ S, μ {a} • Measure.dirac a := Measure.ae_mem_finset_iff.mp hS
      _ = ∑ a ∈ T, μ {a} • Measure.dirac a := ?_
    apply (sum_subset (filter_subset _ _) ?_).symm
    intro a ha hn
    have hz : μ {a} = 0 := by
      have : ¬0 < μ {a} := by simpa [T, ha] using hn
      exact le_zero_iff.mp (le_of_not_gt this)
    simp [hz]
  have hne : T.Nonempty := by
    by_contra hn
    have ht : T = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [ht] at he
    have hu := congrArg (fun ν : Measure α => ν univ) he
    simpa using hu
  have hpos : ∀ a ∈ T, 0 < (μ {a}).toReal := by
    intro a ha
    exact ENNReal.toReal_pos (mem_filter.mp ha).2.ne' (measure_ne_top _ _)
  have hrep : μ = finiteLaw (fun a : T => (a : α)) (fun a : T => (μ {(a : α)}).toReal) := by
    calc
      μ = ∑ a ∈ T, μ {a} • Measure.dirac a := he
      _ = ∑ a : T, μ {(a : α)} • Measure.dirac (a : α) :=
        (Finset.sum_coe_sort T (fun a : α => μ {a} • Measure.dirac a)).symm
      _ = finiteLaw (fun a : T => (a : α)) (fun a : T => (μ {(a : α)}).toReal) := by
        rw [finiteLaw, Measure.sum_fintype]
        apply sum_congr rfl
        intro a _
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ⟨T, hne, hpos, ?_, hrep⟩
  have hi := finiteLaw_integral (fun a : T => (a : α))
    (fun a : T => (μ {(a : α)}).toReal) (fun a => ENNReal.toReal_nonneg) (fun _ => (1 : ℝ))
  rw [← hrep] at hi
  rw [← Finset.sum_coe_sort T (fun a : α => (μ {a}).toReal)]
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] using hi.symm

lemma finite_range_law {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Ω → α) (hmA : Measurable A) (hFA : (range A).Finite) :
    ∃ T : Finset α, T.Nonempty ∧
      (∀ a ∈ T, 0 < ((P.map A) {a}).toReal) ∧
      (∑ a ∈ T, ((P.map A) {a}).toReal) = 1 ∧
      P.map A = finiteLaw (fun a : T => (a : α)) (fun a : T => ((P.map A) {(a : α)}).toReal) := by
  classical
  let : IsProbabilityMeasure (P.map A) := Measure.isProbabilityMeasure_map hmA.aemeasurable
  let S := hFA.toFinset
  have hS : ∀ᵐ a ∂P.map A, a ∈ S := by
    apply (ae_map_iff hmA.aemeasurable S.measurableSet).mpr
    filter_upwards with ω
    change A ω ∈ hFA.toFinset
    exact hFA.mem_toFinset.mpr ⟨ω, rfl⟩
  exact positive_atomic_representation (P.map A) S hS

lemma payoff_of_finite_law {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype ι]
    (P : Measure Ω) (A : Ω → α) (hmA : Measurable A) (x : ι → α) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hrep : P.map A = finiteLaw x p)
    (φ : α → ℝ) (hφ : Measurable φ) :
    (∫ ω, φ (A ω) ∂P) = ∑ i, p i * φ (x i) := by
  calc
    (∫ ω, φ (A ω) ∂P) = ∫ z, φ z ∂P.map A :=
      (integral_map_of_stronglyMeasurable hmA hφ.stronglyMeasurable).symm
    _ = _ := by rw [hrep]; exact finiteLaw_integral x p hp φ

end MultivariateStrassenLaw
#print axioms MultivariateStrassenLaw.finiteLaw_apply
#print axioms MultivariateStrassenLaw.finiteLaw_integrable
#print axioms MultivariateStrassenLaw.finiteLaw_integral
#print axioms MultivariateStrassenLaw.finiteLaw_probability
#print axioms MultivariateStrassenLaw.positive_atomic_representation
#print axioms MultivariateStrassenLaw.finite_range_law
#print axioms MultivariateStrassenLaw.payoff_of_finite_law

set_option autoImplicit false
open scoped BigOperators
namespace RiskOrderFinite.Duality

/-!
# Finitely generated convex cones and primitive cones

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007,
§6.4, p. 89 (convex cone generated by `a₁, …, aₙ`) and §6.5, p. 96 (primitive cone).
Points of `ℝ^m` are elements of `EuclideanSpace ℝ (Fin m)`, so distances are Euclidean.
-/

variable {m n : ℕ}

/-- The **convex cone generated by** `a₁, …, aₙ ∈ ℝ^m` (p. 89): the set of all linear
combinations `t₁a₁ + ⋯ + tₙaₙ` with `t₁, …, tₙ ≥ 0`.  For `n = 0` it is `{0}`. -/
def coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ t : Fin n → ℝ, (∀ i, 0 ≤ t i) ∧ x = ∑ i, t i • a i}

/-- A **primitive cone** in `ℝ^m` (p. 96): a convex cone generated by some `k ≤ m` linearly
independent vectors (`k = 0` gives `{0}`). -/
def IsPrimitiveCone (P : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ k : ℕ, k ≤ m ∧ ∃ v : Fin k → EuclideanSpace ℝ (Fin m),
    LinearIndependent ℝ v ∧ P = coneGen v

end RiskOrderFinite.Duality

open Finset

namespace RiskOrderConicCara

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

/-- Conic Carathéodory: a nonnegative combination of `a` is a nonnegative combination of a
linearly independent subfamily. -/
theorem exists_linIndep_repr (a : Fin n → E) :
    ∀ (k : ℕ) (t : Fin n → ℝ), (∀ i, 0 ≤ t i) → (univ.filter fun i => t i ≠ 0).card ≤ k →
      ∃ (S : Finset (Fin n)) (s : Fin n → ℝ), (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧
        LinearIndependent ℝ (fun i : S => a i) ∧ ∑ i, s i • a i = ∑ i, t i • a i := by
  intro k
  induction k with
  | zero =>
    intro t ht hk
    refine ⟨∅, t, ht, fun i _ => ?_, linearIndependent_empty_type, rfl⟩
    by_contra h
    have : i ∈ univ.filter fun i => t i ≠ 0 := by simp [h]
    simp_all
  | succ k ih =>
    intro t ht hk
    set T := univ.filter fun i => t i ≠ 0 with hT
    by_cases hli : LinearIndependent ℝ (fun i : T => a i)
    · refine ⟨T, t, ht, fun i hi => ?_, hli, rfl⟩
      by_contra h; exact hi (by simp [T, h])
    · -- a nontrivial dependency supported on T
      obtain ⟨g, hg, j, hj⟩ := Fintype.not_linearIndependent_iff.mp hli
      -- extend to Fin n, possibly negating so that some coefficient is positive
      have hpos : ∃ μ : Fin n → ℝ, (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • a i = 0 ∧ ∃ i, 0 < μ i := by
        set μ0 : Fin n → ℝ := fun i => if h : i ∈ T then g ⟨i, h⟩ else 0
        have hsum : ∑ i, μ0 i • a i = 0 := by
          rw [← hg]
          rw [← Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by simp [μ0, hi])]
          rw [← Finset.sum_coe_sort T]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [μ0, i.2]
        have hsupp : ∀ i, i ∉ T → μ0 i = 0 := fun i hi => by simp [μ0, hi]
        have hj' : μ0 j ≠ 0 := by simp [μ0, j.2, hj]
        rcases lt_or_gt_of_ne hj' with hneg | hpos
        · refine ⟨-μ0, fun i hi => by simp [hsupp i hi], by simp [neg_smul, hsum], j, by simpa using hneg⟩
        · exact ⟨μ0, hsupp, hsum, j, hpos⟩
      obtain ⟨μ, hμT, hμsum, i₀, hi₀⟩ := hpos
      -- choose the ratio-minimizing positive coordinate
      set P := univ.filter fun i => 0 < μ i
      have hPne : P.Nonempty := ⟨i₀, by simp [P, hi₀]⟩
      obtain ⟨j₀, hj₀P, hj₀min⟩ := P.exists_min_image (fun i => t i / μ i) hPne
      have hμj₀ : 0 < μ j₀ := (Finset.mem_filter.mp hj₀P).2
      set θ := t j₀ / μ j₀
      have hθ : 0 ≤ θ := div_nonneg (ht j₀) hμj₀.le
      set t' : Fin n → ℝ := fun i => t i - θ * μ i
      have ht' : ∀ i, 0 ≤ t' i := by
        intro i
        by_cases hi : 0 < μ i
        · have := hj₀min i (by simp [P, hi])
          rw [div_le_div_iff₀ hμj₀ hi] at this
          simp only [t', sub_nonneg, θ]
          rw [div_mul_eq_mul_div, div_le_iff₀ hμj₀]
          linarith
        · push_neg at hi
          simp only [t']
          nlinarith [ht i]
      have ht'j₀ : t' j₀ = 0 := by simp [t', θ, div_mul_cancel₀ _ hμj₀.ne']
      have hsubset : (univ.filter fun i => t' i ≠ 0) ⊆ T := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hti
        apply hi
        have hti' : t i = 0 := by simpa [T] using hti
        have hμi : μ i = 0 := hμT i hti
        simp [t', hti', hμi]
      have hj₀T : j₀ ∈ T := by
        by_contra h
        have hμj₀0 : μ j₀ = 0 := hμT j₀ h
        linarith
      have hsub : (univ.filter fun i => t' i ≠ 0) ⊂ T :=
        (Finset.ssubset_iff_of_subset hsubset).mpr ⟨j₀, hj₀T, by simp [ht'j₀]⟩
      have hcard : (univ.filter fun i => t' i ≠ 0).card ≤ k := by
        have := Finset.card_lt_card hsub; omega
      obtain ⟨S, s, hs, hsS, hSli, hsum⟩ := ih t' ht' hcard
      refine ⟨S, s, hs, hsS, hSli, ?_⟩
      rw [hsum]
      simp only [t', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμsum,
        smul_zero, sub_zero]

end RiskOrderConicCara

namespace RiskOrderConeAux

open RiskOrderFinite.Duality

variable {m n : ℕ}

/-- The cone generated by the subfamily indexed by `S`, as supported combinations. -/
def subCone (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ s : Fin n → ℝ, (∀ i, 0 ≤ s i) ∧ (∀ i, i ∉ S → s i = 0) ∧ x = ∑ i, s i • a i}

lemma subCone_subset (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    subCone a S ⊆ coneGen a := by
  rintro x ⟨s, hs, -, rfl⟩; exact ⟨s, hs, rfl⟩

/-- A linearly independent subfamily generates a primitive cone. -/
lemma subCone_primitive (a : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n))
    (hS : LinearIndependent ℝ (fun i : S => a i)) : IsPrimitiveCone (subCone a S) := by
  classical
  set σ : Fin S.card ≃o S := S.orderIsoOfFin rfl
  set v : Fin S.card → EuclideanSpace ℝ (Fin m) := fun r => a (σ r)
  have hv : LinearIndependent ℝ v := hS.comp σ σ.injective
  refine ⟨S.card, ?_, v, hv, ?_⟩
  · have := hv.fintype_card_le_finrank
    simpa using this
  · ext x
    constructor
    · rintro ⟨s, hs, hsS, rfl⟩
      refine ⟨fun r => s (σ r), fun r => hs _, ?_⟩
      rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hsS i hi])]
      rw [← Finset.sum_coe_sort S]
      exact (Equiv.sum_comp σ.toEquiv (fun i : S => s i • a i)).symm
    · rintro ⟨t, ht, rfl⟩
      set s : Fin n → ℝ := fun i => if h : i ∈ S then t (σ.symm ⟨i, h⟩) else 0
      refine ⟨s, fun i => ?_, fun i hi => by simp [s, hi], ?_⟩
      · simp only [s]; split_ifs <;> simp [ht]
      · rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [s, hi])]
        rw [← Finset.sum_coe_sort S]
        rw [← Equiv.sum_comp σ.toEquiv (fun i : S => s i • a i)]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [s, v]

/-- Every finitely generated cone is the union of the primitive cones of its linearly independent
subfamilies. -/
lemma coneGen_eq_iUnion (a : Fin n → EuclideanSpace ℝ (Fin m)) :
    coneGen a = ⋃ (S : Finset (Fin n)) (_ : LinearIndependent ℝ (fun i : S => a i)),
      subCone a S := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨S, s, hs, hsS, hli, hsum⟩ :=
      RiskOrderConicCara.exists_linIndep_repr a _ t ht le_rfl
    exact ⟨S, hli, s, hs, hsS, hsum.symm⟩
  · rintro ⟨S, -, hx⟩; exact subCone_subset a S hx

lemma isClosed_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : IsClosed (coneGen a) := by
  classical
  rw [coneGen_eq_iUnion]
  refine isClosed_iUnion_of_finite fun S => isClosed_iUnion_of_finite fun hli => ?_
  obtain ⟨k, -, v, hv, hP⟩ := subCone_primitive a S hli
  rw [hP]
  -- a primitive cone is closed (image of the orthant under a closed embedding)
  set L : (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Fintype.linearCombination ℝ v
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  have himage : coneGen v = L '' {t | ∀ i, 0 ≤ t i} := by
    ext x
    simp only [coneGen, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
  rw [himage]
  apply (LinearMap.isClosedEmbedding_of_injective hL).isClosedMap
  have : {t : Fin k → ℝ | ∀ i, 0 ≤ t i} = ⋂ i, {t | 0 ≤ t i} := by ext; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

lemma zero_mem_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : (0 : _) ∈ coneGen a :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma convex_coneGen (a : Fin n → EuclideanSpace ℝ (Fin m)) : Convex ℝ (coneGen a) := by
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ α β hα hβ -
  refine ⟨fun i => α * s i + β * t i, fun i => by have := hs i; have := ht i; positivity, ?_⟩
  simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]

end RiskOrderConeAux

open RiskOrderFinite.Duality RiskOrderConeAux in
theorem riskOrderFarkasGeometric {m n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    Xor (b ∈ coneGen a)
      (∃ y : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ inner ℝ y (a i)) ∧ inner ℝ y b < 0) := by
  by_cases hb : b ∈ coneGen a
  · -- no separating vector exists
    refine Or.inl ⟨hb, ?_⟩
    rintro ⟨y, hy, hyb⟩
    obtain ⟨t, ht, rfl⟩ := hb
    have : 0 ≤ inner ℝ y (∑ i, t i • a i) := by
      rw [inner_sum]
      exact Finset.sum_nonneg fun i _ => by rw [inner_smul_right]; exact mul_nonneg (ht i) (hy i)
    linarith
  · refine Or.inr ⟨?_, hb⟩
    -- nearest point z of the closed convex cone; y = z - b separates
    obtain ⟨z, hz, hdist⟩ := (isClosed_coneGen a).exists_infDist_eq_dist ⟨0, zero_mem_coneGen a⟩ b
    have hmin : ‖b - z‖ = ⨅ w : coneGen a, ‖b - w‖ := by
      rw [← dist_eq_norm, ← hdist, Metric.infDist_eq_iInf]
      simp [dist_eq_norm]
    have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_coneGen a) hz).mp hmin
    -- variational inequality: ⟪b - z, w - z⟫ ≤ 0 for all w in the cone
    have hai : ∀ i, inner ℝ (b - z) (a i) ≤ 0 := by
      intro i
      obtain ⟨s, hs, rfl⟩ := hz
      have hw : (∑ j, s j • a j) + a i ∈ coneGen a :=
        ⟨fun j => s j + if j = i then 1 else 0, fun j => by
          show 0 ≤ s j + (if j = i then (1 : ℝ) else 0)
          have := hs j; split_ifs <;> linarith,
          by simp [add_smul, Finset.sum_add_distrib, Finset.sum_ite_eq']⟩
      simpa using hvar _ hw
    have hz0 : inner ℝ (b - z) z = 0 := by
      have h0 := hvar 0 (zero_mem_coneGen a)
      have h2 : (2 : ℝ) • z ∈ coneGen a := by
        obtain ⟨s, hs, hzs⟩ := hz
        exact ⟨fun j => 2 * s j, fun j => by have := hs j; positivity, by
          simp [hzs, Finset.smul_sum, mul_smul]⟩
      have h2' := hvar _ h2
      simp only [zero_sub, inner_neg_right] at h0
      rw [show (2 : ℝ) • z - z = z by module] at h2'
      linarith
    have hne : b - z ≠ 0 := by
      intro h; apply hb; rw [sub_eq_zero.mp h]; exact hz
    refine ⟨z - b, fun i => ?_, ?_⟩
    · have := hai i
      rw [show z - b = -(b - z) by abel, inner_neg_left]; linarith
    · have hpos : 0 < inner ℝ (b - z) (b - z) := real_inner_self_pos.mpr hne
      have hsplit : inner ℝ (b - z) b = inner ℝ (b - z) (b - z) + inner ℝ (b - z) z := by
        rw [← inner_add_right]; congr 1; abel
      rw [show z - b = -(b - z) by abel, inner_neg_left, hsplit, hz0]
      linarith

namespace RiskOrderFarkas

open Matrix RiskOrderFinite.Duality RiskOrderConeAux

/-- Farkas' lemma, equational form: `Ax = b, x ≥ 0` is solvable iff every `y` with `Aᵀy ≥ 0`
has `yᵀb ≥ 0`. -/
theorem farkas_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro h
    set a : Fin n → EuclideanSpace ℝ (Fin m) := fun j => WithLp.toLp 2 (fun i => A i j)
    rcases riskOrderFarkasGeometric a (WithLp.toLp 2 b) with ⟨hb, -⟩ | ⟨⟨y, hy, hyb⟩, -⟩
    · obtain ⟨t, ht, hbt⟩ := hb
      refine ⟨t, fun i => ht i, ?_⟩
      have hb' : b = ∑ j, t j • (fun i => A i j) := by
        have := congrArg WithLp.ofLp hbt
        simpa [a, WithLp.ofLp_sum, WithLp.ofLp_smul] using this
      rw [hb']
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · exfalso
      set y' : Fin m → ℝ := WithLp.ofLp y
      have hy' : 0 ≤ Aᵀ *ᵥ y' := by
        intro j
        have := hy j
        simp only [a] at this
        have hy_eq : y = WithLp.toLp 2 y' := rfl
        rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at this
        simpa [mulVec, dotProduct, transpose_apply, mul_comm] using this
      have := h y' hy'
      have hy_eq : y = WithLp.toLp 2 y' := rfl
      rw [hy_eq, EuclideanSpace.inner_toLp_toLp] at hyb
      simp only [star_trivial] at hyb
      rw [dotProduct_comm] at hyb
      linarith


/-- `farkas_eq` for an arbitrary finite column index. -/
theorem farkas_eq_fintype {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ι
  set A' : Matrix (Fin m) (Fin (Fintype.card ι)) ℝ := A.submatrix id e.symm
  have hmul : ∀ x : ι → ℝ, A' *ᵥ (x ∘ e.symm) = A *ᵥ x := by
    intro x; funext i
    simp only [A', mulVec, dotProduct, submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp e.symm (fun j => A i j * x j)
  have htr : ∀ y : Fin m → ℝ, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := by
    intro y; funext j; simp [A', mulVec, dotProduct, transpose_apply]
  have hnonneg : ∀ y : Fin m → ℝ, (0 ≤ A'ᵀ *ᵥ y ↔ 0 ≤ Aᵀ *ᵥ y) := by
    intro y; rw [htr]
    constructor
    · intro h j; simpa using h (e j)
    · intro h j; exact h _
  rw [show (∀ y : Fin m → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) ↔
      (∀ y : Fin m → ℝ, 0 ≤ A'ᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b) from
      forall_congr' fun y => by rw [hnonneg]]
  rw [← farkas_eq A' b]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x ∘ e.symm, fun j => hx _, hmul x⟩
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x' ∘ e, fun j => hx' _, ?_⟩
    rw [← hmul]; congr 1; funext j; simp


/-- Farkas, equational form, arbitrary finite row and column index types. -/
theorem farkas_eq_gen {ρ ι : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype ι] [DecidableEq ι]
    (A : Matrix ρ ι ℝ) (b : ρ → ℝ) :
    (∃ x : ι → ℝ, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y : ρ → ℝ, 0 ≤ Aᵀ *ᵥ y → 0 ≤ y ⬝ᵥ b := by
  set e := Fintype.equivFin ρ
  set A' : Matrix (Fin (Fintype.card ρ)) ι ℝ := A.submatrix e.symm id
  have h := farkas_eq_fintype A' (b ∘ e.symm)
  have hrow : ∀ x : ι → ℝ, A' *ᵥ x = (A *ᵥ x) ∘ e.symm := by
    intro x; funext r; simp [A', mulVec, dotProduct]
  have hcol : ∀ y' : Fin (Fintype.card ρ) → ℝ, A'ᵀ *ᵥ y' = Aᵀ *ᵥ (y' ∘ e) := by
    intro y'; funext j
    simp only [A', mulVec, dotProduct, transpose_apply, submatrix_apply, id, Function.comp]
    rw [← Equiv.sum_comp e (fun x => A (e.symm x) j * y' x)]
    simp
  have hdot : ∀ y' : Fin (Fintype.card ρ) → ℝ, y' ⬝ᵥ (b ∘ e.symm) = (y' ∘ e) ⬝ᵥ b := by
    intro y'
    simp only [dotProduct, Function.comp]
    rw [← Equiv.sum_comp e (fun x => y' x * b (e.symm x))]
    simp
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    exact dotProduct_nonneg_of_nonneg hx hy
  · intro hy
    obtain ⟨x, hx, hAx⟩ := h.mpr fun y' hy' => by
      rw [hcol] at hy'; rw [hdot]; exact hy _ hy'
    refine ⟨x, hx, ?_⟩
    funext r
    have := congrFun hAx (e r)
    rw [hrow] at this; simpa using this

end RiskOrderFarkas
#print axioms RiskOrderFarkas.farkas_eq_gen

set_option autoImplicit false
open Finset PalmQueueing.Ordering MeasureTheory
open scoped BigOperators
namespace StrassenStFinite
noncomputable def upperEnvelope {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) (t : Fin d → ℝ) : ℝ := by
  classical
  exact univ.sup' univ_nonempty (fun i => if CoordLe (x i) t then -a i else B)

lemma upperEnvelope_coordMonotone {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) (hB : ∀ i, B ≤ -a i) :
    ∀ t u, CoordLe t u → upperEnvelope x a B t ≤ upperEnvelope x a B u := by
  classical
  intro t u htu
  unfold upperEnvelope
  apply sup'_le
  intro i _
  have hu := le_sup' (fun i => if CoordLe (x i) u then -a i else B) (mem_univ i)
  by_cases hi : CoordLe (x i) t
  · have hiu : CoordLe (x i) u := fun k => (hi k).trans (htu k)
    simpa only [hi,hiu,↓reduceIte] using hu
  · simp only [hi,↓reduceIte]
    by_cases hiu : CoordLe (x i) u
    · simp only [hiu,↓reduceIte] at hu
      exact (hB i).trans hu
    · simpa only [hiu,↓reduceIte] using hu

lemma upperEnvelope_mem_classI {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) (hB : ∀ i, B ≤ -a i) :
    upperEnvelope x a B ∈ classI d := upperEnvelope_coordMonotone x a B hB

lemma source_le_upperEnvelope {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) (i : ι) :
    -a i ≤ upperEnvelope x a B (x i) := by
  classical
  have hh := le_sup' (fun j => if CoordLe (x j) (x i) then -a j else B) (mem_univ i)
  have hi : CoordLe (x i) (x i) := fun _ => le_rfl
  simpa only [hi,↓reduceIte,upperEnvelope] using hh

lemma upperEnvelope_le_destination {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Nonempty ι] (x : ι → Fin d → ℝ) (y : κ → Fin d → ℝ)
    (a : ι → ℝ) (b : κ → ℝ) (B : ℝ) (hB : ∀ j, B ≤ b j)
    (hab : ∀ i j, CoordLe (x i) (y j) → 0 ≤ a i+b j) :
    ∀ j, upperEnvelope x a B (y j) ≤ b j := by
  classical
  intro j
  unfold upperEnvelope
  apply sup'_le
  intro i _
  by_cases hi : CoordLe (x i) (y j)
  · simp only [hi,↓reduceIte]
    linarith [hab i j hi]
  · simp only [hi,↓reduceIte]
    exact hB j

lemma isClosed_coord_upper {d : ℕ} (x : Fin d → ℝ) :
    IsClosed {t : Fin d → ℝ | CoordLe x t} := by
  change IsClosed {t : Fin d → ℝ | ∀ k, x k ≤ t k}
  convert isClosed_iInter (fun k : Fin d => isClosed_le (continuous_const : Continuous (fun _ : Fin d → ℝ => x k)) (continuous_apply k)) using 1
  ext t
  simp only [Set.mem_ofPred_eq,Set.mem_iInter]

lemma finite_sup_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => univ.sup' univ_nonempty (fun i => f i ω)) := by
  classical
  have hmain : ∀ (s : Finset ι) (hs : s.Nonempty),
      Measurable (fun ω => s.sup' hs (fun i => f i ω)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro hs; exact False.elim (not_nonempty_empty hs)
    | insert i s hnot ih =>
      intro hs
      by_cases hS : s.Nonempty
      · simp_rw [sup'_insert hS]
        exact (hf i).sup (ih hS)
      · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hS
        subst s
        simpa using hf i
  exact hmain univ univ_nonempty

lemma upperEnvelope_measurable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) : Measurable (upperEnvelope x a B) := by
  classical
  unfold upperEnvelope
  apply finite_sup_measurable
  intro i
  exact measurable_const.ite (isClosed_coord_upper (x i)).measurableSet measurable_const

lemma upperEnvelope_bounded {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |upperEnvelope x a B t| ≤ C := by
  classical
  let C := ‖a‖+|B|
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hv : ∀ i t, |if CoordLe (x i) t then -a i else B| ≤ C := by
    intro i t
    have hi : |a i| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i
    by_cases ht : CoordLe (x i) t
    · simpa only [ht,↓reduceIte,abs_neg] using hi.trans (le_add_of_nonneg_right (abs_nonneg B))
    · simpa only [ht,↓reduceIte] using (le_add_of_nonneg_left (norm_nonneg a) : |B| ≤ ‖a‖+|B|)
  refine ⟨C,hC,?_⟩
  intro t
  unfold upperEnvelope
  apply abs_le.mpr
  constructor
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ((abs_le.mp (hv i t)).1).trans (le_sup' (fun i => if CoordLe (x i) t then -a i else B) (mem_univ i))
  · apply sup'_le
    intro i _
    exact (le_abs_self _).trans (hv i t)

lemma upperEnvelope_integrable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : Measure (Fin d → ℝ)) [IsFiniteMeasure F]
    (x : ι → Fin d → ℝ) (a : ι → ℝ) (B : ℝ) : Integrable (upperEnvelope x a B) F := by
  obtain ⟨C,hC,hb⟩ := upperEnvelope_bounded x a B
  apply (integrable_const C).mono' (upperEnvelope_measurable x a B).aestronglyMeasurable
  exact ae_of_all F (fun t => by simpa only [Real.norm_eq_abs] using hb t)

end StrassenStFinite
#print axioms StrassenStFinite.upperEnvelope_coordMonotone
#print axioms StrassenStFinite.upperEnvelope_mem_classI
#print axioms StrassenStFinite.source_le_upperEnvelope
#print axioms StrassenStFinite.upperEnvelope_le_destination
#print axioms StrassenStFinite.isClosed_coord_upper

#print axioms StrassenStFinite.finite_sup_measurable
#print axioms StrassenStFinite.upperEnvelope_measurable
#print axioms StrassenStFinite.upperEnvelope_bounded
#print axioms StrassenStFinite.upperEnvelope_integrable

set_option autoImplicit false
open Finset Matrix PalmQueueing.Ordering
open scoped BigOperators
namespace StrassenStFinite
noncomputable def orderedMatrix {d : ℕ} {ι κ : Type*}
    (x : ι → Fin d → ℝ) (y : κ → Fin d → ℝ) :
    Matrix (ι ⊕ (κ ⊕ (ι × κ))) (ι × κ) ℝ := by
  classical
  exact fun r ij => match r with
    | Sum.inl i => if i=ij.1 then 1 else 0
    | Sum.inr (Sum.inl j) => if j=ij.2 then 1 else 0
    | Sum.inr (Sum.inr (i,j)) =>
      if i=ij.1 then if j=ij.2 then if CoordLe (x i) (y j) then 0 else 1 else 0 else 0

def orderedRhs {ι κ : Type*} (p : ι → ℝ) (q : κ → ℝ) : (ι ⊕ (κ ⊕ (ι × κ))) → ℝ
  | Sum.inl i => p i
  | Sum.inr (Sum.inl j) => q j
  | Sum.inr (Sum.inr _) => 0

lemma finite_ordered_feasible {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (x : ι → Fin d → ℝ) (y : κ → Fin d → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ f ∈ classI d, (∑ i, p i*f (x i)) ≤ ∑ j, q j*f (y j)) :
    ∃ c, 0 ≤ c ∧ orderedMatrix x y *ᵥ c = orderedRhs p q := by
  classical
  apply (RiskOrderFarkas.farkas_eq_gen (orderedMatrix x y) (orderedRhs p q)).mpr
  intro w hw
  let a : ι → ℝ := fun i => w (Sum.inl i)
  let b : κ → ℝ := fun j => w (Sum.inr (Sum.inl j))
  have hab : ∀ i j, CoordLe (x i) (y j) → 0 ≤ a i+b j := by
    intro i j hij
    have hh := hw (i,j)
    simpa [orderedMatrix,mulVec,dotProduct,transpose_apply,Fintype.sum_sum_type,
      Fintype.sum_prod_type,a,b,hij,mul_comm] using hh
  let B := min (univ.inf' univ_nonempty (fun i => -a i)) (univ.inf' univ_nonempty b)
  have hBa : ∀ i, B ≤ -a i := fun i =>
    (min_le_left _ _).trans (inf'_le (fun i => -a i) (mem_univ i))
  have hBb : ∀ j, B ≤ b j := fun j =>
    (min_le_right _ _).trans (inf'_le b (mem_univ j))
  let f := upperEnvelope x a B
  have ho := horder f (upperEnvelope_mem_classI x a B hBa)
  have hsrc : (∑ i, p i*(-a i)) ≤ ∑ i, p i*f (x i) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (source_le_upperEnvelope x a B i) (hp i)
  have hdst : (∑ j, q j*f (y j)) ≤ ∑ j, q j*b j :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (upperEnvelope_le_destination x y a b B hBb hab j) (hq j)
  have he : w ⬝ᵥ orderedRhs p q = (∑ i, p i*a i)+(∑ j, q j*b j) := by
    simp [dotProduct,orderedRhs,Fintype.sum_sum_type,a,b,mul_comm]
  rw [he]
  simp only [mul_neg,sum_neg_distrib] at hsrc
  linarith

lemma finite_ordered_transport {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (x : ι → Fin d → ℝ) (y : κ → Fin d → ℝ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (horder : ∀ f ∈ classI d, (∑ i, p i*f (x i)) ≤ ∑ j, q j*f (y j)) :
    ∃ c : ι → κ → ℝ, (∀ i j, 0 ≤ c i j) ∧
      (∀ i, ∑ j, c i j = p i) ∧ (∀ j, ∑ i, c i j = q j) ∧
      ∀ i j, ¬CoordLe (x i) (y j) → c i j = 0 := by
  classical
  obtain ⟨c,hc,he⟩ := finite_ordered_feasible x y p q hp hq horder
  refine ⟨fun i j => c (i,j),fun i j => hc (i,j),?_,?_,?_⟩
  · intro i
    have hh := congrFun he (Sum.inl i)
    simp only [orderedMatrix,orderedRhs,mulVec,dotProduct,Fintype.sum_prod_type] at hh
    rw [Finset.sum_comm] at hh
    simpa [mul_comm] using hh
  · intro j
    have hh := congrFun he (Sum.inr (Sum.inl j))
    simpa [orderedMatrix,orderedRhs,mulVec,dotProduct,Fintype.sum_prod_type,mul_comm,Finset.sum_comm] using hh
  · intro i j hij
    have hh := congrFun he (Sum.inr (Sum.inr (i,j)))
    simpa [orderedMatrix,orderedRhs,mulVec,dotProduct,Fintype.sum_prod_type,hij,mul_comm] using hh
end StrassenStFinite
#print axioms StrassenStFinite.finite_ordered_feasible
#print axioms StrassenStFinite.finite_ordered_transport

set_option autoImplicit false
open MeasureTheory Set Finset PalmQueueing.Ordering MultivariateStrassenLaw
open scoped BigOperators Classical
namespace StrassenStFinite
/- Marginal-law construction adapted from the accepted vector convex-root pair-law proof. -/
lemma matrix_monotone_pair_law {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Fin n → ℝ) (y : κ → Fin n → ℝ) (p : ι → ℝ) (q : κ → ℝ) (c : ι → κ → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hrow : ∀ i, ∑ j, c i j = p i)
    (hcol : ∀ j, ∑ i, c i j = q j)
    (hzero : ∀ i j, ¬CoordLe (x i) (y j) → c i j = 0) (hp : ∑ i, p i = 1) :
    ∃ μ : Measure ((Fin n → ℝ) × (Fin n → ℝ)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = finiteLaw x p ∧ μ.map Prod.snd = finiteLaw y q ∧
      ∀ᵐ z ∂μ, CoordLe z.1 z.2 := by
  classical
  let z : ι × κ → (Fin n → ℝ) × (Fin n → ℝ) := fun ij => (x ij.1, y ij.2)
  let w : ι × κ → ℝ := fun ij => c ij.1 ij.2
  let μ := finiteLaw z w
  have hw : ∀ ij, 0 ≤ w ij := fun ij => hc _ _
  have hsum : ∑ ij, w ij = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [w, hrow] using hp
  refine ⟨μ, finiteLaw_probability z w hw hsum, ?_, ?_, ?_⟩
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply measurable_fst hs, finiteLaw_apply, finiteLaw_apply, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    by_cases hi : x i ∈ s
    · simp only [z, w, Set.mem_preimage, hi, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hc i j), hrow]
    · simp [z, w, hi]
  · apply Measure.ext
    intro s hs
    rw [Measure.map_apply measurable_snd hs, finiteLaw_apply, finiteLaw_apply, Fintype.sum_prod_type, sum_comm]
    apply sum_congr rfl
    intro j _
    by_cases hj : y j ∈ s
    · simp only [z, w, Set.mem_preimage, hj, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hc i j), hcol]
    · simp [z, w, hj]
  · rw [ae_iff]
    change μ {z | ¬CoordLe z.1 z.2} = 0
    rw [finiteLaw_apply]
    apply sum_eq_zero
    intro ij _
    by_cases hij : CoordLe (x ij.1) (y ij.2)
    · simp [z,w,hij]
    · simp [z,w,hij,hzero ij.1 ij.2 hij]

lemma finite_stochastic_coupling {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (x : ι → Fin d → ℝ) (y : κ → Fin d → ℝ) (p : ι → ℝ) (q : κ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (hsum : ∑ i, p i = 1)
    (horder : StLe (finiteLaw x p) (finiteLaw y q)) :
    ∃ μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = finiteLaw x p ∧ μ.map Prod.snd = finiteLaw y q ∧
      ∀ᵐ z ∂μ, CoordLe z.1 z.2 := by
  have ho : ∀ f ∈ classI d, (∑ i, p i*f (x i)) ≤ ∑ j, q j*f (y j) := by
    intro f hf
    have hh := horder f hf (finiteLaw_integrable x p f) (finiteLaw_integrable y q f)
    rw [finiteLaw_integral x p hp,finiteLaw_integral y q hq] at hh
    exact hh
  obtain ⟨c,hc,hrow,hcol,hzero⟩ := finite_ordered_transport x y p q hp hq ho
  exact matrix_monotone_pair_law x y p q c hc hrow hcol hzero hsum
end StrassenStFinite
#print axioms StrassenStFinite.matrix_monotone_pair_law
#print axioms StrassenStFinite.finite_stochastic_coupling

set_option autoImplicit false
open MeasureTheory Filter PalmQueueing.Ordering
open scoped Topology BoundedContinuousFunction
namespace StrassenStLimit
noncomputable def violationTest {d : ℕ} (k : Fin d) : ((Fin d → ℝ) × (Fin d → ℝ)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => min 1 (max 0 (z.1 k-z.2 k)))
    (by fun_prop) 1 (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (by norm_num) (le_max_left _ _))]
      exact min_le_left _ _)

lemma violationTest_nonneg {d : ℕ} (k : Fin d) (z : (Fin d → ℝ) × (Fin d → ℝ)) :
    0 ≤ violationTest k z := le_min (by norm_num) (le_max_left _ _)

lemma violationTest_eq_zero_of_order {d : ℕ} (k : Fin d)
    (z : (Fin d → ℝ) × (Fin d → ℝ)) (hz : CoordLe z.1 z.2) : violationTest k z = 0 := by
  change min (1 : ℝ) (max 0 (z.1 k-z.2 k)) = 0
  rw [max_eq_left (sub_nonpos.mpr (hz k))]
  norm_num

lemma weak_limit_ordered_couplings {d : ℕ}
    (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (horder : ∀ n, ∀ᵐ z ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))), CoordLe z.1 z.2) :
    ∀ᵐ z ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))), CoordLe z.1 z.2 := by
  apply ae_all_iff.mpr
  intro k
  have hi : ∀ n, (∫ z, violationTest k z ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) = 0 := by
    intro n
    apply integral_eq_zero_of_ae
    filter_upwards [horder n] with z hz
    exact violationTest_eq_zero_of_order k z hz
  have hl := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (violationTest k)
  simp_rw [hi] at hl
  have hzero : (∫ z, violationTest k z ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) = 0 :=
    tendsto_nhds_unique hl tendsto_const_nhds
  have hz := (integral_eq_zero_iff_of_nonneg (fun z => violationTest_nonneg k z)
    ((violationTest k).integrable (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))))).mp hzero
  filter_upwards [hz] with z hzero
  by_contra hle
  have hd : 0 < z.1 k-z.2 k := sub_pos.mpr (lt_of_not_ge hle)
  have hp : 0 < min (1 : ℝ) (max 0 (z.1 k-z.2 k)) :=
    lt_min (by norm_num) (hd.trans_le (le_max_right _ _))
  change min (1 : ℝ) (max 0 (z.1 k-z.2 k)) = 0 at hzero
  linarith
end StrassenStLimit
#print axioms StrassenStLimit.violationTest_nonneg
#print axioms StrassenStLimit.violationTest_eq_zero_of_order
#print axioms StrassenStLimit.weak_limit_ordered_couplings

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped BigOperators Topology
/- Adapted from the accepted scalar risk-order Strassen source. Norm moments,
   tightness, and law convergence are generalized to every finite vector dimension;
   pair moment bounds explicitly allow the two distinct original measures. -/
namespace MultivariateStrassenCompactness
lemma integral_norm_le_of_L1_close {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X A : Ω → Fin d → ℝ) (hX : Integrable X P) (hA : Integrable A P)
    (ε : ℝ) (he : (∫ ω, ‖X ω-A ω‖ ∂P) ≤ ε) :
    (∫ ω, ‖A ω‖ ∂P) ≤ (∫ ω, ‖X ω‖ ∂P)+ε := by
  have hb : ∀ ω, ‖A ω‖ ≤ ‖X ω‖+‖X ω-A ω‖ := by
    intro ω
    have hh := norm_add_le (X ω) (A ω-X ω)
    rw [add_sub_cancel] at hh
    simpa only [norm_sub_rev] using hh
  calc
    _ ≤ ∫ ω, ‖X ω‖+‖X ω-A ω‖ ∂P :=
      integral_mono hA.norm (hX.norm.add (hX.sub hA).norm) hb
    _ = (∫ ω, ‖X ω‖ ∂P)+(∫ ω, ‖X ω-A ω‖ ∂P) :=
      integral_add hX.norm (hX.sub hA).norm
    _ ≤ _ := add_le_add le_rfl he

lemma pair_moment_bound {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ω') (X A : Ω → Fin d → ℝ) (Y B : Ω' → Fin d → ℝ)
    (hX : Integrable X P) (hY : Integrable Y Q) (hA : Integrable A P) (hB : Integrable B Q)
    (μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)))
    (hf : IdentDistrib Prod.fst A μ P) (hs : IdentDistrib Prod.snd B μ Q)
    (ε : ℝ) (heA : (∫ ω, ‖X ω-A ω‖ ∂P) ≤ ε) (heB : (∫ ω, ‖Y ω-B ω‖ ∂Q) ≤ ε) :
    Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) μ ∧
      (∫ z, ‖z‖ ∂μ) ≤ (∫ ω, ‖X ω‖ ∂P)+(∫ ω, ‖Y ω‖ ∂Q)+2*ε := by
  have hif : Integrable Prod.fst μ := hf.integrable_iff.mpr hA
  have his : Integrable Prod.snd μ := hs.integrable_iff.mpr hB
  have hn : ∀ z : (Fin d → ℝ) × (Fin d → ℝ), ‖z‖ ≤ ‖z.1‖+‖z.2‖ := by
    intro z
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hi : Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) μ :=
    (hif.norm.add his.norm).mono' continuous_norm.aestronglyMeasurable
      (ae_of_all _ (fun z => by simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hn z))
  refine ⟨hi,?_⟩
  have hfabs := (hf.comp measurable_norm).integral_eq
  have hsabs := (hs.comp measurable_norm).integral_eq
  have hboundA := integral_norm_le_of_L1_close P X A hX hA ε heA
  have hboundB := integral_norm_le_of_L1_close Q Y B hY hB ε heB
  calc
    _ ≤ ∫ z, ‖z.1‖+‖z.2‖ ∂μ := integral_mono hi (hif.norm.add his.norm) hn
    _ = (∫ z, ‖z.1‖ ∂μ)+(∫ z, ‖z.2‖ ∂μ) := integral_add hif.norm his.norm
    _ = (∫ ω, ‖A ω‖ ∂P)+(∫ ω, ‖B ω‖ ∂Q) := congrArg₂ (· + ·) hfabs hsabs
    _ ≤ _ := by linarith

lemma tight_of_bounded_first_moment {d : ℕ} (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n, Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hbound : ∀ n, (∫ z, ‖z‖ ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ C) :
    IsTightMeasureSet (range (fun n => (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases he : ε = ⊤
  · subst ε; exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
  have hepos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' he
  let r := (C + 1) / ε.toReal
  have hr : 0 < r := div_pos (by linarith) hepos
  have hre : r * ε.toReal = C + 1 := div_mul_cancel₀ _ hepos.ne'
  refine ⟨Metric.closedBall (0 : (Fin d → ℝ) × (Fin d → ℝ)) r, isCompact_closedBall _ _, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hsub : (Metric.closedBall (0 : (Fin d → ℝ) × (Fin d → ℝ)) r)ᶜ ⊆ {z : (Fin d → ℝ) × (Fin d → ℝ) | r ≤ ‖z‖} := by
    intro z hz
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hmono := ENNReal.toReal_mono (measure_ne_top (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) _)
    (measure_mono hsub)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) (ae_of_all _ (fun z => norm_nonneg z)) (hint n) r
  have hb : r * ((μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) (Metric.closedBall (0 : (Fin d → ℝ) × (Fin d → ℝ)) r)ᶜ).toReal ≤ C :=
    (mul_le_mul_of_nonneg_left hmono hr.le).trans (hmark.trans (hbound n))
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) he).mp
  nlinarith

lemma subsequence_of_bounded_first_moment {d : ℕ} (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (C : ℝ) (hC : 0 ≤ C)
    (hint : ∀ n, Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖) (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))))
    (hbound : ∀ n, (∫ z, ‖z‖ ∂(μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ C) :
    ∃ ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have ht := tight_of_bounded_first_moment μ C hC hint hbound
  have hs : IsTightMeasureSet {((ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) : Measure ((Fin d → ℝ) × (Fin d → ℝ))) | ν ∈ range μ} := by
    convert ht using 1
    ext ν
    simp only [mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨m, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ν, _, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hs).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨ν, φ, hφ, hlim⟩


lemma tendsto_eLpNorm_one_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (A n - X) 1 P) atTop (𝓝 0) := by
  have hn : ∀ n, eLpNorm (A n - X) 1 P = ENNReal.ofReal (∫ ω, ‖X ω - A n ω‖ ∂P) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm ((hA n).sub hX)]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by simp [norm_sub_rev])
  simp_rw [hn]
  simpa using ENNReal.tendsto_ofReal he

lemma laws_tendsto_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0)) :
    TendstoInDistribution A atTop X (fun _ => P) P := by
  have hn := tendsto_eLpNorm_one_of_L1 P X A hX hA he
  have hi := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 1)
    (by norm_num) (by norm_num) (fun n => (hA n).aestronglyMeasurable)
    hX.aestronglyMeasurable hn
  exact hi.tendstoInDistribution (fun n => (hA n).aemeasurable)

lemma uniform_integrability_of_L1 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0)) :
    UnifIntegrable A 1 P := by
  exact unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num)
    (fun n => (memLp_one_iff_integrable.mpr (hA n))) (memLp_one_iff_integrable.mpr hX) (tendsto_eLpNorm_one_of_L1 P X A hX hA he)

lemma marginal_of_L1_weak_limit {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Fin d → ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (hX : Integrable X P) (hA : ∀ n, Integrable (A n) P)
    (he : Tendsto (fun n => ∫ ω, ‖X ω - A n ω‖ ∂P) atTop (𝓝 0))
    (μ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ))) (ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (hweak : Tendsto (μ ∘ φ) atTop (𝓝 ν))
    (f : (Fin d → ℝ) × (Fin d → ℝ) → Fin d → ℝ) (hf : Continuous f)
    (hmap : ∀ n, (μ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map f = P.map (A n)) :
    (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map f = P.map X := by
  have hd := laws_tendsto_of_L1 P X A hX hA he
  have hds := hd.tendsto.comp hφ.tendsto_atTop
  have hms := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (μ ∘ φ) ν hweak hf
  have heq : (fun n => ((μ ∘ φ) n).map hf.measurable.aemeasurable) =
      (fun n => (⟨P.map (A (φ n)), Measure.isProbabilityMeasure_map (hd.forall_aemeasurable (φ n))⟩ : ProbabilityMeasure (Fin d → ℝ))) := by
    funext n
    apply Subtype.ext
    exact hmap (φ n)
  rw [heq] at hms
  have hu := tendsto_nhds_unique hms hds
  exact congrArg Subtype.val hu

end MultivariateStrassenCompactness
#print axioms MultivariateStrassenCompactness.integral_norm_le_of_L1_close
#print axioms MultivariateStrassenCompactness.pair_moment_bound
#print axioms MultivariateStrassenCompactness.tight_of_bounded_first_moment
#print axioms MultivariateStrassenCompactness.subsequence_of_bounded_first_moment
#print axioms MultivariateStrassenCompactness.tendsto_eLpNorm_one_of_L1
#print axioms MultivariateStrassenCompactness.laws_tendsto_of_L1
#print axioms MultivariateStrassenCompactness.uniform_integrability_of_L1
#print axioms MultivariateStrassenCompactness.marginal_of_L1_weak_limit

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
namespace StrassenStApproximation
lemma finite_range_payoff_measurable {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (A : Ω → α) (hmA : Measurable A) (hFA : (Set.range A).Finite) (f : α → ℝ) :
    Measurable (f ∘ A) := by
  let s : SimpleFunc Ω α := ⟨A,fun a => hmA (measurableSet_singleton a),hFA⟩
  exact (s.map f).measurable

lemma finite_range_payoff_integrable {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure Ω) [IsFiniteMeasure P]
    (A : Ω → α) (hmA : Measurable A) (hFA : (Set.range A).Finite) (f : α → ℝ) :
    Integrable (f ∘ A) P := by
  let s : SimpleFunc Ω α := ⟨A,fun a => hmA (measurableSet_singleton a),hFA⟩
  exact (s.map f).integrable_of_isFiniteMeasure

lemma st_map_of_common_finite_monotone {d : ℕ}
    (F G : Measure (Fin d → ℝ)) [IsFiniteMeasure F] [IsFiniteMeasure G]
    (horder : StLe F G) (A : (Fin d → ℝ) → Fin d → ℝ)
    (hmA : Measurable A) (hFA : (Set.range A).Finite)
    (hmono : ∀ x y, CoordLe x y → CoordLe (A x) (A y)) :
    StLe (F.map A) (G.map A) := by
  intro f hf hiF hiG
  have hc : f ∘ A ∈ classI d := fun x y hxy => hf _ _ (hmono x y hxy)
  have hh := horder (f ∘ A) hc
    (finite_range_payoff_integrable F A hmA hFA f) (finite_range_payoff_integrable G A hmA hFA f)
  rw [integral_map hmA.aemeasurable hiF.aestronglyMeasurable,
    integral_map hmA.aemeasurable hiG.aestronglyMeasurable]
  exact hh
end StrassenStApproximation
#print axioms StrassenStApproximation.finite_range_payoff_measurable
#print axioms StrassenStApproximation.finite_range_payoff_integrable
#print axioms StrassenStApproximation.st_map_of_common_finite_monotone

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Finset PalmQueueing.Ordering
open MultivariateStrassenLaw MultivariateStrassenCompactness
open StrassenStQuantization StrassenStFinite StrassenStApproximation StrassenStLimit
open scoped BigOperators Topology
namespace StrassenStBounded
lemma quantized_monotone_pair {d : ℕ} (F G : Measure (Fin d → ℝ))
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (horder : StLe F G) (n : ℕ) :
    ∃ μ : Measure ((Fin d → ℝ) × (Fin d → ℝ)), IsProbabilityMeasure μ ∧
      μ.map Prod.fst = F.map (quantizer n) ∧ μ.map Prod.snd = G.map (quantizer n) ∧
      ∀ᵐ z ∂μ, CoordLe z.1 z.2 := by
  classical
  obtain ⟨T,hT,hposT,hsumT,hrepT⟩ :=
    finite_range_law F (quantizer n) (quantizer_measurable n) (quantizer_finiteRange n)
  obtain ⟨U,hU,hposU,hsumU,hrepU⟩ :=
    finite_range_law G (quantizer n) (quantizer_measurable n) (quantizer_finiteRange n)
  letI : Nonempty T := hT.to_subtype
  letI : Nonempty U := hU.to_subtype
  have ho := st_map_of_common_finite_monotone F G horder (quantizer n)
    (quantizer_measurable n) (quantizer_finiteRange n) (quantizer_monotone n)
  rw [hrepT,hrepU] at ho
  have hs : ∑ a : T, ((F.map (quantizer n)) {(a : Fin d → ℝ)}).toReal = 1 := by
    rw [← Finset.sum_coe_sort T (fun a : Fin d → ℝ => ((F.map (quantizer n)) {a}).toReal)] at hsumT
    exact hsumT
  obtain ⟨μ,hμ,hf,hg,hxy⟩ := finite_stochastic_coupling
    (fun a : T => (a : Fin d → ℝ)) (fun a : U => (a : Fin d → ℝ))
    (fun a : T => ((F.map (quantizer n)) {(a : Fin d → ℝ)}).toReal)
    (fun a : U => ((G.map (quantizer n)) {(a : Fin d → ℝ)}).toReal)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hs ho
  exact ⟨μ,hμ,hf.trans hrepT.symm,hg.trans hrepU.symm,hxy⟩

lemma bounded_monotone_coupling {d : ℕ} (F G : Measure (Fin d → ℝ))
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (horder : StLe F G)
    (hbF : ∀ᵐ x ∂F, ‖x‖ ≤ 2) (hbG : ∀ᵐ y ∂G, ‖y‖ ≤ 2) :
    ∃ ν : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)),
      (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F ∧
      (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G ∧
      ∀ᵐ z ∂(ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))), CoordLe z.1 z.2 := by
  classical
  choose μ hμ hf hg hxy using (fun n : ℕ => quantized_monotone_pair F G horder n)
  let γ : ℕ → ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) := fun n => ⟨μ n,hμ n⟩
  have hiF := bounded_identity_integrable F hbF
  have hiG := bounded_identity_integrable G hbG
  let C := (∫ x, ‖x‖ ∂F)+(∫ y, ‖y‖ ∂G)+2
  have hC : 0 ≤ C := by
    have h₁ : 0 ≤ ∫ x, ‖x‖ ∂F := integral_nonneg (fun x => norm_nonneg x)
    have h₂ : 0 ≤ ∫ y, ‖y‖ ∂G := integral_nonneg (fun y => norm_nonneg y)
    dsimp only [C]; linarith
  have hb : ∀ n, Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖z‖)
      (γ n : Measure ((Fin d → ℝ) × (Fin d → ℝ))) ∧
      (∫ z, ‖z‖ ∂(γ n : Measure ((Fin d → ℝ) × (Fin d → ℝ)))) ≤ C := by
    intro n
    have hidf : IdentDistrib Prod.fst (quantizer n) (μ n) F :=
      ⟨measurable_fst.aemeasurable,(quantizer_measurable n).aemeasurable,hf n⟩
    have hidg : IdentDistrib Prod.snd (quantizer n) (μ n) G :=
      ⟨measurable_snd.aemeasurable,(quantizer_measurable n).aemeasurable,hg n⟩
    have hh := pair_moment_bound F G (fun x => x) (quantizer n) (fun y => y) (quantizer n)
      hiF hiG (quantizer_integrable n F) (quantizer_integrable n G) (μ n) hidf hidg
      _ (quantizer_L1_error n F hbF) (quantizer_L1_error n G hbG)
    have he : (1 : ℝ)/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    refine ⟨hh.1,hh.2.trans ?_⟩
    dsimp only [C]; linarith
  obtain ⟨ν,φ,hφ,hweak⟩ := subsequence_of_bounded_first_moment γ C hC
    (fun n => (hb n).1) (fun n => (hb n).2)
  have heF : Tendsto (fun n => ∫ x, ‖x-quantizer n x‖ ∂F) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => quantizer_L1_error n F hbF) tendsto_one_div_add_atTop_nhds_zero_nat
  have heG : Tendsto (fun n => ∫ y, ‖y-quantizer n y‖ ∂G) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => quantizer_L1_error n G hbG) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨ν,?_,?_,?_⟩
  · have hh := marginal_of_L1_weak_limit F (fun x => x) quantizer hiF
      (fun n => quantizer_integrable n F) heF γ ν φ hφ hweak Prod.fst continuous_fst hf
    change (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.fst = F.map id at hh
    rw [Measure.map_id] at hh
    exact hh
  · have hh := marginal_of_L1_weak_limit G (fun y => y) quantizer hiG
      (fun n => quantizer_integrable n G) heG γ ν φ hφ hweak Prod.snd continuous_snd hg
    change (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))).map Prod.snd = G.map id at hh
    rw [Measure.map_id] at hh
    exact hh
  · exact weak_limit_ordered_couplings (γ ∘ φ) ν hweak (fun n => hxy (φ n))
end StrassenStBounded
#print axioms StrassenStBounded.quantized_monotone_pair
#print axioms StrassenStBounded.bounded_monotone_coupling

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering StrassenStTransform StrassenStBounded
namespace StrassenStGeneral
lemma original_monotone_coupling {d : ℕ} (F G : Measure (Fin d → ℝ))
    [IsProbabilityMeasure F] [IsProbabilityMeasure G] (horder : StLe F G) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin d → ℝ),
        Measurable X ∧ Measurable Y ∧ P.map X = F ∧ P.map Y = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω) (Y ω) := by
  let FT := F.map boundedTransform
  let GT := G.map boundedTransform
  letI : IsProbabilityMeasure FT := Measure.isProbabilityMeasure_map
    boundedTransform_continuous.measurable.aemeasurable
  letI : IsProbabilityMeasure GT := Measure.isProbabilityMeasure_map
    boundedTransform_continuous.measurable.aemeasurable
  have hb (P : Measure (Fin d → ℝ)) : ∀ᵐ x ∂P.map boundedTransform, ‖x‖ ≤ 2 := by
    apply (ae_map_iff boundedTransform_continuous.measurable.aemeasurable
      (isClosed_le continuous_norm continuous_const).measurableSet).mpr
    apply ae_of_all
    intro x
    have hh := boundedTransform_norm x
    have hp := Real.pi_lt_four
    linarith
  obtain ⟨ν,hf,hg,hxy⟩ := bounded_monotone_coupling FT GT
    (bounded_transform_st F G horder) (hb F) (hb G)
  obtain ⟨hF,hG,horder'⟩ := recover_original_coupling F G
    (ν : Measure ((Fin d → ℝ) × (Fin d → ℝ))) hf hg hxy
  exact ⟨(Fin d → ℝ) × (Fin d → ℝ),inferInstance,ν,inferInstance,
    inverseTransform ∘ Prod.fst,inverseTransform ∘ Prod.snd,
    inverseTransform_measurable.comp measurable_fst,
    inverseTransform_measurable.comp measurable_snd,hF,hG,horder'⟩
end StrassenStGeneral
#print axioms StrassenStGeneral.original_monotone_coupling

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering
namespace StrassenStReverse
lemma monotone_coupling_implies_st {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (F G : Measure (Fin d → ℝ)) (P : Measure Ω) (X Y : Ω → Fin d → ℝ)
    (hmX : Measurable X) (hmY : Measurable Y)
    (hmapX : P.map X = F) (hmapY : P.map Y = G)
    (hXY : ∀ᵐ ω ∂P, CoordLe (X ω) (Y ω)) : StLe F G := by
  intro f hf hiF hiG
  have hFX : Integrable f (P.map X) := hmapX.symm ▸ hiF
  have hFY : Integrable f (P.map Y) := hmapY.symm ▸ hiG
  have hiX := (integrable_map_measure hFX.aestronglyMeasurable hmX.aemeasurable).mp hFX
  have hiY := (integrable_map_measure hFY.aestronglyMeasurable hmY.aemeasurable).mp hFY
  have hpoint : (fun ω => f (X ω)) ≤ᵐ[P] fun ω => f (Y ω) :=
    hXY.mono (fun ω hω => hf _ _ hω)
  have hh := integral_mono_ae hiX hiY hpoint
  change (∫ ω, f (X ω) ∂P) ≤ ∫ ω, f (Y ω) ∂P at hh
  rw [← integral_map hmX.aemeasurable hFX.aestronglyMeasurable,
    ← integral_map hmY.aemeasurable hFY.aestronglyMeasurable,hmapX,hmapY] at hh
  exact hh
end StrassenStReverse
#print axioms StrassenStReverse.monotone_coupling_implies_st

set_option autoImplicit false
open MeasureTheory PalmQueueing.Ordering StrassenStGeneral StrassenStReverse

theorem solution {n : ℕ} (F G : Measure (Fin n → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G) :
    StLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω) (Y ω) := by
  letI : IsProbabilityMeasure F := hF
  letI : IsProbabilityMeasure G := hG
  constructor
  · exact original_monotone_coupling F G
  · rintro ⟨Ω,mΩ,P,hP,X,Y,hmX,hmY,hmapX,hmapY,hxy⟩
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    exact monotone_coupling_implies_st F G P X Y hmX hmY hmapX hmapY hxy

#print axioms solution

namespace PalmQueueing.Ordering

open MeasureTheory

/-- **Theorem 4.2.1 (Strassen's `≤_i` theorem)** (p.277). For `F` and `G` in `𝒟(ℝⁿ)`, `F ≤_i G`
**if and only if** there exist two `ℝⁿ`-valued random variables `X` and `Y` defined on the same
probability space with probability distribution `F` and `G` respectively, and such that `X ≤ Y`
a.s.

The stochastic order holds exactly when the two distributions can be **coupled monotonically**.
This is the pathwise representation that makes the order usable in higher dimensions: "These
representations are particularly useful to establish comparison properties of embedded sequences
in various queueing systems by simple induction arguments, which replace the usual analytical
proofs, based on stability properties of the integral order with respect to convolutions or
products of c.d.f."

Both directions are asserted; the converse — that a monotone coupling gives the order — is
immediate, and the construction of the coupling is the theorem.

In dimension `1` the coupling is explicit and the book gives it: take `U` uniform on `[0,1]` and
set `X = F^{-1}(U)`, `Y = G^{-1}(U)` with `F^{-1}(u) = inf{x; F(x) > u}`. In dimension `n` no such
formula is available, which is why the theorem is Strassen's.

**No integrability hypothesis**, unlike Theorem 4.2.2: the stochastic order does not need first
moments. -/
example {n : ℕ} (F G : Measure (Fin n → ℝ))
    (hF : IsDistribution F) (hG : IsDistribution G) :
    StLe F G ↔
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X Y : Ω → Fin n → ℝ),
        Measurable X ∧ Measurable Y ∧
        Measure.map X P = F ∧ Measure.map Y P = G ∧
        ∀ᵐ ω ∂P, CoordLe (X ω) (Y ω) := by
  exact solution F G hF hG

end PalmQueueing.Ordering

#print axioms solution
