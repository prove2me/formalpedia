-- Prove2me | solution 1 for TalagrandConc.BinPacking.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T04:37:21.722356+00:00
-- url     : https://prove2.me/submissions/8446586e-f9be-4b4e-96f6-bd5e99cb1e89

-- Complete checked reconstruction of the native Talagrand bin-packing concentration theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_TalagrandConc_BinPacking_Basic
import Mathlib


-- Begin Canonical

-- End Canonical

-- Begin GridBasic

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory Filter
open scoped Topology

noncomputable def gridIndex (m : ℕ) (x : unitInterval) : Fin (m + 2) :=
  ⟨⌊((m : ℝ) + 1) * x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (by positivity) x.property.1)).mpr
    have hx := x.property.2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith⟩

noncomputable def gridValue (m : ℕ) (j : Fin (m + 2)) : unitInterval :=
  ⟨(j : ℝ) / ((m : ℝ) + 1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      have hj : j.val ≤ m + 1 := Nat.le_of_lt_succ j.isLt
      exact_mod_cast hj⟩

noncomputable def grid (m : ℕ) (x : unitInterval) : unitInterval :=
  gridValue m (gridIndex m x)

lemma grid_le (m : ℕ) (x : unitInterval) : (grid m x : ℝ) ≤ x := by
  change (⌊((m : ℝ) + 1) * x⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ x
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity) x.property.1)

lemma grid_error (m : ℕ) (x : unitInterval) :
    (x : ℝ) - (grid m x : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
  have h := Nat.lt_floor_add_one (((m : ℝ) + 1) * (x : ℝ))
  change (x : ℝ) - (⌊((m : ℝ) + 1) * x⌋₊ : ℝ) / ((m : ℝ) + 1) ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  have hd : (⌊((m : ℝ) + 1) * x⌋₊ : ℝ) / ((m : ℝ) + 1) * ((m : ℝ) + 1) =
      ⌊((m : ℝ) + 1) * x⌋₊ := div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma measurable_gridIndex (m : ℕ) : Measurable (gridIndex m) := by
  apply measurable_to_countable'
  intro j
  have h := ((measurable_const.mul measurable_subtype_coe).nat_floor :
    Measurable (fun x : unitInterval => ⌊((m : ℝ) + 1) * (x : ℝ)⌋₊))
  simpa only [Set.preimage, Set.mem_singleton_iff, Pi.mul_apply, gridIndex, Fin.ext_iff] using
    h (measurableSet_singleton j.val)

lemma measurable_grid (m : ℕ) : Measurable (grid m) := by
  exact (measurable_of_finite (gridValue m)).comp (measurable_gridIndex m)

lemma grid_tendsto (x : unitInterval) : Tendsto (fun m => grid m x) atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  have hz : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun m => (x : ℝ) - grid m x) atTop (𝓝 0) :=
    squeeze_zero (fun m => sub_nonneg.mpr (grid_le m x)) (fun m => grid_error m x) hz
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := (x : ℝ))).sub he

end TalagrandConc.BinPacking.Proof
-- End GridBasic

-- Begin PackingBasic

namespace TalagrandConc.BinPacking.Proof
open scoped BigOperators

lemma packing_self {N : ℕ} (x : Fin N → unitInterval) : IsPacking x N := by
  classical
  refine ⟨id, ?_⟩
  intro j
  simpa [Finset.sum_filter] using (x j).property.2

lemma packing_binNumber {N : ℕ} (x : Fin N → unitInterval) :
    IsPacking x (binNumber x) := by
  exact Nat.sInf_mem (s := {k : ℕ | IsPacking x k}) ⟨N, packing_self x⟩

lemma binNumber_le_of_packing {N k : ℕ} {x : Fin N → unitInterval}
    (h : IsPacking x k) : binNumber x ≤ k := Nat.sInf_le h

lemma binNumber_le {N : ℕ} (x : Fin N → unitInterval) : binNumber x ≤ N :=
  binNumber_le_of_packing (packing_self x)

lemma binNumber_zero (x : Fin 0 → unitInterval) : binNumber x = 0 := by
  exact Nat.eq_zero_of_le_zero (binNumber_le x)

lemma binNumber_pos {N : ℕ} (hN : 0 < N) (x : Fin N → unitInterval) :
    0 < binNumber x := by
  obtain ⟨σ, _⟩ := packing_binNumber x
  exact (σ ⟨0, hN⟩).pos

lemma packing_mono_items {N k : ℕ} {x y : Fin N → unitInterval}
    (hxy : ∀ i, (x i : ℝ) ≤ y i) (hy : IsPacking y k) : IsPacking x k := by
  classical
  obtain ⟨σ, hσ⟩ := hy
  refine ⟨σ, fun j => le_trans ?_ (hσ j)⟩
  exact Finset.sum_le_sum fun i _ => hxy i

lemma binNumber_mono {N : ℕ} {x y : Fin N → unitInterval}
    (hxy : ∀ i, (x i : ℝ) ≤ y i) : binNumber x ≤ binNumber y :=
  binNumber_le_of_packing (packing_mono_items hxy (packing_binNumber y))

lemma packing_relabel {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (x : Fin N → unitInterval) (σ : Fin N → J)
    (hσ : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => σ i = j), (x i : ℝ) ≤ 1) :
    IsPacking x (Fintype.card J) := by
  classical
  let e := Fintype.equivFin J
  refine ⟨fun i => e (σ i), ?_⟩
  intro j
  simpa only [← e.eq_symm_apply] using hσ (e.symm j)

end TalagrandConc.BinPacking.Proof
-- End PackingBasic

-- Begin PackingTopology

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory
open scoped BigOperators

lemma isClosed_packing (N k : ℕ) : IsClosed {x : Fin N → unitInterval | IsPacking x k} := by
  classical
  have heq : {x : Fin N → unitInterval | IsPacking x k} =
      ⋃ σ : Fin N → Fin k, ⋂ j : Fin k,
        {x | ∑ i ∈ Finset.univ.filter (fun i => σ i = j), (x i : ℝ) ≤ 1} := by
    ext x
    simp [IsPacking]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro σ
  apply isClosed_iInter
  intro j
  exact isClosed_le (continuous_finsetSum _ fun i _ =>
    continuous_subtype_val.comp (continuous_apply i)) continuous_const

lemma packing_add_bins {N k l : ℕ} {x : Fin N → unitInterval}
    (h : IsPacking x k) (hkl : k ≤ l) : IsPacking x l := by
  classical
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun i => (σ i).castLE hkl, ?_⟩
  intro j
  by_cases hj : j.val < k
  · simpa only [Fin.ext_iff, Fin.val_castLE] using hσ ⟨j.val, hj⟩
  · have hf : Finset.univ.filter (fun i => (σ i).castLE hkl = j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hi
      exact hj (hi ▸ (σ i).isLt)
    simp [hf]

lemma binNumber_le_iff {N k : ℕ} (x : Fin N → unitInterval) :
    binNumber x ≤ k ↔ IsPacking x k := by
  exact ⟨fun h => packing_add_bins (packing_binNumber x) h, binNumber_le_of_packing⟩

lemma isClosed_binNumber_le (N k : ℕ) :
    IsClosed {x : Fin N → unitInterval | binNumber x ≤ k} := by
  simpa only [binNumber_le_iff] using isClosed_packing N k

lemma measurable_binNumber (N : ℕ) : Measurable (fun x : Fin N → unitInterval => binNumber x) := by
  apply measurable_of_Iic
  intro k
  exact (isClosed_binNumber_le N k).measurableSet

end TalagrandConc.BinPacking.Proof
-- End PackingTopology

-- Begin GridPacking

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory Filter
open scoped Topology

lemma binNumber_eventually_eq {N : ℕ} (x : Fin N → unitInterval)
    (z : ℕ → Fin N → unitInterval) (hz : Tendsto z atTop (𝓝 x))
    (hle : ∀ m i, (z m i : ℝ) ≤ x i) :
    ∀ᶠ m in atTop, binNumber (z m) = binNumber x := by
  by_cases hb : binNumber x = 0
  · exact Filter.Eventually.of_forall fun m => by
      have hh := binNumber_mono (hle m)
      omega
  · have hx : x ∈ {y : Fin N → unitInterval | binNumber y ≤ binNumber x - 1}ᶜ := by
      change ¬ binNumber x ≤ binNumber x - 1
      omega
    have he := hz.eventually ((isClosed_binNumber_le N (binNumber x - 1)).isOpen_compl.mem_nhds hx)
    filter_upwards [he] with m hm
    have hh := binNumber_mono (hle m)
    change ¬ binNumber (z m) ≤ binNumber x - 1 at hm
    omega

lemma grid_binNumber_eventually (N : ℕ) (x : Fin N → unitInterval) :
    ∀ᶠ m in atTop, binNumber (fun i => grid m (x i)) = binNumber x := by
  apply binNumber_eventually_eq x (fun m i => grid m (x i))
  · exact tendsto_pi_nhds.mpr fun i => grid_tendsto (x i)
  · exact fun m i => grid_le m (x i)

lemma measurable_grid_config (m N : ℕ) :
    Measurable (fun x : Fin N → unitInterval => fun i => grid m (x i)) :=
  measurable_pi_lambda _ fun i => (measurable_grid m).comp (measurable_pi_apply i)

end TalagrandConc.BinPacking.Proof
-- End GridPacking

-- Begin FiniteLaw

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

noncomputable def configWeight {K : Type*} {N : ℕ} (p : K → ℝ) (x : Fin N → K) : ℝ := ∏ i,p (x i)
noncomputable def finiteExpect {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ) (f : (Fin N → K) → ℝ) : ℝ :=
  ∑ x,configWeight p x*f x
noncomputable def finiteMass {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ) (A : Set (Fin N → K)) : ℝ :=
  finiteExpect p (A.indicator (fun _ => 1))

lemma configWeight_nonneg {K : Type*} {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k) (x : Fin N → K) :
    0 ≤ configWeight p x := Finset.prod_nonneg (fun i _ => hp (x i))

lemma configWeight_sum {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∑ k,p k=1) :
    (∑ x : Fin N → K,configWeight p x)=1 := by
  classical
  simp only [configWeight]
  rw [← Fintype.prod_sum]
  simp [hp]

lemma finiteExpect_one {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∑ k,p k=1) :
    finiteExpect (N := N) p (fun _ => 1)=1 := by
  simp only [finiteExpect,mul_one]
  exact configWeight_sum hp

lemma finiteMass_nonneg {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    (A : Set (Fin N → K)) : 0 ≤ finiteMass p A := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (configWeight_nonneg hp x)
  by_cases hx : x∈A <;> simp [hx]

lemma finiteMass_le_one {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (A : Set (Fin N → K)) : finiteMass p A ≤ 1 := by
  classical
  rw [← finiteExpect_one (N := N) hp]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (configWeight_nonneg hp0 x)
  by_cases hx : x∈A <;> simp [hx]

lemma finiteMass_pos_nonempty {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    {A : Set (Fin N → K)} (hA : 0 < finiteMass p A) : A.Nonempty := by
  by_contra hn
  have he : A=∅ := Set.not_nonempty_iff_eq_empty.mp hn
  simp [he,finiteMass,finiteExpect] at hA

lemma configWeight_cons {K : Type*} {N : ℕ} (p : K → ℝ) (z : K) (x : Fin N → K) :
    configWeight p (Fin.cons z x)=p z*configWeight p x := by
  simp [configWeight,Fin.prod_univ_succ]

lemma finiteExpect_nonneg {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    {f : (Fin N → K) → ℝ} (hf : ∀ x,0 ≤ f x) : 0 ≤ finiteExpect p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (configWeight_nonneg hp x) (hf x))

end TalagrandConc.BinPacking.Proof
-- End FiniteLaw

-- Begin FiniteMeasure

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory
open scoped BigOperators

lemma singleton_weights_nonneg {K : Type*} [MeasurableSpace K] (ρ : Measure K) (k : K) :
    0 ≤ ρ.real {k} := ENNReal.toReal_nonneg

lemma singleton_weights_sum {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] :
    ∑ k, ρ.real {k} = 1 := by
  simp

lemma configWeight_eq_singleton {K : Type*} [MeasurableSpace K] (ρ : Measure K)
    [IsProbabilityMeasure ρ] {N : ℕ} (x : Fin N → K) :
    configWeight (fun k => ρ.real {k}) x = (Measure.pi (fun _ : Fin N => ρ)).real {x} := by
  simp only [configWeight, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]

lemma finiteExpect_eq_integral {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] {N : ℕ}
    (f : (Fin N → K) → ℝ) :
    finiteExpect (fun k => ρ.real {k}) f = ∫ x, f x ∂Measure.pi (fun _ : Fin N => ρ) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [finiteExpect, configWeight_eq_singleton, smul_eq_mul]

lemma finiteMass_eq_real {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] {N : ℕ}
    (A : Set (Fin N → K)) :
    finiteMass (fun k => ρ.real {k}) A = (Measure.pi (fun _ : Fin N => ρ)).real A := by
  rw [finiteMass, finiteExpect_eq_integral, integral_indicator (Set.toFinite A).measurableSet]
  simp

lemma weighted_sum_eq_integral {K : Type*} [Fintype K] [MeasurableSpace K]
    [MeasurableSingletonClass K] (ρ : Measure K) [IsProbabilityMeasure ρ] (f : K → ℝ) :
    (∑ k, ρ.real {k} * f k) = ∫ k, f k ∂ρ := by
  rw [integral_fintype (Integrable.of_finite)]
  rfl

end TalagrandConc.BinPacking.Proof
-- End FiniteMeasure

-- Begin GridMeasure

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory Filter
open scoped Topology

noncomputable def gridLaw (μ : Measure unitInterval) (m : ℕ) : Measure (Fin (m + 2)) :=
  μ.map (gridIndex m)

instance gridLaw_probability (μ : Measure unitInterval) [IsProbabilityMeasure μ] (m : ℕ) :
    IsProbabilityMeasure (gridLaw μ m) := Measure.isProbabilityMeasure_map (measurable_gridIndex m).aemeasurable

lemma gridLaw_product (μ : Measure unitInterval) [IsProbabilityMeasure μ] (m N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).map (fun x i => gridIndex m (x i)) =
      Measure.pi (fun _ : Fin N => gridLaw μ m) :=
  Measure.pi_map_pi (fun _ => (measurable_gridIndex m).aemeasurable)

lemma gridLaw_event (μ : Measure unitInterval) [IsProbabilityMeasure μ] (m N : ℕ)
    (S : Set ℕ) :
    (Measure.pi (fun _ : Fin N => gridLaw μ m)).real
      {x | binNumber (gridValue m ∘ x) ∈ S} =
    (Measure.pi (fun _ : Fin N => μ)).real
      {x | binNumber (fun i => grid m (x i)) ∈ S} := by
  rw [← gridLaw_product, measureReal_def, Measure.map_apply]
  · rfl
  · exact measurable_pi_lambda _ fun i => (measurable_gridIndex m).comp (measurable_pi_apply i)
  · exact (Set.toFinite _).measurableSet

lemma grid_event_tendsto (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (N : ℕ) (S : Set ℕ) :
    Tendsto (fun m => (Measure.pi (fun _ : Fin N => μ)).real
      {x | binNumber (fun i => grid m (x i)) ∈ S}) atTop
      (𝓝 ((Measure.pi (fun _ : Fin N => μ)).real {x | binNumber x ∈ S})) := by
  have ht := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop
    (Measure.pi (fun _ : Fin N => μ))
    (As := fun m => {x | binNumber (fun i => grid m (x i)) ∈ S})
    (A := {x | binNumber x ∈ S})
    (fun m => (Set.to_countable S).measurableSet.preimage
      ((measurable_binNumber N).comp (measurable_grid_config m N)))
    (fun x => (grid_binNumber_eventually N x).mono fun m hm => by
      change binNumber (fun i => grid m (x i)) ∈ S ↔ binNumber x ∈ S
      rw [hm])
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht

end TalagrandConc.BinPacking.Proof
-- End GridMeasure

-- Begin GridMoment

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory
open scoped BigOperators

lemma secondMoment_nonneg (μ : Measure unitInterval) : 0 ≤ secondMoment μ :=
  integral_nonneg (fun x => sq_nonneg (x : ℝ))

lemma integral_sq_integrable (μ : Measure unitInterval) [IsProbabilityMeasure μ] :
    Integrable (fun x : unitInterval => (x : ℝ)^2) μ := by
  apply Integrable.of_mem_Icc 0 1 (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    constructor
    · positivity
    · nlinarith [x.property.1, x.property.2]

lemma grid_sq_integrable (μ : Measure unitInterval) [IsProbabilityMeasure μ] (m : ℕ) :
    Integrable (fun x : unitInterval => (grid m x : ℝ)^2) μ := by
  apply Integrable.of_mem_Icc 0 1
    ((measurable_subtype_coe.comp (measurable_grid m)).pow_const 2).aemeasurable
  exact Filter.Eventually.of_forall fun x => by
    constructor
    · positivity
    · change (grid m x : ℝ)^2 ≤ 1
      nlinarith [(grid m x).property.1, (grid m x).property.2]

lemma grid_moment_le (μ : Measure unitInterval) [IsProbabilityMeasure μ] (m : ℕ) :
    (∑ k, (gridLaw μ m).real {k} * (gridValue m k : ℝ)^2) ≤ secondMoment μ := by
  rw [weighted_sum_eq_integral]
  change (∫ k, (gridValue m k : ℝ)^2 ∂μ.map (gridIndex m)) ≤ _
  rw [integral_map (measurable_gridIndex m).aemeasurable (by fun_prop)]
  apply integral_mono (grid_sq_integrable μ m) (integral_sq_integrable μ)
  intro x
  have h := grid_le m x
  have hz := (grid m x).property.1
  change (grid m x : ℝ)^2 ≤ (x : ℝ)^2
  nlinarith [x.property.1]

end TalagrandConc.BinPacking.Proof
-- End GridMoment

-- Begin FiniteDistance

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

noncomputable def sqNorm {N : ℕ} (s : Fin N → ℝ) : ℝ := ∑ i,s i^2
lemma sqNorm_nonneg {N : ℕ} (s : Fin N → ℝ) : 0 ≤ sqNorm s := Finset.sum_nonneg (fun i _ => sq_nonneg (s i))
lemma continuous_sqNorm (N : ℕ) : Continuous (sqNorm (N := N)) := by unfold sqNorm; fun_prop

lemma masks_finite {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) :
    (TalagrandConc.ConvexHull.U A x).Finite := by
  classical
  let f : (Fin N → Bool) → (Fin N → ℝ) := fun b i => if b i then 1 else 0
  apply (Set.finite_range f).subset
  intro s hs
  refine ⟨fun i => decide (s i=1),?_⟩
  funext i
  rcases hs.1 i with hi | hi <;> simp [f,hi]

lemma masks_nonempty {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    (TalagrandConc.ConvexHull.U A x).Nonempty := by
  obtain ⟨y,hy⟩ := hA
  refine ⟨fun _ => 1,?_,y,hy,?_⟩
  · intro i; exact Or.inr rfl
  · intro i hi; norm_num at hi

lemma hull_compact {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) :
    IsCompact (TalagrandConc.ConvexHull.V A x) := (masks_finite A x).isCompact_convexHull ℝ

lemma hull_nonempty {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    (TalagrandConc.ConvexHull.V A x).Nonempty := (masks_nonempty hA x).mono (subset_convexHull ℝ _)

lemma exists_min_mask {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    ∃ s ∈ TalagrandConc.ConvexHull.V A x, ∀ t ∈ TalagrandConc.ConvexHull.V A x,sqNorm s ≤ sqNorm t :=
  (hull_compact A x).exists_isMinOn (hull_nonempty hA x) (continuous_sqNorm N).continuousOn

noncomputable def minMask {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : Fin N → ℝ :=
  by
    classical
    exact if hA : A.Nonempty then Classical.choose (exists_min_mask hA x) else 0

noncomputable def distSq {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : ℝ := sqNorm (minMask A x)

lemma minMask_mem {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K) :
    minMask A x ∈ TalagrandConc.ConvexHull.V A x := by
  rw [minMask,dif_pos hA]
  exact (Classical.choose_spec (exists_min_mask hA x)).1

lemma distSq_le {K : Type*} {N : ℕ} {A : Set (Fin N → K)} (hA : A.Nonempty) (x : Fin N → K)
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.V A x) : distSq A x ≤ sqNorm s := by
  rw [distSq,minMask,dif_pos hA]
  exact (Classical.choose_spec (exists_min_mask hA x)).2 s hs

lemma distSq_nonneg {K : Type*} {N : ℕ} (A : Set (Fin N → K)) (x : Fin N → K) : 0 ≤ distSq A x :=
  sqNorm_nonneg _

lemma sqNorm_cons {N : ℕ} (a : ℝ) (s : Fin N → ℝ) : sqNorm (Fin.cons a s)=a^2+sqNorm s := by
  simp [sqNorm,Fin.sum_univ_succ]

lemma distSq_zero_dim {K : Type*} (A : Set (Fin 0 → K)) (x : Fin 0 → K) : distSq A x=0 := by
  simp [distSq,sqNorm]

end TalagrandConc.BinPacking.Proof
-- End FiniteDistance

-- Begin DistanceLift

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

noncomputable def liftMask {N : ℕ} (b : ℝ) : (Fin N → ℝ) →ᵃ[ℝ] (Fin (N+1) → ℝ) where
  toFun := fun s => (Fin.cons b s : Fin (N+1) → ℝ)
  linear :=
    { toFun := fun s => (Fin.cons 0 s : Fin (N+1) → ℝ)
      map_add' := by intro x y; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := by intro a x; funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  map_vadd' := by
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def fiber {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (z : K) : Set (Fin N → K) :=
  {x | Fin.cons z x ∈ A}
def projection {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) : Set (Fin N → K) :=
  {x | ∃ z,Fin.cons z x ∈ A}

lemma fiber_subset_projection {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (z : K) :
    fiber A z ⊆ projection A := fun _ hx => ⟨z,hx⟩

lemma projection_nonempty {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} (hA : A.Nonempty) :
    (projection A).Nonempty := by
  obtain ⟨x,hx⟩ := hA
  exact ⟨Fin.tail x,x 0,by simpa using hx⟩

lemma lift_fiber_mask {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (x : Fin N → K) (z : K)
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.U (fiber A z) x) :
    liftMask 0 s ∈ TalagrandConc.ConvexHull.U A (Fin.cons z x) := by
  obtain ⟨hb,y,hy,he⟩ := hs
  refine ⟨?_,Fin.cons z y,hy,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact hb j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _; rfl
    · exact he j

lemma lift_projection_mask {K : Type*} {N : ℕ} (A : Set (Fin (N+1) → K)) (x : Fin N → K) (z : K)
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.U (projection A) x) :
    liftMask 1 s ∈ TalagrandConc.ConvexHull.U A (Fin.cons z x) := by
  obtain ⟨hb,y,⟨v,hy⟩,he⟩ := hs
  refine ⟨?_,Fin.cons v y,hy,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr rfl
    · exact hb j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi; norm_num [liftMask] at hi
    · exact he j

lemma lift_hull {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} {B : Set (Fin N → K)}
    {x : Fin N → K} {z : K} {b : ℝ}
    (h : ∀ s ∈ TalagrandConc.ConvexHull.U B x,liftMask b s ∈ TalagrandConc.ConvexHull.U A (Fin.cons z x))
    {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.V B x) :
    liftMask b s ∈ TalagrandConc.ConvexHull.V A (Fin.cons z x) := by
  have hi : liftMask b '' TalagrandConc.ConvexHull.U B x ⊆ TalagrandConc.ConvexHull.U A (Fin.cons z x) := by
    rintro _ ⟨s,hs,rfl⟩; exact h s hs
  apply convexHull_mono hi
  rw [← AffineMap.image_convexHull]
  exact ⟨s,hs,rfl⟩

lemma distSq_projection {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)} (hA : A.Nonempty)
    (x : Fin N → K) (z : K) : distSq A (Fin.cons z x) ≤ 1+distSq (projection A) x := by
  have hm := lift_hull (fun s hs => lift_projection_mask A x z hs) (minMask_mem (projection_nonempty hA) x)
  have hd := distSq_le hA (Fin.cons z x) hm
  simpa only [liftMask,AffineMap.coe_mk,sqNorm_cons,one_pow,distSq] using hd

end TalagrandConc.BinPacking.Proof
-- End DistanceLift

-- Begin DistanceInterpolation

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma sqNorm_interpolate {N : ℕ} (s t : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    sqNorm (a • liftMask 0 s+(1-a) • liftMask 1 t) ≤
      (1-a)^2+a*sqNorm s+(1-a)*sqNorm t := by
  simp only [sqNorm,Fin.sum_univ_succ,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    liftMask,AffineMap.coe_mk,Fin.cons_zero,Fin.cons_succ,mul_zero,mul_one,zero_add]
  have hb : (∑ i : Fin N,(a*s i+(1-a)*t i)^2) ≤
      a*(∑ i,s i^2)+(1-a)*(∑ i,t i^2) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr ha1)) (sq_nonneg (s i-t i))]
  linarith

lemma distSq_interpolate {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)}
    (hA : A.Nonempty) (x : Fin N → K) (z : K) (hF : (fiber A z).Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    distSq A (Fin.cons z x) ≤ (1-a)^2+a*distSq (fiber A z) x+(1-a)*distSq (projection A) x := by
  let s := minMask (fiber A z) x
  let t := minMask (projection A) x
  have hs := lift_hull (fun v hv => lift_fiber_mask A x z hv) (minMask_mem hF x)
  have ht := lift_hull (fun v hv => lift_projection_mask A x z hv) (minMask_mem (projection_nonempty hA) x)
  have hm : a • liftMask 0 s+(1-a) • liftMask 1 t ∈ TalagrandConc.ConvexHull.V A (Fin.cons z x) :=
    (convex_convexHull ℝ _) hs ht ha (sub_nonneg.mpr ha1) (by ring)
  exact (distSq_le hA (Fin.cons z x) hm).trans (sqNorm_interpolate s t ha ha1)

end TalagrandConc.BinPacking.Proof
-- End DistanceInterpolation

-- Begin FiniteProduct

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

def configEquiv (K : Type*) (N : ℕ) : (K × (Fin N → K)) ≃ (Fin (N+1) → K) where
  toFun := fun y => Fin.cons y.1 y.2
  invFun := fun x => (x 0,Fin.tail x)
  left_inv := by intro y; cases y; simp
  right_inv := by intro x; simp

lemma finiteExpect_succ {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ)
    (f : (Fin (N+1) → K) → ℝ) :
    finiteExpect p f = ∑ z,p z*finiteExpect p (fun x => f (Fin.cons z x)) := by
  classical
  unfold finiteExpect
  rw [← (configEquiv K N).sum_comp (fun x => configWeight p x*f x),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  simp only [configEquiv,Equiv.coe_fn_mk,configWeight_cons,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma finiteMass_succ {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ)
    (A : Set (Fin (N+1) → K)) : finiteMass p A=∑ z,p z*finiteMass p (fiber A z) := by
  classical
  rw [finiteMass,finiteExpect_succ]
  apply Finset.sum_congr rfl
  intro z _
  congr 1

lemma finiteMass_mono {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    {A B : Set (Fin N → K)} (hAB : A ⊆ B) : finiteMass p A ≤ finiteMass p B := by
  classical
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (configWeight_nonneg hp x)
  by_cases hx : x∈A
  · simp [hx,hAB hx]
  · by_cases hy : x∈B <;> simp [hx,hy]

lemma finiteMass_le_projection {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (A : Set (Fin (N+1) → K)) :
    finiteMass p A ≤ finiteMass p (projection A) := by
  rw [finiteMass_succ]
  calc
    _ ≤ ∑ z,p z*finiteMass p (projection A) := Finset.sum_le_sum (fun z _ =>
      mul_le_mul_of_nonneg_left (finiteMass_mono hp0 (fiber_subset_projection A z)) (hp0 z))
    _ = _ := by rw [← Finset.sum_mul,hp,one_mul]

lemma finiteExpect_mono {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ} (hp : ∀ k,0 ≤ p k)
    {f g : (Fin N → K) → ℝ} (h : ∀ x,f x ≤ g x) : finiteExpect p f ≤ finiteExpect p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (configWeight_nonneg hp x))

lemma finiteExpect_const_mul {K : Type*} [Fintype K] {N : ℕ} (p : K → ℝ)
    (f : (Fin N → K) → ℝ) (c : ℝ) : finiteExpect p (fun x => c*f x)=c*finiteExpect p f := by
  unfold finiteExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end TalagrandConc.BinPacking.Proof
-- End FiniteProduct

-- Begin FiniteHolder

open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma finite_holder_bound {I : Type*} [Fintype I] (w a b : I → ℝ)
    (hw : ∀ i,0 ≤ w i) (ha : ∀ i,0 ≤ a i) (hb : ∀ i,0 ≤ b i)
    {A B l : ℝ} (hA : 0 < A) (hB : 0 < B) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hsa : ∑ i,w i*a i ≤ A) (hsb : ∑ i,w i*b i ≤ B) :
    (∑ i,w i*(a i^l*b i^(1-l))) ≤ A^l*B^(1-l) := by
  let C := A^l*B^(1-l)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  have he (i : I) : a i^l*b i^(1-l)=C*((a i/A)^l*(b i/B)^(1-l)) := by
    rw [Real.div_rpow (ha i) hA.le,Real.div_rpow (hb i) hB.le]
    dsimp [C]
    field_simp [(Real.rpow_pos_of_pos hA l).ne',(Real.rpow_pos_of_pos hB (1-l)).ne']
  have hm (i : I) : a i^l*b i^(1-l) ≤ C*(l*(a i/A)+(1-l)*(b i/B)) := by
    rw [he]
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.geom_mean_le_arith_mean2_weighted hl (sub_nonneg.mpr hl1)
      (div_nonneg (ha i) hA.le) (div_nonneg (hb i) hB.le) (by ring)
  have hs : (∑ i,w i*(l*(a i/A)+(1-l)*(b i/B))) ≤ 1 := by
    have he' : (∑ i,w i*(l*(a i/A)+(1-l)*(b i/B)))=
        (l/A)*(∑ i,w i*a i)+((1-l)/B)*(∑ i,w i*b i) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he']
    calc
      _ ≤ (l/A)*A+((1-l)/B)*B := add_le_add
        (mul_le_mul_of_nonneg_left hsa (div_nonneg hl hA.le))
        (mul_le_mul_of_nonneg_left hsb (div_nonneg (sub_nonneg.mpr hl1) hB.le))
      _ = 1 := by field_simp; ring
  calc
    _ ≤ ∑ i,w i*(C*(l*(a i/A)+(1-l)*(b i/B))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hm i) (hw i))
    _ = C*(∑ i,w i*(l*(a i/A)+(1-l)*(b i/B))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ C*1 := mul_le_mul_of_nonneg_left hs hC
    _ = _ := mul_one _

end TalagrandConc.BinPacking.Proof
-- End FiniteHolder

-- Begin ScalarInterpolation

open Set
namespace TalagrandConc.BinPacking.Proof

lemma derivative_mono_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

lemma derivative_anti_Icc {f g : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, g x ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    exact hg x (interior_subset hx)

noncomputable def logDeficit (r : ℝ) : ℝ := Real.log (2-r)+Real.log r+(Real.log r)^2
noncomputable def logSlope (r : ℝ) : ℝ := -r/(2-r)+1+2*Real.log r

lemma logSlope_deriv {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    HasDerivAt logSlope (2/r-2/(2-r)^2) r := by
  have hn : 2-r ≠ 0 := by linarith
  have hd := (((hasDerivAt_id r).neg.div ((hasDerivAt_const r 2).sub (hasDerivAt_id r)) hn).add_const 1).add
    ((Real.hasDerivAt_log hr.ne').const_mul 2)
  convert! hd using 1
  dsimp
  field_simp
  ring

lemma logSlope_nonpos {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : logSlope r ≤ 0 := by
  have hm : MonotoneOn logSlope (Icc r 1) := by
    apply derivative_mono_Icc (fun x hx => logSlope_deriv (hr.trans_le hx.1) hx.2)
    intro x hx
    have hxp := hr.trans_le hx.1
    have hx2 : 1 ≤ 2-x := by linarith [hx.2]
    have hsq : 1 ≤ (2-x)^2 := by nlinarith
    have ha : 2 ≤ 2/x := (le_div_iff₀ hxp).mpr (by linarith [hx.2])
    have hb : 2/(2-x)^2 ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    linarith
  have hh := hm ⟨le_rfl,hr1⟩ ⟨hr1,le_rfl⟩ hr1
  norm_num [logSlope] at hh ⊢
  exact hh

lemma logDeficit_deriv {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    HasDerivAt logDeficit (logSlope r/r) r := by
  have hn : 2-r ≠ 0 := by linarith
  have hd := (((Real.hasDerivAt_log hn).comp r
    ((hasDerivAt_const r 2).sub (hasDerivAt_id r))).add (Real.hasDerivAt_log hr.ne')).add
      ((Real.hasDerivAt_log hr.ne').pow 2)
  convert! hd using 1
  dsimp [logSlope]
  field_simp
  ring

lemma logDeficit_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 0 ≤ logDeficit r := by
  have hm : AntitoneOn logDeficit (Icc r 1) := by
    apply derivative_anti_Icc (fun x hx => logDeficit_deriv (hr.trans_le hx.1) hx.2)
    intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (logSlope_nonpos (hr.trans_le hx.1) hx.2) (hr.trans_le hx.1).le
  have hh := hm ⟨le_rfl,hr1⟩ ⟨hr1,le_rfl⟩ hr1
  norm_num [logDeficit] at hh ⊢
  exact hh

lemma scalar_interpolation {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ a ∈ Icc (0:ℝ) 1, Real.exp ((1-a)^2/4)*r^(-a) ≤ 2-r := by
  by_cases hb : Real.exp (-(1/2:ℝ)) ≤ r
  · refine ⟨1+2*Real.log r,⟨?_,?_⟩,?_⟩
    · have hl := Real.log_le_log (Real.exp_pos _) hb
      rw [Real.log_exp] at hl
      linarith
    · have hl := Real.log_nonpos hr.le hr1
      linarith
    · rw [Real.rpow_def_of_pos hr,← Real.exp_add]
      apply (Real.le_log_iff_exp_le (by linarith : 0 < 2-r)).mp
      have hf := logDeficit_nonneg hr hr1
      dsimp [logDeficit] at hf
      nlinarith
  · refine ⟨0,⟨le_rfl,zero_le_one⟩,?_⟩
    simp only [sub_zero,one_pow,neg_zero,Real.rpow_zero,mul_one]
    have he : Real.exp (-(1/2:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hf := logDeficit_nonneg (Real.exp_pos (-(1/2:ℝ))) he
    dsimp [logDeficit] at hf
    rw [Real.log_exp] at hf
    have hh : Real.exp (1/4:ℝ) ≤ 2-Real.exp (-(1/2:ℝ)) := by
      apply (Real.le_log_iff_exp_le (by linarith : 0 < 2-Real.exp (-(1/2:ℝ)))).mp
      nlinarith
    exact hh.trans (by linarith [lt_of_not_ge hb])

end TalagrandConc.BinPacking.Proof
-- End ScalarInterpolation

-- Begin DistanceConditional

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma holder_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (l : ℝ) :
    (1/a)^l*(1/b)^(1-l)=(1/b)*(a/b)^(-l) := by
  rw [Real.div_rpow (by norm_num) ha.le,Real.div_rpow (by norm_num) hb.le,
    Real.one_rpow,Real.one_rpow,Real.rpow_neg (div_nonneg ha.le hb.le),
    Real.div_rpow ha.le hb.le,Real.rpow_sub hb,Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos ha l).ne',(Real.rpow_pos_of_pos hb l).ne']

lemma distance_exp_interpolate {K : Type*} {N : ℕ} {A : Set (Fin (N+1) → K)}
    (hA : A.Nonempty) (x : Fin N → K) (z : K) (hF : (fiber A z).Nonempty)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (distSq A (Fin.cons z x)/4) ≤ Real.exp ((1-a)^2/4)*
      (Real.exp (distSq (fiber A z) x/4)^a*Real.exp (distSq (projection A) x/4)^(1-a)) := by
  have hd := distSq_interpolate hA x z hF ha ha1
  calc
    _ ≤ Real.exp (((1-a)^2+a*distSq (fiber A z) x+(1-a)*distSq (projection A) x)/4) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [← Real.exp_mul,← Real.exp_mul,← Real.exp_add,← Real.exp_add]
      congr 1
      ring

lemma conditional_positive_bound {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) {A : Set (Fin (N+1) → K)} (hA : A.Nonempty) (z : K)
    (ha : 0 < finiteMass p (fiber A z)) (hb : 0 < finiteMass p (projection A))
    (hsub : finiteMass p (fiber A z) ≤ finiteMass p (projection A))
    (hf : finiteExpect p (fun x => Real.exp (distSq (fiber A z) x/4)) ≤ 1/finiteMass p (fiber A z))
    (hg : finiteExpect p (fun x => Real.exp (distSq (projection A) x/4)) ≤ 1/finiteMass p (projection A)) :
    finiteExpect p (fun x => Real.exp (distSq A (Fin.cons z x)/4)) ≤
      (2-finiteMass p (fiber A z)/finiteMass p (projection A))/finiteMass p (projection A) := by
  obtain ⟨a,ha01,hs⟩ := scalar_interpolation (div_pos ha hb) ((div_le_one hb).mpr hsub)
  have hh := finite_holder_bound (configWeight p)
    (fun x => Real.exp (distSq (fiber A z) x/4)) (fun x => Real.exp (distSq (projection A) x/4))
    (configWeight_nonneg hp) (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (one_div_pos.mpr ha) (one_div_pos.mpr hb) ha01.1 ha01.2 hf hg
  calc
    _ ≤ finiteExpect p (fun x => Real.exp ((1-a)^2/4)*
      (Real.exp (distSq (fiber A z) x/4)^a*Real.exp (distSq (projection A) x/4)^(1-a))) :=
        finiteExpect_mono hp (fun x => distance_exp_interpolate hA x z (finiteMass_pos_nonempty ha) ha01.1 ha01.2)
    _ = Real.exp ((1-a)^2/4)*finiteExpect p (fun x =>
      Real.exp (distSq (fiber A z) x/4)^a*Real.exp (distSq (projection A) x/4)^(1-a)) := finiteExpect_const_mul _ _ _
    _ ≤ Real.exp ((1-a)^2/4)*((1/finiteMass p (fiber A z))^a*(1/finiteMass p (projection A))^(1-a)) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = (Real.exp ((1-a)^2/4)*(finiteMass p (fiber A z)/finiteMass p (projection A))^(-a))/finiteMass p (projection A) := by
      rw [holder_ratio ha hb]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hs hb.le

end TalagrandConc.BinPacking.Proof
-- End DistanceConditional

-- Begin DistanceInduction

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma exp_quarter_le_two : Real.exp (1/4:ℝ) ≤ 2 := by
  have he : Real.exp (-(1/2:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hf := logDeficit_nonneg (Real.exp_pos (-(1/2:ℝ))) he
  dsimp [logDeficit] at hf
  rw [Real.log_exp] at hf
  have hh : Real.exp (1/4:ℝ) ≤ 2-Real.exp (-(1/2:ℝ)) := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < 2-Real.exp (-(1/2:ℝ)))).mp
    nlinarith
  exact hh.trans (by linarith [Real.exp_pos (-(1/2:ℝ))])

lemma conditional_zero_bound {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) {A : Set (Fin (N+1) → K)} (hA : A.Nonempty) (z : K)
    (hb : 0 < finiteMass p (projection A))
    (hg : finiteExpect p (fun x => Real.exp (distSq (projection A) x/4)) ≤ 1/finiteMass p (projection A)) :
    finiteExpect p (fun x => Real.exp (distSq A (Fin.cons z x)/4)) ≤ 2/finiteMass p (projection A) := by
  have he (x : Fin N → K) : Real.exp (distSq A (Fin.cons z x)/4) ≤
      Real.exp (1/4:ℝ)*Real.exp (distSq (projection A) x/4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd := distSq_projection hA x z
    linarith
  calc
    _ ≤ finiteExpect p (fun x => Real.exp (1/4:ℝ)*Real.exp (distSq (projection A) x/4)) := finiteExpect_mono hp he
    _ = Real.exp (1/4:ℝ)*finiteExpect p (fun x => Real.exp (distSq (projection A) x/4)) := finiteExpect_const_mul _ _ _
    _ ≤ Real.exp (1/4:ℝ)*(1/finiteMass p (projection A)) := mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
    _ ≤ 2*(1/finiteMass p (projection A)) := mul_le_mul_of_nonneg_right exp_quarter_le_two (one_div_nonneg.mpr hb.le)
    _ = _ := by ring

lemma projection_final_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (2-a/b)/b ≤ 1/a := by
  apply (div_le_div_iff₀ hb ha).mpr
  have he : (2-a/b)*a*b=2*a*b-a^2 := by field_simp
  have hs := sq_nonneg (b-a)
  apply (mul_le_mul_iff_of_pos_right hb).mp
  nlinarith

lemma finite_distance_exponential {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (N : ℕ)
    (A : Set (Fin N → K)) (hA : 0 < finiteMass p A) :
    finiteExpect p (fun x => Real.exp (distSq A x/4)) ≤ 1/finiteMass p A := by
  induction N with
  | zero =>
    simp only [distSq_zero_dim,zero_div,Real.exp_zero,finiteExpect_one hp]
    exact (one_le_div hA).mpr (finiteMass_le_one hp0 hp A)
  | succ N ih =>
    have hB : 0 < finiteMass p (projection A) := hA.trans_le (finiteMass_le_projection hp0 hp A)
    have hnon := finiteMass_pos_nonempty hA
    have hg := ih (projection A) hB
    have hc (z : K) : finiteExpect p (fun x => Real.exp (distSq A (Fin.cons z x)/4)) ≤
        (2-finiteMass p (fiber A z)/finiteMass p (projection A))/finiteMass p (projection A) := by
      by_cases hz : 0 < finiteMass p (fiber A z)
      · exact conditional_positive_bound hp0 hnon z hz hB
          (finiteMass_mono hp0 (fiber_subset_projection A z)) (ih (fiber A z) hz) hg
      · have he : finiteMass p (fiber A z)=0 := le_antisymm (le_of_not_gt hz) (finiteMass_nonneg hp0 _)
        simpa only [he,zero_div,sub_zero] using conditional_zero_bound hp0 hnon z hB hg
    rw [finiteExpect_succ]
    calc
      _ ≤ ∑ z,p z*((2-finiteMass p (fiber A z)/finiteMass p (projection A))/finiteMass p (projection A)) :=
        Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hc z) (hp0 z))
      _ = (2-finiteMass p A/finiteMass p (projection A))/finiteMass p (projection A) := by
        rw [finiteMass_succ]
        simp only [← mul_div_assoc,mul_sub,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_mul,hp]
        ring
      _ ≤ _ := projection_final_bound hA hB

end TalagrandConc.BinPacking.Proof
-- End DistanceInduction

-- Begin DistanceTail

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma finite_exp_markov {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) (f : (Fin N → K) → ℝ) (b : ℝ) :
    finiteMass p {x | b ≤ f x} ≤ Real.exp (-b)*finiteExpect p (fun x => Real.exp (f x)) := by
  unfold finiteMass
  rw [← finiteExpect_const_mul]
  apply finiteExpect_mono hp
  intro x
  by_cases hx : b ≤ f x
  · rw [Set.indicator_of_mem (show x ∈ {x | b ≤ f x} from hx)]
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  · rw [Set.indicator_of_notMem (show x ∉ {x | b ≤ f x} from hx)]
    positivity

lemma finite_distance_product {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (N : ℕ)
    (A : Set (Fin N → K)) (t : ℝ) :
    finiteMass p A*finiteMass p {x | t^2 ≤ distSq A x} ≤ Real.exp (-(t^2/4)) := by
  by_cases hA : 0 < finiteMass p A
  · have hm := finite_exp_markov hp0 (fun x => distSq A x/4) (t^2/4)
    have he : {x | t^2/4 ≤ distSq A x/4}={x | t^2 ≤ distSq A x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    rw [he] at hm
    have hd := finite_distance_exponential p hp0 hp N A hA
    calc
      _ ≤ finiteMass p A*(Real.exp (-(t^2/4))*finiteExpect p (fun x => Real.exp (distSq A x/4))) :=
        mul_le_mul_of_nonneg_left hm hA.le
      _ ≤ finiteMass p A*(Real.exp (-(t^2/4))*(1/finiteMass p A)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le) hA.le
      _ = _ := by field_simp
  · have he : finiteMass p A=0 := le_antisymm (le_of_not_gt hA) (finiteMass_nonneg hp0 A)
    rw [he,zero_mul]
    exact (Real.exp_pos _).le

end TalagrandConc.BinPacking.Proof
-- End DistanceTail

-- Begin FiniteNormTail

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma exp_le_one_add_two {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp z ≤ 1+2*z := by
  have h := convexOn_exp.2 (show (0:ℝ)∈(Set.univ:Set ℝ) from Set.mem_univ _)
    (show (1:ℝ)∈(Set.univ:Set ℝ) from Set.mem_univ _) (sub_nonneg.mpr hz1) hz
    (show 1-z+z=1 by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
  have he := Real.exp_one_lt_three
  nlinarith

lemma finite_square_mgf {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (v : K → unitInterval)
    (V : ℝ) (hm : ∑ k,p k*(v k : ℝ)^2 ≤ V) (N : ℕ) :
    finiteExpect p (fun x : Fin N → K => Real.exp (∑ i,(v (x i):ℝ)^2)) ≤
      Real.exp (2*(N:ℝ)*V) := by
  classical
  have h1 : (∑ k,p k*Real.exp ((v k:ℝ)^2)) ≤ Real.exp (2*V) := by
    calc
      _ ≤ ∑ k,p k*(1+2*(v k:ℝ)^2) := Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_left (exp_le_one_add_two (sq_nonneg _) (by
          have h0 := (v k).property.1
          have h1 := (v k).property.2
          nlinarith)) (hp0 k))
      _ = 1+2*(∑ k,p k*(v k:ℝ)^2) := by
        simp only [mul_add,mul_one,Finset.sum_add_distrib,hp]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ ≤ 1+2*V := by linarith
      _ ≤ Real.exp (2*V) := by linarith [Real.add_one_le_exp (2*V)]
  have he : finiteExpect p (fun x : Fin N → K => Real.exp (∑ i,(v (x i):ℝ)^2)) =
      (∑ k,p k*Real.exp ((v k:ℝ)^2))^N := by
    simp only [finiteExpect,configWeight,Real.exp_sum,← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (_ : Fin N) (k : K) => p k*Real.exp ((v k:ℝ)^2))]
    simp
  rw [he]
  calc
    _ ≤ (Real.exp (2*V))^N := pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ =>
      mul_nonneg (hp0 k) (Real.exp_pos _).le)) h1 N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma finite_square_tail {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (v : K → unitInterval)
    (V : ℝ) (hm : ∑ k,p k*(v k : ℝ)^2 ≤ V) (N : ℕ) :
    finiteMass p {x : Fin N → K | 4*(N:ℝ)*V ≤ ∑ i,(v (x i):ℝ)^2} ≤
      Real.exp (-2*(N:ℝ)*V) := by
  have h := finite_exp_markov hp0 (fun x : Fin N → K => ∑ i,(v (x i):ℝ)^2) (4*N*V)
  calc
    _ ≤ _ := h
    _ ≤ Real.exp (-(4*N*V))*Real.exp (2*N*V) :=
      mul_le_mul_of_nonneg_left (finite_square_mgf p hp0 hp v V hm N) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TalagrandConc.BinPacking.Proof
-- End FiniteNormTail

-- Begin PackingMerge

namespace TalagrandConc.BinPacking.Proof
open scoped BigOperators

noncomputable def load {N : ℕ} {J : Type*} (x : Fin N → unitInterval)
    (σ : Fin N → J) (j : J) : ℝ := by
  classical
  exact ∑ i, if σ i = j then (x i : ℝ) else 0

lemma load_nonneg {N : ℕ} {J : Type*} (x : Fin N → unitInterval)
    (σ : Fin N → J) (j : J) : 0 ≤ load x σ j := by
  classical
  unfold load
  exact Finset.sum_nonneg fun i _ => by split_ifs; exact (x i).property.1; rfl

lemma load_eq {N : ℕ} {J : Type*} [DecidableEq J] (x : Fin N → unitInterval)
    (σ : Fin N → J) (j : J) :
    load x σ j = ∑ i ∈ Finset.univ.filter (fun i => σ i = j), (x i : ℝ) := by
  classical
  simp only [load, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

lemma sum_load {N : ℕ} {J : Type*} [Fintype J] (x : Fin N → unitInterval)
    (σ : Fin N → J) : ∑ j, load x σ j = ∑ i, (x i : ℝ) := by
  classical
  rw [show (∑ j, load x σ j) = ∑ i, ∑ j, if σ i = j then (x i : ℝ) else 0 by
    exact Finset.sum_comm]
  simp

lemma optimal_pair_load {N : ℕ} (x : Fin N → unitInterval)
    (σ : Fin N → Fin (binNumber x)) (hσ : ∀ j, load x σ j ≤ 1)
    {a b : Fin (binNumber x)} (hab : a ≠ b) : 1 < load x σ a + load x σ b := by
  classical
  by_contra! hsum
  let τ : Fin N → {j : Fin (binNumber x) // j ≠ b} :=
    fun i => if h : σ i = b then ⟨a, hab⟩ else ⟨σ i, h⟩
  have ht : ∀ j, load x τ j ≤ 1 := by
    intro j
    have heq : load x τ j = load x σ j.val + if j.val = a then load x σ b else 0 := by
      by_cases hja : j.val = a
      · simp only [hja, if_true, load, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hb : σ i = b
        · simp [τ, hb, Ne.symm hab, Subtype.ext_iff, hja]
        · simp [τ, hb, Subtype.ext_iff, hja]
      · simp only [hja, if_false, add_zero, load]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hb : σ i = b
        · simp [τ, hb, Subtype.ext_iff, Ne.symm hja, Ne.symm j.property]
        · simp [τ, hb, Subtype.ext_iff]
    rw [heq]
    split_ifs with hja
    · simpa [hja] using hsum
    · simpa using hσ j.val
  have hp : IsPacking x (Fintype.card {j : Fin (binNumber x) // j ≠ b}) :=
    packing_relabel x τ (fun j => by simpa only [← load_eq] using ht j)
  have hc : Fintype.card {j : Fin (binNumber x) // j ≠ b} < binNumber x := by
    simpa using (Fintype.card_subtype_lt (p := fun j : Fin (binNumber x) => j ≠ b)
      (x := b) (by simp))
  exact (not_lt_of_ge (binNumber_le_of_packing hp)) hc

end TalagrandConc.BinPacking.Proof
-- End PackingMerge

-- Begin HalfFull

namespace TalagrandConc.BinPacking.Proof
open scoped BigOperators

lemma card_le_twice_sum_add_one {J : Type*} [Fintype J] (a : J → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : ∀ i j, i ≠ j → 1 < a i + a j) :
    (Fintype.card J : ℝ) ≤ 2 * ∑ j, a j + 1 := by
  classical
  by_cases h : ∃ j, a j ≤ 1 / 2
  · obtain ⟨j, hj⟩ := h
    have ho : ∀ i ∈ Finset.univ.erase j, (1 / 2 : ℝ) ≤ a i := by
      intro i hi
      have hh := hp i j (Finset.mem_erase.mp hi).1
      linarith
    have hs := Finset.sum_le_sum ho
    have hc : (Finset.univ.erase j).card + 1 = Fintype.card J := by
      exact Finset.card_erase_add_one (Finset.mem_univ j)
    have hcr : ((Finset.univ.erase j).card : ℝ) + 1 = Fintype.card J := by exact_mod_cast hc
    have he := Finset.sum_erase_add Finset.univ a (Finset.mem_univ j)
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    have hz := ha j
    linarith
  · push Not at h
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (h j).le)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    linarith

lemma binNumber_half_full {N : ℕ} (x : Fin N → unitInterval) :
    (binNumber x : ℝ) ≤ 2 * ∑ i, (x i : ℝ) + 1 := by
  classical
  obtain ⟨σ, hσ⟩ := packing_binNumber x
  have hb : ∀ j, load x σ j ≤ 1 := fun j => by simpa only [load_eq] using hσ j
  have h := card_le_twice_sum_add_one (load x σ) (load_nonneg x σ)
    (fun i j hij => optimal_pair_load x σ hb hij)
  simpa only [Fintype.card_fin, sum_load] using h

end TalagrandConc.BinPacking.Proof
-- End HalfFull

-- Begin PackingSplit

namespace TalagrandConc.BinPacking.Proof
open scoped BigOperators

noncomputable def restrictItems {N : ℕ} (x : Fin N → unitInterval) (S : Set (Fin N)) :
    Fin N → unitInterval := by classical exact fun i => if i ∈ S then x i else 0

lemma packing_split {N : ℕ} (x : Fin N → unitInterval) (S : Set (Fin N)) :
    binNumber x ≤ binNumber (restrictItems x S) + binNumber (restrictItems x Sᶜ) := by
  classical
  obtain ⟨σ, hσ⟩ := packing_binNumber (restrictItems x S)
  obtain ⟨τ, hτ⟩ := packing_binNumber (restrictItems x Sᶜ)
  let f : Fin N → (Fin (binNumber (restrictItems x S)) ⊕
      Fin (binNumber (restrictItems x Sᶜ))) :=
    fun i => if i ∈ S then Sum.inl (σ i) else Sum.inr (τ i)
  have hf : ∀ j, load x f j ≤ 1 := by
    intro j
    cases j with
    | inl j =>
      have he : load x f (Sum.inl j) = load (restrictItems x S) σ j := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [f, restrictItems, hi]
      rw [he, load_eq]
      exact hσ j
    | inr j =>
      have he : load x f (Sum.inr j) = load (restrictItems x Sᶜ) τ j := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S <;> simp [f, restrictItems, hi]
      rw [he, load_eq]
      exact hτ j
  have hp := packing_relabel x f (fun j => by simpa only [← load_eq] using hf j)
  simpa only [Fintype.card_sum, Fintype.card_fin] using binNumber_le_of_packing hp

lemma packing_mask_bound {N : ℕ} (x y : Fin N → unitInterval) (s : Fin N → ℝ)
    (hs : ∀ i, s i = 0 ∨ s i = 1) (hxy : ∀ i, s i = 0 → x i = y i) :
    (binNumber x : ℝ) ≤ binNumber y + 2 * ∑ i, (x i : ℝ) * s i + 1 := by
  classical
  let S : Set (Fin N) := {i | s i = 0}
  have hm : binNumber (restrictItems x S) ≤ binNumber y := by
    apply binNumber_mono
    intro i
    by_cases hi : s i = 0
    · simp [restrictItems, S, hi, hxy i hi]
    · simpa [restrictItems, S, hi] using (y i).property.1
  have hspl : (binNumber x : ℝ) ≤
      binNumber (restrictItems x S) + binNumber (restrictItems x Sᶜ) := by
    exact_mod_cast packing_split x S
  have hh := binNumber_half_full (restrictItems x Sᶜ)
  have hsum : (∑ i, (restrictItems x Sᶜ i : ℝ)) = ∑ i, (x i : ℝ) * s i := by
    apply Finset.sum_congr rfl
    intro i _
    rcases hs i with hi | hi <;> simp [restrictItems, S, hi]
  rw [hsum] at hh
  have hmr : (binNumber (restrictItems x S) : ℝ) ≤ binNumber y := by exact_mod_cast hm
  linarith

end TalagrandConc.BinPacking.Proof
-- End PackingSplit

-- Begin PackingDistance

namespace TalagrandConc.BinPacking.Proof
open scoped BigOperators

lemma packing_hull_bound {K : Type*} {N : ℕ} (v : K → unitInterval)
    {A : Set (Fin N → K)} {a : ℝ} (hA : ∀ y ∈ A, (binNumber (v ∘ y) : ℝ) ≤ a)
    (x : Fin N → K) {s : Fin N → ℝ} (hs : s ∈ TalagrandConc.ConvexHull.V A x) :
    (binNumber (v ∘ x) : ℝ) ≤ a + 2 * ∑ i, (v (x i) : ℝ) * s i + 1 := by
  let f : (Fin N → ℝ) → ℝ := fun t => ∑ i, (v (x i) : ℝ) * t i
  have hf : IsLinearMap ℝ f := by
    constructor
    · intro t u
      simp [f, mul_add, Finset.sum_add_distrib]
    · intro c t
      simp [f, Finset.mul_sum, mul_left_comm]
  have hsub : TalagrandConc.ConvexHull.U A x ⊆
      {t | ((binNumber (v ∘ x) : ℝ) - a - 1) / 2 ≤ f t} := by
    intro t ht
    obtain ⟨ht, y, hy, hxy⟩ := ht
    have hb := packing_mask_bound (v ∘ x) (v ∘ y) t ht
      (fun i hi => congrArg v (hxy i hi))
    have ha := hA y hy
    change _ ≤ ∑ i, (v (x i) : ℝ) * t i
    change (binNumber (v ∘ x) : ℝ) ≤ binNumber (v ∘ y) +
      2 * ∑ i, (v (x i) : ℝ) * t i + 1 at hb
    linarith
  have hh := convexHull_min hsub (convex_halfSpace_ge hf _) hs
  change ((binNumber (v ∘ x) : ℝ) - a - 1) / 2 ≤ ∑ i, (v (x i) : ℝ) * s i at hh
  linarith

lemma packing_distance_bound {K : Type*} {N : ℕ} (v : K → unitInterval)
    {A : Set (Fin N → K)} {a : ℝ} (hne : A.Nonempty)
    (hA : ∀ y ∈ A, (binNumber (v ∘ y) : ℝ) ≤ a) (x : Fin N → K) :
    (binNumber (v ∘ x) : ℝ) ≤
      a + 2 * l2Norm (v ∘ x) * Real.sqrt (distSq A x) + 1 := by
  have h := packing_hull_bound v hA x (minMask_mem hne x)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => (v (x i) : ℝ)) (minMask A x)
  change (∑ i, (v (x i) : ℝ) * minMask A x i) ≤
    l2Norm (v ∘ x) * Real.sqrt (distSq A x) at hc
  nlinarith

end TalagrandConc.BinPacking.Proof
-- End PackingDistance

-- Begin FinitePackingProduct

open Set
open scoped BigOperators
namespace TalagrandConc.BinPacking.Proof

lemma finiteMass_union_le {K : Type*} [Fintype K] {N : ℕ} {p : K → ℝ}
    (hp : ∀ k,0 ≤ p k) (A B : Set (Fin N → K)) :
    finiteMass p (A ∪ B) ≤ finiteMass p A+finiteMass p B := by
  classical
  unfold finiteMass finiteExpect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hw := configWeight_nonneg hp x
  by_cases hA : x∈A <;> by_cases hB : x∈B <;> simp [hA,hB]; linarith

lemma finite_packing_product {K : Type*} [Fintype K] (p : K → ℝ)
    (hp0 : ∀ k,0 ≤ p k) (hp : ∑ k,p k=1) (v : K → unitInterval)
    (V : ℝ) (hV : 0 < V) (hm : ∑ k,p k*(v k : ℝ)^2 ≤ V)
    (N : ℕ) (hN : 0 < N) (a t : ℝ) (ht : 0 < t) :
    finiteMass p {x : Fin N → K | (binNumber (v ∘ x):ℝ) ≤ a} *
      finiteMass p {x : Fin N → K | a+1+4*t*Real.sqrt ((N:ℝ)*V) ≤ (binNumber (v ∘ x):ℝ)} ≤
      Real.exp (-(t^2/4))+Real.exp (-2*(N:ℝ)*V) := by
  let A : Set (Fin N → K) := {x | (binNumber (v ∘ x):ℝ) ≤ a}
  let C : Set (Fin N → K) := {x | a+1+4*t*Real.sqrt ((N:ℝ)*V) ≤ (binNumber (v ∘ x):ℝ)}
  let D : Set (Fin N → K) := {x | t^2 ≤ distSq A x}
  let B : Set (Fin N → K) := {x | 4*(N:ℝ)*V ≤ ∑ i,(v (x i):ℝ)^2}
  change finiteMass p A*finiteMass p C ≤ _
  by_cases hA : 0 < finiteMass p A
  · have hne := finiteMass_pos_nonempty hA
    have hNV : 0 < (N:ℝ)*V := mul_pos (by exact_mod_cast hN) hV
    have hs : 0 < Real.sqrt ((N:ℝ)*V) := Real.sqrt_pos.mpr hNV
    have hsub : C ⊆ D ∪ B := by
      intro x hx
      by_contra hh
      have hd : distSq A x < t^2 := lt_of_not_ge (fun h => hh (Or.inl h))
      have hb : (∑ i,(v (x i):ℝ)^2) < 4*(N:ℝ)*V :=
        lt_of_not_ge (fun h => hh (Or.inr h))
      have hds : Real.sqrt (distSq A x) < t := by
        apply (Real.sqrt_lt (distSq_nonneg A x) ht.le).mpr
        exact hd
      have hnorm : l2Norm (v ∘ x) < 2*Real.sqrt ((N:ℝ)*V) := by
        unfold l2Norm
        apply (Real.sqrt_lt (Finset.sum_nonneg (fun i _ => sq_nonneg (v (x i):ℝ))) (by positivity : 0 ≤ 2*Real.sqrt ((N:ℝ)*V))).mpr
        have he := Real.sq_sqrt hNV.le
        change (∑ i,(v (x i):ℝ)^2) < _
        nlinarith
      have he := packing_distance_bound v hne (fun y hy => hy) x
      have hp : l2Norm (v ∘ x)*Real.sqrt (distSq A x) <
          (2*Real.sqrt ((N:ℝ)*V))*t :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hnorm.le (Real.sqrt_nonneg _))
          (mul_lt_mul_of_pos_left hds (by positivity))
      change a+1+4*t*Real.sqrt ((N:ℝ)*V) ≤ (binNumber (v ∘ x):ℝ) at hx
      nlinarith
    have hmass := (finiteMass_mono hp0 hsub).trans (finiteMass_union_le hp0 D B)
    have hdist := finite_distance_product p hp0 hp N A t
    have hnorm := finite_square_tail p hp0 hp v V hm N
    have hAle := finiteMass_le_one hp0 hp A
    have hB0 := finiteMass_nonneg hp0 B
    calc
      _ ≤ finiteMass p A*(finiteMass p D+finiteMass p B) := mul_le_mul_of_nonneg_left hmass hA.le
      _ = finiteMass p A*finiteMass p D+finiteMass p A*finiteMass p B := by ring
      _ ≤ Real.exp (-(t^2/4))+finiteMass p B := add_le_add hdist (by nlinarith)
      _ ≤ _ := add_le_add_right hnorm _
  · have he : finiteMass p A=0 := le_antisymm (le_of_not_gt hA) (finiteMass_nonneg hp0 A)
    rw [he,zero_mul]
    positivity

end TalagrandConc.BinPacking.Proof
-- End FinitePackingProduct

-- Begin NativeProduct

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory Filter

lemma packing_product_bound (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (hV : 0 < secondMoment μ) (a t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin N => μ)).real {x | (binNumber x : ℝ) ≤ a} *
      (Measure.pi (fun _ : Fin N => μ)).real
        {x | a + 1 + 4*t*Real.sqrt ((N:ℝ)*secondMoment μ) ≤ (binNumber x : ℝ)} ≤
      Real.exp (-(t^2/4)) + Real.exp (-(2*N*secondMoment μ)) := by
  let b := a + 1 + 4*t*Real.sqrt ((N:ℝ)*secondMoment μ)
  have hg : ∀ m : ℕ,
      (Measure.pi (fun _ : Fin N => μ)).real
        {x | (binNumber (fun i => grid m (x i)) : ℝ) ≤ a} *
      (Measure.pi (fun _ : Fin N => μ)).real
        {x | b ≤ (binNumber (fun i => grid m (x i)) : ℝ)} ≤
      Real.exp (-(t^2/4)) + Real.exp (-(2*N*secondMoment μ)) := by
    intro m
    have hh := finite_packing_product (fun k => (gridLaw μ m).real {k})
      (singleton_weights_nonneg _) (singleton_weights_sum _) (gridValue m)
      (secondMoment μ) hV (grid_moment_le μ m) N hN a t ht
    rw [finiteMass_eq_real, finiteMass_eq_real] at hh
    change (Measure.pi (fun _ : Fin N => gridLaw μ m)).real
      {x | binNumber (gridValue m ∘ x) ∈ {k : ℕ | (k : ℝ) ≤ a}} *
      (Measure.pi (fun _ : Fin N => gridLaw μ m)).real
      {x | binNumber (gridValue m ∘ x) ∈ {k : ℕ | b ≤ (k : ℝ)}} ≤ _ at hh
    rw [gridLaw_event, gridLaw_event] at hh
    simpa only [neg_mul, Set.mem_ofPred_eq] using hh
  exact le_of_tendsto
    ((grid_event_tendsto μ N {k : ℕ | (k : ℝ) ≤ a}).mul
      (grid_event_tendsto μ N {k : ℕ | b ≤ (k : ℝ)})) (Eventually.of_forall hg)

end TalagrandConc.BinPacking.Proof
-- End NativeProduct

-- Begin MedianTail

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory

lemma median_ge_one (μ : Measure unitInterval) [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 0 < N) {M : ℝ}
    (hM : IsMedian (Measure.pi (fun _ : Fin N => μ)) (fun x => (binNumber x : ℝ)) M) :
    1 ≤ M := by
  by_contra! hlt
  have he : {x : Fin N → unitInterval | (binNumber x : ℝ) ≤ M} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    change (binNumber x : ℝ) ≤ M at hx
    have hb : (1 : ℝ) ≤ binNumber x := by exact_mod_cast binNumber_pos hN x
    linarith
  have hh := hM.1
  rw [he, measure_empty] at hh
  norm_num at hh

lemma median_real_bounds {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (Z : α → ℝ) (M : ℝ) (hM : IsMedian P Z M) :
    (1 / 2 : ℝ) ≤ P.real {x | Z x ≤ M} ∧ (1 / 2 : ℝ) ≤ P.real {x | M ≤ Z x} := by
  constructor
  · simpa [measureReal_def] using ENNReal.toReal_mono (measure_ne_top _ _) hM.1
  · simpa [measureReal_def] using ENNReal.toReal_mono (measure_ne_top _ _) hM.2

lemma median_tail_from_product (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) {M u e : ℝ} (_hu : 0 < u) (he : 0 ≤ e)
    (hM : IsMedian (Measure.pi (fun _ : Fin N => μ)) (fun x => (binNumber x : ℝ)) M)
    (hprod : ∀ a : ℝ, 0 < a →
      (Measure.pi (fun _ : Fin N => μ)).real {x | (binNumber x : ℝ) ≤ a} *
      (Measure.pi (fun _ : Fin N => μ)).real {x | a + 1 + u ≤ (binNumber x : ℝ)} ≤ 2 * e) :
    (Measure.pi (fun _ : Fin N => μ)).real {x | 1 + u ≤ |(binNumber x : ℝ) - M|} ≤ 8 * e := by
  let P := Measure.pi (fun _ : Fin N => μ)
  have hm := median_real_bounds P (fun x => (binNumber x : ℝ)) M hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (median_ge_one μ hN hM)
  have hupp : P.real {x | M + 1 + u ≤ (binNumber x : ℝ)} ≤ 4 * e := by
    have hh := hprod M hMpos
    have hz : 0 ≤ P.real {x | M + 1 + u ≤ (binNumber x : ℝ)} := ENNReal.toReal_nonneg
    change P.real _ * P.real _ ≤ _ at hh
    nlinarith [hm.1]
  have hlo : P.real {x | (binNumber x : ℝ) ≤ M - u - 1} ≤ 4 * e := by
    by_cases ha : 0 < M - u - 1
    · have hh := hprod (M - u - 1) ha
      have heq : M - u - 1 + 1 + u = M := by ring
      rw [heq] at hh
      have hz : 0 ≤ P.real {x | (binNumber x : ℝ) ≤ M - u - 1} := ENNReal.toReal_nonneg
      change P.real _ * P.real _ ≤ _ at hh
      nlinarith [hm.2]
    · have hempty : {x : Fin N → unitInterval | (binNumber x : ℝ) ≤ M - u - 1} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        change (binNumber x : ℝ) ≤ M - u - 1 at hx
        have hb : (0 : ℝ) < binNumber x := by exact_mod_cast binNumber_pos hN x
        linarith
      rw [hempty]
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) he
  have hset : {x : Fin N → unitInterval | 1 + u ≤ |(binNumber x : ℝ) - M|} =
      {x | M + 1 + u ≤ (binNumber x : ℝ)} ∪ {x | (binNumber x : ℝ) ≤ M - u - 1} := by
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, le_abs]
    constructor
    · rintro (h | h) <;> [left; right] <;> linarith
    · rintro (h | h) <;> [left; right] <;> linarith
  rw [hset]
  exact (measureReal_union_le _ _).trans (by linarith)

end TalagrandConc.BinPacking.Proof
-- End MedianTail

-- Begin TailConstants

namespace TalagrandConc.BinPacking.Proof

lemma tail_parameter {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hmax : u ≤ 8 * Real.sqrt 2 * b) :
    ∃ t : ℝ, 0 < t ∧ 4 * t * Real.sqrt b = u ∧
      t^2 / 4 = u^2 / (64*b) ∧
      Real.exp (-(2*b)) ≤ Real.exp (-(t^2/4)) := by
  let t := u / (4 * Real.sqrt b)
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : (Real.sqrt b)^2 = b := Real.sq_sqrt hb.le
  have ht : 0 < t := div_pos hu (mul_pos (by norm_num) hs)
  have he : 4 * t * Real.sqrt b = u := by dsimp [t]; field_simp
  have hq : t^2 / 4 = u^2 / (64*b) := by
    dsimp [t]
    rw [div_pow, mul_pow, hsq]
    ring
  have hsqmax : u^2 ≤ (8 * Real.sqrt 2 * b)^2 :=
    (sq_le_sq₀ hu.le (by positivity)).mpr hmax
  have hconst : (8 * Real.sqrt 2 * b)^2 = 128*b^2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [hconst] at hsqmax
  have hqle : u^2 / (64*b) ≤ 2*b := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨t, ht, he, hq, ?_⟩
  apply Real.exp_le_exp.mpr
  rw [hq]
  linarith

end TalagrandConc.BinPacking.Proof
-- End TailConstants

-- Begin NativeMedian

namespace TalagrandConc.BinPacking.Proof
open MeasureTheory

lemma native_concentration (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) (M : ℝ)
    (hM : IsMedian (Measure.pi (fun _ : Fin N => μ)) (fun x => (binNumber x : ℝ)) M)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 8 * Real.sqrt 2 * N * secondMoment μ) :
    Measure.pi (fun _ : Fin N => μ) {x | 1 + u ≤ |(binNumber x : ℝ) - M|} ≤
      ENNReal.ofReal (8 * Real.exp (-(u ^ 2 / (64 * N * secondMoment μ)))) := by
  by_cases huZ : u = 0
  · subst u
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, neg_zero, Real.exp_zero, mul_one]
    exact (prob_le_one).trans (by norm_num)
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huZ)
  have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hv0 := secondMoment_nonneg μ
  have hb : 0 < (N : ℝ)*secondMoment μ := by
    by_contra! hn
    have hz : (N : ℝ)*secondMoment μ = 0 := le_antisymm hn (mul_nonneg hn0 hv0)
    have he : 8 * Real.sqrt 2 * N * secondMoment μ = 0 := by
      calc _ = 8 * Real.sqrt 2 * ((N : ℝ)*secondMoment μ) := by ring
           _ = 0 := by rw [hz, mul_zero]
    rw [he] at hu
    linarith
  have hNreal : 0 < (N : ℝ) := by nlinarith
  have hN : 0 < N := by exact_mod_cast hNreal
  have hv : 0 < secondMoment μ := by nlinarith
  obtain ⟨t, ht, hscale, hq, hexp⟩ := tail_parameter hb hup (by nlinarith [hu])
  have hh := median_tail_from_product μ hN hup
    (le_of_lt (Real.exp_pos (-(u^2/(64*((N : ℝ)*secondMoment μ)))))) hM (fun a _ => by
      have hp := packing_product_bound μ N hN hv a t ht
      rw [hscale] at hp
      have he : -(2 * (N : ℝ) * secondMoment μ) = -(2*((N : ℝ)*secondMoment μ)) := by ring
      rw [he] at hp
      rw [hq] at hexp hp
      linarith)
  have hden : 64*((N : ℝ)*secondMoment μ) = 64*N*secondMoment μ := by ring
  rw [hden] at hh
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact hh

end TalagrandConc.BinPacking.Proof
-- End NativeMedian

-- Begin RootAssembly

namespace TalagrandConc.BinPacking

open MeasureTheory

/-- Talagrand (1995), p. 152, Theorem 6.5: if `M` is a median of `B_N` under the product
probability `P = μ^{⊗N}` on `[0,1]^N`, then for all `0 ≤ u ≤ 8 √2 N E X₁²`,
`P(|B_N(X₁, …, X_N) − M| ≥ 1 + u) ≤ 8 exp(−u² / (64 N E X₁²))`.
(The paper writes "for all `u ≤ 8√2 N E X₁²`"; `u ≥ 0` is implicit — its proof sets
`u = 4t √N (E X₁²)^{1/2}` with `t > 0` — and is stated here.) -/
theorem theorem_6_5 (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) (M : ℝ)
    (hM : IsMedian (Measure.pi (fun _ : Fin N => μ)) (fun x => (binNumber x : ℝ)) M)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 8 * Real.sqrt 2 * N * secondMoment μ) :
    Measure.pi (fun _ : Fin N => μ) {x | 1 + u ≤ |(binNumber x : ℝ) - M|} ≤
      ENNReal.ofReal (8 * Real.exp (-(u ^ 2 / (64 * N * secondMoment μ)))) := by
  exact Proof.native_concentration μ N M hM u hu0 hu

end TalagrandConc.BinPacking
-- End RootAssembly

-- Begin Solution

open MeasureTheory TalagrandConc.BinPacking

theorem solution (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) (M : ℝ)
    (hM : IsMedian (Measure.pi (fun _ : Fin N => μ)) (fun x => (binNumber x : ℝ)) M)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 8 * Real.sqrt 2 * N * secondMoment μ) :
    Measure.pi (fun _ : Fin N => μ) {x | 1 + u ≤ |(binNumber x : ℝ) - M|} ≤
      ENNReal.ofReal (8 * Real.exp (-(u ^ 2 / (64 * N * secondMoment μ)))) := by
  exact theorem_6_5 μ N M hM u hu0 hu
-- End Solution
