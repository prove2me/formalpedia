-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:07:31.700204+00:00
-- url     : https://prove2.me/submissions/d6e1194a-a563-4a5e-bee7-6dd1777ddb2c

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Lem47Aux

open PowerOfDUniversality.Fluid

abbrev E := ↥(lp (fun _ : ℕ => ℝ) 1)

lemma summ_abs (y : E) : Summable (fun i => |(y : ℕ → ℝ) i|) := by
  have := (lp.memℓp y).summable (p := 1) (by simp)
  simpa [Real.norm_eq_abs] using this

lemma norm_eq (y : E) : ‖y‖ = ∑' i, |(y : ℕ → ℝ) i| := by
  rw [lp.norm_eq_tsum_rpow (by simp)]
  simp [Real.norm_eq_abs]

lemma dist_eq' (y z : E) : dist y z = ∑' i, |(y : ℕ → ℝ) i - (z : ℕ → ℝ) i| := by
  rw [dist_eq_norm, norm_eq, lp.coeFn_sub]
  rfl

lemma coord_le (y z : E) (i : ℕ) : |(y : ℕ → ℝ) i - (z : ℕ → ℝ) i| ≤ dist y z := by
  rw [dist_eq_norm]
  have := lp.norm_apply_le_norm (p := 1) (by simp) (y - z) i
  rw [lp.coeFn_sub] at this
  simpa [Real.norm_eq_abs] using this

lemma coord_cont (i : ℕ) : Continuous (fun y : E => (y : ℕ → ℝ) i) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq]
  simpa using coord_le y z i

lemma fluid_nonneg {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) (i : ℕ) : 0 ≤ x i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; rw [hx.1]; norm_num
  · exact (hx.2.1 i h).1

lemma fluid_le_one {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) (i : ℕ) : x i ≤ 1 := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; rw [hx.1]
  · exact (hx.2.1 i h).2

/-- An element of `𝕊` as an element of `ℓ¹`. -/
noncomputable def mkE {b : ℕ∞} (x : ℕ → ℝ) (hx : x ∈ FluidSpace b) : E :=
  ⟨x, memℓp_gen (by
    have hs : Summable x := hx.2.2.2.2
    simpa [Real.norm_eq_abs, abs_of_nonneg (fluid_nonneg hx _)] using hs)⟩

lemma mkE_coe {b : ℕ∞} (x : ℕ → ℝ) (hx : x ∈ FluidSpace b) : ((mkE x hx : E) : ℕ → ℝ) = x := rfl

/-- Totally bounded by approximation with totally bounded sets. -/
lemma totallyBounded_of_approx {α : Type*} [PseudoMetricSpace α] (s : Set α)
    (h : ∀ δ > 0, ∃ t : Set α, TotallyBounded t ∧ ∀ x ∈ s, ∃ y ∈ t, dist x y < δ) :
    TotallyBounded s := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, ht, hst⟩ := h (ε / 2) (by linarith)
  obtain ⟨F, hF, htF⟩ := (Metric.totallyBounded_iff.mp ht) (ε / 2) (by linarith)
  refine ⟨F, hF, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hst x hx
  have := htF hy
  rw [Set.mem_iUnion₂] at this ⊢
  obtain ⟨z, hz, hyz⟩ := this
  refine ⟨z, hz, ?_⟩
  rw [Metric.mem_ball] at hyz ⊢
  linarith [dist_triangle x y z]

/-- The embedding of the first `k` coordinates into `ℓ¹`. -/
noncomputable def embL (k : ℕ) : (Fin k → ℝ) →ₗ[ℝ] E where
  toFun v := ⟨fun i => if h : i < k then v ⟨i, h⟩ else 0, memℓp_gen (by
    apply summable_of_ne_finset_zero (s := Finset.range k)
    intro i hi
    rw [Finset.mem_range] at hi
    simp [hi])⟩
  map_add' v w := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, Pi.add_apply]
    show (if h : i < k then (v + w) ⟨i, h⟩ else 0) =
      (if h : i < k then v ⟨i, h⟩ else 0) + (if h : i < k then w ⟨i, h⟩ else 0)
    split_ifs <;> simp
  map_smul' c v := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    show (if h : i < k then (c • v) ⟨i, h⟩ else 0) = c • (if h : i < k then v ⟨i, h⟩ else 0)
    split_ifs <;> simp

lemma embL_apply (k : ℕ) (v : Fin k → ℝ) (i : ℕ) :
    ((embL k v : E) : ℕ → ℝ) i = if h : i < k then v ⟨i, h⟩ else 0 := rfl

lemma abs_le_aux (a b : ℝ) : |a| ≤ |a - b| + |b| := by
  have := abs_sub_abs_le_abs_sub a b
  linarith

/-- tail bound: `∑'_i |y_{i+k}| ≤ ∑'_i |y_{i+k} - z_{i+k}| + ∑'_i |z_{i+k}|`. -/
lemma tail_le (y z : E) (k : ℕ) :
    ∑' i, |(y : ℕ → ℝ) (i + k)| ≤ dist y z + ∑' i, |(z : ℕ → ℝ) (i + k)| := by
  have hyz : Summable (fun i => |(y : ℕ → ℝ) i - (z : ℕ → ℝ) i|) := by
    have := summ_abs (y - z)
    simpa [lp.coeFn_sub] using this
  have h1 : Summable (fun i => |(y : ℕ → ℝ) (i + k) - (z : ℕ → ℝ) (i + k)|) :=
    (summable_nat_add_iff (f := fun i => |(y : ℕ → ℝ) i - (z : ℕ → ℝ) i|) k).mpr hyz
  have h2 : Summable (fun i => |(z : ℕ → ℝ) (i + k)|) :=
    (summable_nat_add_iff (f := fun i => |(z : ℕ → ℝ) i|) k).mpr (summ_abs z)
  have h3 : Summable (fun i => |(y : ℕ → ℝ) (i + k)|) :=
    (summable_nat_add_iff (f := fun i => |(y : ℕ → ℝ) i|) k).mpr (summ_abs y)
  have hsub : ∑' i, |(y : ℕ → ℝ) (i + k) - (z : ℕ → ℝ) (i + k)| ≤ dist y z := by
    rw [dist_eq', ← hyz.sum_add_tsum_nat_add k]
    have : 0 ≤ ∑ i ∈ Finset.range k, |(y : ℕ → ℝ) i - (z : ℕ → ℝ) i| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  calc ∑' i, |(y : ℕ → ℝ) (i + k)|
      ≤ ∑' i, (|(y : ℕ → ℝ) (i + k) - (z : ℕ → ℝ) (i + k)| + |(z : ℕ → ℝ) (i + k)|) :=
        h3.tsum_le_tsum (fun i => abs_le_aux _ _) (h1.add h2)
    _ = ∑' i, |(y : ℕ → ℝ) (i + k) - (z : ℕ → ℝ) (i + k)| + ∑' i, |(z : ℕ → ℝ) (i + k)| :=
        h1.tsum_add h2
    _ ≤ dist y z + ∑' i, |(z : ℕ → ℝ) (i + k)| := by linarith

lemma tail_shift {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) (k : ℕ) :
    ∑' i, x (k + i) = ∑' i, x (i + k) := by
  simp_rw [add_comm k]

lemma summable_tail {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) (k : ℕ) :
    Summable (fun i => x (k + i)) := by
  have := (summable_nat_add_iff (f := x) k).mpr hx.2.2.2.2
  simpa [add_comm] using this

lemma tail_nonneg {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) (k : ℕ) :
    0 ≤ ∑' i, x (k + i) := tsum_nonneg (fun i => fluid_nonneg hx _)

lemma tail_anti {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) {k k' : ℕ} (hk : k ≤ k') :
    ∑' i, x (k' + i) ≤ ∑' i, x (k + i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hs := summable_tail hx k
  rw [← hs.sum_add_tsum_nat_add d]
  have h1 : ∑' i, x (k + d + i) = ∑' i, x (k + (i + d)) := by
    congr 1; funext i; congr 1; omega
  rw [h1]
  have : 0 ≤ ∑ i ∈ Finset.range d, x (k + i) := Finset.sum_nonneg (fun i _ => fluid_nonneg hx _)
  linarith

lemma tail_tendsto {b : ℕ∞} {x : ℕ → ℝ} (hx : x ∈ FluidSpace b) :
    Tendsto (fun k => ∑' i, x (k + i)) atTop (𝓝 0) := by
  have := tendsto_sum_nat_add x
  simpa [add_comm] using this

/-- Lemma A: `ℓ¹`-compactness gives uniformly small tails. -/
lemma tails_of_compact {b : ℕ∞} (K : Set (ℕ → ℝ)) (hK : K ⊆ FluidSpace b)
    (hc : IsCompact {x : E | (x : ℕ → ℝ) ∈ K}) (δ : ℝ) (hδ : 0 < δ) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ x ∈ K, ∑' i, x (k + i) < δ := by
  have hTB := hc.totallyBounded
  obtain ⟨t, ht, hcov⟩ := (Metric.totallyBounded_iff.mp hTB) (δ / 2) (by positivity)
  have hev : ∀ᶠ k in atTop, ∀ z ∈ t, ∑' i, |(z : ℕ → ℝ) (i + k)| < δ / 2 := by
    rw [Filter.eventually_all_finite ht]
    intro z _
    have := tendsto_sum_nat_add (fun i => |(z : ℕ → ℝ) i|)
    exact (this.eventually (gt_mem_nhds (by positivity)))
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨k0, fun k hk x hx => ?_⟩
  have hxF := hK hx
  have hmem : mkE x hxF ∈ {y : E | (y : ℕ → ℝ) ∈ K} := by
    simp only [Set.mem_setOf_eq, mkE_coe]; exact hx
  have := hcov hmem
  rw [Set.mem_iUnion₂] at this
  obtain ⟨z, hz, hxz⟩ := this
  rw [Metric.mem_ball] at hxz
  have h1 := tail_le (mkE x hxF) z k
  have h2 := hk0 k hk z hz
  simp only [mkE_coe] at h1
  have h3 : ∑' i, x (k + i) = ∑' i, |x (i + k)| := by
    rw [tail_shift hxF]
    congr 1; funext i; rw [abs_of_nonneg (fluid_nonneg hxF _)]
  rw [h3]
  linarith

lemma coe_cont : Continuous (fun y : E => (y : ℕ → ℝ)) :=
  continuous_pi (fun i => coord_cont i)

/-- Lemma B: product-closed and uniformly small tails give `ℓ¹`-compactness. -/
lemma compact_of_tails {b : ℕ∞} (K : Set (ℕ → ℝ)) (hK : K ⊆ FluidSpace b) (hcl : IsClosed K)
    (ht : ∀ δ > 0, ∃ k : ℕ, ∀ x ∈ K, ∑' i, x (k + i) ≤ δ) :
    IsCompact {x : E | (x : ℕ → ℝ) ∈ K} := by
  have hclosed : IsClosed {x : E | (x : ℕ → ℝ) ∈ K} := hcl.preimage coe_cont
  rw [isCompact_iff_totallyBounded_isComplete]
  refine ⟨?_, hclosed.isComplete⟩
  apply totallyBounded_of_approx
  intro δ hδ
  obtain ⟨k, hk⟩ := ht (δ / 2) (by positivity)
  refine ⟨embL k '' (Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)), ?_, ?_⟩
  · apply IsCompact.totallyBounded
    apply IsCompact.image
    · exact isCompact_univ_pi (fun _ => isCompact_Icc)
    · exact (embL k).continuous_of_finiteDimensional
  · intro y hy
    simp only [Set.mem_setOf_eq] at hy
    have hyF := hK hy
    refine ⟨embL k (fun j => (y : ℕ → ℝ) j), ⟨fun j => (y : ℕ → ℝ) j, ?_, rfl⟩, ?_⟩
    · intro j _
      exact ⟨fluid_nonneg hyF _, fluid_le_one hyF _⟩
    · have htail := hk _ hy
      rw [tail_shift hyF] at htail
      rw [dist_eq', ← Summable.sum_add_tsum_nat_add k]
      · have h0 : ∑ i ∈ Finset.range k, |(y : ℕ → ℝ) i -
            ((embL k (fun j => (y : ℕ → ℝ) j) : E) : ℕ → ℝ) i| = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_range] at hi
          rw [embL_apply, dif_pos hi]; simp
        have h1 : ∑' i, |(y : ℕ → ℝ) (i + k) -
            ((embL k (fun j => (y : ℕ → ℝ) j) : E) : ℕ → ℝ) (i + k)| =
            ∑' i, (y : ℕ → ℝ) (i + k) := by
          congr 1; funext i
          rw [embL_apply, dif_neg (by omega), sub_zero, abs_of_nonneg (fluid_nonneg hyF _)]
        rw [h0, h1]
        linarith
      · have := summ_abs (y - embL k (fun j => (y : ℕ → ℝ) j))
        simpa [lp.coeFn_sub] using this


section prob

variable {b : ℕ∞} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X : ℕ → Ω → ℕ → ℝ) (hXm : ∀ N, Measurable (X N)) (hXS : ∀ N ω, X N ω ∈ FluidSpace b)
include hXm hXS

/-- Lemma D: for a fixed `N`, the tail probabilities vanish as `k → ∞`. -/
lemma tail_prob_tendsto (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun k : ℕ => P {ω | δ < ∑' i : ℕ, X N ω (k + i)}) atTop (𝓝 0) := by
  have hmeas : ∀ k, MeasurableSet {ω | δ < ∑' i : ℕ, X N ω (k + i)} := by
    intro k
    apply measurableSet_lt measurable_const
    exact Measurable.tsum (fun i => (measurable_pi_apply (k + i)).comp (hXm N))
  have hanti : Antitone (fun k : ℕ => {ω | δ < ∑' i : ℕ, X N ω (k + i)}) := by
    intro k k' hk ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_lt_of_le hω (tail_anti (hXS N ω) hk)
  have := tendsto_measure_iInter_atTop (μ := P) (fun k => (hmeas k).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ k : ℕ, {ω | δ < ∑' i : ℕ, X N ω (k + i)}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    obtain ⟨k, hk⟩ := ((tail_tendsto (hXS N ω)).eventually (gt_mem_nhds hδ)).exists
    exact ⟨k, hk.le⟩
  rw [hempty, measure_empty] at this
  exact this

/-- Lemma C: a uniform-in-`N` tail bound from (4.23). -/
lemma tail_uniform
    (h423 : ∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ =>
        limsup (fun N => P {ω | ε < ∑' i : ℕ, X N ω (k + i)}) atTop) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ k : ℕ, ∀ N, P {ω | δ < ∑' i : ℕ, X N ω (k + i)} ≤ η := by
  obtain ⟨k1, hk1⟩ := ((h423 δ hδ).eventually (gt_mem_nhds hη)).exists
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (Filter.eventually_lt_of_limsup_lt hk1)
  have hfin : ∀ N, ∃ kN : ℕ, ∀ k, kN ≤ k → P {ω | δ < ∑' i : ℕ, X N ω (k + i)} ≤ η := by
    intro N
    obtain ⟨kN, hkN⟩ := Filter.eventually_atTop.mp
      ((tail_prob_tendsto P X hXm hXS N δ hδ).eventually (gt_mem_nhds hη))
    exact ⟨kN, fun k hk => (hkN k hk).le⟩
  choose kN hkN using hfin
  refine ⟨max k1 ((Finset.range N1).sup kN), fun N => ?_⟩
  by_cases hN : N1 ≤ N
  · refine le_trans (measure_mono ?_) (hN1 N hN).le
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_lt_of_le hω (tail_anti (hXS N ω) (le_max_left _ _))
  · apply hkN N
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup (f := kN) (Finset.mem_range.mpr (by omega))

end prob

end PowerOfDUniversality.Fluid.Lem47Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Lem47Aux

theorem solution (b : ℕ∞) (hb : 1 ≤ b)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ → ℝ) (hXm : ∀ N, Measurable (X N)) (hXS : ∀ N ω, X N ω ∈ FluidSpace b) :
    ((∀ ε : ℝ, 0 < ε → ∃ K ⊆ FluidSpace b, IsCompact K ∧
        ∀ N, P {ω | X N ω ∉ K} ≤ ENNReal.ofReal ε) ∧
      ∀ ε : ℝ, 0 < ε → Tendsto (fun k : ℕ =>
        limsup (fun N => P {ω | ε < ∑' i : ℕ, X N ω (k + i)}) atTop) atTop (𝓝 0)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ K ⊆ FluidSpace b,
        IsCompact {x : lp (fun _ : ℕ => ℝ) 1 | (x : ℕ → ℝ) ∈ K} ∧
        ∀ N, P {ω | X N ω ∉ K} ≤ ENNReal.ofReal ε) := by
  constructor
  · rintro ⟨hprod, h423⟩ ε hε
    obtain ⟨K0, hK0S, hK0c, hK0P⟩ := hprod (ε / 2) (by positivity)
    have hk : ∀ j : ℕ, ∃ k : ℕ, ∀ N, P {ω | 1 / ((j : ℝ) + 1) < ∑' i : ℕ, X N ω (k + i)} ≤
        ENNReal.ofReal (ε / 2 / 2 / 2 ^ j) := fun j =>
      tail_uniform P X hXm hXS h423 _ (by positivity) _ (by simp; positivity)
    choose kj hkj using hk
    set T : ℕ → Set (ℕ → ℝ) := fun j =>
      {x | ∀ s : Finset ℕ, ∑ i ∈ s, x (kj j + i) ≤ 1 / ((j : ℝ) + 1)} with hT
    refine ⟨K0 ∩ ⋂ j, T j, fun x hx => hK0S hx.1, ?_, fun N => ?_⟩
    · apply compact_of_tails (b := b) _ (fun x hx => hK0S hx.1)
      · refine hK0c.isClosed.inter (isClosed_iInter (fun j => ?_))
        simp only [hT, Set.setOf_forall]
        exact isClosed_iInter (fun s => isClosed_le
          (continuous_finset_sum _ (fun i _ => continuous_apply _)) continuous_const)
      · intro δ hδ
        obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
        refine ⟨kj j, fun x hx => ?_⟩
        have hxS := hK0S hx.1
        have hxT : x ∈ T j := Set.mem_iInter.mp hx.2 j
        have := (summable_tail hxS (kj j)).tsum_le_of_sum_le hxT
        linarith
    · have hsub : {ω | X N ω ∉ K0 ∩ ⋂ j, T j} ⊆
          {ω | X N ω ∉ K0} ∪ ⋃ j : ℕ, {ω | 1 / ((j : ℝ) + 1) < ∑' i : ℕ, X N ω (kj j + i)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, not_and_or,
          not_forall] at hω
        rcases hω with h | ⟨j, hj⟩
        · exact Or.inl h
        · right
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          refine ⟨j, ?_⟩
          simp only [hT, Set.mem_setOf_eq, not_forall, not_le] at hj
          obtain ⟨s, hs⟩ := hj
          have := (summable_tail (hXS N ω) (kj j)).sum_le_tsum s
            (fun i _ => fluid_nonneg (hXS N ω) _)
          linarith
      calc P {ω | X N ω ∉ K0 ∩ ⋂ j, T j}
          ≤ P {ω | X N ω ∉ K0} +
              P (⋃ j : ℕ, {ω | 1 / ((j : ℝ) + 1) < ∑' i : ℕ, X N ω (kj j + i)}) :=
            le_trans (measure_mono hsub) (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (ε / 2) + ∑' j : ℕ, ENNReal.ofReal (ε / 2 / 2 / 2 ^ j) :=
            add_le_add (hK0P N) (le_trans (measure_iUnion_le _)
              (ENNReal.tsum_le_tsum (fun j => hkj j N)))
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
              (summable_geometric_two' (ε / 2)), tsum_geometric_two' (ε / 2),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
  · intro h
    constructor
    · intro ε hε
      obtain ⟨K, hKS, hKc, hKP⟩ := h ε hε
      refine ⟨K, hKS, ?_, hKP⟩
      have : K = (fun y : E => (y : ℕ → ℝ)) '' {x : E | (x : ℕ → ℝ) ∈ K} := by
        ext x
        constructor
        · intro hx; exact ⟨mkE x (hKS hx), hx, rfl⟩
        · rintro ⟨y, hy, rfl⟩; exact hy
      rw [this]
      exact hKc.image coe_cont
    · intro ε hε
      rw [ENNReal.tendsto_nhds_zero]
      intro η hη
      by_cases hηt : η = ⊤
      · exact Filter.Eventually.of_forall (fun _ => hηt ▸ le_top)
      obtain ⟨K, hKS, hKc, hKP⟩ := h η.toReal (ENNReal.toReal_pos hη.ne' hηt)
      obtain ⟨k0, hk0⟩ := tails_of_compact K hKS hKc ε hε
      filter_upwards [Filter.eventually_ge_atTop k0] with k hk
      apply Filter.limsup_le_of_le (by isBoundedDefault)
      refine Filter.Eventually.of_forall (fun N => ?_)
      refine le_trans (measure_mono ?_) (le_trans (hKP N) (ENNReal.ofReal_toReal hηt).le)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro hK
      linarith [hk0 k hk _ hK]
