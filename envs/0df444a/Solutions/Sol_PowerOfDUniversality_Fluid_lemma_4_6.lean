-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:55:41.212382+00:00
-- url     : https://prove2.me/submissions/d4d97187-4bf7-4ee4-970c-d9a69c2c9c1b

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Lem46Aux

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

lemma fluid_nonneg {x : ℕ → ℝ} (hx : x ∈ FluidSpace ⊤) (i : ℕ) : 0 ≤ x i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; rw [hx.1]; norm_num
  · exact (hx.2.1 i h).1

lemma fluid_le_one {x : ℕ → ℝ} (hx : x ∈ FluidSpace ⊤) (i : ℕ) : x i ≤ 1 := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; rw [hx.1]
  · exact (hx.2.1 i h).2

lemma isClosed_F : IsClosed (FluidSpaceL1 ⊤) := by
  have h : FluidSpaceL1 ⊤ = {y : E | (y : ℕ → ℝ) 0 = 1} ∩
      (⋂ i : ℕ, {y : E | 1 ≤ i → 0 ≤ (y : ℕ → ℝ) i ∧ (y : ℕ → ℝ) i ≤ 1}) ∩
      (⋂ i : ℕ, ⋂ j : ℕ, {y : E | 1 ≤ i → i ≤ j → (y : ℕ → ℝ) j ≤ (y : ℕ → ℝ) i}) := by
    ext y
    simp only [FluidSpaceL1, FluidSpace, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h0, h1, h2, _, _⟩
      exact ⟨⟨h0, h1⟩, h2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨h0, h1, h2, ?_, ?_⟩
      · intro i hi; exact absurd hi (not_lt.mpr le_top)
      · exact (summ_abs y).of_abs
  rw [h]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_eq (coord_cont 0) continuous_const
  · refine isClosed_iInter (fun i => ?_)
    by_cases hi : 1 ≤ i
    · simp only [hi, true_implies]
      exact IsClosed.inter (isClosed_le continuous_const (coord_cont i))
        (isClosed_le (coord_cont i) continuous_const)
    · simp only [hi, false_implies, Set.setOf_true]
      exact isClosed_univ
  · refine isClosed_iInter (fun i => isClosed_iInter (fun j => ?_))
    by_cases hij : 1 ≤ i ∧ i ≤ j
    · simp only [hij.1, hij.2, true_implies]
      exact isClosed_le (coord_cont j) (coord_cont i)
    · have : {y : E | 1 ≤ i → i ≤ j → (y : ℕ → ℝ) j ≤ (y : ℕ → ℝ) i} = Set.univ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ hij
      rw [this]; exact isClosed_univ

/-- An element of `𝕊` as an element of `ℓ¹`. -/
noncomputable def mkE (x : ℕ → ℝ) (hx : x ∈ FluidSpace ⊤) : E :=
  ⟨x, memℓp_gen (by
    have hs : Summable x := hx.2.2.2.2
    simpa [Real.norm_eq_abs, abs_of_nonneg (fluid_nonneg hx _)] using hs)⟩

lemma mkE_coe (x : ℕ → ℝ) (hx : x ∈ FluidSpace ⊤) : ((mkE x hx : E) : ℕ → ℝ) = x := rfl

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

lemma tail_ennreal (x : ℕ → ℝ) (hx : x ∈ FluidSpace ⊤) (k : ℕ) :
    ∑' i : ℕ, ENNReal.ofReal (x (k + i)) = ENNReal.ofReal (∑' i, x (i + k)) := by
  have hs : Summable (fun i => x (i + k)) := (summable_nat_add_iff (f := x) k).mpr hx.2.2.2.2
  rw [ENNReal.ofReal_tsum_of_nonneg (fun i => fluid_nonneg hx _) hs]
  simp_rw [add_comm k]

/-- The core equivalence in `ℓ¹`. -/
lemma core (K : Set (ℕ → ℝ)) (hK : K ⊆ FluidSpace ⊤) :
    TotallyBounded {y : E | (y : ℕ → ℝ) ∈ K} ↔
      Tendsto (fun k : ℕ => ⨆ x ∈ K, ∑' i : ℕ, ENNReal.ofReal (x (k + i))) atTop (𝓝 0) := by
  constructor
  · intro hTB
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεt : ε = ⊤
    · exact Filter.Eventually.of_forall (fun _ => hεt ▸ le_top)
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    set δ := ε.toReal / 2 with hδ
    obtain ⟨t, ht, hcov⟩ := (Metric.totallyBounded_iff.mp hTB) δ (by positivity)
    have hev : ∀ᶠ k in atTop, ∀ z ∈ t, ∑' i, |(z : ℕ → ℝ) (i + k)| < δ := by
      rw [Filter.eventually_all_finite ht]
      intro z _
      have := tendsto_sum_nat_add (fun i => |(z : ℕ → ℝ) i|)
      exact (this.eventually (gt_mem_nhds (by positivity)))
    filter_upwards [hev] with k hk
    apply iSup₂_le
    intro x hx
    have hxF := hK hx
    rw [tail_ennreal x hxF k]
    have hmem : mkE x hxF ∈ {y : E | (y : ℕ → ℝ) ∈ K} := by
      simp only [Set.mem_setOf_eq, mkE_coe]; exact hx
    have := hcov hmem
    rw [Set.mem_iUnion₂] at this
    obtain ⟨z, hz, hxz⟩ := this
    rw [Metric.mem_ball] at hxz
    have h1 := tail_le (mkE x hxF) z k
    have h2 := hk z hz
    simp only [mkE_coe] at h1
    have h3 : ∑' i, x (i + k) = ∑' i, |x (i + k)| := by
      congr 1; funext i; rw [abs_of_nonneg (fluid_nonneg hxF _)]
    rw [h3, ← ENNReal.ofReal_toReal hεt]
    apply ENNReal.ofReal_le_ofReal
    linarith
  · intro hT
    apply totallyBounded_of_approx
    intro δ hδ
    have hev := (ENNReal.tendsto_nhds_zero.mp hT) (ENNReal.ofReal (δ / 2))
      (by simp [hδ])
    obtain ⟨k, hk⟩ := hev.exists
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
      · have htail : ∑' i : ℕ, ENNReal.ofReal ((y : ℕ → ℝ) (k + i)) ≤ ENNReal.ofReal (δ / 2) :=
          le_trans (le_iSup₂ (f := fun x (_ : x ∈ K) =>
            ∑' i : ℕ, ENNReal.ofReal (x (k + i))) (y : ℕ → ℝ) hy) hk
        rw [tail_ennreal _ hyF k, ENNReal.ofReal_le_ofReal_iff (by linarith)] at htail
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

end PowerOfDUniversality.Fluid.Lem46Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Lem46Aux

theorem solution (K : Set (ℕ → ℝ)) (hK : K ⊆ FluidSpace ⊤) :
    IsCompact (closure {x : FluidSpaceL1 ⊤ |
        ((x : lp (fun _ : ℕ => ℝ) 1) : ℕ → ℝ) ∈ K}) ↔
      Tendsto (fun k : ℕ => ⨆ x ∈ K, ∑' i : ℕ, ENNReal.ofReal (x (k + i))) atTop (𝓝 0) := by
  have : IsClosed (FluidSpaceL1 ⊤) := isClosed_F
  haveI : CompleteSpace (FluidSpaceL1 ⊤) := IsClosed.completeSpace_coe
  rw [← core K hK]
  set S := {x : FluidSpaceL1 ⊤ | ((x : lp (fun _ : ℕ => ℝ) 1) : ℕ → ℝ) ∈ K}
  have himg : Subtype.val '' S = {y : E | (y : ℕ → ℝ) ∈ K} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, S]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨⟨y, hK hy⟩, hy, rfl⟩
  rw [← himg, totallyBounded_image_iff (isUniformInducing_val _)]
  rw [isCompact_iff_totallyBounded_isComplete, totallyBounded_closure]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, isClosed_closure.isComplete⟩
