-- Prove2me | solution 1 for OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:03:05.983741+00:00
-- url     : https://prove2.me/submissions/1eea1cac-4481-4c7f-8557-24f96fe3ec0c

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A009
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_compact_actual_waves_sign_and_jets_supported

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GridPoint
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
namespace YauCounterexamples

theorem gridPoint_cover (d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (x : Fin d → ℝ) (hx : ‖x‖ ≤ (m : ℝ) * δ) :
    ∃ k : Fin d → Fin (2 * m + 1), dist x (gridPoint d m δ k) ≤ δ := by
  have hcoord (j : Fin d) : |x j| ≤ (m : ℝ) * δ :=
    (norm_le_pi_norm x j).trans hx
  have hy0 (j : Fin d) : 0 ≤ x j / δ + (m : ℝ) := by
    have hh : -(m : ℝ) ≤ x j / δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [(abs_le.mp (hcoord j)).1])
    linarith
  have hy2 (j : Fin d) : x j / δ + (m : ℝ) ≤ (2 * m : ℕ) := by
    have h := (abs_le.mp (hcoord j)).2
    have hh : x j / δ ≤ (m : ℝ) := (div_le_iff₀ hδ).mpr h
    push_cast
    linarith
  let k : Fin d → Fin (2 * m + 1) := fun j =>
    ⟨⌊x j / δ + (m : ℝ)⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (hy2 j))⟩
  refine ⟨k, ?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro j
  change |x j - δ * ((⌊x j / δ + (m : ℝ)⌋₊ : ℝ) - m)| ≤ δ
  have h := Nat.abs_sub_floor_le (hy0 j)
  have heq : x j - δ * ((⌊x j / δ + (m : ℝ)⌋₊ : ℝ) - m) =
      δ * (x j / δ + m - ⌊x j / δ + (m : ℝ)⌋₊) := by field_simp; ring
  rw [heq, abs_mul, abs_of_pos hδ]
  nlinarith

theorem gridPoint_card (d m : ℕ) :
    Fintype.card (Fin d → Fin (2 * m + 1)) = (2 * m + 1) ^ d := by simp

theorem recenter_finite_net {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (p : I → X) (K : Set X) (δ : ℝ)
    (hcover : ∀ x ∈ K, ∃ i, dist x (p i) ≤ δ) :
    ∃ t : Finset X, (↑t : Set X) ⊆ K ∧ t.card ≤ Fintype.card I ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ 2 * δ := by
  classical
  let A : Set I := {i | ∃ x ∈ K, dist x (p i) ≤ δ}
  let : Fintype A := Fintype.ofFinite A
  let q : A → X := fun i => i.property.choose
  have hq (i : A) : q i ∈ K ∧ dist (q i) (p i) ≤ δ := i.property.choose_spec
  refine ⟨Finset.univ.image q, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hq i).1
  · exact (Finset.card_image_le).trans (Fintype.card_le_of_injective (fun i : A => (i : I)) Subtype.val_injective)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    let j : A := ⟨i, x, hx, hi⟩
    refine ⟨q j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    calc
      dist x (q j) ≤ dist x (p i) + dist (p i) (q j) := dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add hi (by simpa [dist_comm] using (hq j).2)
      _ = 2 * δ := by ring

theorem cube_subset_finite_net (d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (K : Set (Fin d → ℝ)) (hK : ∀ x ∈ K, ‖x‖ ≤ (m : ℝ) * δ) :
    ∃ t : Finset (Fin d → ℝ), (↑t : Set (Fin d → ℝ)) ⊆ K ∧
      t.card ≤ (2 * m + 1) ^ d ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ 2 * δ := by
  simpa only [gridPoint_card] using recenter_finite_net (gridPoint d m δ) K δ
    (fun x hx => gridPoint_cover d m δ hδ x (hK x hx))

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ProbabilityBadJet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
namespace YauCounterexamples

theorem probability_bad_jet_le {Ω X V I : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace X] [NormedAddCommGroup V] [Fintype I]
    (μ : Measure Ω) (F : Ω → X → V) (G : Set Ω) (K : Set X) (p : I → X)
    (δ τ L : ℝ) (hL : 0 ≤ L)
    (hcover : ∀ x ∈ K, ∃ i, dist x (p i) ≤ δ)
    (hLip : ∀ outcome ∈ G, ∀ x ∈ K, ∀ i, ‖F outcome x - F outcome (p i)‖ ≤ L * dist x (p i))
    (q : ℝ≥0∞) (hsmall : ∀ i, μ {outcome | ‖F outcome (p i)‖ < τ + L * δ} ≤ q) :
    μ {outcome | ∃ x ∈ K, ‖F outcome x‖ < τ} ≤ μ Gᶜ + Fintype.card I * q := by
  have hsub : {outcome | ∃ x ∈ K, ‖F outcome x‖ < τ} ⊆
      Gᶜ ∪ ⋃ i, {outcome | ‖F outcome (p i)‖ < τ + L * δ} := by
    intro outcome hω
    by_cases hG : outcome ∈ G
    · obtain ⟨x, hx, hFx⟩ := hω
      obtain ⟨i, hi⟩ := hcover x hx
      refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
      have hh := (hLip outcome hG x hx i).trans (mul_le_mul_of_nonneg_left hi hL)
      have ht := norm_sub_norm_le (F outcome (p i)) (F outcome x)
      rw [norm_sub_rev] at ht
      change ‖F outcome (p i)‖ < τ + L * δ
      linarith
    · exact Or.inl hG
  calc
    μ {outcome | ∃ x ∈ K, ‖F outcome x‖ < τ} ≤
        μ (Gᶜ ∪ ⋃ i, {outcome | ‖F outcome (p i)‖ < τ + L * δ}) := measure_mono hsub
    _ ≤ μ Gᶜ + μ (⋃ i, {outcome | ‖F outcome (p i)‖ < τ + L * δ}) := measure_union_le _ _
    _ ≤ μ Gᶜ + ∑ i, μ {outcome | ‖F outcome (p i)‖ < τ + L * δ} :=
      add_le_add le_rfl (measure_iUnion_fintype_le μ _)
    _ ≤ μ Gᶜ + ∑ _i : I, q := add_le_add le_rfl (Finset.sum_le_sum fun i _ => hsmall i)
    _ = μ Gᶜ + Fintype.card I * q := by simp

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_BoundedThreePolynomialNet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
namespace YauCounterexamples

theorem bounded_three_polynomial_net (B : ℝ) (hB : 0 < B)
    (c : ℝ) (hc : 0 < c) :
    ∃ C > 0, ∀ K : Set (Fin 3 → ℝ), (∀ x ∈ K, ‖x‖ ≤ B) →
      ∀ n : ℝ, 1 ≤ n → ∃ t : Finset (Fin 3 → ℝ),
      (↑t : Set (Fin 3 → ℝ)) ⊆ K ∧ (t.card : ℝ) ≤ C*n^3 ∧
      ∀ x ∈ K, ∃ y ∈ t, dist x y ≤ c/n := by
  let A := 4*B/c+3
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^3,pow_pos hA _,?_⟩
  intro K hbound n hn
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let δ := c/(2*n)
  have hδ : 0 < δ := div_pos hc (mul_pos (by norm_num) hn0)
  let m := ⌈B/δ⌉₊
  have hm : B ≤ (m : ℝ)*δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (B/δ))
  obtain ⟨t,htK,htcard,htcover⟩ := cube_subset_finite_net 3 m δ hδ K
    (fun x hx => (hbound x hx).trans hm)
  refine ⟨t,htK,?_,?_⟩
  · have hm' : (m : ℝ) < B/δ+1 := Nat.ceil_lt_add_one (div_nonneg hB.le hδ.le)
    have heq : B/δ = (2*B/c)*n := by dsimp [δ]; field_simp
    have hbase : (2*m+1 : ℝ) ≤ A*n := by
      dsimp [A]
      rw [heq] at hm'
      have hid : (4*B/c+3)*n = 2*((2*B/c)*n)+3*n := by ring
      rw [hid]
      linarith
    calc
      (t.card : ℝ) ≤ ((2*m+1)^3 : ℕ) := by exact_mod_cast htcard
      _ = (2*(m : ℝ)+1)^3 := by norm_cast
      _ ≤ (A*n)^3 := pow_le_pow_left₀ (by positivity) hbase _
      _ = A^3*n^3 := mul_pow _ _ _
  · intro x hx
    obtain ⟨y,hy,hd⟩ := htcover x hx
    refine ⟨y,hy,?_⟩
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [δ]
    field_simp

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_UniformPolynomialSmallBall
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma complex_gaussian_norm_tail :
    ∃ M > 0, ∀ n : ℝ, 0 < n →
      stdGaussian ℂ {z | n < ‖z‖} ≤ ENNReal.ofReal (M/n^8) := by
  have hi : Integrable (fun z : ℂ => ‖z‖^8) (stdGaussian ℂ) := by
    simpa only [id_eq] using (IsGaussian.memLp_id (stdGaussian ℂ) 8 (by norm_num)).integrable_norm_pow'
  let M₀ := ∫ z : ℂ, ‖z‖^8 ∂stdGaussian ℂ
  have hM₀ : 0 ≤ M₀ := integral_nonneg (fun z => pow_nonneg (norm_nonneg z) _)
  refine ⟨1+M₀,by linarith,?_⟩
  intro n hn
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (stdGaussian ℂ) (fun z => pow_nonneg (norm_nonneg z) 8)) hi (n^8)
  have hs : {z : ℂ | n < ‖z‖} ⊆ {z : ℂ | n^8 ≤ ‖z‖^8} :=
    fun z hz => pow_le_pow_left₀ hn.le hz.le 8
  rw [←ENNReal.ofReal_toReal (measure_ne_top (stdGaussian ℂ) _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (stdGaussian ℂ {z | n < ‖z‖}).toReal ≤
        (stdGaussian ℂ {z | n^8 ≤ ‖z‖^8}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs)
    _ ≤ M₀/n^8 := by
      apply (le_div_iff₀ (pow_pos hn _)).mpr
      simpa only [Measure.real,mul_comm] using hMark
    _ ≤ (1+M₀)/n^8 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hn.le _)

theorem finite_gaussian_coefficient_tail :
    ∃ M > 0, ∀ (I : Type) [Fintype I] (n : ℝ), 0 < n →
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | ∃ i ℓ, n < ‖γ i ℓ‖} ≤
      (Fintype.card I : ℝ≥0∞)*3*ENNReal.ofReal (M/n^8) := by
  obtain ⟨M,hM,hTail⟩ := complex_gaussian_norm_tail
  refine ⟨M,hM,?_⟩
  intro I _ n hn
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  have hm (i : I) (ℓ : Fin 3) :
      μ {γ | n < ‖γ i ℓ‖} ≤ ENNReal.ofReal (M/n^8) := by
    have hf : MeasurePreserving (fun γ : I → Fin 3 → ℂ => γ i ℓ) μ (stdGaussian ℂ) :=
      (measurePreserving_eval (fun _ : Fin 3 => stdGaussian ℂ) ℓ).comp
        (measurePreserving_eval (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)) i)
    have he : {γ : I → Fin 3 → ℂ | n < ‖γ i ℓ‖} =
        (fun γ => γ i ℓ) ⁻¹' {z : ℂ | n < ‖z‖} := rfl
    rw [he,hf.measure_preimage (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet]
    exact hTail n hn
  have hset : {γ : I → Fin 3 → ℂ | ∃ i ℓ, n < ‖γ i ℓ‖} =
      ⋃ i, ⋃ ℓ, {γ | n < ‖γ i ℓ‖} := by ext γ; simp
  rw [hset]
  calc
    μ (⋃ i, ⋃ ℓ, {γ | n < ‖γ i ℓ‖}) ≤
        ∑ i, μ (⋃ ℓ, {γ | n < ‖γ i ℓ‖}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ∑ ℓ, μ {γ | n < ‖γ i ℓ‖} :=
      Finset.sum_le_sum (fun i _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, ENNReal.ofReal (M/n^8) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun ℓ _ => hm i ℓ))
    _ = _ := by simp [mul_assoc]
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set MeasureTheory
open scoped ENNReal

theorem uniform_polynomial_smallBall (B C : ℝ) (hB : 0 < B) (hC : 0 < C) :
    ∃ A > 0, ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) (F : Ω → (Fin 3 → ℝ) → ((Fin 1 ⊕ Fin 3) → ℝ))
      (G : Set Ω) (K : Set (Fin 3 → ℝ)) (n L : ℝ),
      1 ≤ n → 0 ≤ L → L ≤ n^4 →
      (∀ x ∈ K, ‖x‖ ≤ B) →
      (∀ outcome ∈ G, ∀ x ∈ K, ∀ y ∈ K, ‖F outcome x-F outcome y‖ ≤ (L*n^6)*dist x y) →
      (∀ x ∈ K, ∀ r : ℝ, 0 ≤ r →
        μ {outcome | ‖F outcome x‖ ≤ r} ≤ ENNReal.ofReal (C*n^28*r^4)) →
      μ {outcome | ∃ x ∈ K, ‖F outcome x‖ < 1/n^110} ≤
        μ Gᶜ+ENNReal.ofReal (A/n^52) := by
  classical
  obtain ⟨Q,hQ,hnet⟩ := bounded_three_polynomial_net B hB 1 (by norm_num)
  refine ⟨16*Q*C,by positivity,?_⟩
  intro Ω _ μ F G K n L hn hL hLn hK hLip hsmall
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hn120 : 1 ≤ n^120 := one_le_pow₀ hn
  obtain ⟨t,htK,htcard,htcover⟩ := hnet K hK (n^120) hn120
  have hδ : (L*n^6)*(1/n^120) ≤ 1/n^110 := by
    calc
      _ ≤ (n^4*n^6)*(1/n^120) := by gcongr
      _ = _ := by field_simp
  have hr : 0 ≤ 2/n^110 := by positivity
  have hnetSmall (i : t) : μ {outcome | ‖F outcome i.1‖ < 1/n^110+(L*n^6)*(1/n^120)} ≤
      ENNReal.ofReal (C*n^28*(2/n^110)^4) := by
    apply (measure_mono (show {outcome | ‖F outcome i.1‖ < 1/n^110+(L*n^6)*(1/n^120)} ⊆
        {outcome | ‖F outcome i.1‖ ≤ 2/n^110} from fun outcome hω => by
          change ‖F outcome i.1‖ < _ at hω
          change ‖F outcome i.1‖ ≤ _
          apply hω.le.trans
          calc
            _ ≤ 1/n^110+1/n^110 := add_le_add le_rfl hδ
            _ = _ := by ring)).trans
    exact hsmall i.1 (htK i.2) _ hr
  have h := probability_bad_jet_le μ F G K (fun i : t => i.1)
    (1/n^120) (1/n^110) (L*n^6) (by positivity)
    (fun x hx => by obtain ⟨y,hy,hd⟩ := htcover x hx; exact ⟨⟨y,hy⟩,hd⟩)
    (fun outcome hω x hx i => hLip outcome hω x hx i (htK i.2)) _ hnetSmall
  apply h.trans (add_le_add le_rfl ?_)
  have hcard : (Fintype.card t : ℝ) ≤ Q*n^360 := by
    simpa only [Fintype.card_coe,←pow_mul] using htcard
  rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card t : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Q*n^360)*(C*n^28*(2/n^110)^4) := by gcongr
    _ = _ := by field_simp; ring

theorem gaussian_uniform_polynomial_smallBall (B C Q : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hQ : 0 < Q) :
    ∃ A > 0, ∀ (I : Type) [Fintype I]
      (F : (I → Fin 3 → ℂ) → (Fin 3 → ℝ) → ((Fin 1 ⊕ Fin 3) → ℝ))
      (K : Set (Fin 3 → ℝ)) (n L : ℝ),
      1 ≤ n → 0 ≤ L → L ≤ n^4 →
      (Fintype.card I : ℝ) ≤ Q*n^3 → (∀ x ∈ K, ‖x‖ ≤ B) →
      (∀ γ, (∀ i ℓ, ‖γ i ℓ‖ ≤ n) → ∀ x ∈ K, ∀ y ∈ K,
        ‖F γ x-F γ y‖ ≤ (L*n^6)*dist x y) →
      (∀ x ∈ K, ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => ProbabilityTheory.stdGaussian ℂ)))
          {γ | ‖F γ x‖ ≤ r} ≤ ENNReal.ofReal (C*n^28*r^4)) →
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => ProbabilityTheory.stdGaussian ℂ)))
        {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ x ∈ K, ‖F γ x‖ < 1/n^110} ≤
        ENNReal.ofReal (A/n^5) := by
  classical
  obtain ⟨M,hM,hTail⟩ := finite_gaussian_coefficient_tail
  obtain ⟨A,hA,hNet⟩ := uniform_polynomial_smallBall B C hB hC
  refine ⟨6*Q*M+A,by positivity,?_⟩
  intro I _ F K n L hn hL hLn hcard hK hLip hsmall
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => ProbabilityTheory.stdGaussian ℂ))
  let G : Set (I → Fin 3 → ℂ) := {γ | ∀ i ℓ, ‖γ i ℓ‖ ≤ n}
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hG : Gᶜ = {γ | ∃ i ℓ, n < ‖γ i ℓ‖} := by ext γ; simp [G]
  have ht : μ Gᶜ ≤ ENNReal.ofReal (3*Q*M/n^5) := by
    rw [hG]
    apply (hTail I n hn0).trans
    rw [←ENNReal.ofReal_natCast,show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card I : ℝ)),
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card I : ℝ)*3)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (Q*n^3)*3*(M/n^8) := by gcongr
      _ = _ := by field_simp
  have hj := hNet _ μ F G K n L hn hL hLn hK (fun γ hγ => hLip γ hγ) hsmall
  have hset : {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ x ∈ K, ‖F γ x‖ < 1/n^110} =
      Gᶜ ∪ {γ | ∃ x ∈ K, ‖F γ x‖ < 1/n^110} := by rw [hG]; rfl
  rw [hset]
  apply (measure_union_le _ _).trans
  apply (add_le_add ht (hj.trans (add_le_add ht le_rfl))).trans
  rw [←ENNReal.ofReal_add (by positivity : 0 ≤ 3*Q*M/n^5) (by positivity : 0 ≤ A/n^52),
    ←ENNReal.ofReal_add (by positivity : 0 ≤ 3*Q*M/n^5) (by positivity : 0 ≤ 3*Q*M/n^5+A/n^52)]
  apply ENNReal.ofReal_le_ofReal
  have hp : n^5 ≤ n^52 := pow_le_pow_right₀ hn (by omega)
  have hd : A/n^52 ≤ A/n^5 := div_le_div_of_nonneg_left hA.le (pow_pos hn0 _) hp
  calc
    _ ≤ 3*Q*M/n^5+(3*Q*M/n^5+A/n^5) := by linarith
    _ = _ := by ring

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_NormIteratedFDerivCompLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

lemma contDiff_finiteWaveSuperposition {E I : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : E → ℝ} {U : I → Fin 3 → E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) : ContDiff ℝ ∞ (finiteWaveSuperposition w U γ) :=
  hw.add (ContDiff.sum (fun i _ => ContDiff.sum (fun ℓ _ =>
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ)))))

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_real_complex_mul {u : E → ℂ}
    (hu : ContDiff ℝ ∞ u) (a : ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => (a*u y).re) x‖ ≤
      ‖a‖*‖iteratedFDeriv ℝ j u x‖ := by
  have h : ContDiff ℝ ∞ (fun y => a*u y) := contDiff_const.mul hu
  have hh := Complex.reCLM.norm_iteratedFDeriv_comp_left h.contDiffAt (x := x) (n := j) (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))
  have he : iteratedFDeriv ℝ j (fun y => a*u y) x = a • iteratedFDeriv ℝ j u x :=
    by simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (a := a) (x := x) (hu.of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt
  simpa only [Complex.reCLM_norm,one_mul,he,norm_smul,Function.comp_def,Complex.reCLM_apply] using hh

lemma norm_iteratedFDeriv_finiteWaveSum {I : Type*} [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤
      ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ := by
  classical
  have hs (i) (ℓ) : ContDiff ℝ ∞ (fun y => (γ i ℓ*U i ℓ y).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ))
  rw [iteratedFDeriv_fun_sum_apply (fun i _ =>
    ((ContDiff.sum (fun ℓ _ => hs i ℓ)).of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [iteratedFDeriv_fun_sum_apply (fun ℓ _ => ((hs i ℓ).of_le (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))).contDiffAt)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ℓ _ =>
    norm_iteratedFDeriv_real_complex_mul (hU i ℓ) (γ i ℓ) j x))

theorem finiteWaveSum_derivative_bound {I : Type*} [Fintype I]
    {U : I → Fin 3 → E → ℂ} (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q T W : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hW : 0 ≤ W)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E) (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) x‖ ≤
      (3*Q*T)*n^(j+4)*W := by
  classical
  calc
    _ ≤ ∑ i, ∑ ℓ, ‖γ i ℓ‖*‖iteratedFDeriv ℝ j (U i ℓ) x‖ :=
      norm_iteratedFDeriv_finiteWaveSum hU γ j x
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, n*(T*n^j*W) := by
      apply Finset.sum_le_sum; intro i _
      exact Finset.sum_le_sum (fun ℓ _ =>
        mul_le_mul (hγ i ℓ) (hbound i ℓ) (norm_nonneg _) hn)
    _ = (Fintype.card I : ℝ)*3*(n*(T*n^j*W)) := by simp; ring
    _ ≤ (Q*n^3)*3*(n*(T*n^j*W)) := by gcongr
    _ = _ := by rw [pow_add]; ring
end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalized_scalar_derivative_bound {f W : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hW : DifferentiableAt ℝ W x) (hW0 : 0 < W x)
    {B₀ B₁ H : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hH : 0 ≤ H)
    (h₀ : ‖f x‖ ≤ B₀*W x) (h₁ : ‖fderiv ℝ f x‖ ≤ B₁*W x)
    (hlog : ‖fderiv ℝ W x‖ ≤ H*W x) :
    DifferentiableAt ℝ (fun y => (W y)⁻¹*f y) x ∧
      ‖fderiv ℝ (fun y => (W y)⁻¹*f y) x‖ ≤ B₁+B₀*H := by
  have hi := (hasDerivAt_inv hW0.ne').comp_hasFDerivAt x hW.hasFDerivAt
  have hd := hi.mul hf.hasFDerivAt
  refine ⟨hd.differentiableAt,?_⟩
  change ‖fderiv ℝ (((fun z : ℝ => z⁻¹) ∘ W)*f) x‖ ≤ _
  rw [hd.fderiv]
  calc
    _ ≤ ‖(W x)⁻¹ • fderiv ℝ f x‖ +
        ‖f x • (-(W x^2)⁻¹ • fderiv ℝ W x)‖ := norm_add_le _ _
    _ = (W x)⁻¹*‖fderiv ℝ f x‖ + ‖f x‖*((W x^2)⁻¹*‖fderiv ℝ W x‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_neg,
        abs_of_pos hW0,abs_of_pos (pow_pos hW0 2)]
    _ ≤ (W x)⁻¹*(B₁*W x)+(B₀*W x)*((W x^2)⁻¹*(H*W x)) := by
      apply add_le_add
      · simpa only [mul_comm] using
          mul_le_mul h₁ (le_refl ((W x)⁻¹))
            (inv_nonneg.mpr hW0.le) (mul_nonneg hB₁ hW0.le)
      · apply mul_le_mul h₀ _
          (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (norm_nonneg _))
          (mul_nonneg hB₀ hW0.le)
        simpa only [mul_comm] using
          mul_le_mul hlog (le_refl ((W x^2)⁻¹))
            (inv_nonneg.mpr (sq_nonneg _)) (mul_nonneg hH hW0.le)
    _ = _ := by field_simp

lemma norm_fderiv_evaluation {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (v : E) :
    ‖fderiv ℝ (fun y => fderiv ℝ u y v) x‖ ≤ ‖v‖*‖fderiv ℝ (fderiv ℝ u) x‖ := by
  let L := ContinuousLinearMap.apply ℝ ℝ v
  have hL : ‖L‖ ≤ ‖v‖ := L.opNorm_le_bound (norm_nonneg _) (fun f => by
    simpa only [L,ContinuousLinearMap.apply_apply,mul_comm] using f.le_opNorm v)

  change ‖fderiv ℝ (L ∘ fderiv ℝ u) x‖ ≤ _
  rw [fderiv_comp x L.differentiableAt hu,L.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalized_scalar_lipschitz_on {f W : E → ℝ} {S : Set E} (hS : Convex ℝ S)
    (hf : Differentiable ℝ f) (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    {B₀ B₁ H : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hH : 0 ≤ H)
    (h₀ : ∀ x ∈ S, ‖f x‖ ≤ B₀*W x) (h₁ : ∀ x ∈ S, ‖fderiv ℝ f x‖ ≤ B₁*W x)
    (hlog : ∀ x ∈ S, ‖fderiv ℝ W x‖ ≤ H*W x) (x y : E) (hx : x ∈ S) (hy : y ∈ S) :
    ‖(W x)⁻¹*f x-(W y)⁻¹*f y‖ ≤ (B₁+B₀*H)*dist x y := by
  have hb (z : E) (hz : z ∈ S) := normalized_scalar_derivative_bound (hf z) (hW z) (hW0 z)
    hB₀ hB₁ hH (h₀ z hz) (h₁ z hz) (hlog z hz)
  simpa only [dist_eq_norm] using
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (hb z hz).1)
      (fun z hz => (hb z hz).2) hS hy hx

theorem realWaveJet_lipschitz_of_relative_bounds_on
    {S : Set (Fin 3 → ℝ)} (hS : Convex ℝ S)
    {u W : (Fin 3 → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u)
    (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    {n B₀ B₁ B₂ H L : ℝ} (hn : 0 < n)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hH : 0 ≤ H)
    (h₀ : ∀ x ∈ S, ‖u x‖ ≤ B₀*W x)
    (h₁ : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ B₁*W x)
    (h₂ : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B₂*W x)
    (hlog : ∀ x ∈ S, ‖fderiv ℝ W x‖ ≤ H*W x)
    (hL₀ : B₁+B₀*H ≤ L) (hL₁ : n⁻¹*(B₂+B₁*H) ≤ L) (x y : Fin 3 → ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    ‖realWaveJet n (W x) u x-realWaveJet n (W y) u y‖ ≤ L*dist x y := by
  have hL : 0 ≤ L := (by positivity : 0 ≤ B₁+B₀*H).trans hL₀
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL dist_nonneg)).mpr
  intro i
  rcases i with i|i
  · exact (normalized_scalar_lipschitz_on hS (hu.differentiable (by simp)) hW hW0
      hB₀ hB₁ hH h₀ h₁ hlog x y hx hy).trans (mul_le_mul_of_nonneg_right hL₀ dist_nonneg)
  · let v : Fin 3 → ℝ := Pi.single i 1
    have hv : ‖v‖ = 1 := by simp [v,Pi.norm_single]
    have hd := (hu.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ (∞ : ℕ∞ω) by simp)).differentiable (by simp)
    have hfv : Differentiable ℝ (fun z => fderiv ℝ u z v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hd
    have hv₀ (z) (hz : z ∈ S) : ‖fderiv ℝ u z v‖ ≤ B₁*W z := by
      exact ((fderiv ℝ u z).le_opNorm v).trans (by simpa [hv] using h₁ z hz)
    have hv₁ (z) (hz : z ∈ S) : ‖fderiv ℝ (fun z => fderiv ℝ u z v) z‖ ≤ B₂*W z :=
      (norm_fderiv_evaluation (hd z) v).trans (by simpa [hv] using h₂ z hz)
    have hh := normalized_scalar_lipschitz_on hS hfv hW hW0 hB₁ hB₂ hH hv₀ hv₁ hlog x y hx hy
    change ‖n⁻¹*(W x)⁻¹*fderiv ℝ u x v-n⁻¹*(W y)⁻¹*fderiv ℝ u y v‖ ≤ _
    rw [mul_assoc,mul_assoc,←mul_sub,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hL₁ (dist_nonneg : 0 ≤ dist x y))
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set
open scoped ContDiff

lemma norm_iteratedFDeriv_comp_linear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) {u : F → G} (hu : ContDiff ℝ ∞ u) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (u ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j u (L x)‖*‖L‖^j := by
  rw [L.iteratedFDeriv_comp_right hu x (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) from
    le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)))]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j u (L x)) (fun _ : Fin j => L)

lemma physical_packet_low_derivative {u : NormalWaveSpace → ℂ}
    (hu : ContDiff ℝ ∞ u) {T n W : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T) (hW : 0 ≤ W)
    {j : ℕ} (hj : j ≤ 2) (x : Fin 3 → ℝ)
    (hbound : ‖iteratedFDeriv ℝ j u (normalWaveEquiv x)‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (u ∘ normalWaveEquiv) x‖ ≤
      (T*(max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2)*n^j*W := by
  have hp : ‖normalWaveEquiv.toContinuousLinearMap‖^j ≤
      (max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  exact (norm_iteratedFDeriv_comp_linear normalWaveEquiv.toContinuousLinearMap hu j x).trans
    ((mul_le_mul hbound hp (pow_nonneg (norm_nonneg _) _) (by positivity)).trans_eq (by ring))

theorem finiteWaveSuperposition_relative_derivative {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    {w : E → ℝ} {U : I → Fin 3 → E → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (γ : I → Fin 3 → ℂ) {n Q T T₀ W : ℝ}
    (hn : 1 ≤ n) (hT : 0 ≤ T) (hT₀ : 0 ≤ T₀) (hW : 0 ≤ W)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (j : ℕ) (x : E)
    (hwbound : ‖iteratedFDeriv ℝ j w x‖ ≤ T₀*n^j*W)
    (hbound : ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W) :
    ‖iteratedFDeriv ℝ j (finiteWaveSuperposition w U γ) x‖ ≤
      (T₀+3*Q*T)*n^(j+4)*W := by
  classical
  have hs : ContDiff ℝ ∞ (fun y => ∑ i, ∑ ℓ, (γ i ℓ*U i ℓ y).re) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun ℓ _ =>
      Complex.reCLM.contDiff.comp (contDiff_const.mul (hU i ℓ))))
  have hle : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  unfold finiteWaveSuperposition
  rw [fun_iteratedFDeriv_add_apply (hw.of_le hle).contDiffAt (hs.of_le hle).contDiffAt]
  apply (norm_add_le _ _).trans
  have hsum := finiteWaveSum_derivative_bound hU γ (zero_le_one.trans hn) hT hW hcard hγ j x hbound
  have hp : n^j ≤ n^(j+4) := pow_le_pow_right₀ hn (by omega)
  calc
    _ ≤ T₀*n^j*W+(3*Q*T)*n^(j+4)*W := add_le_add hwbound hsum
    _ ≤ T₀*n^(j+4)*W+(3*Q*T)*n^(j+4)*W := by gcongr
    _ = _ := by ring

theorem finiteWaveSuperposition_normalized_lipschitz {I : Type*} [Fintype I]
    {S : Set (Fin 3 → ℝ)} (hS : Convex ℝ S)
    {w W : (Fin 3 → ℝ) → ℝ} {U : I → Fin 3 → (Fin 3 → ℝ) → ℂ}
    (hw : ContDiff ℝ ∞ w) (hU : ∀ i ℓ, ContDiff ℝ ∞ (U i ℓ))
    (hW : Differentiable ℝ W) (hW0 : ∀ x, 0 < W x)
    (γ : I → Fin 3 → ℂ) {n Q T T₀ H : ℝ}
    (hn : 1 ≤ n) (hQ : 0 ≤ Q) (hT : 0 ≤ T) (hT₀ : 0 ≤ T₀) (hH : 0 ≤ H)
    (hcard : (Fintype.card I : ℝ) ≤ Q*n^3) (hγ : ∀ i ℓ, ‖γ i ℓ‖ ≤ n)
    (hwbound : ∀ x ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j w x‖ ≤ T₀*n^j*W x)
    (hbound : ∀ x ∈ S, ∀ j ≤ 2, ∀ i ℓ, ‖iteratedFDeriv ℝ j (U i ℓ) x‖ ≤ T*n^j*W x)
    (hlog : ∀ x ∈ S, ‖fderiv ℝ W x‖ ≤ H*n*W x)
    (x y : Fin 3 → ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    ‖realWaveJet n (W x) (finiteWaveSuperposition w U γ) x-
      realWaveJet n (W y) (finiteWaveSuperposition w U γ) y‖ ≤
      ((T₀+3*Q*T)*(1+H)*n^6)*dist x y := by
  let A := T₀+3*Q*T
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hb (z) (hz : z ∈ S) (j) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j (finiteWaveSuperposition w U γ) z‖ ≤ A*n^(j+4)*W z :=
    finiteWaveSuperposition_relative_derivative hw hU γ hn hT hT₀ (hW0 z).le hcard hγ j z
      (hwbound z hz j hj) (hbound z hz j hj)
  apply realWaveJet_lipschitz_of_relative_bounds_on hS
    (contDiff_finiteWaveSuperposition hw hU γ) hW hW0 hn0
    (B₀ := A*n^4) (B₁ := A*n^5) (B₂ := A*n^6) (H := H*n)
    (by positivity) (by positivity) (by positivity) (by positivity)
    ?_ ?_ ?_ hlog ?_ ?_ x y hx hy
  · intro z hz
    simpa only [norm_iteratedFDeriv_zero,zero_add] using hb z hz 0 (by omega)
  · intro z hz
    simpa only [norm_iteratedFDeriv_one] using hb z hz 1 (by omega)
  · intro z hz
    have he : ‖fderiv ℝ (fderiv ℝ (finiteWaveSuperposition w U γ)) z‖ =
        ‖iteratedFDeriv ℝ 2 (finiteWaveSuperposition w U γ) z‖ := by
      rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    rw [he]
    exact hb z hz 2 (by omega)
  · calc
      A*n^5+(A*n^4)*(H*n) = A*(1+H)*n^5 := by ring
      _ ≤ A*(1+H)*n^6 := by gcongr; norm_num
  · calc
      n⁻¹*(A*n^6+(A*n^5)*(H*n)) = A*(1+H)*n^5 := by field_simp
      _ ≤ A*(1+H)*n^6 := by gcongr; norm_num

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_CompactActualWavesSubregionsSupported
attribute [-instance] _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_acg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_mod _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_nacg _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_ns _root_.OAI.YauCounterexamples.CompactMetricAtlas.realH_snacg _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_finite _root_.OAI.YauCounterexamples.MetricIntegralAtlas.volumeMeasure_openPos _root_.OAI.YauCounterexamples.circle_dimension_fact _root_.OAI.YauCounterexamples.normalCoordinateVolume_finiteOnCompacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal

theorem compact_actual_sign_noncancellation_supported_oai
    (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    {O : Set NormalWaveSpace} (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ p₀ > 0,
    ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
    (∀ x ∈ K, fderiv ℝ φ x ≠ 0 → actualProfileStrict g φ x) →
    (∀ x ∈ K, fderiv ℝ φ x = 0 →
      ∃ P : Submodule ℝ NormalWaveSpace, Module.finrank ℝ P = 2 ∧
        ∀ v ∈ P, v ≠ 0 → 0 < actualCoordinateHessian g φ x v v) →
    ∀ m D : ℕ, ∀ T₀ H : ℝ, 0 ≤ T₀ → 0 ≤ H → ∃ c₀ > 0, ∃ T > 0, ∃ c > 0, ∃ A > 0, ∃ Q > 0,
    ∃ N : ℝ, 2 ≤ N ∧ ∀ s : ℝ, N ≤ s →
    let n := s^4
    ∃ t : Finset (Fin 3 → ℝ), ∃ p : t → metricFrameSet g K,
    ∃ U : t → Fin 3 → NormalWaveSpace → ℂ,
      (∀ i ℓ, tsupport (U i ℓ) ⊆ O) ∧
      (t.card : ℝ) ≤ Q*n^3 ∧
      (∀ i ℓ, ContDiff ℝ ∞ (U i ℓ) ∧ HasCompactSupport (U i ℓ) ∧
        U i ℓ (p i).1.1 = Complex.exp ((n : ℂ)*(φ (p i).1.1 : ℂ)) ∧
        ∀ y : NormalWaveSpace, ∀ k ≤ max m 2,
          ‖iteratedFDeriv ℝ k (U i ℓ) y‖ ≤ T*n^k*Real.exp (n*φ y)*Real.exp (-c*n*‖y-(p i).1.1‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun w => complexLaplaceBeltrami g (U i ℓ) w +
            (n : ℂ)*((n : ℂ)+2)*U i ℓ w) y‖ ≤ T*(n^(D+1))⁻¹*Real.exp (n*φ y)) ∧
      (∀ S : Set (Fin 3 → ℝ), Convex ℝ S →
        ∀ E : Set (Fin 3 → ℝ), E ⊆ S → E ⊆ normalWaveEquiv.symm '' K →
        ∀ w : NormalWaveSpace → ℝ, ContDiff ℝ ∞ w →
        ∀ W : (Fin 3 → ℝ) → ℝ, Differentiable ℝ W → (∀ y, 0 < W y) →
        (∀ y ∈ S, Real.exp (n*φ (normalWaveEquiv y)) ≤ W y) →
        (∀ y ∈ E, W y ≤ (1+n^6)*Real.exp (n*φ (normalWaveEquiv y))) →
        (∀ y ∈ S, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (w ∘ normalWaveEquiv) y‖ ≤ T₀*n^j*W y) →
        (∀ y ∈ S, ‖fderiv ℝ W y‖ ≤ H*n*W y) →
        (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
          {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ y ∈ E,
            ‖realWaveJet n (W y) (finiteWaveSuperposition (w ∘ normalWaveEquiv)
              (fun i ℓ => U i ℓ ∘ normalWaveEquiv) γ) y‖ < 1/n^110} ≤
          ENNReal.ofReal (A/n^5)) ∧
      ∀ b : NormalWaveSpace → ℝ, (∀ y ∈ K, |b y| ≤ c₀*Real.exp (n*φ y)) →
      ∀ x ∈ K, ∀ ℓ : ℝ, profileFrequencyScale g φ x ≤ ℓ → ℓ ≤ 2*profileFrequencyScale g φ x →
      (∀ j, packetAxisShift x n ε ℓ j ∈ K) →
      ∃ j, ENNReal.ofReal p₀ ≤ (Measure.pi (fun _ : t => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | finiteWaveSuperposition b U γ x *
          finiteWaveSuperposition b U γ (packetAxisShift x n ε ℓ j) < 0} := by
  classical
  obtain ⟨ε,hε,hε1,p₀,hp₀,hdata⟩ := compact_actual_waves_sign_and_jets_supported g hK hO hKO
  refine ⟨ε,hε,hε1,p₀,hp₀,?_⟩
  intro φ hφ hnc hcrit m D T₀ H hT₀ hH
  obtain ⟨c₀,hc₀,T,hT,c,hc,C,hC,Q,hQ,N,hN,hdata⟩ := hdata φ hφ hnc hcrit (max m 2) D
  obtain ⟨B,hB,hBK⟩ := (hK.image normalWaveEquiv.symm.continuous).isBounded.exists_pos_norm_le
  obtain ⟨A,hA,hNet⟩ := gaussian_uniform_polynomial_smallBall B C Q hB hC hQ
  let T' := T*(max 1 ‖normalWaveEquiv.toContinuousLinearMap‖)^2
  have hT' : 0 ≤ T' := by dsimp [T']; positivity
  let L := (T₀+3*Q*T')*(1+H)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨c₀,hc₀,T,hT,c,hc,A,hA,Q,hQ,max N L,le_max_of_le_left hN,?_⟩
  intro s hs
  have hsN : N ≤ s := (le_max_left _ _).trans hs
  have hs1 : 1 ≤ s := (by linarith : (1:ℝ) ≤ N).trans hsN
  have hs4 : s ≤ s^4 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (show 1 ≤ 4 by omega)
  let n := s^4
  have hn1 : 1 ≤ n := hs1.trans hs4
  have hnL : L ≤ n^4 := ((le_max_right N L).trans hs).trans (hs4.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (show 1 ≤ 4 by omega)))
  obtain ⟨t,p,U,hSupport,ht,hU,hlaw,hsign⟩ := hdata s hsN
  refine ⟨t,p,U,hSupport,ht,hU,?_,hsign⟩
  intro S hS E hES hEK w hw W hW hW0 hWlower hWupper hwbound hlog
  let U' : t → Fin 3 → (Fin 3 → ℝ) → ℂ := fun i ℓ => U i ℓ ∘ normalWaveEquiv
  have hU' (i) (ℓ) : ContDiff ℝ ∞ (U' i ℓ) := (hU i ℓ).1.comp normalWaveEquiv.contDiff
  have hw' : ContDiff ℝ ∞ (w ∘ normalWaveEquiv) := hw.comp normalWaveEquiv.contDiff
  have hcard : (Fintype.card t : ℝ) ≤ Q*n^3 := by simpa using ht
  refine hNet t (fun γ y => realWaveJet n (W y)
    (finiteWaveSuperposition (w ∘ normalWaveEquiv) U' γ) y) E n L
    hn1 hL hnL hcard (fun y hy => hBK y (hEK hy)) ?_ ?_
  · intro γ hγ x hx y hy
    apply finiteWaveSuperposition_normalized_lipschitz hS hw' hU' hW hW0 γ
      hn1 hQ.le hT' hT₀ hH hcard hγ hwbound ?_ hlog x y (hES hx) (hES hy)
    intro z hz j hj i ℓ
    have hb := physical_packet_low_derivative (hU i ℓ).1 (zero_le_one.trans hn1)
      hT.le (Real.exp_pos _).le hj z (le_trans ((hU i ℓ).2.2.2 _ j (hj.trans (le_max_right _ _))).1 (by
        have he : Real.exp (-c*n*‖normalWaveEquiv z-(p i).1.1‖^2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have hn0 := zero_le_one.trans hn1
            exact mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hn0) (sq_nonneg _))
        exact mul_le_of_le_one_right (by positivity) he))
    exact hb.trans (mul_le_mul_of_nonneg_left (hWlower z hz) (by positivity))
  · intro y hy r hr
    let R := W y-Real.exp (n*φ (normalWaveEquiv y))
    have hR : 0 ≤ R := sub_nonneg.mpr (hWlower y (hES hy))
    have hRcap : R ≤ n^6*Real.exp (n*φ (normalWaveEquiv y)) := by
      have := hWupper y hy
      dsimp [R]; nlinarith
    have he : Real.exp (n*φ (normalWaveEquiv y))+R = W y := by dsimp [R]; ring
    have hh := hlaw w hw y (hEK hy) R hR hRcap r hr
    rw [he] at hh
    exact hh

end


open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported_oai := @OAI.YauCounterexamples.compact_actual_sign_noncancellation_supported_oai
