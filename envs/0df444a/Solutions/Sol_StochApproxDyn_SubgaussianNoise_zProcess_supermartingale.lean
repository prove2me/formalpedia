-- Prove2me | solution 1 for StochApproxDyn.SubgaussianNoise.zProcess_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:12:06.801791+00:00
-- url     : https://prove2.me/submissions/8f36f1ca-ed54-47dc-b06a-165d9507c562

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace ZProc85

theorem integrable_mul_of_condExp_le {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfi : Integrable f μ) (hg : Integrable g μ) (hg0 : ∀ ω, 0 ≤ g ω)
    (C : ℝ) (hC : μ[g | m] ≤ᵐ[μ] fun _ => C) : Integrable (f * g) μ := by
  have hfm : StronglyMeasurable[m0] f := hf.mono hm
  refine ⟨hfm.aestronglyMeasurable.mul hg.1, ?_⟩
  set fk : ℕ → Ω → ℝ := fun k ω => min (f ω) k with hfk
  have hfkm : ∀ k, StronglyMeasurable[m] (fk k) := by
    intro k
    exact (continuous_id.min continuous_const).comp_stronglyMeasurable hf
  have hfk0 : ∀ k ω, 0 ≤ fk k ω := fun k ω => le_min (hf0 ω) (Nat.cast_nonneg k)
  have hfkb : ∀ k, ∀ᵐ ω ∂μ, ‖fk k ω‖ ≤ k := fun k => Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfk0 k ω)]; exact min_le_right _ _
  have hint : ∀ k, Integrable (fun ω => fk k ω * g ω) μ := fun k =>
    hg.bdd_mul ((hfkm k).mono hm).aestronglyMeasurable (hfkb k)
  set B : ℝ := ∫ ω, f ω * |C| ∂μ
  have hbound : ∀ k, ∫ ω, fk k ω * g ω ∂μ ≤ B := by
    intro k
    have h1 : ∫ ω, fk k ω * g ω ∂μ = ∫ ω, (μ[fk k * g | m]) ω ∂μ :=
      (integral_condExp hm).symm
    have h2 : μ[fk k * g | m] =ᵐ[μ] fk k * μ[g | m] :=
      condExp_stronglyMeasurable_mul_of_bound hm (hfkm k) hg k (hfkb k)
    rw [h1, integral_congr_ae h2]
    have hi2 : Integrable (fun ω => fk k ω * (μ[g | m]) ω) μ :=
      integrable_condExp.bdd_mul ((hfkm k).mono hm).aestronglyMeasurable (hfkb k)
    refine integral_mono_ae hi2 (hfi.mul_const _) ?_
    filter_upwards [hC] with ω hω
    simp only [Pi.mul_apply]
    calc fk k ω * (μ[g | m]) ω ≤ fk k ω * C := mul_le_mul_of_nonneg_left hω (hfk0 k ω)
      _ ≤ fk k ω * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) (hfk0 k ω)
      _ ≤ f ω * |C| := mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg C)
  have hsup : ∀ ω, ‖(f * g) ω‖ₑ = ⨆ k : ℕ, ENNReal.ofReal (fk k ω * g ω) := by
    intro ω
    rw [Pi.mul_apply, Real.enorm_eq_ofReal (mul_nonneg (hf0 ω) (hg0 ω))]
    apply le_antisymm
    · refine le_iSup_of_le (⌈f ω⌉₊) (le_of_eq ?_)
      congr 1
      simp only [hfk, min_eq_left (Nat.le_ceil (f ω))]
    · exact iSup_le fun k => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (hg0 ω))
  unfold HasFiniteIntegral
  simp_rw [hsup]
  rw [lintegral_iSup' (fun k => (hint k).1.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun ω => fun a b hab =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_min_left _ (by exact_mod_cast hab)) (hg0 ω)))]
  refine lt_of_le_of_lt (b := ENNReal.ofReal B) (iSup_le fun k => ?_) ENNReal.ofReal_lt_top
  show ∫⁻ ω, ENNReal.ofReal (fk k ω * g ω) ∂μ ≤ ENNReal.ofReal B
  rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
    (Eventually.of_forall fun ω => mul_nonneg (hfk0 k ω) (hg0 ω))]
  exact ENNReal.ofReal_le_ofReal (hbound k)

end ZProc85

open MeasureTheory ProbabilityTheory InnerProductSpace StochApproxDyn.SubgaussianNoise in
theorem solution {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    Supermartingale
      (fun (n : ℕ) (ω : Ω) =>
        Real.exp (∑ i ∈ Finset.range n, ⟪θ, γ (i + 1) • U (i + 1) ω⟫_ℝ
          - Γ / 2 * ∑ i ∈ Finset.range n, γ (i + 1) ^ 2 * ‖θ‖ ^ 2))
      ℱ P := by
  set Z : ℕ → Ω → ℝ := fun (n : ℕ) (ω : Ω) =>
        Real.exp (∑ i ∈ Finset.range n, ⟪θ, γ (i + 1) • U (i + 1) ω⟫_ℝ
          - Γ / 2 * ∑ i ∈ Finset.range n, γ (i + 1) ^ 2 * ‖θ‖ ^ 2) with hZ
  set Y : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (-(Γ / 2 * (γ (n + 1) ^ 2 * ‖θ‖ ^ 2))) *
      Real.exp ⟪γ (n + 1) • θ, U (n + 1) ω⟫_ℝ with hY
  have hrec : ∀ n, Z (n + 1) = Z n * Y n := by
    intro n; funext ω
    simp only [hZ, hY, Pi.mul_apply, Finset.sum_range_succ, real_inner_smul_left,
      real_inner_smul_right]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hU : ∀ i, StronglyMeasurable[ℱ (i + 1)] (U (i + 1)) := hRM.2.2.2.1
  have hadp : StronglyAdapted ℱ Z := by
    intro n
    have hm : ∀ i ∈ Finset.range n, Measurable[ℱ n] (fun ω => ⟪θ, γ (i + 1) • U (i + 1) ω⟫_ℝ) := by
      intro i hi
      have hle : ℱ (i + 1) ≤ ℱ n := ℱ.mono (Finset.mem_range.mp hi)
      have hUm : Measurable[ℱ n] (U (i + 1)) := ((hU i).mono hle).measurable
      have hs : Measurable[ℱ n] fun ω => γ (i + 1) • U (i + 1) ω := hUm.const_smul (γ (i + 1))
      exact (continuous_const.inner continuous_id).measurable.comp hs
    refine Measurable.stronglyMeasurable ?_
    exact Real.measurable_exp.comp ((Finset.measurable_sum _ hm).sub_const _)
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun n ω => by positivity
  have hZ0 : ∀ n ω, 0 ≤ Z n ω := fun n ω => by positivity
  have hYi : ∀ n, Integrable (Y n) P := fun n => (hsg n (γ (n + 1) • θ)).1.const_mul _
  have hYc : ∀ n, P[Y n | ℱ n] ≤ᵐ[P] fun _ => (1 : ℝ) := by
    intro n
    have h1 : P[Y n | ℱ n] =ᵐ[P]
        Real.exp (-(Γ / 2 * (γ (n + 1) ^ 2 * ‖θ‖ ^ 2))) •
          P[fun ω => Real.exp ⟪γ (n + 1) • θ, U (n + 1) ω⟫_ℝ | ℱ n] :=
      condExp_smul (Real.exp (-(Γ / 2 * (γ (n + 1) ^ 2 * ‖θ‖ ^ 2)))) _ _
    filter_upwards [h1, (hsg n (γ (n + 1) • θ)).2] with ω h1ω h2ω
    rw [h1ω, Pi.smul_apply, smul_eq_mul]
    have hn : ‖γ (n + 1) • θ‖ ^ 2 = γ (n + 1) ^ 2 * ‖θ‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hn] at h2ω
    calc Real.exp (-(Γ / 2 * (γ (n + 1) ^ 2 * ‖θ‖ ^ 2))) *
          (P[fun ω => Real.exp ⟪γ (n + 1) • θ, U (n + 1) ω⟫_ℝ | ℱ n]) ω
        ≤ Real.exp (-(Γ / 2 * (γ (n + 1) ^ 2 * ‖θ‖ ^ 2))) *
          Real.exp (Γ / 2 * (γ (n + 1) ^ 2 * ‖θ‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2ω (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hZi : ∀ n, Integrable (Z n) P := by
    intro n
    induction n with
    | zero => simp only [hZ, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]; exact integrable_const _
    | succ n ih =>
      rw [hrec n]
      exact ZProc85.integrable_mul_of_condExp_le (ℱ.le n) (hadp n) (hZ0 n) ih (hYi n) (hY0 n) 1 (hYc n)
  refine supermartingale_nat hadp hZi fun n => ?_
  rw [hrec n]
  have hpull : P[Z n * Y n | ℱ n] =ᵐ[P] Z n * P[Y n | ℱ n] :=
    condExp_mul_of_stronglyMeasurable_left (hadp n) (hrec n ▸ hZi (n + 1)) (hYi n)
  filter_upwards [hpull, hYc n] with ω h1 h2
  rw [h1, Pi.mul_apply]
  calc Z n ω * (P[Y n | ℱ n]) ω ≤ Z n ω * 1 := mul_le_mul_of_nonneg_left h2 (hZ0 n ω)
    _ = Z n ω := mul_one _
