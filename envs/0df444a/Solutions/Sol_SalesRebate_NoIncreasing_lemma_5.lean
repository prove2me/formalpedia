-- Prove2me | solution 1 for SalesRebate.NoIncreasing.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T02:21:26.329175+00:00
-- url     : https://prove2.me/submissions/f42eb69a-e7b1-4d42-8db8-81f931cb0477

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting

open MeasureTheory ProbabilityTheory BlackScholesModel SalesRebate.NoIncreasing

namespace SRAux

lemma cdf_eq_integral (t : ℝ) :
    stdNormalCDF t = ∫ z in Set.Iic t, gaussianPDFReal 0 1 z := by
  unfold stdNormalCDF
  rw [← integral_const_mul]
  congr 1; ext z
  simp [gaussianPDFReal]

lemma cdf_eq_measureReal (t : ℝ) :
    stdNormalCDF t = (gaussianReal 0 1).real (Set.Iic t) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero, ENNReal.toReal_ofReal,
    cdf_eq_integral]
  exact setIntegral_nonneg measurableSet_Iic (fun _ _ => gaussianPDFReal_nonneg _ _ _)

lemma cdf_eq_gaussian_Ici (m s t : ℝ) (hs : 0 < s) :
    stdNormalCDF ((m - t) / s) = (gaussianReal m (s ^ 2).toNNReal).real (Set.Ici t) := by
  have hmap : gaussianReal m (s ^ 2).toNNReal =
      (gaussianReal 0 1).map (fun z => (-s) * z + m) := by
    have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (-s)
    have h3 : (fun z : ℝ => (-s) * z + m) = (fun x => x + m) ∘ (fun x => (-s) * x) := rfl
    rw [h3, ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_add_const]
    congr 1
    · ring
    · ext; simp [Real.toNNReal_of_nonneg (sq_nonneg s)]
  rw [hmap, cdf_eq_measureReal, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ici]
  congr 2
  ext z
  simp only [Set.mem_Iic, Set.mem_preimage, Set.mem_Ici]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith


variable (M : Model) (hM : M.Valid)
include hM

lemma sigma_sq : M.σ ^ 2 = M.σε ^ 2 + M.σθ ^ 2 := by
  unfold Model.σ
  have := hM.σε_pos; have := hM.σθ_pos
  rw [Real.sq_sqrt (by positivity)]

lemma sigma_pos : 0 < M.σ := by
  unfold Model.σ
  have := hM.σε_pos
  exact Real.sqrt_pos.2 (by positivity)

lemma salesVolume_eq (c v : ℝ) :
    M.salesVolume c v = (gaussianReal v (M.σε ^ 2).toNNReal).real (Set.Ici c) :=
  cdf_eq_gaussian_Ici v M.σε c hM.σε_pos

lemma psi_eq (x : ℝ) : M.psi x = gaussianPDFReal M.θ (M.σ ^ 2).toNNReal x := by
  have hσ := sigma_pos M hM
  unfold Model.psi stdNormalPDF gaussianPDFReal
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  have h2 : Real.sqrt (2 * Real.pi * M.σ ^ 2) = Real.sqrt (2 * Real.pi) * M.σ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le]
  rw [h2]
  have h3 : -((M.θ - x) / M.σ) ^ 2 / 2 = -(x - M.θ) ^ 2 / (2 * M.σ ^ 2) := by
    field_simp; ring
  rw [h3]
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

lemma s1_ne : (M.σθ ^ 2).toNNReal ≠ 0 := by
  have := hM.σθ_pos; exact (Real.toNNReal_pos.2 (by positivity)).ne'

lemma s2_ne : (M.σε ^ 2).toNNReal ≠ 0 := by
  have := hM.σε_pos; exact (Real.toNNReal_pos.2 (by positivity)).ne'

lemma sT_ne : (M.σ ^ 2).toNNReal ≠ 0 := by
  have := sigma_pos M hM; exact (Real.toNNReal_pos.2 (by positivity)).ne'

lemma sv_ne : M.σv2.toNNReal ≠ 0 := by
  have := hM.σε_pos; have := hM.σθ_pos
  refine (Real.toNNReal_pos.2 ?_).ne'
  unfold Model.σv2; positivity

omit hM in
lemma integrable_bdd {μ : Measure ℝ} [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ v, |f v| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs]; exact hC v))

lemma postMean_mono : Monotone M.postMean := by
  intro x y hxy
  unfold Model.postMean
  have : 0 ≤ M.tau := by unfold Model.tau; positivity
  nlinarith

lemma condReward_shift (rhat : ℝ → ℝ) (hmeas : Measurable rhat) (x : ℝ) :
    M.condReward rhat x = ∫ w, rhat (w + M.postMean x) ∂(gaussianReal 0 M.σv2.toNNReal) := by
  unfold Model.condReward Model.posterior
  have hmap : gaussianReal (M.postMean x) M.σv2.toNNReal =
      (gaussianReal 0 M.σv2.toNNReal).map (· + M.postMean x) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [hmap, integral_map (by fun_prop) hmeas.aestronglyMeasurable]

theorem lemma_5' (p : ℝ) (rhat : ℝ → ℝ) (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) :
    (Monotone rhat → (∃ a b, rhat a ≠ rhat b) → StrictMono (M.condReward rhat)) ∧
      (Antitone rhat → Antitone (M.condReward rhat)) := by
  have hb : ∀ m : ℝ, ∀ w, |rhat (w + m)| ≤ p := fun m w => by
    rw [abs_of_nonneg (hbound _).1]; exact (hbound _).2
  have hsv := sv_ne M hM
  constructor
  · intro hmono ⟨a0, b0, hab0⟩
    have hmeas : Measurable rhat := hmono.measurable
    -- an increasing pair
    obtain ⟨a, b, hab, hlt⟩ : ∃ a b, a < b ∧ rhat a < rhat b := by
      rcases lt_trichotomy a0 b0 with h | h | h
      · exact ⟨a0, b0, h, lt_of_le_of_ne (hmono h.le) hab0⟩
      · exact absurd (congrArg rhat h) hab0
      · exact ⟨b0, a0, h, lt_of_le_of_ne (hmono h.le) (Ne.symm hab0)⟩
    intro x y hxy
    have htau : 0 < M.tau := by
      have := hM.σθ_pos; have := hM.σε_pos; unfold Model.tau; positivity
    set δ := M.postMean y - M.postMean x with hδ
    have hδpos : 0 < δ := by
      rw [hδ]; unfold Model.postMean; nlinarith
    -- the set where the shift by δ strictly increases `rhat`
    set S : Set ℝ := {t | rhat t < rhat (t + δ)} with hS
    have hSpos : volume S ≠ 0 := by
      intro hS0
      obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / δ + 1)
      have hcover : Set.Icc (a - δ) a ⊆ ⋃ k ∈ Finset.range n, (· + (k : ℝ) * δ) ⁻¹' S := by
        intro u hu
        by_contra hnot
        simp only [Set.mem_iUnion, Set.mem_preimage, Finset.mem_range, not_exists,
          not_and, hS, Set.mem_setOf_eq, not_lt] at hnot
        have hchain : ∀ k : ℕ, k ≤ n → rhat (u + (k : ℝ) * δ) ≤ rhat u := by
          intro k
          induction k with
          | zero => intro _; simp
          | succ k ih =>
            intro hk
            have h1 := hnot k (by omega)
            have h2 := ih (by omega)
            have : u + ((k + 1 : ℕ) : ℝ) * δ = u + (k : ℝ) * δ + δ := by push_cast; ring
            rw [this]; linarith
        have hfin := hchain n le_rfl
        have hub : b ≤ u + (n : ℝ) * δ := by
          have h1 : (b - a) / δ * δ = b - a := div_mul_cancel₀ _ hδpos.ne'
          have h2 : ((b - a) / δ + 1) * δ ≤ (n : ℝ) * δ :=
            mul_le_mul_of_nonneg_right hn hδpos.le
          nlinarith [hu.1]
        have := hmono hub
        have := hmono hu.2
        linarith
      have hnull : volume (⋃ k ∈ Finset.range n, (· + (k : ℝ) * δ) ⁻¹' S) = 0 := by
        refine (measure_biUnion_null_iff (Finset.range n).countable_toSet).2 (fun k _ => ?_)
        rw [measure_preimage_add_right]; exact hS0
      have := measure_mono_null hcover hnull
      rw [Real.volume_Icc] at this
      simp at this
      linarith
    -- positivity of the integral of the increment
    have hint : ∀ m : ℝ, Integrable (fun w => rhat (w + m)) (gaussianReal 0 M.σv2.toNNReal) :=
      fun m => integrable_bdd _ (hmeas.comp (by fun_prop)) p (hb m)
    rw [condReward_shift M hM rhat hmeas, condReward_shift M hM rhat hmeas, ← sub_pos,
      ← integral_sub (hint _) (hint _)]
    have hnn : 0 ≤ fun w => rhat (w + M.postMean y) - rhat (w + M.postMean x) := by
      intro w
      simp only [Pi.zero_apply, sub_nonneg]
      exact hmono (by linarith [postMean_mono M hM hxy.le])
    rw [integral_pos_iff_support_of_nonneg hnn ((hint _).sub (hint _))]
    have hsub : (· + M.postMean x) ⁻¹' S ⊆
        Function.support (fun w => rhat (w + M.postMean y) - rhat (w + M.postMean x)) := by
      intro w hw
      simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hw
      simp only [Function.mem_support]
      have : w + M.postMean x + δ = w + M.postMean y := by rw [hδ]; ring
      rw [this] at hw
      linarith
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    refine pos_iff_ne_zero.2 (fun h0 => hSpos ?_)
    have := gaussianReal_absolutelyContinuous' 0 hsv h0
    rwa [measure_preimage_add_right] at this
  · intro hanti
    have hmeas : Measurable rhat := hanti.measurable
    intro x y hxy
    rw [condReward_shift M hM rhat hmeas, condReward_shift M hM rhat hmeas]
    refine integral_mono (integrable_bdd _ (hmeas.comp (by fun_prop)) p (hb _))
      (integrable_bdd _ (hmeas.comp (by fun_prop)) p (hb _)) (fun w => ?_)
    exact hanti (add_le_add_right (postMean_mono M hM hxy) w)


end SRAux

open SRAux

open SalesRebate.NoIncreasing in
theorem solution (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hbound : ∀ v, rhat v ∈ Set.Icc 0 p) :
    (Monotone rhat → (∃ a b, rhat a ≠ rhat b) → StrictMono (M.condReward rhat)) ∧
      (Antitone rhat → Antitone (M.condReward rhat)) :=
  lemma_5' M hM p rhat hbound
