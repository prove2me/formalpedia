-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.lemma_5_1_uniqueness_of_svm_solutions
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:14:58.502003+00:00
-- url     : https://prove2.me/submissions/4c49a646-2ff7-4d0b-bfa5-ea13f4fbf028

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- A two-point type, to be equipped with the trivial σ-algebra. -/
def aux_u51_X : Type := Bool

/-- The trivial σ-algebra `{∅, univ}` on the two-point type. -/
instance aux_u51_ms : MeasurableSpace aux_u51_X := ⊥

/-- The two "targets" `±1`. -/
noncomputable def aux_u51_s (x : Bool) : ℝ := if x then 1 else -1

/-- The squared loss towards the target `s x` (independent of the label). -/
noncomputable def aux_u51_L : Loss aux_u51_X := fun x _ t => (t - aux_u51_s x) ^ 2

/-- `ℝ` realized as the constant functions on the two-point type. -/
def aux_u51_toFun : ℝ →ₗ[ℝ] (aux_u51_X → ℝ) := LinearMap.pi (fun _ => LinearMap.id)

lemma aux_u51_sq (x : Bool) : aux_u51_s x ^ 2 = 1 := by
  unfold aux_u51_s; split_ifs <;> norm_num

lemma aux_u51_hL : ∀ x y, ConvexOn ℝ Set.univ (aux_u51_L x y) := by
  intro x y
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ μ ν hμ hν hμν
  simp only [aux_u51_L, smul_eq_mul]
  obtain rfl : ν = 1 - μ := by linarith
  nlinarith [mul_nonneg (mul_nonneg hμ hν) (sq_nonneg (a - b))]

lemma aux_u51_hLnn : ∀ x y t, 0 ≤ aux_u51_L x y t := by
  intro x y t
  exact sq_nonneg _

lemma aux_u51_rkhs : IsRKHSOfKernel ℝ aux_u51_toFun (fun _ _ => 1) := by
  refine ⟨?_, fun _ => 1, fun _ _ => rfl, ?_⟩
  · intro a b hab
    have := congr_fun hab (true : Bool)
    exact this
  · intro f x
    show f = inner (𝕜 := ℝ) f 1
    simp

/-- Measurable functions on `aux_u51_X × ℝ` do not depend on the first coordinate. -/
lemma aux_u51_fact (g : aux_u51_X × ℝ → ENNReal) (hg : Measurable g) (x x' : aux_u51_X)
    (y : ℝ) : g (x, y) = g (x', y) := by
  have hle : (Prod.instMeasurableSpace : MeasurableSpace (aux_u51_X × ℝ)) ≤
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace ℝ) := by
    show MeasurableSpace.comap Prod.fst aux_u51_ms ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace ℝ) ≤ _
    refine sup_le ?_ le_rfl
    rw [show aux_u51_ms = ⊥ from rfl, MeasurableSpace.comap_bot]
    exact bot_le
  have hS : MeasurableSet (g ⁻¹' {g (x, y)}) := hg (measurableSet_singleton _)
  obtain ⟨B, _, hB⟩ := hle _ hS
  have h1 : (x, y) ∈ g ⁻¹' {g (x, y)} := rfl
  rw [← hB] at h1
  have h2 : (x', y) ∈ g ⁻¹' {g (x, y)} := by rw [← hB]; exact h1
  exact (h2 : g (x', y) = g (x, y)).symm

lemma aux_u51_R_eq (P : Measure (aux_u51_X × ℝ)) (r : ℝ) :
    populationRisk aux_u51_L P (aux_u51_toFun r) =
      ∫⁻ p, ENNReal.ofReal ((r - aux_u51_s p.1) ^ 2) ∂P := rfl

/-- Upper bound: the (lower) integral only sees the best point. -/
lemma aux_u51_upper (P : Measure (aux_u51_X × ℝ)) [IsProbabilityMeasure P] (r : ℝ)
    (x0 : aux_u51_X) :
    populationRisk aux_u51_L P (aux_u51_toFun r) ≤ ENNReal.ofReal ((r - aux_u51_s x0) ^ 2) := by
  rw [aux_u51_R_eq]
  obtain ⟨g, hgm, hgle, heq⟩ :=
    exists_measurable_le_lintegral_eq P (fun p => ENNReal.ofReal ((r - aux_u51_s p.1) ^ 2))
  rw [heq]
  calc ∫⁻ p, g p ∂P ≤ ∫⁻ _, ENNReal.ofReal ((r - aux_u51_s x0) ^ 2) ∂P := by
        apply lintegral_mono
        rintro ⟨a, b⟩
        rw [aux_u51_fact g hgm a x0 b]
        exact hgle (x0, b)
    _ = ENNReal.ofReal ((r - aux_u51_s x0) ^ 2) := by simp

/-- Lower bound via a constant minorant. -/
lemma aux_u51_lower (P : Measure (aux_u51_X × ℝ)) [IsProbabilityMeasure P] (r : ℝ) :
    ENNReal.ofReal (min ((r - 1) ^ 2) ((r + 1) ^ 2)) ≤
      populationRisk aux_u51_L P (aux_u51_toFun r) := by
  rw [aux_u51_R_eq]
  calc ENNReal.ofReal (min ((r - 1) ^ 2) ((r + 1) ^ 2))
        = ∫⁻ _, ENNReal.ofReal (min ((r - 1) ^ 2) ((r + 1) ^ 2)) ∂P := by simp
    _ ≤ ∫⁻ p, ENNReal.ofReal ((r - aux_u51_s p.1) ^ 2) ∂P := by
        apply lintegral_mono
        intro p
        apply ENNReal.ofReal_le_ofReal
        unfold aux_u51_s
        split_ifs
        · exact min_le_left _ _
        · have e : (r - -1) ^ 2 = (r + 1) ^ 2 := by ring
          rw [e]; exact min_le_right _ _

lemma aux_u51_opt (P : Measure (aux_u51_X × ℝ)) [IsProbabilityMeasure P] (x0 : aux_u51_X)
    (g : ℝ) :
    ENNReal.ofReal (1 * ‖aux_u51_s x0 / 2‖ ^ 2) +
        populationRisk aux_u51_L P (aux_u51_toFun (aux_u51_s x0 / 2)) ≤
      ENNReal.ofReal (1 * ‖g‖ ^ 2) + populationRisk aux_u51_L P (aux_u51_toFun g) := by
  have hc := aux_u51_sq x0
  have h1 : ‖aux_u51_s x0 / 2‖ ^ 2 = 1 / 4 := by
    rw [Real.norm_eq_abs, sq_abs]; linear_combination (1 / 4) * hc
  have h2 : populationRisk aux_u51_L P (aux_u51_toFun (aux_u51_s x0 / 2)) ≤
      ENNReal.ofReal (1 / 4) := by
    have := aux_u51_upper P (aux_u51_s x0 / 2) x0
    have e : (aux_u51_s x0 / 2 - aux_u51_s x0) ^ 2 = 1 / 4 := by
      linear_combination (1 / 4) * hc
    rw [e] at this; exact this
  have h3 := aux_u51_lower P g
  calc _ ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
          rw [one_mul, h1]; exact add_le_add le_rfl h2
    _ = ENNReal.ofReal (1 / 2) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ ≤ ENNReal.ofReal (g ^ 2 + min ((g - 1) ^ 2) ((g + 1) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rcases min_cases ((g - 1) ^ 2) ((g + 1) ^ 2) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
            nlinarith [sq_nonneg (g - 1 / 2), sq_nonneg (g + 1 / 2)]
    _ = ENNReal.ofReal (1 * ‖g‖ ^ 2) + ENNReal.ofReal (min ((g - 1) ^ 2) ((g + 1) ^ 2)) := by
          rw [ENNReal.ofReal_add (sq_nonneg _) (le_min (sq_nonneg _) (sq_nonneg _)), one_mul,
            Real.norm_eq_abs, sq_abs]
    _ ≤ _ := add_le_add le_rfl h3

end SupportVectorMachines.InfiniteSample

open SupportVectorMachines.InfiniteSample

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (hLnn : ∀ x y t, 0 ≤ L x y t)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hfin : ∃ f : H, populationRisk L P (toFun f) < ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f1 f2 : H)
    (hf1 : ∀ g : H, ENNReal.ofReal (lam * ‖f1‖ ^ 2) + populationRisk L P (toFun f1) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g))
    (hf2 : ∀ g : H, ENNReal.ofReal (lam * ‖f2‖ ^ 2) + populationRisk L P (toFun f2) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)),
    f1 = f2) := by
  intro h
  have key := @h aux_u51_X aux_u51_ms aux_u51_L aux_u51_hL aux_u51_hLnn ℝ _ _ _ aux_u51_toFun
    (fun _ _ => 1) aux_u51_rkhs (Measure.dirac ((true : Bool), (0 : ℝ))) _
    ⟨0, lt_of_le_of_lt (aux_u51_upper _ 0 (true : Bool)) ENNReal.ofReal_lt_top⟩
    1 one_pos (aux_u51_s (true : Bool) / 2) (aux_u51_s (false : Bool) / 2)
    (aux_u51_opt _ (true : Bool)) (aux_u51_opt _ (false : Bool))
  simp [aux_u51_s] at key
  norm_num at key
