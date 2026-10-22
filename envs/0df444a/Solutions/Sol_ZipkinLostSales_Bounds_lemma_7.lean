-- Prove2me | solution 1 for ZipkinLostSales.Bounds.lemma_7
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:32:46.026987+00:00
-- url     : https://prove2.me/submissions/a02f830c-b5b8-49bf-80dd-9b4b5ea00dec

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model



namespace ZipkinLostSales.Bounds

namespace L7Cex

open MeasureTheory
open scoped ENNReal

/-- Demand law: `0` or `1` with probability `1/2` each. -/
noncomputable def μ0 : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

/-- The product law of two demands. -/
noncomputable def ν0 : Measure (Fin 2 → ℝ) :=
  (2⁻¹ * 2⁻¹ : ℝ≥0∞) • (Measure.dirac ![0, 0] + Measure.dirac ![0, 1] + Measure.dirac ![1, 0] +
    Measure.dirac ![1, 1])

lemma integral_μ0 (F : ℝ → ℝ) : ∫ x, F x ∂μ0 = 2⁻¹ * (F 0 + F 1) := by
  unfold μ0
  rw [integral_smul_measure, integral_add_measure (integrable_dirac enorm_lt_top)
    (integrable_dirac enorm_lt_top), integral_dirac, integral_dirac]
  simp

lemma integral_ν0 (G : (Fin 2 → ℝ) → ℝ) :
    ∫ x, G x ∂ν0 = 2⁻¹ * 2⁻¹ * (G ![0, 0] + G ![0, 1] + G ![1, 0] + G ![1, 1]) := by
  unfold ν0
  rw [integral_smul_measure]
  have hd : ∀ a : Fin 2 → ℝ, Integrable G (Measure.dirac a) := fun a =>
    integrable_dirac enorm_lt_top
  rw [integral_add_measure (((hd _).add_measure (hd _)).add_measure (hd _)) (hd _),
    integral_add_measure ((hd _).add_measure (hd _)) (hd _), integral_add_measure (hd _) (hd _)]
  rw [integral_dirac, integral_dirac, integral_dirac, integral_dirac]
  simp

instance : IsProbabilityMeasure μ0 := by
  constructor
  simp only [μ0, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul, mul_add,
    mul_one]
  exact ENNReal.inv_two_add_inv_two

lemma pi_μ0 : Measure.pi (fun _ : Fin 2 => μ0) = ν0 := by
  refine Measure.pi_eq ?_
  intro s hs
  have hps : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  simp only [ν0, μ0, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hps,
    Measure.dirac_apply' _ (hs _), Fin.prod_univ_two, smul_eq_mul]
  simp only [Set.indicator, Set.mem_univ_pi, Fin.forall_fin_two, Pi.one_apply]
  split_ifs <;> simp_all <;> ring

noncomputable def M0 : Data := ⟨μ0, 0, 1, 6, 1⟩

lemma hM0 : Assumptions 2 M0 where
  hL := by norm_num
  prob := by show IsProbabilityMeasure μ0; infer_instance
  demand_nonneg := by
    show μ0 (Set.Iio 0) = 0
    simp [μ0, Measure.dirac_apply' _ measurableSet_Iio]
  integrable := by
    show Integrable id μ0
    exact (integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top) |>.smul_measure
      (by simp)
  hc := by simp [M0]
  hhh := by simp [M0]
  hp := by norm_num [M0]
  hγ0 := by norm_num [M0]
  hγ1 := by norm_num [M0]
  hch := by norm_num [M0, Data.h]
  hph := by norm_num [M0, Data.h]

lemma q0_M0 (y : ℝ) : q0 M0 y =
    2⁻¹ * (max y 0 + max (y - 1) 0) + 6 * (2⁻¹ * (max (-y) 0 + max (1 - y) 0)) := by
  simp only [q0, M0, Data.h]
  rw [integral_μ0, integral_μ0]
  ring_nf

lemma q_M0 (v : Fin 2 → ℝ) (z : ℝ) : q M0 v z = 2⁻¹ * 2⁻¹ *
    (q0 M0 (yPlusL v z ![0, 0]) + q0 M0 (yPlusL v z ![0, 1]) + q0 M0 (yPlusL v z ![1, 0]) +
      q0 M0 (yPlusL v z ![1, 1])) := by
  simp only [q]
  have : M0.μ = μ0 := rfl
  rw [this, pi_μ0, integral_ν0]
  simp [M0]

lemma yPlusL_eq (v : Fin 2 → ℝ) (z : ℝ) (D : Fin 2 → ℝ) :
    yPlusL v z D = max (max (v 0 - v 1 - D 0) 0 + v 1 - D 1) 0 + z := by
  simp [yPlusL, onHand, arrival, xext, ZipkinLostSales.LNatural.vext]

lemma fB1 (v : Fin 2 → ℝ) : fB M0 1 v = ⨅ z : Set.Ici (0:ℝ), q M0 v z := by
  simp [fB, gstep]

lemma qA (z : ℝ) (hz : 0 ≤ z) : 11 / 8 ≤ q M0 ![2, 1] z := by
  rw [q_M0]
  simp only [yPlusL_eq, q0_M0]
  norm_num
  have := le_max_left (1 + z) 0
  have := le_max_left (2 + z) 0
  have := le_max_left (2 + z - 1) 0
  have := le_max_right (2 + z - 1) 0
  have := le_max_right (-z + -2) 0
  have := le_max_right (-z + -1) 0
  have := le_max_right (1 - (2 + z)) 0
  have := le_max_left z 0
  have := le_max_left (z - 1) 0
  have := le_max_right (z - 1) 0
  have := le_max_left (1 - z) 0
  have := le_max_right (1 - z) 0
  have := le_max_right (-z) 0
  rcases le_total z 1 with h | h <;> linarith

lemma qB0 : q M0 ![2, 2] 0 = 1 := by
  rw [q_M0]
  simp only [yPlusL_eq, q0_M0]
  norm_num

lemma q0_nonneg (y : ℝ) : 0 ≤ q0 M0 y := by
  rw [q0_M0]
  have := le_max_right y 0
  have := le_max_right (y - 1) 0
  have := le_max_right (-y) 0
  have := le_max_right (1 - y) 0
  linarith

lemma q_nonneg (v : Fin 2 → ℝ) (z : ℝ) : 0 ≤ q M0 v z := by
  rw [q_M0]
  have := q0_nonneg (yPlusL v z ![0, 0])
  have := q0_nonneg (yPlusL v z ![0, 1])
  have := q0_nonneg (yPlusL v z ![1, 0])
  have := q0_nonneg (yPlusL v z ![1, 1])
  positivity

lemma vA_mem : (![2, 1] : Fin 2 → ℝ) ∈ ZipkinLostSales.LNatural.V 2 := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro l; fin_cases l <;> norm_num

lemma vB_mem : (![2, 2] : Fin 2 → ℝ) ∈ ZipkinLostSales.LNatural.V 2 := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro l; fin_cases l <;> norm_num

lemma vAB_le : (![2, 1] : Fin 2 → ℝ) ≤ ![2, 2] := by
  intro l; fin_cases l <;> norm_num

lemma not_mono : ¬ MonotoneOn (fB M0 1) (ZipkinLostSales.LNatural.V 2) := by
  intro h
  have h1 := h vA_mem vB_mem vAB_le
  rw [fB1, fB1] at h1
  have hlow : (11 / 8 : ℝ) ≤ ⨅ z : Set.Ici (0:ℝ), q M0 ![2, 1] z := by
    have : Nonempty (Set.Ici (0:ℝ)) := ⟨⟨0, Set.mem_Ici.2 le_rfl⟩⟩
    exact le_ciInf fun z => qA z z.2
  have hup : (⨅ z : Set.Ici (0:ℝ), q M0 ![2, 2] z) ≤ 1 := by
    have hb : BddBelow (Set.range fun z : Set.Ici (0:ℝ) => q M0 ![2, 2] z) :=
      ⟨0, by rintro _ ⟨z, rfl⟩; exact q_nonneg _ _⟩
    have := ciInf_le hb ⟨0, Set.mem_Ici.2 le_rfl⟩
    rw [qB0] at this
    exact this
  linarith

end L7Cex

theorem lemma_7_false : ¬ (∀ {L : ℕ} (M : Data) (hM : Assumptions L M),
    MonotoneOn (fB M 1) (ZipkinLostSales.LNatural.V L)) := by
  intro h
  exact L7Cex.not_mono (h L7Cex.M0 L7Cex.hM0)

theorem theorem_8_false : ¬ (∀ {L : ℕ} (M : Data) (hM : Assumptions L M) (k : ℕ),
    MonotoneOn (fB M (k + 1)) (ZipkinLostSales.LNatural.V L) ∧
      ∀ v ∈ ZipkinLostSales.LNatural.V L,
        ∃ z z' : ℝ, IsOptOrder M k v z ∧ IsOptOrder M 0 v z' ∧ z ≤ z') := by
  intro h
  exact L7Cex.not_mono (h L7Cex.M0 L7Cex.hM0 0).1

end ZipkinLostSales.Bounds

open ZipkinLostSales.Bounds


theorem solution : ¬ (∀ {L : ℕ} (M : Data) (hM : Assumptions L M),
    MonotoneOn (fB M 1) (ZipkinLostSales.LNatural.V L)) := by
  exact lemma_7_false
