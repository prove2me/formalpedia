-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P15.jarzynski_identity
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-07T02:13:06.582661+00:00
-- url     : https://prove2.me/submissions/d5ea1a31-999f-4073-8530-1b73056834a3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P15

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Intakethird100.P15
open QAlgorithms.Papers.Independent.Information100.P37 (transition)
open scoped ENNReal Topology

universe u v w

private theorem born_row_hasSum {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type v}
    (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E) (g : ι) :
    HasSum (fun a => transition (fun j i => inner ℂ (b j) (U (b i))) g a) 1 := by
  let v := U.symm (b g)
  have hterm (a : ι) :
      (inner ℂ v (b a) * inner ℂ (b a) v).re =
        transition (fun j i => inner ℂ (b j) (U (b i))) g a := by
    have hinner : inner ℂ (b g) (U (b a)) = inner ℂ v (b a) := by
      simpa only [v, U.apply_symm_apply] using U.inner_map_map v (b a)
    change (inner ℂ v (b a) * inner ℂ (b a) v).re =
      Complex.normSq (inner ℂ (b g) (U (b a)))
    rw [hinner, ← inner_conj_symm (𝕜 := ℂ) (b a) v,
      Complex.mul_conj, Complex.ofReal_re]
  have hnorm : ‖v‖ = 1 := by
    rw [show ‖v‖ = ‖b g‖ from U.symm.norm_map _, b.orthonormal.norm_eq_one g]
  have hre : (inner ℂ v v).re = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  simpa only [hterm, hre] using Complex.hasSum_re (b.hasSum_inner_mul_inner v v)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

theorem solution [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    let P := workLaw b d.evolution energy beta
    Integrable (fun e : ℝ => Real.exp (-beta * e)) P ∧
    (∫ e, Real.exp (-beta * e) ∂P) = 1 ∧
    (∫⁻ e, ENNReal.ofReal (Real.exp (-beta * e)) ∂P) = 1 := by
  classical
  let P := workLaw b d.evolution energy beta
  let weight := spectralGibbsWeight energy beta
  let born : ι → ι → ℝ := transition (fun g a => inner ℂ (b g) (d.evolution (b a)))
  have hsum := hheat beta hbeta
  have hZ : 0 < heatTrace energy beta := by
    let i : ι := Classical.choice ‹Nonempty ι›
    exact (Real.exp_pos _).trans_le (hsum.le_tsum i (fun j _ => (Real.exp_pos _).le))
  have hw (i : ι) : 0 ≤ weight i := div_nonneg (Real.exp_pos _).le hZ.le
  have hwsum : Summable weight := hsum.div_const _
  have hweight : (∑' i, weight i) = 1 := by
    change (∑' i, Real.exp (-beta * energy i) / heatTrace energy beta) = 1
    rw [tsum_div_const, ← heatTrace, div_self hZ.ne']
  have hborn (g a : ι) : 0 ≤ born g a := Complex.normSq_nonneg _
  have hrow (g : ι) : (∑' a, ENNReal.ofReal (born g a)) = 1 := by
    have hs : HasSum (born g) 1 := born_row_hasSum b d.evolution g
    rw [← ENNReal.ofReal_tsum_of_nonneg (hborn g) hs.summable, hs.tsum_eq, ENNReal.ofReal_one]
  have htilt (a g : ι) :
      weight a * born g a * Real.exp (-beta * (energy g - energy a)) =
        weight g * born g a := by
    have hexp : Real.exp (-beta * energy a) * Real.exp (-beta * (energy g - energy a)) =
        Real.exp (-beta * energy g) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change Real.exp (-beta * energy a) / heatTrace energy beta * born g a *
      Real.exp (-beta * (energy g - energy a)) =
      Real.exp (-beta * energy g) / heatTrace energy beta * born g a
    calc
      _ = (Real.exp (-beta * energy a) * Real.exp (-beta * (energy g - energy a))) /
          heatTrace energy beta * born g a := by ring
      _ = _ := by rw [hexp]
  have hlin : (∫⁻ e, ENNReal.ofReal (Real.exp (-beta * e)) ∂P) = 1 := by
    calc
      _ = ∑' p : ι × ι, ENNReal.ofReal
          (weight p.1 * born p.2 p.1 * Real.exp (-beta * (energy p.2 - energy p.1))) := by
        unfold P workLaw preparedWorkLaw
        rw [lintegral_sum_measure]
        refine tsum_congr fun p => ?_
        rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
          ← ENNReal.ofReal_mul (mul_nonneg (hw p.1) (hborn p.2 p.1))]
      _ = ∑' p : ι × ι, ENNReal.ofReal (weight p.2 * born p.2 p.1) := by
        exact tsum_congr fun p => congrArg ENNReal.ofReal (htilt p.1 p.2)
      _ = ∑' g : ι, ∑' a : ι, ENNReal.ofReal (weight g * born g a) := by
        rw [← ENNReal.tsum_prod]
        exact (Equiv.prodComm ι ι).tsum_eq
          (fun p => ENNReal.ofReal (weight p.1 * born p.1 p.2))
      _ = ∑' g : ι, ENNReal.ofReal (weight g) := by
        refine tsum_congr fun g => ?_
        simp_rw [ENNReal.ofReal_mul (hw g), ENNReal.tsum_mul_left, hrow g, mul_one]
      _ = 1 := by rw [← ENNReal.ofReal_tsum_of_nonneg hw hwsum, hweight, ENNReal.ofReal_one]
  have hmeas : AEStronglyMeasurable (fun e : ℝ => Real.exp (-beta * e)) P :=
    (show Continuous (fun e : ℝ => Real.exp (-beta * e)) by fun_prop).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[P] (fun e : ℝ => Real.exp (-beta * e)) :=
    Eventually.of_forall fun _ => (Real.exp_pos _).le
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp ?_, ?_, hlin⟩
  · rw [hlin]
    exact ENNReal.one_ne_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas, hlin, ENNReal.toReal_one]
