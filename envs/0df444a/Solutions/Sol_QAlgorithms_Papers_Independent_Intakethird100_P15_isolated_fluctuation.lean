-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P15.isolated_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-15T02:07:07.096409+00:00
-- url     : https://prove2.me/submissions/ca06980f-4b9c-4a47-bfe0-2f044e55a43d

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_wholeCycle_timeReversal
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_jarzynski_identity

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Intakethird100.P15
open QAlgorithms.Papers.Independent.Information100.P37 (transition)
open QAlgorithms.Papers.Independent.Support21.P03 (reflectedLaw)
open scoped ENNReal Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

private theorem transition_symmetric [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b) (a g : ι) :
    transition (fun j i => inner ℂ (b j) (d.evolution (b i))) g a =
      transition (fun j i => inner ℂ (b j) (d.evolution (b i))) a g := by
  let U := d.evolution
  have h := (wholeCycle_timeReversal b d).2 a g
  change inner ℂ (b a) (U.symm (b g)) = star (inner ℂ (b a) (U (b g))) at h
  rw [← U.inner_map_map (b a) (U.symm (b g)), U.apply_symm_apply] at h
  have hconj : star (inner ℂ (U (b a)) (b g)) = inner ℂ (b g) (U (b a)) :=
    inner_conj_symm (𝕜 := ℂ) (b g) (U (b a))
  rw [h, star_star] at hconj
  exact congrArg Complex.normSq hconj.symm

private theorem gibbs_tilt (energy : ι → ℝ) (beta : ℝ) (a g : ι) :
    spectralGibbsWeight energy beta a * Real.exp (-beta * (energy g - energy a)) =
      spectralGibbsWeight energy beta g := by
  unfold spectralGibbsWeight
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

theorem solution [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    let P := workLaw b d.evolution energy beta
    IsProbabilityMeasure P ∧
    reflectedLaw P = P.withDensity (fun e => ENNReal.ofReal (Real.exp (-beta * e))) ∧
    (P ≪ reflectedLaw P) ∧ (reflectedLaw P ≪ P) ∧
    (∀ e : ℝ, (P {e}).toReal = Real.exp (beta * e) * (P {-e}).toReal) := by
  let P := workLaw b d.evolution energy beta
  let density (e : ℝ) := ENNReal.ofReal (Real.exp (-beta * e))
  let weight := spectralGibbsWeight energy beta
  let born : ι → ι → ℝ := transition (fun g a => inner ℂ (b g) (d.evolution (b a)))
  let gap (p : ι × ι) : ℝ := energy p.2 - energy p.1
  let mass (p : ι × ι) : ℝ≥0∞ := ENNReal.ofReal (weight p.1 * born p.2 p.1)
  have hneg : Measurable (fun x : ℝ => -x) := by fun_prop
  have hd : Measurable density := by dsimp [density]; fun_prop
  have hm_nonneg (p : ι × ι) : 0 ≤ weight p.1 * born p.2 p.1 := by
    refine mul_nonneg ?_ (Complex.normSq_nonneg _)
    exact div_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  have hmass (p : ι × ι) : mass p * density (gap p) = mass p.swap := by
    dsimp [mass, density, gap]
    rw [← ENNReal.ofReal_mul (hm_nonneg p)]
    congr 1
    calc
      _ = (weight p.1 * Real.exp (-beta * (energy p.2 - energy p.1))) * born p.2 p.1 := by ring
      _ = _ := by
        rw [gibbs_tilt energy beta p.1 p.2]
        exact congrArg (weight p.2 * ·) (transition_symmetric b d p.1 p.2)
  have hreflect : reflectedLaw P = P.withDensity density := by
    change (Measure.sum (fun p => mass p • Measure.dirac (gap p))).map (fun x : ℝ => -x) =
      (Measure.sum (fun p => mass p • Measure.dirac (gap p))).withDensity density
    rw [Measure.map_sum hneg.aemeasurable, withDensity_sum]
    simp_rw [Measure.map_smul, Measure.map_dirac' hneg, withDensity_smul_measure,
      dirac_withDensity, smul_smul, hmass]
    let reflectedAtom (p : ι × ι) := mass p • Measure.dirac (-gap p)
    change Measure.sum reflectedAtom =
      Measure.sum (fun p : ι × ι => mass p.swap • Measure.dirac (gap p))
    rw [← Measure.sum_comp_equiv (Equiv.prodComm ι ι) reflectedAtom]
    congr 1
    funext p
    have hgap : -gap p.swap = gap p := by dsimp [gap]; ring
    simp only [Function.comp_apply, Equiv.prodComm_apply, reflectedAtom, hgap]
  have hreflection_apply (e : ℝ) : reflectedLaw P {e} = P {-e} := by
    unfold reflectedLaw
    rw [Measure.map_apply hneg (measurableSet_singleton e)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact neg_eq_iff_eq_neg
  have hprob : IsProbabilityMeasure P := by
    have hj := (jarzynski_identity b d energy beta hbeta henergy hheat).2.2
    refine ⟨?_⟩
    calc
      P Set.univ = reflectedLaw P Set.univ := by
        simp [reflectedLaw, Measure.map_apply hneg MeasurableSet.univ]
      _ = _ := by
        rw [hreflect, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        exact hj
  refine ⟨hprob, hreflect, ?_, ?_, ?_⟩
  · rw [hreflect]
    exact withDensity_absolutelyContinuous' hd.aemeasurable
      (Eventually.of_forall fun e => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  · rw [hreflect]
    exact withDensity_absolutelyContinuous P density
  · intro e
    have hpoint : P {-e} = density e * P {e} := by
      rw [← hreflection_apply, hreflect, withDensity_apply _ (measurableSet_singleton e),
        lintegral_singleton]
    rw [hpoint, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have hexp : Real.exp (beta * e) * Real.exp (-beta * e) = 1 := by
      rw [← Real.exp_add, show beta * e + -beta * e = 0 by ring, Real.exp_zero]
    rw [← mul_assoc, hexp, one_mul]
