-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P15.bath_fluctuation
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-16T02:05:21.794326+00:00
-- url     : https://prove2.me/submissions/f8bd057d-9417-49ec-be71-57444fd785dc

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P15_wholeCycle_timeReversal

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


private theorem gibbs_nonneg {α : Type*} (energy : α → ℝ) (beta : ℝ) (a : α) :
    0 ≤ spectralGibbsWeight energy beta a :=
  div_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)

private theorem gibbs_sum {α : Type*} (energy : α → ℝ) (beta : ℝ)
    (hZ : 0 < heatTrace energy beta)
    (hsum : Summable (fun a => Real.exp (-beta * energy a))) :
    (∑' a, ENNReal.ofReal (spectralGibbsWeight energy beta a)) = 1 := by
  have hw : Summable (spectralGibbsWeight energy beta) := hsum.div_const _
  rw [← ENNReal.ofReal_tsum_of_nonneg (gibbs_nonneg energy beta) hw]
  unfold spectralGibbsWeight
  rw [tsum_div_const, ← heatTrace, div_self hZ.ne', ENNReal.ofReal_one]

theorem solution {B S : Type*} [Countable B] [Nonempty B]
    [Countable S] [Nonempty S]
    (b : HilbertBasis (B × S) ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (bathEnergy : B → ℝ) (systemO : S → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (hO_lower : ∃ L : ℝ, ∀ s, L ≤ systemO s)
    (hZbath : 0 < heatTrace bathEnergy beta)
    (hZsystem : 0 < heatTrace systemO beta)
    (hbath_beta : Summable (fun a => Real.exp (-beta * bathEnergy a)))
    (hsystem_beta : Summable (fun a => Real.exp (-beta * systemO a)))
    (hbath_strip : ∀ mu : ℝ, 0 < mu → mu < 1 →
      Summable (fun a => Real.exp (-(2 * beta * mu) * bathEnergy a)))
    (hpower : ∀ mu : ℝ, 0 < mu → mu < 1 →
      Summable (fun a => (spectralGibbsWeight systemO beta a) ^ (2 * mu))) :
    let P := preparedWorkLaw b d.evolution (bathObservedEnergy bathEnergy systemO)
      (bathPreparation bathEnergy systemO beta)
    IsProbabilityMeasure P ∧
    reflectedLaw P = P.withDensity (fun e => ENNReal.ofReal (Real.exp (-beta * e))) ∧
    (P ≪ reflectedLaw P) ∧ (reflectedLaw P ≪ P) ∧
    (∀ e : ℝ, (P {e}).toReal = Real.exp (beta * e) * (P {-e}).toReal) := by
  let energy := bathObservedEnergy bathEnergy systemO
  let P := preparedWorkLaw b d.evolution energy (bathPreparation bathEnergy systemO beta)
  let density (e : ℝ) := ENNReal.ofReal (Real.exp (-beta * e))
  let weight := bathPreparation bathEnergy systemO beta
  let born : (B × S) → (B × S) → ℝ := transition (fun g a => inner ℂ (b g) (d.evolution (b a)))
  let gap (p : (B × S) × (B × S)) : ℝ := energy p.2 - energy p.1
  let mass (p : (B × S) × (B × S)) : ℝ≥0∞ := ENNReal.ofReal (weight p.1 * born p.2 p.1)
  have hneg : Measurable (fun x : ℝ => -x) := by fun_prop
  have hd : Measurable density := by dsimp [density]; fun_prop
  have hw (a : B × S) : 0 ≤ weight a :=
    mul_nonneg (gibbs_nonneg bathEnergy beta a.1) (gibbs_nonneg systemO beta a.2)
  have hwtilt (a g : B × S) : weight a * Real.exp (-beta * (energy g - energy a)) =
      weight g := by
    have hsplit : -beta * (energy g - energy a) =
        -beta * (bathEnergy g.1 - bathEnergy a.1) +
          -beta * (systemO g.2 - systemO a.2) := by
      unfold energy bathObservedEnergy
      ring
    rw [hsplit, Real.exp_add]
    change (spectralGibbsWeight bathEnergy beta a.1 * spectralGibbsWeight systemO beta a.2) *
        (Real.exp (-beta * (bathEnergy g.1 - bathEnergy a.1)) *
          Real.exp (-beta * (systemO g.2 - systemO a.2))) =
        spectralGibbsWeight bathEnergy beta g.1 * spectralGibbsWeight systemO beta g.2
    rw [mul_mul_mul_comm, gibbs_tilt, gibbs_tilt]
  have hm_nonneg (p : (B × S) × (B × S)) : 0 ≤ weight p.1 * born p.2 p.1 :=
    mul_nonneg (hw p.1) (Complex.normSq_nonneg _)
  have hmass (p : (B × S) × (B × S)) : mass p * density (gap p) = mass p.swap := by
    dsimp [mass, density, gap]
    rw [← ENNReal.ofReal_mul (hm_nonneg p)]
    congr 1
    calc
      _ = (weight p.1 * Real.exp (-beta * (energy p.2 - energy p.1))) * born p.2 p.1 := by ring
      _ = _ := by
        rw [hwtilt p.1 p.2]
        exact congrArg (weight p.2 * ·) (transition_symmetric b d p.1 p.2)
  have hreflect : reflectedLaw P = P.withDensity density := by
    change (Measure.sum (fun p => mass p • Measure.dirac (gap p))).map (fun x : ℝ => -x) =
      (Measure.sum (fun p => mass p • Measure.dirac (gap p))).withDensity density
    rw [Measure.map_sum hneg.aemeasurable, withDensity_sum]
    simp_rw [Measure.map_smul, Measure.map_dirac' hneg, withDensity_smul_measure,
      dirac_withDensity, smul_smul, hmass]
    let reflectedAtom (p : (B × S) × (B × S)) := mass p • Measure.dirac (-gap p)
    change Measure.sum reflectedAtom =
      Measure.sum (fun p : (B × S) × (B × S) => mass p.swap • Measure.dirac (gap p))
    rw [← Measure.sum_comp_equiv (Equiv.prodComm (B × S) (B × S)) reflectedAtom]
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
  have hcol (a : B × S) : (∑' g, ENNReal.ofReal (born g a)) = 1 := by
    let v := d.evolution (b a)
    have hterm (g : B × S) : (inner ℂ v (b g) * inner ℂ (b g) v).re = born g a := by
      change (inner ℂ v (b g) * inner ℂ (b g) v).re = Complex.normSq (inner ℂ (b g) v)
      rw [mul_comm, ← inner_conj_symm (𝕜 := ℂ) v (b g), Complex.mul_conj, Complex.ofReal_re]
    have hnorm : ‖v‖ = 1 := by
      rw [show ‖v‖ = ‖b a‖ from d.evolution.norm_map _, b.orthonormal.norm_eq_one a]
    have hre : (inner ℂ v v).re = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      simp
    have hs : HasSum (fun g => born g a) 1 := by
      simpa only [hterm, hre] using Complex.hasSum_re (b.hasSum_inner_mul_inner v v)
    have hborn (g : B × S) : 0 ≤ born g a := Complex.normSq_nonneg _
    rw [← ENNReal.ofReal_tsum_of_nonneg hborn hs.summable,
      hs.tsum_eq, ENNReal.ofReal_one]
  have hweights : (∑' a, ENNReal.ofReal (weight a)) = 1 := by
    rw [ENNReal.tsum_prod']
    change (∑' j : B, ∑' k : S, ENNReal.ofReal
      (spectralGibbsWeight bathEnergy beta j * spectralGibbsWeight systemO beta k)) = 1
    simp_rw [ENNReal.ofReal_mul (gibbs_nonneg bathEnergy beta _), ENNReal.tsum_mul_left,
      gibbs_sum systemO beta hZsystem hsystem_beta, mul_one]
    exact gibbs_sum bathEnergy beta hZbath hbath_beta
  have hprob : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    calc
      P Set.univ = ∑' p : (B × S) × (B × S), mass p := by
        change Measure.sum (fun p => mass p • Measure.dirac (gap p)) Set.univ = _
        rw [Measure.sum_apply _ MeasurableSet.univ]
        simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _),
          mul_one]
      _ = ∑' a : B × S, ENNReal.ofReal (weight a) := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun a => ?_
        simp_rw [mass, ENNReal.ofReal_mul (hw a), ENNReal.tsum_mul_left, hcol a, mul_one]
      _ = 1 := hweights
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
