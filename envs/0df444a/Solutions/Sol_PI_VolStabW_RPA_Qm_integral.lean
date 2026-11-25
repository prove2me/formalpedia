-- Prove2me | solution 1 for PI.VolStabW.RPA.Qm_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:01.88083+00:00
-- url     : https://prove2.me/submissions/3dba4584-8b51-40e7-a880-f2de09fb11e1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_KapIntegral
import Theorems.Thm_PI_VolStabW_RPA_tl_split
import Theorems.Thm_PI_VolStabW_RPA_tl_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]
namespace PI.VolStabW.RPA
theorem _root_.solution [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  unfold Qm
  split_ifs with hh
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (hh i.1 i.2)
    have hP : ∀ j : {i // i ∉ S}, Integrable (g j.1) (Pn m L j.1) := fun j =>
      ((hg j.1).restrict).smul_measure (ENNReal.inv_ne_top.2 (hh j.1 j.2).1)
    let F : (∀ j : T', W j.1.1) → ℂ := fun y => ∏ j : T', g j.1.1 (y j)
    have hpi : Integrable F (Measure.pi (fun j : T' => Pn m L j.1.1)) :=
      Integrable.fintype_prod_dep (fun j => hP j.1)
    have hre : (fun z : (∀ j : {i // i ∉ S}, W j.1) => ∏ j ∈ T', g j.1 (z j)) =
        fun z => F (T'.restrict z) := by
      funext z
      exact (Finset.prod_coe_sort T' (fun j => g j.1 (z j))).symm
    have hmap := Measure.infinitePi_map_restrict (μ := fun j : {i // i ∉ S} => Pn m L j.1) (I := T')
    have hpi' : Integrable F ((Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1).map
        T'.restrict) := by rw [hmap]; exact hpi
    have hint : Integrable (fun z => F (T'.restrict z))
        (Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1) :=
      (integrable_map_measure hpi'.aestronglyMeasurable
        (Finset.measurable_restrict _).aemeasurable).1 hpi'
    rw [hre]
    refine ⟨hint.smul_measure_nnreal, ?_⟩
    rw [integral_smul_nnreal_measure,
      integral_restrict_infinitePi (fun j : {i // i ∉ S} => Pn m L j.1) hpi.aestronglyMeasurable]
    simp only [F]
    rw [integral_fintype_prod_eq_prod]
    simp only [Pn, integral_smul_measure]
    rw [Finset.prod_coe_sort T' (fun j => ((m j.1 (L j.1))⁻¹.toReal • ∫ w, g j.1 w ∂(m j.1).restrict (L j.1))),
      hT', Finset.prod_subtype_eq_prod_filter (f := fun i => ((m i (L i))⁻¹.toReal • ∫ w, g i w ∂(m i).restrict (L i))),
      ← Finset.sdiff_eq_filter, tl_split hT hST]
    have hmu : ∀ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i) = ∫ w, g i w ∂(m i).restrict (L i) := by
      intro i hi
      rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [Finset.prod_congr rfl hmu]
    have hone : (∏ i ∈ T \ S, ((am m L i : ℝ) : ℂ)) * (∏ i ∈ T \ S, (((m i (L i))⁻¹.toReal : ℝ) : ℂ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one (fun i hi => ?_)
      have h1 := hh i (Finset.mem_sdiff.1 hi).2
      rw [← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_inv,
        mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h1.1, h1.2⟩), Complex.ofReal_one]
    simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod,
      Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
    linear_combination (((tl m L T : ℝ) : ℂ) * ∏ i ∈ T \ S, ∫ w, g i w ∂(m i).restrict (L i)) * hone
  · push_neg at hh
    obtain ⟨i, hiS, hi⟩ := hh
    have h0 : m i (L i) = 0 := by
      by_contra h; exact hfin i (hi h)
    refine ⟨integrable_zero_measure, ?_⟩
    rw [integral_zero_measure]
    by_cases hiT : i ∈ T
    · rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hiT, hiS⟩), zero_mul]
      rw [mu, if_neg hiS, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    · rw [tl_zero hT hiT (by simp [am, h0])]
      simp
end PI.VolStabW.RPA
