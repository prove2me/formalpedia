-- Prove2me | solution 1 for RelaxRoundPoA.rounded_half_utility_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:43:28.400844+00:00
-- url     : https://prove2.me/submissions/9407465e-3474-4f4c-bc8c-6f6352571a43

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded

open MeasureTheory ProbabilityTheory NNReal

namespace Aux_RelaxRoundPoA_rounded_half_utility_ge

open RelaxRoundPoA


theorem profile_update {N : Type*} [DecidableEq N] {Ω' : Type*} (Val : N → Set (Ω' → ℝ≥0))
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) (w : Ω' → ℝ≥0) (hw : w ∈ Val i) :
    IsProfile Val (Function.update b i w) := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    exact hw
  · rw [Function.update_of_ne hj]
    exact hb j

theorem half_integral {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') (v : Ω' → ℝ≥0) :
    ∫ x, ((v x / 2 : ℝ≥0) : ℝ) ∂μ = (∫ x, (v x : ℝ) ∂μ) / 2 := by
  have hfun : (fun x => ((v x / 2 : ℝ≥0) : ℝ)) = fun x => (v x : ℝ) / 2 := by
    funext x
    rw [NNReal.coe_div]
    norm_num
  rw [hfun, integral_div]

theorem rounded_key {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0)) (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω')
    (hfin' : ExpFinite Val M') (hfin : ExpFinite Val M) (hround : IsObliviousRounding Val Ω α R)
    (hrel : IsRounded Val M' R M) (b' : N → Ω' → ℝ≥0) (hp' : IsProfile Val b') (i : N)
    (v : Ω' → ℝ≥0) (hv : v ∈ Val i) :
    ∫ x, (v x : ℝ) ∂(M'.outcome b') ≤ α * ∫ x, (v x : ℝ) ∂(M.outcome b') := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hround.1
  have hO : M.outcome b' = (M'.outcome b').bind R := hrel b' hp'
  have hI : Integrable (fun x => (v x : ℝ)) (M.outcome b') := hfin b' hp' i v hv
  have hI' : Integrable (fun x => (v x : ℝ)) (M'.outcome b') := hfin' b' hp' i v hv
  have hA : ∫ x, (v x : ℝ) ∂(M'.outcome b') =
      (∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(M'.outcome b')).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => NNReal.coe_nonneg (v x)))
      hI'.aestronglyMeasurable
  have hB : ∫ x, (v x : ℝ) ∂(M.outcome b') =
      (∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(M.outcome b')).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => NNReal.coe_nonneg (v x)))
      hI.aestronglyMeasurable
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (v x : ℝ)) ((M'.outcome b').bind R) := by
    rw [← hO]
    exact hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hBbind : ∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(M.outcome b') =
      ∫⁻ x', ∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(R x') ∂(M'.outcome b') := by
    rw [hO]
    exact Measure.lintegral_bind R.measurable.aemeasurable hmeas
  have hguar : ∀ x', ENNReal.ofReal (v x' : ℝ) ≤
      ENNReal.ofReal α * ∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(R x') := by
    intro x'
    have h := hround.2.2.2 x' i v hv
    simp only [ENNReal.ofReal_coe_nnreal]
    exact h
  have hA' : ∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(M'.outcome b') ≤
      ENNReal.ofReal α * ∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(M.outcome b') := by
    rw [hBbind, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hguar
  have hBfin : ∫⁻ x, ENNReal.ofReal (v x : ℝ) ∂(M.outcome b') ≠ ⊤ := hI.lintegral_lt_top.ne
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin) hA'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα0] at h1
  rw [hA, hB]
  exact h1

end Aux_RelaxRoundPoA_rounded_half_utility_ge

open RelaxRoundPoA Aux_RelaxRoundPoA_rounded_half_utility_ge in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω') (hhalf : HalfClosed Val)
    (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M) (hfin' : ExpFinite Val M')
    (hfin : ExpFinite Val M) (hround : IsObliviousRounding Val Ω α R) (hrel : IsRounded Val M' R M)
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) (v : Ω' → ℝ≥0) (hv : v ∈ Val i) :
    1 / (2 * α) * ∫ x, (v x : ℝ) ∂(M'.outcome (Function.update b i (fun y => v y / 2))) ≤
        utility M i (Function.update b i (fun y => v y / 2)) v ∧
      1 / (2 * α) * ∫ x, (v x : ℝ) ∂(M'.outcome (Function.update b i (fun y => v y / 2))) =
        1 / α * utility M' i (Function.update b i (fun y => v y / 2)) v := by
  obtain ⟨b', hb'⟩ : ∃ b', b' = Function.update b i (fun y => v y / 2) := ⟨_, rfl⟩
  rw [← hb']
  have hα1 : 1 ≤ α := hround.1
  have hαpos : 0 < α := by linarith
  have hvh : (fun y => v y / 2) ∈ Val i := hhalf i v hv
  have hp' : IsProfile Val b' := by
    rw [hb']
    exact profile_update Val b hb i _ hvh
  have hbi : b' i = fun y => v y / 2 := by rw [hb', Function.update_self]
  have hP := hpay b' hp' i
  have hP' := hpay' b' hp' i
  simp only [hbi] at hP hP'
  rw [half_integral] at hP hP'
  have hAB := rounded_key Val Ω α R M' M hfin' hfin hround hrel b' hp' i v hv
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ x, (v x : ℝ) ∂(M'.outcome b') := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∫ x, (v x : ℝ) ∂(M.outcome b') := ⟨_, rfl⟩
  rw [← hA, ← hB] at hAB
  rw [← hA] at hP'
  rw [← hB] at hP
  have hu : utility M i b' v = B - B / 2 := by
    show ∫ x, (v x : ℝ) ∂(M.outcome b') - M.expPay b' i = B - B / 2
    rw [hP, ← hB]
  have hu' : utility M' i b' v = A - A / 2 := by
    show ∫ x, (v x : ℝ) ∂(M'.outcome b') - M'.expPay b' i = A - A / 2
    rw [hP', ← hA]
  rw [hu, hu', ← hA]
  refine ⟨?_, ?_⟩
  · have h1 : 1 / (2 * α) * A ≤ 1 / (2 * α) * (α * B) :=
      mul_le_mul_of_nonneg_left hAB (div_nonneg zero_le_one (by linarith))
    have h2 : 1 / (2 * α) * (α * B) = B / 2 * (α / α) := by ring
    rw [h2, div_self hαpos.ne', mul_one] at h1
    linarith
  · ring

