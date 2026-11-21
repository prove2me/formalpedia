-- Prove2me | solution 1 for RelaxRoundPoA.relaxed_payment_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:29:46.038171+00:00
-- url     : https://prove2.me/submissions/fe6fe275-302e-490d-a339-7d62afbd9487

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded

open MeasureTheory ProbabilityTheory NNReal ENNReal

open RelaxRoundPoA in
theorem solution {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω')
    (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M) (hfin' : ExpFinite Val M')
    (hfin : ExpFinite Val M) (hround : IsObliviousRounding Val Ω α R) (hrel : IsRounded Val M' R M)
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) :
    M'.expPay b i ≤ α * M.expPay b i := by
  obtain ⟨hα, _, _, hguar⟩ := hround
  have hν : M.outcome b = (M'.outcome b).bind R := hrel b hb
  have I' : Integrable (fun x => ((b i x : ℝ≥0) : ℝ)) (M'.outcome b) := hfin' b hb i (b i) (hb i)
  have I : Integrable (fun x => ((b i x : ℝ≥0) : ℝ)) (M.outcome b) := hfin b hb i (b i) (hb i)
  rw [hpay' b hb i, hpay b hb i]
  have hα0 : 0 ≤ α := by linarith
  have hnn : 0 ≤ ∫ x, ((b i x : ℝ≥0) : ℝ) ∂(M.outcome b) :=
    integral_nonneg (fun x => NNReal.coe_nonneg _)
  have hf : AEMeasurable (fun x => ((b i x : ℝ≥0) : ℝ≥0∞)) (M.outcome b) := by
    have h := I.aemeasurable.ennreal_ofReal
    simpa only [ENNReal.ofReal_coe_nnreal] using h
  rw [hν] at hf
  have key : ENNReal.ofReal (∫ x, ((b i x : ℝ≥0) : ℝ) ∂(M'.outcome b))
      ≤ ENNReal.ofReal (α * ∫ x, ((b i x : ℝ≥0) : ℝ) ∂(M.outcome b)) := by
    rw [← lintegral_coe_eq_integral (b i) I', ENNReal.ofReal_mul hα0,
      ← lintegral_coe_eq_integral (b i) I, hν,
      Measure.lintegral_bind R.measurable.aemeasurable hf,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono (fun x' => hguar x' i (b i) (hb i))
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα0 hnn)).mp key
