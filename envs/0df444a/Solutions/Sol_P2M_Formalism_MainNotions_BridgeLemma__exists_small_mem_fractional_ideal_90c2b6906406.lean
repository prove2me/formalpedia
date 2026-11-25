-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__exists_small_mem_fractional_ideal_90c2b6906406
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:45:11.673842+00:00
-- url     : https://prove2.me/submissions/dbac1e9a-28c8-43d9-8d1b-34bc175c3415

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rootDiscr_pow_eq_sqrt_discr_9399e9c24fe2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
open scoped Classical
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, (w a) ^ 2 ≤ rootDiscriminant K := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h1
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hr2 : 0 < InfinitePlace.nrComplexPlaces K := by omega
  have hr0 : 0 ≤ rootDiscriminant K := by unfold rootDiscriminant; positivity
  let f : InfinitePlace K → NNReal := fun _ => NNReal.sqrt (Real.toNNReal (rootDiscriminant K))
  have hmult : ∀ w : InfinitePlace K, w.mult = 2 := fun w => by
    rw [InfinitePlace.mult, if_neg]
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add]
  have hS : (∏ w, f w ^ w.mult) = NNReal.sqrt ‖discr K‖₊ := by
    apply NNReal.eq
    rw [NNReal.coe_prod, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs, ← rootDiscr_pow_eq_sqrt_discr K]
    simp only [hmult, f, NNReal.coe_pow, NNReal.sq_sqrt, Real.coe_toNNReal _ hr0, Finset.prod_const,
      Finset.card_univ, hcard]
  have hbound : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume, hS]
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis,
      mixedEmbedding.finrank]
    unfold convexBodyLTFactor
    rw [IsTotallyComplex.nrRealPlaces_eq_zero K, pow_zero, one_mul, ← h1]
    have hs0 : ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) ≠ 0 := by
      simpa using discr_ne_zero K
    have hst : ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hN : ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      exact_mod_cast hI
    calc ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞)) *
          2 ^ (2 * InfinitePlace.nrComplexPlaces K)
        ≤ 1 * (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞)) *
          2 ^ (2 * InfinitePlace.nrComplexPlaces K) := by gcongr
      _ = 2 ^ InfinitePlace.nrComplexPlaces K * ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) := by
          rw [one_mul, pow_mul, mul_comm, ← mul_assoc, ← mul_pow]
          congr 1
          · rw [show ((2 : ℝ≥0∞) ^ 2 * 2⁻¹) = 2 by
              rw [pow_two, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]]
      _ < ((NNReal.pi ^ InfinitePlace.nrComplexPlaces K : NNReal) : ℝ≥0∞) *
          ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) := by
          rw [mul_comm _ ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞),
            mul_comm _ ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞)]
          refine ENNReal.mul_lt_mul_right hs0 hst ?_
          rw [ENNReal.coe_pow]
          refine ENNReal.pow_lt_pow_left hr2.ne' ?_
          rw [← ENNReal.coe_ofNat, ENNReal.coe_lt_coe]
          exact NNReal.coe_lt_coe.1 (by rw [NNReal.coe_real_pi, NNReal.coe_ofNat]; linarith [Real.pi_gt_three])
  obtain ⟨a, haI, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I hbound
  refine ⟨a, haI, ha0, fun w => ?_⟩
  have h2 := hlt w
  have hw0 : 0 ≤ w a := AbsoluteValue.nonneg _ _
  have hf2 : ((f w : NNReal) : ℝ) ^ 2 = rootDiscriminant K := by
    rw [← NNReal.coe_pow, NNReal.sq_sqrt, Real.coe_toNNReal _ hr0]
  calc (w a) ^ 2 ≤ ((f w : NNReal) : ℝ) ^ 2 := pow_le_pow_left₀ hw0 h2.le 2
    _ = rootDiscriminant K := hf2
end Formalism.MainNotions.BridgeLemma₂
