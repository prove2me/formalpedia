-- Prove2me | solution 1 for PI.Dv.TIW.finsum_eq_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:24.087588+00:00
-- url     : https://prove2.me/submissions/2ad49255-08dc-42c6-9e3a-988b39de7197

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Theorems.Thm_P2M_PI_Dv_TIW_volume_finite__4c8f653d0763
import Theorems.Thm_PI_Dv_TIW_norm_embedding_eq
import Theorems.Thm_PI_Dv_TIW_log_norm_embedding
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero
namespace PI.Dv.TIW
theorem _root_.solution {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (hx : x ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      Real.log |((Algebra.norm ℤ x : ℤ) : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  classical
  have hxK : algebraMap (𝓞 K) K x ≠ 0 := by
    first
    | simpa using hx
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hx
  have hf : ∀ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      -Real.log ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ / (Module.finrank ℚ K : ℝ) := by
    intro w
    rw [log_norm_embedding w _ hxK]
    unfold lw
    ring
  have hfin := volume_finite' K x hx
  have hsub : ∀ w, w ∉ hfin.toFinset → ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ = 1 := by
    intro w hw
    have h0 : vAdd w (algebraMap (𝓞 K) K x) = 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hw
      exact hw
    rw [norm_embedding_eq w _ hxK, h0, neg_zero, zpow_zero]
  have hne : ∀ w ∈ hfin.toFinset, ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ ≠ 0 :=
    fun w _ => norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hxK)
  have hprod : ∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ =
      ∏ w ∈ hfin.toFinset, ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro w hw
    rw [Finset.mem_coe]
    by_contra hws
    exact hw (hsub w hws)
  have PF : ∏ᶠ w : FinitePlace K, w (algebraMap (𝓞 K) K x) = (|((Algebra.norm ℤ x : ℤ) : ℝ)|)⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm_int hx
    first
    | exact h
    | (rw [Int.cast_abs] at h; exact h)
    | (push_cast at h; exact h)
    | (convert h using 3; simp)
  have PF' : ∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ =
      (|((Algebra.norm ℤ x : ℤ) : ℝ)|)⁻¹ := by
    rw [← PF]
    first
    | exact finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
    | exact finprod_eq_of_bijective (FinitePlace.equivHeightOneSpectrum (K := K)).symm (Equiv.bijective _)
        (fun _ => rfl)
    | exact (finprod_eq_of_bijective (FinitePlace.equivHeightOneSpectrum (K := K)).symm (Equiv.bijective _)
        (fun _ => rfl)).symm
  rw [finsum_congr hf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [← Finset.sum_div, Finset.sum_neg_distrib,
      ← Real.log_prod hne,
      ← hprod, PF', Real.log_inv, neg_neg]
  · intro w hw
    rw [Finset.mem_coe]
    by_contra hws
    apply hw
    show -Real.log ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ / (Module.finrank ℚ K : ℝ) = 0
    rw [hsub w hws, Real.log_one, neg_zero, zero_div]
end PI.Dv.TIW
