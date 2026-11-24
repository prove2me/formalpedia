-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_sum_log_places_eq_zero_ae84c0a90009
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:50.879369+00:00
-- url     : https://prove2.me/submissions/b3efebfd-f0e8-4c61-b561-3965b1573001

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {t : K} (ht : t ≠ 0) :
    (∑ᶠ v : FinitePlace K, Real.log (v t)) + ∑ σ : K →+* ℂ, Real.log ‖σ t‖ = 0 := by
  have hfin : (Function.mulSupport fun w : FinitePlace K ↦ w t).Finite :=
    FinitePlace.hasFiniteMulSupport ht
  have hprod := FinitePlace.prod_eq_inv_abs_norm ht
  rw [finprod_eq_prod_of_mulSupport_subset (s := hfin.toFinset) _
    (fun v hv ↦ Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hv))] at hprod
  have hsupp : (Function.support fun v : FinitePlace K ↦ Real.log (v t)) ⊆ hfin.toFinset := by
    intro v hv
    refine Finset.mem_coe.mpr (hfin.mem_toFinset.mpr fun h ↦ hv ?_)
    simp only [h, Real.log_one]
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Real.log_prod (fun v _ ↦ (FinitePlace.pos_iff.mpr ht).ne'), hprod]
  have h1 : (((Algebra.norm ℚ t : ℚ) : ℂ)) = ∏ σ : K →+* ℂ, σ t := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ t
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl).symm
  rw [← Real.log_prod (fun σ _ ↦ by rw [norm_ne_zero_iff, map_ne_zero]; exact ht),
    ← norm_prod, ← h1, Complex.norm_ratCast]
  push_cast
  rw [Real.log_inv]
  ring
end GroundTheory.Heights₂.Heights
