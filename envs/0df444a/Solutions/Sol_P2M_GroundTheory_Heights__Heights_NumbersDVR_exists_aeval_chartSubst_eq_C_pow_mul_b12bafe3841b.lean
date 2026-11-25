-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_aeval_chartSubst_eq_C_pow_mul_b12bafe3841b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:09.910133+00:00
-- url     : https://prove2.me/submissions/3e98ae21-81ea-4af5-86f4-17f68ef05d6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontalMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalChartLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_chartSubst_liftForm_b9c03287c289


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (a : J → MRing ι R) (j₀ : J) (h : Polynomial (MRing ι R)) :
    ∃ (d : ℕ) (H : MRing (extIdx ι J) R),
      aeval (chartSubst a) H = Polynomial.C (a j₀ ^ d) * h := by
  refine ⟨h.natDegree, ∑ k ∈ Finset.range (h.natDegree + 1),
    liftForm (h.coeff k * a j₀ ^ (h.natDegree - k)) * newVar j₀ ^ k, ?_⟩
  have hs : Polynomial.C (a j₀ ^ h.natDegree) * h = ∑ k ∈ Finset.range (h.natDegree + 1),
      Polynomial.C (a j₀ ^ h.natDegree) * (Polynomial.C (h.coeff k) * Polynomial.X ^ k) := by
    rw [← Finset.mul_sum, ← h.as_sum_range_C_mul_X_pow]
  rw [hs, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ h.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e : a j₀ ^ h.natDegree = a j₀ ^ (h.natDegree - k) * a j₀ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [map_mul, map_pow, aeval_chartSubst_liftForm, e]
  simp only [newVar, aeval_X, chartSubst, map_mul, map_pow]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
