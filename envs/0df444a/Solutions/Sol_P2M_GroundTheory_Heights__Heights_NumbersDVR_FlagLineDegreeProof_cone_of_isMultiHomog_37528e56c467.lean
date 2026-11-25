-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_cone_of_isMultiHomog_37528e56c467
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:44.146344+00:00
-- url     : https://prove2.me/submissions/629024ea-b083-4ff8-961e-fe97970ca47d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_weight_blockWeight_apply_2427db235b67

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
theorem _root_.solution {K Kt : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {R S : Type*} [CommRing R] [CommRing S] (r : R →+* S)
    (x : (Σ k, ι k) → S) (τ : K → Kt) {h : MRing ι R} {D : K → ℕ} (hh : IsMultiHomog h D) :
    eval₂Hom (C.comp r) (fun p => C (x p) * X (τ p.1)) h =
      C (eval₂ r x h) * ∏ k, (X (τ k) : MvPolynomial Kt S) ^ D k := by
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  rw [map_sum, eval₂_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [eval₂Hom_monomial, eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc,
    RingHom.comp_apply]
  have hB : ∏ p : (Σ k, ι k), (X (τ p.1) : MvPolynomial Kt S) ^ μ p = ∏ k, X (τ k) ^ D k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i : ι k, (X (τ k) : MvPolynomial Kt S) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hh (mem_support_iff.mp hμ)]
  rw [hB]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
