-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_blockSpecial_monomial_ab1e8c92d616
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:21.223532+00:00
-- url     : https://prove2.me/submissions/d57f8d59-fa91-4fcd-a9a4-2d2a51b66f9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PValuativeCentre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_prod_pow_blockWeight_69a38f0cbb39


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (ρ : MRing ι F →+* κ) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    blockSpecial ρ (monomial d a) = C (ρ (monomial d a)) *
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) 1 := by
  have hT : (monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) (1 : κ)) =
      d.prod fun v n => (X v.1 : MvPolynomial K κ) ^ n := by
    rw [← prod_pow_blockWeight, monomial_eq, C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [hT, blockSpecial, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, map_mul,
    map_finsuppProd, map_finsuppProd]
  simp only [RingHom.comp_apply, mul_pow, map_pow]
  rw [Finsupp.prod_mul, mul_assoc]
end GroundTheory.Heights₂.Heights.FieldNumbers
