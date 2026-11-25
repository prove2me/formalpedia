-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralPermute_proof_c7843aa748b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:16.846545+00:00
-- url     : https://prove2.me/submissions/20db82aa-133e-408f-aa3b-3116a22d821b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralPermute
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18


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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagIntegralPermute
theorem _root_.solution (h1 : FlagCoeffBlockPermute.Statement) :
    FlagIntegralPermute.Statement := by
  classical
  intro f N w H
  let e : Fin f × Fin N ≃ Fin f × Fin N := Equiv.prodShear (Equiv.refl _) w
  have hcomp : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) =
        Finsupp.equivMapDomain e.symm α := by
    intro α; ext p; simp [Finsupp.equivMapDomain_apply, e, Equiv.prodShear]
  have hH : ∀ α, coeff α (blockPermute f N w H) = coeff (Finsupp.equivMapDomain e.symm α) H := by
    intro α; rw [h1, hcomp]
  have hD : ∀ α, coeff (Finsupp.equivMapDomain e.symm α) (blockVandermonde f N) =
      blockSign f N w * coeff α (blockVandermonde f N) := by
    intro α
    rw [← hcomp, ← h1, Flag.blockPermute_blockVandermonde, coeff_smul, smul_eq_mul]
  have hs2 : blockSign f N w * blockSign f N w = 1 := Flag.blockSign_mul_self f N w
  have hs0 : blockSign f N w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs2; exact zero_ne_one hs2
  have hfac : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivMapDomain e.symm α).prod (fun _ n => (n.factorial : ℚ)) =
        α.prod (fun _ n => (n.factorial : ℚ)) := by
    intro α; rw [Finsupp.prod_equivMapDomain]
  unfold flagIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
  · simp only [MvPolynomial.mem_support_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      Finsupp.domCongr_apply, hD]
    exact ⟨fun h => mul_ne_zero hs0 h, fun h h' => h (by rw [h', mul_zero])⟩
  · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, hH, hD, hfac]
    linear_combination (-(coeff (Finsupp.equivMapDomain e.symm α) H *
      coeff α (blockVandermonde f N) * α.prod (fun _ n => (n.factorial : ℚ)))) * hs2
end FlagIntegralPermute
end GroundTheory.Heights₂.Heights.RestTerms
