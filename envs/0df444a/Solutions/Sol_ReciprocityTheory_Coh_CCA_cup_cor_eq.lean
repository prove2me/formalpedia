-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.cup_cor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:14.258198+00:00
-- url     : https://prove2.me/submissions/c25aa923-c852-4638-be7f-8b41fb947084

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
import Theorems.Thm_ReciprocityTheory_Coh_CCA_pp_trunc
import Theorems.Thm_ReciprocityTheory_Coh_CCA_prod_castAdd
import Theorems.Thm_ReciprocityTheory_Coh_CCA_pp_tail
import Theorems.Thm_ReciprocityTheory_Coh_CCA_resSub_rho_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M N P : TRep R G}
  (U : Subgroup G) [U.FiniteIndex]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution (b : Pairing M N P) (p q : ℕ) (f : (Fin p → U) → M.V) (f' : (Fin q → G) → N.V)
    (g : Fin (p + q) → G) :
    cupFun b p q (corFun M U p f) f' g =
      normF P U (p + q) (hcup b.β p q (fun x => homz (M.resSub U).rho p f (fun i => retr U (x i)))
        (homz N.rho q f')) (Fin.partialProd g) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel U)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel U))
  have hr1 : ∀ c : Quotient (QuotientGroup.rightRel U), retr U c.out = 1 := by
    intro c
    apply Subtype.ext
    show c.out * (⟦c.out⟧ : Quotient (QuotientGroup.rightRel U)).out⁻¹ = 1
    rw [Quotient.out_eq, mul_inv_cancel]
  have htail : ∀ j : Fin q, (Fin.partialProd g ⟨p + ↑j, by omega⟩)⁻¹ *
      Fin.partialProd g ⟨p + (↑j + 1), by omega⟩ = g (Fin.natAdd p j) := fun j => pp_tail g j
  have h0 : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  unfold cupFun corFun normF
  simp only [finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hcup, homz, Fin.coe_castSucc, Fin.val_succ, Fin.val_zero, add_zero]
  simp only [pp_trunc, Fin.coe_castSucc, Fin.val_succ]
  rw [h0, mul_one, hr1]
  erw [resSub_rho_one]
  rw [prod_castAdd]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, htail]
  rw [← b.equiv]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
end ReciprocityTheory.Coh.CCA
