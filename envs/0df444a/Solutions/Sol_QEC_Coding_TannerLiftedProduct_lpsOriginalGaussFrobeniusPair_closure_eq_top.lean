-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrobeniusPair_closure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:01:05.188361+00:00
-- url     : https://prove2.me/submissions/f5b13c38-a4c6-4949-9a25-1f1b77276c26

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFrobeniusPair_subring_eq_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_not_prime_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI : CharP (LPSOriginalGaussAffineOrder N hN p ⧸ q) p :=
      lpsOriginalGaussMaximalResidue_charP N hN p q
    Subring.closure (Set.range ((RingHom.id (LPSOriginalGaussAffineOrder N hN p ⧸ q)).prod
      (frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p)) ∪
      Set.range ((frobenius (LPSOriginalGaussAffineOrder N hN p ⧸ q) p).prod
        (RingHom.id (LPSOriginalGaussAffineOrder N hN p ⧸ q)))) = ⊤ := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  apply lpsOriginalFrobeniusPair_subring_eq_top p _
    (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩))
    (lpsOriginalGaussMaximalResidueJN N hN p q)
  exact lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q
    ((lpsOriginalGaussMaximalResidueJN N hN p q)^p)
end QEC.Coding.TannerLiftedProduct
