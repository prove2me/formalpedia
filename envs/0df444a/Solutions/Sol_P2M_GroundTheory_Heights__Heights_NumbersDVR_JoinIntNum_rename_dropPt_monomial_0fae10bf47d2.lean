-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_rename_dropPt_monomial_0fae10bf47d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:37.087883+00:00
-- url     : https://prove2.me/submissions/05ca7d3e-0eb3-4a0f-a94e-9aec5b10f94f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum

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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
theorem _root_.solution (d : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) →₀ ℕ) (c : F) :
    rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (monomial d c)) * X newVar ^ (d newVar) =
      monomial d c := by
  induction d using Finsupp.induction generalizing c with
  | zero =>
    rw [Finsupp.coe_zero, Pi.zero_apply, pow_zero, mul_one, ← C_apply, aeval_C, algebraMap_eq,
      rename_C]
  | single_add a b f _ _ ih =>
    have hsplit : monomial (Finsupp.single a b + f) c = X a ^ b * monomial f c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have key : rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (X a ^ b : MRing (Sum.elim ι ptIdx) F)) *
        X newVar ^ (Finsupp.single a b newVar) = X a ^ b := by
      rcases a with ⟨k | u, i⟩
      · have hne : (⟨.inl k, i⟩ : Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≠ newVar := by
          intro h
          exact Sum.inl_ne_inr (congrArg Sigma.fst h)
        rw [Finsupp.single_eq_of_ne hne.symm]
        simp only [map_pow, aeval_X, pow_zero, mul_one]
        show (rename (liftVar (ι := ι) ptIdx) (X ⟨k, i⟩ : MRing ι F)) ^ b = _
        rw [rename_X]
        rfl
      · cases u
        obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
        show _ * X newVar ^ (Finsupp.single newVar b newVar) = X newVar ^ b
        simp [dropPt, newVar]
    rw [hsplit, map_mul, map_mul, Finsupp.add_apply, pow_add]
    calc _ = (rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (X a ^ b : MRing (Sum.elim ι ptIdx) F)) *
          X newVar ^ (Finsupp.single a b newVar)) *
          (rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (monomial f c)) *
          X newVar ^ (f newVar)) := by ring
      _ = _ := by rw [key, ih]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
