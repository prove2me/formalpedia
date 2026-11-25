-- Prove2me | solution 1 for PI.GreenLabelMapW.greenLab_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:24.273844+00:00
-- url     : https://prove2.me/submissions/e7093c2d-cd33-41a9-88a6-66b460f40fb7

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Theorems.Thm_PI_GreenLabelMapW_greenLab_eq
import Theorems.Thm_PI_GreenLabelMapW_isCuspidal_fin_one
import Theorems.Thm_PI_GreenLabelMapW_charpoly_fin_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution (Cv : LabelConv K) (hC : CuspParam K Cv) (τ : FDRep ℂ (GL (Fin 1) K))
    (x : K) (hs : Simple τ) (hx : x ≠ 0)
    (htr : ∀ (γ : GL (Fin 1) K) (m : ℕ),
      Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = Cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m) :
    greenLab Cv 1 τ = X - Polynomial.C x := by
  apply greenLab_eq Cv hC le_rfl hs (isCuspidal_fin_one τ)
  have hxX : X - Polynomial.C x ≠ X := by
    intro h
    apply hx
    have h' := congrArg (fun P : K[X] => P.coeff 0) h
    simpa using h'
  refine ⟨monic_X_sub_C x, irreducible_X_sub_C x, hxX, by simp, ?_⟩
  intro x' hx' γ _ z hz m hm
  have hx'' : x' = algebraMap K (AlgebraicClosure K) x := by
    simpa [sub_eq_zero] using hx'
  have hz' : z = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) := by
    rw [charpoly_fin_one] at hz
    have hz2 : z = algebraMap K (AlgebraicClosure K) ((γ : Matrix (Fin 1) (Fin 1) K) 0 0) := by
      simpa [sub_eq_zero] using hz
    rw [hz2, Matrix.det_unique, Fin.default_eq_zero]
  simp only [Fintype.card_fin, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, mul_one]
  rw [hx'', htr γ m (hm.trans hz')]
end PI.GreenLabelMapW
