-- Prove2me | solution 1 for PI.GreenLabelMapW.irreducible_charpoly_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:29.959262+00:00
-- url     : https://prove2.me/submissions/5ff14941-f14a-4949-bb3c-9bd715b17383

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Theorems.Thm_PI_GreenLabelMapW_root_inv

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix ι ι K))) {z : AlgebraicClosure K}
    (hz0 : z ≠ 0) (hz : aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0) :
    Irreducible (Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K)) := by
  classical
  have hint : ∀ w : AlgebraicClosure K, IsIntegral K w := fun w => Algebra.IsIntegral.isIntegral w
  have h1 : Matrix.charpoly (γ : Matrix ι ι K) = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hadj : IntermediateField.adjoin K {z⁻¹} = IntermediateField.adjoin K {z} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K z)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h2 := inv_mem (IntermediateField.mem_adjoin_simple_self K z⁻¹)
      rwa [inv_inv] at h2
  have hdeg : (minpoly K z⁻¹).natDegree = (minpoly K z).natDegree := by
    rw [← IntermediateField.adjoin.finrank (hint _), ← IntermediateField.adjoin.finrank (hint _), hadj]
  have hdvd : minpoly K z⁻¹ ∣ Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K) :=
    minpoly.dvd K _ (root_inv γ hz0 hz)
  have heq : Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K) = minpoly K z⁻¹ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hint _)) (Matrix.charpoly_monic _) hdvd
      (by rw [Matrix.charpoly_natDegree_eq_dim, hdeg, ← h1, Matrix.charpoly_natDegree_eq_dim])
  rw [heq]
  exact minpoly.irreducible (hint _)
end PI.GreenLabelMapW
