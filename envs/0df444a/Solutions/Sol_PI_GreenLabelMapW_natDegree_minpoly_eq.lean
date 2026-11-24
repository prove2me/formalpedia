-- Prove2me | solution 1 for PI.GreenLabelMapW.natDegree_minpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:43.799952+00:00
-- url     : https://prove2.me/submissions/9839b644-2e41-42e5-8541-12a208fed332

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Theorems.Thm_PI_GreenLabelMapW_aroots_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]
namespace PI.GreenLabelMapW
theorem _root_.solution {P : K[X]} (hm : P.Monic) (hi : Irreducible P)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x))
    (hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ P = 0 → aeval r₂ P = 0 → f r₁ = f r₂ → r₁ = r₂) :
    (minpoly K (f w)).natDegree = P.natDegree := by
  have e1 : ∀ Q : K[X], (Q.aroots (AlgebraicClosure K)).card = Q.natDegree := fun Q => by
    unfold Polynomial.aroots
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  rw [← e1, ← e1, aroots_eq_map hm hi hw f hf hinj, Multiset.card_map]
end PI.GreenLabelMapW
