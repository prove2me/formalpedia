-- Prove2me | solution 1 for PI.WickFormula.Asm.phiH_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:50.631993+00:00
-- url     : https://prove2.me/submissions/f5164348-3677-4acd-9742-6aa756ff65d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
namespace PI.WickFormula.Asm
theorem _root_.solution (h1 : OrdLin) (a b : Fin r → AA) (a' b' : Fin s → AA) (σ₀ : M)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) : phiH h1 a b a' b' σ₀ R = ordEval (a + b) (a' + b') R • σ₀ := rfl
end PI.WickFormula.Asm
