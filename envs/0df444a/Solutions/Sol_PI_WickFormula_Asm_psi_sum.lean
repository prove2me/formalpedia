-- Prove2me | solution 1 for PI.WickFormula.Asm.psi_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:17.66428+00:00
-- url     : https://prove2.me/submissions/e16ba274-db28-4325-a699-6a0ea4e1a803

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
theorem _root_.solution (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (N : ℕ) {α : Type} (t : Finset α) (g : α → MvPolynomial (Fin r ⊕ Fin s) k) :
    psi h1 a a' κ σ₀ N (∑ x ∈ t, g x) = ∑ x ∈ t, psi h1 a a' κ σ₀ N (g x) := by
  unfold psi
  simp only [map_sum]
  exact Finset.sum_comm
end PI.WickFormula.Asm
