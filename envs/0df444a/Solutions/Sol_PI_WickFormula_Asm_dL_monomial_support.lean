-- Prove2me | solution 1 for PI.WickFormula.Asm.dL_monomial_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:19:17.387306+00:00
-- url     : https://prove2.me/submissions/9b79ede0-c89f-4b55-9d88-454389581ff2

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
namespace PI.WickFormula.Asm
theorem _root_.solution {k : Type} [CommRing k] {r s : ℕ} (κ : Fin r → Fin s → k) (i : Fin r)
    (m : Fin r ⊕ Fin s →₀ ℕ) (c : k) (u : Fin r ⊕ Fin s →₀ ℕ)
    (hu : u ∈ (Gen.dL κ i (monomial m c)).support) : xdeg u ≤ xdeg m := by
  have key : Gen.dL κ i (monomial m c) =
      ∑ j, monomial (m - Finsupp.single (Sum.inr j) 1) (κ i j * (c * (m (Sum.inr j) : k))) := by
    simp [Gen.dL, pderiv_monomial, smul_monomial]
  rw [key] at hu
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  have hu' := MvPolynomial.support_monomial_subset hj
  rw [Finset.mem_singleton] at hu'
  subst hu'
  unfold xdeg
  exact Finset.sum_le_sum fun i _ => by simp
end PI.WickFormula.Asm
