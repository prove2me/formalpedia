-- Prove2me | solution 1 for PI.WickFormula.Asm.xdeg_le_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:23.525976+00:00
-- url     : https://prove2.me/submissions/bdd46362-d41f-4444-9749-cc3bf1da42bd

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
theorem _root_.solution {k : Type} [CommRing k] {r s : ℕ} (P : MvPolynomial (Fin r ⊕ Fin s) k)
    (m : Fin r ⊕ Fin s →₀ ℕ) (hm : m ∈ P.support) : xdeg m ≤ P.totalDegree := by
  have h := MvPolynomial.le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type] at h
  unfold xdeg
  omega
end PI.WickFormula.Asm
