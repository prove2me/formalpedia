-- Prove2me | solution 1 for PI.WickFormula.omon_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:43.673032+00:00
-- url     : https://prove2.me/submissions/095e1f09-6c72-48fd-a7b5-666582de8e9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
namespace PI.WickFormula
theorem _root_.solution {AA : Type} [Ring AA] {r s : ℕ} (a : Fin r → AA) (a' : Fin s → AA)
    (m : Fin r ⊕ Fin s →₀ ℕ) (j : Fin s) :
    omon a a' (m - Finsupp.single (Sum.inr j) 1) =
      lprod a (fun i => m (Sum.inl i)) * lprod a' (fun j' => m (Sum.inr j') - if j = j' then 1 else 0) := by
  unfold omon
  congr 1
  · congr 1
    funext i
    simp
  · congr 1
    funext j'
    simp [Finsupp.single_apply]
end PI.WickFormula
