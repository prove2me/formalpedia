-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.eG_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:56:13.000444+00:00
-- url     : https://prove2.me/submissions/58c85a8b-4688-45db-8271-9e0f6aea2622

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_eS_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (T : GoodSet K G) (P0 : Pair K G) (hM : M1 T P0) :
    ∃ n : ℕ, ∃ a b : Fin n → MonoidAlgebra K G, eG T = ∑ i, a i * eps P0 * b i := by
  classical
  choose n a b h using eS_mem T P0 hM
  let ι := Σ s : T.S, Fin (n s)
  let e := (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, fun i => eS T (e.symm i).1 * a _ (e.symm i).2,
    fun i => b _ (e.symm i).2, ?_⟩
  rw [eG, Fintype.sum_equiv e.symm (fun i => eS T (e.symm i).1 * a _ (e.symm i).2 * eps P0 *
      b _ (e.symm i).2) (fun t : ι => eS T t.1 * a _ t.2 * eps P0 * b _ t.2) (fun _ => rfl),
    Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun s _ => h s
end PI.Dv.HermitianFormEquivalence
