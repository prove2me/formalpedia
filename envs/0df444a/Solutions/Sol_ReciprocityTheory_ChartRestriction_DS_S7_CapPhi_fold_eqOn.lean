-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.fold_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:47.826522+00:00
-- url     : https://prove2.me/submissions/4f33414a-7b78-4833-91f9-74b522ea39da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
theorem _root_.solution : ∀ (p : ℕ) (T : Fin p → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Fin p → Module.End ℂ (smoothS n)),
    (∀ i (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (T i F) ((A i G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)) →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn ((List.ofFn T).foldr (fun t h => t h) F)
        ((((List.ofFn A).prod) G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)
  | 0, T, A, _, F, G, h => by simpa using h
  | p + 1, T, A, hTA, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply]
    exact hTA 0 _ _ (solution p (fun i => T i.succ) (fun i => A i.succ) (fun i => hTA i.succ) F G h)
end ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
