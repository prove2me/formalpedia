-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPs.fold_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:13.295477+00:00
-- url     : https://prove2.me/submissions/24c8f4f7-8008-4f8f-8487-0fba3840ed84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice

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
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPs
theorem _root_.solution (c : 𝕄 → 𝕄) : ∀ {p : ℕ} (T T' : Fin p → (𝕄 → ℂ) → (𝕄 → ℂ)),
    (∀ i F, T i (fun y => F (c y)) = fun y => T' i F (c y)) → ∀ F : 𝕄 → ℂ,
    (List.ofFn T).foldr (fun t h => t h) (fun y => F (c y)) =
      fun y => (List.ofFn T').foldr (fun t h => t h) F (c y)
  | 0, _, _, _, F => by simp
  | p + 1, T, T', h, F => by
    simp only [List.ofFn_succ, List.foldr_cons]
    rw [solution c (fun i => T i.succ) (fun i => T' i.succ) (fun i => h i.succ) F, h 0]
end ReciprocityTheory.ChartRestriction.DS.S7.CapPs
