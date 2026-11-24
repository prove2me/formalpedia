-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIMultilin_update_comp_swap_7f6a686cf33e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:10.781175+00:00
-- url     : https://prove2.me/submissions/c47497f0-e132-4b6e-aae2-6bdfefee07ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmIMultilin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
theorem _root_.solution {m : ℕ} (L : Fin (m + 1) → HermLine ι) (j : Fin (m + 1)) (X : HermLine ι) :
    Function.update L j X ∘ Equiv.swap j (Fin.last m) =
      Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · have hne : Equiv.swap j (Fin.last m) i.castSucc ≠ j := by
      intro h
      have h' : Equiv.swap j (Fin.last m) i.castSucc = Equiv.swap j (Fin.last m) (Fin.last m) := by
        rw [h, Equiv.swap_apply_right]
      exact Fin.castSucc_ne_last i ((Equiv.swap j (Fin.last m)).injective h')
    simp [Function.update_of_ne hne]
end GroundTheory.Heights₂.Heights.Inter.ThmIMultilin
