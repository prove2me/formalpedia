-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_pull_c9953dbb0544
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:28.912814+00:00
-- url     : https://prove2.me/submissions/2d0a12fe-e037-4527-af76-d4e9140efc4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (j : Fin 2) {X : HermLine (T.yyIdx ι ν κ)} {X' : HermLine (T.wwIdx ι ν κ)}
    (hX : IsSmoothHerm X) (hp : IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) X X') : IsSmoothHerm X' := by
  have hfun : X'.h = fun z => X.h (fun p => z (T.yyEmb j p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hfun]
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, T.wwIdx ι ν κ k) → ℂ => fun p => z (T.yyEmb j p)) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (T.yyEmb j p)
  refine hX.comp hlin.contDiffOn ?_
  intro z hz k
  fin_cases j <;> cases k
  · obtain ⟨i, hi⟩ := hz .base; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .det; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .line0; exact ⟨i, by simpa [T.yyEmb] using hi⟩
  · obtain ⟨i, hi⟩ := hz .base; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .det; exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := hz .line1; exact ⟨i, by simpa [T.yyEmb] using hi⟩
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
