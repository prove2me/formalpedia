-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_halfInvLine_52cbab56b65e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:51.92719+00:00
-- url     : https://prove2.me/submissions/29ff3ec2-60a6-48ea-80b2-3911624b0073

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_halfInvLine_h_of_pos_2cba2ddf9fad

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (c : K → ℤ)
    (hc : ∀ k, 2 * c k = -(A.a k + B.a k)) : IsSmoothHerm (halfInvLine A B c hc) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A.h z * B.h z) ^ (-(1 / 2 : ℝ)))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA.mul hB).rpow_const_of_ne fun z hz => (mul_pos (A.pos z hz) (B.pos z hz)).ne'
  exact hs.congr fun z hz => halfInvLine_h_of_pos A B c hc z hz
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
