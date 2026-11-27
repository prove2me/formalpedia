-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DefectConstStep_proof_87d705ead95b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:05.985913+00:00
-- url     : https://prove2.me/submissions/0534b6fb-7198-4250-9ac7-aa5f402da5e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectConstStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory
namespace GroundTheory.Heights₂.Heights
namespace DefectConstStep
theorem _root_.solution (h1 : DefectSymm.Statement) (h2 : ProperSymmCycle.Statement)
    (h3 : AdmissibleAE.Statement) (h4 : CycleSectionData.Statement) : DefectConstStep.Statement := by
  intro e hA n δ h Z f u u' hd hu hu'
  have hdu := h4 n e δ Z f u hd hu
  have hdu' := h4 n e δ Z f u' hd hu'
  have rel : ∀ {Y : ProjCycle ℂ n} {g : ℕ} {d : ℕ} {F : MvPolynomial (Fin (g + 1) × Fin n) ℂ},
      IsChowCycleData Y g d F → ∀ W ∈ Y.support, IsRelevant W :=
    fun hY W hW => (hY.prime W hW).isRelevant
  have hae := (h3 n Z (rel hd)).and ((h3 n _ (rel hdu)).and (h3 n _ (rel hdu')))
  obtain ⟨v, hvZ, hvu, hvu'⟩ := hae.exists
  have s1 : IsAdmissible (cycleSection Z v) u := h2 n Z u v hd.prime hu hvZ hvu
  have s2 : IsAdmissible (cycleSection Z v) u' := h2 n Z u' v hd.prime hu' hvZ hvu'
  rw [h1 e hA n δ h Z f u v hd hu hvZ hvu s1, h1 e hA n δ h Z f v u' hd hvZ hu' s2 hvu']
end DefectConstStep
end GroundTheory.Heights₂.Heights
