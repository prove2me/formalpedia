-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsMF.hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:46.2928+00:00
-- url     : https://prove2.me/submissions/fd0091b6-c026-406c-8d1e-b10d70ab4269

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qm_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace IsMF
theorem _root_.solution {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) := by
  obtain ⟨g, hg⟩ := hf
  have hgf : (⇑g : ℍ → ℂ) = f := funext hg
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rw [hgf, ← qm_one_eq] at h
  exact h
end IsMF
end ReciprocityTheory.ChartRestriction.L1
