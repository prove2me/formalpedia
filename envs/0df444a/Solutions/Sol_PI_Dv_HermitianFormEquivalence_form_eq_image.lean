-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.form_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:58.05808+00:00
-- url     : https://prove2.me/submissions/7e98543f-8dad-4270-867f-3f6b69410a63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_io_j_asAlg

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
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution (M : GMap K σ G T EE ρE) (a : MonoidAlgebra K G) :
    M.form a = (fun z => ∑ g : G, σ (a.coeff g) • ρE g z) '' M.form 1 := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨M.io (M.j x), ⟨x, by simp⟩, ?_⟩
    exact (io_j_asAlg M a x).symm
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    simp only [map_one, Module.End.one_apply]
    exact io_j_asAlg M a x
end PI.Dv.HermitianFormEquivalence
