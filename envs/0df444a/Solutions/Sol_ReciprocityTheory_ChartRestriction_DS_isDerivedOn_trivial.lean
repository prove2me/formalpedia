-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isDerivedOn_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:19.40102+00:00
-- url     : https://prove2.me/submissions/0dea5a61-f523-433d-838c-8ff9603891d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] :
    IsURepOn (UJset ε) (fun _ : Matrix (Fin n) (Fin n) ℂ => (1 : H →L[ℂ] H)) ∧
      IsDerivedOn ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (1 : H →L[ℂ] H)) ⊤ (fun _ _ => 0) := by

  refine ⟨⟨⟨rfl, fun a _ b _ => ?_⟩, fun g _ v => ?_, fun v => continuousOn_const⟩, ⟨?_, ?_, ?_⟩⟩
  · ext v
    simp
  · simp
  · intro a b c d
    simp
  · intro k _ v _
    exact Submodule.mem_top
  · intro X _ v
    have h1 : ((actM (fun _ _ => (0 : Module.End ℂ (⊤ : Submodule ℂ H))) X v : (⊤ : Submodule ℂ H)) : H) = 0 := by
      simp [actM]
    rw [h1]
    simp only [ContinuousLinearMap.one_apply]
    exact hasDerivAt_const _ _
end ReciprocityTheory.ChartRestriction.DS
