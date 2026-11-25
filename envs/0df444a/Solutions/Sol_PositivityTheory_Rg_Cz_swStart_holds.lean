-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.swStart_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:17.78227+00:00
-- url     : https://prove2.me/submissions/f3544f8c-28c7-4dd8-abbe-fe4d0787b58d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_tensor_exists
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_exists_half
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_nonvanish
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : SWStart := by
  unfold SWStart
  intro n M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG φ hφ
  classical
  letI : MeasurableSpace Γ := borel Γ
  haveI : BorelSpace Γ := ⟨rfl⟩
  obtain ⟨H, hH⟩ := SWS.exists_half bar hK.invol hK.ne
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  have hf : Continuous fun k => φ (ρ k y) := hG.cont y φ
  have h1 : φ (ρ 1 y) ≠ 0 := by simpa [hG.one] using hy
  obtain ⟨g, ⟨m, lab, c, I, K, hlab, rfl⟩, hg⟩ :=
    SWS.nonvanish (Measure.haar : Measure Γ) hK hH hf 1 h1
  obtain ⟨ξ, hξ1, hξ2⟩ := SWS.tensor_exists (Measure.haar : Measure Γ) hK hG y lab c K
  refine ⟨m, lab, -c, ξ, ?_, ?_, I, 1, Subalgebra.one_mem _, ?_⟩
  · intro p q h
    exact (hH (lab q)).1 (hlab q) (h ▸ hlab p)
  · intro γ
    rw [hξ1 γ]
    simp
  · simpa [hξ2 I φ] using hg
end PositivityTheory.Rg.Cz
