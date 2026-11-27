-- Prove2me | solution 2 for PositivityTheory.Rg.Rs.SliceClasses.exists_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:27.851552+00:00
-- url     : https://prove2.me/submissions/5d6f5365-bd93-417e-8983-282a9149281d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC
import Theorems.Thm_PositivityTheory_Rg_Rs_SliceClasses_C_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
namespace PositivityTheory.Rg.Rs.SliceClasses
theorem _root_.solution {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}
    (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) (Φ : U →ₗ[ℂ] ℂ) (hΦ : Φ ≠ 0)
    (hinv : ∀ i, Φ ∘ₗ M i = Φ) : ∃ w, w ≠ 0 ∧ ∀ i, M i w = w := by
  have hv : ∃ v ∈ (⊤ : Submodule ℂ U), Φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ (LinearMap.ext fun v => by rw [h v Submodule.mem_top, LinearMap.zero_apply])
  obtain ⟨w, -, hw0, hfix⟩ := C_gen M hc Φ _ ⊤ rfl (fun _ _ _ => Submodule.mem_top)
    (fun i v _ => LinearMap.congr_fun (hinv i) v) hv
  exact ⟨w, hw0, hfix⟩
end PositivityTheory.Rg.Rs.SliceClasses
