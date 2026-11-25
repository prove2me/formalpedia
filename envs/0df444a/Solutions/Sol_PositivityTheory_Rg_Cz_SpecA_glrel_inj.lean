-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.glrel_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:38.174857+00:00
-- url     : https://prove2.me/submissions/38d9690f-e92d-4753-a641-4bb2134f4940

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
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
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (G : Fin n → Fin n → Module.End ℂ V) (H : Fin n → Fin n → Module.End ℂ W) (φ : V →ₗ[ℂ] W)
    (hφ : Function.Injective φ) (h : ∀ a b, φ ∘ₗ G a b = H a b ∘ₗ φ) (hH : GlRel H) : GlRel G := by
  have h' : ∀ a b v, φ (G a b v) = H a b (φ v) := fun a b v => LinearMap.congr_fun (h a b) v
  intro a b c d
  ext v
  apply hφ
  have hv := LinearMap.congr_fun (hH a b c d) (φ v)
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simpa [h', hbc, hda] using hv
end PositivityTheory.Rg.Cz.SpecA
