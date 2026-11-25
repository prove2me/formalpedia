-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SemiInvariantDeterminant.det_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:03.635162+00:00
-- url     : https://prove2.me/submissions/40b50305-2859-4ae4-b483-a700519b2f43

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSemiZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SemiInvariantDeterminant
namespace PositivityTheory.Rg.Cz.SemiInvariantDeterminant
theorem _root_.solution {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by
  have e : κ (bar τ) γ = (starRingEnd ℂ).mapMatrix (κ τ γ) := by
    ext i j; exact hK.conj τ γ i j
  rw [e, ← RingHom.map_det]
  rfl
end PositivityTheory.Rg.Cz.SemiInvariantDeterminant
