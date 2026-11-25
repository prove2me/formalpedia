-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SemiInvariantDeterminant.det_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:23.319863+00:00
-- url     : https://prove2.me/submissions/9b4caec5-0096-4539-8c57-bb93b9ca7760

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
    (κ τ γ).det * star (κ τ γ).det = 1 := by
  have := congrArg Matrix.det (hK.unit τ γ)
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
end PositivityTheory.Rg.Cz.SemiInvariantDeterminant
