-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.mono_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:26.509961+00:00
-- url     : https://prove2.me/submissions/86340126-88d5-4ef0-b241-5e8181ed62d5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartA

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
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
namespace PositivityTheory.Rg.Cz.SWS
theorem _root_.solution (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Continuous (mono κ lab c I K) := by
  have hent : ∀ τ, Continuous fun k => κ τ k :=
    fun τ => continuous_pi fun i => continuous_pi fun j => hK.cont τ i j
  unfold mono
  refine Continuous.mul ?_ ?_
  · refine continuous_finset_prod _ fun τ _ => ?_
    exact ((hent τ).matrix_det).zpow₀ (c τ) fun k => Or.inl (det_ne hK τ k)
  · exact continuous_finset_prod _ fun p _ => hK.cont (lab p) (I p) (K p)
end PositivityTheory.Rg.Cz.SWS
