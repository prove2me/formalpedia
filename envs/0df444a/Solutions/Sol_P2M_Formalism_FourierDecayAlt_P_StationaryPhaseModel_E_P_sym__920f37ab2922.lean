-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:46.999821+00:00
-- url     : https://prove2.me/submissions/8c1fd740-3102-4a2a-8b1e-2a3ba03bd09d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_subset
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) {N : ℕ}
    (hN : N ≤ d + 6) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) 3 N
      ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) (E_P φ) :=
  ((E_P_sym (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit hph.bd).subset
    (Metric.closedBall_subset_closedBall hρr)).mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x) hN le_rfl
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
