-- Prove2me | solution 1 for PI.VolStabW.volAA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:05.316647+00:00
-- url     : https://prove2.me/submissions/6c9adced-377b-4472-ac54-af9601e950b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVol
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isCompact_latV
import Theorems.Thm_PI_VolStabW_SdUniqW_BR_add
import Theorems.Thm_PI_VolStabW_SdUniqW_pairHerm_add
import Theorems.Thm_PI_VolStabW_SdUniqW_psiV_add
import Theorems.Thm_PI_VolStabW_VolAAW_ann_eq
import Theorems.Thm_PI_VolStabW_VolAAW_ev_dual
import Theorems.Thm_PI_VolStabW_VolAAW_ev_dualH
import Theorems.Thm_PI_VolStabW_VolAAW_isCompact_hermO
import Theorems.Thm_PI_VolStabW_VolAAW_smul_hermO
import Theorems.Thm_PI_VolStabW_VolAAW_smul_latV
import Theorems.Thm_PI_VolStabW_VolAAW_vol_one_of_ann
import Theorems.Thm_PI_VolStabW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabW_secondCountable_Fv
import Theorems.Thm_PI_VolStabW_sigma_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW PositiveNearLattice SdDualW VolAAW
namespace PI.VolStabW
theorem _root_.solution (hC : CondAA) : VolAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  filter_upwards [hC F ψ hψ, ev_dual b σ hσ J hJ.2 (a := a), ev_dualH b σ hσ a] with v hCv hDW hDH
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  refine ⟨fun μv hμ => ?_, fun νv hν => ?_⟩
  · have hA := ann_eq v (psiV F ψ v) (BR (Fv F v) σ J (n := a)) (latV (M := M) (n := a) b v) hCv
      (smul_latV b v σ J) hDW
    exact vol_one_of_ann hμ (fun X T Y => by rw [BR_add, psiV_add]) (SdDualW.latSub v b a M)
      (isCompact_latV b v a M) (isClopen_latV b v a M).isOpen hA
  · have hA := ann_eq v (psiV F ψ v) (pairHerm (Fv F v) σ a)
      (hermO b v σ a : Set (HermR (Fv F v) σ a)) hCv (smul_hermO b v σ a) hDH
    exact vol_one_of_ann hν (fun S T U => by rw [pairHerm_add, psiV_add]) (hermO b v σ a)
      (isCompact_hermO b v σ a).1 (isCompact_hermO b v σ a).2 hA
end PI.VolStabW
