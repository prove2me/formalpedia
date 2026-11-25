-- Prove2me | solution 1 for P2M_Formalism_L2_S_Pv_EnergyAbs_prod_map__inv_221c0b6c8f4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:57.510955+00:00
-- url     : https://prove2.me/submissions/1df90c6f-d74f-4da1-99eb-386998bfd660

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Theorems.Thm_P2M_Formalism_L2_S_Pv_EnergyAbs_measurable__inv_e6ee5e712638

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) :
    μ.prod μ = ((ν.prod μS).prod (ν'.prod μS')).map (Prod.map φinv φinv) := by
  calc μ.prod μ = ((ν.prod μS).map φinv).prod ((ν'.prod μS').map φinv) := by
        rw [← hm, ← hm']
    _ = _ := map_prod_map _ _ measurable_φinv measurable_φinv
end Formalism.L2.S.Pv.EnergyAbs
