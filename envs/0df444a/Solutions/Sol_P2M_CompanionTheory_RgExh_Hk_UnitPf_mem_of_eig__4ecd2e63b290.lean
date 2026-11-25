-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_UnitPf_mem_of_eig__4ecd2e63b290
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:11:10.593497+00:00
-- url     : https://prove2.me/submissions/b1438d8f-72f6-4344-a755-9eccd237f2c6

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}
namespace CompanionTheory.RgExh.Hk.UnitPf
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] {T : Module.End ℂ M} {μ : ℂ} {f : M}
    (h : T f = μ • f) : f ∈ T.maxGenEigenspace μ :=
  Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 h)
end CompanionTheory.RgExh.Hk.UnitPf
