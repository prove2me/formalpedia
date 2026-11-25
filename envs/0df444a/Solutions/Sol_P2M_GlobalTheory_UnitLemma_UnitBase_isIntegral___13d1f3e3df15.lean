-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_UnitBase_isIntegral___13d1f3e3df15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:34:14.391163+00:00
-- url     : https://prove2.me/submissions/de637e61-fb37-4d57-9cf6-e54fefe1c865

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution {K : UQ} (B : InvAlg K) {y : B.A} (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (cO K), hp.map _, ?_⟩
  have hc : (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) = (algebraMap K.O B.A).comp (cO K) := by
    ext x; exact σ_algebraMap_O B x
  have := congrArg (B.σ : B.A →+* B.A) hpy
  rw [map_zero, Polynomial.hom_eval₂, hc] at this
  rw [Polynomial.eval₂_map]; exact this
end GlobalTheory.UnitLemma.UnitBase
