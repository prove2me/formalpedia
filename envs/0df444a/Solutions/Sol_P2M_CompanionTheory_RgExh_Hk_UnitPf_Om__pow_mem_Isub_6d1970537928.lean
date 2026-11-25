-- Prove2me | solution 1 for P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__pow_mem_Isub_6d1970537928
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:27:07.334786+00:00
-- url     : https://prove2.me/submissions/3c6d1712-aa46-43ec-8331-034fe66f6353

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule
import Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_UnitPf_Om__mem_Isub_9bd49289c361

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
theorem _root_.solution (k : ℕ) {H} (h : H ∈ Isub X) : (Om' X ^ k) H ∈ Isub X := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact Om'_mem_Isub ih
end CompanionTheory.RgExh.Hk.UnitPf
