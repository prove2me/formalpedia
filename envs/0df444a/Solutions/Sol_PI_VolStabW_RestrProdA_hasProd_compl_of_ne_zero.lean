-- Prove2me | solution 1 for PI.VolStabW.RestrProdA.hasProd_compl_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:26.961416+00:00
-- url     : https://prove2.me/submissions/efcde20d-340d-4f2c-8ff5-62f8dd3f5df6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.RestrProdA
theorem _root_.solution {β : Type} {f : β → ℂ} {p : ℂ} (h : HasProd f p) (S : Finset β)
    (hS : ∀ b ∈ S, f b ≠ 0) :
    HasProd ({b | b ∉ S}.mulIndicator f) (p * ∏ b ∈ S, (f b)⁻¹) := by
  classical
  have h2 : HasProd (fun b => if b ∈ S then (f b)⁻¹ else 1)
      (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1)) := hasProd_prod_of_ne_finset_one fun b hb => if_neg hb
  have e : ∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1) = ∏ b ∈ S, (f b)⁻¹ :=
    Finset.prod_congr rfl fun b hb => if_pos hb
  rw [e] at h2
  convert h.mul h2 using 1
  funext b
  by_cases hb : b ∈ S
  · simp [Set.mulIndicator, hb, hS b hb]
  · simp [Set.mulIndicator, hb]
end PI.VolStabW.RestrProdA
