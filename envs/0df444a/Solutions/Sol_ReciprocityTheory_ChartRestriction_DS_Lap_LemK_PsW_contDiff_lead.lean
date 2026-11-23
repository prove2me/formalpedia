-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.contDiff_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:51.710174+00:00
-- url     : https://prove2.me/submissions/d8b5c762-c719-4f01-81d1-b741b35da9eb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
private theorem contDiff_det_k_type {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Fin m → Fin m → ℂ => Matrix.det z) := by
  have h : (fun z : Fin m → Fin m → ℂ => Matrix.det z) =
      fun z => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z (σ i) i := by
    funext z
    exact Matrix.det_apply' _
  rw [h]
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => contDiff_pi.1 (contDiff_pi.1 contDiff_id (σ i)) i)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
end PsW
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution (i : ℕ) : ContDiff ℂ ω (fun z : 𝕄 => lead i z) := by
  by_cases h : i ≤ n
  · have e : (fun z : 𝕄 => lead i z) = fun z : 𝕄 =>
        Matrix.det (fun a b => z (Fin.castLE h a) (Fin.castLE h b) : Fin i → Fin i → ℂ) := by
      funext z
      simp only [lead, dif_pos h]
      rfl
    rw [e]
    exact contDiff_det_k_type.comp (contDiff_pi.2 fun a => contDiff_pi.2 fun b =>
      contDiff_pi.1 (contDiff_pi.1 contDiff_id (Fin.castLE h a)) (Fin.castLE h b))
  · have e : (fun z : 𝕄 => lead i z) = fun _ => 0 := by
      funext z
      simp only [lead, dif_neg h]
    rw [e]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
