-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.lhol_Fint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:56.084523+00:00
-- url     : https://prove2.me/submissions/7d3bd98d-aec7-4a77-97bd-c88fb4bba07c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_emb_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_FD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_int_FD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_hasFDerivAt_Fint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
variable [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) (X : Matrix (Fin n) (Fin n) ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Ps1.Uset ε) : Lhol X (Fint T g) z = Fint T (DH X g) z := by
  have h2 : fderiv ℂ (fun x : 𝕄f => Fint T g x) z = cK T • ∫ k, FD T g z k ∂(muK ε) :=
    (hasFDerivAt_Fint T hg hz).fderiv
  have h4 : fderiv ℂ (fun x : 𝕄f => Fint T g x) z (X * z) = cK T • ∫ k, FD T g z k (X * z) ∂(muK ε) := by
    rw [h2]
    exact congrArg (cK T • ·) (ContinuousLinearMap.integral_apply (int_FD T hg hz) (show 𝕄f from X * z))
  have h5 : ∀ k, FD T g z k (X * z) = DH X g (emb z k) • Pk T k := fun k => by
    rw [FD_apply T hg k (emb_mem hz k)]; rfl
  unfold Lhol
  refine h4.trans ?_
  unfold Fint
  simp only [h5]
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
