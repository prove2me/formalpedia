-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.lWord_psM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:24.014707+00:00
-- url     : https://prove2.me/submissions/4ba0ffd7-9ad5-46b9-8d63-78b68ce77244

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_integrable_G__3d0a1905c680
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_hasFDerivAt_intG
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_G__apply_f1b4125cf86b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_intG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∀ (D : List MM) (z : MM), z ∈ Ps1.Uset ε →
      lWord D (psM T μ) z = cc T • ∫ k, G T μ D z k ∂(muK ε)
  | [], _, _ => rfl
  | Z :: D, z, hz => by
    have hE : (fun x : 𝕄 => lWord D (psM T μ) x) =ᶠ[𝓝 z]
        fun x => cc T • ∫ k, G T μ D x k ∂(muK ε) :=
      Filter.eventually_of_mem (Ps1.isOpen_Uset.mem_nhds hz) fun x hx => solution T μ D x hx
    have hd := (hasFDerivAt_intG T μ D hz).const_smul (cc T)
    show fderiv ℂ (fun x : 𝕄 => lWord D (psM T μ) x) z (Z * z) = _
    have h1 : fderiv ℂ (fun x : 𝕄 => lWord D (psM T μ) x) z = cc T • ∫ k, G' T μ D z k ∂(muK ε) :=
      hE.fderiv_eq.trans hd.fderiv
    refine (congrArg (fun L : 𝕄 →L[ℂ] (T.V →L[ℂ] T.V) => L (Z * z)) h1).trans ?_
    refine ((ContinuousLinearMap.smul_apply _ _ _).trans (congrArg (fun v => cc T • v)
      (ContinuousLinearMap.integral_apply (integrable_G' T μ D hz) (Z * z)))).trans ?_
    exact congrArg (fun v => cc T • v)
      (integral_congr_ae (Filter.Eventually.of_forall fun k => G'_apply T μ D hz k Z))
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
