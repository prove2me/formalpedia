-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.two_D_sq_khw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:31.983866+00:00
-- url     : https://prove2.me/submissions/4527f75a-fc43-4b4d-852f-e14f7afb3a5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_khwVec_compact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_diagE_compact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_real_identity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_two_D_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) {δ : Fin n → ℝ} {v : W}
    (hv : IsKHWVec ε (diagE ε E cp cm) (δ + rhoHol ε) v) {c : ℂ} (hc : casimir E v = c • v) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) v =
      (((nsq (δ + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - c) • v := by
  have hK := casimirK_khwVec_compact ε (diagE_compact hE hC hEC ε) hv
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a v =
      ((dot (rhoHol ε) (δ + rhoHol ε) : ℝ) : ℂ) • v := by
    simp only [hv.1, smul_smul, ← sum_smul]
    congr 1
    unfold dot
    push_cast
    rfl
  rw [← LinearMap.smul_apply, two_D_sq hE hC hEC ε]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hc, hK, hs]
  rw [← khw_real_identity ε δ]
  simp only [smul_smul, sub_smul]
  push_cast
  simp only [sub_smul, mul_smul]
  abel
end ReciprocityTheory.ChartRestriction.DS
