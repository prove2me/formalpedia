-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.detD_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:56.140115+00:00
-- url     : https://prove2.me/submissions/1cc57e0f-5748-4a57-b0cc-94a5896416d9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CK_isymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ → ℂ) (hG : AnalyticAt ℂ G 0) :
    detD G = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
  have hgen : ∀ (m : ℕ) (h : m = N) (e : Fin m ≃ Fin N) (σ : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ m G 0 (fun i => Matrix.single (e i) (σ (e i)) (1 : ℂ)) =
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
    intro m h e σ
    subst h
    exact isymm G 0 hG m (fun k => Matrix.single k (σ k) 1) e
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hgen _ (Fintype.card_fin N) _ σ]
end PositivityTheory.Rg.Sw.LVs.CK
