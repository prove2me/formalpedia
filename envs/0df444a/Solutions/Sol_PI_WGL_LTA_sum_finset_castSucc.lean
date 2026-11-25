-- Prove2me | solution 1 for PI.WGL.LTA.sum_finset_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:00.429471+00:00
-- url     : https://prove2.me/submissions/54c0fa93-5689-4c1e-996a-82753dd08735

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL.LTA
theorem _root_.solution {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Finset (Fin (m + 1)) → M)
    (hf : ∀ S, Fin.last m ∈ S → f S = 0) :
    ∑ S : Finset (Fin (m + 1)), f S = ∑ S : Finset (Fin m), f (S.map Fin.castSuccEmb) := by
  classical
  have hm : ∑ S : Finset (Fin m), f (S.map Fin.castSuccEmb) =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin m))).map (Finset.mapEmbedding Fin.castSuccEmb).toEmbedding, f S := by
    rw [Finset.sum_map]
    rfl
  rw [hm]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro S _ hS
  apply hf
  by_contra hl
  apply hS
  rw [Finset.mem_map]
  refine ⟨S.preimage Fin.castSucc (Fin.castSucc_injective m).injOn, Finset.mem_univ _, ?_⟩
  ext x
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.mem_map, Finset.mem_preimage,
    Fin.coe_castSuccEmb]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    have hxl : x ≠ Fin.last m := fun h => hl (h ▸ hx)
    exact ⟨x.castPred hxl, by simpa using hx, by simp⟩
end PI.WGL.LTA
