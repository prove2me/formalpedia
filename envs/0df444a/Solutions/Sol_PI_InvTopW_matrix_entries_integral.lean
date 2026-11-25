-- Prove2me | solution 1 for PI.InvTopW.matrix_entries_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:34.14136+00:00
-- url     : https://prove2.me/submissions/cfc8bcb5-3ef7-48da-b60b-90f99031e04a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.InvTopW
theorem _root_.solution (I : AutInst) (c g : ℕ)
    (h1 : ∀ y ∈ I.Lf, ∀ i, (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E)
    (h2 : ∀ u : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, u i ∈ Formalism.MainNotions.S.IntAf I.F I.E) →
      (fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * u i) ∈ I.Lf)
    (X : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hX : ∀ i j, InNInt I (g * c * c) (X i j)) (y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, X *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z := by
  choose w hw hXw using hX
  refine ⟨fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * ∑ k, w i k * ((c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y k), h2 _ (fun i => ?_), ?_⟩
  · exact sum_mem fun k _ => mul_mem (hw i k) (h1 y hy k)
  · funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hXw]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
end PI.InvTopW
