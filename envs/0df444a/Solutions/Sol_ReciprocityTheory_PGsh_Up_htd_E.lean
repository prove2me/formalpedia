-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.htd_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:31.822382+00:00
-- url     : https://prove2.me/submissions/f5f79fa0-8017-4938-8fee-dc2a4884b7c6

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (H : HodgeTateDatum p g v R O σ cp) :
    (H.E.map (algebraMap ℤ_[p] R))ᵀ = -H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, H.E.map (algebraMap ℤ_[p] R) i i = 0) ∧ IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  · intro i
    simp [Matrix.map_apply, H.E_alternating.2 i]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact H.isUnit_det_E.map _
end ReciprocityTheory.PGsh.Up
