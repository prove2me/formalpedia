-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.PullbackHopfOrder.isLat_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:46.353622+00:00
-- url     : https://prove2.me/submissions/139f81b7-be54-452e-9d85-c34f93812ccc

import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_MapTensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsMatOfEquiv

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.PullbackHopfOrder
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder
theorem _root_.solution {X K : Type} [Fintype X] [DecidableEq X] {_ : Fintype K} {_ : DecidableEq K}
    (e : X ≃ K) {M : Submodule R (K → C)} (hM : IsLat R M) :
    IsLat R (M.map (LinearMap.funLeft R C e)) := by
  obtain ⟨B, hB, rfl⟩ := hM
  refine ⟨B.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Submodule.map_span, ← Set.range_comp]
  have h1 : (fun j x => (B.submatrix e e) x j) =
      (⇑(LinearMap.funLeft R C e) ∘ fun j x => B x j) ∘ e := by
    funext j x
    rfl
  rw [h1, e.surjective.range_comp]
end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
