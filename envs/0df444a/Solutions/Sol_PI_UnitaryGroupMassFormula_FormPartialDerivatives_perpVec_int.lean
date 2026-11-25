-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FormPartialDerivatives.perpVec_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:04.423734+00:00
-- url     : https://prove2.me/submissions/f7c3d8af-ab4e-4a7a-9ac0-0830faf13896

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_PerpVecPerpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_PerpendicularDeterminants_PerpVecOfPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FormPartialDerivatives
open ReciprocityTheory.ChartRestriction.G.TB
namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives
theorem _root_.solution (R : Type) [CommRing R] (O : Subring R) (V : Type) [AddCommGroup V] [Module R V]
    (p : ℕ) (h : V →ₗ[R] (V → R)) (L : Submodule O V)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ O) (e e' : Fin p → V) (g : V)
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : perpVec h e e' g ∈ L := by
  let MO : Matrix (Fin p) (Fin p) O := Matrix.of fun a' a => ⟨h (e' a') (e a), hL _ (he' a') _ (he a)⟩
  have hMap : hMat h e e' = O.subtype.mapMatrix MO := by
    ext a' a
    rfl
  have hdet : (hMat h e e').det ∈ O := by
    rw [hMap, ← RingHom.map_det]
    exact (MO.det).2
  have hadj : ∀ a a', (hMat h e e').adjugate a a' ∈ O := by
    intro a a'
    rw [hMap, ← RingHom.map_adjugate]
    exact (MO.adjugate a a').2
  have hs : ∀ r ∈ O, ∀ v ∈ L, r • v ∈ L := by
    intro r hr v hv
    exact L.smul_mem (⟨r, hr⟩ : O) hv
  unfold perpVec
  refine L.sub_mem (hs _ hdet _ hg) (L.sum_mem fun a _ => L.sum_mem fun a' _ => ?_)
  exact hs _ (O.mul_mem (hadj a a') (hL _ hg _ (he a))) _ (he' a')
end PI.UnitaryGroupMassFormula.FormPartialDerivatives
