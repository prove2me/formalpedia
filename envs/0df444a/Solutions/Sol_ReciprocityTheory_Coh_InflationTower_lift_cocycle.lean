-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.lift_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:53.767896+00:00
-- url     : https://prove2.me/submissions/38590969-41e1-4cd6-92de-ee63f5c66d25

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_H_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution {A B : Cx R} (φ : Hom A B) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ)
    (z : A.Z n) (w : B.Z n) (h : φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk w) :
    ∃ z' : A.Z n, (Submodule.Quotient.mk z' : A.H n) = Submodule.Quotient.mk z ∧ φ.Z n z' = w := by
  rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap] at h
  cases n with
  | zero =>
    refine ⟨z, rfl, ?_⟩
    have h' : ((φ.Z 0 z - w : B.Z 0) : B.X 0) = 0 := h
    exact sub_eq_zero.mp (Subtype.ext h')
  | succ k =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨c', rfl⟩ := hs k c
    have hdc : A.d (k+1) (A.d k c') = 0 := A.dd k c'
    refine ⟨z - ⟨A.d k c', hdc⟩, ?_, ?_⟩
    · rw [Submodule.Quotient.eq, Submodule.mem_comap]
      refine ⟨-c', ?_⟩
      show A.d k (-c') = (z : A.X (k+1)) - A.d k c' - z
      rw [map_neg]; abel
    · apply Subtype.ext
      have hc' : B.d k (φ.f k c') = φ.f (k+1) z - w := hc
      show φ.f (k+1) ((z : A.X (k+1)) - A.d k c') = w
      rw [map_sub, φ.comm, hc']; abel
end ReciprocityTheory.Coh.InflationTower
