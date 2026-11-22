-- Prove2me | solution 1 for OrderIdeal.gaugeNorm_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:59.39274+00:00
-- url     : https://prove2.me/submissions/4fe00727-3512-4baf-91f0-3916bd9f0937

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)
namespace OrderIdeal
theorem _root_.solution {e u : X} (he : 0 ≤ e) (heu : e ≤ u)
    {x : X} (hx : x ∈ principal e) : gaugeNorm u x ≤ gaugeNorm e x := by
  -- S_e ⊆ S_u (since |e| = e ≤ u = |u|, so c • |e| ≤ c • |u|)
  apply le_csInf hx
  intro c ⟨hc, hle⟩
  apply csInf_le (gaugeNorm_bddBelow u x)
  exact ⟨hc, le_trans hle (smul_le_smul_of_nonneg_left
    (by rwa [abs_of_nonneg he, abs_of_nonneg (le_trans he heu)]) hc)⟩
end OrderIdeal
