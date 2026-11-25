-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasLen_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:51:48.427706+00:00
-- url     : https://prove2.me/submissions/147566a4-561b-425b-9104-5fb537bf38e1

import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Theorems.Thm_ReciprocityTheory_PGsh_Up_prod_dvd_of_iso

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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x y : NNReal}
    (hx : HasLen v R M x) (hy : HasLen v R M y) : x = y := by
  obtain ⟨m, c, ⟨φ⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨ψ⟩, rfl⟩ := hy
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (algebraMap R C) h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have hlt : ∀ z : R, ¬ IsUnit z → v (algebraMap R C z) < 1 := fun z hz =>
    lt_of_le_of_ne (hv.map_le_one z) fun h1 => hz (hv.isUnit_iff_valuation_eq_one.mpr h1)
  haveI : IsLocalRing R := by
    refine IsLocalRing.of_nonunits_add fun a b ha hb hab => ?_
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hab
    rw [map_add] at h1
    have h2 := (v.map_add _ _).trans_lt (max_lt (hlt a ha) (hlt b hb))
    rw [h1] at h2
    exact lt_irrefl _ h2
  have h1 := prod_dvd_of_iso c d (φ.symm.trans ψ)
  have h2 := prod_dvd_of_iso d c (ψ.symm.trans φ)
  rw [Ideal.mem_span_singleton, hv.dvd_iff_le] at h1 h2
  simp only [map_prod] at h1 h2
  exact le_antisymm h1 h2
end ReciprocityTheory.PGsh.Up
