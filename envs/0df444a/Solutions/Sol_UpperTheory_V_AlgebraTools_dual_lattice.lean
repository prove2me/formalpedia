-- Prove2me | solution 1 for UpperTheory.V.AlgebraTools.dual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:16.813922+00:00
-- url     : https://prove2.me/submissions/ab782254-e9ec-4bd6-881d-abc6b5277c31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualLatticeDenominator
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_DualLattice
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsSmulMemOfIsLattice__dual_lattice_denom_0a14bd9a2b01

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Matrix IsLocalRing TensorProduct
private theorem UpperTheory.V.AlgebraTools.dual_lattice_denom {A : Type} [CommRing A] [IsDomain A]
    {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V]
    [Module A V] [IsScalarTower A F V] (Y : Submodule A V) (hY : Submodule.IsLattice F Y)
    (z : V) : ∃ a : A, a ≠ 0 ∧ a • z ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom Y hY z
private theorem UpperTheory.V.AlgebraTools.dual_lattice_pow {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (a : A) (ha : a ≠ 0) :
    ∃ s : ℕ, maximalIdeal A ^ s ≤ Ideal.span {a} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact (Units.isUnit u).mul_left_dvd.mpr dvd_rfl
end

set_option autoImplicit false
open Polynomial Matrix IsLocalRing TensorProduct
namespace UpperTheory.V.AlgebraTools
theorem _root_.solution :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (Bf : LinearMap.BilinForm F V), Bf.IsSymm → Bf.Nondegenerate → ∀ Y : Submodule A V, Submodule.IsLattice F Y → Submodule.IsLattice F (Bf.dualSubmodule Y) ∧ Bf.dualSubmodule (Bf.dualSubmodule Y) = Y ∧ ∀ Z : Submodule A V, Submodule.IsLattice F Z → ∃ s : ℕ, maximalIdeal A ^ s • Z ≤ Y := by
  intro A _ _ _ F V _ _ _ _ _ _ _ _ Bf hs hn Y hY
  classical
  haveI : Module.Free A Y := Submodule.IsLattice.free F Y
  haveI : Module.Finite A Y := Submodule.IsLattice.finite F Y
  let b0 := Module.Free.chooseBasis A Y
  let b := b0.extendOfIsLattice F
  have hb : Submodule.span A (Set.range b) = Y := by
    have : (b : _ → V) = Y.subtype ∘ b0 := by
      funext i; simp [b]
    rw [this, Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis Bf hn b]
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [Submodule.span_span_of_tower, Module.Basis.span_eq]
  · rw [← hb]
    exact LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis Bf hn hs b
  · intro Z hZ
    have hfg := hZ.fg
    clear hZ
    induction Z, hfg using Submodule.fg_induction with
    | singleton x =>
      obtain ⟨a, ha, hax⟩ := UpperTheory.V.AlgebraTools.dual_lattice_denom Y hY x
      obtain ⟨s, hs⟩ := UpperTheory.V.AlgebraTools.dual_lattice_pow a ha
      refine ⟨s, (Submodule.smul_mono_left hs).trans ?_⟩
      refine Submodule.smul_le.mpr fun r hr y hy => ?_
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [mul_smul, smul_comm a c]
      exact Y.smul_mem _ (Y.smul_mem _ hax)
    | sup M N _ _ hM hN =>
      obtain ⟨s, hs⟩ := hM
      obtain ⟨t, ht⟩ := hN
      refine ⟨s + t, ?_⟩
      rw [Submodule.smul_sup]
      refine sup_le ?_ ?_
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right s t))).trans hs
      · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left t s))).trans ht
end UpperTheory.V.AlgebraTools
