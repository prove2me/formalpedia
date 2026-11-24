-- Prove2me | solution 1 for P2M_h_exists__3f6441b4d557
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:35.442356+00:00
-- url     : https://prove2.me/submissions/dab55630-0589-417d-bc15-ac0b169d441d

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
variable [IsUnramifiedAtInfinitePlaces k K]
include hp
theorem _root_.solution : ∃ (h : ℕ) (ν : (𝓞 k)ˣ), IsPrimitiveRoot (ν : k) (p ^ h) ∧
    ∀ (ε : (𝓞 k)ˣ) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε := by
  have : NeZero p := ⟨hp.ne_zero⟩
  classical
  let H := Subgroup.toAddSubgroup.symm
    (Submodule.torsion' ℤ (Additive (𝓞 k)ˣ) (Submonoid.powers p)).toAddSubgroup
  have : H ≤ NumberField.Units.torsion k := by
    rintro x ⟨⟨_, i, rfl⟩, hnx : x ^ (p ^ i) = 1⟩
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ i, Fin.pos', hnx⟩
  obtain ⟨ν, hν⟩ := Subgroup.isCyclic_of_le this
  obtain ⟨⟨_, i, rfl⟩, hiν : (ν : (𝓞 k)ˣ) ^ (p ^ i) = 1⟩ := ν.prop
  obtain ⟨j, _, hj'⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hiν)
  refine ⟨j, ν, IsPrimitiveRoot.coe_coe_iff.mpr (hj' ▸ IsPrimitiveRoot.orderOf ν.1),
    fun ε n hn ↦ ?_⟩
  let _ : Fintype (Units.torsion k) := Fintype.ofFinite _
  have : Fintype H := Set.fintypeSubset (NumberField.Units.torsion k) this
  obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.mpr (hν ⟨ε, ⟨_, n, rfl⟩, hn⟩)
  exact ⟨i, congr_arg Subtype.val hi⟩
