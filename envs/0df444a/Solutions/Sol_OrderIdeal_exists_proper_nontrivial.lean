-- Prove2me | solution 1 for OrderIdeal.exists_proper_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:28:34.933094+00:00
-- url     : https://prove2.me/submissions/4d123816-0303-4326-84d1-af7dbb5c7f8f

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_OrderIdeal_self_mem_principal
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_abs_eq_zero_iff_zero
public import Theorems.Thm_exists_pair_ne_zero_isVLDisjoint
public import Theorems.Thm_nonneg_smul_inf
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top


section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderIdeal
variable (J : OrderIdeal X)
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)
private lemma eq_zero_of_mem_principal_disjoint {p q : X} (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hpq : p ⊓ q = 0) (hq_in : q ∈ principal p) : q = 0 := by
  obtain ⟨c, hc, hle⟩ := hq_in
  rw [abs_of_nonneg hq, abs_of_nonneg hp] at hle
  rcases le_or_gt 1 c with h1 | h1
  · have hq_le_cq : q ≤ c • q := by
      calc q = (1 : ℝ) • q := (one_smul ℝ q).symm
        _ ≤ c • q := smul_le_smul_of_nonneg_right h1 hq
    have hboth : q ≤ c • p ⊓ c • q := le_inf hle hq_le_cq
    rw [← nonneg_smul_inf p q c (le_trans zero_le_one h1), hpq, smul_zero] at hboth
    exact le_antisymm hboth hq
  · have hcp_le_p : c • p ≤ p := by
      calc c • p ≤ (1 : ℝ) • p := smul_le_smul_of_nonneg_right h1.le hp
        _ = p := one_smul ℝ p
    have hq_le_p : q ≤ p := le_trans hle hcp_le_p
    have : p ⊓ q = q := inf_eq_right.mpr hq_le_p
    rwa [this] at hpq
section Closure
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
end Closure
end OrderIdeal
namespace ClosedOrderIdeal
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
end ClosedOrderIdeal
end
end

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
theorem _root_.solution [IsVLArchimedean X] (h : 1 < Module.rank ℝ X) :
    ∃ J : OrderIdeal X, J ≠ ⊥ ∧ J ≠ ⊤ := by
  obtain ⟨u, v, hu, hv, huv⟩ := exists_pair_ne_zero_isVLDisjoint h
  have habs_u_nn : 0 ≤ |u| := abs_nonneg u
  have habs_v_nn : 0 ≤ |v| := abs_nonneg v
  have habs_u_nz : |u| ≠ 0 := fun h => hu ((abs_eq_zero_iff_zero u).mp h)
  have habs_v_nz : |v| ≠ 0 := fun h => hv ((abs_eq_zero_iff_zero v).mp h)
  refine ⟨principal (|u|), ?_, ?_⟩
  · intro heq
    have : (|u| : X) ∈ (⊥ : OrderIdeal X) := heq ▸ self_mem_principal |u|
    exact habs_u_nz (mem_bot.mp this)
  · intro heq
    have hv_mem : (|v| : X) ∈ principal (|u|) := heq ▸ mem_top
    exact habs_v_nz
      (eq_zero_of_mem_principal_disjoint habs_u_nn habs_v_nn huv hv_mem)
end OrderIdeal
