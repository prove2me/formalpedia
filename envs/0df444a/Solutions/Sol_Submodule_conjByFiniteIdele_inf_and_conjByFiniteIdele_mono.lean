-- Prove2me | solution 1 for Submodule.conjByFiniteIdele_inf_and_conjByFiniteIdele_mono
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0ce74c6b-607a-5d24-a13a-3191b0a5dddc

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_conjByFiniteIdele_inf_and_conjByFiniteIdele_mono

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

namespace ConjInf

open Submodule

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem finiteAdeleBox_mono {Λ₁ Λ₂ : Submodule ℤ D} (h : Λ₁ ≤ Λ₂) :
    finiteAdeleBox Λ₁ ≤ finiteAdeleBox Λ₂ :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem conjByFiniteIdele_mono {Λ₁ Λ₂ : Submodule ℤ D} (h : Λ₁ ≤ Λ₂)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    conjByFiniteIdele Λ₁ g ≤ conjByFiniteIdele Λ₂ g := by
  intro z hz
  rw [mem_conjByFiniteIdele_iff] at hz ⊢
  exact AddSubgroup.map_mono (finiteAdeleBox_mono h) hz

theorem exists_ne_zero_nsmul_mem (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hsp : Submodule.span ℚ (Λ : Set D) = ⊤) (z : D) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : ℚ) • z ∈ Λ := by
  obtain ⟨N, hN, hmem⟩ :=
    Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox Λ hsp (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))
  refine ⟨N, hN, ?_⟩
  rw [← Submodule.ofFiniteIdele_one Λ hfg hsp, Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  refine ⟨(N : ℚ) • (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)), hmem, ?_⟩
  simp only [AddMonoidHom.coe_mulLeft, Units.val_one, one_mul, TensorProduct.smul_tmul']

omit [Algebra ℚ D] in
theorem fg_inf (Λ Λ' : Submodule ℤ D) (hfg : Λ.FG) : (Λ ⊓ Λ').FG :=
  haveI : IsNoetherian ℤ ↥Λ := isNoetherian_of_fg_of_noetherian Λ hfg
  isNoetherian_submodule.mp inferInstance _ inf_le_left

theorem span_inf_eq_top (Λ Λ' : Submodule ℤ D) (hfg : Λ.FG) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤)
    (hfg' : Λ'.FG) (hsp' : Submodule.span ℚ (Λ' : Set D) = ⊤) :
    Submodule.span ℚ ((Λ ⊓ Λ' : Submodule ℤ D) : Set D) = ⊤ := by
  rw [eq_top_iff']
  intro z
  obtain ⟨N, hN, hz⟩ := exists_ne_zero_nsmul_mem Λ hfg hsp z
  obtain ⟨N', hN', hz'⟩ := exists_ne_zero_nsmul_mem Λ' hfg' hsp' ((N : ℚ) • z)
  have hmem : ((N' * N : ℕ) : ℚ) • z ∈ (Λ ⊓ Λ' : Submodule ℤ D) := by
    rw [Nat.cast_mul, mul_smul]
    refine ⟨?_, hz'⟩
    rw [Nat.cast_smul_eq_nsmul]
    exact Submodule.smul_of_tower_mem _ N' hz
  have hne : ((N' * N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hN' hN
  have : z = ((N' * N : ℕ) : ℚ)⁻¹ • (((N' * N : ℕ) : ℚ) • z) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem conjByFiniteIdele_inf (Λ Λ' : Submodule ℤ D) (hfg : Λ.FG) (hsp : Submodule.span ℚ (Λ : Set D) = ⊤)
    (hfg' : Λ'.FG) (hsp' : Submodule.span ℚ (Λ' : Set D) = ⊤)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    conjByFiniteIdele (Λ ⊓ Λ') g = conjByFiniteIdele Λ g ⊓ conjByFiniteIdele Λ' g := by
  refine le_antisymm (le_inf (conjByFiniteIdele_mono inf_le_left g) (conjByFiniteIdele_mono inf_le_right g)) ?_
  intro z hz
  obtain ⟨hz₁, hz₂⟩ := Submodule.mem_inf.mp hz
  rw [mem_conjByFiniteIdele_iff, AddSubgroup.mem_map] at hz₁ hz₂ ⊢
  obtain ⟨x, hx, hxz⟩ := hz₁
  obtain ⟨x', hx', hx'z⟩ := hz₂

  have hxx' : x = x' := by
    have h := hxz.trans hx'z.symm
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight] at h
    exact (Units.mul_right_inj g).mp ((Units.mul_left_inj g⁻¹).mp h)
  subst hxx'
  refine ⟨x, ?_, hxz⟩
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ (fg_inf Λ Λ' hfg)
    (span_inf_eq_top Λ Λ' hfg hsp hfg' hsp')]
  intro v
  rw [Submodule.localBox_inf Λ Λ' hfg hsp hfg' hsp' v]
  exact ⟨(Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hsp x).mp hx v,
    (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ' hfg' hsp' x).mp hx' v⟩

end ConjInf

theorem solution
    {a b : ℚ} (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hΛ' : IsOrder Λ')
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.conjByFiniteIdele (Λ ⊓ Λ') g = Submodule.conjByFiniteIdele Λ g ⊓ Submodule.conjByFiniteIdele Λ' g ∧
    (Λ ≤ Λ' → Submodule.conjByFiniteIdele Λ g ≤ Submodule.conjByFiniteIdele Λ' g) := by
  exact ⟨ConjInf.conjByFiniteIdele_inf Λ Λ' hΛ.fg hΛ.spanTop hΛ'.fg hΛ'.spanTop g,
    fun h => ConjInf.conjByFiniteIdele_mono h g⟩

#print axioms solution

end S_Submodule_conjByFiniteIdele_inf_and_conjByFiniteIdele_mono
end P2MW
export P2MW.S_Submodule_conjByFiniteIdele_inf_and_conjByFiniteIdele_mono (solution)
