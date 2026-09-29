-- Prove2me | solution 1 for ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c86ede8e-876a-5378-b98c-564c7739d45b

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn

set_option autoImplicit false

universe u

open IsLocalRing Polynomial

noncomputable section

namespace ValuationSubring
p2m_export "ValuationSubring" "inertiaSubgroup toSubring ext nonunits mem_nonunits_iff isLocalRing add_mem decompositionSubgroup inclusion inertiaSubgroupIn henselianLocalRing_of_isAlgClosed"
namespace HensOI
p2m_open "ValuationSubring"

theorem isUnit_of_sub_mem {R : Type u} [CommRing R] [IsLocalRing R] {x y : R} (hx : IsUnit x)
    (hxy : y - x ∈ maximalIdeal R) : IsUnit y := by
  by_contra hy
  have hy' : y ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hy
  have hx' : x ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hy' hxy
    rwa [sub_sub_cancel] at this
  exact (mem_maximalIdeal _).mp hx' hx

theorem eval_sub_eval_mem {R : Type u} [CommRing R] [IsLocalRing R] (g : R[X]) {x y : R}
    (hxy : x - y ∈ maximalIdeal R) : g.eval x - g.eval y ∈ maximalIdeal R := by
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub x y g
  rw [hc]
  exact Ideal.mul_mem_right _ _ hxy

theorem root_unique {R : Type u} [CommRing R] [IsLocalRing R] (f : R[X]) (a₀ : R)
    (hu : IsUnit (f.derivative.eval a₀)) {α β : R} (hα : f.IsRoot α) (hα₀ : α - a₀ ∈ maximalIdeal R)
    (hβ : f.IsRoot β) (hβ₀ : β - a₀ ∈ maximalIdeal R) : β = α := by

  set g := f /ₘ (X - C α) with hg
  have hfac : (X - C α) * g = f := mul_divByMonic_eq_iff_isRoot.mpr hα
  have hder : f.derivative.eval α = g.eval α := by
    conv_lhs => rw [← hfac]
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  have hgα : IsUnit (g.eval α) := by
    rw [← hder]
    exact isUnit_of_sub_mem hu (eval_sub_eval_mem f.derivative hα₀)
  have hβα : β - α ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hβ₀ hα₀
    rwa [sub_sub_sub_cancel_right] at this
  have hgβ : IsUnit (g.eval β) := isUnit_of_sub_mem hgα (eval_sub_eval_mem g hβα)

  have h0 : (β - α) * g.eval β = 0 := by
    have := hβ.eq_zero
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at this
    exact this
  have : β - α = 0 := (hgβ.mul_left_eq_zero).mp h0
  exact sub_eq_zero.mp this

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) (I : Subgroup (L ≃ₐ[K] L))

abbrev OI : Subring L := A.toSubring ⊓ (IntermediateField.fixedField I).toSubring

def incl : ↥(OI (K := K) A I) →+* ↥A := Subring.inclusion inf_le_left

theorem incl_coe (o : ↥(OI (K := K) A I)) : ((incl (K := K) A I o : ↥A) : L) = (o : L) := rfl

theorem incl_injective : Function.Injective (incl (K := K) A I) := fun x y h =>
  Subtype.ext (by rw [← incl_coe (K := K) A I x, ← incl_coe (K := K) A I y, h])

theorem mem_fixed (o : ↥(OI (K := K) A I)) : (o : L) ∈ IntermediateField.fixedField I := (Subring.mem_inf.mp o.2).2

theorem isUnit_iff (o : ↥(OI (K := K) A I)) : IsUnit o ↔ IsUnit (incl (K := K) A I o) := by
  refine ⟨fun h => h.map _, fun h => ?_⟩
  have ho' : (o : L) ≠ 0 := by
    intro h0
    apply h.ne_zero
    exact Subtype.ext h0
  obtain ⟨w, hw⟩ := h.exists_left_inv
  have h1 : ((w : ↥A) : L) * (o : L) = 1 := by
    have := congrArg (fun a : ↥A => (a : L)) hw
    simpa [incl_coe] using this
  have hwL : ((w : ↥A) : L) = ((o : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hinvA : (o : L)⁻¹ ∈ A := by rw [← hwL]; exact w.2
  have hinvF : (o : L)⁻¹ ∈ IntermediateField.fixedField I := inv_mem (mem_fixed (K := K) A I o)
  have hinvO : (o : L)⁻¹ ∈ OI (K := K) A I := Subring.mem_inf.mpr ⟨hinvA, hinvF⟩
  refine IsUnit.of_mul_eq_one ⟨_, hinvO⟩ ?_
  apply Subtype.ext
  show (o : L) * (o : L)⁻¹ = 1
  exact mul_inv_cancel₀ ho'

scoped instance isLocalRing : IsLocalRing ↥(OI (K := K) A I) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [_root_.mem_nonunits_iff, isUnit_iff, ← _root_.mem_nonunits_iff, ← mem_maximalIdeal] at ha hb ⊢
  rw [map_add]
  exact Ideal.add_mem _ ha hb

theorem mem_maximalIdeal_iff (o : ↥(OI (K := K) A I)) :
    o ∈ maximalIdeal ↥(OI (K := K) A I) ↔ incl (K := K) A I o ∈ maximalIdeal ↥A := by
  rw [mem_maximalIdeal, mem_maximalIdeal, _root_.mem_nonunits_iff, _root_.mem_nonunits_iff, isUnit_iff]

theorem exists_decomp_of_mem {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ τ : ↥(A.decompositionSubgroup K), τ ∈ A.inertiaSubgroup K ∧ (τ : L ≃ₐ[K] L) = σ := by
  obtain ⟨τ, hτ, hτσ⟩ := Subgroup.mem_map.mp hσ
  exact ⟨τ, hτ, hτσ⟩

theorem smul_sub_mem (τ : ↥(A.decompositionSubgroup K)) (hτ : τ ∈ A.inertiaSubgroup K) (a : ↥A) :
    τ • a - a ∈ maximalIdeal ↥A := by
  have h1 : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup K)) (ResidueField ↥A) τ = 1 :=
    (MonoidHom.mem_ker).mp hτ
  have h2 : τ • residue ↥A a = residue ↥A a := by
    have := congrArg (fun e : RingAut (ResidueField ↥A) => e (residue ↥A a)) h1
    simpa [MulSemiringAction.toRingAut_apply] using this
  rw [← ResidueField.residue_smul] at h2
  exact Ideal.Quotient.eq.mp h2

theorem coe_smul (τ : ↥(A.decompositionSubgroup K)) (a : ↥A) : ((τ • a : ↥A) : L) = (τ : L ≃ₐ[K] L) (a : L) := rfl

theorem smul_incl (τ : ↥(A.decompositionSubgroup K)) (hτI : (τ : L ≃ₐ[K] L) ∈ I) (o : ↥(OI (K := K) A I)) :
    τ • incl (K := K) A I o = incl (K := K) A I o := by
  apply Subtype.ext
  rw [coe_smul, incl_coe]
  exact (IntermediateField.mem_fixedField_iff _ _).mp (mem_fixed (K := K) A I o) _ hτI

variable [IsAlgClosed L]

theorem henselian (hI : I ≤ A.inertiaSubgroupIn K) : HenselianLocalRing ↥(OI (K := K) A I) where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₀ hu := by
    haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
    set ι := incl (K := K) A I with hι
    set fA := f.map ι with hfA
    have hfAm : fA.Monic := hf.map ι
    have hev : ∀ o, fA.eval (ι o) = ι (f.eval o) := fun o => by rw [hfA, eval_map, eval₂_hom]
    have h₀A : fA.eval (ι a₀) ∈ maximalIdeal ↥A := by
      rw [hev]; exact (mem_maximalIdeal_iff A I _).mp h₀
    have huA : IsUnit (fA.derivative.eval (ι a₀)) := by
      rw [hfA, derivative_map, eval_map, eval₂_hom]; exact hu.map ι
    obtain ⟨α, hα, hα₀⟩ := HenselianLocalRing.is_henselian fA hfAm (ι a₀) h₀A huA

    have hfix : ∀ σ ∈ I, σ (α : L) = α := by
      intro σ hσ
      obtain ⟨τ, hτ, rfl⟩ := exists_decomp_of_mem A (hI hσ)
      have hsm : τ • fA = fA := by
        ext n
        rw [coeff_smul, hfA, coeff_map, smul_incl A I τ hσ]
      have hβroot : fA.IsRoot (τ • α) := by
        show fA.eval (τ • α) = 0
        conv_lhs => rw [← hsm]
        rw [smul_eval_smul, (show fA.eval α = 0 from hα), smul_zero]
      have hβ₀ : τ • α - ι a₀ ∈ maximalIdeal ↥A := by
        have := Ideal.add_mem _ (smul_sub_mem A τ hτ α) hα₀
        rwa [sub_add_sub_cancel] at this
      have hβα : τ • α = α := root_unique fA (ι a₀) huA hα hα₀ hβroot hβ₀
      exact congrArg (fun a : ↥A => (a : L)) hβα
    have hαK : (α : L) ∈ IntermediateField.fixedField I := (IntermediateField.mem_fixedField_iff _ _).mpr hfix
    let a : ↥(OI (K := K) A I) := ⟨(α : L), Subring.mem_inf.mpr ⟨α.2, hαK⟩⟩
    have ha : ι a = α := Subtype.ext rfl
    refine ⟨a, ?_, ?_⟩
    · apply incl_injective (K := K) A I
      show ι (f.eval a) = ι 0
      rw [map_zero, ← hev, ha]
      exact hα
    · rw [mem_maximalIdeal_iff, map_sub]
      show ι a - ι a₀ ∈ maximalIdeal ↥A
      rw [ha]
      exact hα₀

end ValuationSubring.HensOI
p2m_reactivate "P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.ValuationSubring P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.ValuationSubring.HensOI"
p2m_reactivate "P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.ValuationSubring"

theorem solution
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  ValuationSubring.HensOI.henselian (K := K) A I hI

end
p2m_reactivate "P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.ValuationSubring P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn.ValuationSubring.HensOI"

end S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn (solution)
