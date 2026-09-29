-- Prove2me | solution 1 for ValuationSubring.surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d7301df2-8416-5df3-abb9-1b4f096421a3

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn

set_option autoImplicit false

universe u

open IsLocalRing

noncomputable section

namespace ValuationSubring
p2m_export "ValuationSubring" "mem_comap toSubring ext nonunits mem_nonunits_iff isLocalRing add_mem inclusion LiesOverPrime inertiaSubgroupIn exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq"
namespace ResOI
p2m_open "ValuationSubring"

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

end ValuationSubring.ResOI
p2m_reactivate "P2MW.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn.ValuationSubring P2MW.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn.ValuationSubring.ResOI"
p2m_reactivate "P2MW.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn.ValuationSubring"

theorem solution
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ) :
    let OI : Subring (AlgebraicClosure ℚ) := Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring
    let toκ : ↥OI →+* IsLocalRing.ResidueField ↥Pl := (IsLocalRing.residue ↥Pl).comp (Subring.inclusion inf_le_left)
    Function.Surjective toκ ∧ ∀ x : ↥OI, IsUnit x ↔ toκ x ≠ 0 := by
  intro OI toκ
  refine ⟨fun x => ?_, fun o => ?_⟩
  ·
    obtain ⟨y, hy⟩ := ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq Pl hPl x
    have hyP : ((y : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) ∈ Pl := ValuationSubring.mem_comap.mp y.2
    have hyI : ((y : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) ∈ IntermediateField.fixedField I :=
      (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ =>
        (IntermediateField.mem_fixedField_iff _ _).mp (y : ↥(IntermediateField.fixedField (Pl.inertiaSubgroupIn ℚ))).2 σ (hI hσ)
    refine ⟨⟨_, Subring.mem_inf.mpr ⟨hyP, hyI⟩⟩, ?_⟩
    exact hy
  ·
    rw [ValuationSubring.ResOI.isUnit_iff (K := ℚ) Pl I o]
    show IsUnit (ValuationSubring.ResOI.incl (K := ℚ) Pl I o) ↔ (IsLocalRing.residue ↥Pl) (ValuationSubring.ResOI.incl (K := ℚ) Pl I o) ≠ 0
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

end
end S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_surjective_residue_comp_inclusion_inf_fixedField_and_isUnit_iff_of_le_inertiaSubgroupIn (solution)
