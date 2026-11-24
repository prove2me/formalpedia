-- Prove2me | solution 1 for P2M_FltRegular_CaseI_exists_int_sum_eq_zero__050f4fd83c8a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:16.821391+00:00
-- url     : https://prove2.me/submissions/b36eb1f2-3a25-4d77-9201-4eeef6e2b24a

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CaseI
public import Theorems.Thm_FltRegular_CaseI_pow_sub_intGalConj_mem
public import Theorems.Thm_P2M_FltRegular_CaseI_exists_int_sum_eq_zero__aux_bf59d6c122ae
public import Theorems.Thm_unit_inv_conj_is_root_of_unity


set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
local notation3 "zetaUnit" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
open FractionalIdeal NumberField IsCMField
open FltRegular FltRegular.CaseI
namespace FltRegular.CaseI
theorem _root_.solution (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) = u * α ^ p) [Fact (p.Prime)]
    (hp : 2 < p) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (zetaUnit ^ i : (𝓞 K)ˣ) -
      ((zetaUnit ^ k) ^ 2 : (𝓞 K)ˣ) *
        (x + y * (zetaUnit ^ (-i) : (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hroot⟩ := unit_inv_conj_is_root_of_unity hζ u hp
  refine ⟨k, ?_⟩
  rw [← exists_int_sum_eq_zero'_aux _ _ _ _ hp, h, ← hroot, Units.val_mul, mul_assoc,
    ← mul_sub]
  convert Ideal.mul_mem_left _ ↑u (pow_sub_intGalConj_mem α hp) using 3
  ext
  simp only [map_mul, map_pow, map_units_inv, Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv,
    RingOfIntegers.mapRingEquiv_apply, RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    coe_ringOfIntegersComplexConj, ne_eq, EmbeddingLike.map_eq_zero_iff,
    FaithfulSMul.algebraMap_eq_zero_iff, Units.ne_zero, not_false_eq_true, inv_mul_cancel_left₀]
end FltRegular.CaseI
