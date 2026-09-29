-- Prove2me | solution 1 for ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5afd4996-7572-54c0-8c98-cf9a8e776efc

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_mem_decompositionSubgroup_forall_residue_smul_eq
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open IsLocalRing Polynomial
open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable section

namespace ValuationSubring
p2m_export "ValuationSubring" "coe_mem_nonunits_iff toSubring ext mem_nonunits_iff valuation_lt_one_iff decompositionSubgroup valuation_le_one_iff algebra valuation inclusion LiesOverPrime henselianLocalRing_of_isAlgClosed isAlgClosed_residueField_algebraicClosure_rat exists_mem_decompositionSubgroup_forall_residue_smul_eq isDiscreteValuationRing_inf_fixedField_decompositionSubgroup"
namespace DecompRing
p2m_open "ValuationSubring"

theorem isUnit_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {x y : R} (hx : IsUnit x)
    (hxy : y - x ∈ maximalIdeal R) : IsUnit y := by
  by_contra hy
  have hy' : y ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hy
  have hx' : x ∈ maximalIdeal R := by
    have := Ideal.sub_mem _ hy' hxy
    rwa [sub_sub_cancel] at this
  exact (mem_maximalIdeal _).mp hx' hx

theorem eval_sub_eval_mem {R : Type*} [CommRing R] [IsLocalRing R] (g : R[X]) {x y : R}
    (hxy : x - y ∈ maximalIdeal R) : g.eval x - g.eval y ∈ maximalIdeal R := by
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub x y g
  rw [hc]
  exact Ideal.mul_mem_right _ _ hxy

theorem root_unique {R : Type*} [CommRing R] [IsLocalRing R] (f : R[X]) (a₀ : R)
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

variable (A : ValuationSubring ℚ̄)

abbrev decField : IntermediateField ℚ ℚ̄ := IntermediateField.fixedField (A.decompositionSubgroup ℚ)

abbrev Z : Subring ℚ̄ := A.toSubring ⊓ (decField A).toSubring

variable {A}

theorem coe_memA (x : Z A) : (x : ℚ̄) ∈ A := x.2.1

theorem coe_fixed (x : Z A) (σ : Gal) (hσ : σ ∈ A.decompositionSubgroup ℚ) : σ (x : ℚ̄) = x :=
  (IntermediateField.mem_fixedField_iff _ _).mp x.2.2 σ hσ

def mkZ (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ x = x) : Z A :=
  ⟨x, ⟨hxA, (IntermediateField.mem_fixedField_iff _ _).mpr hfix⟩⟩

@[scoped simp] theorem coe_mkZ (x : ℚ̄) (hxA : x ∈ A) (hfix) : ((mkZ x hxA hfix : Z A) : ℚ̄) = x := rfl

variable (A)

def incl : Z A →+* A where
  toFun z := ⟨z, coe_memA z⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[scoped simp] theorem incl_coe (z : Z A) : ((incl A z : A) : ℚ̄) = z := rfl

theorem incl_injective : Function.Injective (incl A) := fun x y h =>
  Subtype.ext (by rw [← incl_coe A x, ← incl_coe A y, h])

variable {A}

theorem not_isUnit_iff (hfwd : ∀ x : Z A, A.valuation (x : ℚ̄) < 1 → ¬ IsUnit x) (z : Z A) :
    ¬ IsUnit z ↔ A.valuation (z : ℚ̄) < 1 := by
  refine ⟨fun hz => ?_, hfwd z⟩
  by_contra hv
  apply hz
  have hv1 : A.valuation (z : ℚ̄) = 1 := le_antisymm ((A.valuation_le_one_iff _).mpr (coe_memA z)) (not_lt.mp hv)
  have hz0 : (z : ℚ̄) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv1
    exact zero_ne_one hv1
  have hinvA : (z : ℚ̄)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀, hv1, inv_one]
  have hinvF : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ (z : ℚ̄)⁻¹ = (z : ℚ̄)⁻¹ := fun σ hσ => by
    rw [map_inv₀, coe_fixed z σ hσ]
  refine IsUnit.of_mul_eq_one (mkZ ((z : ℚ̄)⁻¹) hinvA hinvF) (Subtype.ext ?_)
  change (z : ℚ̄) * (z : ℚ̄)⁻¹ = 1
  exact mul_inv_cancel₀ hz0

theorem isUnit_iff_incl (hfwd : ∀ x : Z A, A.valuation (x : ℚ̄) < 1 → ¬ IsUnit x) (z : Z A) :
    IsUnit z ↔ IsUnit (incl A z) := by
  rw [← not_iff_not, not_isUnit_iff hfwd, show ((z : ℚ̄)) = ((incl A z : A) : ℚ̄) from rfl,
    ← ValuationSubring.valuation_lt_one_iff, mem_maximalIdeal, _root_.mem_nonunits_iff]

theorem coe_smul (τ : ↥(A.decompositionSubgroup ℚ)) (a : A) : ((τ • a : A) : ℚ̄) = (τ : Gal) (a : ℚ̄) := rfl

theorem smul_mem_maximalIdeal (τ : ↥(A.decompositionSubgroup ℚ)) {a : A} (ha : a ∈ maximalIdeal A) :
    τ • a ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, _root_.mem_nonunits_iff] at ha ⊢
  intro hu
  apply ha
  have h := hu.map (MulSemiringAction.toRingHom (↥(A.decompositionSubgroup ℚ)) A τ⁻¹)
  rwa [MulSemiringAction.toRingHom_apply, inv_smul_smul] at h

theorem smul_incl (τ : ↥(A.decompositionSubgroup ℚ)) (z : Z A) : τ • incl A z = incl A z :=
  Subtype.ext (coe_fixed z τ τ.2)

theorem henselian (hfwd : ∀ x : Z A, A.valuation (x : ℚ̄) < 1 → ¬ IsUnit x) [IsLocalRing (Z A)] :
    HenselianLocalRing (Z A) where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₀ hu := by
    haveI : HenselianLocalRing A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
    have hmax : ∀ z : Z A, z ∈ maximalIdeal (Z A) ↔ incl A z ∈ maximalIdeal A := fun z => by
      rw [mem_maximalIdeal, mem_maximalIdeal, _root_.mem_nonunits_iff, _root_.mem_nonunits_iff, isUnit_iff_incl hfwd]
    set ι := incl A with hι
    set fA := f.map ι with hfA
    have hfAm : fA.Monic := hf.map ι
    have hev : ∀ o, fA.eval (ι o) = ι (f.eval o) := fun o => by rw [hfA, eval_map, eval₂_hom]
    have h₀A : fA.eval (ι a₀) ∈ maximalIdeal A := by
      rw [hev]; exact (hmax _).mp h₀
    have huA : IsUnit (fA.derivative.eval (ι a₀)) := by
      rw [hfA, derivative_map, eval_map, eval₂_hom]; exact hu.map ι
    obtain ⟨α, hα, hα₀⟩ := HenselianLocalRing.is_henselian fA hfAm (ι a₀) h₀A huA

    have hfix : ∀ σ : Gal, σ ∈ A.decompositionSubgroup ℚ → σ (α : ℚ̄) = α := by
      intro σ hσ
      let τ : ↥(A.decompositionSubgroup ℚ) := ⟨σ, hσ⟩
      have hsm : τ • fA = fA := by
        ext n
        rw [coeff_smul, hfA, coeff_map, smul_incl τ]
      have hβroot : fA.IsRoot (τ • α) := by
        show fA.eval (τ • α) = 0
        conv_lhs => rw [← hsm]
        rw [smul_eval_smul, (show fA.eval α = 0 from hα), smul_zero]
      have hβ₀ : τ • α - ι a₀ ∈ maximalIdeal A := by
        have h1 : τ • (α - ι a₀) ∈ maximalIdeal A := smul_mem_maximalIdeal τ hα₀
        rwa [smul_sub, smul_incl τ] at h1
      have hβα : τ • α = α := root_unique fA (ι a₀) huA hα hα₀ hβroot hβ₀
      exact congrArg (fun a : A => (a : ℚ̄)) hβα
    let a : Z A := mkZ (α : ℚ̄) α.2 hfix
    have ha : ι a = α := Subtype.ext rfl
    refine ⟨a, ?_, ?_⟩
    · apply incl_injective A
      show ι (f.eval a) = ι 0
      rw [map_zero, ← hev, ha]
      exact hα
    · rw [hmax, map_sub]
      show ι a - ι a₀ ∈ maximalIdeal A
      rw [ha]
      exact hα₀

variable (A)
variable (ℓ : ℕ) [Fact ℓ.Prime]

omit [Fact ℓ.Prime] in
theorem natCast_mem_maximalIdeal (hA : A.LiesOverPrime ℓ) : ((ℓ : ℕ) : A) ∈ maximalIdeal A := by
  apply ValuationSubring.coe_mem_nonunits_iff.mp
  have : ((((ℓ : ℕ) : A) : ℚ̄)) = (ℓ : ℚ̄) := by push_cast; rfl
  rw [this]
  exact hA

theorem charP_residueField (hA : A.LiesOverPrime ℓ) : CharP (ResidueField A) ℓ := by
  rw [CharP.charP_iff_prime_eq_zero Fact.out]
  have h := (residue_eq_zero_iff _).mpr (natCast_mem_maximalIdeal A ℓ hA)
  rwa [map_natCast] at h

theorem frobenius_residue_rat (hA : A.LiesOverPrime ℓ) [PerfectRing (ResidueField A) ℓ]
    (x : ℚ) (hx : algebraMap ℚ ℚ̄ x ∈ A) :
    haveI := charP_residueField A ℓ hA
    frobeniusEquiv (ResidueField A) ℓ (residue A ⟨algebraMap ℚ ℚ̄ x, hx⟩) = residue A ⟨algebraMap ℚ ℚ̄ x, hx⟩ := by
  haveI := charP_residueField A ℓ hA
  set r := residue A ⟨algebraMap ℚ ℚ̄ x, hx⟩ with hr

  have hA1 : (⟨algebraMap ℚ ℚ̄ x, hx⟩ : A) * ((x.den : ℕ) : A) = ((x.num : ℤ) : A) := by
    apply Subtype.ext
    push_cast
    rw [← map_natCast (algebraMap ℚ ℚ̄), ← map_mul, Rat.mul_den_eq_num, map_intCast]
  have hres : r * ((x.den : ℕ) : ResidueField A) = ((x.num : ℤ) : ResidueField A) := by
    have := congrArg (residue A) hA1
    rwa [map_mul, map_natCast, map_intCast] at this

  have hden : ((x.den : ℕ) : ResidueField A) ≠ 0 := by
    intro h0
    have hnum0 : ((x.num : ℤ) : ResidueField A) = 0 := by rw [← hres, h0, mul_zero]
    have hℓden : ℓ ∣ x.den := (CharP.cast_eq_zero_iff (ResidueField A) ℓ x.den).mp h0
    have hℓnum : (ℓ : ℤ) ∣ x.num := (CharP.intCast_eq_zero_iff (ResidueField A) ℓ x.num).mp hnum0
    have hℓnum' : ℓ ∣ x.num.natAbs := Int.natCast_dvd.mp hℓnum
    have h1 : ℓ ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd hℓnum' hℓden
    rw [x.reduced, Nat.dvd_one] at h1
    exact (Fact.out : ℓ.Prime).one_lt.ne' h1
  apply mul_right_cancel₀ hden
  rw [hres]
  have h2 := congrArg (frobeniusEquiv (ResidueField A) ℓ) hres
  rw [map_mul, map_natCast, map_intCast] at h2
  exact h2

theorem exists_frobenius (hA : A.LiesOverPrime ℓ) :
    ∃ σ : Gal, ∃ hσ : σ ∈ A.decompositionSubgroup ℚ,
      ∀ a : A, residue A ((⟨σ, hσ⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = (residue A a) ^ ℓ := by
  haveI := charP_residueField A ℓ hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : ExpChar (ResidueField A) ℓ := ExpChar.prime Fact.out

  haveI : IsGalois ℚ ℚ̄ := by
    convert @IsAlgClosure.isGalois ℚ ℚ̄ _ _ _ (@AlgebraicClosure.instIsAlgClosure ℚ _) _
  obtain ⟨σ, hσ, h⟩ := ValuationSubring.exists_mem_decompositionSubgroup_forall_residue_smul_eq A
    (frobeniusEquiv (ResidueField A) ℓ) (fun x hx => frobenius_residue_rat A ℓ hA x hx)
  exact ⟨σ, hσ, fun a => by rw [h a, frobeniusEquiv_apply, frobenius_def]⟩

variable {A}

theorem mem_range_of_pow_eq {F : Type*} [Field F] [CharP F ℓ] {y : F} (hy : y ^ ℓ = y) :
    y ∈ (ZMod.castHom (dvd_refl ℓ) F).range := by
  classical
  set ι := ZMod.castHom (dvd_refl ℓ) F with hι
  have hℓ : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  set P : F[X] := X ^ ℓ - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hℓ
  have hdeg : P.natDegree = ℓ := FiniteField.X_pow_card_sub_X_natDegree_eq F hℓ
  have hroot : ∀ z : F, z ^ ℓ = z → z ∈ P.roots := fun z hz => by
    rw [Polynomial.mem_roots hP0, Polynomial.IsRoot, hP, eval_sub, eval_pow, eval_X, hz, sub_self]
  by_contra hyS

  let S : Finset F := (Finset.univ : Finset (ZMod ℓ)).image ι
  have hScard : S.card = ℓ := by
    rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, ZMod.card]
  have hyS' : y ∉ S := by
    intro h
    apply hyS
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, ha⟩
  have hsub : insert y S ⊆ P.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset]
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hroot _ hy
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz'
      apply hroot
      rw [← map_pow, ZMod.pow_card]
  have h1 : (insert y S).card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hyS', hScard] at h1
  have h2 : P.roots.toFinset.card ≤ ℓ :=
    (Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' P)
  omega

theorem exists_residue (hA : A.LiesOverPrime ℓ) [IsLocalRing (Z A)] :
    ∃ π : Z A →+* ZMod ℓ, Function.Surjective π ∧ ∀ x : Z A, π x = 0 ↔ A.valuation (x : ℚ̄) < 1 := by
  haveI := charP_residueField A ℓ hA
  obtain ⟨σ, hσ, hfrob⟩ := exists_frobenius A ℓ hA
  let ι := ZMod.castHom (dvd_refl ℓ) (ResidueField A)
  let ψ : Z A →+* ResidueField A := (residue A).comp (incl A)

  have hψ : ∀ z : Z A, ψ z ∈ ι.range := fun z => by
    apply mem_range_of_pow_eq ℓ
    have h := hfrob (incl A z)
    rw [smul_incl ⟨σ, hσ⟩ z] at h
    exact h.symm
  let e : ZMod ℓ ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b h => ι.injective (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let π : Z A →+* ZMod ℓ := e.symm.toRingHom.comp (ψ.codRestrict ι.range hψ)
  have hπ : ∀ z, ι (π z) = ψ z := fun z => by
    have h1 : ((e (π z) : ι.range) : ResidueField A) = ι (π z) := rfl
    rw [← h1]
    change ((e (e.symm (ψ.codRestrict ι.range hψ z)) : ι.range) : ResidueField A) = ψ z
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨π, ZMod.ringHom_surjective π, fun z => ?_⟩
  rw [← map_eq_zero_iff ι ι.injective, hπ]
  change residue A (incl A z) = 0 ↔ _
  rw [residue_eq_zero_iff, show ((z : ℚ̄)) = ((incl A z : A) : ℚ̄) from rfl, ValuationSubring.valuation_lt_one_iff]

end ValuationSubring.DecompRing
p2m_reactivate "P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.ValuationSubring P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.ValuationSubring.DecompRing"
p2m_reactivate "P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.ValuationSubring"

open ValuationSubring.DecompRing in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    HenselianLocalRing ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) ∧
      (∃ π : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring) →+* ZMod ℓ,
        Function.Surjective π ∧
        ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
          π x = 0 ↔ A.valuation (x : AlgebraicClosure ℚ) < 1) ∧
      ∀ x : ↥((A.toSubring) ⊓ (IntermediateField.fixedField (A.decompositionSubgroup ℚ)).toSubring),
        ¬ IsUnit x ↔ A.valuation (x : AlgebraicClosure ℚ) < 1 := by
  obtain ⟨hdvr, -, hfwd⟩ := ValuationSubring.isDiscreteValuationRing_inf_fixedField_decompositionSubgroup A ℓ hA
  haveI : IsLocalRing (Z A) := hdvr.toIsLocalRing
  exact ⟨henselian hfwd, exists_residue ℓ hA, not_isUnit_iff hfwd⟩

end
p2m_reactivate "P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.ValuationSubring P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup.ValuationSubring.DecompRing"

end S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
end P2MW
export P2MW.S_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup (solution)
