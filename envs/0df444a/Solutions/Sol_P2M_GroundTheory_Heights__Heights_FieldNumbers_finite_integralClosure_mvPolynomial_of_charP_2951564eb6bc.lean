-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_integralClosure_mvPolynomial_of_charP_2951564eb6bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:06:49.339071+00:00
-- url     : https://prove2.me/submissions/9a3ba009-2886-4dfe-be85-fa5fe4053b4f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharP
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_pow_eq_map_expand_ad624b380e19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_mapExpand_723755a99971
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_injective_of_isIntegral_57e3e3cc9dbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isSeparable_of_pow_coeff_3ab81127b728


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
universe u
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (s : ℕ) (L : Type u) [Field L] [Algebra (FractionRing (MvPolynomial (Fin s) k)) L]
    [FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) L]
    [Algebra (MvPolynomial (Fin s) k) L]
    [IsScalarTower (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) L] :
    Module.Finite (MvPolynomial (Fin s) k) (integralClosure (MvPolynomial (Fin s) k) L) := by
  classical
  set B := MvPolynomial (Fin s) k
  set F := FractionRing B
  have hp : p.Prime := Fact.out
  have hinjBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective B F)
  have : CharP L p := charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C)
    (hinjBL.comp (MvPolynomial.C_injective (Fin s) k)) p

  have : ExpChar (separableClosure F L) p := ExpChar.prime hp
  have : IsPurelyInseparable (separableClosure F L) L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent (separableClosure F L) L
  set q := p ^ e with hqdef
  have hq : 0 < q := pow_pos hp.pos e
  have hsepq : ∀ y : L, IsSeparable F (y ^ q) := by
    intro y
    rw [← IsPurelyInseparable.algebraMap_iterateFrobenius (separableClosure F L) p (le_refl e) y]
    exact mem_separableClosure_iff.mp
      (IsPurelyInseparable.iterateFrobenius (separableClosure F L) L p (le_refl e) y).2

  let : Algebra k L := ((algebraMap B L).comp (algebraMap k B)).toAlgebra
  have : IsScalarTower k B L := IsScalarTower.of_algebraMap_eq' rfl
  set Ω := AlgebraicClosure L
  have hinjBΩ : Function.Injective (algebraMap B Ω) := by
    rw [IsScalarTower.algebraMap_eq B L Ω]
    exact (algebraMap L Ω).injective.comp hinjBL

  let b := Module.finBasis F L
  let g : Fin (Module.finrank F L) → F[X] := fun j => minpoly F (b j ^ q)
  choose num den hden hnd using fun c : F => IsFractionRing.div_surjective (A := B) c
  let Tk : Finset k := Finset.univ.biUnion fun j => (Finset.range ((g j).natDegree + 1)).biUnion
    fun i => (num ((g j).coeff i)).support.image (num ((g j).coeff i)).coeff ∪
      (den ((g j).coeff i)).support.image (den ((g j).coeff i)).coeff

  choose r hr using fun a : k => IsAlgClosed.exists_pow_nat_eq (algebraMap k Ω a) hq
  choose t ht using fun i : Fin s =>
    IsAlgClosed.exists_pow_nat_eq (algebraMap B Ω (MvPolynomial.X i)) hq
  let k' : IntermediateField k Ω := IntermediateField.adjoin k (r '' (Tk : Set k))
  have : FiniteDimensional k k' := by
    have : Finite (r '' (Tk : Set k)) := ((Tk.finite_toSet).image r).to_subtype
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨a, -, rfl⟩
    refine ⟨X ^ q - C a, monic_X_pow_sub_C a hq.ne', ?_⟩
    simp [eval₂_sub, hr a, Algebra.algebraMap_eq_smul_one]
  have hk'root : ∀ a ∈ Tk, ∃ z : k', z ^ q = algebraMap k k' a := by
    intro a ha
    refine ⟨⟨r a, IntermediateField.subset_adjoin k _ ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    simp [hr a]
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p

  set B' := MvPolynomial (Fin s) k'
  let θ : B →ₐ[k] B' := (MvPolynomial.mapAlgHom (Algebra.ofId k k')).comp (MvPolynomial.expand q)
  have hθ : ∀ N : B, θ N = MvPolynomial.map (algebraMap k k') (MvPolynomial.expand q N) :=
    fun N => rfl
  let : Algebra B B' := θ.toRingHom.toAlgebra
  have : Module.Finite B B' := finite_mapExpand k k' (Fin s) q hq
  have : Algebra.IsIntegral B B' := Algebra.IsIntegral.of_finite B B'
  let ψ : B' →ₐ[k'] Ω := MvPolynomial.aeval t
  have hψθ : ∀ N : B, ψ (θ N) = algebraMap B Ω N := by
    have h : (ψ.restrictScalars k).comp θ = IsScalarTower.toAlgHom k B Ω := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, θ, ψ, MvPolynomial.mapAlgHom_apply,
        MvPolynomial.expand_X, map_pow, MvPolynomial.map_X]
      erw [MvPolynomial.aeval_X]
      rw [ht]
      rfl
    intro N
    exact DFunLike.congr_fun h N
  have hψinj : Function.Injective ψ := by
    refine injective_of_isIntegral (B := B) ψ.toRingHom ?_
    convert hinjBΩ using 1
    funext N
    exact hψθ N
  let : Algebra B' Ω := ψ.toRingHom.toAlgebra
  have : IsScalarTower B B' Ω := IsScalarTower.of_algebraMap_eq fun N => (hψθ N).symm
  have : FaithfulSMul B' Ω := (faithfulSMul_iff_algebraMap_injective B' Ω).mpr hψinj
  set F' := FractionRing B'
  let : Algebra F' Ω := FractionRing.liftAlgebra B' Ω

  have hFF' : ∀ c : F, ∃ c' : F', algebraMap F' Ω c' = algebraMap F Ω c := by
    intro c
    refine ⟨algebraMap B' F' (θ (num c)) / algebraMap B' F' (θ (den c)), ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    change ψ (θ (num c)) / ψ (θ (den c)) = _
    rw [hψθ, hψθ]
    conv_rhs => rw [← hnd c]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hrootB : ∀ N : B, (∀ m ∈ N.support, N.coeff m ∈ Tk) →
      ∃ N' : B', ψ N' ^ q = algebraMap B Ω N := by
    intro N hN
    obtain ⟨N', hN'⟩ := exists_pow_eq_map_expand (k' := k') p e N fun m => by
      by_cases hm : m ∈ N.support
      · exact hk'root _ (hN m hm)
      · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
        exact ⟨0, zero_pow hq.ne'⟩
    refine ⟨N', ?_⟩
    rw [← map_pow, hN', ← hθ, hψθ]
  have hcoeff : ∀ j i, ∃ d : F', algebraMap F' Ω d ^ q = algebraMap F Ω ((g j).coeff i) := by
    intro j i
    by_cases hc : (g j).coeff i = 0
    · exact ⟨0, by rw [hc, map_zero, map_zero, zero_pow hq.ne']⟩
    have hi : i ∈ Finset.range ((g j).natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hc))
    set c := (g j).coeff i
    obtain ⟨N', hN'⟩ := hrootB (num c) fun m hm => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm)⟩⟩
    obtain ⟨D', hD'⟩ := hrootB (den c) fun m hm => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hm)⟩⟩
    refine ⟨algebraMap B' F' N' / algebraMap B' F' D', ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_pow]
    change ψ N' ^ q / ψ D' ^ q = _
    rw [hN', hD']
    conv_rhs => rw [← hnd c]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

  let ω : Fin (Module.finrank F L) → Ω := fun j => algebraMap L Ω (b j)
  have hωsep : ∀ j, IsSeparable F' (ω j) := by
    intro j
    refine isSeparable_of_pow_coeff p e (g j) (hsepq (b j)) (ω j) ?_ (hcoeff j)
    rw [← map_pow, aeval_algebraMap_apply, minpoly.aeval, map_zero]
  let E : IntermediateField F' Ω := IntermediateField.adjoin F' (Set.range ω)
  have : FiniteDimensional F' E := by
    have : Finite (Set.range ω) := Set.finite_range ω
    exact IntermediateField.finiteDimensional_adjoin fun x ⟨j, hj⟩ => hj ▸ (hωsep j).isIntegral
  have : Algebra.IsSeparable F' E :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := F') (E := Ω)).mpr fun x ⟨j, hj⟩ => hj ▸ hωsep j
  have hLE : ∀ y : L, algebraMap L Ω y ∈ E := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun j _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    obtain ⟨c', hc'⟩ := hFF' (b.repr y j)
    rw [← hc']
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin F' _ ⟨j, rfl⟩)
  have : IsScalarTower B' F' Ω := FractionRing.isScalarTower_liftAlgebra B' Ω
  let : Algebra B' E := E.algebra'
  have : IsScalarTower B' F' E := IntermediateField.isScalarTower E
  have : IsScalarTower B' E Ω := IsScalarTower.of_algebraMap_eq fun x => rfl

  have hC' : Module.Finite B' (integralClosure B' E) :=
    IsIntegralClosure.finite B' F' E (integralClosure B' E)
  let S : Submodule B' Ω :=
    (integralClosure B' E).toSubmodule.map (IsScalarTower.toAlgHom B' E Ω).toLinearMap
  have hSfg : S.FG := (Module.Finite.iff_fg.mp hC').map _
  have : Module.Finite B (S.restrictScalars B) := Module.Finite.iff_fg.mpr hSfg.restrictScalars
  have : IsNoetherian B (S.restrictScalars B) := isNoetherian_of_isNoetherianRing_of_finite B (S.restrictScalars B)
  let φ : L →ₗ[B] Ω := (IsScalarTower.toAlgHom B L Ω).toLinearMap
  have hle : (integralClosure B L).toSubmodule.map φ ≤ S.restrictScalars B := by
    rintro _ ⟨y, hy, rfl⟩
    have hint : IsIntegral B' (algebraMap L Ω y) :=
      ((hy : IsIntegral B y).map (IsScalarTower.toAlgHom B L Ω)).tower_top
    refine ⟨⟨algebraMap L Ω y, hLE y⟩, ?_, rfl⟩
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B' E Ω)
      (algebraMap E Ω).injective).mp hint
  have : IsNoetherian B ((integralClosure B L).toSubmodule.map φ) := isNoetherian_of_le hle
  have hfg : ((integralClosure B L).toSubmodule.map φ).FG := Module.Finite.iff_fg.mp (Module.IsNoetherian.finite B _)
  exact Module.Finite.iff_fg.mpr
    (Submodule.fg_of_fg_map_injective φ (algebraMap L Ω).injective hfg)
end GroundTheory.Heights₂.Heights.FieldNumbers
