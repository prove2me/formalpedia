-- Prove2me | solution 1 for PDivisibleGroup.ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/49d01deb-27db-5f0e-b5b1-4fd80d87eeb9

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_algHom_apply_mem_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one

set_option autoImplicit false

namespace RedUnit

open TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem core (Pl : ValuationSubring ℚ̄)
    {R : Type} [CommRing R] [Algebra R ℚ̄] (hR : ∀ r : R, algebraMap R ℚ̄ r ∈ Pl)
    {T : Type} [CommRing T] [Algebra R T] [Module.Finite R T] [Module.Flat R T]
    (ε : T →ₐ[R] R)
    (hred : ∀ (χ : T →ₐ[R] ℚ̄) (c : T), Pl.valuation (χ c - algebraMap R ℚ̄ (ε c)) < 1)
    (f : T →+* IsLocalRing.ResidueField ↥Pl)
    (hf : f.comp (algebraMap R T) = (IsLocalRing.residue ↥Pl).comp ((algebraMap R ℚ̄).codRestrict Pl hR))
    (c : T) :
    f c = IsLocalRing.residue ↥Pl ⟨algebraMap R ℚ̄ (ε c), hR (ε c)⟩ := by
  classical

  let P : Type := ↥Pl
  let κ : Type := IsLocalRing.ResidueField ↥Pl
  letI : Algebra R P := ((algebraMap R ℚ̄).codRestrict Pl hR).toAlgebra
  haveI : IsScalarTower R P ℚ̄ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI algRκ : Algebra R κ := ((IsLocalRing.residue ↥Pl).comp (algebraMap R P)).toAlgebra
  haveI : IsScalarTower R P κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let fₐ : T →ₐ[R] κ := ⟨f, fun r => DFunLike.congr_fun hf r⟩
  let fS : P ⊗[R] T →ₐ[P] κ := Algebra.TensorProduct.lift (Algebra.ofId P κ) fₐ (fun _ _ => Commute.all _ _)
  have hfS : ∀ x : T, fS ((1 : P) ⊗ₜ[R] x) = f x := fun x => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl

  let ιE : P ⊗[R] T →ₐ[P] ℚ̄ ⊗[R] T := Algebra.TensorProduct.map (Algebra.ofId P ℚ̄) (AlgHom.id R T)
  have hιE : Function.Injective ιE := by
    have hsub : Function.Injective ((Algebra.ofId P ℚ̄).toLinearMap.restrictScalars R) := Subtype.val_injective
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := T) ((Algebra.ofId P ℚ̄).toLinearMap.restrictScalars R) hsub
    intro x y hxy
    apply h
    have : ∀ z : P ⊗[R] T, ιE z = ((Algebra.ofId P ℚ̄).toLinearMap.restrictScalars R).rTensor T z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rfl
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    rw [← this, ← this]; exact hxy

  haveI : (RingHom.ker fS).IsPrime := RingHom.ker_isPrime _
  obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (P ⊗[R] T)) ≤ RingHom.ker fS)
  obtain ⟨𝔮, h𝔮, h𝔮𝔭⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective (f := (ιE : P ⊗[R] T →+* ℚ̄ ⊗[R] T)) hιE 𝔭 h𝔭min

  haveI := h𝔮
  haveI : IsDomain ((ℚ̄ ⊗[R] T) ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  have hbij : Function.Bijective (algebraMap ℚ̄ ((ℚ̄ ⊗[R] T) ⧸ 𝔮)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : ((ℚ̄ ⊗[R] T) ⧸ 𝔮) ≃ₐ[ℚ̄] ℚ̄ := (AlgEquiv.ofBijective (Algebra.ofId ℚ̄ ((ℚ̄ ⊗[R] T) ⧸ 𝔮)) hbij).symm
  let χE : ℚ̄ ⊗[R] T →ₐ[ℚ̄] ℚ̄ := (ψ : ((ℚ̄ ⊗[R] T) ⧸ 𝔮) →ₐ[ℚ̄] ℚ̄).comp (Ideal.Quotient.mkₐ ℚ̄ 𝔮)
  have hχE : RingHom.ker χE = 𝔮 := by
    ext x
    rw [RingHom.mem_ker]
    change ψ (Ideal.Quotient.mk 𝔮 x) = 0 ↔ x ∈ 𝔮
    rw [map_eq_zero_iff ψ ψ.injective, Ideal.Quotient.eq_zero_iff_mem]

  let χ : T →ₐ[R] ℚ̄ := (χE.restrictScalars R).comp (Algebra.TensorProduct.includeRight : T →ₐ[R] ℚ̄ ⊗[R] T)
  let χS : P ⊗[R] T →ₐ[P] ℚ̄ := (χE.restrictScalars P).comp ιE
  have hχS1 : ∀ x : T, χS ((1 : P) ⊗ₜ[R] x) = χ x := fun x => by
    change χE (ιE ((1 : P) ⊗ₜ[R] x)) = χE ((1 : ℚ̄) ⊗ₜ[R] x)
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  have hkerχS : RingHom.ker χS ≤ RingHom.ker fS := by
    intro x hx
    apply h𝔭le
    rw [RingHom.mem_ker] at hx
    rw [← h𝔮𝔭, Ideal.mem_comap, ← hχE, RingHom.mem_ker]
    exact hx

  have hmem : ∀ s : P ⊗[R] T, χS s ∈ Pl := fun s =>
    ValuationSubring.algHom_apply_mem_of_moduleFinite Pl (fun r : P => r.2) χS s
  have key : ∀ s : P ⊗[R] T, fS s = IsLocalRing.residue ↥Pl ⟨χS s, hmem s⟩ := by
    intro s
    have h0 : s - algebraMap P (P ⊗[R] T) ⟨χS s, hmem s⟩ ∈ RingHom.ker fS := by
      apply hkerχS
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]; rfl
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h0
    rw [h0, AlgHom.commutes]; rfl

  rw [← hfS, key]
  apply Ideal.Quotient.eq.2
  rw [Pl.valuation_lt_one_iff]
  have := hred χ c
  rwa [← hχS1] at this

end RedUnit

set_option linter.unusedVariables false in

theorem solution
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    {t : ℕ} (𝒯 : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p t)
    (hred : ∀ (v : ℕ) (y : 𝒯.Point (AlgebraicClosure ℚ) v) (c : 𝒯.level v),
      Pl.valuation (PDivisibleGroup.Point.toAlgHom y c -
        algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)
          (Coalgebra.counit c)) < 1)
    (v : ℕ) (f : 𝒯.level v →+* IsLocalRing.ResidueField ↥Pl)
    (hf : f.comp (algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (𝒯.level v)) =
      (IsLocalRing.residue ↥Pl).comp
        ((algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)).codRestrict
          Pl (fun r => r.2.1)))
    (c : 𝒯.level v) :
    f c = IsLocalRing.residue ↥Pl
      ((algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)).codRestrict
        Pl (fun r => r.2.1) (Coalgebra.counit c)) := by
  exact RedUnit.core Pl (fun r => r.2.1) (Bialgebra.counitAlgHom _ (𝒯.level v))
    (fun χ c => hred v (PDivisibleGroup.Point.ofAlgHom χ) c) f hf c

end S_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one
end P2MW
export P2MW.S_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one (solution)
