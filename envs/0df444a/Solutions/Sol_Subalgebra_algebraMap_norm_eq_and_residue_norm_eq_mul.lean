-- Prove2me | solution 1 for Subalgebra.algebraMap_norm_eq_and_residue_norm_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d6216828-5b27-5e8a-a917-426d87aef325

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul

set_option autoImplicit false

open scoped nonZeroDivisors TensorProduct

theorem Ws14Port.free_of_finite_of_torsion_eq_bot_of_valuationRing {R M : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Submodule.torsion R M = ⊥) : Module.Free R M := by
  have : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr h
  exact Module.free_of_flat_of_isLocalRing

theorem Ws14Port.free_of_finite_of_isTorsionFree_of_valuationRing {R M : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  Ws14Port.free_of_finite_of_torsion_eq_bot_of_valuationRing
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp ‹_›)

namespace Ws14Port

theorem algebraMap_injective_of_tower (V K F : Type*) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] : Function.Injective (algebraMap V F) := by
  rw [IsScalarTower.algebraMap_eq V K F]
  exact (algebraMap K F).injective.comp (IsFractionRing.injective V K)

theorem isTorsionFree_subalgebra {V F : Type*} [CommRing V] [IsDomain V] [Field F] [Algebra V F]
    (hinj : Function.Injective (algebraMap V F)) (S : Subalgebra V F) :
    Module.IsTorsionFree V S :=
  haveI : Module.IsTorsionFree V F := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  Function.Injective.moduleIsTorsionFree (Subtype.val : S → F) Subtype.val_injective
    (fun _ _ => rfl)

theorem free_subalgebra {V F : Type*} [CommRing V] [IsDomain V] [ValuationRing V] [Field F]
    [Algebra V F] (hinj : Function.Injective (algebraMap V F)) (S : Subalgebra V F)
    [Module.Finite V S] : Module.Free V S :=
  haveI := isTorsionFree_subalgebra hinj S
  Ws14Port.free_of_finite_of_isTorsionFree_of_valuationRing

theorem isLocalization_of_span_eq_top {V K F : Type*} [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) (hspan : Submodule.span K (S : Set F) = ⊤) :
    IsLocalization (Algebra.algebraMapSubmonoid S V⁰) F := by
  have hinj := algebraMap_injective_of_tower V K F
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, v, hv, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [← IsScalarTower.algebraMap_apply V S F v]
    exact (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hv)
  · intro z
    have hz : z ∈ Submodule.span K (S : Set F) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact ⟨(⟨x, hx⟩, 1), by simp⟩
    | zero => exact ⟨(0, 1), by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨a, m⟩, ha⟩ := hx
      obtain ⟨⟨b, n⟩, hb⟩ := hy
      refine ⟨(a * n + b * m, m * n), ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at ha hb ⊢
      rw [add_mul, ← mul_assoc, ha, mul_comm (algebraMap S F (m : S)) (algebraMap S F (n : S)),
        ← mul_assoc, hb]
    | smul k x _ hx =>
      obtain ⟨⟨a, m⟩, ha⟩ := hx
      obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := V) k
      have hdS : algebraMap V S d ∈ Algebra.algebraMapSubmonoid S V⁰ := ⟨d, hd, rfl⟩
      refine ⟨(algebraMap V S c * a, m * ⟨algebraMap V S d, hdS⟩), ?_⟩
      have hd0 : algebraMap V F d ≠ 0 :=
        (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hd)
      simp only [Submonoid.coe_mul, map_mul] at ha ⊢
      rw [← IsScalarTower.algebraMap_apply V S F d, ← IsScalarTower.algebraMap_apply V S F c,
        Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply V K F,
        ← IsScalarTower.algebraMap_apply V K F, ← ha]
      field_simp
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

theorem finrank_subalgebra_eq {V K F : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤) :
    Module.finrank V S = Module.finrank K F := by
  haveI := free_subalgebra (algebraMap_injective_of_tower V K F) S
  haveI := isLocalization_of_span_eq_top S hspan
  let b := Module.Free.chooseBasis V S
  rw [Module.finrank_eq_card_chooseBasisIndex,
    Module.finrank_eq_card_basis (b.localizationLocalization K V⁰ F)]

theorem algebraMap_norm_subalgebra_eq {V K F : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤) (s : S) :
    algebraMap V K (Algebra.norm V s) = Algebra.norm K (s : F) := by
  haveI := free_subalgebra (algebraMap_injective_of_tower V K F) S
  haveI := isLocalization_of_span_eq_top S hspan
  exact (Algebra.norm_localization V V⁰ (Rₘ := K) (Sₘ := F) s).symm

end Ws14Port

namespace Ws14Port

theorem norm_one_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (A' : Type*) [CommRing A'] [Algebra A A'] (b : B) :
    Algebra.norm A' ((1 : A') ⊗ₜ[A] b) = algebraMap A A' (Algebra.norm A b) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem norm_prod_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Free R S] [Module.Finite R S] [Module.Free R T]
    [Module.Finite R T] (x : S × T) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : Algebra.lmul R (S × T) x
      = LinearMap.prodMap (Algebra.lmul R S x.1) (Algebra.lmul R T x.2) :=
    LinearMap.ext fun _ => rfl
  rw [Algebra.norm_apply, h, LinearMap.det_prodMap, ← Algebra.norm_apply, ← Algebra.norm_apply]

theorem residue_norm_eq_prod_norm_of_surjective {V B : Type*} [CommRing V] [IsLocalRing V]
    [CommRing B] [Algebra V B] [Module.Free V B] [Module.Finite V B]
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : B →ₐ[V] κ₁) (ρ₂ : B →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun b : B => (ρ₁ b, ρ₂ b))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank V B) (b : B) :
    IsLocalRing.residue V (Algebra.norm V b)
      = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ b)
          * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ b) := by
  set κ := IsLocalRing.ResidueField V

  let Φ : κ ⊗[V] B →ₐ[κ] κ₁ × κ₂ :=
    Algebra.TensorProduct.lift (Algebra.ofId κ (κ₁ × κ₂)) (ρ₁.prod ρ₂) fun _ _ => Commute.all _ _
  have hΦ : ∀ x : B, Φ ((1 : κ) ⊗ₜ[V] x) = (ρ₁ x, ρ₂ x) := fun x => by
    simp [Φ, Algebra.TensorProduct.lift_tmul]
  have hΦsurj : Function.Surjective Φ := fun c => by
    obtain ⟨x, hx⟩ := hsurj c
    exact ⟨1 ⊗ₜ x, by rw [hΦ]; exact hx⟩
  have hdim' : Module.finrank κ (κ ⊗[V] B) = Module.finrank κ (κ₁ × κ₂) := by
    rw [Module.finrank_baseChange, Module.finrank_prod, hdim]
  have hΦinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim' (f := Φ.toLinearMap)).mpr
      hΦsurj
  let e : κ ⊗[V] B ≃ₐ[κ] κ₁ × κ₂ := AlgEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  calc IsLocalRing.residue V (Algebra.norm V b)
      = algebraMap V κ (Algebra.norm V b) := rfl
    _ = Algebra.norm κ ((1 : κ) ⊗ₜ[V] b) := (norm_one_tmul κ b).symm
    _ = Algebra.norm κ (e ((1 : κ) ⊗ₜ[V] b)) := (Algebra.norm_eq_of_algEquiv e _).symm
    _ = Algebra.norm κ (ρ₁ b, ρ₂ b) := by rw [AlgEquiv.ofBijective_apply, hΦ]
    _ = Algebra.norm κ (ρ₁ b) * Algebra.norm κ (ρ₂ b) := norm_prod_apply _

end Ws14Port

namespace Ws14Port

theorem residue_norm_subalgebra_eq_prod {V K F : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F] [Algebra V F]
    [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤)
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : S →ₐ[V] κ₁) (ρ₂ : S →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun s : S => (ρ₁ s, ρ₂ s))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank K F) (s : S) :
    IsLocalRing.residue V (Algebra.norm V s)
      = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ s)
          * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ s) := by
  haveI := free_subalgebra (algebraMap_injective_of_tower V K F) S
  exact residue_norm_eq_prod_norm_of_surjective ρ₁ ρ₂ hsurj
    (hdim.trans (finrank_subalgebra_eq S hspan).symm) s

end Ws14Port

theorem solution {V K F : Type*} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F]
    [Algebra V F] [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤)
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : S →ₐ[V] κ₁) (ρ₂ : S →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun s : S => (ρ₁ s, ρ₂ s))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank K F) (s : S) :
    algebraMap V K (Algebra.norm V s) = Algebra.norm K (s : F) ∧
      IsLocalRing.residue V (Algebra.norm V s)
        = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ s)
            * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ s) :=
  ⟨Ws14Port.algebraMap_norm_subalgebra_eq S hspan s,
    Ws14Port.residue_norm_subalgebra_eq_prod S hspan ρ₁ ρ₂ hsurj hdim s⟩

end S_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul
end P2MW
export P2MW.S_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul (solution)
