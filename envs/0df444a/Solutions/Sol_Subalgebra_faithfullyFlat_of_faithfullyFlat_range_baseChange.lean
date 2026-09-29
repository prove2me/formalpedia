-- Prove2me | solution 1 for Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/cd3a7981-aa49-5776-bc5f-8075d5eeb568

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct

universe u v w

namespace S17Ta

universe u₁ u₂ u₃

section Descent

variable (R : Type u₁) [CommRing R] (S : Type u₂) [CommRing S] [Algebra R S]
variable (M : Type u₃) [AddCommGroup M] [Module R M]

noncomputable def cancelIso (N : Type*) [AddCommGroup N] [Module R N] :
    (S ⊗[R] M) ⊗[S] (S ⊗[R] N) ≃ₗ[S] S ⊗[R] (M ⊗[R] N) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (S ⊗[R] M) N).trans
    (TensorProduct.AlgebraTensorModule.assoc R R S S M N)

theorem cancelIso_tmul {N : Type*} [AddCommGroup N] [Module R N] (s s' : S) (m : M) (n : N) :
    cancelIso R S M N ((s ⊗ₜ[R] m) ⊗ₜ[S] (s' ⊗ₜ[R] n)) = (s' * s) ⊗ₜ[R] (m ⊗ₜ[R] n) := by
  simp [cancelIso, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem cancelIso_naturality {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') (z : (S ⊗[R] M) ⊗[S] (S ⊗[R] N)) :
    cancelIso R S M N' (((f.baseChange S).lTensor (S ⊗[R] M)) z)
      = (f.lTensor M).lTensor S (cancelIso R S M N z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      induction x with
      | zero => simp
      | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
      | tmul s m =>
          induction y with
          | zero => simp
          | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
          | tmul s' n =>
              rw [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul, cancelIso_tmul, cancelIso_tmul,
                LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]

theorem faithfullyFlat_of_faithfullyFlat_baseChange [Module.FaithfullyFlat R S]
    [Module.FaithfullyFlat S (S ⊗[R] M)] : Module.FaithfullyFlat R M := by
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  constructor
  ·
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ f hf
    rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective R S]
    have hfS : Function.Injective (f.baseChange S) := Module.Flat.lTensor_preserves_injective_linearMap f hf
    have hg : Function.Injective ((f.baseChange S).lTensor (S ⊗[R] M)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hfS
    have hcomp : ((f.lTensor M).lTensor S : S ⊗[R] (M ⊗[R] N) → S ⊗[R] (M ⊗[R] N'))
        = (cancelIso R S M N') ∘ ((f.baseChange S).lTensor (S ⊗[R] M)) ∘ (cancelIso R S M N).symm := by
      funext z
      simp only [Function.comp_apply]
      rw [cancelIso_naturality, LinearEquiv.apply_symm_apply]
    rw [hcomp]
    exact (cancelIso R S M N').injective.comp (hg.comp (cancelIso R S M N).symm.injective)
  ·
    intro I hI hIM
    let J : Ideal S := I.map (algebraMap R S)
    have hJ : J ≠ ⊤ := by
      intro hJ
      have h1 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal R S).mp inferInstance).2 I hI
      apply h1
      have hJ' : Ideal.map (algebraMap R S) I = ⊤ := hJ
      rw [Ideal.smul_top_eq_map, hJ']
      rfl
    have h2 := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal S (S ⊗[R] M)).mp inferInstance).2 J hJ
    apply h2

    have hone : ∀ m : M, (1 : S) ⊗ₜ[R] m ∈ J • (⊤ : Submodule S (S ⊗[R] M)) := by
      intro m
      have hm : m ∈ I • (⊤ : Submodule R M) := by rw [hIM]; exact Submodule.mem_top
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro i hi n _
        have : (1 : S) ⊗ₜ[R] (i • n) = (algebraMap R S i) • ((1 : S) ⊗ₜ[R] n) := by
          rw [TensorProduct.tmul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top
      · intro x y hx hy
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hx hy
    rw [eq_top_iff]
    rintro z -
    induction z with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul s m =>
        have : s ⊗ₜ[R] m = s • ((1 : S) ⊗ₜ[R] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ s (hone m)

end Descent

end S17Ta

namespace S17Ta

section Plumbing

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
variable (k' : Type w) [Field k'] [Algebra k k']

noncomputable abbrev φ : k' ⊗[k] ↥K →ₐ[k'] k' ⊗[k] H := Algebra.TensorProduct.map (AlgHom.id k' k') K.val

noncomputable abbrev K' : Subalgebra k' (k' ⊗[k] H) := (φ K k').range

theorem φ_tmul (c : k') (x : ↥K) : φ K k' (c ⊗ₜ[k] x) = c ⊗ₜ[k] (x : H) := by
  rw [Algebra.TensorProduct.map_tmul]; rfl

theorem tmul_mem (c : k') {y : H} (hy : y ∈ K) : c ⊗ₜ[k] y ∈ K' K k' :=
  ⟨c ⊗ₜ[k] ⟨y, hy⟩, φ_tmul K k' c ⟨y, hy⟩⟩

noncomputable def ι : ↥K →ₐ[k] ↥(K' K k') :=
  (((φ K k').rangeRestrict).restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem ι_apply_coe (x : ↥K) : ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) = (1 : k') ⊗ₜ[k] (x : H) := by
  show φ K k' ((1 : k') ⊗ₜ[k] x) = _
  exact φ_tmul K k' 1 x

end Plumbing

end S17Ta

set_option maxHeartbeats 16000000 in
open S17Ta in
theorem solution
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    (k' : Type w) [Field k'] [Algebra k k']
    (hff : Module.FaithfullyFlat
      ↥((Algebra.TensorProduct.map (AlgHom.id k' k') K.val).range) (k' ⊗[k] H)) :
    Module.FaithfullyFlat ↥K H := by
  classical
  haveI := hff

  letI algKK' : Algebra ↥K ↥(K' K k') := (ι K k').toRingHom.toAlgebra
  have hsmulK' : ∀ (x : ↥K) (κ : ↥(K' K k')), x • κ = ι K k' x * κ := fun _ _ => rfl
  haveI towerk : IsScalarTower k ↥K ↥(K' K k') := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply Subtype.ext
    show algebraMap k (k' ⊗[k] H) c = ((ι K k' (algebraMap k ↥K c) : ↥(K' K k')) : k' ⊗[k] H)
    rw [ι_apply_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

  let g : ↥K →ₗ[↥K] k' →ₗ[k] ↥(K' K k') :=
    LinearMap.mk₂' ↥K k (fun x c => ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩)
      (fun x y c => Subtype.ext (by
        show c ⊗ₜ[k] ((x + y : ↥K) : H) = c ⊗ₜ[k] (x : H) + c ⊗ₜ[k] (y : H)
        rw [Subalgebra.coe_add, TensorProduct.tmul_add]))
      (fun y x c => Subtype.ext (by
        show c ⊗ₜ[k] ((y • x : ↥K) : H) = ((ι K k' y * ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩ : ↥(K' K k')) : k' ⊗[k] H)
        rw [Subalgebra.coe_mul, ι_apply_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul,
          Subalgebra.coe_mul]))
      (fun x c₁ c₂ => Subtype.ext (by
        show (c₁ + c₂) ⊗ₜ[k] (x : H) = c₁ ⊗ₜ[k] (x : H) + c₂ ⊗ₜ[k] (x : H)
        rw [TensorProduct.add_tmul]))
      (fun a x c => Subtype.ext (by
        show (a • c) ⊗ₜ[k] (x : H) = a • (c ⊗ₜ[k] (x : H))
        rw [TensorProduct.smul_tmul']))
  let f : ↥K ⊗[k] k' →ₗ[↥K] ↥(K' K k') := TensorProduct.AlgebraTensorModule.lift g
  have hf : ∀ (x : ↥K) (c : k'), f (x ⊗ₜ[k] c) = ⟨c ⊗ₜ[k] (x : H), tmul_mem K k' c x.2⟩ := fun x c => by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]; rfl
  have hfsurj : Function.Surjective f := by
    have key : ∀ t : k' ⊗[k] ↥K, ∃ s, f s = ⟨φ K k' t, t, rfl⟩ := by
      intro t
      induction t with
      | zero => exact ⟨0, by rw [map_zero]; exact Subtype.ext (show ((0 : ↥(K' K k')) : k' ⊗[k] H) = φ K k' 0 by rw [map_zero]; rfl)⟩
      | tmul c x => exact ⟨x ⊗ₜ[k] c, by rw [hf]; exact Subtype.ext (φ_tmul K k' c x).symm⟩
      | add t₁ t₂ h₁ h₂ =>
          obtain ⟨s₁, hs₁⟩ := h₁
          obtain ⟨s₂, hs₂⟩ := h₂
          exact ⟨s₁ + s₂, by
            rw [map_add, hs₁, hs₂]
            exact Subtype.ext (show φ K k' t₁ + φ K k' t₂ = φ K k' (t₁ + t₂) by rw [map_add])⟩
    rintro ⟨y, t, rfl⟩
    obtain ⟨s, hs⟩ := key t
    exact ⟨s, hs⟩
  have hfval : ∀ s, ((f s : ↥(K' K k')) : k' ⊗[k] H)
      = (K.val.toLinearMap.lTensor k') (TensorProduct.comm k ↥K k' s) := by
    intro s
    induction s with
    | zero => simp
    | add x y hx hy => rw [map_add, Subalgebra.coe_add, hx, hy, map_add, map_add]
    | tmul x c => rw [hf, TensorProduct.comm_tmul, LinearMap.lTensor_tmul]; rfl
  have hfinj : Function.Injective f := by
    intro s₁ s₂ h
    have h' : ((f s₁ : ↥(K' K k')) : k' ⊗[k] H) = f s₂ := congrArg Subtype.val h
    rw [hfval, hfval] at h'
    exact (TensorProduct.comm k ↥K k').injective
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective h')
  let e : ↥K ⊗[k] k' ≃ₗ[↥K] ↥(K' K k') := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  haveI : Module.FaithfullyFlat ↥K ↥(K' K k') := Module.FaithfullyFlat.of_linearEquiv ↥K (↥K ⊗[k] k') e.symm

  letI modKH' : Module ↥K (k' ⊗[k] H) := Module.compHom (k' ⊗[k] H) (ι K k').toRingHom
  have hsmulH' : ∀ (x : ↥K) (z : k' ⊗[k] H), x • z = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * z := fun _ _ => rfl
  haveI : IsScalarTower ↥K ↥(K' K k') (k' ⊗[k] H) :=
    ⟨fun x κ z => by
      show (((ι K k' x * κ : ↥(K' K k')) : k' ⊗[k] H)) * z = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * z)
      rw [Subalgebra.coe_mul, mul_assoc]⟩
  let g' : ↥(K' K k') →ₗ[↥(K' K k')] H →ₗ[↥K] (k' ⊗[k] H) :=
    LinearMap.mk₂' ↥(K' K k') ↥K (fun κ h => (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] h))
      (fun κ₁ κ₂ h => by rw [Subalgebra.coe_add, add_mul])
      (fun κ' κ h => by
        show ((κ' * κ : ↥(K' K k')) : k' ⊗[k] H) * _ = (κ' : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * _)
        rw [Subalgebra.coe_mul, mul_assoc])
      (fun κ h₁ h₂ => by rw [TensorProduct.tmul_add, mul_add])
      (fun x κ h => by
        show (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] ((x : H) * h)) = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * ((κ : k' ⊗[k] H) * _)
        rw [ι_apply_coe, ← mul_one (1 : k'), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        ring)
  let Φ₀ : ↥(K' K k') ⊗[↥K] H →ₗ[↥(K' K k')] (k' ⊗[k] H) := TensorProduct.AlgebraTensorModule.lift g'
  have hΦ₀ : ∀ (κ : ↥(K' K k')) (h : H), Φ₀ (κ ⊗ₜ[↥K] h) = (κ : k' ⊗[k] H) * ((1 : k') ⊗ₜ[k] h) := fun κ h => by
    rw [TensorProduct.AlgebraTensorModule.lift_tmul]; rfl
  have hΦ₀surj : Function.Surjective Φ₀ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro z -
    induction z with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c h =>
        refine ⟨(⟨c ⊗ₜ[k] (1 : H), tmul_mem K k' c K.one_mem⟩ : ↥(K' K k')) ⊗ₜ[↥K] h, ?_⟩
        rw [hΦ₀]
        show (c ⊗ₜ[k] (1 : H)) * ((1 : k') ⊗ₜ[k] h) = c ⊗ₜ[k] h
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  let cK : k' → ↥(K' K k') := fun c => ⟨c ⊗ₜ[k] (1 : H), tmul_mem K k' c K.one_mem⟩
  have cK_zero : cK 0 = 0 := Subtype.ext (TensorProduct.zero_tmul _ (1 : H))
  have cK_add : ∀ c₁ c₂, cK (c₁ + c₂) = cK c₁ + cK c₂ := fun c₁ c₂ => Subtype.ext (TensorProduct.add_tmul c₁ c₂ (1 : H))
  let ψ₂ : k' →+ H →+ (↥(K' K k') ⊗[↥K] H) :=
    { toFun := fun c => (TensorProduct.mk ↥K ↥(K' K k') H (cK c)).toAddMonoidHom
      map_zero' := by
        ext h
        show cK 0 ⊗ₜ[↥K] h = 0
        rw [cK_zero, TensorProduct.zero_tmul]
      map_add' := fun c₁ c₂ => by
        ext h
        show cK (c₁ + c₂) ⊗ₜ[↥K] h = cK c₁ ⊗ₜ[↥K] h + cK c₂ ⊗ₜ[↥K] h
        rw [cK_add, TensorProduct.add_tmul] }
  have cK_smul : ∀ (a : k) (c : k'), (algebraMap k ↥K a) • cK c = cK (a • c) := by
    intro a c
    apply Subtype.ext
    show ((ι K k' (algebraMap k ↥K a) : ↥(K' K k')) : k' ⊗[k] H) * (c ⊗ₜ[k] (1 : H)) = (a • c) ⊗ₜ[k] (1 : H)
    rw [TensorProduct.smul_tmul, ι_apply_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, Algebra.algebraMap_eq_smul_one]
  let Ψ : k' ⊗[k] H →+ (↥(K' K k') ⊗[↥K] H) := TensorProduct.liftAddHom ψ₂ (fun a c h => by
    show cK (a • c) ⊗ₜ[↥K] h = cK c ⊗ₜ[↥K] (a • h)
    have e1 : ((algebraMap k ↥K a) • cK c) ⊗ₜ[↥K] h = cK c ⊗ₜ[↥K] ((algebraMap k ↥K a) • h) :=
      TensorProduct.smul_tmul _ _ _
    have e2 : (algebraMap k ↥K a) • h = a • h := algebraMap_smul (↥K) a h
    rw [← e2, ← e1, cK_smul])
  have hΨ : ∀ (c : k') (h : H), Ψ (c ⊗ₜ[k] h) = cK c ⊗ₜ[↥K] h := fun c h =>
    TensorProduct.liftAddHom_tmul _ _ _ _
  have hL : ∀ (t : k' ⊗[k] ↥K) (h : H),
      Ψ (φ K k' t * ((1 : k') ⊗ₜ[k] h)) = (⟨φ K k' t, t, rfl⟩ : ↥(K' K k')) ⊗ₜ[↥K] h := by
    intro t h
    induction t with
    | zero =>
        have h0 : (⟨φ K k' 0, (0 : k' ⊗[k] ↥K), rfl⟩ : ↥(K' K k')) = 0 := Subtype.ext (map_zero _)
        rw [h0, TensorProduct.zero_tmul, map_zero, zero_mul, map_zero]
    | tmul c x =>
        have h1 : (⟨φ K k' (c ⊗ₜ[k] x), c ⊗ₜ[k] x, rfl⟩ : ↥(K' K k')) = x • cK c := by
          apply Subtype.ext
          show φ K k' (c ⊗ₜ[k] x) = ((ι K k' x : ↥(K' K k')) : k' ⊗[k] H) * (c ⊗ₜ[k] (1 : H))
          rw [φ_tmul, ι_apply_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [h1, φ_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hΨ, TensorProduct.smul_tmul]
        rfl
    | add t₁ t₂ h₁ h₂ =>
        have h2 : (⟨φ K k' (t₁ + t₂), t₁ + t₂, rfl⟩ : ↥(K' K k'))
            = ⟨φ K k' t₁, t₁, rfl⟩ + ⟨φ K k' t₂, t₂, rfl⟩ := Subtype.ext (map_add _ _ _)
        rw [h2, TensorProduct.add_tmul, map_add, add_mul, map_add, h₁, h₂]
  have hΨΦ : ∀ w, Ψ (Φ₀ w) = w := by
    intro w
    induction w with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul κ h =>
        obtain ⟨t, ht⟩ := κ.2
        have hκ : κ = ⟨φ K k' t, t, rfl⟩ := Subtype.ext ht.symm
        rw [hκ, hΦ₀]
        exact hL t h
  have hΦ₀inj : Function.Injective Φ₀ := fun w₁ w₂ h => by
    rw [← hΨΦ w₁, ← hΨΦ w₂, h]
  let Φ : ↥(K' K k') ⊗[↥K] H ≃ₗ[↥(K' K k')] (k' ⊗[k] H) := LinearEquiv.ofBijective Φ₀ ⟨hΦ₀inj, hΦ₀surj⟩
  haveI : Module.FaithfullyFlat ↥(K' K k') (↥(K' K k') ⊗[↥K] H) :=
    Module.FaithfullyFlat.of_linearEquiv ↥(K' K k') (k' ⊗[k] H) Φ

  exact faithfullyFlat_of_faithfullyFlat_baseChange ↥K ↥(K' K k') H

end S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange
end P2MW
export P2MW.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange (solution)
