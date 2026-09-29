-- Prove2me | solution 1 for Submodule.exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a468e2fa-7404-5a4a-b321-2da1cc9fd22f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace

set_option autoImplicit false

open scoped TensorProduct

namespace C4

section ZModLemmas

variable {p : ℕ} [Fact p.Prime] (k : Type*) [Field k]
variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module (ZMod p) M] [Module (ZMod p) M']

theorem baseChange_injective_of_retraction (f : M →+ M') (g : M' →+ M) (hgf : ∀ x, g (f x) = x) :
    Function.Injective (f.toIntLinearMap.baseChange k) := by
  have h : ∀ w, (g.toIntLinearMap.baseChange k) (f.toIntLinearMap.baseChange k w) = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c x => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]; exact congrArg _ (hgf x)
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact fun a b hab => by rw [← h a, ← h b, hab]

theorem baseChange_injective_of_injective (f : M →ₗ[ZMod p] M') (hf : Function.Injective f) :
    Function.Injective (f.toAddMonoidHom.toIntLinearMap.baseChange k) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  exact baseChange_injective_of_retraction k f.toAddMonoidHom g.toAddMonoidHom
    (fun x => LinearMap.congr_fun hg x)

theorem mem_range_baseChange_ker_subtype_of (g : M →ₗ[ZMod p] M') (w : k ⊗[ℤ] M)
    (hw : g.toAddMonoidHom.toIntLinearMap.baseChange k w = 0) :
    w ∈ LinearMap.range ((LinearMap.ker g).subtype.toAddMonoidHom.toIntLinearMap.baseChange k) := by
  classical
  obtain ⟨C, hC⟩ := (LinearMap.ker g).exists_isCompl

  let πK : M →ₗ[ZMod p] ↥(LinearMap.ker g) := Submodule.projectionOnto _ C hC
  let πC : M →ₗ[ZMod p] ↥C := Submodule.projectionOnto C _ hC.symm
  have hdecomp : ∀ x : M, ((πK x : M) + (πC x : M)) = x := fun x =>
    Submodule.projection_add_projection_eq_self hC x

  have hinjC : Function.Injective (g ∘ₗ C.subtype) := by
    intro a b hab
    have : (a : M) - b ∈ LinearMap.ker g ⊓ C := by
      refine Submodule.mem_inf.mpr ⟨?_, C.sub_mem a.2 b.2⟩
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hab
    rw [hC.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext this

  let K := LinearMap.ker g
  let iK : k ⊗[ℤ] ↥K →ₗ[k] k ⊗[ℤ] M := K.subtype.toAddMonoidHom.toIntLinearMap.baseChange k
  let iC : k ⊗[ℤ] ↥C →ₗ[k] k ⊗[ℤ] M := C.subtype.toAddMonoidHom.toIntLinearMap.baseChange k
  let pK : k ⊗[ℤ] M →ₗ[k] k ⊗[ℤ] ↥K := πK.toAddMonoidHom.toIntLinearMap.baseChange k
  let pC : k ⊗[ℤ] M →ₗ[k] k ⊗[ℤ] ↥C := πC.toAddMonoidHom.toIntLinearMap.baseChange k
  let gC : k ⊗[ℤ] ↥C →ₗ[k] k ⊗[ℤ] M' := (g ∘ₗ C.subtype).toAddMonoidHom.toIntLinearMap.baseChange k

  have hsplit : ∀ z : k ⊗[ℤ] M, iK (pK z) + iC (pC z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul c x =>
      simp only [iK, iC, pK, pC, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap,
        LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
      rw [← TensorProduct.tmul_add, hdecomp]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, add_add_add_comm, hx, hy]

  have hgw : ∀ z : k ⊗[ℤ] M, g.toAddMonoidHom.toIntLinearMap.baseChange k z = gC (pC z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c x =>
      simp only [gC, pC, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
        LinearMap.comp_apply, Submodule.subtype_apply]
      congr 1
      conv_lhs => rw [← hdecomp x]
      rw [map_add, (πK x).2, zero_add]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  have hpC : pC w = 0 := by
    apply baseChange_injective_of_injective k (g ∘ₗ C.subtype) hinjC
    rw [map_zero]
    exact (hgw w).symm.trans hw
  refine ⟨pK w, ?_⟩
  have := hsplit w
  rw [hpC, map_zero, add_zero] at this
  exact this

end ZModLemmas

end C4

namespace C4

section Core

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]
variable (k : Type*) [Field k] [Algebra F k]
variable (V : Type*) [AddCommGroup V] [Module F V]

def smK (c : F) : k ⊗[ℤ] V →ₗ[k] k ⊗[ℤ] V := (DistribSMul.toLinearMap ℤ V c).baseChange k

theorem smK_tmul (c : F) (a : k) (v : V) : smK F k V c (a ⊗ₜ[ℤ] v) = a ⊗ₜ[ℤ] (c • v) := by
  rw [smK, LinearMap.baseChange_tmul]; rfl

theorem smK_mul (c d : F) : smK F k V (c * d) = smK F k V c ∘ₗ smK F k V d := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a v => rw [LinearMap.comp_apply, smK_tmul, smK_tmul, smK_tmul, mul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem smK_comm (c d : F) (x : k ⊗[ℤ] V) : smK F k V c (smK F k V d x) = smK F k V d (smK F k V c x) := by
  rw [← LinearMap.comp_apply, ← smK_mul, mul_comm, smK_mul, LinearMap.comp_apply]

def eig : Submodule k (k ⊗[ℤ] V) where
  carrier := {e | ∀ c : F, smK F k V c e = algebraMap F k c • e}
  add_mem' := fun {x y} hx hy c => by rw [map_add, hx c, hy c, smul_add]
  zero_mem' := fun c => by rw [map_zero, smul_zero]
  smul_mem' := fun a x hx c => by
    show smK F k V c (a • x) = algebraMap F k c • (a • x)
    rw [LinearMap.map_smul, hx c, smul_comm]

theorem mem_eig {e : k ⊗[ℤ] V} : e ∈ eig F k V ↔ ∀ c : F, smK F k V c e = algebraMap F k c • e := Iff.rfl

theorem card_units_ne_zero (p : ℕ) [Fact p.Prime] [CharP F p] [CharP k p] : ((Fintype.card Fˣ : ℕ) : k) ≠ 0 := by
  obtain ⟨n, hp, hq⟩ := FiniteField.card F p
  rw [Fintype.card_units, hq]
  have h1 : 1 ≤ p ^ (n : ℕ) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  rw [Nat.cast_sub h1, Nat.cast_pow, CharP.cast_eq_zero k p, zero_pow (PNat.ne_zero n), zero_sub, Nat.cast_one]
  exact neg_ne_zero.mpr one_ne_zero

private def _root_.C4.proj : k ⊗[ℤ] V →ₗ[k] k ⊗[ℤ] V :=
  ((Fintype.card Fˣ : ℕ) : k)⁻¹ • ∑ u : Fˣ, (algebraMap F k ((u⁻¹ : Fˣ) : F)) • smK F k V (u : F)

p2m_export "C4" "proj"
theorem proj_apply (x : k ⊗[ℤ] V) :
    proj F k V x = ((Fintype.card Fˣ : ℕ) : k)⁻¹ • ∑ u : Fˣ, algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V u x := by
  simp only [proj, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

theorem proj_mem_eig (x : k ⊗[ℤ] V) : proj F k V x ∈ eig F k V := by
  intro c
  rw [proj_apply, LinearMap.map_smul, smul_comm (algebraMap F k c)]
  congr 1
  rw [map_sum, Finset.smul_sum]
  by_cases hc : c = 0
  · subst hc
    have h0 : ∀ y : k ⊗[ℤ] V, smK F k V 0 y = 0 := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero]
      | tmul a v => rw [smK_tmul, zero_smul, TensorProduct.tmul_zero]
      | add y z hy hz => rw [map_add, hy, hz, add_zero]
    simp only [h0, map_zero, zero_smul, Finset.sum_const_zero]
  · let cu : Fˣ := Units.mk0 c hc
    have hterm : ∀ u : Fˣ, smK F k V c (algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V u x) =
        algebraMap F k c • (algebraMap F k (((cu * u)⁻¹ : Fˣ) : F) • smK F k V ((cu * u : Fˣ) : F) x) := by
      intro u
      rw [LinearMap.map_smul, ← LinearMap.comp_apply, ← smK_mul, smul_smul]
      congr 1
      · rw [mul_inv_rev, Units.val_mul, map_mul, Units.val_inv_eq_inv_val cu, Units.val_mk0, map_inv₀,
          mul_comm (algebraMap F k ((u⁻¹ : Fˣ) : F)), ← mul_assoc, mul_inv_cancel₀, one_mul]
        exact (map_ne_zero (algebraMap F k)).mpr hc
    calc ∑ u : Fˣ, smK F k V c (algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V u x)
        = ∑ u : Fˣ, algebraMap F k c • (algebraMap F k (((cu * u)⁻¹ : Fˣ) : F) • smK F k V ((cu * u : Fˣ) : F) x) :=
          Finset.sum_congr rfl fun u _ => hterm u
      _ = ∑ u : Fˣ, algebraMap F k c • (algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V (u : F) x) :=
          Fintype.sum_equiv (Equiv.mulLeft cu)
            (fun u => algebraMap F k c • (algebraMap F k (((cu * u)⁻¹ : Fˣ) : F) • smK F k V ((cu * u : Fˣ) : F) x))
            (fun u => algebraMap F k c • (algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V (u : F) x))
            (fun u => rfl)

theorem proj_eq_self_of_mem (hq : ((Fintype.card Fˣ : ℕ) : k) ≠ 0) {e : k ⊗[ℤ] V} (he : e ∈ eig F k V) :
    proj F k V e = e := by
  rw [proj_apply]
  have : ∀ u : Fˣ, algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V u e = e := by
    intro u
    rw [he, smul_smul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_cancel₀, one_smul]
    exact (map_ne_zero (algebraMap F k)).mpr u.ne_zero
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem smK_proj (c : F) (x : k ⊗[ℤ] V) : smK F k V c (proj F k V x) = algebraMap F k c • proj F k V x :=
  proj_mem_eig F k V x c

theorem proj_smK (c : F) (x : k ⊗[ℤ] V) : proj F k V (smK F k V c x) = smK F k V c (proj F k V x) := by
  rw [proj_apply, proj_apply, LinearMap.map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.map_smul, smK_comm]

def quo : k ⊗[ℤ] V →ₗ[k] k ⊗[F] V := TensorProduct.mapOfCompatibleSMul F ℤ k k V

theorem quo_tmul (a : k) (v : V) : quo F k V (a ⊗ₜ[ℤ] v) = a ⊗ₜ[F] v := rfl

def projOne : V →ₗ[F] k ⊗[ℤ] V where
  toFun v := proj F k V ((1 : k) ⊗ₜ[ℤ] v)
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]
  map_smul' c v := by
    rw [RingHom.id_apply, ← smK_tmul, proj_smK, smK_proj, algebraMap_smul]

theorem projOne_apply (v : V) : projOne F k V v = proj F k V ((1 : k) ⊗ₜ[ℤ] v) := rfl

def sec : k ⊗[F] V →ₗ[k] k ⊗[ℤ] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a => a • projOne F k V
      map_add' := fun a b => add_smul a b _
      map_smul' := fun a b => by rw [RingHom.id_apply, smul_eq_mul, mul_smul] }

theorem sec_tmul (a : k) (v : V) : sec F k V (a ⊗ₜ[F] v) = a • proj F k V ((1 : k) ⊗ₜ[ℤ] v) := by
  rw [sec, TensorProduct.AlgebraTensorModule.lift_tmul]; rfl

theorem quo_proj_one_tmul (hq : ((Fintype.card Fˣ : ℕ) : k) ≠ 0) (v : V) :
    quo F k V (proj F k V ((1 : k) ⊗ₜ[ℤ] v)) = (1 : k) ⊗ₜ[F] v := by
  rw [proj_apply, LinearMap.map_smul, map_sum]
  have : ∀ u : Fˣ, quo F k V (algebraMap F k ((u⁻¹ : Fˣ) : F) • smK F k V u ((1 : k) ⊗ₜ[ℤ] v)) =
      (1 : k) ⊗ₜ[F] v := by
    intro u
    have h1 : (((u : F) • (1 : k)) ⊗ₜ[F] v) = algebraMap F k u • ((1 : k) ⊗ₜ[F] v) := by
      rw [Algebra.smul_def, mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.map_smul, smK_tmul, quo_tmul, ← TensorProduct.smul_tmul, h1, smul_smul,
      Units.val_inv_eq_inv_val, map_inv₀, inv_mul_cancel₀ ((map_ne_zero (algebraMap F k)).mpr u.ne_zero), one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem quo_sec (hq : ((Fintype.card Fˣ : ℕ) : k) ≠ 0) (x : k ⊗[F] V) : quo F k V (sec F k V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a v =>
    rw [sec_tmul, LinearMap.map_smul, quo_proj_one_tmul F k V hq, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sec_quo (x : k ⊗[ℤ] V) : sec F k V (quo F k V x) = proj F k V x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a v =>
    rw [quo_tmul, sec_tmul, ← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem sec_mem_eig (x : k ⊗[F] V) : sec F k V x ∈ eig F k V := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul a v => rw [sec_tmul]; exact Submodule.smul_mem _ a (proj_mem_eig F k V _)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem sec_injective (hq : ((Fintype.card Fˣ : ℕ) : k) ≠ 0) : Function.Injective (sec F k V) := fun x y h => by
  rw [← quo_sec F k V hq x, ← quo_sec F k V hq y, h]

theorem range_sec (hq : ((Fintype.card Fˣ : ℕ) : k) ≠ 0) : LinearMap.range (sec F k V) = eig F k V := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact sec_mem_eig F k V x
  · intro e he
    exact ⟨quo F k V e, by rw [sec_quo, proj_eq_self_of_mem F k V hq he]⟩

end Core

end C4

namespace C4

section Aux

variable (k : Type*) [Field k]

theorem piRight_baseChange_apply {M : Type*} [AddCommGroup M] {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {N : ι' → Type*} [∀ i, AddCommGroup (N i)] (f : M →ₗ[ℤ] (∀ i, N i)) (w : k ⊗[ℤ] M) (i : ι') :
    TensorProduct.piRight ℤ k k N (f.baseChange k w) i = ((LinearMap.proj i ∘ₗ f).baseChange k) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

def commonKer {M : Type*} [AddCommGroup M] (T : Set (M →+ M)) : AddSubgroup M where
  carrier := {u | ∀ t ∈ T, t u = 0}
  add_mem' := fun {x y} hx hy t ht => by rw [map_add, hx t ht, hy t ht, add_zero]
  zero_mem' := fun t _ => map_zero t
  neg_mem' := fun {x} hx t ht => by rw [map_neg, hx t ht, neg_zero]

theorem mem_commonKer {M : Type*} [AddCommGroup M] (T : Set (M →+ M)) (u : M) :
    u ∈ commonKer T ↔ ∀ t ∈ T, t u = 0 := Iff.rfl

theorem mem_range_baseChange_commonKer (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (T : Set (M →+ M)) [Finite ↥T] (w : k ⊗[ℤ] M)
    (hw : ∀ t ∈ T, (t : M →+ M).toIntLinearMap.baseChange k w = 0) :
    w ∈ LinearMap.range ((commonKer T).subtype.toIntLinearMap.baseChange k) := by
  classical
  letI : Fintype ↥T := Fintype.ofFinite _
  let gA : M →+ (↥T → M) :=
    { toFun := fun u t => t.1 u
      map_zero' := by funext t; exact map_zero t.1
      map_add' := fun x y => by funext t; exact map_add t.1 x y }
  let g : M →ₗ[ZMod p] (↥T → M) := gA.toZModLinearMap p
  have hker : ∀ u : M, u ∈ LinearMap.ker g ↔ u ∈ commonKer T := by
    intro u
    rw [LinearMap.mem_ker, mem_commonKer]
    constructor
    · intro h t ht
      exact congrFun h ⟨t, ht⟩
    · intro h
      funext t
      exact h t.1 t.2
  have hgw : g.toAddMonoidHom.toIntLinearMap.baseChange k w = 0 := by
    apply (TensorProduct.piRight ℤ k k (fun _ : ↥T => M)).injective
    rw [map_zero]
    funext t
    rw [Pi.zero_apply, piRight_baseChange_apply]
    have h1 : (LinearMap.proj t ∘ₗ g.toAddMonoidHom.toIntLinearMap) = (t.1 : M →+ M).toIntLinearMap := by
      apply LinearMap.ext; intro u; rfl
    rw [h1]
    exact hw t.1 t.2
  obtain ⟨z, hz⟩ := mem_range_baseChange_ker_subtype_of k g w hgw
  let θ : ↥(LinearMap.ker g) →+ ↥(commonKer T) :=
    { toFun := fun u => ⟨(u : M), (hker u).mp u.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have htr : ∀ z : k ⊗[ℤ] ↥(LinearMap.ker g), ((commonKer T).subtype.toIntLinearMap.baseChange k)
      ((θ.toIntLinearMap.baseChange k) z) = ((LinearMap.ker g).subtype.toAddMonoidHom.toIntLinearMap.baseChange k) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c u => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  exact ⟨(θ.toIntLinearMap.baseChange k) z, by rw [htr, hz]⟩

end Aux

end C4

open Submodule in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open scoped TensorProduct in
theorem solution
    {A : Type*} [CommRing A] {J : Type*} [AddCommGroup J] [Module A J]
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (I 𝔪 : Ideal A) [𝔪.IsMaximal] (hI : I ≤ 𝔪) (hp : (p : A) ∈ I)
    (hfin : Finite ↥(Submodule.torsionBySet A J (I : Set A)))
    (ι : A ⧸ 𝔪 →+* k) :
    letI := ι.toAlgebra
    ∃ j : k ⊗[A ⧸ 𝔪] ↥(Submodule.torsionBySet A J (𝔪 : Set A)) →ₗ[k]
        k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
      Function.Injective j ∧
      ∀ w : k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
        w ∈ LinearMap.range j ↔
          ∀ a : A,
            ((DistribSMul.toLinearMap ℤ ↥(Submodule.torsionBySet A J (I : Set A)) a).baseChange k) w =
              ι (Ideal.Quotient.mk 𝔪 a) • w := by
  letI := ι.toAlgebra
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  classical

  let U := ↥(Submodule.torsionBySet A J (I : Set A))
  let V := ↥(Submodule.torsionBySet A J (𝔪 : Set A))
  have hVU : Submodule.torsionBySet A J (𝔪 : Set A) ≤ Submodule.torsionBySet A J (I : Set A) :=
    Submodule.torsionBySet_le_torsionBySet_of_subset (fun a ha => hI ha)
  haveI : Finite V := Finite.of_injective (Submodule.inclusion hVU) (Submodule.inclusion_injective hVU)
  have halg : ∀ c : A ⧸ 𝔪, algebraMap (A ⧸ 𝔪) k c = ι c := fun c => rfl

  have hpU : ∀ u : U, p • u = 0 := by
    intro u
    rw [← Nat.cast_smul_eq_nsmul A]
    apply Subtype.ext
    rw [Submodule.coe_smul, ZeroMemClass.coe_zero]
    exact (Submodule.mem_torsionBySet_iff _ _).mp u.2 ⟨(p : A), hp⟩
  have hpV : ∀ v : V, p • v = 0 := by
    intro v
    have := hpU (Submodule.inclusion hVU v)
    rw [← map_nsmul] at this
    exact Submodule.inclusion_injective hVU (by rw [this, map_zero])
  letI mU : Module (ZMod p) U := AddCommGroup.zmodModule hpU
  letI mV : Module (ZMod p) V := AddCommGroup.zmodModule hpV

  let incl : V →+ U := (Submodule.inclusion hVU).toAddMonoidHom
  let inclZ : V →ₗ[ZMod p] U := incl.toZModLinearMap p
  let inclK : k ⊗[ℤ] V →ₗ[k] k ⊗[ℤ] U := incl.toIntLinearMap.baseChange k
  have inclK_tmul : ∀ (c : k) (v : V), inclK (c ⊗ₜ[ℤ] v) = c ⊗ₜ[ℤ] (Submodule.inclusion hVU v) := fun c v => rfl
  have hinclK : Function.Injective inclK :=
    C4.baseChange_injective_of_injective k inclZ (Submodule.inclusion_injective hVU)

  let opU : A → (k ⊗[ℤ] U →ₗ[k] k ⊗[ℤ] U) := fun a => (DistribSMul.toLinearMap ℤ U a).baseChange k
  let opV : A → (k ⊗[ℤ] V →ₗ[k] k ⊗[ℤ] V) := fun a => (DistribSMul.toLinearMap ℤ V a).baseChange k
  have hopU : ∀ a, opU a = (DistribSMul.toLinearMap ℤ U a).baseChange k := fun a => rfl
  have hnat : ∀ (a : A) (x : k ⊗[ℤ] V), opU a (inclK x) = inclK (opV a x) := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c v =>
      rw [inclK_tmul, hopU, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, inclK_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hopV : ∀ a : A, opV a = C4.smK (A ⧸ 𝔪) k V (Ideal.Quotient.mk 𝔪 a) := by
    intro a
    show (DistribSMul.toLinearMap ℤ V a).baseChange k =
      (DistribSMul.toLinearMap ℤ V (Ideal.Quotient.mk 𝔪 a)).baseChange k
    have hlin : DistribSMul.toLinearMap ℤ V a = DistribSMul.toLinearMap ℤ V (Ideal.Quotient.mk 𝔪 a) := by
      apply LinearMap.ext
      intro v
      rfl
    rw [hlin]

  have step2 : ∀ w : k ⊗[ℤ] U, (∀ a : A, opU a w = ι (Ideal.Quotient.mk 𝔪 a) • w) →
      w ∈ LinearMap.range inclK := by
    intro w hw
    haveI : Finite U := hfin
    haveI : Finite (U →+ U) := Finite.of_injective (fun f : U →+ U => (f : U → U)) DFunLike.coe_injective
    let T : Set (U →+ U) := Set.range fun a : ↥𝔪 => DistribSMul.toAddMonoidHom U (a : A)
    have hwT : ∀ t ∈ T, (t : U →+ U).toIntLinearMap.baseChange k w = 0 := by
      rintro t ⟨a, rfl⟩
      have h1 : (DistribSMul.toAddMonoidHom U (a : A)).toIntLinearMap = DistribSMul.toLinearMap ℤ U (a : A) :=
        LinearMap.ext fun _ => rfl
      rw [h1, ← hopU, hw a, Ideal.Quotient.eq_zero_iff_mem.mpr a.2, map_zero, zero_smul]
    obtain ⟨z, hz⟩ := C4.mem_range_baseChange_commonKer k p T w hwT

    have hKV : ∀ u : U, u ∈ C4.commonKer T → ((u : U) : J) ∈ Submodule.torsionBySet A J (𝔪 : Set A) := by
      intro u hu
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      have := hu _ ⟨⟨a, a.2⟩, rfl⟩
      exact congrArg Subtype.val this
    let θ : ↥(C4.commonKer T) →+ V :=
      { toFun := fun u => ⟨((u : U) : J), hKV u u.2⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have htr : ∀ z : k ⊗[ℤ] ↥(C4.commonKer T), inclK ((θ.toIntLinearMap.baseChange k) z) =
        ((C4.commonKer T).subtype.toIntLinearMap.baseChange k) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c u => rw [LinearMap.baseChange_tmul, inclK_tmul]; rfl
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    exact ⟨(θ.toIntLinearMap.baseChange k) z, by rw [htr, hz]⟩

  by_cases hV : Nontrivial V
  ·
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    haveI : Finite (A ⧸ 𝔪) := Finite.of_injective (fun c : A ⧸ 𝔪 => c • v₀) (smul_left_injective _ hv₀)
    letI : Fintype (A ⧸ 𝔪) := Fintype.ofFinite _
    have h0 : ((p : ℕ) : A ⧸ 𝔪) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
      exact hI hp
    haveI : CharP (A ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0
    have hq := C4.card_units_ne_zero (A ⧸ 𝔪) k p
    refine ⟨inclK ∘ₗ C4.sec (A ⧸ 𝔪) k V, hinclK.comp (C4.sec_injective (A ⧸ 𝔪) k V hq), fun w => ⟨?_, ?_⟩⟩
    · rintro ⟨x, rfl⟩ a
      have he := C4.sec_mem_eig (A ⧸ 𝔪) k V x (Ideal.Quotient.mk 𝔪 a)
      rw [LinearMap.comp_apply, hnat, hopV, he, LinearMap.map_smul, halg]
    · intro hw
      obtain ⟨e, rfl⟩ := step2 w hw
      have he : e ∈ C4.eig (A ⧸ 𝔪) k V := by
        intro c
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        apply hinclK
        rw [← hopV, ← hnat, hw a, LinearMap.map_smul, halg]
      refine ⟨C4.quo (A ⧸ 𝔪) k V e, ?_⟩
      rw [LinearMap.comp_apply, C4.sec_quo, C4.proj_eq_self_of_mem (A ⧸ 𝔪) k V hq he]
  ·
    rw [not_nontrivial_iff_subsingleton] at hV
    have hV0 : ∀ x : k ⊗[ℤ] V, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul c v => rw [Subsingleton.elim v 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    have hT0 : ∀ x : k ⊗[A ⧸ 𝔪] V, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul c v => rw [Subsingleton.elim v 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    refine ⟨0, fun x y _ => by rw [hT0 x, hT0 y], fun w => ⟨?_, ?_⟩⟩
    · rintro ⟨x, rfl⟩ a
      rw [LinearMap.zero_apply, map_zero, smul_zero]
    · intro hw
      obtain ⟨e, rfl⟩ := step2 w hw
      exact ⟨0, by simp only [hV0 e, map_zero]⟩

end S_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
end P2MW
export P2MW.S_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace (solution)
