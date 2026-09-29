-- Prove2me | solution 1 for PDivisibleGroup.Tower.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/51fc5b08-7900-5c5e-9b66-ce299f378794

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
import Theorems.Thm_HopfAlgebra_isHopfGalois_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w x

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv PDivisibleGroup

namespace PDivTowerIsog

section J

variable {R : Type u} [CommRing R] {p h : ℕ}
variable {L : ℕ → Type v} [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]
variable [∀ w, Coalgebra.IsCocomm R (L w)]
variable (t : ∀ w, L (w + 1) →ₐc[R] L w) (ht : ∀ w, Function.Surjective (t w))
variable (hkerL : ∀ w, RingHom.ker (t w) = Hopf.torsionIdeal R (L (w + 1)) (p ^ w))
variable (v u : ℕ)

abbrev iAlg : L (v + u) →ₐ[R] L v := (Tower.transitionLE t v u : L (v + u) →ₐ[R] L v)

include ht in
theorem iAlg_surjective : Function.Surjective (iAlg t v u) := Tower.transitionLE_surjective t ht v u

include ht hkerL in
theorem ker_iAlg_le_ker_nsmulAlgHom :
    RingHom.ker (iAlg t v u).toRingHom ≤
      RingHom.ker (Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).toRingHom := by
  intro a ha
  have ha' : a ∈ Hopf.torsionIdeal R (L (v + u)) (p ^ v) := by
    rw [← Tower.ker_transitionLE ht hkerL v u]; exact ha
  have hle : Hopf.torsionIdeal R (L (v + u)) (p ^ v) ≤
      RingHom.ker (Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).toRingHom := by
    rw [Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
    intro b hb
    change Hopf.nsmulAlgHom R _ (p ^ u) (Hopf.nsmulAlgHom R _ (p ^ v) b) = 0
    rw [Hopf.nsmulAlgHom_nsmulAlgHom_apply, ← pow_add, add_comm u v,
      Tower.nsmulAlgHom_pow_apply ht hkerL (v + u), (Hopf.mem_augIdeal_iff R _ b).1 hb, map_zero]
  exact hle ha'

def jAlg : L v →ₐ[R] L (v + u) :=
  AlgHom.liftOfSurjective (iAlg t v u) (iAlg_surjective t ht v u)
    (Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)) (ker_iAlg_le_ker_nsmulAlgHom t ht hkerL v u)

theorem jAlg_comp_iAlg :
    (jAlg t ht hkerL v u).comp (iAlg t v u) = Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) :=
  AlgHom.liftOfSurjective_comp _ _ _ _

@[scoped simp] theorem jAlg_iAlg (a : L (v + u)) :
    jAlg t ht hkerL v u (Tower.transitionLE t v u a) = Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a :=
  DFunLike.congr_fun (jAlg_comp_iAlg t ht hkerL v u) a

include ht in
theorem algHom_eq_of_comp_iAlg_eq {X : Type x} [Semiring X] [Algebra R X]
    {f g : L v →ₐ[R] X} (hfg : f.comp (iAlg t v u) = g.comp (iAlg t v u)) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := iAlg_surjective t ht v u b
  exact DFunLike.congr_fun hfg a

theorem counitAlgHom_comp_jAlg :
    (counitAlgHom R (L (v + u))).comp (jAlg t ht hkerL v u) = counitAlgHom R (L v) := by
  apply algHom_eq_of_comp_iAlg_eq t ht v u
  rw [AlgHom.comp_assoc, jAlg_comp_iAlg]
  refine AlgHom.ext fun a => ?_
  change counit (R := R) (Hopf.nsmulAlgHom R _ (p ^ u) a) = counit (R := R) (Tower.transitionLE t v u a)
  rw [Hopf.counit_nsmulAlgHom, Tower.counit_transitionLE]

theorem map_comp_comulAlgHom_jAlg :
    (Algebra.TensorProduct.map (jAlg t ht hkerL v u) (jAlg t ht hkerL v u)).comp (comulAlgHom R (L v)) =
      (comulAlgHom R (L (v + u))).comp (jAlg t ht hkerL v u) := by
  apply algHom_eq_of_comp_iAlg_eq t ht v u
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, jAlg_comp_iAlg,
    ← BialgHom.map_comp_comulAlgHom (Tower.transitionLE t v u), ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp, jAlg_comp_iAlg]
  exact Hopf.map_comp_comulAlgHom_nsmulAlgHom R (L (v + u)) (p ^ u)

def jB : L v →ₐc[R] L (v + u) :=
  BialgHom.ofAlgHom (jAlg t ht hkerL v u) (counitAlgHom_comp_jAlg t ht hkerL v u)
    (map_comp_comulAlgHom_jAlg t ht hkerL v u)

theorem toAlgHom_jB : (jB t ht hkerL v u : L v →ₐ[R] L (v + u)) = jAlg t ht hkerL v u := rfl

end J

section Sub

variable {R : Type u} [CommRing R] {p h : ℕ}
variable {L : ℕ → Type v} [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]
variable [∀ w, Coalgebra.IsCocomm R (L w)]
variable (t : ∀ w, L (w + 1) →ₐc[R] L w) (ht : ∀ w, Function.Surjective (t w))
variable (hkerL : ∀ w, RingHom.ker (t w) = Hopf.torsionIdeal R (L (w + 1)) (p ^ w))
variable (v u : ℕ)
variable {B : Type w} [CommRing B] [HopfAlgebra R B]
variable (π : L (v + u) →ₐc[R] B) (hπ : Function.Surjective π)
variable (hkerπ : RingHom.ker (π : L (v + u) →ₐ[R] B) = Hopf.torsionIdeal R (L (v + u)) (p ^ u))

include hπ hkerπ in

theorem pi_comp_jAlg :
    (π : L (v + u) →ₐ[R] B).comp (jAlg t ht hkerL v u) =
      (Algebra.ofId R B).comp (counitAlgHom R (L v)) := by
  apply algHom_eq_of_comp_iAlg_eq t ht v u
  rw [AlgHom.comp_assoc, jAlg_comp_iAlg, ← Hopf.nsmulAlgHom_comp_bialgHom π (p ^ u),
    Hopf.nsmulAlgHom_eq_of_ker_eq_torsionIdeal π hπ (p ^ u) hkerπ, AlgHom.comp_assoc, AlgHom.comp_assoc]
  congr 1
  rw [BialgHom.counitAlgHom_comp]
  refine AlgHom.ext fun a => ?_
  change counit (R := R) a = counit (R := R) (Tower.transitionLE t v u a)
  rw [Tower.counit_transitionLE]

abbrev C : Subalgebra R (L (v + u)) := HopfAlgebra.hopfKer π

include hπ hkerπ in
theorem jAlg_mem_C (b : L v) : jAlg t ht hkerL v u b ∈ C v u π := by
  rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply]
  have hcomul : comul (R := R) (jAlg t ht hkerL v u b) =
      Algebra.TensorProduct.map (jAlg t ht hkerL v u) (jAlg t ht hkerL v u) (comul (R := R) b) := by
    have h := DFunLike.congr_fun (map_comp_comulAlgHom_jAlg t ht hkerL v u) b
    exact h.symm
  rw [hcomul, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, pi_comp_jAlg t ht hkerL v u π hπ hkerπ,
    AlgHom.id_comp]
  have key : ∀ z : L v ⊗[R] L v,
      Algebra.TensorProduct.map (jAlg t ht hkerL v u) ((Algebra.ofId R B).comp (counitAlgHom R (L v))) z =
        Algebra.TensorProduct.map (jAlg t ht hkerL v u) (Algebra.ofId R B)
          ((LinearMap.lTensor (L v) (counit (R := R) (A := L v))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key, Coalgebra.lTensor_counit_comul, Algebra.TensorProduct.map_tmul, map_one]

def jC : L v →ₐ[R] ↥(C v u π) :=
  (jAlg t ht hkerL v u).codRestrict (C v u π) (jAlg_mem_C t ht hkerL v u π hπ hkerπ)

@[scoped simp] theorem coe_jC (b : L v) : (jC t ht hkerL v u π hπ hkerπ b : L (v + u)) = jAlg t ht hkerL v u b := rfl

variable {T : Type x} [CommRing T] [Algebra R T]

omit [Algebra R T] in
theorem lift_comp_right {A B₀ B' : Type*} [CommRing A] [CommRing B₀] [CommRing B'] [Algebra R A]
    [Algebra R B₀] [Algebra R B'] [Algebra R T] (f : A →ₐ[R] T) (g : B₀ →ₐ[R] T) (ρ : B' →ₐ[R] B₀) :
    Algebra.TensorProduct.lift f (g.comp ρ) (fun _ _ => .all _ _) =
      (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) ρ) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

include hπ hkerπ in

theorem apply_eq_of_comp_jAlg_eq (x y : L (v + u) →ₐ[R] T)
    (hxy : x.comp (jAlg t ht hkerL v u) = y.comp (jAlg t ht hkerL v u)) {c : L (v + u)}
    (hc : c ∈ C v u π) : x c = y c := by
  have hy : IsUnit (toConv y) := HopfAlgebra.isUnit_toConv_algHom y
  set z : WithConv (L (v + u) →ₐ[R] T) := toConv x * ↑(hy.unit⁻¹) with hz_def
  have hxz : toConv x = toConv y * z := by
    rw [hz_def, mul_left_comm, Units.mul_inv_of_eq hy.unit_spec, mul_one]
  let Φ := HopfAlgebra.convCompMonoidHom T (jB t ht hkerL v u)
  have hΦxy : Φ (toConv x) = Φ (toConv y) := by
    change toConv (x.comp (jB t ht hkerL v u : L v →ₐ[R] L (v + u))) =
      toConv (y.comp (jB t ht hkerL v u : L v →ₐ[R] L (v + u)))
    rw [toAlgHom_jB, hxy]
  have hΦz : Φ z = 1 := by
    rw [hz_def, map_mul, hΦxy, ← map_mul, Units.mul_inv_of_eq hy.unit_spec, map_one]
  have hzp : z ^ (p ^ u) = 1 := by
    have h1 : z ^ (p ^ u) = toConv (z.ofConv.comp (Hopf.nsmulAlgHom R (L (v + u)) (p ^ u))) := by
      conv_lhs => rw [← toConv_ofConv z]
      exact Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom z.ofConv (p ^ u)
    have h2 : z.ofConv.comp (jAlg t ht hkerL v u) = (1 : WithConv (L v →ₐ[R] T)).ofConv := by
      have := congrArg WithConv.ofConv hΦz
      exact this
    rw [h1, ← jAlg_comp_iAlg t ht hkerL v u, ← AlgHom.comp_assoc, h2, AlgHom.convOne_def, ofConv_toConv,
      AlgHom.comp_assoc]
    change toConv ((Algebra.ofId R T).comp ((counitAlgHom R (L v)).comp
      (Tower.transitionLE t v u : L (v + u) →ₐ[R] L v))) = 1
    rw [BialgHom.counitAlgHom_comp]
    rfl
  obtain ⟨z₁, hz₁⟩ := Hopf.exists_comp_eq_of_pow_eq_one π hπ (p ^ u) hkerπ z hzp
  have hx : x c = (toConv y * z).ofConv c := by rw [← hxz]
  rw [hx, AlgHom.convMul_apply, ← hz₁, lift_comp_right, AlgHom.comp_apply]
  have hco : Algebra.TensorProduct.map (AlgHom.id R (L (v + u)))
      (π : L (v + u) →ₐ[R] B) (comul (R := R) c) = c ⊗ₜ[R] 1 := hc
  rw [hco, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

variable [Module.Finite R B] [Module.Free R B]
variable [∀ w, Module.Free R (L w)] [∀ w, Module.Finite R (L w)]

include hπ hkerπ in

theorem jC_surjective : Function.Surjective (jC t ht hkerL v u π hπ hkerπ) := by
  obtain ⟨⟨r, hr⟩, hfin, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  letI : Algebra (L v) (L (v + u)) := (jAlg t ht hkerL v u).toRingHom.toAlgebra
  haveI : IsScalarTower R (L v) (L (v + u)) :=
    IsScalarTower.of_algebraMap_eq fun x => ((jAlg t ht hkerL v u).commutes x).symm
  letI : Algebra (L v) ↥(C v u π) := (jC t ht hkerL v u π hπ hkerπ).toRingHom.toAlgebra
  haveI : IsScalarTower R (L v) ↥(C v u π) :=
    IsScalarTower.of_algebraMap_eq fun x => ((jC t ht hkerL v u π hπ hkerπ).commutes x).symm
  haveI : Module.Finite R ↥(C v u π) := hfin
  haveI : Module.Finite (L v) ↥(C v u π) := Module.Finite.of_restrictScalars_finite R _ _
  have hr_smul : ∀ (s : L v) (a : L (v + u)), r (s • a) = s • r a := by
    intro s a
    have h1 : s • a = (jC t ht hkerL v u π hπ hkerπ s) • a := rfl
    rw [h1, LinearMap.map_smul]
    rfl
  let rS : L (v + u) →ₗ[L v] ↥(C v u π) :=
    { toFun := r, map_add' := fun a b => r.map_add a b, map_smul' := hr_smul }
  have hepi : Algebra.IsEpi (L v) ↥(C v u π) := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro c
    let T' := L (v + u) ⊗[L v] L (v + u)
    let x : L (v + u) →ₐ[R] T' := Algebra.TensorProduct.includeLeft
    let y : L (v + u) →ₐ[R] T' :=
      (Algebra.TensorProduct.includeRight : L (v + u) →ₐ[L v] T').restrictScalars R
    have hxy : x.comp (jAlg t ht hkerL v u) = y.comp (jAlg t ht hkerL v u) := by
      refine AlgHom.ext fun s => ?_
      change (algebraMap (L v) (L (v + u)) s) ⊗ₜ[L v] (1 : L (v + u)) =
        (1 : L (v + u)) ⊗ₜ[L v] (algebraMap (L v) (L (v + u)) s)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have key : (c : L (v + u)) ⊗ₜ[L v] (1 : L (v + u)) = (1 : L (v + u)) ⊗ₜ[L v] (c : L (v + u)) :=
      apply_eq_of_comp_jAlg_eq t ht hkerL v u π hπ hkerπ x y hxy c.2
    have h1 : r (1 : L (v + u)) = 1 := hr 1
    have := congrArg (TensorProduct.map rS rS) key
    simp only [TensorProduct.map_tmul] at this
    change r (c : L (v + u)) ⊗ₜ[L v] r 1 = r 1 ⊗ₜ[L v] r (c : L (v + u)) at this
    rw [hr c, h1] at this
    exact this.symm
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

variable (hrankL : ∀ w, Module.finrank R (L w) = p ^ (w * h))
variable (hrankB : Module.finrank R B = p ^ (u * h))

theorem nontrivial_level [Nontrivial R] (w : ℕ) : Nontrivial (L w) := by
  by_contra hA
  rw [not_nontrivial_iff_subsingleton] at hA
  have h1 : counit (R := R) (1 : L w) = 1 := Bialgebra.counit_one
  rw [Subsingleton.elim (1 : L w) 0, map_zero] at h1
  exact zero_ne_one h1

include L hrankL in
theorem pow_h_ne_zero [Nontrivial R] : p ^ h ≠ 0 := by
  haveI := nontrivial_level (R := R) (L := L) 1
  intro h0
  have h1 := hrankL 1
  rw [one_mul, h0, Module.finrank_eq_zero_iff_of_free] at h1
  exact false_of_nontrivial_of_subsingleton (L 1)

omit [CommRing R] in
theorem nontrivial_of_primeSpectrum [CommRing R] (𝔭 : PrimeSpectrum R) : Nontrivial R := by
  by_contra hR
  rw [not_nontrivial_iff_subsingleton] at hR
  exact 𝔭.2.ne_top (Subsingleton.elim _ _)

include hπ hrankL hrankB in

theorem rankAtStalk_C (𝔭 : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ↥(C v u π) 𝔭 = p ^ (v * h) := by
  obtain ⟨-, -, -, hrank⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  haveI := nontrivial_of_primeSpectrum 𝔭
  have h1 := hrank 𝔭
  rw [hrankB, hrankL (v + u), add_mul, pow_add] at h1
  have hpos : 0 < p ^ (u * h) := by
    rw [mul_comm, pow_mul]
    exact Nat.pos_of_ne_zero (pow_ne_zero _ (pow_h_ne_zero (R := R) (L := L) hrankL))
  exact Nat.eq_of_mul_eq_mul_right hpos h1

include hrankL hrankB in
theorem jC_injective : Function.Injective (jC t ht hkerL v u π hπ hkerπ) := by
  obtain ⟨-, hfin, hproj, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  haveI := hfin
  haveI := hproj
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (L v) := Module.subsingleton R _
    exact fun a b _ => Subsingleton.elim a b
  let f : L v →ₗ[R] ↥(C v u π) := (jC t ht hkerL v u π hπ hkerπ).toLinearMap
  have hf : Function.Surjective f := jC_surjective t ht hkerL v u π hπ hkerπ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfσ : ∀ c, f (σ c) = c := fun c => DFunLike.congr_fun hσ c
  have hσinj : Function.Injective σ := Function.LeftInverse.injective hfσ
  let K : Submodule R (L v) := LinearMap.ker f
  let s : L v →ₗ[R] ↥K :=
    LinearMap.codRestrict K (LinearMap.id - σ.comp f) fun x => by
      change f (x - σ (f x)) = 0
      rw [map_sub, hfσ, sub_self]
  have hsK : s.comp K.subtype = LinearMap.id := by
    refine LinearMap.ext fun k => Subtype.ext ?_
    change (k : L v) - σ (f k) = k
    rw [show f k = 0 from k.2, map_zero, sub_zero]
  haveI : Module.Projective R ↥K := Module.Projective.of_split K.subtype s hsK
  haveI : Module.Finite R ↥K :=
    Module.Finite.of_surjective s fun k => ⟨k, DFunLike.congr_fun hsK k⟩
  let P : Submodule R (L v) := LinearMap.range σ
  let π' : L v →ₗ[R] ↥P :=
    LinearMap.codRestrict P (σ.comp f) fun x => LinearMap.mem_range_self σ (f x)
  have hπ' : ∀ x : ↥P, π' x = x := by
    rintro ⟨x, ⟨c, rfl⟩⟩
    refine Subtype.ext ?_
    change σ (f (σ c)) = σ c
    rw [hfσ]
  have hcompl : IsCompl P (LinearMap.ker π') := LinearMap.isCompl_of_proj hπ'
  have hkerπ' : LinearMap.ker π' = K := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      have hx' : σ (f x) = 0 := congrArg Subtype.val hx
      rw [← map_zero σ] at hx'
      exact hσinj hx'
    · intro hx
      refine Subtype.ext ?_
      change σ (f x) = 0
      rw [show f x = 0 from hx, map_zero]
  let e : L v ≃ₗ[R] ↥(C v u π) × ↥K :=
    (Submodule.prodEquivOfIsCompl P (LinearMap.ker π') hcompl).symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.ofInjective σ hσinj).symm
        (LinearEquiv.ofEq _ _ hkerπ'))
  have hK : Module.rankAtStalk (R := R) ↥K = 0 := by
    funext 𝔭
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv e) 𝔭
    rw [Module.rankAtStalk_prod, Module.rankAtStalk_eq_finrank_of_free, hrankL v] at h1
    have h2 : Module.rankAtStalk (R := R) ↥(C v u π) 𝔭 = p ^ (v * h) :=
      rankAtStalk_C v u π hπ hrankL hrankB 𝔭
    change p ^ (v * h) = Module.rankAtStalk (R := R) ↥(C v u π) 𝔭 + Module.rankAtStalk (R := R) ↥K 𝔭
      at h1
    rw [h2] at h1
    change Module.rankAtStalk (R := R) ↥K 𝔭 = 0
    omega
  have hKs : Subsingleton ↥K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK
  intro a b hab
  have hmem : a - b ∈ K := by
    change f (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.2 hab
  have h0 : (⟨a - b, hmem⟩ : ↥K) = 0 := Subsingleton.elim _ _
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

include ht hkerL hπ hkerπ hrankL hrankB in

theorem C_eq_range : C v u π = (Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range := by
  apply le_antisymm
  · intro c hc
    obtain ⟨s, hs⟩ := jC_surjective t ht hkerL v u π hπ hkerπ ⟨c, hc⟩
    obtain ⟨a, rfl⟩ := iAlg_surjective t ht v u s
    refine ⟨a, ?_⟩
    have := congrArg Subtype.val hs
    rw [coe_jC] at this
    exact (jAlg_iAlg t ht hkerL v u a).symm.trans this
  · rintro c ⟨a, rfl⟩
    change Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a ∈ C v u π
    rw [← jAlg_iAlg t ht hkerL v u]
    exact jAlg_mem_C t ht hkerL v u π hπ hkerπ _

end Sub

section Rank

open HopfAlgebra

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
variable (π : A →ₐc[R] B) (hπ : Function.Surjective π)

def qC : A ⊗[R] A →ₗ[R] A ⊗[↥(hopfKer π)] A :=
  TensorProduct.lift
    (LinearMap.mk₂ R (fun a a' => a ⊗ₜ[↥(hopfKer π)] a')
      (fun a₁ a₂ a' => TensorProduct.add_tmul a₁ a₂ a')
      (fun c a a' => by simp only [TensorProduct.smul_tmul'])
      (fun a a₁ a₂ => TensorProduct.tmul_add a a₁ a₂)
      (fun c a a' => by simp only [TensorProduct.tmul_smul]))

@[scoped simp] theorem qC_tmul (a a' : A) : qC π (a ⊗ₜ[R] a') = a ⊗ₜ[↥(hopfKer π)] a' := rfl

theorem qC_surjective : Function.Surjective (qC π) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a a' => exact ⟨a ⊗ₜ[R] a', rfl⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

theorem qC_balancing {z : A ⊗[R] A} (hz : z ∈ Submodule.span R (balancingRelations π)) :
    qC π z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, a', hb, rfl⟩ := hx
    rw [map_sub, qC_tmul, qC_tmul, sub_eq_zero, mul_comm a b,
      show b * a = (⟨b, hb⟩ : ↥(hopfKer π)) • a from rfl,
      show b * a' = (⟨b, hb⟩ : ↥(hopfKer π)) • a' from rfl, TensorProduct.smul_tmul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

omit [Module.Finite R A] [Module.Free R A] [Module.Finite R B] [Module.Free R B] in

theorem smul_AB (c : ↥(hopfKer π)) (X : A ⊗[R] B) : c • X = ((c : A) ⊗ₜ[R] (1 : B)) * X := by
  induction X using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change ((c : A) • x) ⊗ₜ[R] y = _
    rw [smul_eq_mul]
  | add x y hx hy => rw [smul_add, hx, hy, mul_add]

def canC : A ⊗[↥(hopfKer π)] A →ₗ[A] A ⊗[R] B :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun a' => canMap π (a ⊗ₜ[R] a')
          map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
          map_smul' := fun c a' => by
            rw [RingHom.id_apply, Subalgebra.smul_def, smul_eq_mul, ← canMap_mul_tmul π a a' c.2,
              canMap_tmul, canMap_tmul, smul_AB, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
              one_mul, mul_comm a] }
      map_add' := fun x y => by
        refine LinearMap.ext fun a' => ?_
        change canMap π ((x + y) ⊗ₜ[R] a') = canMap π (x ⊗ₜ[R] a') + canMap π (y ⊗ₜ[R] a')
        rw [TensorProduct.add_tmul, map_add]
      map_smul' := fun a₀ x => by
        refine LinearMap.ext fun a' => ?_
        change canMap π ((a₀ • x) ⊗ₜ[R] a') = a₀ • canMap π (x ⊗ₜ[R] a')
        rw [canMap_tmul, canMap_tmul, smul_eq_mul, ← smul_mul_assoc, TensorProduct.smul_tmul',
          smul_eq_mul] }

theorem canC_tmul (a a' : A) : canC π (a ⊗ₜ[↥(hopfKer π)] a') = canMap π (a ⊗ₜ[R] a') := rfl

theorem canC_qC (z : A ⊗[R] A) : canC π (qC π z) = canMap π z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a a' => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

include hπ in
theorem canC_bijective : Function.Bijective (canC π) := by
  have hGal := HopfAlgebra.isHopfGalois_of_surjective π hπ
  constructor
  · intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    obtain ⟨w, hw⟩ := qC_surjective π (x - y)
    rw [← hw, canC_qC] at hxy
    rw [← hw]
    exact qC_balancing π (hGal.2 w hxy)
  · intro y
    obtain ⟨z, rfl⟩ := hGal.1 y
    exact ⟨qC π z, canC_qC π z⟩

def canCEquiv : A ⊗[↥(hopfKer π)] A ≃ₗ[A] A ⊗[R] B :=
  LinearEquiv.ofBijective (canC π) (canC_bijective π hπ)

include hπ in

theorem rankAtStalk_hopfKer_eq (𝔮 : PrimeSpectrum ↥(hopfKer π)) :
    Module.rankAtStalk (R := ↥(hopfKer π)) A 𝔮 = Module.finrank R B := by
  obtain ⟨hfin, hproj⟩ := HopfAlgebra.finite_projective_hopfKer_of_surjective π hπ
  haveI := hfin
  haveI := hproj
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap ↥(hopfKer π) A)) :=
    PrimeSpectrum.comap_surjective_iff_injective_of_finite.2 Subtype.val_injective
  obtain ⟨𝔔, rfl⟩ := hsurj 𝔮
  rw [← Module.rankAtStalk_baseChange (S := A), Module.rankAtStalk_eq_of_equiv (canCEquiv π hπ),
    Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free]
  rfl

end Rank

section Assembly

variable {R : Type u} [CommRing R] {p h : ℕ}
variable {L : ℕ → Type v} [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]
variable [∀ w, Coalgebra.IsCocomm R (L w)] [∀ w, Module.Free R (L w)] [∀ w, Module.Finite R (L w)]
variable (t : ∀ w, L (w + 1) →ₐc[R] L w) (ht : ∀ w, Function.Surjective (t w))
variable (hrankL : ∀ w, Module.finrank R (L w) = p ^ (w * h))
variable (hkerL : ∀ w, RingHom.ker (t w) = Hopf.torsionIdeal R (L (w + 1)) (p ^ w))
variable (v u : ℕ)

def levelCast : ∀ {n m : ℕ}, n = m → (L n ≃ₐc[R] L m)
  | _, _, rfl => BialgEquiv.refl R _

def proj : L (v + u) →ₐc[R] L u :=
  (Tower.transitionLE t u v).comp
    ((levelCast (R := R) (L := L) (Nat.add_comm v u) : L (v + u) ≃ₐc[R] L (u + v)) :
      L (v + u) →ₐc[R] L (u + v))

include ht in
theorem proj_surjective : Function.Surjective (proj t v u) := by
  rw [proj, BialgHom.coe_comp]
  exact (Tower.transitionLE_surjective t ht u v).comp
    (levelCast (R := R) (L := L) (Nat.add_comm v u) : L (v + u) ≃ₐc[R] L (u + v)).surjective

theorem ker_comp_equiv_eq_torsionIdeal {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R A'] [HopfAlgebra R B]
    (ρ : A' →ₐc[R] B) (e : A ≃ₐc[R] A') (n : ℕ)
    (hker : RingHom.ker (ρ : A' →ₐ[R] B) = Hopf.torsionIdeal R A' n) :
    RingHom.ker ((ρ.comp (e : A →ₐc[R] A') : A →ₐc[R] B) : A →ₐ[R] B) = Hopf.torsionIdeal R A n := by
  have hsurj : Function.Surjective (e : A →ₐc[R] A') := e.surjective
  have hsurj' : Function.Surjective (e.symm : A' →ₐc[R] A) := e.symm.surjective
  apply le_antisymm
  · intro a ha
    have ha' : (e : A →ₐc[R] A') a ∈ RingHom.ker (ρ : A' →ₐ[R] B) := ha
    rw [hker] at ha'
    have hmem := Ideal.mem_map_of_mem ((e.symm : A' →ₐc[R] A) : A' →ₐ[R] A) ha'
    rw [Hopf.map_torsionIdeal_of_surjective (e.symm : A' →ₐc[R] A) hsurj' n] at hmem
    have : ((e.symm : A' →ₐc[R] A) : A' →ₐ[R] A) ((e : A →ₐc[R] A') a) = a := e.symm_apply_apply a
    rw [this] at hmem
    exact hmem
  · intro a ha
    have hmem := Ideal.mem_map_of_mem ((e : A →ₐc[R] A') : A →ₐ[R] A') ha
    rw [Hopf.map_torsionIdeal_of_surjective (e : A →ₐc[R] A') hsurj n, ← hker] at hmem
    exact hmem

include ht hkerL in
theorem ker_proj :
    RingHom.ker (proj t v u : L (v + u) →ₐ[R] L u) = Hopf.torsionIdeal R (L (v + u)) (p ^ u) :=
  ker_comp_equiv_eq_torsionIdeal (Tower.transitionLE t u v)
    (levelCast (R := R) (L := L) (Nat.add_comm v u) : L (v + u) ≃ₐc[R] L (u + v)) (p ^ u)
    (Tower.ker_transitionLE ht hkerL u v)

def jEquiv : L v ≃ₐ[R] ↥(C v u (proj t v u)) :=
  AlgEquiv.ofBijective (jC t ht hkerL v u (proj t v u) (proj_surjective t ht v u) (ker_proj t ht hkerL v u))
    ⟨jC_injective t ht hkerL v u (proj t v u) (proj_surjective t ht v u) (ker_proj t ht hkerL v u)
        hrankL (hrankL u),
      jC_surjective t ht hkerL v u (proj t v u) (proj_surjective t ht v u) (ker_proj t ht hkerL v u)⟩

theorem jEquiv_apply (s : L v) :
    jEquiv t ht hrankL hkerL v u s =
      jC t ht hkerL v u (proj t v u) (proj_surjective t ht v u) (ker_proj t ht hkerL v u) s := rfl

include ht hrankL hkerL in

theorem main_C :
    (∃ e : L v ≃ₐ[R] ↥(C v u (proj t v u)),
        ∀ a : L (v + u),
          ((e (Tower.transitionLE t v u a) : ↥(C v u (proj t v u))) : L (v + u)) =
            Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a) ∧
      Module.Finite ↥(C v u (proj t v u)) (L (v + u)) ∧
      Module.Projective ↥(C v u (proj t v u)) (L (v + u)) ∧
      (∃ r : L (v + u) →ₗ[↥(C v u (proj t v u))] ↥(C v u (proj t v u)),
        ∀ c : ↥(C v u (proj t v u)), r (c : L (v + u)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥(C v u (proj t v u)),
        Module.rankAtStalk (R := ↥(C v u (proj t v u))) (L (v + u)) 𝔮 = p ^ (u * h) := by
  obtain ⟨hfin, hproj⟩ :=
    HopfAlgebra.finite_projective_hopfKer_of_surjective (proj t v u) (proj_surjective t ht v u)
  obtain ⟨hret, -, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (proj t v u) (proj_surjective t ht v u)
  refine ⟨⟨jEquiv t ht hrankL hkerL v u, fun a => ?_⟩, hfin, hproj, hret, fun 𝔮 => ?_⟩
  · rw [jEquiv_apply, coe_jC, jAlg_iAlg]
  · rw [rankAtStalk_hopfKer_eq (proj t v u) (proj_surjective t ht v u) 𝔮, hrankL u]

include ht hrankL hkerL in

theorem main_of_eq (S : Subalgebra R (L (v + u))) (hS : S = C v u (proj t v u)) :
    (∃ e : L v ≃ₐ[R] ↥S,
        ∀ a : L (v + u),
          ((e (Tower.transitionLE t v u a) : ↥S) : L (v + u)) = Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a) ∧
      Module.Finite ↥S (L (v + u)) ∧
      Module.Projective ↥S (L (v + u)) ∧
      (∃ r : L (v + u) →ₗ[↥S] ↥S, ∀ c : ↥S, r (c : L (v + u)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥S, Module.rankAtStalk (R := ↥S) (L (v + u)) 𝔮 = p ^ (u * h) := by
  subst hS
  exact main_C t ht hrankL hkerL v u

end Assembly

end PDivTowerIsog
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk.PDivTowerIsog"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk.PDivTowerIsog"

theorem solution
    {R : Type u} [CommRing R] (p h : ℕ)
    (L : ℕ → Type v) [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]
    [∀ w, Coalgebra.IsCocomm R (L w)] [∀ w, Module.Free R (L w)] [∀ w, Module.Finite R (L w)]
    (t : ∀ w, L (w + 1) →ₐc[R] L w) (ht : ∀ w, Function.Surjective (t w))
    (hrankL : ∀ w, Module.finrank R (L w) = p ^ (w * h))
    (hkerL : ∀ w, RingHom.ker (t w) = PDivisibleGroup.Hopf.torsionIdeal R (L (w + 1)) (p ^ w))
    (v u : ℕ) :
    (∃ e : L v ≃ₐ[R] ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        ∀ a : L (v + u),
          ((e (PDivisibleGroup.Tower.transitionLE t v u a) :
              ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range) : L (v + u)) =
            PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u) a) ∧
      Module.Finite ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range (L (v + u)) ∧
      Module.Projective ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range (L (v + u)) ∧
      (∃ r : L (v + u) →ₗ[↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range]
          ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        ∀ c : ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
          r (c : L (v + u)) = c) ∧
      ∀ 𝔮 : PrimeSpectrum ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range,
        Module.rankAtStalk (R := ↥(PDivisibleGroup.Hopf.nsmulAlgHom R (L (v + u)) (p ^ u)).range)
          (L (v + u)) 𝔮 = p ^ (u * h) :=
  PDivTowerIsog.main_of_eq t ht hrankL hkerL v u _
    (PDivTowerIsog.C_eq_range t ht hkerL v u (PDivTowerIsog.proj t v u)
      (PDivTowerIsog.proj_surjective t ht v u) (PDivTowerIsog.ker_proj t ht hkerL v u)
      hrankL (hrankL u)).symm

end S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
end P2MW
export P2MW.S_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk (solution)
