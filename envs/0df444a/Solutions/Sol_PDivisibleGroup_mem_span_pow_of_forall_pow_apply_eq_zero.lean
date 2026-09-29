-- Prove2me | solution 1 for PDivisibleGroup.mem_span_pow_of_forall_pow_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7b21d185-867d-5e00-bd69-c22aa7bc7658

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_mem_span_pow_of_forall_pow_apply_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

namespace PDivBTH

universe u v

section NSMulBialg

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A] [IsCocomm R A]

def nsmulBialgHom (n : ℕ) : A →ₐc[R] A := ((toConv (BialgHom.id R A)) ^ n).ofConv

theorem toAlgHom_nsmulBialgHom (n : ℕ) :
    (nsmulBialgHom R A n : A →ₐ[R] A) = PDivisibleGroup.Hopf.nsmulAlgHom R A n := by
  have h := BialgHom.toAlgHom_convPow (toConv (BialgHom.id R A)) n
  apply WithConv.toConv_injective
  exact h

@[scoped simp] theorem nsmulBialgHom_apply (n : ℕ) (a : A) :
    nsmulBialgHom R A n a = PDivisibleGroup.Hopf.nsmulAlgHom R A n a := by
  rw [← toAlgHom_nsmulBialgHom]; rfl

end NSMulBialg

section J

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

open PDivisibleGroup

theorem nsmulAlgHom_comp_nsmulAlgHom {A : Type v} [CommRing A] [Bialgebra R A] (m n : ℕ) :
    (Hopf.nsmulAlgHom R A m).comp (Hopf.nsmulAlgHom R A n) = Hopf.nsmulAlgHom R A (m * n) := by
  rw [Hopf.nsmulAlgHom_mul]
  apply WithConv.toConv_injective
  rw [toConv_ofConv]
  exact (Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom (Hopf.nsmulAlgHom R A m) n).symm

theorem ker_transition_le_ker_nsmulAlgHom (v : ℕ) :
    RingHom.ker (G.transitionAlgHom v).toRingHom ≤
      RingHom.ker (Hopf.nsmulAlgHom R (G.level (v + 1)) p).toRingHom := by
  intro a ha
  have ha' : a ∈ Hopf.torsionIdeal R (G.level (v + 1)) (p ^ v) := by
    rw [← G.ker_transition v]; exact ha
  have hle : Hopf.torsionIdeal R (G.level (v + 1)) (p ^ v) ≤
      RingHom.ker (Hopf.nsmulAlgHom R (G.level (v + 1)) p).toRingHom := by
    rw [Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
    intro b hb
    change Hopf.nsmulAlgHom R _ p (Hopf.nsmulAlgHom R _ (p ^ v) b) = 0
    rw [← AlgHom.comp_apply, nsmulAlgHom_comp_nsmulAlgHom, ← pow_succ',
      G.nsmulAlgHom_pow_level_apply (v + 1), (Hopf.mem_augIdeal_iff R _ b).1 hb, map_zero]
  exact hle ha'

def jAlg (v : ℕ) : G.level v →ₐ[R] G.level (v + 1) :=
  AlgHom.liftOfSurjective (G.transitionAlgHom v) (G.transition_surjective v)
    (Hopf.nsmulAlgHom R (G.level (v + 1)) p) (ker_transition_le_ker_nsmulAlgHom G v)

theorem jAlg_comp_transition (v : ℕ) :
    (jAlg G v).comp (G.transitionAlgHom v) = Hopf.nsmulAlgHom R (G.level (v + 1)) p :=
  AlgHom.liftOfSurjective_comp _ _ _ _

@[scoped simp] theorem jAlg_transition (v : ℕ) (a : G.level (v + 1)) :
    jAlg G v (G.transition v a) = Hopf.nsmulAlgHom R (G.level (v + 1)) p a :=
  DFunLike.congr_fun (jAlg_comp_transition G v) a

theorem transition_jAlg (v : ℕ) (b : G.level v) :
    G.transition v (jAlg G v b) = Hopf.nsmulAlgHom R (G.level v) p b := by
  obtain ⟨a, rfl⟩ := G.transition_surjective v b
  rw [jAlg_transition, G.nsmulAlgHom_transition]

theorem algHom_eq_of_comp_transition_eq {v : ℕ} {X : Type v} [Semiring X] [Algebra R X]
    {f g : G.level v →ₐ[R] X}
    (hfg : f.comp (G.transitionAlgHom v) = g.comp (G.transitionAlgHom v)) : f = g := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := G.transition_surjective v b
  exact DFunLike.congr_fun hfg a

theorem counitAlgHom_comp_jAlg (v : ℕ) :
    (counitAlgHom R (G.level (v + 1))).comp (jAlg G v) = counitAlgHom R (G.level v) := by
  apply algHom_eq_of_comp_transition_eq G
  rw [AlgHom.comp_assoc, jAlg_comp_transition]
  refine AlgHom.ext fun a => ?_
  change counit (R := R) (Hopf.nsmulAlgHom R _ p a) = counit (R := R) (G.transition v a)
  rw [Hopf.counit_nsmulAlgHom, G.counit_transition]

theorem map_comp_comulAlgHom_jAlg (v : ℕ) :
    (Algebra.TensorProduct.map (jAlg G v) (jAlg G v)).comp (comulAlgHom R (G.level v)) =
      (comulAlgHom R (G.level (v + 1))).comp (jAlg G v) := by
  apply algHom_eq_of_comp_transition_eq G
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, jAlg_comp_transition,
    ← BialgHom.map_comp_comulAlgHom (G.transition v), ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp, jAlg_comp_transition]
  have h := BialgHom.map_comp_comulAlgHom (nsmulBialgHom R (G.level (v + 1)) p)
  rw [toAlgHom_nsmulBialgHom] at h
  exact h

def jB (v : ℕ) : G.level v →ₐc[R] G.level (v + 1) :=
  BialgHom.ofAlgHom (jAlg G v) (counitAlgHom_comp_jAlg G v) (map_comp_comulAlgHom_jAlg G v)

@[scoped simp] theorem jB_apply (v : ℕ) (b : G.level v) : jB G v b = jAlg G v b := rfl

theorem toAlgHom_jB (v : ℕ) : (jB G v : G.level v →ₐ[R] G.level (v + 1)) = jAlg G v := rfl

def proj : ∀ v : ℕ, G.level (v + 1) →ₐc[R] G.level 1
  | 0 => BialgHom.id R (G.level 1)
  | v + 1 => (proj v).comp (G.transition (v + 1))

@[scoped simp] theorem proj_zero : proj G 0 = BialgHom.id R (G.level 1) := rfl

theorem proj_succ (v : ℕ) : proj G (v + 1) = (proj G v).comp (G.transition (v + 1)) := rfl

theorem proj_surjective : ∀ v : ℕ, Function.Surjective (proj G v)
  | 0 => Function.surjective_id
  | v + 1 => by
    rw [proj_succ, BialgHom.coe_comp]
    exact (proj_surjective v).comp (G.transition_surjective (v + 1))

theorem nsmulAlgHom_p_level_one :
    Hopf.nsmulAlgHom R (G.level 1) p = (Algebra.ofId R (G.level 1)).comp (counitAlgHom R (G.level 1)) := by
  have h := G.nsmulAlgHom_pow_level 1
  rwa [pow_one] at h

theorem proj_comp_jAlg (v : ℕ) :
    (proj G v : G.level (v + 1) →ₐ[R] G.level 1).comp (jAlg G v) =
      (Algebra.ofId R (G.level 1)).comp (counitAlgHom R (G.level v)) := by
  apply algHom_eq_of_comp_transition_eq G
  rw [AlgHom.comp_assoc, jAlg_comp_transition, ← Hopf.nsmulAlgHom_comp_bialgHom (proj G v) p,
    nsmulAlgHom_p_level_one, AlgHom.comp_assoc, AlgHom.comp_assoc]
  congr 1
  rw [BialgHom.counitAlgHom_comp]
  refine AlgHom.ext fun a => ?_
  change counit (R := R) a = counit (R := R) (G.transition v a)
  rw [G.counit_transition]

theorem proj_jAlg (v : ℕ) (b : G.level v) :
    proj G v (jAlg G v b) = algebraMap R (G.level 1) (counit (R := R) b) :=
  DFunLike.congr_fun (proj_comp_jAlg G v) b

abbrev C (v : ℕ) : Subalgebra R (G.level (v + 1)) := HopfAlgebra.hopfKer (proj G v)

theorem jAlg_mem_C (v : ℕ) (b : G.level v) : jAlg G v b ∈ C G v := by
  rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply]
  have hcomul : comul (R := R) (jAlg G v b) =
      Algebra.TensorProduct.map (jAlg G v) (jAlg G v) (comul (R := R) b) := by
    have h := DFunLike.congr_fun (map_comp_comulAlgHom_jAlg G v) b
    exact h.symm
  rw [hcomul, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, proj_comp_jAlg, AlgHom.id_comp]

  have key : ∀ z : G.level v ⊗[R] G.level v,
      Algebra.TensorProduct.map (jAlg G v) ((Algebra.ofId R (G.level 1)).comp (counitAlgHom R (G.level v))) z =
        Algebra.TensorProduct.map (jAlg G v) (Algebra.ofId R (G.level 1))
          ((LinearMap.lTensor (G.level v) (counit (R := R) (A := G.level v))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [key, Coalgebra.lTensor_counit_comul, Algebra.TensorProduct.map_tmul, map_one]

def jC (v : ℕ) : G.level v →ₐ[R] ↥(C G v) := (jAlg G v).codRestrict (C G v) (jAlg_mem_C G v)

@[scoped simp] theorem coe_jC (v : ℕ) (b : G.level v) : (jC G v b : G.level (v + 1)) = jAlg G v b := rfl

end J

section Points

universe w

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable {T : Type w} [CommRing T] [Algebra R T]

open PDivisibleGroup

theorem exists_comp_proj_of_pow_eq_one :
    ∀ (v : ℕ) (z : WithConv (G.level (v + 1) →ₐ[R] T)), z ^ p = 1 →
      ∃ z₁ : G.level 1 →ₐ[R] T, z.ofConv = z₁.comp (proj G v : G.level (v + 1) →ₐ[R] G.level 1)
  | 0, z, _ => ⟨z.ofConv, by
      rw [proj_zero, BialgHom.id_toAlgHom, AlgHom.comp_id]⟩
  | v + 1, z, hz => by
    have hz' : z ^ (p ^ (v + 1)) = 1 := by rw [pow_succ', pow_mul, hz, one_pow]
    obtain ⟨g, hg⟩ := G.exists_comp_transition_eq (v + 1) z hz'
    have hgp : (toConv g) ^ p = 1 := by
      have hinj := G.comp_transition_injective (v + 1) (L := T)
      have h1 : ((toConv g) ^ p).ofConv.comp
            (G.transition (v + 1) : G.level (v + 1 + 1) →ₐ[R] G.level (v + 1)) =
          (1 : WithConv (G.level (v + 1) →ₐ[R] T)).ofConv.comp
            (G.transition (v + 1) : G.level (v + 1 + 1) →ₐ[R] G.level (v + 1)) := by
        have e1 := Hopf.convPow_comp_bialgHom (toConv g) (G.transition (v + 1)) p
        have e0 := Hopf.convPow_comp_bialgHom (toConv g) (G.transition (v + 1)) 0
        rw [pow_zero, pow_zero] at e0
        rw [e1, e0, ofConv_toConv, hg, toConv_ofConv, hz]
      exact WithConv.ofConv_injective (hinj h1)
    obtain ⟨z₁, hz₁⟩ := exists_comp_proj_of_pow_eq_one v (toConv g) hgp
    refine ⟨z₁, ?_⟩
    rw [ofConv_toConv] at hz₁
    rw [← hg, hz₁, proj_succ, BialgHom.comp_toAlgHom, AlgHom.comp_assoc]

omit [Algebra R T] in
theorem lift_comp_right {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B'] [Algebra R A]
    [Algebra R B] [Algebra R B'] [Algebra R T] (f : A →ₐ[R] T) (g : B →ₐ[R] T) (π : B' →ₐ[R] B) :
    Algebra.TensorProduct.lift f (g.comp π) (fun _ _ => .all _ _) =
      (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) π) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp

theorem apply_eq_of_comp_jAlg_eq (v : ℕ) (x y : G.level (v + 1) →ₐ[R] T)
    (hxy : x.comp (jAlg G v) = y.comp (jAlg G v)) {c : G.level (v + 1)} (hc : c ∈ C G v) :
    x c = y c := by
  have hy : IsUnit (toConv y) := Hopf.isUnit_toConv_algHom y
  set z : WithConv (G.level (v + 1) →ₐ[R] T) := toConv x * ↑(hy.unit⁻¹) with hz_def
  have hxz : toConv x = toConv y * z := by
    rw [hz_def, mul_left_comm, Units.mul_inv_of_eq hy.unit_spec, mul_one]

  let Φ := Hopf.convCompMonoidHom T (jB G v)
  have hΦxy : Φ (toConv x) = Φ (toConv y) := by
    change toConv (x.comp (jB G v : G.level v →ₐ[R] G.level (v + 1))) =
      toConv (y.comp (jB G v : G.level v →ₐ[R] G.level (v + 1)))
    rw [toAlgHom_jB, hxy]
  have hΦz : Φ z = 1 := by
    rw [hz_def, map_mul, hΦxy, ← map_mul, Units.mul_inv_of_eq hy.unit_spec, map_one]

  have hzp : z ^ p = 1 := by
    have h1 : z ^ p = toConv (z.ofConv.comp (Hopf.nsmulAlgHom R (G.level (v + 1)) p)) := by
      conv_lhs => rw [← toConv_ofConv z]
      exact Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom z.ofConv p
    have h2 : z.ofConv.comp (jAlg G v) = (1 : WithConv (G.level v →ₐ[R] T)).ofConv := by
      have := congrArg WithConv.ofConv hΦz
      exact this
    rw [h1, ← jAlg_comp_transition, ← AlgHom.comp_assoc, h2, AlgHom.convOne_def, ofConv_toConv,
      AlgHom.comp_assoc]
    change toConv ((Algebra.ofId R T).comp ((counitAlgHom R (G.level v)).comp
      (G.transition v : G.level (v + 1) →ₐ[R] G.level v))) = 1
    rw [BialgHom.counitAlgHom_comp]
    rfl
  obtain ⟨z₁, hz₁⟩ := exists_comp_proj_of_pow_eq_one G v z hzp

  have hx : x c = (toConv y * z).ofConv c := by rw [← hxz]
  rw [hx, AlgHom.convMul_apply, hz₁, ofConv_toConv, lift_comp_right, AlgHom.comp_apply]
  have hco : Algebra.TensorProduct.map (AlgHom.id R (G.level (v + 1)))
      (proj G v : G.level (v + 1) →ₐ[R] G.level 1) (comul (R := R) c) = c ⊗ₜ[R] 1 := hc
  rw [hco, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

end Points

section Surj

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

open PDivisibleGroup

theorem jC_surjective (v : ℕ) : Function.Surjective (jC G v) := by
  obtain ⟨⟨r, hr⟩, hfin, -, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (proj G v) (proj_surjective G v)
  letI : Algebra (G.level v) (G.level (v + 1)) := (jAlg G v).toRingHom.toAlgebra
  haveI : IsScalarTower R (G.level v) (G.level (v + 1)) :=
    IsScalarTower.of_algebraMap_eq fun x => ((jAlg G v).commutes x).symm
  letI : Algebra (G.level v) ↥(C G v) := (jC G v).toRingHom.toAlgebra
  haveI : IsScalarTower R (G.level v) ↥(C G v) :=
    IsScalarTower.of_algebraMap_eq fun x => ((jC G v).commutes x).symm
  haveI : Module.Finite R ↥(C G v) := hfin
  haveI : Module.Finite (G.level v) ↥(C G v) := Module.Finite.of_restrictScalars_finite R _ _

  have hr_smul : ∀ (s : G.level v) (a : G.level (v + 1)), r (s • a) = s • r a := by
    intro s a
    have h1 : s • a = (jC G v s) • a := rfl
    rw [h1, LinearMap.map_smul]
    rfl
  let rS : G.level (v + 1) →ₗ[G.level v] ↥(C G v) :=
    { toFun := r, map_add' := fun a b => r.map_add a b, map_smul' := hr_smul }
  have hepi : Algebra.IsEpi (G.level v) ↥(C G v) := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro c

    let T := G.level (v + 1) ⊗[G.level v] G.level (v + 1)
    let x : G.level (v + 1) →ₐ[R] T := Algebra.TensorProduct.includeLeft
    let y : G.level (v + 1) →ₐ[R] T :=
      (Algebra.TensorProduct.includeRight : G.level (v + 1) →ₐ[G.level v] T).restrictScalars R
    have hxy : x.comp (jAlg G v) = y.comp (jAlg G v) := by
      refine AlgHom.ext fun s => ?_
      change (algebraMap (G.level v) (G.level (v + 1)) s) ⊗ₜ[G.level v] (1 : G.level (v + 1)) =
        (1 : G.level (v + 1)) ⊗ₜ[G.level v] (algebraMap (G.level v) (G.level (v + 1)) s)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have key : (c : G.level (v + 1)) ⊗ₜ[G.level v] (1 : G.level (v + 1)) =
        (1 : G.level (v + 1)) ⊗ₜ[G.level v] (c : G.level (v + 1)) :=
      apply_eq_of_comp_jAlg_eq G v x y hxy c.2

    have h1 : r (1 : G.level (v + 1)) = 1 := hr 1
    have := congrArg (TensorProduct.map rS rS) key
    simp only [TensorProduct.map_tmul] at this
    change r (c : G.level (v + 1)) ⊗ₜ[G.level v] r 1 = r 1 ⊗ₜ[G.level v] r (c : G.level (v + 1)) at this
    rw [hr c, h1] at this
    exact this.symm
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

theorem exists_jAlg_eq_of_mem_C (v : ℕ) {c : G.level (v + 1)} (hc : c ∈ C G v) :
    ∃ s : G.level v, jAlg G v s = c := by
  obtain ⟨s, hs⟩ := jC_surjective G v ⟨c, hc⟩
  exact ⟨s, congrArg Subtype.val hs⟩

end Surj

section Inj

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

open PDivisibleGroup

theorem nontrivial_level [Nontrivial R] (v : ℕ) : Nontrivial (G.level v) := by
  by_contra hA
  rw [not_nontrivial_iff_subsingleton] at hA
  have h1 : counit (R := R) (1 : G.level v) = 1 := Bialgebra.counit_one
  rw [Subsingleton.elim (1 : G.level v) 0, map_zero] at h1
  exact zero_ne_one h1

include G in
theorem pow_h_ne_zero [Nontrivial R] : p ^ h ≠ 0 := by
  haveI := nontrivial_level G 1
  intro h0
  have h1 := G.finrank_level 1
  rw [one_mul, h0, Module.finrank_eq_zero_iff_of_free] at h1
  exact false_of_nontrivial_of_subsingleton (G.level 1)

omit [CommRing R] in
theorem nontrivial_of_primeSpectrum [CommRing R] (𝔭 : PrimeSpectrum R) : Nontrivial R := by
  by_contra hR
  rw [not_nontrivial_iff_subsingleton] at hR
  exact 𝔭.2.ne_top (Subsingleton.elim _ _)

theorem rankAtStalk_C (v : ℕ) (𝔭 : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) ↥(C G v) 𝔭 = p ^ (v * h) := by
  obtain ⟨-, -, -, hrank⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (proj G v) (proj_surjective G v)
  haveI := nontrivial_of_primeSpectrum 𝔭
  have h1 := hrank 𝔭
  rw [G.finrank_level 1, G.finrank_level (v + 1), one_mul, add_mul, one_mul, pow_add] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_h_ne_zero G)) h1

theorem jC_injective (v : ℕ) : Function.Injective (jC G v) := by
  obtain ⟨-, hfin, hproj, -⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (proj G v) (proj_surjective G v)
  haveI := hfin
  haveI := hproj
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (G.level v) := Module.subsingleton R _
    exact fun a b _ => Subsingleton.elim a b
  let f : G.level v →ₗ[R] ↥(C G v) := (jC G v).toLinearMap
  have hf : Function.Surjective f := jC_surjective G v
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfσ : ∀ c, f (σ c) = c := fun c => DFunLike.congr_fun hσ c
  have hσinj : Function.Injective σ := Function.LeftInverse.injective hfσ

  let K : Submodule R (G.level v) := LinearMap.ker f
  let s : G.level v →ₗ[R] ↥K :=
    LinearMap.codRestrict K (LinearMap.id - σ.comp f) fun x => by
      change f (x - σ (f x)) = 0
      rw [map_sub, hfσ, sub_self]
  have hsK : s.comp K.subtype = LinearMap.id := by
    refine LinearMap.ext fun k => Subtype.ext ?_
    change (k : G.level v) - σ (f k) = k
    rw [show f k = 0 from k.2, map_zero, sub_zero]
  haveI : Module.Projective R ↥K := Module.Projective.of_split K.subtype s hsK
  haveI : Module.Finite R ↥K :=
    Module.Finite.of_surjective s fun k => ⟨k, DFunLike.congr_fun hsK k⟩

  let P : Submodule R (G.level v) := LinearMap.range σ
  let π' : G.level v →ₗ[R] ↥P :=
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
  let e : G.level v ≃ₗ[R] ↥(C G v) × ↥K :=
    (Submodule.prodEquivOfIsCompl P (LinearMap.ker π') hcompl).symm.trans
      (LinearEquiv.prodCongr (LinearEquiv.ofInjective σ hσinj).symm
        (LinearEquiv.ofEq _ _ hkerπ'))

  have hK : Module.rankAtStalk (R := R) ↥K = 0 := by
    funext 𝔭
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv e) 𝔭
    rw [Module.rankAtStalk_prod, Module.rankAtStalk_eq_finrank_of_free, G.finrank_level v] at h1
    have h2 : Module.rankAtStalk (R := R) ↥(C G v) 𝔭 = p ^ (v * h) := rankAtStalk_C G v 𝔭
    change p ^ (v * h) = Module.rankAtStalk (R := R) ↥(C G v) 𝔭 + Module.rankAtStalk (R := R) ↥K 𝔭
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

def jEquiv (v : ℕ) : G.level v ≃ₗ[R] ↥(C G v) :=
  LinearEquiv.ofBijective (jC G v).toLinearMap ⟨jC_injective G v, jC_surjective G v⟩

@[scoped simp] theorem jEquiv_apply (v : ℕ) (s : G.level v) : jEquiv G v s = jC G v s := rfl

def ret (v : ℕ) : G.level (v + 1) →ₗ[↥(C G v)] ↥(C G v) :=
  (HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (proj G v) (proj_surjective G v)).1.choose

theorem ret_coe (v : ℕ) (c : ↥(C G v)) : ret G v (c : G.level (v + 1)) = c :=
  (HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
      (proj G v) (proj_surjective G v)).1.choose_spec c

def jLeftInv (v : ℕ) : G.level (v + 1) →ₗ[R] G.level v :=
  (jEquiv G v).symm.toLinearMap.comp ((ret G v).restrictScalars R)

theorem jLeftInv_jAlg (v : ℕ) (s : G.level v) : jLeftInv G v (jAlg G v s) = s := by
  change (jEquiv G v).symm (ret G v (jC G v s : G.level (v + 1))) = s
  rw [ret_coe, ← jEquiv_apply, LinearEquiv.symm_apply_apply]

end Inj

section Main

variable {k : Type} [Field k] {p h : ℕ} [hp : Fact p.Prime] [CharP k p] (G : PDivisibleGroup k p h)

open PDivisibleGroup

private theorem _root_.PDivBTH.cast_eq_zero (T : Type*) [Ring T] [Algebra k T] : (p : T) = 0 := by
  rw [← map_natCast (algebraMap k T), CharP.cast_eq_zero, map_zero]

p2m_export "PDivBTH" "cast_eq_zero"
omit [CharP k p] in
theorem add_pow_char' {T : Type*} [CommRing T] (hT : (p : T) = 0) (x y : T) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp.out, hT, zero_mul, zero_mul, zero_mul, add_zero]

def J (v : ℕ) : Ideal (G.level v) :=
  Ideal.span ((fun a : G.level v => a ^ p) '' (Hopf.augIdeal k (G.level v) : Set (G.level v)))

omit hp [CharP k p] in
theorem pow_mem_J (v : ℕ) {a : G.level v} (ha : a ∈ Hopf.augIdeal k (G.level v)) : a ^ p ∈ J G v :=
  Ideal.subset_span ⟨a, ha, rfl⟩

def Jext : Ideal (G.level 2) := (J G 1).map (jAlg G 1)

theorem pow_mem_Jext_of_transition_eq_zero {y : G.level 2} (hy : G.transition 1 y = 0) :
    y ^ p ∈ Jext G := by
  have hy' : y ∈ Hopf.torsionIdeal k (G.level 2) (p ^ 1) := (G.mem_ker_transition_iff 1 y).1 hy
  rw [pow_one, Hopf.torsionIdeal, Ideal.map, ← Ideal.submodule_span_eq] at hy'
  have hA : (p : G.level 2) = 0 := cast_eq_zero (k := k) (p := p) (G.level 2)
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, rfl⟩ := hz

    rw [← map_pow, ← jAlg_transition, map_pow]
    refine Ideal.mem_map_of_mem _ (pow_mem_J G 1 ?_)
    rw [Hopf.mem_augIdeal_iff, G.counit_transition]
    exact hc
  | zero => rw [zero_pow hp.out.ne_zero]; exact Ideal.zero_mem _
  | add z w _ _ hz hw => rw [add_pow_char' hA]; exact Ideal.add_mem _ hz hw
  | smul a z _ hz => rw [smul_eq_mul, mul_pow]; exact Ideal.mul_mem_left _ _ hz

theorem ret_mem_of_mem_Jext {z : G.level 2} (hz : z ∈ Jext G) :
    ret G 1 z ∈ (J G 1).map (jC G 1) := by
  rw [Jext, Ideal.map, ← Ideal.submodule_span_eq, Submodule.mem_span_set] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  rw [Finsupp.sum, map_sum]
  refine Ideal.sum_mem _ fun w hw => ?_
  obtain ⟨d, hd, rfl⟩ := hc hw

  have h1 : c (jAlg G 1 d) • jAlg G 1 d = (jC G 1 d) • c (jAlg G 1 d) := by
    rw [smul_eq_mul, mul_comm]; rfl
  rw [h1, LinearMap.map_smul, smul_eq_mul, mul_comm]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (SetLike.mem_coe.1 hd))

omit hp [CharP k p] in

theorem exists_adapted_basis :
    ∃ (ι₁ ι₂ : Type) (_ : Fintype ι₁) (_ : Fintype ι₂) (e : Module.Basis (ι₁ ⊕ ι₂) k (G.level 2)),
      (∀ (i : ι₁), ∃ φ : CartierDual k (G.level 1),
          CartierDual.ofDual k (G.level 2) (e.coord (Sum.inl i)) = CartierDual.map (G.transition 1) φ) ∧
      (∀ i : ι₂, G.transition 1 (e (Sum.inr i)) = 0) := by
  let t : G.level 2 →ₗ[k] G.level 1 := (G.transitionAlgHom 1).toLinearMap
  have ht : Function.Surjective t := G.transition_surjective 1
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective t (LinearMap.range_eq_top.2 ht)
  have hts : ∀ y, t (s y) = y := fun y => DFunLike.congr_fun hs y
  let K : Submodule k (G.level 2) := LinearMap.ker t

  let L₀ : (G.level 1 × ↥K) →ₗ[k] G.level 2 := s.coprod K.subtype
  have hL₀_apply : ∀ (y : G.level 1) (z : ↥K), L₀ (y, z) = s y + z := fun y z => by
    simp [L₀]
  have hL₀ : Function.Bijective L₀ := by
    constructor
    · rintro ⟨y, z⟩ ⟨y', z'⟩ hyz
      have h1 : s y + z = s y' + z' := by rw [← hL₀_apply, ← hL₀_apply]; exact hyz
      have h2 : y = y' := by
        have := congrArg t h1
        rw [map_add, map_add, hts, hts, show t z = 0 from z.2, show t z' = 0 from z'.2,
          add_zero, add_zero] at this
        exact this
      subst h2
      have h3 : (z : G.level 2) = z' := add_left_cancel h1
      rw [Subtype.ext h3]
    · intro a
      refine ⟨(t a, ⟨a - s (t a), ?_⟩), ?_⟩
      · change t (a - s (t a)) = 0
        rw [map_sub, hts, sub_self]
      · rw [hL₀_apply]
        change s (t a) + (a - s (t a)) = a
        abel
  let L : (G.level 1 × ↥K) ≃ₗ[k] G.level 2 := LinearEquiv.ofBijective L₀ hL₀
  have hLsymm : ∀ a : G.level 2, (L.symm a).1 = t a := by
    intro a
    have hmem : a - s (t a) ∈ K := by
      change t (a - s (t a)) = 0
      rw [map_sub, hts, sub_self]
    have h1 : L (t a, ⟨a - s (t a), hmem⟩) = a := by
      change L₀ (t a, ⟨a - s (t a), hmem⟩) = a
      rw [hL₀_apply]
      change s (t a) + (a - s (t a)) = a
      abel
    rw [← LinearEquiv.eq_symm_apply] at h1
    rw [← h1]
  let b₁ := Module.Free.chooseBasis k (G.level 1)
  let b₂ := Module.Free.chooseBasis k ↥K
  refine ⟨_, _, inferInstance, inferInstance, (b₁.prod b₂).map L, ?_, ?_⟩
  · intro i
    refine ⟨CartierDual.ofDual k (G.level 1) (b₁.coord i), ?_⟩
    apply CartierDual.ext
    intro a
    change ((b₁.prod b₂).map L).repr a (Sum.inl i) = b₁.repr (G.transition 1 a) i
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.prod_repr_inl, hLsymm]
    rfl
  · intro i
    rw [Module.Basis.map_apply, Module.Basis.prod_apply]
    change t (L₀ (0, b₂ i)) = 0
    rw [hL₀_apply, map_zero, zero_add]
    exact (b₂ i).2

theorem main (x : G.level 1) (hx : ∀ φ : CartierDual k (G.level 1), (φ ^ p) x = 0) :
    x ∈ J G 1 := by
  obtain ⟨b, rfl⟩ := G.transition_surjective 1 x
  obtain ⟨ι₁, ι₂, _, _, e, he₁, he₂⟩ := exists_adapted_basis G

  have hVF := PDivisibleGroup.Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow (p := p) e b
  rw [Fintype.sum_sum_type] at hVF

  have h1 : ∀ i : ι₁, (CartierDual.ofDual k (G.level 2) (e.coord (Sum.inl i)) ^ p) b = 0 := by
    intro i
    obtain ⟨φ, hφ⟩ := he₁ i
    rw [hφ, ← map_pow, CartierDual.map_apply]
    exact hx φ
  simp only [h1, zero_smul, Finset.sum_const_zero, zero_add] at hVF

  have h2 : PDivisibleGroup.Hopf.nsmulAlgHom k (G.level 2) p b ∈ Jext G := by
    rw [hVF]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (pow_mem_Jext_of_transition_eq_zero G (he₂ i))

  rw [← jAlg_transition] at h2
  have h3 := ret_mem_of_mem_Jext G h2
  rw [show jAlg G 1 (G.transition 1 b) = (jC G 1 (G.transition 1 b) : G.level 2) from rfl,
    ret_coe] at h3
  obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective (jC G 1) (jC_surjective G 1)).1 h3
  rw [← jC_injective G 1 hyx]
  exact hy

end Main

end PDivBTH
p2m_reactivate "P2MW.S_PDivisibleGroup_mem_span_pow_of_forall_pow_apply_eq_zero.PDivBTH"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_mem_span_pow_of_forall_pow_apply_eq_zero.PDivBTH"

theorem solution
    {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {h : ℕ}
    (G : PDivisibleGroup k p h) (x : G.level 1)
    (hx : ∀ φ : CartierDual k (G.level 1), (φ ^ p) x = 0) :
    x ∈ Ideal.span ((fun a : G.level 1 => a ^ p) ''
      (PDivisibleGroup.Hopf.augIdeal k (G.level 1) : Set (G.level 1))) :=
  PDivBTH.main G x hx

end S_PDivisibleGroup_mem_span_pow_of_forall_pow_apply_eq_zero
end P2MW
export P2MW.S_PDivisibleGroup_mem_span_pow_of_forall_pow_apply_eq_zero (solution)
