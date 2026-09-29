-- Prove2me | solution 1 for PDivisibleGroup.transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4846961f-df01-5490-8dea-4e78902893f4

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_PDivisibleGroup_exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
import Theorems.Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective_of_moduleFinite_baseChange_of_charZero
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing

set_option autoImplicit false

open scoped TensorProduct

theorem HQUOT.transition_apply_eq_zero_of_mem_torsionIdeal_hopfKer
    {R : Type} [CommRing R] {p : ℕ} {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v)
    (v : ℕ) [Module.Flat R ↥(HopfAlgebra.hopfKer (π (v + 1)))]
    (a : ↥(HopfAlgebra.hopfKer (π (v + 1))))
    (ha : a ∈ PDivisibleGroup.Hopf.torsionIdeal R ↥(HopfAlgebra.hopfKer (π (v + 1))) (p ^ v)) :
    G.transition v (a : G.level (v + 1)) = 0 := by
  have hle := PDivisibleGroup.Hopf.map_torsionIdeal_le (HopfAlgebra.HopfKerHopf.hopfKerVal (π (v + 1))) (p ^ v)
  have hmem : (a : G.level (v + 1)) ∈ PDivisibleGroup.Hopf.torsionIdeal R (G.level (v + 1)) (p ^ v) :=
    hle (Ideal.mem_map_of_mem _ ha)
  rw [← G.ker_transition v] at hmem
  exact hmem

namespace HQSNAKE

open scoped TensorProduct
open WithConv

theorem mem_iff_mk_eq_zero {A : Type} [CommRing A] (J : Ideal A) (a : A) : a ∈ J ↔ Ideal.Quotient.mk J a = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).symm

section Generic
variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A]

theorem nsmulAlgHom_sub_mem_torsionIdeal (n : ℕ) (x : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A n x - algebraMap R A (Coalgebra.counit (R := R) x) ∈
      PDivisibleGroup.Hopf.torsionIdeal R A n := by
  have hx : x - algebraMap R A (Coalgebra.counit (R := R) x) ∈ PDivisibleGroup.Hopf.augIdeal R A :=
    PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal R A x
  have := PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal R A hx n
  rwa [map_sub, AlgHom.commutes] at this

theorem mk_pow_eq_one (n : ℕ) :
    (toConv (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R A n)) :
        WithConv (A →ₐ[R] A ⧸ PDivisibleGroup.Hopf.torsionIdeal R A n)) ^ n = 1 := by
  rw [PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom, AlgHom.convOne_def]
  congr 1
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.mk _ (PDivisibleGroup.Hopf.nsmulAlgHom R A n x) =
    algebraMap R (A ⧸ PDivisibleGroup.Hopf.torsionIdeal R A n) (Coalgebra.counit (R := R) x)
  rw [IsScalarTower.algebraMap_apply R A (A ⧸ PDivisibleGroup.Hopf.torsionIdeal R A n), Ideal.Quotient.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact nsmulAlgHom_sub_mem_torsionIdeal n x

theorem toConv_comp_mul {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (f : S →ₐ[R] S') (φ ψ : WithConv (A →ₐ[R] S)) :
    toConv (f.comp (φ * ψ).ofConv) = toConv (f.comp φ.ofConv) * toConv (f.comp ψ.ofConv) := by
  rw [AlgHom.comp_convMul_distrib]

theorem toConv_comp_one {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (f : S →ₐ[R] S') : toConv (f.comp (1 : WithConv (A →ₐ[R] S)).ofConv) = (1 : WithConv (A →ₐ[R] S')) := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, ← AlgHom.comp_assoc, Algebra.comp_ofId]

theorem toConv_comp_pow {S S' : Type} [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
    (f : S →ₐ[R] S') (φ : WithConv (A →ₐ[R] S)) (n : ℕ) :
    toConv (f.comp (φ ^ n).ofConv) = toConv (f.comp φ.ofConv) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toConv_comp_one]
  | succ n ih => rw [pow_succ, pow_succ, toConv_comp_mul, ih]

end Generic

section Root
variable {R : Type} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {t : ℕ} (T : PDivisibleGroup R p t)

theorem exists_faithfullyFlat_pow_p_eq (v : ℕ) (S' : Type) [CommRing S'] [Algebra R S']
    (ξ : WithConv (T.level (v + 1) →ₐ[R] S')) (hξ : ξ ^ (p ^ v) = 1) :
    ∃ (S'' : Type) (_ : CommRing S'') (_ : Algebra R S'') (_ : Algebra S' S'') (_ : IsScalarTower R S' S'')
      (_ : Module.FaithfullyFlat S' S'') (η : WithConv (T.level (v + 1) →ₐ[R] S'')),
      η ^ p = toConv ((IsScalarTower.toAlgHom R S' S'').comp ξ.ofConv) := by
  classical
  obtain ⟨m, hmt, htm, hinj, haug, hff⟩ :=
    PDivisibleGroup.exists_bialgHom_comp_transition_eq_nsmulBialgHom_and_injective_and_map_ker_counit_eq_torsionIdeal_and_faithfullyFlat
      p T v

  obtain ⟨ξv, hξv⟩ := PDivisibleGroup.Hopf.exists_comp_eq_of_pow_eq_one (T.transition v) (T.transition_surjective v) (p ^ v)
    (T.ker_transition v) ξ hξ

  letI algm : Algebra (T.level v) (T.level (v + 1)) := (m : T.level v →ₐ[R] T.level (v + 1)).toRingHom.toAlgebra
  haveI : IsScalarTower R (T.level v) (T.level (v + 1)) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((m : T.level v →ₐ[R] T.level (v + 1)).commutes r).symm)
  haveI : Module.FaithfullyFlat (T.level v) (T.level (v + 1)) := hff
  letI algξ : Algebra (T.level v) S' := ξv.toRingHom.toAlgebra
  haveI : IsScalarTower R (T.level v) S' := IsScalarTower.of_algebraMap_eq (fun r => (ξv.commutes r).symm)
  let S'' := S' ⊗[T.level v] T.level (v + 1)
  refine ⟨S'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    toConv ((Algebra.TensorProduct.includeRight : T.level (v + 1) →ₐ[T.level v] S'').restrictScalars R), ?_⟩

  rw [PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom, ← hmt]
  congr 1
  rw [← AlgHom.comp_assoc]
  have key : ((Algebra.TensorProduct.includeRight : T.level (v + 1) →ₐ[T.level v] S'').restrictScalars R).comp
        (m : T.level v →ₐ[R] T.level (v + 1)) = (IsScalarTower.toAlgHom R S' S'').comp ξv := by
    apply AlgHom.ext
    intro b
    change (1 : S') ⊗ₜ[T.level v] (m b) = (algebraMap S' S'') (ξv b)
    have h1 : (m b : T.level (v + 1)) = b • (1 : T.level (v + 1)) := by
      rw [Algebra.smul_def, mul_one]; rfl
    have h2 : (algebraMap S' S'') (ξv b) = (ξv b) ⊗ₜ[T.level v] (1 : T.level (v + 1)) := rfl
    have h3 : (ξv b : S') = b • (1 : S') := by rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, h2, h3, TensorProduct.smul_tmul]
  rw [key, AlgHom.comp_assoc, hξv]

theorem exists_faithfullyFlat_pow_pow_eq (v : ℕ) (S₁ : Type) [CommRing S₁] [Algebra R S₁]
    (χ : WithConv (T.level (v + 1) →ₐ[R] S₁)) (hχ : χ ^ p = 1) :
    ∀ j : ℕ, j ≤ v → ∃ (S'' : Type) (_ : CommRing S'') (_ : Algebra R S'') (_ : Algebra S₁ S'') (_ : IsScalarTower R S₁ S'')
      (_ : Module.FaithfullyFlat S₁ S'') (η : WithConv (T.level (v + 1) →ₐ[R] S'')),
      η ^ (p ^ j) = toConv ((IsScalarTower.toAlgHom R S₁ S'').comp χ.ofConv) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨S₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, χ, ?_⟩
    rw [pow_zero, pow_one]
    apply WithConv.ext
    apply AlgHom.ext; intro x; rfl
  | succ j ih =>
    intro hj
    obtain ⟨Sj, _, _, _, _, hffj, ηj, hηj⟩ := ih (Nat.le_of_succ_le hj)

    have hkill : ηj ^ (p ^ v) = 1 := by
      have h1 : ηj ^ (p ^ (j + 1)) = 1 := by
        rw [pow_succ, pow_mul, hηj, ← HQSNAKE.toConv_comp_pow, hχ, HQSNAKE.toConv_comp_one]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
      have hpv : p ^ v = p ^ (j + 1) * p ^ k := by rw [hk, pow_add]
      rw [hpv, pow_mul, h1, one_pow]
    obtain ⟨S'', _, _, _, _, hff', η', hη'⟩ := exists_faithfullyFlat_pow_p_eq T v Sj ηj hkill
    letI algS : Algebra S₁ S'' := ((algebraMap Sj S'').comp (algebraMap S₁ Sj)).toAlgebra
    haveI : IsScalarTower S₁ Sj S'' := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsScalarTower R S₁ S'' := IsScalarTower.of_algebraMap_eq (fun r => by
      change algebraMap R S'' r = (algebraMap Sj S'') (algebraMap S₁ Sj (algebraMap R S₁ r))
      rw [← IsScalarTower.algebraMap_apply R S₁ Sj, ← IsScalarTower.algebraMap_apply R Sj S''])
    haveI : Module.FaithfullyFlat S₁ S'' := Module.FaithfullyFlat.trans S₁ Sj S''
    refine ⟨S'', inferInstance, inferInstance, algS, inferInstance, inferInstance, η', ?_⟩
    rw [pow_succ', pow_mul, hη', ← HQSNAKE.toConv_comp_pow, hηj]
    apply WithConv.ext
    apply AlgHom.ext; intro x; rfl

end Root

end HQSNAKE

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (p : ℕ) [Fact p.Prime] {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v))
    (v : ℕ) [Module.Flat R ↥(HopfAlgebra.hopfKer (π (v + 1)))]
    (a : ↥(HopfAlgebra.hopfKer (π (v + 1)))) :
    G.transition v (a : G.level (v + 1)) = 0 ↔
      a ∈ PDivisibleGroup.Hopf.torsionIdeal R ↥(HopfAlgebra.hopfKer (π (v + 1))) (p ^ v) := by
  constructor
  · intro hτ
    classical

    have hπv := hπ (v + 1)

    haveI : Algebra.FiniteType R (G.level (v + 1)) := inferInstance
    obtain ⟨-, hffK, -⟩ :=
      HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective_of_moduleFinite_baseChange_of_charZero
        R (G.level (v + 1)) K (T.level (v + 1)) (π (v + 1)) hπv
    haveI := hffK

    let J₂ := PDivisibleGroup.Hopf.torsionIdeal R ↥(HopfAlgebra.hopfKer (π (v + 1))) (p ^ v)
    rw [HQSNAKE.mem_iff_mk_eq_zero]
    let S := ↥(HopfAlgebra.hopfKer (π (v + 1))) ⧸ J₂
    let u : ↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] S := Ideal.Quotient.mkₐ R J₂
    have hu : (WithConv.toConv u) ^ (p ^ v) = 1 := HQSNAKE.mk_pow_eq_one (A := ↥(HopfAlgebra.hopfKer (π (v + 1)))) (p ^ v)

    let S₁ := S ⊗[↥(HopfAlgebra.hopfKer (π (v + 1)))] G.level (v + 1)
    haveI : Module.FaithfullyFlat S S₁ := inferInstance
    let g : G.level (v + 1) →ₐ[R] S₁ := (Algebra.TensorProduct.includeRight : G.level (v + 1) →ₐ[↥(HopfAlgebra.hopfKer (π (v + 1)))] S₁).restrictScalars R
    let ι₁ : S →ₐ[R] S₁ := (Algebra.TensorProduct.includeLeft : S →ₐ[↥(HopfAlgebra.hopfKer (π (v + 1)))] S₁).restrictScalars R
    have hg_val : g.comp (HopfAlgebra.hopfKer (π (v + 1))).val = ι₁.comp u := by
      apply AlgHom.ext
      intro k
      change (1 : S) ⊗ₜ[↥(HopfAlgebra.hopfKer (π (v + 1)))] ((k : ↥(HopfAlgebra.hopfKer (π (v + 1)))) : G.level (v + 1)) = (Ideal.Quotient.mk J₂ k) ⊗ₜ[↥(HopfAlgebra.hopfKer (π (v + 1)))] (1 : G.level (v + 1))
      have hk : ((k : ↥(HopfAlgebra.hopfKer (π (v + 1)))) : G.level (v + 1)) = k • (1 : G.level (v + 1)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      have hk' : (Ideal.Quotient.mk J₂ k : S) = k • (1 : S) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [hk, hk', TensorProduct.smul_tmul]

    have h9 := HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique (π (v + 1)) hπv S₁
    let ρ : WithConv (G.level (v + 1) →ₐ[R] S₁) → WithConv (↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] S₁) :=
      fun ν => WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer (π (v + 1))).val)
    let ρM : WithConv (G.level (v + 1) →ₐ[R] S₁) →* WithConv (↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] S₁) :=
      { toFun := ρ, map_one' := h9.1, map_mul' := h9.2.1 }
    have hρ_pow : ∀ (ν : WithConv (G.level (v + 1) →ₐ[R] S₁)) (n : ℕ), ρ (ν ^ n) = ρ ν ^ n :=
      fun ν n => map_pow ρM ν n
    let y : WithConv (G.level (v + 1) →ₐ[R] S₁) := (WithConv.toConv g) ^ (p ^ v)
    have hρg : ρ (WithConv.toConv g) = WithConv.toConv (ι₁.comp u) := by
      change WithConv.toConv (g.comp (HopfAlgebra.hopfKer (π (v + 1))).val) = _
      rw [hg_val]
    have hρy : ρ y = 1 := by
      change ρ ((WithConv.toConv g) ^ (p ^ v)) = 1
      rw [hρ_pow, hρg, ← HQSNAKE.toConv_comp_pow ι₁ (WithConv.toConv u) (p ^ v), hu]
      exact HQSNAKE.toConv_comp_one ι₁
    have hres : (WithConv.ofConv (1 : WithConv (G.level (v + 1) →ₐ[R] S₁))).comp (HopfAlgebra.hopfKer (π (v + 1))).val =
        (WithConv.ofConv y).comp (HopfAlgebra.hopfKer (π (v + 1))).val := by
      have h1 := h9.1
      have : ρ 1 = ρ y := h1.trans hρy.symm
      exact congrArg WithConv.ofConv this
    obtain ⟨χ, hχ0, hχuniq⟩ := (h9.2.2 1 y).mp hres
    have hχ : y = WithConv.toConv (χ.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) :=
      hχ0.trans (one_mul (M := WithConv (G.level (v + 1) →ₐ[R] S₁)) _)

    have hχp : (WithConv.toConv χ) ^ p = 1 := by
      have hyp : y ^ p = 1 := by
        have e1 : y ^ p = (WithConv.toConv g) ^ (p ^ (v + 1)) := by
          change ((WithConv.toConv g) ^ (p ^ v)) ^ p = _
          rw [pow_succ]
          exact (pow_mul (M := WithConv (G.level (v + 1) →ₐ[R] S₁)) (WithConv.toConv g) (p ^ v) p).symm
        rw [e1]; exact G.point_pow_eq_one (v + 1) (WithConv.toConv g)
      rw [hχ] at hyp

      have hcomp : (WithConv.toConv (χ.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1)))) ^ p =
          WithConv.toConv (((WithConv.toConv χ) ^ p).ofConv.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) := by
        rw [PDivisibleGroup.Hopf.convPow_comp_bialgHom]
      rw [hcomp] at hyp
      have h1 : WithConv.toConv ((WithConv.ofConv (1 : WithConv (T.level (v + 1) →ₐ[R] S₁))).comp
          (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) = (1 : WithConv (G.level (v + 1) →ₐ[R] S₁)) := by
        rw [AlgHom.convOne_def, AlgHom.convOne_def]
        congr 1
        apply AlgHom.ext; intro x
        change algebraMap R S₁ (Coalgebra.counit (R := R) (π (v + 1) x)) = algebraMap R S₁ (Coalgebra.counit (R := R) x)
        rw [PDivisibleGroup.Hopf.counit_bialgHom_apply]
      rw [← h1] at hyp
      have hinj := PDivisibleGroup.Hopf.comp_injective_of_surjective (π (v + 1)) hπv (L := S₁)
      have := hinj (congrArg WithConv.ofConv hyp)
      exact congrArg WithConv.toConv this

    obtain ⟨S₂, _, _, _, _, hff2, η, hη⟩ :=
      HQSNAKE.exists_faithfullyFlat_pow_pow_eq T v S₁ (WithConv.toConv χ) hχp v le_rfl
    let f : S₁ →ₐ[R] S₂ := IsScalarTower.toAlgHom R S₁ S₂

    let g₂ : WithConv (G.level (v + 1) →ₐ[R] S₂) := WithConv.toConv (f.comp g)
    let ζ : WithConv (G.level (v + 1) →ₐ[R] S₂) :=
      WithConv.toConv (η.ofConv.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1)))
    have hζ : ζ ^ (p ^ v) = g₂ ^ (p ^ v) := by
      have e1 : ζ ^ (p ^ v) = WithConv.toConv ((η ^ (p ^ v)).ofConv.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) :=
        (congrArg WithConv.toConv (PDivisibleGroup.Hopf.convPow_comp_bialgHom η (π (v + 1)) (p ^ v))).symm
      have e2 : g₂ ^ (p ^ v) = WithConv.toConv (f.comp y.ofConv) := by
        change (WithConv.toConv (f.comp g)) ^ (p ^ v) = _
        rw [← HQSNAKE.toConv_comp_pow f (WithConv.toConv g)]
      rw [e1, e2, hη, hχ]
      rfl
    obtain ⟨ζu, hζu⟩ := PDivisibleGroup.Hopf.isUnit_toConv_algHom (R := R)
      (η.ofConv.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1)))
    let ζinv : WithConv (G.level (v + 1) →ₐ[R] S₂) := ((ζu⁻¹ : (WithConv (G.level (v + 1) →ₐ[R] S₂))ˣ) : WithConv (G.level (v + 1) →ₐ[R] S₂))
    have hζinv : ζ * ζinv = 1 := by
      have hz : ζ = (ζu : WithConv (G.level (v + 1) →ₐ[R] S₂)) := hζu.symm
      change ζ * ((ζu⁻¹ : (WithConv (G.level (v + 1) →ₐ[R] S₂))ˣ) : WithConv _) = 1
      rw [hz, Units.mul_inv]
    let g' : WithConv (G.level (v + 1) →ₐ[R] S₂) := g₂ * ζinv
    have hg' : g' ^ (p ^ v) = 1 := by
      change (g₂ * ζinv) ^ (p ^ v) = 1
      rw [mul_pow, ← hζ, ← mul_pow, hζinv, one_pow]
    obtain ⟨gv, hgv⟩ := PDivisibleGroup.Hopf.exists_comp_eq_of_pow_eq_one (G.transition v) (G.transition_surjective v) (p ^ v)
      (G.ker_transition v) g' hg'

    have h9₂ := HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique (π (v + 1)) hπv S₂
    let ρ₂ : WithConv (G.level (v + 1) →ₐ[R] S₂) → WithConv (↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] S₂) :=
      fun ν => WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer (π (v + 1))).val)
    have hρζ : ρ₂ ζ = 1 := by
      have : (WithConv.ofConv (1 : WithConv (G.level (v + 1) →ₐ[R] S₂))).comp (HopfAlgebra.hopfKer (π (v + 1))).val =
          (WithConv.ofConv ζ).comp (HopfAlgebra.hopfKer (π (v + 1))).val := by
        refine (h9₂.2.2 1 ζ).mpr ⟨η.ofConv, ?_, ?_⟩
        · exact (one_mul (M := WithConv (G.level (v + 1) →ₐ[R] S₂)) _).symm
        · intro χ' hχ'
          have e := hχ'.symm.trans (one_mul (M := WithConv (G.level (v + 1) →ₐ[R] S₂)) _).symm |>.symm
          have hinj := PDivisibleGroup.Hopf.comp_injective_of_surjective (π (v + 1)) hπv (L := S₂)
          have e2 : WithConv.toConv (χ'.comp (π (v + 1) : G.level (v + 1) →ₐ[R] T.level (v + 1))) = ζ := by
            have := hχ'.symm
            rw [one_mul (M := WithConv (G.level (v + 1) →ₐ[R] S₂))] at this
            exact this
          exact hinj (congrArg WithConv.ofConv e2)
      have e := congrArg WithConv.toConv this
      rw [h9₂.1] at e
      exact e.symm
    have hρinv : ρ₂ ζinv = 1 := by
      have := h9₂.2.1 ζ ζinv
      change ρ₂ (ζ * ζinv) = ρ₂ ζ * ρ₂ ζinv at this
      rw [hζinv, hρζ, one_mul (M := WithConv (↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] S₂))] at this
      exact this.symm.trans h9₂.1
    have hρg' : ρ₂ g' = WithConv.toConv ((f.comp ι₁).comp u) := by
      have := h9₂.2.1 g₂ ζinv
      change ρ₂ (g₂ * ζinv) = ρ₂ g₂ * ρ₂ ζinv at this
      rw [hρinv, mul_one (M := WithConv (↥(HopfAlgebra.hopfKer (π (v + 1))) →ₐ[R] S₂))] at this
      rw [this]
      change WithConv.toConv ((f.comp g).comp (HopfAlgebra.hopfKer (π (v + 1))).val) = _
      rw [AlgHom.comp_assoc, hg_val, ← AlgHom.comp_assoc]

    have hval : (f.comp ι₁) (u a) = 0 := by
      have e1 : ((f.comp ι₁).comp u) a = (WithConv.ofConv (ρ₂ g')) a := by
        rw [hρg']
      rw [AlgHom.comp_apply] at e1
      rw [e1]
      change (WithConv.ofConv g') ((a : ↥(HopfAlgebra.hopfKer (π (v + 1)))) : G.level (v + 1)) = 0
      rw [← hgv, AlgHom.comp_apply]
      change gv (G.transition v (a : G.level (v + 1))) = 0
      rw [hτ, map_zero]

    letI algS2 : Algebra S S₂ := ((algebraMap S₁ S₂).comp (algebraMap S S₁)).toAlgebra
    haveI : IsScalarTower S S₁ S₂ := IsScalarTower.of_algebraMap_eq (R := S) (S := S₁) (A := S₂) (fun x => rfl)
    haveI : Module.FaithfullyFlat S S₂ := Module.FaithfullyFlat.trans S S₁ S₂
    have hinjS : Function.Injective (algebraMap S S₂) := FaithfulSMul.algebraMap_injective S S₂
    apply hinjS
    rw [map_zero]
    exact hval
  · exact HQUOT.transition_apply_eq_zero_of_mem_torsionIdeal_hopfKer G T π v a

end S_PDivisibleGroup_transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
end P2MW
export P2MW.S_PDivisibleGroup_transition_apply_eq_zero_iff_mem_torsionIdeal_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing (solution)
