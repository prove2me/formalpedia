-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/267d31d7-67a7-503e-ae11-ebdce9c50f3a

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
import Theorems.Thm_CartierDual_dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin
import Theorems.Thm_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp

set_option autoImplicit false

open scoped TensorProduct
open IsLocalRing

namespace Ws50X2

theorem nsmulAlgHom_pow_eq_of_surjective {p : ℕ} [Fact p.Prime] {Rh : Type} [CommRing Rh] [Algebra Rh (ZMod p)]
    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) (v : ℕ)
    {Ge : Type} [CommRing Ge] [HopfAlgebra (ZMod p) Ge]
    (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Ge) (hπe : Function.Surjective πe) :
    PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) Ge (p ^ v) =
      (Algebra.ofId (ZMod p) Ge).comp (Bialgebra.counitAlgHom (ZMod p) Ge) := by
  have hkillB : ∀ b : ZMod p ⊗[Rh] 𝒢.level v, PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) (p ^ v) b =
      algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) (Coalgebra.counit (R := ZMod p) b) := by
    intro b
    rw [← PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange, 𝒢.nsmulAlgHom_pow_level v]
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
        Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
      congr 1
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  refine AlgHom.ext fun y => ?_
  obtain ⟨b, rfl⟩ := hπe y
  have hnat := congrArg (fun (F : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Ge) => F b)
    (PDivisibleGroup.Hopf.nsmulAlgHom_comp_bialgHom (R := ZMod p) πe (p ^ v))
  simp only [AlgHom.comp_apply] at hnat
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  show PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) Ge (p ^ v) (πe b) = _
  rw [show (πe b) = (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Ge) b from rfl, hnat, hkillB, AlgHom.commutes]
  congr 1
  exact (CoalgHomClass.counit_comp_apply πe b).symm

theorem exists_ringHom_dualBaseChangeLin {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra O (ZMod p)]
    (hO : Function.Surjective (algebraMap O (ZMod p)))
    (A : Type) [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A] [Module.Free O A] :
    ∃ s : CartierDual O A →+* CartierDual (ZMod p) (ZMod p ⊗[O] A),
      (∀ φ, s φ = CartierDual.dualBaseChangeLin O (ZMod p) A ((1 : ZMod p) ⊗ₜ[O] φ)) ∧ Function.Surjective s := by
  obtain ⟨hbij, hone, hmul, -, -⟩ := CartierDual.dualBaseChangeLin_bijective_integral O (ZMod p) A
  let sL : CartierDual O A →ₗ[O] CartierDual (ZMod p) (ZMod p ⊗[O] A) :=
    ((CartierDual.dualBaseChangeLin O (ZMod p) A).restrictScalars O) ∘ₗ (TensorProduct.mk O (ZMod p) (CartierDual O A) 1)
  have sL_apply : ∀ φ, sL φ = CartierDual.dualBaseChangeLin O (ZMod p) A ((1 : ZMod p) ⊗ₜ[O] φ) := fun φ => rfl
  refine ⟨{ toFun := sL
            map_one' := by rw [sL_apply]; exact hone
            map_mul' := fun x y => by
              rw [sL_apply, sL_apply, sL_apply, ← hmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
            map_zero' := map_zero sL
            map_add' := map_add sL }, fun φ => rfl, ?_⟩
  intro θ
  obtain ⟨w, rfl⟩ := hbij.2 θ
  obtain ⟨φ, rfl⟩ := TensorProduct.mk_surjective O (CartierDual O A) (ZMod p) hO w
  exact ⟨φ, rfl⟩

theorem exists_algHom_comp_eq {p : ℕ} [Fact p.Prime] {X Y κ : Type} [CommRing X] [CommRing Y] [Algebra (ZMod p) Y]
    [CommRing κ] [Algebra (ZMod p) κ]
    (s : X →+* Y) (hs : Function.Surjective s) (χ₀ : X →+* κ) (hker : RingHom.ker s ≤ RingHom.ker χ₀) :
    ∃ χ : Y →ₐ[ZMod p] κ, ∀ x, χ (s x) = χ₀ x := by
  let χ1 : Y →+* κ := RingHom.liftOfSurjective s hs ⟨χ₀, hker⟩
  have χ1_s : ∀ x, χ1 (s x) = χ₀ x := fun x => RingHom.liftOfSurjective_comp_apply s hs ⟨χ₀, hker⟩ x
  refine ⟨{ χ1 with
      commutes' := fun c => by
        have hc : c = ((c.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val c).symm
        rw [hc, map_natCast, RingHom.toFun_eq_coe, map_natCast, map_natCast] }, fun x => χ1_s x⟩

theorem valuation_sub_lt_one {Rh : Type} [CommRing Rh] [IsLocalRing Rh] [Algebra Rh (AlgebraicClosure ℚ)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hRloc : ∀ x : Rh, x ∈ IsLocalRing.maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {A : Type} [CommRing A] [HopfAlgebra Rh A] [Coalgebra.IsCocomm Rh A] [Module.Finite Rh A] [Module.Free Rh A]
    (Ψ' : CartierDual Rh A →ₐ[Rh] AlgebraicClosure ℚ) (hint' : ∀ φ, Ψ' φ ∈ Pl)
    (φ φ' : CartierDual Rh A) (hm : ∀ x : A, φ x - φ' x ∈ IsLocalRing.maximalIdeal Rh) :
    Pl.valuation (Ψ' φ - Ψ' φ') < 1 := by
  classical
  let bA := Module.Free.chooseBasis Rh A
  haveI : Fintype (Module.Free.ChooseBasisIndex Rh A) := Module.Free.ChooseBasisIndex.fintype Rh A
  have hexp : (CartierDual.toDual Rh _ (φ - φ')) = ∑ i, (φ - φ') (bA i) • bA.coord i :=
    (Module.Basis.sum_dual_apply_smul_coord bA (CartierDual.toDual Rh _ (φ - φ'))).symm
  have hsum : Ψ' (φ - φ') = ∑ i, algebraMap Rh (AlgebraicClosure ℚ) ((φ - φ') (bA i)) * Ψ' (CartierDual.ofDual Rh _ (bA.coord i)) := by
    conv_lhs => rw [show φ - φ' = CartierDual.ofDual Rh _ (CartierDual.toDual Rh _ (φ - φ')) from rfl, hexp]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, Algebra.smul_def]
  rw [← map_sub, hsum]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro i _
  rw [Valuation.map_mul]
  have h1 : Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) ((φ - φ') (bA i))) < 1 := (hRloc _).mp (hm (bA i))
  have h2 : Pl.valuation (Ψ' (CartierDual.ofDual Rh _ (bA.coord i))) ≤ 1 :=
    Pl.valuation_le_one ⟨_, hint' (CartierDual.ofDual Rh _ (bA.coord i))⟩
  calc Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) ((φ - φ') (bA i))) * Pl.valuation (Ψ' (CartierDual.ofDual Rh _ (bA.coord i)))
      ≤ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) ((φ - φ') (bA i))) * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact h1

end Ws50X2

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) {𝒢' : PDivisibleGroup Rh p h} (Dual : 𝒢.CartierDuality 𝒢')
    (v : ℕ)

    (f ε : 𝒢.level v →ₐc[Rh] 𝒢.level v)

    (VB : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)
    (hVB : ∀ (φ : CartierDual (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) (b : ZMod p ⊗[Rh] 𝒢.level v),
      φ (VB b) = (φ ^ p) b)

    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Gc) (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Ge)
    (Θ : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc)
      (πe : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b))

    (hV : (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc).comp
        (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) =
      (qc : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc).comp
        ((VB.comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)) :
    ∀ ψ : 𝒢'.Point (AlgebraicClosure ℚ) v,

      (∀ a : 𝒢'.level v, PDivisibleGroup.Point.toAlgHom ψ a ∈ Pl) →

      (PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map ε).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) = PDivisibleGroup.Point.toAlgHom ψ →

      ∀ a : 𝒢'.level v,
        Pl.valuation ((PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map f).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) a -
          PDivisibleGroup.Point.toAlgHom ψ a ^ p) < 1 := by
  classical
  intro ψ hint hsupp a

  haveI : IsLocalRing Rh := inferInstance
  set A := 𝒢.level v with hAdef
  set e : 𝒢'.level v ≃ₐc[Rh] CartierDual Rh (𝒢.level v) := Dual.equiv v with hedef
  set Ψ : 𝒢'.level v →ₐ[Rh] AlgebraicClosure ℚ := PDivisibleGroup.Point.toAlgHom ψ with hΨdef

  set Ψ' : CartierDual Rh (𝒢.level v) →ₐ[Rh] AlgebraicClosure ℚ := Ψ.comp ((e.symm : CartierDual Rh (𝒢.level v) ≃ₐc[Rh] 𝒢'.level v) :
      CartierDual Rh (𝒢.level v) →ₐ[Rh] 𝒢'.level v) with hΨ'def
  have hΨ'e : ∀ x : 𝒢'.level v, Ψ x = Ψ' (e x) := fun x => by
    simp only [hΨ'def, AlgHom.comp_apply]
    congr 1
    exact (e.symm_apply_apply x).symm
  have hint' : ∀ φ : CartierDual Rh (𝒢.level v), Ψ' φ ∈ Pl := fun φ => hint _

  have htr : ∀ (g : 𝒢.level v →ₐc[Rh] 𝒢.level v) (x : 𝒢'.level v),
      (PDivisibleGroup.Point.toAlgHom ψ).comp (((Dual.equiv v).symm : CartierDual Rh (𝒢.level v) →ₐc[Rh] 𝒢'.level v).comp
          ((CartierDual.map g).comp (Dual.equiv v : 𝒢'.level v →ₐc[Rh] CartierDual Rh (𝒢.level v))) :
            𝒢'.level v →ₐ[Rh] 𝒢'.level v) x = Ψ' (CartierDual.map g (e x)) := fun g x => rfl

  have hsupp' : ∀ φ : CartierDual Rh (𝒢.level v), Ψ' (CartierDual.map ε φ) = Ψ' φ := by
    intro φ
    have hx := congrArg (fun (F : 𝒢'.level v →ₐ[Rh] AlgebraicClosure ℚ) => F (e.symm φ)) hsupp
    beta_reduce at hx
    rw [htr ε (e.symm φ)] at hx
    rw [show e (e.symm φ) = φ from e.apply_symm_apply φ] at hx
    rw [hx, hΨ'e, show e (e.symm φ) = φ from e.apply_symm_apply φ]

  rw [htr f a, hΨ'e a]
  set φ₀ : CartierDual Rh (𝒢.level v) := e a with hφ₀

  let κ := IsLocalRing.ResidueField Pl
  let ρ : Pl →+* κ := IsLocalRing.residue Pl
  have hval : ∀ x y : Pl, ρ x = ρ y ↔ Pl.valuation ((x : AlgebraicClosure ℚ) - y) < 1 := by
    intro x y
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hpval : Pl.valuation ((p : AlgebraicClosure ℚ)) < 1 := by
    have h := (hres (p : Rh)).mp (by simp)
    simpa using h
  have hpκ : (p : κ) = 0 := by
    have : ((p : Pl) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by simp
    rw [← map_natCast ρ p, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, this]
    exact hpval
  haveI : CharP κ p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hpκ)
  letI : Algebra (ZMod p) κ := ZMod.algebra κ p

  have hRhsurj : Function.Surjective (algebraMap Rh (ZMod p)) := by
    intro c
    refine ⟨(c.val : Rh), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨s, s_apply, s_surj⟩ := Ws50X2.exists_ringHom_dualBaseChangeLin hRhsurj (𝒢.level v)
  have s_tmul : ∀ (φ : CartierDual Rh (𝒢.level v)) (c : ZMod p) (x : 𝒢.level v),
      s φ (c ⊗ₜ[Rh] x) = c * algebraMap Rh (ZMod p) (φ x) := by
    intro φ c x
    rw [s_apply, CartierDual.dualBaseChangeLin_tmul_tmul, one_mul]
  have s_map : ∀ (g : 𝒢.level v →ₐc[Rh] 𝒢.level v) (φ : CartierDual Rh (𝒢.level v)),
      s (CartierDual.map g φ) = CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g) (s φ) := by
    intro g φ
    rw [s_apply, s_apply, ← CartierDual.dualBaseChangeLin_lTensor_map_eq_map_baseChange_dualBaseChangeLin, LinearMap.lTensor_tmul]
    rfl

  let Ψ'P : CartierDual Rh (𝒢.level v) →+* Pl := (Ψ' : CartierDual Rh (𝒢.level v) →+* AlgebraicClosure ℚ).codRestrict Pl.toSubring hint'
  have Ψ'P_coe : ∀ φ, ((Ψ'P φ : Pl) : AlgebraicClosure ℚ) = Ψ' φ := fun φ => rfl
  obtain ⟨χ₀, χ₀_apply⟩ : ∃ χ₀ : CartierDual Rh (𝒢.level v) →+* κ, ∀ φ, χ₀ φ = ρ (Ψ'P φ) := ⟨ρ.comp Ψ'P, fun φ => rfl⟩
  have hfib : ∀ φ φ' : CartierDual Rh (𝒢.level v), s φ = s φ' → χ₀ φ = χ₀ φ' := by
    intro φ φ' hφ
    have hm : ∀ x : 𝒢.level v, φ x - φ' x ∈ IsLocalRing.maximalIdeal Rh := by
      intro x
      have h1 := congrArg (fun (θ : CartierDual (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) => θ ((1 : ZMod p) ⊗ₜ[Rh] x)) hφ
      simp only [s_tmul, one_mul] at h1
      rw [hRloc, map_sub]
      rw [← sub_eq_zero, ← map_sub, hres] at h1
      rwa [map_sub] at h1
    rw [χ₀_apply, χ₀_apply, hval, Ψ'P_coe, Ψ'P_coe]
    exact Ws50X2.valuation_sub_lt_one Pl hRloc Ψ' hint' φ φ' hm
  have hker : RingHom.ker s ≤ RingHom.ker χ₀ := by
    intro φ hφ
    rw [RingHom.mem_ker] at hφ ⊢
    rw [hfib φ 0 (by rw [hφ, map_zero]), map_zero]
  obtain ⟨chiD, chiD_s⟩ := Ws50X2.exists_algHom_comp_eq (p := p) s s_surj χ₀ hker

  obtain ⟨εb, hεb⟩ : ∃ εb : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v, εb = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ε := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb : ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v, fb = Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f := ⟨_, rfl⟩
  have s_mapε : ∀ φ, s (CartierDual.map ε φ) = CartierDual.map εb (s φ) := fun φ => by rw [s_map, ← hεb]
  have s_mapf : ∀ φ, s (CartierDual.map f φ) = CartierDual.map fb (s φ) := fun φ => by rw [s_map, ← hfb]
  rw [← hεb, ← hfb] at hV

  have hεinv : ∀ θ, chiD (CartierDual.map εb θ) = chiD θ := by
    intro θ
    obtain ⟨φ, rfl⟩ := s_surj θ
    rw [← s_mapε, chiD_s, chiD_s, χ₀_apply, χ₀_apply]
    congr 1
    exact Subtype.ext (hsupp' φ)

  have hkillGe := Ws50X2.nsmulAlgHom_pow_eq_of_surjective 𝒢 v πe hπe

  haveI : IsReduced κ := inferInstance
  have hR3 := CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
    p (ZMod p ⊗[Rh] 𝒢.level v) Gc Ge qc πe Θ hqc hπe hΘ hΘΔ v hkillGe hGe κ chiD (fb.comp εb) (VB.comp εb) hV
  have hev : chiD (CartierDual.map (fb.comp εb) (s φ₀)) = chiD (CartierDual.map (VB.comp εb) (s φ₀)) :=
    AlgHom.congr_fun hR3 (s φ₀)
  have M1 : CartierDual.map (fb.comp εb) (s φ₀) = CartierDual.map εb (CartierDual.map fb (s φ₀)) := by
    refine CartierDual.ext fun b => ?_
    simp only [CartierDual.map_apply, BialgHom.comp_apply]
  have M2 : CartierDual.map (VB.comp εb) (s φ₀) = CartierDual.map εb (CartierDual.map VB (s φ₀)) := by
    refine CartierDual.ext fun b => ?_
    simp only [CartierDual.map_apply, BialgHom.comp_apply]
  have hVt : CartierDual.map VB (s φ₀) = (s φ₀) ^ p := CartierDual.ext fun b => by
    rw [CartierDual.map_apply, hVB]
  rw [M1, M2, hεinv, hεinv, hVt, map_pow, ← s_mapf, chiD_s, chiD_s, χ₀_apply, χ₀_apply, ← map_pow] at hev
  have hfin := (hval _ _).mp hev
  have e2 : (((Ψ'P φ₀) ^ p : Pl) : AlgebraicClosure ℚ) = (Ψ' φ₀) ^ p := by
    rw [SubmonoidClass.coe_pow, Ψ'P_coe]
  rw [e2] at hfin
  exact hfin

end S_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_forall_point_valuation_cartierTranspose_sub_pow_lt_one_of_comp_eq_comp_verschiebung_of_bijective_tensorProduct_zmodp (solution)
