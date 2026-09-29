-- Prove2me | solution 1 for PDivisibleGroup.free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ee3ce725-60f9-5a70-8a4a-fc4a30c8cc79

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

universe u u' v w w'

set_option autoImplicit false

open scoped TensorProduct
open Function Module

namespace R4K5Free

variable {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]
variable {M : Type w} [AddCommGroup M] [Module O M] [Module.Finite O M]

local notation "𝓀" => IsLocalRing.ResidueField O
local notation "𝒦" => FractionRing O

private theorem finrank_le_and_free
    : finrank 𝒦 (𝒦 ⊗[O] M) ≤ finrank 𝓀 (𝓀 ⊗[O] M) ∧
      (finrank 𝒦 (𝒦 ⊗[O] M) = finrank 𝓀 (𝓀 ⊗[O] M) → Module.Free O M) := by
  classical
  set n := finrank 𝓀 (𝓀 ⊗[O] M) with hn
  let b : Basis (Fin n) 𝓀 (𝓀 ⊗[O] M) := Module.finBasis 𝓀 (𝓀 ⊗[O] M)

  have hsurj : Surjective (TensorProduct.mk O 𝓀 M 1) :=
    TensorProduct.mk_surjective O M 𝓀 Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (b i)
  have hspan : Submodule.span O (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b fun i => hf i

  let π : (Fin n → O) →ₗ[O] M := Fintype.linearCombination O f
  have hπ : Surjective π := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]

  let πK : 𝒦 ⊗[O] (Fin n → O) →ₗ[𝒦] 𝒦 ⊗[O] M := π.baseChange 𝒦
  have hπK : Surjective πK := LinearMap.lTensor_surjective 𝒦 hπ
  have hdimn : finrank 𝒦 (𝒦 ⊗[O] (Fin n → O)) = n := by
    rw [Module.finrank_baseChange, Module.finrank_fin_fun]
  have hle : finrank 𝒦 (𝒦 ⊗[O] M) ≤ n := by
    have h := LinearMap.finrank_range_le πK
    rwa [LinearMap.range_eq_top.2 hπK, finrank_top, hdimn] at h
  refine ⟨hle, fun heq => ?_⟩

  have hinjK : Injective πK := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdimn, heq])]
    exact hπK

  have hinj : Injective π := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h1 : πK ((1 : 𝒦) ⊗ₜ[O] x) = 0 := by
      change (π.baseChange 𝒦) ((1 : 𝒦) ⊗ₜ[O] x) = 0
      rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_zero]
    have h2 : (1 : 𝒦) ⊗ₜ[O] x = 0 := hinjK (by rw [h1, map_zero])
    have h3 : ∀ i, algebraMap O 𝒦 (x i) = 0 := by
      intro i
      have := congrArg (fun z => TensorProduct.piScalarRight O 𝒦 𝒦 (Fin n) z i) h2
      simpa [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul] using this
    rw [Submodule.mem_bot]
    funext i
    exact (IsFractionRing.injective O 𝒦) ((h3 i).trans (map_zero _).symm)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective π ⟨hinj, hπ⟩)

end R4K5Free

namespace R4K5BC

section Fibre

variable {O : Type u} [CommRing O] {κ : Type u'} [CommRing κ] [Algebra O κ]
variable {A : Type v} [CommRing A] [Bialgebra O A]

private noncomputable def redLeft (κ : Type u') [CommRing κ] [Algebra O κ] (A : Type v) [CommRing A]
    [Algebra O A] : A →ₐ[O] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A) :=
  (Algebra.TensorProduct.includeLeft (S := O)).comp Algebra.TensorProduct.includeRight

private noncomputable def redRight (κ : Type u') [CommRing κ] [Algebra O κ] (A : Type v) [CommRing A]
    [Algebra O A] : A →ₐ[O] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A) :=
  ((Algebra.TensorProduct.includeRight :
        κ ⊗[O] A →ₐ[κ] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A)).restrictScalars O).comp
      Algebra.TensorProduct.includeRight

private noncomputable def pi2 (κ : Type u') [CommRing κ] [Algebra O κ] (A : Type v) [CommRing A]
    [Algebra O A] : A ⊗[O] A →ₐ[O] (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A) :=
  Algebra.TensorProduct.lift (redLeft κ A) (redRight κ A)
    (fun _ _ => Commute.all (S := (κ ⊗[O] A) ⊗[κ] (κ ⊗[O] A)) _ _)

private theorem pi2_tmul (x y : A) :
    pi2 κ A (x ⊗ₜ[O] y) = ((1 : κ) ⊗ₜ[O] x) ⊗ₜ[κ] ((1 : κ) ⊗ₜ[O] y) := by
  rw [pi2, Algebra.TensorProduct.lift_tmul]
  change (((1 : κ) ⊗ₜ[O] x) ⊗ₜ[κ] (1 : κ ⊗[O] A)) * ((1 : κ ⊗[O] A) ⊗ₜ[κ] ((1 : κ) ⊗ₜ[O] y)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem comul_one_tmul (a : A) :
    Coalgebra.comul (R := κ) ((1 : κ) ⊗ₜ[O] a) = pi2 κ A (Coalgebra.comul (R := O) a) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply κ 1]
  induction Coalgebra.comul (R := O) a using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul x y =>
    rw [pi2_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

private theorem counit_tmul' (c : κ) (a : A) :
    Coalgebra.counit (R := κ) (c ⊗ₜ[O] a) = algebraMap O κ (Coalgebra.counit (R := O) a) * c := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def]

private theorem convMul_apply_one_tmul {T : Type w} [CommRing T] [Algebra κ T] [Algebra O T]
    [IsScalarTower O κ T]
    (φ ψ : WithConv (κ ⊗[O] A →ₐ[κ] T)) (a : A) :
    (φ * ψ) ((1 : κ) ⊗ₜ[O] a) =
      Algebra.TensorProduct.lift
        ((φ.ofConv.restrictScalars O).comp Algebra.TensorProduct.includeRight)
        ((ψ.ofConv.restrictScalars O).comp Algebra.TensorProduct.includeRight)
        (fun _ _ => Commute.all (S := T) _ _) (Coalgebra.comul (R := O) a) := by
  rw [AlgHom.convMul_apply, comul_one_tmul]
  induction Coalgebra.comul (R := O) a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [pi2_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem nsmulAlgHom_tmul (n : ℕ) (c : κ) (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n (c ⊗ₜ[O] a) =
      c ⊗ₜ[O] PDivisibleGroup.Hopf.nsmulAlgHom O A n a := by

  have key : ∀ a : A, PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n ((1 : κ) ⊗ₜ[O] a) =
      (1 : κ) ⊗ₜ[O] PDivisibleGroup.Hopf.nsmulAlgHom O A n a := by
    induction n with
    | zero =>
      intro a
      rw [PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply,
        counit_tmul', mul_one, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | succ n ih =>
      intro a
      rw [PDivisibleGroup.Hopf.nsmulAlgHom_succ, PDivisibleGroup.Hopf.nsmulAlgHom_succ]
      change (WithConv.toConv (PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n) *
          WithConv.toConv (AlgHom.id κ (κ ⊗[O] A))) ((1 : κ) ⊗ₜ[O] a) =
        (1 : κ) ⊗ₜ[O] (WithConv.toConv (PDivisibleGroup.Hopf.nsmulAlgHom O A n) *
          WithConv.toConv (AlgHom.id O A)) a
      rw [convMul_apply_one_tmul, AlgHom.convMul_apply]
      induction Coalgebra.comul (R := O) a using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.tmul_zero]
      | tmul x y =>
        rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
        change PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n ((1 : κ) ⊗ₜ[O] x) * ((1 : κ) ⊗ₜ[O] y) =
          (1 : κ) ⊗ₜ[O] (PDivisibleGroup.Hopf.nsmulAlgHom O A n x * y)
        rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  have hc : c ⊗ₜ[O] a = c • ((1 : κ) ⊗ₜ[O] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hc, map_smul, key, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem nsmulAlgHom_baseChange (n : ℕ) :
    PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n =
      Algebra.TensorProduct.map (AlgHom.id κ κ) (PDivisibleGroup.Hopf.nsmulAlgHom O A n) := by
  refine Algebra.TensorProduct.ext' fun c a => ?_
  rw [nsmulAlgHom_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

private theorem augIdeal_baseChange :
    PDivisibleGroup.Hopf.augIdeal κ (κ ⊗[O] A) =
      (PDivisibleGroup.Hopf.augIdeal O A).map
        (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) := by

  have hsurj : Surjective (Bialgebra.counitAlgHom O A) := fun r =>
    ⟨algebraMap O A r, Bialgebra.counit_algebraMap r⟩
  have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id O κ) (Bialgebra.counitAlgHom O A)) =
      (PDivisibleGroup.Hopf.augIdeal O A).map
        (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) :=
    Algebra.TensorProduct.lTensor_ker _ hsurj

  have hfun : ∀ x : κ ⊗[O] A, Coalgebra.counit (R := κ) x =
      Algebra.TensorProduct.rid O κ κ
        (Algebra.TensorProduct.map (AlgHom.id O κ) (Bialgebra.counitAlgHom O A) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.counitAlgHom_apply,
        Algebra.TensorProduct.rid_tmul, counit_tmul', Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← hker]
  ext x
  rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, RingHom.mem_ker, hfun,
    map_eq_zero_iff _ (Algebra.TensorProduct.rid O κ κ).injective]

private theorem torsionIdeal_baseChange (n : ℕ) :
    PDivisibleGroup.Hopf.torsionIdeal κ (κ ⊗[O] A) n =
      (PDivisibleGroup.Hopf.torsionIdeal O A n).map
        (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) := by
  rw [PDivisibleGroup.Hopf.torsionIdeal, PDivisibleGroup.Hopf.torsionIdeal, augIdeal_baseChange]
  change ((PDivisibleGroup.Hopf.augIdeal O A).map
      (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A).toRingHom).map
      (PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n).toRingHom =
    ((PDivisibleGroup.Hopf.augIdeal O A).map (PDivisibleGroup.Hopf.nsmulAlgHom O A n).toRingHom).map
      (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A).toRingHom
  rw [Ideal.map_map, Ideal.map_map]

  congr 1
  refine RingHom.ext fun a => ?_
  change PDivisibleGroup.Hopf.nsmulAlgHom κ (κ ⊗[O] A) n ((1 : κ) ⊗ₜ[O] a) =
    (1 : κ) ⊗ₜ[O] PDivisibleGroup.Hopf.nsmulAlgHom O A n a
  exact nsmulAlgHom_tmul n 1 a

end Fibre

section Ker

variable {O : Type u} [CommRing O] {κ : Type u'} [CommRing κ] [Algebra O κ]
variable {A : Type v} [CommRing A] [Bialgebra O A]
variable {B : Type w} [CommRing B] [Bialgebra O B]

private theorem ker_baseChange (t : B →ₐc[O] A) (ht : Surjective t) :
    RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id κ κ) t) =
      (RingHom.ker t).map (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B) := by
  have h := Algebra.TensorProduct.lTensor_ker (A := κ) (t : B →ₐ[O] A) ht
  have hfun : ∀ x : κ ⊗[O] B, Bialgebra.TensorProduct.map (BialgHom.id κ κ) t x =
      Algebra.TensorProduct.map (AlgHom.id O κ) (t : B →ₐ[O] A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c b =>
      rw [Bialgebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have e1 : RingHom.ker (t : B →ₐ[O] A) = RingHom.ker t := Ideal.ext fun _ => Iff.rfl
  have e2 : RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id κ κ) t) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id O κ) (t : B →ₐ[O] A)) := by
    ext x
    simp only [RingHom.mem_ker, hfun x]
  rw [e2, h, e1]

private theorem surjective_baseChange (t : B →ₐc[O] A) (ht : Surjective t) :
    Surjective (Bialgebra.TensorProduct.map (BialgHom.id κ κ) t) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c a =>
    obtain ⟨b, rfl⟩ := ht a
    exact ⟨c ⊗ₜ b, Bialgebra.TensorProduct.map_tmul _ _ _ _⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

end Ker

section Quot

variable {O : Type u} [CommRing O] (κ : Type u') [Field κ] [Algebra O κ]
variable {A : Type v} [CommRing A] [Bialgebra O A]
variable {B : Type w} [CommRing B] [Bialgebra O B]

private theorem finrank_quotient_baseChange (u : B →ₐc[O] A) :
    Module.finrank κ ((κ ⊗[O] A) ⧸ Ideal.map
        (Bialgebra.TensorProduct.map (BialgHom.id κ κ) u : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B)))) =
      Module.finrank κ (κ ⊗[O] (A ⧸ Ideal.map (u : B →ₐ[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom O B)))) := by
  set I : Ideal A := Ideal.map (u : B →ₐ[O] A) (RingHom.ker (Bialgebra.counitAlgHom O B)) with hI

  have hJ : Ideal.map (Bialgebra.TensorProduct.map (BialgHom.id κ κ) u : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A)
        (RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B))) =
      I.map (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) := by
    have h1 : RingHom.ker (Bialgebra.counitAlgHom κ (κ ⊗[O] B)) =
        (RingHom.ker (Bialgebra.counitAlgHom O B)).map
          (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B) := augIdeal_baseChange
    rw [h1, hI]
    change ((RingHom.ker (Bialgebra.counitAlgHom O B)).map
        (Algebra.TensorProduct.includeRight : B →ₐ[O] κ ⊗[O] B).toRingHom).map
        (Bialgebra.TensorProduct.map (BialgHom.id κ κ) u : κ ⊗[O] B →ₐ[κ] κ ⊗[O] A).toRingHom =
      ((RingHom.ker (Bialgebra.counitAlgHom O B)).map (u : B →ₐ[O] A).toRingHom).map
        (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A).toRingHom
    rw [Ideal.map_map, Ideal.map_map]
    congr 1

  let q : κ ⊗[O] A →ₐ[κ] κ ⊗[O] (A ⧸ I) :=
    Algebra.TensorProduct.map (AlgHom.id κ κ) (Ideal.Quotient.mkₐ O I)
  have hq : Surjective q := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul c a =>
      obtain ⟨a', rfl⟩ := Ideal.Quotient.mkₐ_surjective O I a
      exact ⟨c ⊗ₜ a', Algebra.TensorProduct.map_tmul _ _ _ _⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  have hkerq : RingHom.ker q = I.map (Algebra.TensorProduct.includeRight : A →ₐ[O] κ ⊗[O] A) := by
    have h := Algebra.TensorProduct.lTensor_ker (A := κ) (Ideal.Quotient.mkₐ O I)
      (Ideal.Quotient.mkₐ_surjective O I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I := by
      ext a
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    rw [hk] at h
    rw [← h]
    have hfun : ∀ x, q x = Algebra.TensorProduct.map (AlgHom.id O κ) (Ideal.Quotient.mkₐ O I) x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c a => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    ext x
    simp only [RingHom.mem_ker, hfun x]
  rw [hJ, ← hkerq]
  exact ((Ideal.quotientKerAlgEquivOfSurjective hq).toLinearEquiv.finrank_eq)

end Quot

end R4K5BC

theorem solution
    (O : Type u) [CommRing O] [IsDomain O] [IsLocalRing O] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra O (L v)]
    [∀ v, Coalgebra.IsCocomm O (L v)] [∀ v, Module.Free O (L v)] [∀ v, Module.Finite O (L v)]
    (t : ∀ v, L (v + 1) →ₐc[O] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank O (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal O (L (v + 1)) (p ^ v))
    (L' : ℕ → Type w) [∀ v, CommRing (L' v)] [∀ v, HopfAlgebra O (L' v)]
    [∀ v, Coalgebra.IsCocomm O (L' v)] [∀ v, Module.Free O (L' v)] [∀ v, Module.Finite O (L' v)]
    (t' : ∀ v, L' (v + 1) →ₐc[O] L' v) (ht' : ∀ v, Function.Surjective (t' v))
    (hrankL' : ∀ v, Module.finrank O (L' v) = p ^ (v * h))
    (hkerL' : ∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal O (L' (v + 1)) (p ^ v))
    (f : ∀ v, L' v →ₐc[O] L v) (hf : ∀ u, (f u).comp (t' u) = (t u).comp (f (u + 1)))
    (g : ∀ v, L v →ₐc[O] L' v) (hg : ∀ u, (g u).comp (t u) = (t' u).comp (g (u + 1)))
    (w : ℕ)
    (hgf : ∀ u, (f u : L' u →ₐ[O] L u).comp (g u : L u →ₐ[O] L' u) =
      PDivisibleGroup.Hopf.nsmulAlgHom O (L u) (p ^ w))
    (hfg : ∀ u, (g u : L u →ₐ[O] L' u).comp (f u : L' u →ₐ[O] L u) =
      PDivisibleGroup.Hopf.nsmulAlgHom O (L' u) (p ^ w))
    (v : ℕ) (hv : w ≤ v) :
    Module.Free O (L v ⧸ Ideal.map (f v : L' v →ₐ[O] L v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L' v)))) ∧
    Module.Free O (L' v ⧸ Ideal.map (g v : L v →ₐ[O] L' v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L v)))) ∧
    Module.finrank O (L v ⧸ Ideal.map (f v : L' v →ₐ[O] L v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L' v)))) *
      Module.finrank O (L' v ⧸ Ideal.map (g v : L v →ₐ[O] L' v)
        (RingHom.ker (Bialgebra.counitAlgHom O (L v)))) = p ^ (w * h) := by
  classical

  set HF := L v ⧸ Ideal.map (f v : L' v →ₐ[O] L v) (RingHom.ker (Bialgebra.counitAlgHom O (L' v)))
  set HG := L' v ⧸ Ideal.map (g v : L v →ₐ[O] L' v) (RingHom.ker (Bialgebra.counitAlgHom O (L v)))
  haveI : Module.Finite O HF := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ O _).toLinearMap (Ideal.Quotient.mkₐ_surjective O _)
  haveI : Module.Finite O HG := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ O _).toLinearMap (Ideal.Quotient.mkₐ_surjective O _)

  have count : ∀ (κ : Type u) [Field κ] [Algebra O κ],
      Module.finrank κ (κ ⊗[O] HF) * Module.finrank κ (κ ⊗[O] HG) = p ^ (w * h) := by
    intro κ _ _
    have key := PDivisibleGroup.finrank_quotient_map_ker_counit_mul_eq_pow_of_comp_eq_nsmulAlgHom κ p h
      (fun v => κ ⊗[O] L v)
      (fun v => Bialgebra.TensorProduct.map (BialgHom.id κ κ) (t v))
      (fun v => R4K5BC.surjective_baseChange (t v) (ht v))
      (fun v => by rw [Module.finrank_baseChange, hrankL v])
      (fun v => by
        rw [R4K5BC.ker_baseChange (t v) (ht v), hkerL v, R4K5BC.torsionIdeal_baseChange])
      (fun v => κ ⊗[O] L' v)
      (fun v => Bialgebra.TensorProduct.map (BialgHom.id κ κ) (t' v))
      (fun v => R4K5BC.surjective_baseChange (t' v) (ht' v))
      (fun v => by rw [Module.finrank_baseChange, hrankL' v])
      (fun v => by
        rw [R4K5BC.ker_baseChange (t' v) (ht' v), hkerL' v, R4K5BC.torsionIdeal_baseChange])
      (fun v => Bialgebra.TensorProduct.map (BialgHom.id κ κ) (f v))
      (fun u => by
        refine BialgHom.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul c a =>
          change Bialgebra.TensorProduct.map (BialgHom.id κ κ) (f u)
              (Bialgebra.TensorProduct.map (BialgHom.id κ κ) (t' u) (c ⊗ₜ[O] a)) =
            Bialgebra.TensorProduct.map (BialgHom.id κ κ) (t u)
              (Bialgebra.TensorProduct.map (BialgHom.id κ κ) (f (u + 1)) (c ⊗ₜ[O] a))
          rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
            Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul]
          exact congrArg (fun y => (BialgHom.id κ κ) ((BialgHom.id κ κ) c) ⊗ₜ[O] y)
            (DFunLike.congr_fun (hf u) a)
        | add x y hx hy => simp only [map_add, hx, hy])
      (fun v => Bialgebra.TensorProduct.map (BialgHom.id κ κ) (g v))
      (fun u => by
        refine BialgHom.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul c a =>
          change Bialgebra.TensorProduct.map (BialgHom.id κ κ) (g u)
              (Bialgebra.TensorProduct.map (BialgHom.id κ κ) (t u) (c ⊗ₜ[O] a)) =
            Bialgebra.TensorProduct.map (BialgHom.id κ κ) (t' u)
              (Bialgebra.TensorProduct.map (BialgHom.id κ κ) (g (u + 1)) (c ⊗ₜ[O] a))
          rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
            Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul]
          exact congrArg (fun y => (BialgHom.id κ κ) ((BialgHom.id κ κ) c) ⊗ₜ[O] y)
            (DFunLike.congr_fun (hg u) a)
        | add x y hx hy => simp only [map_add, hx, hy])
      w
      (fun u => by
        refine AlgHom.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul c a =>
          rw [R4K5BC.nsmulAlgHom_tmul, AlgHom.comp_apply]
          change Bialgebra.TensorProduct.map (BialgHom.id κ κ) (f u)
              (Bialgebra.TensorProduct.map (BialgHom.id κ κ) (g u) (c ⊗ₜ[O] a)) = _
          rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul]
          exact congrArg (fun y => (BialgHom.id κ κ) ((BialgHom.id κ κ) c) ⊗ₜ[O] y)
            (DFunLike.congr_fun (hgf u) a)
        | add x y hx hy => simp only [map_add, hx, hy])
      (fun u => by
        refine AlgHom.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul c a =>
          rw [R4K5BC.nsmulAlgHom_tmul, AlgHom.comp_apply]
          change Bialgebra.TensorProduct.map (BialgHom.id κ κ) (g u)
              (Bialgebra.TensorProduct.map (BialgHom.id κ κ) (f u) (c ⊗ₜ[O] a)) = _
          rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul]
          exact congrArg (fun y => (BialgHom.id κ κ) ((BialgHom.id κ κ) c) ⊗ₜ[O] y)
            (DFunLike.congr_fun (hfg u) a)
        | add x y hx hy => simp only [map_add, hx, hy])
      v hv
    rw [R4K5BC.finrank_quotient_baseChange κ (f v), R4K5BC.finrank_quotient_baseChange κ (g v)] at key
    exact key

  obtain ⟨haF, hfreeF⟩ := R4K5Free.finrank_le_and_free (O := O) (M := HF)
  obtain ⟨haG, hfreeG⟩ := R4K5Free.finrank_le_and_free (O := O) (M := HG)
  have hres := count (IsLocalRing.ResidueField O)
  have hgen := count (FractionRing O)
  set a := Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] HF)
  set b := Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] HG)
  set a' := Module.finrank (FractionRing O) (FractionRing O ⊗[O] HF)
  set b' := Module.finrank (FractionRing O) (FractionRing O ⊗[O] HG)
  have hpos : 0 < p ^ (w * h) := pow_pos (Fact.out : p.Prime).pos _
  have ha'pos : 0 < a' := Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hgen; omega
  have hb'pos : 0 < b' := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hgen; omega
  have hbb : b = b' := by
    refine le_antisymm ?_ haG

    have h1 : a' * b ≤ a' * b' := by
      calc a' * b ≤ a * b := Nat.mul_le_mul_right _ haF
        _ = a' * b' := by rw [hres, hgen]
    exact Nat.le_of_mul_le_mul_left h1 ha'pos
  have haa : a = a' := by
    refine le_antisymm ?_ haF
    have h1 : a * b' ≤ a' * b' := by
      calc a * b' ≤ a * b := Nat.mul_le_mul_left _ haG
        _ = a' * b' := by rw [hres, hgen]
    exact Nat.le_of_mul_le_mul_right h1 hb'pos
  haveI hF : Module.Free O HF := hfreeF haa.symm
  haveI hG : Module.Free O HG := hfreeG hbb.symm
  refine ⟨hF, hG, ?_⟩
  rw [← Module.finrank_baseChange (R := FractionRing O) (M' := HF),
    ← Module.finrank_baseChange (R := FractionRing O) (M' := HG)]
  exact hgen

end S_PDivisibleGroup_free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom
end P2MW
export P2MW.S_PDivisibleGroup_free_quotient_map_ker_counit_of_comp_eq_nsmulAlgHom (solution)
