-- Prove2me | solution 1 for PDivisibleGroup.exists_formallyEtale_tower_bijective_baseChange_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7e5bfeba-217e-565b-b29e-657f380ae23d

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_HopfAlgebra_exists_formallyEtale_bialgEquiv_baseChange_zmodp
import Theorems.Thm_Bialgebra_existsUnique_bialgHom_baseChange_eq_zmodp
import Theorems.Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
import Theorems.Thm_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp

set_option autoImplicit false

open scoped TensorProduct
open Function PDivisibleGroup.Hopf

universe u v w

namespace EtLiftTower

section Fibre

variable {𝓞 : Type*} [CommRing 𝓞] {κ : Type*} [CommRing κ] [Algebra 𝓞 κ]
variable {A : Type*} [CommRing A]

private theorem includeRight_surjective [Algebra 𝓞 A] (hκ : Surjective (algebraMap 𝓞 κ)) :
    Surjective (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c a =>
    obtain ⟨o, rfl⟩ := hκ c
    refine ⟨o • a, ?_⟩
    rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, map_add _ _ _⟩

variable [Bialgebra 𝓞 A]

private theorem counit_tmul' (c : κ) (a : A) :
    Coalgebra.counit (R := κ) (c ⊗ₜ[𝓞] a) = algebraMap 𝓞 κ (Coalgebra.counit (R := 𝓞) a) * c := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def]

private theorem counit_eq_rid_map (x : κ ⊗[𝓞] A) :
    Coalgebra.counit (R := κ) x =
      Algebra.TensorProduct.rid 𝓞 𝓞 κ
        (Algebra.TensorProduct.map (AlgHom.id 𝓞 κ) (Bialgebra.counitAlgHom 𝓞 A) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    rw [counit_tmul', Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
      Bialgebra.counitAlgHom_apply, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem counitAlgHom_surjective : Surjective (Bialgebra.counitAlgHom 𝓞 A) := fun r =>
  ⟨algebraMap 𝓞 A r, by rw [Bialgebra.counitAlgHom_apply, Bialgebra.counit_algebraMap]⟩

private theorem augIdeal_baseChange :
    augIdeal κ (κ ⊗[𝓞] A) = (augIdeal 𝓞 A).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  have hker : (augIdeal 𝓞 A).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id 𝓞 κ) (Bialgebra.counitAlgHom 𝓞 A)) :=
    (Algebra.TensorProduct.lTensor_ker _ counitAlgHom_surjective).symm
  ext x
  rw [mem_augIdeal_iff, hker, RingHom.mem_ker, counit_eq_rid_map,
    map_eq_zero_iff _ (Algebra.TensorProduct.rid 𝓞 𝓞 κ).injective]

private theorem nsmulAlgHom_comp_includeRight (n : ℕ) :
    ((nsmulAlgHom κ (κ ⊗[𝓞] A) n : κ ⊗[𝓞] A →+* κ ⊗[𝓞] A)).comp
        (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) =
      ((Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) : A →+* κ ⊗[𝓞] A).comp
        (nsmulAlgHom 𝓞 A n : A →+* A) := by
  refine RingHom.ext fun a => ?_
  change nsmulAlgHom κ (κ ⊗[𝓞] A) n ((1 : κ) ⊗ₜ[𝓞] a) = (1 : κ) ⊗ₜ[𝓞] nsmulAlgHom 𝓞 A n a
  rw [← PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange 𝓞 κ A n,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

private theorem torsionIdeal_baseChange (n : ℕ) :
    torsionIdeal κ (κ ⊗[𝓞] A) n =
      (torsionIdeal 𝓞 A n).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  rw [torsionIdeal, torsionIdeal, augIdeal_baseChange]
  change ((augIdeal 𝓞 A).map
      ((Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) : A →+* κ ⊗[𝓞] A)).map
      (nsmulAlgHom κ (κ ⊗[𝓞] A) n : κ ⊗[𝓞] A →+* κ ⊗[𝓞] A) =
    ((augIdeal 𝓞 A).map (nsmulAlgHom 𝓞 A n : A →+* A)).map
      ((Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) : A →+* κ ⊗[𝓞] A)
  rw [Ideal.map_map, Ideal.map_map, nsmulAlgHom_comp_includeRight]

private theorem map_id_unit_comp_counit :
    Algebra.TensorProduct.map (AlgHom.id κ κ) ((Algebra.ofId 𝓞 A).comp (Bialgebra.counitAlgHom 𝓞 A)) =
      (Algebra.ofId κ (κ ⊗[𝓞] A)).comp (Bialgebra.counitAlgHom κ (κ ⊗[𝓞] A)) := by
  refine AlgHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply,
      Bialgebra.counitAlgHom_apply, AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply,
      counit_tmul', Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

end Fibre

section KerRed

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]

private theorem exists_ringEquiv_quotient_tensor
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (S : Type*) [CommRing S] [Algebra 𝓞 S] :
    ∃ τ : (S ⧸ (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 S)) ≃+* ZMod p ⊗[𝓞] S,
      ∀ s : S, τ (Ideal.Quotient.mk _ s) = (1 : ZMod p) ⊗ₜ[𝓞] s := by
  have hsurj : Function.Surjective (Algebra.ofId 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hker' : Ideal.span {(p : 𝓞)} = RingHom.ker (Algebra.ofId 𝓞 (ZMod p)) := hker.symm
  let ι : (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ≃ₐ[𝓞] ZMod p :=
    (Ideal.quotientEquivAlgOfEq 𝓞 hker').trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {(p : 𝓞)})
  let e₂ := Algebra.TensorProduct.comm 𝓞 S (𝓞 ⧸ Ideal.span {(p : 𝓞)})
  let e₃ : (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⊗[𝓞] S ≃ₐ[𝓞] ZMod p ⊗[𝓞] S :=
    Algebra.TensorProduct.congr ι (AlgEquiv.refl : S ≃ₐ[𝓞] S)
  refine ⟨e₁.toRingEquiv.trans (e₂.toRingEquiv.trans e₃.toRingEquiv), fun s => ?_⟩
  simp only [RingEquiv.coe_trans, Function.comp_apply, AlgEquiv.coe_ringEquiv]
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

private theorem includeRight_eq_zero_iff
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {S : Type*} [CommRing S] [Algebra 𝓞 S] (s : S) :
    (Algebra.TensorProduct.includeRight : S →ₐ[𝓞] ZMod p ⊗[𝓞] S) s = 0 ↔
      s ∈ (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 S) := by
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_quotient_tensor p hker S
  rw [Algebra.TensorProduct.includeRight_apply, ← hτ, map_eq_zero_iff _ τ.injective,
    Ideal.Quotient.eq_zero_iff_mem]

end KerRed

section BialgMaps

variable {R : Type*} [CommRing R] {A B : Type*} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

private theorem map_augIdeal_of_surjective (g : B →ₐc[R] A) (hg : Surjective g) :
    (augIdeal R B).map (g : B →ₐ[R] A) = augIdeal R A := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, mem_augIdeal_iff]
    change Coalgebra.counit (R := R) (g b) = 0
    rw [CoalgHomClass.counit_comp_apply]
    exact hb
  · intro a ha
    obtain ⟨b, rfl⟩ := hg a
    have hb0 : Coalgebra.counit (R := R) b = 0 := by
      rw [← CoalgHomClass.counit_comp_apply g b]; exact ha
    have hb : b ∈ augIdeal R B := hb0
    exact Ideal.mem_map_of_mem (g : B →ₐ[R] A) hb

private theorem map_torsionIdeal_of_surjective (g : B →ₐc[R] A) (hg : Surjective g) (n : ℕ) :
    (torsionIdeal R B n).map (g : B →ₐ[R] A) = torsionIdeal R A n := by
  rw [torsionIdeal, torsionIdeal, ← map_augIdeal_of_surjective g hg]
  change ((augIdeal R B).map (nsmulAlgHom R B n : B →+* B)).map ((g : B →ₐ[R] A) : B →+* A) =
    ((augIdeal R B).map ((g : B →ₐ[R] A) : B →+* A)).map (nsmulAlgHom R A n : A →+* A)
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact RingHom.ext fun b => (nsmulAlgHom_bialgHom_apply g n b).symm

private theorem nsmulAlgHom_eq_of_ker_eq_torsionIdeal (s : B →ₐc[R] A) (hs : Surjective s) (n : ℕ)
    (hkers : RingHom.ker s = torsionIdeal R B n) (a : A) :
    nsmulAlgHom R A n a = algebraMap R A (Coalgebra.counit (R := R) a) := by
  obtain ⟨b, rfl⟩ := hs a
  have hdec : b = algebraMap R B (Coalgebra.counit (R := R) b) +
      (b - algebraMap R B (Coalgebra.counit (R := R) b)) := by abel
  have hkill : s (nsmulAlgHom R B n (b - algebraMap R B (Coalgebra.counit (R := R) b))) = 0 := by
    have hmem : nsmulAlgHom R B n (b - algebraMap R B (Coalgebra.counit (R := R) b)) ∈ RingHom.ker s := by
      rw [hkers]
      exact nsmulAlgHom_mem_torsionIdeal R B (sub_algebraMap_counit_mem_augIdeal R B b) n
    exact hmem
  rw [nsmulAlgHom_bialgHom_apply]
  conv_lhs => rw [hdec]
  rw [map_add, map_add, hkill, add_zero, nsmulAlgHom_algebraMap, CoalgHomClass.counit_comp_apply]
  exact (s : B →ₐ[R] A).commutes _

private theorem nsmulAlgHom_eq_of_surjective (g : B →ₐc[R] A) (hg : Surjective g) (n : ℕ)
    (hB : ∀ b : B, nsmulAlgHom R B n b = algebraMap R B (Coalgebra.counit (R := R) b)) (a : A) :
    nsmulAlgHom R A n a = algebraMap R A (Coalgebra.counit (R := R) a) := by
  obtain ⟨b, rfl⟩ := hg a
  rw [nsmulAlgHom_bialgHom_apply, hB, CoalgHomClass.counit_comp_apply]
  exact (g : B →ₐ[R] A).commutes _

private theorem torsionIdeal_eq_bot_of_nsmulAlgHom_eq (n : ℕ)
    (hA : ∀ a : A, nsmulAlgHom R A n a = algebraMap R A (Coalgebra.counit (R := R) a)) :
    torsionIdeal R A n = ⊥ := by
  rw [← le_bot_iff, torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_bot]
  rw [hA, (mem_augIdeal_iff R A a).1 ha, map_zero]

end BialgMaps

section Level

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]

private structure LiftData (Ebar : Type v) [CommRing Ebar] [HopfAlgebra (ZMod p) Ebar] where

  carrier : Type u
  [instCommRing : CommRing carrier]
  [instHopf : HopfAlgebra 𝓞 carrier]
  [instCocomm : Coalgebra.IsCocomm 𝓞 carrier]
  [instFree : Module.Free 𝓞 carrier]
  [instFinite : Module.Finite 𝓞 carrier]
  [instEtale : Algebra.FormallyEtale 𝓞 carrier]

  finrank_eq : Module.finrank 𝓞 carrier = Module.finrank (ZMod p) Ebar

  equiv : (ZMod p ⊗[𝓞] carrier) ≃ₐc[ZMod p] Ebar

attribute [scoped instance] LiftData.instCommRing LiftData.instHopf LiftData.instCocomm LiftData.instFree
  LiftData.instFinite LiftData.instEtale

variable {𝓞 p}

private noncomputable def liftData [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Ebar : Type v) [CommRing Ebar] [HopfAlgebra (ZMod p) Ebar] [Coalgebra.IsCocomm (ZMod p) Ebar]
    [Module.Finite (ZMod p) Ebar] [IsReduced Ebar] : LiftData 𝓞 p Ebar :=
  Classical.choice <| by
    obtain ⟨H, _, _, _, _, _, _, hrk, ⟨e⟩⟩ :=
      HopfAlgebra.exists_formallyEtale_bialgEquiv_baseChange_zmodp p hp hker Ebar
    exact ⟨{ carrier := H, finrank_eq := hrk, equiv := e }⟩

end Level

section Transition

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]

include hker

include hp in

private theorem nsmulAlgHom_eq_of_baseChange
    (H : Type*) [CommRing H] [HopfAlgebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    [Algebra.FormallyEtale 𝓞 H] (n : ℕ)
    (hbar : ∀ z : ZMod p ⊗[𝓞] H, nsmulAlgHom (ZMod p) (ZMod p ⊗[𝓞] H) n z =
      algebraMap (ZMod p) (ZMod p ⊗[𝓞] H) (Coalgebra.counit (R := ZMod p) z)) (x : H) :
    nsmulAlgHom 𝓞 H n x = algebraMap 𝓞 H (Coalgebra.counit (R := 𝓞) x) := by
  have hred : Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (nsmulAlgHom 𝓞 H n) =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p))
        ((Algebra.ofId 𝓞 H).comp (Bialgebra.counitAlgHom 𝓞 H)) := by
    rw [PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange, map_id_unit_comp_counit]
    exact AlgHom.ext hbar
  obtain ⟨ψ, -, huniq⟩ :=
    Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp p hp hker H H
      (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p))
        ((Algebra.ofId 𝓞 H).comp (Bialgebra.counitAlgHom 𝓞 H)))
  have h := (huniq _ hred).trans (huniq _ rfl).symm
  exact DFunLike.congr_fun h x

variable (H₁ : Type*) [CommRing H₁] [HopfAlgebra 𝓞 H₁] [Module.Free 𝓞 H₁] [Module.Finite 𝓞 H₁]
  [Algebra.FormallyEtale 𝓞 H₁]
  (H₀ : Type*) [CommRing H₀] [HopfAlgebra 𝓞 H₀] [Module.Free 𝓞 H₀] [Module.Finite 𝓞 H₀]
  [Algebra.FormallyEtale 𝓞 H₀]

omit [Module.Free 𝓞 H₁] [Module.Finite 𝓞 H₁] [Algebra.FormallyEtale 𝓞 H₁] [Module.Free 𝓞 H₀]
  [Algebra.FormallyEtale 𝓞 H₀] in

private theorem surjective_of_surjective_baseChange (st : H₁ →ₐ[𝓞] H₀)
    (hst : Surjective (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) st)) : Surjective st := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hle : (⊤ : Submodule 𝓞 H₀) ≤ LinearMap.range st.toLinearMap ⊔ Ideal.span {(p : 𝓞)} • ⊤ := by
    intro y _
    obtain ⟨z, hz⟩ := hst (Algebra.TensorProduct.includeRight y)
    obtain ⟨x, rfl⟩ := includeRight_surjective (A := H₁) hk z
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at hz
    have hmem : y - st x ∈ (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 H₀) := by
      rw [← includeRight_eq_zero_iff p hker, map_sub, sub_eq_zero, ← hz]
      rfl
    have hmem' : y - st x ∈ (Ideal.span {(p : 𝓞)} • ⊤ : Submodule 𝓞 H₀) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
      exact hmem
    have : y = st x + (y - st x) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ hmem'
  have hN : (⊤ : Submodule 𝓞 H₀).FG := Module.Finite.fg_top
  have hjac : Ideal.span {(p : 𝓞)} ≤ (⊥ : Ideal 𝓞).jacobson := IsAdicComplete.le_jacobson_bot _
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot hN hjac hle
  intro y
  obtain ⟨x, hx⟩ := htop (Submodule.mem_top : y ∈ ⊤)
  exact ⟨x, hx⟩

omit [Module.Free 𝓞 H₁] [Algebra.FormallyEtale 𝓞 H₁] [Module.Finite 𝓞 H₀] [Algebra.FormallyEtale 𝓞 H₀] in
include hp in

private theorem ker_eq_torsionIdeal [IsNoetherianRing 𝓞] (n : ℕ) (st : H₁ →ₐc[𝓞] H₀)
    (hJK : torsionIdeal 𝓞 H₁ n ≤ RingHom.ker st)
    (hKbar : ∀ x : H₁, st x = 0 →
      (Algebra.TensorProduct.includeRight : H₁ →ₐ[𝓞] ZMod p ⊗[𝓞] H₁) x ∈
        torsionIdeal (ZMod p) (ZMod p ⊗[𝓞] H₁) n) :
    RingHom.ker st = torsionIdeal 𝓞 H₁ n := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  refine le_antisymm ?_ hJK
  let K : Submodule 𝓞 H₁ := (RingHom.ker st).restrictScalars 𝓞
  let J : Submodule 𝓞 H₁ := (torsionIdeal 𝓞 H₁ n).restrictScalars 𝓞
  have hpreg : IsSMulRegular H₀ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  have hle : K ≤ J ⊔ Ideal.span {(p : 𝓞)} • K := by
    intro x hx
    have hx0 : st x = 0 := hx
    have h1 : (Algebra.TensorProduct.includeRight : H₁ →ₐ[𝓞] ZMod p ⊗[𝓞] H₁) x ∈
        (torsionIdeal 𝓞 H₁ n).map (Algebra.TensorProduct.includeRight : H₁ →ₐ[𝓞] ZMod p ⊗[𝓞] H₁) := by
      rw [← torsionIdeal_baseChange]
      exact hKbar x hx0
    obtain ⟨j, hj, hjx⟩ := (Ideal.mem_map_iff_of_surjective _ (includeRight_surjective hk)).1 h1
    have h2 : x - j ∈ (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 H₁) := by
      rw [← includeRight_eq_zero_iff p hker, map_sub, hjx, sub_self]
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h2
    obtain ⟨h, hh⟩ := h2
    have hstj : st j = 0 := hJK hj
    have hph : (p : 𝓞) • st h = 0 := by
      have h3 : st (x - j) = 0 := by rw [map_sub, hx0, hstj, sub_zero]
      rw [← hh, map_mul] at h3
      rw [Algebra.smul_def, mul_comm]
      have h4 : st (algebraMap 𝓞 H₁ (p : 𝓞)) = algebraMap 𝓞 H₀ (p : 𝓞) := (st : H₁ →ₐ[𝓞] H₀).commutes _
      rw [← h4]
      exact h3
    have hhK : h ∈ K := by
      change st h = 0
      exact hpreg (hph.trans (smul_zero _).symm)
    have hx' : x = j + (p : 𝓞) • h := by
      rw [Algebra.smul_def, mul_comm, hh]
      abel
    rw [hx']
    exact Submodule.add_mem_sup hj (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hhK)
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hjac : Ideal.span {(p : 𝓞)} ≤ (⊥ : Ideal 𝓞).jacobson := IsAdicComplete.le_jacobson_bot _
  intro x hx
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hKfg hjac hle hx

variable {E₁ : Type*} [CommRing E₁] [HopfAlgebra (ZMod p) E₁] {E₀ : Type*} [CommRing E₀] [HopfAlgebra (ZMod p) E₀]

omit [Algebra.FormallyEtale 𝓞 H₀] in
include hp in

private theorem exists_lift_transition
    (e₁ : (ZMod p ⊗[𝓞] H₁) ≃ₐc[ZMod p] E₁) (e₀ : (ZMod p ⊗[𝓞] H₀) ≃ₐc[ZMod p] E₀) (sbar : E₁ →ₐc[ZMod p] E₀) :
    ∃ st : H₁ →ₐc[𝓞] H₀, ∀ x : ZMod p ⊗[𝓞] H₁,
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (st : H₁ →ₐ[𝓞] H₀) x = e₀.symm (sbar (e₁ x)) := by
  obtain ⟨st, hst, -⟩ := Bialgebra.existsUnique_bialgHom_baseChange_eq_zmodp p hp hker H₁ H₀
    ((e₀.symm : E₀ →ₐc[ZMod p] ZMod p ⊗[𝓞] H₀).comp
      (sbar.comp (e₁ : ZMod p ⊗[𝓞] H₁ →ₐc[ZMod p] E₁)))
  exact ⟨st, fun x => by rw [hst]; rfl⟩

include hp in

private theorem exists_transition [IsNoetherianRing 𝓞]
    (e₁ : (ZMod p ⊗[𝓞] H₁) ≃ₐc[ZMod p] E₁) (e₀ : (ZMod p ⊗[𝓞] H₀) ≃ₐc[ZMod p] E₀)
    (sbar : E₁ →ₐc[ZMod p] E₀) (hs : Surjective sbar) (n : ℕ)
    (hkers : RingHom.ker sbar = torsionIdeal (ZMod p) E₁ n) :
    ∃ st : H₁ →ₐc[𝓞] H₀,
      (∀ x, e₀ (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) st x) = sbar (e₁ x)) ∧
      Surjective st ∧ RingHom.ker st = torsionIdeal 𝓞 H₁ n := by
  obtain ⟨st, hst⟩ := exists_lift_transition p hp hker H₁ H₀ e₁ e₀ sbar
  have hmap : ∀ x, Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) st x =
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (st : H₁ →ₐ[𝓞] H₀) x := fun _ => rfl
  have hst' : ∀ x, e₀ (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) st x) = sbar (e₁ x) := by
    intro x
    rw [hmap, hst, BialgEquiv.apply_symm_apply]
  refine ⟨st, hst', ?_, ?_⟩
  · apply surjective_of_surjective_baseChange p hker H₁ H₀ (st : H₁ →ₐ[𝓞] H₀)
    intro z
    obtain ⟨y, hy⟩ := hs (e₀ z)
    refine ⟨e₁.symm y, ?_⟩
    rw [hst, BialgEquiv.apply_symm_apply, hy, BialgEquiv.symm_apply_apply]
  ·
    have hE₀ := nsmulAlgHom_eq_of_ker_eq_torsionIdeal sbar hs n hkers
    have hsymm : Surjective (e₀.symm : E₀ →ₐc[ZMod p] ZMod p ⊗[𝓞] H₀) := fun z =>
      ⟨e₀ z, e₀.symm_apply_apply z⟩
    have hbar : ∀ z : ZMod p ⊗[𝓞] H₀, nsmulAlgHom (ZMod p) (ZMod p ⊗[𝓞] H₀) n z =
        algebraMap (ZMod p) (ZMod p ⊗[𝓞] H₀) (Coalgebra.counit (R := ZMod p) z) :=
      nsmulAlgHom_eq_of_surjective (e₀.symm : E₀ →ₐc[ZMod p] ZMod p ⊗[𝓞] H₀) hsymm n hE₀
    have hH₀ := nsmulAlgHom_eq_of_baseChange p hp hker H₀ n hbar
    have hJK : torsionIdeal 𝓞 H₁ n ≤ RingHom.ker st := by
      rw [torsionIdeal, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change st (nsmulAlgHom 𝓞 H₁ n a) = 0
      rw [← nsmulAlgHom_bialgHom_apply st n a, hH₀, CoalgHomClass.counit_comp_apply,
        (mem_augIdeal_iff 𝓞 H₁ a).1 ha, map_zero]
    refine ker_eq_torsionIdeal p hp hker H₁ H₀ n st hJK fun x hx => ?_

    have hinj : Injective (e₁ : ZMod p ⊗[𝓞] H₁ →ₐc[ZMod p] E₁) := fun a b h =>
      e₁.injective h
    have hsurj : Surjective (e₁ : ZMod p ⊗[𝓞] H₁ →ₐc[ZMod p] E₁) := fun y =>
      ⟨e₁.symm y, e₁.apply_symm_apply y⟩
    have h1 : sbar (e₁ ((Algebra.TensorProduct.includeRight : H₁ →ₐ[𝓞] ZMod p ⊗[𝓞] H₁) x)) = 0 := by
      rw [← hst', Algebra.TensorProduct.includeRight_apply, hmap, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      change e₀ ((1 : ZMod p) ⊗ₜ[𝓞] st x) = 0
      rw [hx, TensorProduct.tmul_zero, map_zero]
    have h2 : (e₁ : ZMod p ⊗[𝓞] H₁ →ₐc[ZMod p] E₁)
        ((Algebra.TensorProduct.includeRight : H₁ →ₐ[𝓞] ZMod p ⊗[𝓞] H₁) x) ∈
        (torsionIdeal (ZMod p) (ZMod p ⊗[𝓞] H₁) n).map
          ((e₁ : ZMod p ⊗[𝓞] H₁ →ₐc[ZMod p] E₁) : ZMod p ⊗[𝓞] H₁ →ₐ[ZMod p] E₁) := by
      rw [map_torsionIdeal_of_surjective _ hsurj, ← hkers]
      exact h1
    obtain ⟨t, ht, hte⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 h2
    rw [← hinj hte]
    exact ht

end Transition

section Points

variable {𝓞 : Type u} [CommRing 𝓞]

private theorem bijective_comp_mkₐ (H : Type*) [CommRing H] [Algebra 𝓞 H] [Algebra.FormallyEtale 𝓞 H]
    (g : Type w) [CommRing g] [Algebra 𝓞 g] (I : Ideal g) [IsAdicComplete I g] :
    Bijective fun f : H →ₐ[𝓞] g => (Ideal.Quotient.mkₐ 𝓞 I).comp f := by
  constructor
  · intro f₁ f₂ h
    dsimp only at h
    have hI : ⨅ i : ℕ, I ^ i = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_bot]
      refine IsHausdorff.haus (inferInstance : IsHausdorff I g) x fun i => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact (Submodule.mem_iInf _).1 hx i
    exact Algebra.FormallyUnramified.ext_of_iInf (I := I) hI fun x => DFunLike.congr_fun h x
  · intro fbar
    exact Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete fbar

end Points

end EtLiftTower
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp.EtLiftTower"

open EtLiftTower in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (E : ℕ → Type v) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra (ZMod p) (E v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (E v)] [∀ v, Module.Finite (ZMod p) (E v)]
    (hred : ∀ v, IsReduced (E v))
    (s : ∀ v, E (v + 1) →ₐc[ZMod p] E v) (hs : ∀ v, Function.Surjective (s v))
    (hkers : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (E (v + 1)) (p ^ v)) :
    ∃ (Et : ℕ → Type u) (_ : ∀ v, CommRing (Et v)) (_ : ∀ v, HopfAlgebra 𝓞 (Et v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (Et v)) (_ : ∀ v, Module.Free 𝓞 (Et v)) (_ : ∀ v, Module.Finite 𝓞 (Et v))
      (_ : ∀ v, Algebra.FormallyEtale 𝓞 (Et v))
      (st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v)
      (θ : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] E v),
      (∀ v, Function.Bijective (θ v)) ∧
      (∀ v, (θ v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (st v)) =
        (s v).comp (θ (v + 1))) ∧
      (∀ v, Function.Surjective (st v)) ∧
      (∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (Et (v + 1)) (p ^ v)) ∧
      (∀ v, Module.finrank 𝓞 (Et v) = Module.finrank (ZMod p) (E v)) ∧
      (∀ (g : Type w) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g] (v : ℕ),
        Function.Bijective fun f : Et v →ₐ[𝓞] g =>
          (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : g)})).comp f) := by
  classical

  obtain ⟨hD, hDVR, -, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  haveI : ∀ v, IsReduced (E v) := hred

  let D : ∀ v, LiftData 𝓞 p (E v) := fun v => liftData hp hker (E v)

  have htr : ∀ v, ∃ st : (D (v + 1)).carrier →ₐc[𝓞] (D v).carrier,
      (∀ x, (D v).equiv (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) st x) =
        s v ((D (v + 1)).equiv x)) ∧
      Function.Surjective st ∧
      RingHom.ker st = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (D (v + 1)).carrier (p ^ v) := fun v =>
    exists_transition p hp hker (D (v + 1)).carrier (D v).carrier (D (v + 1)).equiv (D v).equiv (s v) (hs v)
      (p ^ v) (hkers v)
  choose st hst using htr
  refine ⟨fun v => (D v).carrier, fun v => (D v).instCommRing, fun v => (D v).instHopf, fun v => (D v).instCocomm,
    fun v => (D v).instFree, fun v => (D v).instFinite, fun v => (D v).instEtale, st,
    fun v => ((D v).equiv : ZMod p ⊗[𝓞] (D v).carrier →ₐc[ZMod p] E v), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun v => EquivLike.bijective (D v).equiv
  · intro v
    exact DFunLike.ext _ _ fun x => (hst v).1 x
  · exact fun v => (hst v).2.1
  · exact fun v => (hst v).2.2
  · exact fun v => (D v).finrank_eq
  · intro g _ _ _ v
    exact bijective_comp_mkₐ (D v).carrier g (Ideal.span {(p : g)})

end S_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_exists_formallyEtale_tower_bijective_baseChange_zmodp (solution)
