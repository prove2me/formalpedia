-- Prove2me | solution 1 for PDivisibleGroup.exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9bfe6900-e10f-5bfb-892c-202232b5edb4

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq
import Theorems.Thm_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_Algebra_Etale_finite_and_bijective_lift_pi_algHom_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot
import Theorems.Thm_PadicAlgCl_mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem

set_option autoImplicit false
open scoped TensorProduct

namespace DescentK

section Dict
variable {O : Type} [CommRing O] (K' : Type) [Field K'] [Algebra O K']
variable {B : Type} [CommRing B] [Algebra O B]
variable (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra K' Ω] [IsScalarTower O K' Ω]

noncomputable def dict : (B →ₐ[O] Ω) ≃ (K' ⊗[O] B →ₐ[K'] Ω) where
  toFun ν := Algebra.TensorProduct.lift (Algebra.ofId K' Ω) ν (fun _ _ => Commute.all _ _)
  invFun χ := (χ.restrictScalars O).comp Algebra.TensorProduct.includeRight
  left_inv ν := by ext b; simp
  right_inv χ := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext b; simp [Algebra.TensorProduct.includeRight_apply]

theorem dict_apply_one_tmul (ν : B →ₐ[O] Ω) (b : B) : dict K' Ω ν ((1 : K') ⊗ₜ[O] b) = ν b := by
  simp [dict, Algebra.ofId_apply]
end Dict

section Wanted
variable {O : Type} [CommRing O] (K' : Type) [Field K'] [Algebra O K']
variable {B : Type} [CommRing B] [HopfAlgebra O B]
variable (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra K' Ω] [IsScalarTower O K' Ω]

theorem toConv_dict_mul (ν₁ ν₂ : WithConv (B →ₐ[O] Ω)) :
    WithConv.toConv (dict K' Ω (WithConv.ofConv (ν₁ * ν₂))) =
      WithConv.toConv (dict K' Ω (WithConv.ofConv ν₁)) * WithConv.toConv (dict K' Ω (WithConv.ofConv ν₂)) := by
  apply WithConv.ofConv_injective
  refine Algebra.TensorProduct.ext' fun k b => ?_
  rw [WithConv.ofConv_toConv, AlgHom.convMul_apply, WithConv.ofConv_toConv, WithConv.ofConv_toConv]
  rw [show dict K' Ω (WithConv.ofConv (ν₁ * ν₂)) (k ⊗ₜ[O] b)
      = k • (WithConv.ofConv (ν₁ * ν₂)) b from by
        simp only [dict, Equiv.coe_fn_mk, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]]
  rw [AlgHom.convMul_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize Coalgebra.comul (R := O) b = z
  induction z with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero, smul_zero]
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul]
    simp only [dict, Equiv.coe_fn_mk, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def,
      map_one, one_mul]
    ring
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, smul_add, hx, hy]

theorem toConv_dict_one :
    WithConv.toConv (dict K' Ω (WithConv.ofConv (1 : WithConv (B →ₐ[O] Ω)))) = 1 := by
  apply WithConv.ofConv_injective
  refine Algebra.TensorProduct.ext' fun k b => ?_
  rw [WithConv.ofConv_toConv, AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply]
  simp only [dict, Equiv.coe_fn_mk, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  rw [AlgHom.convOne_apply, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_comm]

theorem dict_comp_antipode (ν : B →ₐ[O] Ω) :
    (dict K' Ω (ν.comp (PDivisibleGroup.Hopf.antipodeAlgHom O B))).toLinearMap =
      (dict K' Ω ν).toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K') (A := K' ⊗[O] B) := by

  have h1 : WithConv.toConv (dict K' Ω (ν.comp (PDivisibleGroup.Hopf.antipodeAlgHom O B))) *
      WithConv.toConv (dict K' Ω ν) = 1 := by
    have h := toConv_dict_mul K' Ω (WithConv.toConv (ν.comp (PDivisibleGroup.Hopf.antipodeAlgHom O B)))
      (WithConv.toConv ν)
    rw [PDivisibleGroup.Hopf.comp_antipodeAlgHom_convMul, toConv_dict_one, WithConv.ofConv_toConv,
      WithConv.ofConv_toConv] at h
    exact h.symm
  have h2 : WithConv.toConv (dict K' Ω ν) *
      WithConv.toConv ((dict K' Ω ν).comp (PDivisibleGroup.Hopf.antipodeAlgHom K' (K' ⊗[O] B))) = 1 :=
    PDivisibleGroup.Hopf.convMul_comp_antipodeAlgHom _
  have h3 := left_inv_eq_right_inv h1 h2
  rw [show dict K' Ω (ν.comp (PDivisibleGroup.Hopf.antipodeAlgHom O B)) =
      (dict K' Ω ν).comp (PDivisibleGroup.Hopf.antipodeAlgHom K' (K' ⊗[O] B)) from congrArg WithConv.ofConv h3]
  rfl

theorem dict_comp_algEquiv (ν : B →ₐ[O] Ω) (τ : Ω ≃ₐ[O] Ω) (σ : Ω ≃ₐ[K'] Ω) (hτσ : ∀ x, τ x = σ x) :
    dict K' Ω ((τ : Ω →ₐ[O] Ω).comp ν) = (σ : Ω →ₐ[K'] Ω).comp (dict K' Ω ν) := by
  refine Algebra.TensorProduct.ext' fun k b => ?_
  simp only [dict, Equiv.coe_fn_mk, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.comp_apply,
    AlgEquiv.coe_algHom, map_mul, AlgEquiv.commutes, hτσ]

theorem exists_algEquiv_restrict
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (K'' : Type) [Field K''] [Algebra (PadicAlgCl.ringOfIntegers p K) K'']
    [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K'']
    [Algebra K'' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K'' (PadicAlgCl p)]
    (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[K''] PadicAlgCl p, ∀ x, σ x = τ x := by
  have hcomm : ∀ k : K'', τ (algebraMap K'' (PadicAlgCl p) k) = algebraMap K'' (PadicAlgCl p) k := by
    intro k
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PadicAlgCl.ringOfIntegers p K) k
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_div₀,
      AlgEquiv.commutes, AlgEquiv.commutes]
  exact ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hcomm, fun x => rfl⟩

end Wanted

section Tate
variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h)
variable (L : Type) [CommRing L] [Algebra R L]

theorem coe_smul_succ (x : TateModule p (G.Points L)) (v : ℕ) :
    ((((p : ℤ_[p]) • x : TateModule p (G.Points L)) : ℕ → G.Points L) (v + 1)) = (x : ℕ → G.Points L) v := by
  rw [TateModule.natCast_padicInt_smul_apply, TateModule.compat]

theorem pointsMkAdd_comp_transition (v : ℕ) (g : G.Point L v) :
    G.pointsMkAdd L (v + 1) (Additive.ofMul
      (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom g).comp (G.transition v)) : G.Point L (v + 1))) =
      G.pointsMkAdd L v (Additive.ofMul g) := by
  exact G.pointsMkAdd_pointIncl v g

theorem tateModuleRep_apply_eq_pointsMkAdd (τ : L ≃ₐ[R] L) (x : TateModule p (G.Points L)) (v : ℕ) (g : G.Point L v)
    (hg : (x : ℕ → G.Points L) v = G.pointsMkAdd L v (Additive.ofMul g)) :
    ((G.tateModuleRep L τ x : TateModule p (G.Points L)) : ℕ → G.Points L) v =
      G.pointsMkAdd L v (Additive.ofMul
        (PDivisibleGroup.Point.ofAlgHom ((τ : L →ₐ[R] L).comp (PDivisibleGroup.Point.toAlgHom g)) : G.Point L v)) := by
  rw [PDivisibleGroup.tateModuleRep_apply, hg, PDivisibleGroup.Points.smul_pointsMkAdd]
  rfl

end Tate

end DescentK

namespace DescentK

open HopfAlgebra

section PointsOfQuot

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [Bialgebra F A]
variable {L : Type*} [Field L] [Algebra F L]

theorem exists_eq_evalAlgHom {ι : Type*} [Finite ι] (χ : (ι → L) →ₐ[L] L) :
    ∃ i : ι, χ = Pi.evalAlgHom L (fun _ => L) i := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι

  have hidem : ∀ i, χ (Pi.single i 1) = 0 ∨ χ (Pi.single i 1) = 1 := fun i => by
    have h2 : χ (Pi.single i 1) * χ (Pi.single i 1) = χ (Pi.single i 1) := by
      rw [← map_mul]; congr 1; ext j; by_cases hj : j = i <;> simp [hj, Pi.single_apply]
    rcases mul_eq_zero.mp (show χ (Pi.single i 1) * (χ (Pi.single i 1) - 1) = 0 by rw [mul_sub, h2, mul_one, sub_self]) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsum : ∑ i, χ (Pi.single i 1) = 1 := by
    have h1 : (∑ i, Pi.single i (1 : L) : ι → L) = 1 := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [← map_sum, h1, map_one]

  obtain ⟨i, hi⟩ : ∃ i, χ (Pi.single i 1) = 1 := by
    by_contra hne
    push Not at hne
    have : ∑ i, χ (Pi.single i (1 : L)) = 0 := Finset.sum_eq_zero fun i _ => (hidem i).resolve_right (hne i)
    rw [hsum] at this; exact one_ne_zero this
  refine ⟨i, AlgHom.ext fun f => ?_⟩
  rw [Pi.evalAlgHom_apply]
  have hf : f = f i • Pi.single i (1 : L) + (f - f i • Pi.single i 1) := by abel
  have hkill : χ (f - f i • Pi.single i 1) = 0 := by
    have h1 : (f - f i • Pi.single i (1 : L)) * Pi.single i 1 = 0 := by
      ext j; by_cases hj : j = i <;> simp [hj, Pi.single_apply]
    have h2 := congrArg χ h1
    rw [map_mul, hi, mul_one, map_zero] at h2
    exact h2
  conv_lhs => rw [hf]
  rw [map_add, hkill, add_zero, map_smul, hi, smul_eq_mul, mul_one]

theorem exists_eq_liftPoint (S : Submonoid (WithConv (A →ₐ[F] L))) [Finite ↥S]
    (hev : Function.Bijective (evalQuot S)) (ψ : pointQuot S →ₐ[F] L) :
    ∃ s : ↥S, ψ = liftPoint (ptSet S) (WithConv.ofConv s.1) (ofConv_mem_ptSet s) := by
  classical

  let ψL : L ⊗[F] pointQuot S →ₐ[L] L := Algebra.TensorProduct.lift (Algebra.ofId L L) ψ (fun _ _ => Commute.all _ _)
  let e : (L ⊗[F] pointQuot S) ≃ₐ[L] (↥S → L) := AlgEquiv.ofBijective (evalQuot S) hev
  obtain ⟨s, hs⟩ := exists_eq_evalAlgHom (ψL.comp (e.symm : (↥S → L) →ₐ[L] L ⊗[F] pointQuot S))
  refine ⟨s, ?_⟩
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  have h1 : ψ (Ideal.Quotient.mk _ a) = ψL ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk _ a) := by
    simp [ψL, Algebra.ofId_apply]
  have h2 : ψL ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk _ a) =
      (ψL.comp (e.symm : (↥S → L) →ₐ[L] L ⊗[F] pointQuot S)) (e ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk _ a)) := by
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, h1, h2, hs,
    Pi.evalAlgHom_apply, AlgEquiv.ofBijective_apply, evalQuot_tmul, one_mul, liftPoint_mk]

end PointsOfQuot

section Split

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
variable {A : Type*} [CommRing A] [Bialgebra K A] [Module.Finite K A]

theorem vanishingIdealOfPoints_image_ofConv (S : Submonoid (WithConv (A →ₐ[K] L))) :
    vanishingIdealOfPoints ((fun ν : WithConv (A →ₐ[K] L) => WithConv.ofConv ν) '' (S : Set (WithConv (A →ₐ[K] L)))) =
      vanishingIdealOfPoints (ptSet S) := by
  congr 1
  ext ν
  simp only [Set.mem_image, SetLike.mem_coe, mem_ptSet_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨WithConv.toConv ν, h, rfl⟩

theorem evalQuot_bijective (D : Subgroup (L ≃ₐ[K] L)) (hD : IntermediateField.fixedField D = ⊥)
    [Finite (WithConv (A →ₐ[K] L))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L)))
    (S : Submonoid (WithConv (A →ₐ[K] L)))
    (hstab : ∀ σ : L ≃ₐ[K] L, σ ∈ D → ∀ ν ∈ (S : Set (WithConv (A →ₐ[K] L))),
      ∃ ν' ∈ (S : Set (WithConv (A →ₐ[K] L))), ∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) :
    Function.Bijective (evalQuot S) := by
  classical
  have h23 := HopfAlgebra.lift_liftPoint_bijective_of_forall_exists_comp_eq D hD
    (fun ν : WithConv (A →ₐ[K] L) => WithConv.ofConv ν) (fun _ _ h => by simpa using congrArg WithConv.toConv h)
    hev (S : Set (WithConv (A →ₐ[K] L))) hstab
  have hI := vanishingIdealOfPoints_image_ofConv (K := K) (L := L) S
  let e : (A ⧸ vanishingIdealOfPoints ((fun ν : WithConv (A →ₐ[K] L) => WithConv.ofConv ν) ''
      (S : Set (WithConv (A →ₐ[K] L))))) ≃ₐ[K] pointQuot S :=
    Ideal.quotientEquivAlgOfEq K hI
  let mapE : L ⊗[K] pointQuot S →ₐ[L]
      L ⊗[K] (A ⧸ vanishingIdealOfPoints ((fun ν : WithConv (A →ₐ[K] L) => WithConv.ofConv ν) ''
        (S : Set (WithConv (A →ₐ[K] L))))) :=
    Algebra.TensorProduct.map (AlgHom.id L L) e.symm.toAlgHom
  have hmapE : Function.Bijective mapE := by
    let mapE' : _ →ₐ[L] L ⊗[K] pointQuot S := Algebra.TensorProduct.map (AlgHom.id L L) e.toAlgHom
    have h1 : ∀ x, mapE' (mapE x) = x := fun x => by
      have : mapE'.comp mapE = AlgHom.id L _ := by
        apply Algebra.TensorProduct.ext
        · ext
        · ext q; simp [mapE, mapE']
      exact congrArg (fun f => f x) (congrArg DFunLike.coe this)
    have h2 : ∀ y, mapE (mapE' y) = y := fun y => by
      have : mapE.comp mapE' = AlgHom.id L _ := by
        apply Algebra.TensorProduct.ext
        · ext
        · ext q; simp [mapE, mapE']
      exact congrArg (fun f => f y) (congrArg DFunLike.coe this)
    exact ⟨fun x y hxy => by rw [← h1 x, ← h1 y, hxy], fun y => ⟨mapE' y, h2 y⟩⟩

  have hcomp : (evalQuot S : L ⊗[K] pointQuot S →ₐ[L] (↥S → L)) =
      (Algebra.TensorProduct.lift (Algebra.ofId L (↥(S : Set (WithConv (A →ₐ[K] L))) → L))
        (Pi.algHom K _ fun s : ↥(S : Set (WithConv (A →ₐ[K] L))) =>
          liftPoint ((fun ν : WithConv (A →ₐ[K] L) => WithConv.ofConv ν) '' (S : Set (WithConv (A →ₐ[K] L))))
            (WithConv.ofConv s.1) (Set.mem_image_of_mem _ s.2))
        (fun _ _ => Commute.all _ _)).comp mapE := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro a
      funext s
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mkₐ_eq_mk,
        AlgHom.coe_restrictScalars']
      rw [evalQuot_tmul, one_mul]
      simp [mapE, e, Ideal.quotientEquivAlgOfEq_symm, Algebra.ofId_apply, liftPoint_mk]
  rw [show (evalQuot S : L ⊗[K] pointQuot S → (↥S → L)) =
    (Algebra.TensorProduct.lift (Algebra.ofId L (↥(S : Set (WithConv (A →ₐ[K] L))) → L))
        (Pi.algHom K _ fun s : ↥(S : Set (WithConv (A →ₐ[K] L))) =>
          liftPoint ((fun ν : WithConv (A →ₐ[K] L) => WithConv.ofConv ν) '' (S : Set (WithConv (A →ₐ[K] L))))
            (WithConv.ofConv s.1) (Set.mem_image_of_mem _ s.2))
        (fun _ _ => Commute.all _ _)) ∘ mapE from congrArg DFunLike.coe hcomp]
  exact h23.comp hmapE

end Split

end DescentK

namespace DescentK

open HopfAlgebra PDivisibleGroup

section Frame

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
variable {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
variable (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
variable (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
  [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
  [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]

local notation "𝒪" => PadicAlgCl.ringOfIntegers p K
local notation "ℚ̄" => PadicAlgCl p

abbrev Agen (v : ℕ) : Type := K' ⊗[𝒪] G.level v

noncomputable def dictMul (v : ℕ) : WithConv (G.level v →ₐ[𝒪] ℚ̄) ≃* WithConv (Agen p K G K' v →ₐ[K'] ℚ̄) :=
  MulEquiv.mk'
    ((WithConv.equiv (G.level v →ₐ[𝒪] ℚ̄)).trans
      ((dict K' ℚ̄).trans (WithConv.equiv (Agen p K G K' v →ₐ[K'] ℚ̄)).symm))
    (fun a b => toConv_dict_mul K' ℚ̄ a b)

theorem dictMul_apply (v : ℕ) (w : WithConv (G.level v →ₐ[𝒪] ℚ̄)) :
    dictMul p K G K' v w = WithConv.toConv (dict K' ℚ̄ (WithConv.ofConv w)) := rfl

theorem ofConv_dictMul_symm (v : ℕ) (ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) :
    WithConv.ofConv ((dictMul p K G K' v).symm ν) = (dict K' ℚ̄).symm (WithConv.ofConv ν) := by
  apply (dict K' ℚ̄).injective
  rw [Equiv.apply_symm_apply]
  have h1 := dictMul_apply p K G K' v ((dictMul p K G K' v).symm ν)
  rw [MulEquiv.apply_symm_apply] at h1
  exact (congrArg WithConv.ofConv h1).symm

noncomputable def pt (v : ℕ) (ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) : G.Point ℚ̄ v :=
  Point.ofConv ((dictMul p K G K' v).symm ν)

theorem toAlgHom_pt (v : ℕ) (ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) :
    Point.toAlgHom (pt p K G K' v ν) = (dict K' ℚ̄).symm (WithConv.ofConv ν) :=
  ofConv_dictMul_symm p K G K' v ν

theorem dict_toAlgHom_pt (v : ℕ) (ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) :
    dict K' ℚ̄ (Point.toAlgHom (pt p K G K' v ν)) = WithConv.ofConv ν := by
  rw [toAlgHom_pt, Equiv.apply_symm_apply]

theorem pt_mul (v : ℕ) (ν₁ ν₂ : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) :
    pt p K G K' v (ν₁ * ν₂) = pt p K G K' v ν₁ * pt p K G K' v ν₂ := by
  simp only [pt, map_mul, Point.ofConv_mul]

theorem pt_one (v : ℕ) : pt p K G K' v 1 = 1 := by
  simp only [pt, map_one]; rfl

theorem pt_toConv_dict (v : ℕ) (g : G.Point ℚ̄ v) :
    pt p K G K' v (WithConv.toConv (dict K' ℚ̄ (Point.toAlgHom g))) = g := by
  apply Point.ext
  intro a
  rw [toAlgHom_pt, WithConv.ofConv_toConv, Equiv.symm_apply_apply]

def mPts (v : ℕ) : Submonoid (WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) where
  carrier := {ν | ∃ x ∈ M, G.pointsMkAdd ℚ̄ v (Additive.ofMul (pt p K G K' v ν)) = (x : ℕ → G.Points ℚ̄) v}
  mul_mem' := by
    rintro ν₁ ν₂ ⟨x₁, hx₁, h₁⟩ ⟨x₂, hx₂, h₂⟩
    refine ⟨x₁ + x₂, M.add_mem hx₁ hx₂, ?_⟩
    rw [pt_mul, ofMul_mul, map_add, h₁, h₂]
    rfl
  one_mem' := ⟨0, M.zero_mem, by rw [pt_one, ofMul_one, map_zero]; rfl⟩

theorem mem_mPts_iff (v : ℕ) (ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) :
    ν ∈ mPts p K G M K' v ↔
      ∃ x ∈ M, G.pointsMkAdd ℚ̄ v (Additive.ofMul (pt p K G K' v ν)) = (x : ℕ → G.Points ℚ̄) v :=
  Iff.rfl

def galD : Subgroup (ℚ̄ ≃ₐ[K'] ℚ̄) where
  carrier := {σ | ∃ τ : ℚ̄ ≃ₐ[𝒪] ℚ̄, ∀ x, σ x = τ x}
  mul_mem' := by
    rintro σ₁ σ₂ ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩
    exact ⟨τ₂.trans τ₁, fun x => by rw [AlgEquiv.mul_apply, h₁, h₂]; rfl⟩
  one_mem' := ⟨AlgEquiv.refl, fun x => rfl⟩
  inv_mem' := by
    rintro σ ⟨τ, hτ⟩
    refine ⟨τ.symm, fun x => ?_⟩
    have h1 : σ (τ.symm x) = x := by rw [hτ, AlgEquiv.apply_symm_apply]
    calc σ⁻¹ x = σ⁻¹ (σ (τ.symm x)) := by rw [h1]
      _ = τ.symm x := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

end Frame
end DescentK

namespace DescentK

open HopfAlgebra PDivisibleGroup

section Main

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
variable {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
variable (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
variable (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
  [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
  [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]

local notation "𝒪" => PadicAlgCl.ringOfIntegers p K
local notation "ℚ̄" => PadicAlgCl p

theorem fixedField_galD : IntermediateField.fixedField (galD p K K') = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [IntermediateField.mem_bot]
  apply PadicAlgCl.mem_range_algebraMap_of_forall_algEquiv_ringOfIntegers_apply_eq p K K' x
  intro τ
  obtain ⟨σ, hσ⟩ := exists_algEquiv_restrict p K K' τ
  rw [← hσ]
  exact (IntermediateField.mem_fixedField_iff _ _).mp hx σ ⟨τ, hσ⟩

theorem finite_and_hev (v : ℕ) :
    Finite (WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) ∧
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId ℚ̄ (WithConv (Agen p K G K' v →ₐ[K'] ℚ̄) → ℚ̄))
        (Pi.algHom K' _ fun ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄) => (WithConv.ofConv ν : Agen p K G K' v →ₐ[K'] ℚ̄))
        (fun _ _ => Commute.all _ _) : ℚ̄ ⊗[K'] Agen p K G K' v →ₐ[ℚ̄] (WithConv (Agen p K G K' v →ₐ[K'] ℚ̄) → ℚ̄)) := by
  haveI : CharZero K' :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (PadicAlgCl.ringOfIntegers p K) K')
  haveI : Algebra.Etale K' (Agen p K G K' v) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero K' (Agen p K G K' v)
  exact Algebra.Etale.finite_and_bijective_lift_pi_algHom_of_isAlgClosed K' (Agen p K G K' v) ℚ̄

theorem mPts_stab
    (hMstab : ∀ (τ : ℚ̄ ≃ₐ[𝒪] ℚ̄) (x : TateModule p (G.Points ℚ̄)), x ∈ M → G.tateModuleRep ℚ̄ τ x ∈ M)
    (v : ℕ) (σ : ℚ̄ ≃ₐ[K'] ℚ̄) (hσ : σ ∈ galD p K K')
    (ν : WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)) (hν : ν ∈ (mPts p K G M K' v : Set (WithConv (Agen p K G K' v →ₐ[K'] ℚ̄)))) :
    ∃ ν' ∈ (mPts p K G M K' v : Set (WithConv (Agen p K G K' v →ₐ[K'] ℚ̄))),
      ∀ a, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a) := by
  obtain ⟨τ, hτ⟩ := hσ
  obtain ⟨x, hxM, hx⟩ := hν
  refine ⟨WithConv.toConv ((σ : ℚ̄ →ₐ[K'] ℚ̄).comp (WithConv.ofConv ν)), ?_, fun a => rfl⟩
  refine ⟨G.tateModuleRep ℚ̄ τ x, hMstab τ x hxM, ?_⟩
  rw [tateModuleRep_apply_eq_pointsMkAdd p G ℚ̄ τ x v (pt p K G K' v ν) hx.symm]
  congr 2

  apply Point.ext
  intro a
  rw [toAlgHom_pt, Point.toAlgHom_ofAlgHom, WithConv.ofConv_toConv]
  have key : dict K' ℚ̄ (((τ : ℚ̄ →ₐ[𝒪] ℚ̄)).comp (Point.toAlgHom (pt p K G K' v ν))) =
      (σ : ℚ̄ →ₐ[K'] ℚ̄).comp (WithConv.ofConv ν) := by
    rw [dict_comp_algEquiv K' ℚ̄ _ τ σ (fun y => (hτ y).symm), dict_toAlgHom_pt]
  rw [← key, Equiv.symm_apply_apply]

theorem evalQuot_mPts_bijective
    (hMstab : ∀ (τ : ℚ̄ ≃ₐ[𝒪] ℚ̄) (x : TateModule p (G.Points ℚ̄)), x ∈ M → G.tateModuleRep ℚ̄ τ x ∈ M)
    (v : ℕ) : Function.Bijective (evalQuot (mPts p K G M K' v)) := by
  haveI := (finite_and_hev p K G K' v).1
  exact evalQuot_bijective (galD p K K') (fixedField_galD p K K') (finite_and_hev p K G K' v).2
    (mPts p K G M K' v) (fun σ hσ ν hν => mPts_stab p K G M K' hMstab v σ hσ ν hν)

scoped instance finite_mPts (v : ℕ) : Finite ↥(mPts p K G M K' v) := by
  haveI := (finite_and_hev p K G K' v).1
  infer_instance

theorem mPts_inv (v : ℕ) (ν : Agen p K G K' v →ₐ[K'] ℚ̄) (hν : ν ∈ ptSet (mPts p K G M K' v)) :
    ∃ ν' ∈ ptSet (mPts p K G M K' v), ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K') := by
  obtain ⟨x, hxM, hx⟩ := hν
  refine ⟨dict K' ℚ̄ ((Point.toAlgHom (pt p K G K' v (WithConv.toConv ν))).comp
      (PDivisibleGroup.Hopf.antipodeAlgHom 𝒪 (G.level v))), ?_, ?_⟩
  · show WithConv.toConv _ ∈ mPts p K G M K' v
    refine ⟨-x, M.neg_mem hxM, ?_⟩
    have hinv : pt p K G K' v (WithConv.toConv (dict K' ℚ̄ ((Point.toAlgHom (pt p K G K' v (WithConv.toConv ν))).comp
        (PDivisibleGroup.Hopf.antipodeAlgHom 𝒪 (G.level v))))) = (pt p K G K' v (WithConv.toConv ν))⁻¹ := by
      rw [Point.inv_eq, ← pt_toConv_dict p K G K' v (Point.ofAlgHom _), Point.toAlgHom_ofAlgHom]
    rw [hinv, ofMul_inv, map_neg, hx]
    rfl
  · rw [dict_comp_antipode K' ℚ̄, dict_toAlgHom_pt, WithConv.ofConv_toConv]

theorem isHopfIdeal_mPts
    (hMstab : ∀ (τ : ℚ̄ ≃ₐ[𝒪] ℚ̄) (x : TateModule p (G.Points ℚ̄)), x ∈ M → G.tateModuleRep ℚ̄ τ x ∈ M)
    (v : ℕ) :
    (vanishingIdealOfPoints (ptSet (mPts p K G M K' v))).IsHopfIdeal' K' := by
  have hsep := fun x hx => HopfAlgebra.tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot
    (mPts p K G M K' v) (evalQuot_mPts_bijective p K G M K' hMstab v) x hx
  obtain ⟨h1, h2, h3⟩ :=
    HopfAlgebra.map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
      (F := K') (L := ℚ̄) (mPts p K G M K' v) hsep (mPts_inv p K G M K' v)
  exact ⟨h1, h2, h3⟩

theorem transition_mem_vanishingIdeal (v : ℕ) (a : G.level (v + 1))
    (ha : ((1 : K') ⊗ₜ[𝒪] a : Agen p K G K' (v + 1)) ∈ vanishingIdealOfPoints (ptSet (mPts p K G M K' (v + 1)))) :
    ((1 : K') ⊗ₜ[𝒪] G.transition v a : Agen p K G K' v) ∈ vanishingIdealOfPoints (ptSet (mPts p K G M K' v)) := by
  classical
  rw [mem_vanishingIdealOfPoints_iff] at ha ⊢
  intro μ hμ
  rw [mem_ptSet_iff, mem_mPts_iff] at hμ
  obtain ⟨x, hxM, hx⟩ := hμ

  set gv : G.Point (PadicAlgCl p) v := pt p K G K' v (WithConv.toConv μ) with hgv
  set g' : G.Point (PadicAlgCl p) (v + 1) :=
    PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom gv).comp (G.transition v)) with hg'
  set ν : Agen p K G K' (v + 1) →ₐ[K'] (PadicAlgCl p) := dict K' (PadicAlgCl p) (PDivisibleGroup.Point.toAlgHom g') with hν
  have hνmem : ν ∈ ptSet (mPts p K G M K' (v + 1)) := by
    rw [mem_ptSet_iff, mem_mPts_iff]
    refine ⟨(p : ℤ_[p]) • x, M.smul_mem _ hxM, ?_⟩
    rw [hν, pt_toConv_dict, hg', pointsMkAdd_comp_transition, coe_smul_succ]
    exact hx
  have h0 := ha ν hνmem
  rw [hν, dict_apply_one_tmul] at h0
  have h1 : PDivisibleGroup.Point.toAlgHom gv (G.transition v a) = 0 := by
    have h0' : ((PDivisibleGroup.Point.toAlgHom gv).comp (G.transition v)) a = 0 := by
      rw [hg'] at h0
      exact h0
    exact h0'
  have h2 : μ ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] G.transition v a) =
      PDivisibleGroup.Point.toAlgHom gv (G.transition v a) := by
    rw [hgv, toAlgHom_pt, WithConv.ofConv_toConv]
    conv_lhs => rw [← (dict K' (PadicAlgCl p)).apply_symm_apply μ]
    rw [dict_apply_one_tmul]
  rw [h2, h1]

theorem points_iff
    (hMstab : ∀ (τ : ℚ̄ ≃ₐ[𝒪] ℚ̄) (x : TateModule p (G.Points ℚ̄)), x ∈ M → G.tateModuleRep ℚ̄ τ x ∈ M)
    (v : ℕ) (g : G.Point ℚ̄ v) :
    letI := isHopfIdeal_mPts p K G M K' hMstab v
    (∃ g'' : pointQuot (mPts p K G M K' v) →ₐ[K'] ℚ̄, ∀ a : G.level v,
        g'' (HopfAlgebra.quotientBialgHom K' (vanishingIdealOfPoints (ptSet (mPts p K G M K' v)))
          ((1 : K') ⊗ₜ[𝒪] a)) = Point.toAlgHom g a) ↔
      ∃ x ∈ M, G.pointsMkAdd ℚ̄ v (Additive.ofMul g) = (x : ℕ → G.Points ℚ̄) v := by
  letI := isHopfIdeal_mPts p K G M K' hMstab v
  constructor
  · rintro ⟨g'', hg''⟩
    obtain ⟨s, hs⟩ := exists_eq_liftPoint (mPts p K G M K' v) (evalQuot_mPts_bijective p K G M K' hMstab v) g''
    obtain ⟨x, hxM, hx⟩ := s.2
    refine ⟨x, hxM, ?_⟩
    rw [← hx]
    congr 2

    apply Point.ext
    intro a
    rw [toAlgHom_pt, ← dict_apply_one_tmul K' ℚ̄ ((dict K' ℚ̄).symm (WithConv.ofConv s.1)) a, Equiv.apply_symm_apply,
      ← hg'' a, hs, HopfAlgebra.quotientBialgHom_apply, liftPoint_mk]
  · rintro ⟨x, hxM, hx⟩
    have hmem : dict K' ℚ̄ (Point.toAlgHom g) ∈ ptSet (mPts p K G M K' v) := by
      show WithConv.toConv _ ∈ mPts p K G M K' v
      exact ⟨x, hxM, by rw [pt_toConv_dict]; exact hx⟩
    refine ⟨liftPoint (ptSet (mPts p K G M K' v)) _ hmem, fun a => ?_⟩
    rw [HopfAlgebra.quotientBialgHom_apply, liftPoint_mk, dict_apply_one_tmul]

end Main

end DescentK
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem.DescentK"

open DescentK HopfAlgebra PDivisibleGroup in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K'] [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)] :
    ∃ (C : ℕ → Type) (_ : ∀ v, CommRing (C v)) (_ : ∀ v, HopfAlgebra K' (C v))
      (πK : ∀ v, K' ⊗[PadicAlgCl.ringOfIntegers p K] G.level v →ₐc[K'] C v),
      (∀ v, Function.Surjective (πK v)) ∧
      (∀ (v : ℕ) (a : G.level (v + 1)),
        πK (v + 1) ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] a) = 0 →
          πK v ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] G.transition v a) = 0) ∧
      (∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g'' : C v →ₐ[K'] PadicAlgCl p, ∀ a : G.level v,
            g'' (πK v ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] a)) = PDivisibleGroup.Point.toAlgHom g a) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) := by
  classical
  haveI hI : ∀ v, (vanishingIdealOfPoints (ptSet (mPts p K G M K' v))).IsHopfIdeal' K' :=
    fun v => isHopfIdeal_mPts p K G M K' hMstab v
  refine ⟨fun v => pointQuot (mPts p K G M K' v), fun v => inferInstance, fun v => inferInstance,
    fun v => HopfAlgebra.quotientBialgHom K' _, fun v => HopfAlgebra.quotientBialgHom_surjective K' _, ?_, ?_⟩
  · intro v a ha
    rw [HopfAlgebra.quotientBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem] at ha ⊢
    exact transition_mem_vanishingIdeal p K G M K' v a ha
  · intro v g
    exact points_iff p K G M K' hMstab v g

end S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
end P2MW
export P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem (solution)
