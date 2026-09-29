-- Prove2me | solution 1 for PDivisibleGroup.exists_surjective_injective_ker_eq_map_of_comp_eq_self_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ca40fd64-cc52-5e0d-8086-fe30bf5b825d

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_surjective_injective_ker_eq_map_of_comp_eq_self_of_field
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct

noncomputable def Glue.includeLeftBialgHom (F A B : Type) [Field F] [CommRing A] [CommRing B]
    [Bialgebra F A] [Bialgebra F B] : A →ₐc[F] A ⊗[F] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeLeft : A →ₐ[F] A ⊗[F] B)
    (by
      ext a
      simp [Algebra.TensorProduct.includeLeft_apply, TensorProduct.counit_tmul])
    (by
      ext a
      have key : ∀ z : A ⊗[F] A,
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[F] A ⊗[F] B)
            (Algebra.TensorProduct.includeLeft : A →ₐ[F] A ⊗[F] B) z =
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm F F F F A A B B (z ⊗ₜ[F] ((1 : B) ⊗ₜ[F] (1 : B))) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rw [TensorProduct.zero_tmul, map_zero, LinearEquiv.map_zero]
        | tmul x y => rfl
        | add z w hz hw => rw [map_add, TensorProduct.add_tmul, LinearEquiv.map_add, hz, hw]
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply]
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
      exact key _)

noncomputable def Glue.includeRightBialgHom (F A B : Type) [Field F] [CommRing A] [CommRing B]
    [Bialgebra F A] [Bialgebra F B] : B →ₐc[F] A ⊗[F] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeRight : B →ₐ[F] A ⊗[F] B)
    (by
      ext b
      simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul])
    (by
      ext b
      have key : ∀ z : B ⊗[F] B,
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight : B →ₐ[F] A ⊗[F] B)
            (Algebra.TensorProduct.includeRight : B →ₐ[F] A ⊗[F] B) z =
          TensorProduct.AlgebraTensorModule.tensorTensorTensorComm F F F F A A B B (((1 : A) ⊗ₜ[F] (1 : A)) ⊗ₜ[F] z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rw [TensorProduct.tmul_zero, map_zero, LinearEquiv.map_zero]
        | tmul x y => rfl
        | add z w hz hw => rw [map_add, TensorProduct.tmul_add, LinearEquiv.map_add, hz, hw]
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeRight_apply]
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
      exact key _)

@[scoped simp] theorem Glue.includeLeftBialgHom_apply (F A B : Type) [Field F] [CommRing A] [CommRing B]
    [Bialgebra F A] [Bialgebra F B] (a : A) : Glue.includeLeftBialgHom F A B a = a ⊗ₜ 1 := rfl
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_surjective_injective_ker_eq_map_of_comp_eq_self_of_field.Glue"
@[scoped simp] theorem Glue.includeRightBialgHom_apply (F A B : Type) [Field F] [CommRing A] [CommRing B]
    [Bialgebra F A] [Bialgebra F B] (b : B) : Glue.includeRightBialgHom F A B b = 1 ⊗ₜ b := rfl

p2m_reactivate "P2MW.S_PDivisibleGroup_exists_surjective_injective_ker_eq_map_of_comp_eq_self_of_field.Glue"
theorem solution
    {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
    {h : ℕ} (H : PDivisibleGroup F p h)
    (ε ε' : ∀ v : ℕ, H.level v →ₐc[F] H.level v)
    (hε : ∀ v, (ε v).comp (ε v) = ε v) (hε' : ∀ v, (ε' v).comp (ε' v) = ε' v)
    (hεε' : ∀ v, (ε v : H.level v →ₐ[F] H.level v).comp (ε' v : H.level v →ₐ[F] H.level v) =
      (Algebra.ofId F (H.level v)).comp (Bialgebra.counitAlgHom F (H.level v)))
    (hε'ε : ∀ v, (ε' v : H.level v →ₐ[F] H.level v).comp (ε v : H.level v →ₐ[F] H.level v) =
      (Algebra.ofId F (H.level v)).comp (Bialgebra.counitAlgHom F (H.level v)))
    (hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[F] H.level v) *
        WithConv.toConv (ε' v : H.level v →ₐ[F] H.level v) =
      WithConv.toConv (AlgHom.id F (H.level v)))
    (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hε't : ∀ v, (H.transition v).comp (ε' (v + 1)) = (ε' v).comp (H.transition v))
    :
    ∃ (h₁ h₂ : ℕ), h₁ + h₂ = h ∧
    ∃ (H₁ : PDivisibleGroup F p h₁) (H₂ : PDivisibleGroup F p h₂)
      (π₁ : ∀ v, H.level v →ₐc[F] H₁.level v) (j₂ : ∀ v, H₂.level v →ₐc[F] H.level v),
      (∀ v, Function.Surjective (π₁ v)) ∧
      (∀ v, (π₁ v).comp (H.transition v) = (H₁.transition v).comp (π₁ (v + 1))) ∧
      (∀ v, Function.Injective (j₂ v)) ∧
      (∀ v, (H.transition v).comp (j₂ (v + 1)) = (j₂ v).comp (H₂.transition v)) ∧
      (∀ v, RingHom.ker (π₁ v : H.level v →ₐ[F] H₁.level v) =
        Ideal.map (j₂ v : H₂.level v →ₐ[F] H.level v) (RingHom.ker (Bialgebra.counitAlgHom F (H₂.level v)))) ∧

      (∀ (v : ℕ) (b : H.level v), ε' v b = b ↔ ∃ a, j₂ v a = b) ∧
      (∃ σ₁ : ∀ v, H₁.level v →ₐ[F] H.level v,
        (∀ v, (π₁ v : H.level v →ₐ[F] H₁.level v).comp (σ₁ v) = AlgHom.id F (H₁.level v)) ∧
        (∀ v, (σ₁ v).comp (π₁ v : H.level v →ₐ[F] H₁.level v) = (ε v : H.level v →ₐ[F] H.level v))) := by
  classical
  obtain ⟨h₁, h₂, hsum12, H₁, H₂, π₁, π₂, σ₁, σ₂, Θ, hπ₁s, hπ₂s, hπ₁t, hπ₂t, hπσ₁, hσπ₁, hπσ₂, hσπ₂, hΘbij, hΘdef⟩ :=
    PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field p H ε ε' hε hε' hεε' hε'ε hsum hεt hε't
  let Θe : ∀ v : ℕ, H.level v ≃ₐc[F] (H₁.level v ⊗[F] H₂.level v) := fun v => BialgEquiv.ofBijective (Θ v) (hΘbij v)
  have hΘe : ∀ (v : ℕ) (b : H.level v), Θe v b = Θ v b := fun v b => rfl
  let j₂ : ∀ v : ℕ, H₂.level v →ₐc[F] H.level v := fun v =>
    ((Θe v).symm : (H₁.level v ⊗[F] H₂.level v) →ₐc[F] H.level v).comp (Glue.includeRightBialgHom F (H₁.level v) (H₂.level v))
  have hj₂ : ∀ (v : ℕ) (a : H₂.level v), j₂ v a = (Θe v).symm ((1 : H₁.level v) ⊗ₜ[F] a) := fun v a => rfl
  have hΘj₂ : ∀ (v : ℕ) (a : H₂.level v), Θ v (j₂ v a) = (1 : H₁.level v) ⊗ₜ[F] a := fun v a => by
    rw [hj₂, ← hΘe, (Θe v).apply_symm_apply]

  have hσπ₁' : ∀ (v : ℕ) (b : H.level v), σ₁ v (π₁ v b) = ε v b := fun v b => DFunLike.congr_fun (hσπ₁ v) b
  have hπσ₁' : ∀ (v : ℕ) (y : H₁.level v), π₁ v (σ₁ v y) = y := fun v y => DFunLike.congr_fun (hπσ₁ v) y
  have hσπ₂' : ∀ (v : ℕ) (b : H.level v), σ₂ v (π₂ v b) = ε' v b := fun v b => DFunLike.congr_fun (hσπ₂ v) b
  have hπσ₂' : ∀ (v : ℕ) (y : H₂.level v), π₂ v (σ₂ v y) = y := fun v y => DFunLike.congr_fun (hπσ₂ v) y
  have hπ₁ε : ∀ (v : ℕ) (b : H.level v), π₁ v (ε v b) = π₁ v b := fun v b => by rw [← hσπ₁', hπσ₁']
  have hπ₂ε' : ∀ (v : ℕ) (b : H.level v), π₂ v (ε' v b) = π₂ v b := fun v b => by rw [← hσπ₂', hπσ₂']
  have hεε'' : ∀ (v : ℕ) (b : H.level v), ε v (ε' v b) = algebraMap F (H.level v) (Coalgebra.counit (R := F) b) :=
    fun v b => DFunLike.congr_fun (hεε' v) b
  have hε'ε'' : ∀ (v : ℕ) (b : H.level v), ε' v (ε' v b) = ε' v b := fun v b => DFunLike.congr_fun (hε' v) b
  have hπ₁ε' : ∀ (v : ℕ) (b : H.level v), π₁ v (ε' v b) = algebraMap F (H₁.level v) (Coalgebra.counit (R := F) b) := fun v b => by
    rw [← hπ₁ε, hεε'']
    exact AlgHomClass.commutes (π₁ v) _

  have hΘfix : ∀ (v : ℕ) (b : H.level v), ε' v b = b → Θ v b = (1 : H₁.level v) ⊗ₜ[F] π₂ v b := by
    intro v b hb
    have hΦ : (Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[F] H₁.level v) (π₂ v : H.level v →ₐ[F] H₂.level v)).toLinearMap ∘ₗ
        TensorProduct.map (ε' v : H.level v →ₐc[F] H.level v).toLinearMap (ε' v : H.level v →ₐc[F] H.level v).toLinearMap =
        TensorProduct.map (Algebra.linearMap F (H₁.level v)) (π₂ v : H.level v →ₐc[F] H₂.level v).toLinearMap ∘ₗ
          (Coalgebra.counit (R := F) (A := H.level v)).rTensor (H.level v) := by
      apply TensorProduct.ext'
      intro x y
      show π₁ v (ε' v x) ⊗ₜ[F] π₂ v (ε' v y) = Algebra.linearMap F (H₁.level v) (Coalgebra.counit (R := F) x) ⊗ₜ[F] π₂ v y
      rw [hπ₁ε', hπ₂ε', Algebra.linearMap_apply]
    have hcomul : Coalgebra.comul (R := F) (ε' v b) =
        TensorProduct.map (ε' v : H.level v →ₐc[F] H.level v).toLinearMap (ε' v : H.level v →ₐc[F] H.level v).toLinearMap (Coalgebra.comul (R := F) b) :=
      (CoalgHomClass.map_comp_comul_apply (ε' v) b).symm
    rw [hΘdef, ← hb, hcomul, hb]
    have := LinearMap.congr_fun hΦ (Coalgebra.comul (R := F) b)
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [this, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul, Algebra.linearMap_apply, map_one]
    rfl

  have cim : ∀ (v : ℕ) (b : H.level v), ε' v b = b ↔ ∃ a, j₂ v a = b := by
    intro v b
    constructor
    · intro hb
      refine ⟨π₂ v b, ?_⟩
      rw [hj₂, ← hΘfix v b hb, ← hΘe, (Θe v).symm_apply_apply]
    · rintro ⟨a, rfl⟩
      obtain ⟨c, rfl⟩ := hπ₂s v a
      have hfix : j₂ v (π₂ v (ε' v c)) = ε' v c := by
        rw [hj₂, ← hΘfix v _ (hε'ε'' v c), ← hΘe, (Θe v).symm_apply_apply]
      rw [hπ₂ε'] at hfix
      rw [hfix, hε'ε'']

  have hincR : ∀ v : ℕ, Function.Injective (Glue.includeRightBialgHom F (H₁.level v) (H₂.level v)) := fun v => by
    refine Function.LeftInverse.injective
      (g := fun z => TensorProduct.lid F (H₂.level v) (LinearMap.rTensor (H₂.level v) (Coalgebra.counit (R := F) (A := H₁.level v)) z)) ?_
    intro a
    show TensorProduct.lid F (H₂.level v) (LinearMap.rTensor (H₂.level v) Coalgebra.counit ((1 : H₁.level v) ⊗ₜ[F] a)) = a
    rw [LinearMap.rTensor_tmul, Bialgebra.counit_one, TensorProduct.lid_tmul, one_smul]
  have cinj : ∀ v : ℕ, Function.Injective (j₂ v) := fun v => (EquivLike.injective (Θe v).symm).comp (hincR v)

  have hΘt : ∀ (v : ℕ) (b : H.level (v + 1)),
      Θ v (H.transition v b) = Algebra.TensorProduct.map (H₁.transition v : H₁.level (v + 1) →ₐ[F] H₁.level v) (H₂.transition v : H₂.level (v + 1) →ₐ[F] H₂.level v) (Θ (v + 1) b) := by
    intro v b
    have hsq : (Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[F] H₁.level v) (π₂ v : H.level v →ₐ[F] H₂.level v)).toLinearMap ∘ₗ
        TensorProduct.map (H.transition v).toLinearMap (H.transition v).toLinearMap =
        (Algebra.TensorProduct.map (H₁.transition v : H₁.level (v + 1) →ₐ[F] H₁.level v) (H₂.transition v : H₂.level (v + 1) →ₐ[F] H₂.level v)).toLinearMap ∘ₗ
          (Algebra.TensorProduct.map (π₁ (v + 1) : H.level (v + 1) →ₐ[F] H₁.level (v + 1)) (π₂ (v + 1) : H.level (v + 1) →ₐ[F] H₂.level (v + 1))).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      show π₁ v (H.transition v x) ⊗ₜ[F] π₂ v (H.transition v y) = H₁.transition v (π₁ (v + 1) x) ⊗ₜ[F] H₂.transition v (π₂ (v + 1) y)
      rw [show π₁ v (H.transition v x) = H₁.transition v (π₁ (v + 1) x) from DFunLike.congr_fun (hπ₁t v) x,
        show π₂ v (H.transition v y) = H₂.transition v (π₂ (v + 1) y) from DFunLike.congr_fun (hπ₂t v) y]
    have hcomul : Coalgebra.comul (R := F) (H.transition v b) =
        TensorProduct.map (H.transition v).toLinearMap (H.transition v).toLinearMap (Coalgebra.comul (R := F) b) :=
      (CoalgHomClass.map_comp_comul_apply (H.transition v) b).symm
    rw [hΘdef, hΘdef, hcomul]
    have := LinearMap.congr_fun hsq (Coalgebra.comul (R := F) b)
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply] at this
    exact this
  have ctrans : ∀ v : ℕ, (H.transition v).comp (j₂ (v + 1)) = (j₂ v).comp (H₂.transition v) := by
    intro v
    apply BialgHom.ext
    intro a
    show H.transition v (j₂ (v + 1) a) = j₂ v (H₂.transition v a)
    apply (hΘbij v).1
    rw [hΘt, hΘj₂, hΘj₂, Algebra.TensorProduct.map_tmul, map_one]
    rfl

  have hPΘ : ∀ (v : ℕ) (b : H.level v),
      TensorProduct.rid F (H₁.level v) (LinearMap.lTensor (H₁.level v) (Coalgebra.counit (R := F) (A := H₂.level v)) (Θ v b)) = π₁ v b := by
    intro v b
    have hP : (TensorProduct.rid F (H₁.level v)).toLinearMap ∘ₗ LinearMap.lTensor (H₁.level v) (Coalgebra.counit (R := F) (A := H₂.level v)) ∘ₗ
        (Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[F] H₁.level v) (π₂ v : H.level v →ₐ[F] H₂.level v)).toLinearMap =
        (π₁ v : H.level v →ₐc[F] H₁.level v).toLinearMap ∘ₗ (TensorProduct.rid F (H.level v)).toLinearMap ∘ₗ
          LinearMap.lTensor (H.level v) (Coalgebra.counit (R := F) (A := H.level v)) := by
      apply TensorProduct.ext'
      intro x y
      show TensorProduct.rid F (H₁.level v) (LinearMap.lTensor (H₁.level v) Coalgebra.counit (π₁ v x ⊗ₜ[F] π₂ v y)) =
        π₁ v (TensorProduct.rid F (H.level v) (LinearMap.lTensor (H.level v) Coalgebra.counit (x ⊗ₜ[F] y)))
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, TensorProduct.rid_tmul,
        CoalgHomClass.counit_comp_apply, map_smul]
    have := LinearMap.congr_fun hP (Coalgebra.comul (R := F) b)
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] at this
    rw [hΘdef, this, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]
    rfl
  have cker : ∀ v : ℕ, RingHom.ker (π₁ v : H.level v →ₐ[F] H₁.level v) =
      Ideal.map (j₂ v : H₂.level v →ₐ[F] H.level v) (RingHom.ker (Bialgebra.counitAlgHom F (H₂.level v))) := by
    intro v
    apply le_antisymm
    · intro b hb
      rw [RingHom.mem_ker] at hb
      have hb' : π₁ v b = 0 := hb

      have hz : LinearMap.lTensor (H₁.level v) (Coalgebra.counit (R := F) (A := H₂.level v)) (Θ v b) = 0 := by
        apply (TensorProduct.rid F (H₁.level v)).injective
        rw [hPΘ, hb', map_zero]
      have hexact := lTensor_exact (H₁.level v) (LinearMap.exact_subtype_ker_map (Coalgebra.counit (R := F) (A := H₂.level v)))
        (fun r => ⟨algebraMap F (H₂.level v) r, Bialgebra.counit_algebraMap r⟩)
      obtain ⟨w, hw⟩ := (hexact (Θ v b)).mp hz
      have key : ∀ w : H₁.level v ⊗[F] ↥(LinearMap.ker (Coalgebra.counit (R := F) (A := H₂.level v))),
          (Θe v).symm (LinearMap.lTensor (H₁.level v) (LinearMap.ker (Coalgebra.counit (R := F) (A := H₂.level v))).subtype w) ∈
            Ideal.map (j₂ v : H₂.level v →ₐ[F] H.level v) (RingHom.ker (Bialgebra.counitAlgHom F (H₂.level v))) := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]; exact Ideal.zero_mem _
        | tmul x y =>
          rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
          have hsplit : (Θe v).symm (x ⊗ₜ[F] (y : H₂.level v)) = (Θe v).symm (x ⊗ₜ[F] (1 : H₂.level v)) * j₂ v y := by
            rw [hj₂, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [hsplit]
          apply Ideal.mul_mem_left
          apply Ideal.mem_map_of_mem
          rw [RingHom.mem_ker]
          exact y.2
        | add w₁ w₂ h₁' h₂' => rw [map_add, map_add]; exact Ideal.add_mem _ h₁' h₂'
      have hbw : b = (Θe v).symm (LinearMap.lTensor (H₁.level v) (LinearMap.ker (Coalgebra.counit (R := F) (A := H₂.level v))).subtype w) := by
        rw [hw, ← hΘe, (Θe v).symm_apply_apply]
      rw [hbw]
      exact key w
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [RingHom.mem_ker] at hy
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show π₁ v (j₂ v y) = 0
      rw [← hPΘ, hΘj₂, LinearMap.lTensor_tmul]
      have hy' : Coalgebra.counit (R := F) y = 0 := hy
      rw [hy', TensorProduct.tmul_zero, map_zero]
  exact ⟨h₁, h₂, hsum12, H₁, H₂, π₁, j₂, hπ₁s, hπ₁t, cinj, ctrans, cker, cim, σ₁, hπσ₁, hσπ₁⟩

end S_PDivisibleGroup_exists_surjective_injective_ker_eq_map_of_comp_eq_self_of_field
end P2MW
export P2MW.S_PDivisibleGroup_exists_surjective_injective_ker_eq_map_of_comp_eq_self_of_field (solution)
