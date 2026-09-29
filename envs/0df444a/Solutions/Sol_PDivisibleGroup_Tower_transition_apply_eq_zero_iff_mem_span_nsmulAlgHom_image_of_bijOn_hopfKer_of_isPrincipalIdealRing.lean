-- Prove2me | solution 1 for PDivisibleGroup.Tower.transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/af170816-d778-56e8-8b6d-6c38651ffbfa

import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_ker_eq_map_hopfKer_inf_ker_counit_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra

namespace G3

section General

variable {R : Type} [CommRing R]

theorem apply_eq_algebraMap_counit_of_mem_hopfKer {A : Type} [CommRing A] [Bialgebra R A]
    {C : Type} [CommRing C] [Bialgebra R C] (π : A →ₐc[R] C) {a : A} (ha : a ∈ HopfAlgebra.hopfKer π) :
    π a = algebraMap R C (counit (R := R) a) := by
  have h : Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] C) (comul (R := R) a) = a ⊗ₜ[R] (1 : C) := ha

  have h2 := congrArg (TensorProduct.map (counit (R := R) (A := A)) (LinearMap.id : C →ₗ[R] C)) h
  have lhs : TensorProduct.map (counit (R := R) (A := A)) (LinearMap.id : C →ₗ[R] C)
      (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] C) (comul (R := R) a)) =
      (1 : R) ⊗ₜ[R] π a := by
    have hcomp : (TensorProduct.map (counit (R := R) (A := A)) (LinearMap.id : C →ₗ[R] C)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] C)).toLinearMap =
        (TensorProduct.map (LinearMap.id : R →ₗ[R] R) (π : A →ₐ[R] C).toLinearMap).comp
          (TensorProduct.map (counit (R := R) (A := A)) (LinearMap.id : A →ₗ[R] A)) := by
      ext x y
      simp
    have := LinearMap.congr_fun hcomp (comul (R := R) a)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [this]
    have hr : TensorProduct.map (counit (R := R) (A := A)) (LinearMap.id : A →ₗ[R] A) (comul (R := R) a)
        = (1 : R) ⊗ₜ[R] a := rTensor_counit_comul (R := R) a
    rw [hr, TensorProduct.map_tmul]
    rfl
  have rhs : TensorProduct.map (counit (R := R) (A := A)) (LinearMap.id : C →ₗ[R] C) (a ⊗ₜ[R] (1 : C))
      = counit (R := R) a ⊗ₜ[R] (1 : C) := by
    rw [TensorProduct.map_tmul]; rfl
  rw [lhs, rhs] at h2
  have h3 := congrArg (TensorProduct.lid R C) h2
  rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul] at h3
  rw [h3, Algebra.algebraMap_eq_smul_one]

theorem apply_eq_zero_of_mem_hopfKer_of_counit_eq_zero {A : Type} [CommRing A] [Bialgebra R A]
    {C : Type} [CommRing C] [Bialgebra R C] (π : A →ₐc[R] C) {a : A} (ha : a ∈ HopfAlgebra.hopfKer π)
    (h0 : counit (R := R) a = 0) : π a = 0 := by
  rw [apply_eq_algebraMap_counit_of_mem_hopfKer π ha, h0, map_zero]

theorem apply_mem_hopfKer_of_mem_hopfKer_comp {A : Type} [CommRing A] [Bialgebra R A]
    {A' : Type} [CommRing A'] [Bialgebra R A'] {C : Type} [CommRing C] [Bialgebra R C]
    (σ : A →ₐc[R] A') (π : A' →ₐc[R] C) {x : A} (hx : x ∈ HopfAlgebra.hopfKer (π.comp σ)) :
    σ x ∈ HopfAlgebra.hopfKer π := by
  have h : Algebra.TensorProduct.map (AlgHom.id R A) ((π.comp σ : A →ₐc[R] C) : A →ₐ[R] C) (comul (R := R) x)
      = x ⊗ₜ[R] (1 : C) := hx
  show Algebra.TensorProduct.map (AlgHom.id R A') (π : A' →ₐ[R] C) (comul (R := R) (σ x)) = σ x ⊗ₜ[R] (1 : C)
  rw [← CoalgHomClass.map_comp_comul_apply σ x]
  have hcomp : (Algebra.TensorProduct.map (AlgHom.id R A') (π : A' →ₐ[R] C)).toLinearMap.comp
      (TensorProduct.map (σ : A →ₐc[R] A').toLinearMap (σ : A →ₐc[R] A').toLinearMap) =
      (TensorProduct.map (σ : A →ₐc[R] A').toLinearMap (LinearMap.id : C →ₗ[R] C)).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) ((π.comp σ : A →ₐc[R] C) : A →ₐ[R] C)).toLinearMap := by
    ext a b
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, LinearMap.id_coe]
    rfl
  have := LinearMap.congr_fun hcomp (comul (R := R) x)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  erw [this, h, TensorProduct.map_tmul]
  rfl

theorem hopfKer_le_hopfKer_comp {A : Type} [CommRing A] [Bialgebra R A]
    {A' : Type} [CommRing A'] [Bialgebra R A'] {C : Type} [CommRing C] [Bialgebra R C]
    (π : A →ₐc[R] A') (ρ : A' →ₐc[R] C) : HopfAlgebra.hopfKer π ≤ HopfAlgebra.hopfKer (ρ.comp π) := by
  intro d hd
  have h : Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] A') (comul (R := R) d) = d ⊗ₜ[R] (1 : A') := hd
  show Algebra.TensorProduct.map (AlgHom.id R A) ((ρ.comp π : A →ₐc[R] C) : A →ₐ[R] C) (comul (R := R) d) = d ⊗ₜ[R] (1 : C)
  have hcomp : (Algebra.TensorProduct.map (AlgHom.id R A) ((ρ.comp π : A →ₐc[R] C) : A →ₐ[R] C)).toLinearMap =
      (TensorProduct.map (LinearMap.id : A →ₗ[R] A) (ρ : A' →ₐc[R] C).toLinearMap).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] A')).toLinearMap := by
    ext a b
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, LinearMap.id_coe]
    rfl
  have := LinearMap.congr_fun hcomp (comul (R := R) d)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
  rw [this, h, TensorProduct.map_tmul]
  change d ⊗ₜ[R] ρ 1 = d ⊗ₜ[R] (1 : C)
  rw [map_one]

theorem counit_bialgHom {A : Type} [CommRing A] [Bialgebra R A] {C : Type} [CommRing C] [Bialgebra R C]
    (π : A →ₐc[R] C) (a : A) : counit (R := R) (π a) = counit (R := R) a :=
  CoalgHomClass.counit_comp_apply π a

end General

section Tower

set_option linter.unusedSectionVars false

variable {R : Type} [CommRing R] (p i₀ : ℕ)
  (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)] [∀ w, Coalgebra.IsCocomm R (B w)]
  (t : ∀ w, B (w + 1) →ₐc[R] B w) (m : ∀ w, B w →ₐc[R] B (w + 1))

noncomputable def downT : ∀ v : ℕ, B (i₀ + v + 1) → B (i₀ + 1)
  | 0 => id
  | v + 1 => fun a => downT v (t (i₀ + v + 1) a)

noncomputable def upM : ∀ v : ℕ, B (i₀ + 1) → B (i₀ + v + 1)
  | 0 => id
  | v + 1 => fun b => m (i₀ + v + 1) (upM v b)

noncomputable def upM' : ∀ u : ℕ, B i₀ → B (i₀ + u + 1)
  | 0 => fun b => m i₀ b
  | u + 1 => fun b => m (i₀ + u + 1) (upM' u b)

variable {p i₀ B t m}

theorem nsmulAlgHom_pow_eq_upM_downT
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p) :
    ∀ (v : ℕ) (a : B (i₀ + v + 1)),
      PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) a = upM i₀ B m v (downT i₀ B t v a)
  | 0, a => by simp [upM, downT, PDivisibleGroup.Hopf.nsmulAlgHom_one]
  | v + 1, a => by
    have hp : PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1 + 1)) p a = m (i₀ + v + 1) (t (i₀ + v + 1) a) := by
      rw [← PDivisibleGroup.Hopf.nsmulBialgHom_apply]
      exact (DFunLike.congr_fun (hmt (i₀ + v + 1)) a).symm
    show PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1 + 1)) (p ^ (v + 1)) a =
      m (i₀ + v + 1) (upM i₀ B m v (downT i₀ B t v (t (i₀ + v + 1) a)))
    rw [pow_succ, ← PDivisibleGroup.Hopf.nsmulAlgHom_nsmulAlgHom_apply, hp,
      PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, nsmulAlgHom_pow_eq_upM_downT hmt v]

theorem transitionLE_succ_eq_t_downT :
    ∀ (v : ℕ) (a : B (i₀ + v + 1)), PDivisibleGroup.Tower.transitionLE t i₀ (v + 1) a = t i₀ (downT i₀ B t v a)
  | 0, a => rfl
  | v + 1, a => by
    show PDivisibleGroup.Tower.transitionLE t i₀ (v + 1 + 1) a = t i₀ (downT i₀ B t v (t (i₀ + v + 1) a))
    rw [PDivisibleGroup.Tower.transitionLE_succ_apply, transitionLE_succ_eq_t_downT v]
    rfl

theorem downT_surjective (ht : ∀ w, Function.Surjective (t w)) :
    ∀ v : ℕ, Function.Surjective (downT i₀ B t v)
  | 0 => Function.surjective_id
  | v + 1 => (downT_surjective ht v).comp (ht (i₀ + v + 1))

theorem counit_upM : ∀ (v : ℕ) (b : B (i₀ + 1)), counit (R := R) (upM i₀ B m v b) = counit (R := R) b
  | 0, _ => rfl
  | v + 1, b => by
    show counit (R := R) (m (i₀ + v + 1) (upM i₀ B m v b)) = counit (R := R) b
    rw [counit_bialgHom, counit_upM v b]

theorem surjOn_upM_hopfKer
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2)))) :
    ∀ v : ℕ, Set.SurjOn (upM i₀ B m v) (HopfAlgebra.hopfKer (t i₀) : Set (B (i₀ + 1)))
      (HopfAlgebra.hopfKer (t (i₀ + v)) : Set (B (i₀ + v + 1)))
  | 0 => by
    intro d hd
    exact ⟨d, hd, rfl⟩
  | v + 1 => by
    have h := (hbij (i₀ + v) (Nat.le_add_right _ _)).surjOn.comp (surjOn_upM_hopfKer hbij v)
    exact h

theorem nsmulAlgHom_pow_succ_eq_upM'_transitionLE
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p) :
    ∀ (u : ℕ) (y : B (i₀ + u + 1)),
      PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + u + 1)) (p ^ (u + 1)) y =
        upM' i₀ B m u (PDivisibleGroup.Tower.transitionLE t i₀ (u + 1) y)
  | 0, y => by
    rw [pow_one]
    show PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + 0 + 1)) p y = m i₀ (PDivisibleGroup.Tower.transitionLE t i₀ 1 y)
    rw [← PDivisibleGroup.Hopf.nsmulBialgHom_apply, PDivisibleGroup.Tower.transitionLE_one]
    exact (DFunLike.congr_fun (hmt i₀) y).symm
  | u + 1, y => by
    have hp : PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + u + 1 + 1)) p y = m (i₀ + u + 1) (t (i₀ + u + 1) y) := by
      rw [← PDivisibleGroup.Hopf.nsmulBialgHom_apply]
      exact (DFunLike.congr_fun (hmt (i₀ + u + 1)) y).symm
    show PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + u + 1 + 1)) (p ^ (u + 1 + 1)) y =
      m (i₀ + u + 1) (upM' i₀ B m u (PDivisibleGroup.Tower.transitionLE t i₀ (u + 1 + 1) y))
    rw [pow_succ, ← PDivisibleGroup.Hopf.nsmulAlgHom_nsmulAlgHom_apply, hp,
      PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, nsmulAlgHom_pow_succ_eq_upM'_transitionLE hmt u]
    rfl

end Tower

end G3

open G3 in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] (p i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (m : ∀ w, B w →ₐc[R] B (w + 1))
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p)
    (htm : ∀ w, (t w).comp (m w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B w) p)
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (v : ℕ) (x : B (i₀ + v + 1))
    (hx : x ∈ HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1))) :
    t (i₀ + v) x = 0 ↔
      x ∈ Ideal.span (PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) ''
        ((HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1)) : Set (B (i₀ + v + 1))) ∩
          (PDivisibleGroup.Hopf.augIdeal R (B (i₀ + v + 1)) : Set (B (i₀ + v + 1))))) := by
  classical

  have hKv : ∀ {y : B (i₀ + v + 1)}, y ∈ HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1)) →
      t (i₀ + v) y ∈ HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v) := fun hy =>
    apply_mem_hopfKer_of_mem_hopfKer_comp (t (i₀ + v)) (PDivisibleGroup.Tower.transitionLE t i₀ v) hy

  have hkill : ∀ (u : ℕ) (y : B (i₀ + u)), y ∈ HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ u) →
      counit (R := R) y = 0 → PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + u)) (p ^ u) y = 0 := by
    intro u
    cases u with
    | zero =>
      intro y hy hy0
      have h := apply_eq_algebraMap_counit_of_mem_hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ 0) hy
      change y = _ at h
      rw [pow_zero, PDivisibleGroup.Hopf.nsmulAlgHom_one, AlgHom.id_apply, h, hy0, map_zero]
    | succ u =>
      intro y hy hy0
      show PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + u + 1)) (p ^ (u + 1)) y = 0
      rw [nsmulAlgHom_pow_succ_eq_upM'_transitionLE hmt u y,
        apply_eq_algebraMap_counit_of_mem_hopfKer _ hy, hy0, map_zero]

      clear hy hy0 y
      induction u with
      | zero => exact map_zero _
      | succ u ih =>
        show m (i₀ + u + 1) (upM' i₀ B m u 0) = 0
        rw [ih, map_zero]
  constructor
  ·
    intro h0
    have hxker : x ∈ RingHom.ker (t (i₀ + v) : B (i₀ + v + 1) →+* B (i₀ + v)) := h0
    rw [HopfAlgebra.ker_eq_map_hopfKer_inf_ker_counit_of_surjective (t (i₀ + v)) (ht (i₀ + v))] at hxker
    refine (Ideal.span_le.mpr ?_) hxker
    rintro d ⟨hdD, hd0⟩

    obtain ⟨d₀, hd₀, hd⟩ := surjOn_upM_hopfKer hbij v hdD
    obtain ⟨k, hk⟩ := downT_surjective ht v d₀
    have hεd₀ : counit (R := R) d₀ = 0 := by
      have : counit (R := R) d = 0 := hd0
      rwa [← hd, counit_upM] at this

    have hkker : k ∈ RingHom.ker
        (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1) : B (i₀ + v + 1) →+* B i₀) := by
      rw [RingHom.mem_ker]
      show PDivisibleGroup.Tower.transitionLE t i₀ (v + 1) k = 0
      rw [transitionLE_succ_eq_t_downT v k, hk, apply_eq_algebraMap_counit_of_mem_hopfKer (t i₀) hd₀, hεd₀,
        map_zero]

    rw [HopfAlgebra.ker_eq_map_hopfKer_inf_ker_counit_of_surjective (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1))
      (PDivisibleGroup.Tower.transitionLE_surjective t ht i₀ (v + 1))] at hkker

    have hpk : PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) k = d := by
      rw [nsmulAlgHom_pow_eq_upM_downT hmt v k, hk, hd]
    rw [← hpk]
    have hmem := Ideal.mem_map_of_mem (PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v)) hkker
    rw [Ideal.map_span] at hmem
    exact hmem
  ·
    intro hxs
    have hgen : ∀ y ∈ PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) ''
        ((HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1)) : Set (B (i₀ + v + 1))) ∩
          (PDivisibleGroup.Hopf.augIdeal R (B (i₀ + v + 1)) : Set (B (i₀ + v + 1)))),
        t (i₀ + v) y = 0 := by
      rintro _ ⟨k, ⟨hkK, hk0⟩, rfl⟩
      rw [← PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply]
      exact hkill v (t (i₀ + v) k) (hKv hkK) (by rw [counit_bialgHom]; exact hk0)
    have hle : Ideal.span (PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) ''
        ((HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ (v + 1)) : Set (B (i₀ + v + 1))) ∩
          (PDivisibleGroup.Hopf.augIdeal R (B (i₀ + v + 1)) : Set (B (i₀ + v + 1))))) ≤
        RingHom.ker (t (i₀ + v) : B (i₀ + v + 1) →+* B (i₀ + v)) :=
      Ideal.span_le.mpr fun y hy => hgen y hy
    exact hle hxs

end S_PDivisibleGroup_Tower_transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
end P2MW
export P2MW.S_PDivisibleGroup_Tower_transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing (solution)
