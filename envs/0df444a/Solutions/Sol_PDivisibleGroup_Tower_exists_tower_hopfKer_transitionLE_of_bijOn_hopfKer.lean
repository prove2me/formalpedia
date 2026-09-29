-- Prove2me | solution 1 for PDivisibleGroup.Tower.exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/59d11659-22e3-5de8-870c-7df32d888508

import Mathlib
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_PDivisibleGroup_Tower_map_hopfKer_transitionLE_succ_eq
import Theorems.Thm_PDivisibleGroup_Tower_transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
p2m_attr_erase "instance" "HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace Ws47
namespace Gamma

p2m_open "HopfAlgebra~augIdeal PDivisibleGroup PDivisibleGroup.Tower"

variable {R : Type} [CommRing R] [IsLocalRing R]

section Kernel

variable {A : Type} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
variable (π : A →ₐc[R] B) (hπ : Function.Surjective π)
include hπ

theorem finite_hopfKer : Module.Finite R ↥(hopfKer π) :=
  (HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ).2.1

theorem free_hopfKer : Module.Free R ↥(hopfKer π) := by
  obtain ⟨-, hfin, hproj, -⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  haveI := hfin; haveI := hproj
  exact Module.free_of_flat_of_isLocalRing

theorem finrank_hopfKer_mul : Module.finrank R ↥(hopfKer π) * Module.finrank R B = Module.finrank R A := by
  obtain ⟨-, hfin, hproj, hrank⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  haveI := hfin; haveI := hproj
  haveI : Module.Free R ↥(hopfKer π) := Module.free_of_flat_of_isLocalRing
  have h := hrank (IsLocalRing.closedPoint R)
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

end Kernel

theorem nontrivial_of_hopf (A : Type) [CommRing A] [HopfAlgebra R A] : Nontrivial A := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (Coalgebra.counit (R := R) (A := A)) h
  rw [map_zero, Bialgebra.counit_one] at h'
  exact zero_ne_one h'

theorem finrank_pos_of_hopf (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A] :
    0 < Module.finrank R A := by
  classical
  haveI := nontrivial_of_hopf (R := R) A
  rw [Module.finrank_eq_card_chooseBasisIndex]
  haveI := (Module.Free.chooseBasis R A).index_nonempty
  exact Fintype.card_pos

end Ws47.Gamma

namespace Ws47
namespace Gamma

p2m_open "HopfAlgebra~augIdeal PDivisibleGroup PDivisibleGroup.Tower"

variable {R : Type} [CommRing R] [IsLocalRing R]

section TowerRank

variable (p h' i₀ : ℕ)
  (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
  [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
  (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
  (m : ∀ w, B w →ₐc[R] B (w + 1))
  (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
    (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
  (hrank : Module.finrank R ↥(HopfAlgebra.hopfKer (t i₀)) = p ^ h')

include ht hbij hrank

theorem finrank_hopfKer_layer (w : ℕ) (hw : i₀ ≤ w) : Module.finrank R ↥(HopfAlgebra.hopfKer (t w)) = p ^ h' := by
  induction w, hw using Nat.le_induction with
  | base => exact hrank
  | succ w hw ih =>

    have hb := hbij w hw
    let f : ↥(HopfAlgebra.hopfKer (t w)) →ₗ[R] ↥(HopfAlgebra.hopfKer (t (w + 1))) :=
      { toFun := fun x => ⟨m (w + 1) x, hb.mapsTo x.2⟩
        map_add' := fun x y => Subtype.ext (by simp)
        map_smul' := fun r x => Subtype.ext (by simp) }
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        exact Subtype.ext (hb.injOn x.2 y.2 (congrArg Subtype.val hxy))
      · intro y
        obtain ⟨x, hx, hxy⟩ := hb.surjOn y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    rw [← ih]
    exact (LinearEquiv.ofBijective f hf).finrank_eq.symm

theorem finrank_level (v : ℕ) : Module.finrank R (B (i₀ + v)) = p ^ (v * h') * Module.finrank R (B i₀) := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hmul := finrank_hopfKer_mul (t (i₀ + v)) (ht (i₀ + v))
    rw [finrank_hopfKer_layer p h' i₀ B t ht m hbij hrank (i₀ + v) (Nat.le_add_right _ _)] at hmul
    rw [show i₀ + (v + 1) = i₀ + v + 1 from rfl, ← hmul, ih, Nat.succ_mul, pow_add]
    ring

theorem finrank_hopfKer_transitionLE (v : ℕ) :
    Module.finrank R ↥(HopfAlgebra.hopfKer (transitionLE t i₀ v)) = p ^ (v * h') := by
  have hmul := finrank_hopfKer_mul (transitionLE t i₀ v) (transitionLE_surjective t ht i₀ v)
  rw [finrank_level p h' i₀ B t ht m hbij hrank v] at hmul
  exact Nat.eq_of_mul_eq_mul_right (finrank_pos_of_hopf (R := R) (B i₀)) hmul

end TowerRank

end Ws47.Gamma

namespace Ws47
namespace Gamma

p2m_open "HopfAlgebra~augIdeal PDivisibleGroup PDivisibleGroup.Tower"

section Restrict

variable {R : Type} [CommRing R]
variable {A₁ : Type} [CommRing A₁] [HopfAlgebra R A₁] [Coalgebra.IsCocomm R A₁]
variable {A₂ : Type} [CommRing A₂] [HopfAlgebra R A₂] [Coalgebra.IsCocomm R A₂]
variable {C : Type} [CommRing C] [HopfAlgebra R C]
variable (π₁ : A₁ →ₐc[R] C) (π₂ : A₂ →ₐc[R] C) (f : A₁ →ₐc[R] A₂)
variable (hf : ∀ a, π₂ (f a) = π₁ a)
include hf

theorem mapsTo_hopfKer : Set.MapsTo f (hopfKer π₁ : Set A₁) (hopfKer π₂ : Set A₂) := by
  intro a ha
  rw [SetLike.mem_coe, mem_hopfKer_iff, coaction_apply] at ha ⊢
  have key : ∀ (g : A₁ →ₗ[R] A₂), (∀ b, g b = f b) → ∀ x : A₁ ⊗[R] A₁,
      Algebra.TensorProduct.map (AlgHom.id R A₂) (π₂ : A₂ →ₐ[R] C) (TensorProduct.map g g x) =
        Algebra.TensorProduct.map (f : A₁ →ₐ[R] A₂) (AlgHom.id R C)
          (Algebra.TensorProduct.map (AlgHom.id R A₁) (π₁ : A₁ →ₐ[R] C) x) := by
    intro g hg x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hg]
      show f a ⊗ₜ[R] π₂ (f b) = f a ⊗ₜ[R] π₁ b
      rw [hf]
  rw [← CoalgHomClass.map_comp_comul_apply f a]
  refine (key _ (fun _ => rfl) _).trans ?_
  rw [ha, Algebra.TensorProduct.map_tmul, map_one]
  rfl

noncomputable def resAlgHom : ↥(hopfKer π₁) →ₐ[R] ↥(hopfKer π₂) :=
  AlgHom.codRestrict ((f : A₁ →ₐ[R] A₂).comp (hopfKer π₁).val) (hopfKer π₂)
    (fun s => mapsTo_hopfKer π₁ π₂ f hf s.2)

@[scoped simp] theorem coe_resAlgHom (s : ↥(hopfKer π₁)) : ((resAlgHom π₁ π₂ f hf s : ↥(hopfKer π₂)) : A₂) = f s := rfl

variable [Module.Flat R A₁] [Module.Flat R A₂] [Module.Flat R C]
  [Module.Flat R ↥(hopfKer π₁)] [Module.Flat R ↥(hopfKer π₂)]

noncomputable def resBialgHom : ↥(hopfKer π₁) →ₐc[R] ↥(hopfKer π₂) :=
  { resAlgHom π₁ π₂ f hf with
    map_smul' := fun r s => by simp
    counit_comp := by
      ext s
      simp only [LinearMap.coe_comp, Function.comp_apply]
      show Coalgebra.counit (R := R) (resAlgHom π₁ π₂ f hf s) = Coalgebra.counit (R := R) s
      rw [counit_coe, counit_coe, coe_resAlgHom]
      exact CoalgHomClass.counit_comp_apply f _
    map_comp_comul := by
      ext s
      apply HopfAlgebra.HopfKerHopf.ι₂_injective π₂
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [HopfAlgebra.HopfKerHopf.ι₂_eq_map]
      change TensorProduct.map (HopfAlgebra.HopfKerHopf.valL π₂) (HopfAlgebra.HopfKerHopf.valL π₂)
          (TensorProduct.map (resAlgHom π₁ π₂ f hf).toLinearMap (resAlgHom π₁ π₂ f hf).toLinearMap
            (Coalgebra.comul (R := R) s)) =
        TensorProduct.map (HopfAlgebra.HopfKerHopf.valL π₂) (HopfAlgebra.HopfKerHopf.valL π₂)
          (Coalgebra.comul (R := R) (resAlgHom π₁ π₂ f hf s))
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have h1 : HopfAlgebra.HopfKerHopf.valL π₂ ∘ₗ (resAlgHom π₁ π₂ f hf).toLinearMap
          = (f : A₁ →ₐc[R] A₂).toLinearMap ∘ₗ HopfAlgebra.HopfKerHopf.valL π₁ := by
        ext x; rfl
      rw [h1, TensorProduct.map_comp, LinearMap.comp_apply]
      have h2 : TensorProduct.map (HopfAlgebra.HopfKerHopf.valL π₁) (HopfAlgebra.HopfKerHopf.valL π₁)
          (Coalgebra.comul (R := R) s) = Coalgebra.comul (R := R) (s : A₁) := map_val_val_comul π₁ s
      have h3 : TensorProduct.map (HopfAlgebra.HopfKerHopf.valL π₂) (HopfAlgebra.HopfKerHopf.valL π₂)
          (Coalgebra.comul (R := R) (resAlgHom π₁ π₂ f hf s)) = Coalgebra.comul (R := R) ((resAlgHom π₁ π₂ f hf s : ↥(hopfKer π₂)) : A₂) :=
        map_val_val_comul π₂ _
      rw [h2, h3, coe_resAlgHom]
      exact CoalgHomClass.map_comp_comul_apply f _ }

@[scoped simp] theorem coe_resBialgHom (s : ↥(hopfKer π₁)) : ((resBialgHom π₁ π₂ f hf s : ↥(hopfKer π₂)) : A₂) = f s := rfl

end Restrict

end Ws47.Gamma
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47 P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47.Gamma"
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47"

namespace Ws47
namespace Gamma

p2m_open "HopfAlgebra~augIdeal PDivisibleGroup PDivisibleGroup.Tower PDivisibleGroup.Hopf"

section Summand

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (K : Subalgebra R A)

theorem mem_of_mem_span_of_retraction (r : A →ₗ[K] K) (hr : ∀ c : K, r (c : A) = c)
    (I : Ideal K) (S : Set A) (hS : ∀ s ∈ S, ∃ c : K, c ∈ I ∧ (c : A) = s)
    (x : K) (hx : (x : A) ∈ Ideal.span S) : x ∈ I := by
  classical
  obtain ⟨n, a, g, hsum⟩ := (Submodule.mem_span_set'.mp hx)
  have hrx : r (x : A) = x := hr x
  rw [← hrx, ← hsum, map_sum]
  refine I.sum_mem fun i _ => ?_
  obtain ⟨c, hc, hcg⟩ := hS (g i) (g i).2
  rw [← hcg, smul_eq_mul, mul_comm, ← smul_eq_mul, ← Subalgebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  exact I.mul_mem_right _ hc

end Summand
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47 P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47.Gamma"

section Assembly

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem parent' [IsDomain R] [IsPrincipalIdealRing R] (p h' i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (m : ∀ w, B w →ₐc[R] B (w + 1))
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p)
    (htm : ∀ w, (t w).comp (m w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B w) p)
    (hkill : ∀ w, ∀ d ∈ HopfAlgebra.hopfKer (t w),
      PDivisibleGroup.Hopf.nsmulAlgHom R (B (w + 1)) p d = algebraMap R (B (w + 1)) (Coalgebra.counit d))
    (hmaps : ∀ w, Set.MapsTo (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hrank : Module.finrank R ↥(HopfAlgebra.hopfKer (t i₀)) = p ^ h') :
    ∃ (L : ℕ → Type) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra R (L v))
      (_ : ∀ v, Coalgebra.IsCocomm R (L v)) (_ : ∀ v, Module.Free R (L v)) (_ : ∀ v, Module.Finite R (L v))
      (t' : ∀ v, L (v + 1) →ₐc[R] L v) (ι : ∀ v, L v →ₐc[R] B (i₀ + v)),
      (∀ v, Function.Surjective (t' v)) ∧ (∀ v, Module.finrank R (L v) = p ^ (v * h')) ∧
      (∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal R (L (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Injective (ι v)) ∧
      (∀ v, (ι v : L v →ₐ[R] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) ∧
      (∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) := by
  classical

  have hT : ∀ v, Function.Surjective (transitionLE t i₀ v) := transitionLE_surjective t ht i₀
  haveI hfree : ∀ v, Module.Free R ↥(hopfKer (transitionLE t i₀ v)) := fun v => free_hopfKer _ (hT v)
  haveI hfin : ∀ v, Module.Finite R ↥(hopfKer (transitionLE t i₀ v)) := fun v => finite_hopfKer _ (hT v)
  haveI hflat : ∀ v, Module.Flat R ↥(hopfKer (transitionLE t i₀ v)) := fun v => inferInstance
  haveI hflatB : ∀ w, Module.Flat R (B w) := fun w => inferInstance

  let t' : ∀ v, ↥(hopfKer (transitionLE t i₀ (v + 1))) →ₐc[R] ↥(hopfKer (transitionLE t i₀ v)) := fun v =>
    resBialgHom (transitionLE t i₀ (v + 1)) (transitionLE t i₀ v) (t (i₀ + v)) (fun _ => rfl)
  refine ⟨fun v => ↥(hopfKer (transitionLE t i₀ v)), inferInstance, inferInstance, inferInstance, hfree, hfin, t',
    fun v => hopfKerVal (transitionLE t i₀ v), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v y
    have hy : (y : B (i₀ + v)) ∈ (hopfKer (transitionLE t i₀ (v + 1))).map (t (i₀ + v) : B (i₀ + v + 1) →ₐ[R] B (i₀ + v)) := by
      rw [PDivisibleGroup.Tower.map_hopfKer_transitionLE_succ_eq i₀ B t ht hfree v]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subalgebra.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  ·
    intro v
    exact finrank_hopfKer_transitionLE p h' i₀ B t ht m hbij hrank v
  ·
    intro v
    haveI := hflat (v + 1); haveI := hfree (v + 1); haveI := hfin (v + 1)
    ext x
    rw [RingHom.mem_ker]
    have hx0 : t' v x = 0 ↔ t (i₀ + v) (x : B (i₀ + v + 1)) = 0 := by
      rw [Subtype.ext_iff]
      exact Iff.rfl
    rw [hx0, PDivisibleGroup.Tower.transition_apply_eq_zero_iff_mem_span_nsmulAlgHom_image_of_bijOn_hopfKer_of_isPrincipalIdealRing
      p i₀ B t ht m hmt htm hbij v x x.2]

    have hval : ∀ (y : ↥(hopfKer (transitionLE t i₀ (v + 1)))),
        ((nsmulAlgHom R ↥(hopfKer (transitionLE t i₀ (v + 1))) (p ^ v) y : ↥(hopfKer (transitionLE t i₀ (v + 1)))) : B (i₀ + v + 1))
          = nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) (y : B (i₀ + v + 1)) := fun y =>
      (nsmulAlgHom_bialgHom_apply (hopfKerVal (transitionLE t i₀ (v + 1))) (p ^ v) y).symm
    have hgen : ∀ s, s ∈ nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) '' (((hopfKer (transitionLE t i₀ (v + 1))) : Set (B (i₀ + v + 1))) ∩ (augIdeal R (B (i₀ + v + 1)) : Set _)) →
        ∃ c : ↥(hopfKer (transitionLE t i₀ (v + 1))), c ∈ torsionIdeal R ↥(hopfKer (transitionLE t i₀ (v + 1))) (p ^ v) ∧ (c : B (i₀ + v + 1)) = s := by
      rintro s ⟨y, ⟨hyK, hyaug⟩, rfl⟩
      refine ⟨nsmulAlgHom R _ (p ^ v) ⟨y, hyK⟩, nsmulAlgHom_mem_torsionIdeal R _ ?_ _, hval ⟨y, hyK⟩⟩
      rw [Hopf.mem_augIdeal_iff, counit_coe]
      exact hyaug
    constructor
    · intro h
      obtain ⟨⟨r, hr⟩, -, -, -⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
        (transitionLE t i₀ (v + 1)) (hT (v + 1))
      exact mem_of_mem_span_of_retraction (hopfKer (transitionLE t i₀ (v + 1))) r hr _ _ hgen x h
    · intro h

      have hle : torsionIdeal R ↥(hopfKer (transitionLE t i₀ (v + 1))) (p ^ v) ≤
          (Ideal.span (nsmulAlgHom R (B (i₀ + v + 1)) (p ^ v) ''
            (((hopfKer (transitionLE t i₀ (v + 1))) : Set (B (i₀ + v + 1))) ∩ (augIdeal R (B (i₀ + v + 1)) : Set _)))).comap
            ((hopfKer (transitionLE t i₀ (v + 1))).val : ↥(hopfKer (transitionLE t i₀ (v + 1))) →+* B (i₀ + v + 1)) := by
        rw [torsionIdeal, Ideal.map_le_iff_le_comap]
        intro y hy
        rw [Ideal.mem_comap, Ideal.mem_comap]
        refine Ideal.subset_span ⟨(y : B (i₀ + v + 1)), ⟨y.2, ?_⟩, ?_⟩
        · rw [Hopf.mem_augIdeal_iff] at hy
          rw [SetLike.mem_coe, Hopf.mem_augIdeal_iff, ← counit_coe]
          exact hy
        · exact (hval y).symm
      exact hle h
  · exact fun v => hopfKerVal_injective _
  · intro v
    ext y
    constructor
    · rintro ⟨s, rfl⟩; exact s.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  · intro v
    exact BialgHom.ext fun _ => rfl

end Assembly
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47 P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47.Gamma"

end Ws47.Gamma
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47 P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47.Gamma"
p2m_reactivate "P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47 P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer.Ws47.Gamma"

open Ws47.Gamma in

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R] (p h' i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w) (ht : ∀ w, Function.Surjective (t w))
    (m : ∀ w, B w →ₐc[R] B (w + 1))
    (hmt : ∀ w, (m w).comp (t w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B (w + 1)) p)
    (htm : ∀ w, (t w).comp (m w) = PDivisibleGroup.Hopf.nsmulBialgHom R (B w) p)
    (hkill : ∀ w, ∀ d ∈ HopfAlgebra.hopfKer (t w),
      PDivisibleGroup.Hopf.nsmulAlgHom R (B (w + 1)) p d = algebraMap R (B (w + 1)) (Coalgebra.counit d))
    (hmaps : ∀ w, Set.MapsTo (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hbij : ∀ w, i₀ ≤ w → Set.BijOn (m (w + 1)) (HopfAlgebra.hopfKer (t w) : Set (B (w + 1)))
      (HopfAlgebra.hopfKer (t (w + 1)) : Set (B (w + 2))))
    (hrank : Module.finrank R ↥(HopfAlgebra.hopfKer (t i₀)) = p ^ h') :
    ∃ (L : ℕ → Type) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra R (L v))
      (_ : ∀ v, Coalgebra.IsCocomm R (L v)) (_ : ∀ v, Module.Free R (L v)) (_ : ∀ v, Module.Finite R (L v))
      (t' : ∀ v, L (v + 1) →ₐc[R] L v) (ι : ∀ v, L v →ₐc[R] B (i₀ + v)),
      (∀ v, Function.Surjective (t' v)) ∧ (∀ v, Module.finrank R (L v) = p ^ (v * h')) ∧
      (∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal R (L (v + 1)) (p ^ v)) ∧
      (∀ v, Function.Injective (ι v)) ∧
      (∀ v, (ι v : L v →ₐ[R] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) ∧
      (∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) := by
  exact Ws47.Gamma.parent' p h' i₀ B t ht m hmt htm hkill hmaps hbij hrank

end S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer
end P2MW
export P2MW.S_PDivisibleGroup_Tower_exists_tower_hopfKer_transitionLE_of_bijOn_hopfKer (solution)
