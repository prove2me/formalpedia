-- Prove2me | solution 1 for RingHom.finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/12039ff6-c87a-561e-aa39-631b9cc4668c

import Mathlib
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Theorems.Thm_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
import Theorems.Thm_RingHom_finite_and_faithfullyFlat_of_maximalIdeal_eq_span_natCast_of_mem_jacobson
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace RingHom
p2m_export "RingHom" "range_eq_top Flat Finite.of_surjective Finite ext ker_eq_comap_bot FaithfullyFlat mk ker mem_ker toAlgebra finite_and_faithfullyFlat_of_maximalIdeal_eq_span_natCast_of_mem_jacobson"
namespace ETQE
p2m_open "RingHom"

open scoped TensorProduct

private theorem projective_quotient_span_one_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Projective R A] {e : A} (he : IsIdempotentElem e) :
    Module.Projective R (A ⧸ Ideal.span {1 - e}) := by
  let I : Ideal A := Ideal.span {1 - e}
  have hI : ∀ a ∈ I, e * a = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [mul_left_comm, he.mul_one_sub_self, mul_zero]
  let i₀ : (A ⧸ I.restrictScalars R) →ₗ[R] A :=
    (I.restrictScalars R).liftQ (LinearMap.mulLeft R e) (fun a ha => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact hI a ha)
  let i : (A ⧸ I) →ₗ[R] A := i₀ ∘ₗ (Submodule.Quotient.restrictScalarsEquiv R I).symm.toLinearMap
  let s : A →ₗ[R] (A ⧸ I) := (Ideal.Quotient.mkₐ R I).toLinearMap
  refine Module.Projective.of_split i s ?_
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk I (e * a) = Ideal.Quotient.mk I a
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton'.mpr ⟨-a, by ring⟩)

private theorem not_isUnit_natCast {𝓞 A : Type*} [CommRing 𝓞] [CommRing A] [Algebra 𝓞 A]
    [Module.Finite 𝓞 A] [Nontrivial A] (p : ℕ) (hpJ : (p : 𝓞) ∈ (⊥ : Ideal 𝓞).jacobson) :
    ¬ IsUnit (p : A) := by
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hle : (⊤ : Submodule 𝓞 A) ≤ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 A) := by
    intro x _
    have hx : x = (p : 𝓞) • ((↑u⁻¹ : A) * x) := by
      rw [Algebra.smul_def, map_natCast, ← mul_assoc, ← hu, Units.mul_inv, one_mul]
    rw [hx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have htop : (⊤ : Submodule 𝓞 A) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top hle (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hpJ)
  have h1 : (1 : A) ∈ (⊤ : Submodule 𝓞 A) := Submodule.mem_top
  rw [htop, Submodule.mem_bot] at h1
  exact one_ne_zero h1

private theorem jacobson_bot_eq_bot {R : Type*} [CommRing R] [IsArtinianRing R] [IsReduced R] :
    (⊥ : Ideal R).jacobson = ⊥ := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  refine le_bot_iff.mp fun x hx => ?_
  have h : x ^ n ∈ (⊥ : Ideal R).jacobson ^ n := Ideal.pow_mem_pow hx n
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact Ideal.mem_bot.mpr (IsReduced.eq_zero x ⟨n, h⟩)

private theorem mem_span_natCast_of_one_tmul_eq_zero {𝓞 : Type*} [CommRing 𝓞] (p : ℕ)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {H : Type*} [CommRing H] [Algebra 𝓞 H] {h : H} (hh : (1 : ZMod p) ⊗ₜ[𝓞] h = 0) :
    h ∈ Ideal.span {(p : H)} := by
  let θ : (𝓞 ⧸ RingHom.ker (Algebra.ofId 𝓞 (ZMod p))) ≃ₐ[𝓞] ZMod p :=
    Ideal.quotientKerAlgEquivOfSurjective (ZMod.ringHom_surjective _)
  let Φ : (ZMod p ⊗[𝓞] H) ≃ₐ[𝓞] ((𝓞 ⧸ RingHom.ker (Algebra.ofId 𝓞 (ZMod p))) ⊗[𝓞] H) :=
    Algebra.TensorProduct.congr θ.symm AlgEquiv.refl
  have h1 : Φ ((1 : ZMod p) ⊗ₜ h) = (1 : 𝓞 ⧸ RingHom.ker (Algebra.ofId 𝓞 (ZMod p))) ⊗ₜ h := by
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have h2 : ((1 : 𝓞 ⧸ RingHom.ker (Algebra.ofId 𝓞 (ZMod p))) ⊗ₜ[𝓞] h) = 0 := by
    rw [← h1, hh, map_zero]
  have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul H (RingHom.ker (Algebra.ofId 𝓞 (ZMod p)))) h2
  rw [map_zero, ← map_one (Ideal.Quotient.mk _), TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map] at h3
  have h4 : h ∈ (RingHom.ker (Algebra.ofId 𝓞 (ZMod p))).map (algebraMap 𝓞 H) := h3
  have hK : RingHom.ker (Algebra.ofId 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)} := hker
  rw [hK, Ideal.map_span, Set.image_singleton, map_natCast] at h4
  exact h4

end RingHom.ETQE

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (H : Type v) [CommRing H] [Algebra 𝓞 H] [Module.Free 𝓞 H] [Module.Finite 𝓞 H]
    (hred : IsReduced (ZMod p ⊗[𝓞] H))
    (T : Type w) [CommRing T] [Algebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]
    (ι : H →ₐ[𝓞] T) (hι : Function.Injective ι) :
    ι.toRingHom.Finite ∧ ι.toRingHom.FaithfullyFlat := by
  classical

  obtain ⟨hdom, hdvr, _, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  haveI := hdvr
  haveI : HenselianLocalRing 𝓞 :=
    { is_henselian := fun f hf a₀ h₁ h₂ => by
        rw [hmax] at h₁ ⊢
        exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _) }
  have hpJ : (p : 𝓞) ∈ (⊥ : Ideal 𝓞).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : 𝓞)}) (Ideal.mem_span_singleton_self _)

  letI : Algebra H T := ι.toRingHom.toAlgebra
  haveI : IsScalarTower 𝓞 H T := IsScalarTower.of_algebraMap_eq fun r => (ι.commutes r).symm
  haveI hfinHT : Module.Finite H T := Module.Finite.of_restrictScalars_finite 𝓞 H T
  refine ⟨hfinHT, ?_⟩
  change Module.FaithfullyFlat H T

  let ψ : H →ₐ[𝓞] ZMod p ⊗[𝓞] H := Algebra.TensorProduct.includeRight
  have hψ : ∀ h, ψ h = (1 : ZMod p) ⊗ₜ h := fun h => rfl
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨h, hh⟩ := TensorProduct.mk_surjective 𝓞 H (ZMod p) (ZMod.ringHom_surjective _) z
    exact ⟨h, hh⟩
  haveI : IsArtinianRing (ZMod p ⊗[𝓞] H) := IsArtinianRing.of_finite (ZMod p) (ZMod p ⊗[𝓞] H)
  haveI := hred
  have hjac : (⊥ : Ideal (ZMod p ⊗[𝓞] H)).jacobson = ⊥ := RingHom.ETQE.jacobson_bot_eq_bot

  obtain ⟨hF, e, hce, he1, he2, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := 𝓞) (S := H)
  let E : MaximalSpectrum H → Type v := fun i => H ⧸ Ideal.span {1 - e i}
  let T' : MaximalSpectrum H → Type w := fun i => T ⧸ Ideal.span {1 - ι (e i)}
  have hidem : ∀ i, IsIdempotentElem (e i) := fun i => hce.idem i
  have hfidem : ∀ i, IsIdempotentElem (ι (e i)) := fun i => (hidem i).map ι
  have hone_sub_mem : ∀ i : MaximalSpectrum H, 1 - e i ∈ i.asIdeal := by
    intro i
    have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ i)
    rw [hce.complete] at h
    rw [show (1 : H) - e i = ∑ j ∈ Finset.univ.erase i, e j by rw [← h]; ring]
    exact Ideal.sum_mem _ fun j hj => he2 j i (Finset.ne_of_mem_erase hj)
  have hmk_surj : ∀ i, Function.Surjective (Ideal.Quotient.mk (Ideal.span {1 - e i})) := fun i =>
    Ideal.Quotient.mk_surjective

  have hcomap_map : ∀ i : MaximalSpectrum H, (i.asIdeal.map (Ideal.Quotient.mk (Ideal.span {1 - e i}))).comap
      (Ideal.Quotient.mk (Ideal.span {1 - e i})) = i.asIdeal := by
    intro i
    rw [Ideal.comap_map_of_surjective _ (hmk_surj i), ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (hone_sub_mem i)
  have hne : ∀ i : MaximalSpectrum H, i.asIdeal.map (Ideal.Quotient.mk (Ideal.span {1 - e i})) ≠ ⊤ := by
    intro i htop
    have h := hcomap_map i
    rw [htop, Ideal.comap_top] at h
    exact i.isMaximal.ne_top h.symm
  haveI hlocE : ∀ i, IsLocalRing (E i) := hloc
  have hmapmax : ∀ i : MaximalSpectrum H, i.asIdeal.map (Ideal.Quotient.mk (Ideal.span {1 - e i})) =
      IsLocalRing.maximalIdeal (E i) := fun i =>
    IsLocalRing.eq_maximalIdeal
      ((Ideal.map_eq_top_or_isMaximal_of_surjective _ (hmk_surj i) i.isMaximal).resolve_left (hne i))

  have hle : ∀ i, Ideal.span {1 - e i} ≤ (Ideal.span {1 - ι (e i)}).comap (ι : H →+* T) := by
    intro i
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_sub, map_one]
    exact Ideal.mem_span_singleton_self _
  let ιq : ∀ i, E i →ₐ[𝓞] T' i := fun i => Ideal.quotientMapₐ _ ι (hle i)

  haveI hfinE : ∀ i, Module.Finite 𝓞 (E i) := fun i =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {1 - e i})).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝓞 _)
  haveI hfinT' : ∀ i, Module.Finite 𝓞 (T' i) := fun i =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {1 - ι (e i)})).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝓞 _)
  haveI hfreeE : ∀ i, Module.Free 𝓞 (E i) := fun i => by
    haveI : Module.Projective 𝓞 (E i) := RingHom.ETQE.projective_quotient_span_one_sub (hidem i)
    exact Module.free_of_flat_of_isLocalRing
  haveI hfreeT' : ∀ i, Module.Free 𝓞 (T' i) := fun i => by
    haveI : Module.Projective 𝓞 (T' i) := RingHom.ETQE.projective_quotient_span_one_sub (hfidem i)
    exact Module.free_of_flat_of_isLocalRing
  haveI hnontT' : ∀ i, Nontrivial (T' i) := by
    intro i
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 : 1 - ι (e i) = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp (hfidem i).one_sub
    have h0 : e i = 0 := hι (by rw [map_zero]; simpa using h1)
    exact he1 i (h0 ▸ Ideal.zero_mem _)
  have hmaxE : ∀ i, IsLocalRing.maximalIdeal (E i) = Ideal.span {(p : E i)} := by
    intro i
    apply le_antisymm
    ·
      intro x hx
      obtain ⟨h₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hrep : Ideal.Quotient.mk (Ideal.span {1 - e i}) (h₀ * e i) =
          Ideal.Quotient.mk (Ideal.span {1 - e i}) h₀ :=
        Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton'.mpr ⟨-h₀, by ring⟩)
      rw [← hrep] at hx ⊢

      have hall : ∀ m : MaximalSpectrum H, h₀ * e i ∈ m.asIdeal := by
        intro m
        by_cases hmi : m = i
        · subst hmi
          rw [← hmapmax m] at hx
          have h := Ideal.mem_comap.mpr hx
          rw [hcomap_map m] at h
          exact h
        · exact m.asIdeal.mul_mem_left _ (he2 i m (Ne.symm hmi))

      have hψh : ψ (h₀ * e i) ∈ (⊥ : Ideal (ZMod p ⊗[𝓞] H)).jacobson := by
        rw [Ideal.jacobson, Ideal.mem_sInf]
        rintro N ⟨-, hN⟩
        haveI := hN
        have hcm : (N.comap (ψ : H →+* ZMod p ⊗[𝓞] H)).IsMaximal :=
          Ideal.comap_isMaximal_of_surjective _ hψsurj
        exact Ideal.mem_comap.mp (hall ⟨_, hcm⟩)
      rw [hjac, Ideal.mem_bot, hψ] at hψh
      have hmem := RingHom.ETQE.mem_span_natCast_of_one_tmul_eq_zero p hker hψh
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
      rw [← hy, map_mul, map_natCast]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    ·
      refine IsLocalRing.le_maximalIdeal ?_
      rw [Ne, Ideal.span_singleton_eq_top]
      exact RingHom.ETQE.not_isUnit_natCast p hpJ
  have hETQB : ∀ i, (ιq i).toRingHom.Finite ∧ (ιq i).toRingHom.FaithfullyFlat := fun i =>
    RingHom.finite_and_faithfullyFlat_of_maximalIdeal_eq_span_natCast_of_mem_jacobson p hpJ (E i)
      (hmaxE i) (T' i) (ιq i)

  have hflat' : ∀ i, Module.Flat H (T' i) := fun i => by
    letI : Algebra (E i) (T' i) := (ιq i).toRingHom.toAlgebra
    haveI : IsScalarTower H (E i) (T' i) := IsScalarTower.of_algebraMap_eq fun h => rfl
    haveI : Module.Flat H (E i) := by
      haveI : Module.Projective H (E i) := RingHom.ETQE.projective_quotient_span_one_sub (hidem i)
      infer_instance
    haveI : Module.FaithfullyFlat (E i) (T' i) := (hETQB i).2
    exact Module.Flat.trans H (E i) (T' i)
  have hcf : CompleteOrthogonalIdempotents fun i => ι (e i) := hce.map ι.toRingHom
  let piT : T →+* (∀ i, T' i) := RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span {1 - ι (e i)})
  have hbij : Function.Bijective piT := hcf.bijective_pi
  let piTₗ : T →ₗ[H] (∀ i, T' i) :=
    { toFun := piT
      map_add' := fun x y => map_add piT x y
      map_smul' := fun h t => by
        funext i
        change Ideal.Quotient.mk (Ideal.span {1 - ι (e i)}) (h • t) =
          h • Ideal.Quotient.mk (Ideal.span {1 - ι (e i)}) t
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  let eT : T ≃ₗ[H] (∀ i, T' i) := LinearEquiv.ofBijective piTₗ hbij
  haveI : Module.Flat H (∀ i, T' i) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype H (MaximalSpectrum H) T').symm
  haveI hflatT : Module.Flat H T := Module.Flat.of_linearEquiv eT

  refine { submodule_ne_top := ?_ }
  intro 𝔫 h𝔫 htop
  let m : MaximalSpectrum H := ⟨𝔫, h𝔫⟩
  letI : Algebra (E m) (T' m) := (ιq m).toRingHom.toAlgebra
  haveI : IsScalarTower H (E m) (T' m) := IsScalarTower.of_algebraMap_eq fun h => rfl
  have hff : Module.FaithfullyFlat (E m) (T' m) := (hETQB m).2
  have h𝔫E : ∀ h ∈ 𝔫, algebraMap H (E m) h ∈ IsLocalRing.maximalIdeal (E m) := by
    intro h hh
    rw [← hmapmax m]
    exact Ideal.mem_map_of_mem _ hh
  let π : T →ₗ[H] T' m := (Ideal.Quotient.mkₐ H (Ideal.span {1 - ι (e m)})).toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective H _
  have h1 : (𝔫 • ⊤ : Submodule H (T' m)) = ⊤ := by
    have h := congrArg (Submodule.map π) htop
    rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hπ] at h
  have h2 : (𝔫 • ⊤ : Submodule H (T' m)) ≤
      ((IsLocalRing.maximalIdeal (E m)) • ⊤ : Submodule (E m) (T' m)).restrictScalars H := by
    refine Submodule.smul_le.mpr fun h hh t _ => ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul (E m) h t]
    exact Submodule.smul_mem_smul (h𝔫E h hh) Submodule.mem_top
  apply hff.submodule_ne_top (IsLocalRing.maximalIdeal.isMaximal (E m))
  rw [eq_top_iff]
  intro t _
  have ht : t ∈ (𝔫 • ⊤ : Submodule H (T' m)) := by
    rw [h1]
    exact Submodule.mem_top
  exact h2 ht

end S_RingHom_finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp
end P2MW
export P2MW.S_RingHom_finite_and_faithfullyFlat_of_isReduced_baseChange_of_injective_zmodp (solution)
