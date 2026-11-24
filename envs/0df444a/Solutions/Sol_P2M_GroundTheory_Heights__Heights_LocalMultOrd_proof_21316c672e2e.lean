-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalMultOrd_proof_21316c672e2e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:45.51191+00:00
-- url     : https://prove2.me/submissions/08f2eac4-9d06-4b6d-8c16-217e11634467

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsLocalMultOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLocalMultOrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LocalMultOrd
theorem _root_.solution : LocalMultOrd.Statement := by
  intro A _ _ I W x _ hW
  set J := I ⊔ Ideal.span {x} with hJ
  have hWp : W.IsPrime := hW.1.1
  have hIW : I ≤ W := le_sup_left.trans hW.1.2
  have hxJ : x ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  set P := W.map (Ideal.Quotient.mk I) with hPdef
  have hcomap : W = P.comap (Ideal.Quotient.mk I) := by
    rw [hPdef, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIW]
  have hcompl : ∀ a : A, a ∉ W → Ideal.Quotient.mk I a ∈ P.primeCompl := fun a ha h =>
    ha (hcomap ▸ h)
  let AW := Localization.AtPrime W
  let BP := Localization.AtPrime P
  let φ : AW →+* BP := Localization.localRingHom W P (Ideal.Quotient.mk I) hcomap
  set x' : BP := algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I x) with hx'
  let C := BP ⧸ Ideal.span {x'}
  let π : AW →+* C := (Ideal.Quotient.mk _).comp φ
  have hφ : ∀ a : A, φ (algebraMap A AW a) = algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I a) :=
    fun a => Localization.localRingHom_to_map _ _ _ _ _
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
    have htW : t ∈ W.primeCompl := fun h => s.2 (ht ▸ Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' AW a ⟨t, htW⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht
  have hπs : Function.Surjective π := Ideal.Quotient.mk_surjective.comp hφs

  have hmax : ∀ Q ∈ (Ideal.span {x'}).minimalPrimes, Q.IsMaximal := by
    intro Q hQ
    have := hQ.1.1
    have hle : W ≤ (Q.comap (algebraMap (A ⧸ I) BP)).comap (Ideal.Quotient.mk I) := by
      refine hW.2 ⟨Ideal.comap_isPrime _ _, sup_le ?_ ?_⟩ ?_
      · intro a ha
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hQ.1.2 (Ideal.mem_span_singleton_self _)
      · intro a ha
        by_contra haW
        exact hQ.1.1.ne_top (Ideal.eq_top_of_isUnit_mem _ ha
          (IsLocalization.map_units BP (⟨_, hcompl a haW⟩ : P.primeCompl)))
    have hm : IsLocalRing.maximalIdeal BP ≤ Q := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro b hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact hle (by rw [hcomap]; exact hb)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) hm]
    infer_instance
  have : Ring.KrullDimLE 0 C :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmax
  have : IsArtinianRing C := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := C)
  have hfin : Module.length C C ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

  let : Algebra AW C := RingHom.toAlgebra (R := AW) (S := C) π
  have hJπ : ∀ y ∈ J.map (algebraMap A AW), (Algebra.ofId AW C) y = 0 := by
    have : J.map (algebraMap A AW) ≤ RingHom.ker π := by
      rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) ?_
      · simp [RingHom.mem_ker, π, hφ, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        simp [RingHom.mem_ker, π, hφ, ← hx']
    exact fun y hy => this hy
  let f : (AW ⧸ J.map (algebraMap A AW)) →ₐ[AW] C := Ideal.Quotient.liftₐ _ (Algebra.ofId AW C) hJπ
  have hf : ∀ y, f (Ideal.Quotient.mk _ y) = π y := fun y => rfl
  let ψ0 : A ⧸ I →+* AW ⧸ J.map (algebraMap A AW) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (algebraMap A AW)) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left ha)))
  have hunit : ∀ s : P.primeCompl, IsUnit (ψ0 s) := by
    intro s
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
    have htW : t ∈ W.primeCompl := fun h => s.2 (ht ▸ Ideal.mem_map_of_mem _ h)
    rw [← ht]
    exact (IsLocalization.map_units AW (⟨t, htW⟩ : W.primeCompl)).map (Ideal.Quotient.mk _)
  let ψ1 : BP →+* AW ⧸ J.map (algebraMap A AW) := IsLocalization.lift hunit
  have hψ1 : ∀ a : A, ψ1 (algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (algebraMap A AW a) := fun a => by
    simp [ψ1, ψ0, IsLocalization.lift_eq]
  let ψ : C →+* AW ⧸ J.map (algebraMap A AW) := Ideal.Quotient.lift _ ψ1 (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, hx', hψ1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hxJ), mul_zero])
  have hψπ : ψ.comp π = Ideal.Quotient.mk _ := by
    apply IsLocalization.ringHom_ext W.primeCompl
    ext a
    change ψ (Ideal.Quotient.mk _ (φ (algebraMap A AW a))) =
      Ideal.Quotient.mk _ (algebraMap A AW a)
    rw [hφ]
    exact hψ1 a
  have hinj : Function.Injective f := by
    intro q₁ q₂ h
    obtain ⟨y₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
    obtain ⟨y₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
    rw [hf, hf] at h
    have e₁ : ψ (π y₁) = _ := RingHom.congr_fun hψπ y₁
    have e₂ : ψ (π y₂) = _ := RingHom.congr_fun hψπ y₂
    exact e₁.symm.trans ((congrArg ψ h).trans e₂)
  have hsurj : Function.Surjective f := fun c => by
    obtain ⟨y, rfl⟩ := hπs c
    exact ⟨_, hf y⟩
  let e := LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩
  have hord : Ring.ord BP x' = Module.length C C :=
    Module.length_eq_of_surjective (S := BP) (R := C) (M := C) Ideal.Quotient.mk_surjective
  have hlen : Module.length AW (AW ⧸ J.map (algebraMap A AW)) = Module.length C C := by
    rw [e.length_eq]
    exact Module.length_eq_of_surjective (S := AW) (R := C) (M := C) hπs
  have hloc : localMult J W = (Module.length AW (AW ⧸ J.map (algebraMap A AW))).toNat := by
    unfold localMult
    rw [dif_pos hWp]
  rw [hloc, hlen, hord]
  exact ENat.natCast_toNat hfin
end LocalMultOrd
end GroundTheory.Heights₂.Heights
