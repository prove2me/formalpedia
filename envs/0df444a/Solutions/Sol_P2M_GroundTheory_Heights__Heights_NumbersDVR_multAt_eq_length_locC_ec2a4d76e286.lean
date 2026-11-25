-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_eq_length_locC_ec2a4d76e286
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:33.392931+00:00
-- url     : https://prove2.me/submissions/38d8e3ae-e5cd-4bc5-93b2-66bc18b62356

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_quotient_of_surjective_637be7b48f99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_quotient_eq_77bc8143a94c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial HomLocLaurent
noncomputable section
universe u
set_option linter.style.haveILetI false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
  {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (hPW : P ≤ W) (x : MRing ι R) :
    multAt (P ⊔ Ideal.span {x}) W =
      Module.length (locC hPW) (locC hPW ⧸ Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  set J := P ⊔ Ideal.span {x}
  set I : Ideal (locC hPW) := Ideal.span {algQC hPW (Ideal.Quotient.mk P x)}
  set θ : MRing ι R →+* locC hPW := (algQC hPW).comp (Ideal.Quotient.mk P) with hθ
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hunit : ∀ {s : MRing ι R}, s ∉ W → IsUnit (θ s) := fun hs =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h)
  obtain ⟨θW, hθWdef⟩ : ∃ φ : Localization.AtPrime W →+* locC hPW,
      φ = IsLocalization.lift (M := W.primeCompl) (g := θ) fun s => hunit s.2 := ⟨_, rfl⟩
  have hθW : ∀ f, θW (algebraMap (MRing ι R) (Localization.AtPrime W) f) = θ f := fun f => by
    rw [hθWdef]
    exact IsLocalization.lift_eq _ _

  have hval : ∀ (a s : MRing ι R) (hs : s ∈ W.primeCompl),
      (θW (IsLocalization.mk' (Localization.AtPrime W) a ⟨s, hs⟩) : FractionRing (MRing ι R ⧸ P)) *
        fr P s = fr P a := by
    intro a s hs
    have := congrArg θW (IsLocalization.mk'_spec (Localization.AtPrime W) a ⟨s, hs⟩)
    rw [RingHom.map_mul, hθW, hθW] at this
    exact congrArg Subtype.val this
  have hsurj : Function.Surjective θW := by
    rintro ⟨c, a', s', hs', rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsW : s ∉ W := fun h => hs' (Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hsW⟩ : W.primeCompl), Subtype.ext ?_⟩
    have h := hval a s hsW
    change _ = fr P a * (fr P s)⁻¹
    rw [← h, mul_assoc, mul_inv_cancel₀ (hne hsW), mul_one]
  letI : Algebra (Localization.AtPrime W) (locC hPW) := θW.toAlgebra
  let f : Localization.AtPrime W →ₐ[Localization.AtPrime W] (locC hPW ⧸ I) :=
    Algebra.ofId (Localization.AtPrime W) (locC hPW ⧸ I)
  have hf : ∀ y, f y = Ideal.Quotient.mk I (θW y) := fun y => rfl
  have hfs : Function.Surjective f := fun q => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨y, rfl⟩ := hsurj c
    exact ⟨y, hf y⟩
  have hker : RingHom.ker f = J.map (algebraMap (MRing ι R) (Localization.AtPrime W)) := by
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
      obtain ⟨⟨c, b', t', ht', hc⟩, hcy⟩ := hy
      obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl y
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
      have htW : t ∉ W := fun h => ht' (Ideal.mem_map_of_mem _ h)
      have h1 := hval a s hs
      rw [← hcy] at h1
      change c * fr P x * fr P s = fr P a at h1
      rw [hc] at h1
      change fr P b * (fr P t)⁻¹ * fr P x * fr P s = fr P a at h1
      have hat : a * t - b * x * s ∈ P := by
        have h2 : fr P a * fr P t = fr P b * fr P x * fr P s := by
          rw [← h1]
          calc _ = fr P b * fr P x * fr P s * ((fr P t)⁻¹ * fr P t) := by ring
            _ = _ := by rw [inv_mul_cancel₀ (hne htW), mul_one]
        rw [← fr_eq_zero_iff, map_sub, map_mul, map_mul, map_mul, h2, sub_self]
      have hatJ : a * t ∈ J := by
        have : a * t = (a * t - b * x * s) + (b * s) * x := by ring
        rw [this]
        exact J.add_mem (Ideal.mem_sup_left hat)
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      have hst : s * t ∈ W.primeCompl := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs htW
      have heq : IsLocalization.mk' (Localization.AtPrime W) a (⟨s, hs⟩ : W.primeCompl) *
          algebraMap (MRing ι R) (Localization.AtPrime W) (s * t) =
            algebraMap (MRing ι R) (Localization.AtPrime W) (a * t) := by
        rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, map_mul]
      have hu : IsUnit (algebraMap (MRing ι R) (Localization.AtPrime W) (s * t)) :=
        IsLocalization.map_units (Localization.AtPrime W) (⟨s * t, hst⟩ : W.primeCompl)
      rw [← Ideal.mul_unit_mem_iff_mem _ hu, heq]
      exact Ideal.mem_map_of_mem _ hatJ
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker, hf, hθW, Ideal.Quotient.eq_zero_iff_mem]
      have hJ : J ≤ I.comap θ := by
        refine sup_le (fun p hp => ?_) ?_
        · have h0 : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [Ideal.mem_comap, hθ, RingHom.comp_apply, h0, RingHom.map_zero]
          exact zero_mem _
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span rfl
      exact Ideal.mem_comap.mp (hJ hj)
  have hlen := (Ideal.quotientKerAlgEquivOfSurjective hfs).toLinearEquiv.length_eq
  rw [multAt, length_localizedModule_quotient_eq, ← (Submodule.quotEquivOfEq _ _ hker).length_eq, hlen]
  exact length_quotient_of_surjective hsurj I
end GroundTheory.Heights₂.Heights.NumbersDVR
