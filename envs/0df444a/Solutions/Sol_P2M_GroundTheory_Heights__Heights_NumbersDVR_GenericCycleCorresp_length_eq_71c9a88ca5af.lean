-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericCycleCorresp_length_eq_71c9a88ca5af
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:49.625023+00:00
-- url     : https://prove2.me/submissions/de1a2576-fad1-498b-90f4-935a00d2a876

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericCycleCorresp

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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (M : Submonoid S)
  [IsLocalization M T]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
theorem _root_.solution (J W : Ideal S) [W.IsPrime] (hW : Disjoint (M : Set S) W)
    [(W.map (algebraMap S T)).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap S T)))
        (LocalizedModule (W.map (algebraMap S T)).primeCompl (T ⧸ J.map (algebraMap S T))) := by
  set W' := W.map (algebraMap S T)
  set J' := J.map (algebraMap S T)
  have hcomap : W'.comap (algebraMap S T) = W :=
    IsLocalization.under_map_of_isPrime_disjoint M T ‹_› hW
  have hnot : ∀ x : S, x ∉ W → algebraMap S T x ∉ W' := fun x hx h =>
    hx (hcomap ▸ Ideal.mem_comap.mpr h)
  haveI : IsLocalization.AtPrime (Localization.AtPrime W') W := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime W') W'
    unfold IsLocalization.AtPrime at this ⊢
    convert this using 2
    exact hcomap.symm
  let σ : Localization.AtPrime W ≃ₐ[S] Localization.AtPrime W' :=
    IsLocalization.algEquiv W.primeCompl _ _
  let N := LocalizedModule W'.primeCompl (T ⧸ J')
  letI iAN : Module (Localization.AtPrime W) N :=
    Module.compHom N (σ : Localization.AtPrime W →+* Localization.AtPrime W')
  letI iAB : Algebra (Localization.AtPrime W) (Localization.AtPrime W') :=
    (σ : Localization.AtPrime W →+* Localization.AtPrime W').toAlgebra
  haveI : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime W') N :=
    ⟨fun a b n => mul_smul (σ a) b n⟩
  haveI : IsScalarTower S (Localization.AtPrime W) N := by
    refine ⟨fun s a n => ?_⟩
    calc (s • a) • n = σ (s • a) • n := rfl
      _ = (algebraMap S (Localization.AtPrime W') s * σ a) • n := by
        rw [map_smul, Algebra.smul_def]
      _ = algebraMap S (Localization.AtPrime W') s • (σ a • n) := mul_smul _ _ _
      _ = algebraMap T (Localization.AtPrime W') (algebraMap S T s) • (σ a • n) := by
        rw [← IsScalarTower.algebraMap_apply]
      _ = algebraMap S T s • (σ a • n) := algebraMap_smul _ _ _
      _ = s • (σ a • n) := algebraMap_smul _ _ _
      _ = s • (a • n) := rfl
  let q : (S ⧸ J) →ₐ[S] (T ⧸ J') :=
    Ideal.quotientMapₐ J' (Algebra.ofId S T)
      (fun x hx => Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))
  let g : (S ⧸ J) →ₗ[S] N :=
    { toFun := fun x => LocalizedModule.mk (q x) 1
      map_add' := fun x y => by
        rw [map_add, LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
      map_smul' := fun s x => by
        simp only [RingHom.id_apply]
        rw [LocalizedModule.smul'_mk, map_smul] }
  have hm : ∀ m : M, (m : S) ∉ W := fun m hm => Set.disjoint_left.mp hW m.2 hm
  have hden : ∀ (t : T) (b : S) (m' : M), t ∉ W' → t * algebraMap S T m' = algebraMap S T b →
      b ∉ W := by
    intro t b m' ht hb hbW
    have : t * algebraMap S T m' ∈ W' := hb ▸ Ideal.mem_map_of_mem _ hbW
    rcases (inferInstance : W'.IsPrime).mem_or_mem this with h | h
    · exact ht h
    · exact hm m' (hcomap ▸ Ideal.mem_comap.mpr h)
  haveI hg : IsLocalizedModule W.primeCompl g := by
    constructor
    · intro s
      rw [Module.End.isUnit_iff]
      have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap W'.primeCompl (T ⧸ J'))
        (⟨algebraMap S T s, hnot s s.2⟩ : W'.primeCompl)
      rw [Module.End.isUnit_iff] at hu
      convert hu using 1
      funext n
      simp only [Module.algebraMap_end_apply]
      exact (algebraMap_smul T (s : S) n).symm
    · intro n
      induction n using LocalizedModule.induction_on with
      | h y t =>
        obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨⟨a, m⟩, hy⟩ := IsLocalization.surj M y0
        obtain ⟨⟨b, m'⟩, ht⟩ := IsLocalization.surj M (t : T)
        simp only at hy ht
        have hb : b ∉ W := hden t b m' t.2 ht
        refine ⟨⟨Ideal.Quotient.mk J (a * m'), ⟨b * m, W.primeCompl.mul_mem hb (hm m)⟩⟩, ?_⟩
        show (b * m) • LocalizedModule.mk (Ideal.Quotient.mk J' y0) t =
          LocalizedModule.mk (Ideal.Quotient.mk J' (algebraMap S T (a * m'))) 1
        rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq, ← algebraMap_smul T (b * m)]
        refine ⟨1, ?_⟩
        rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
        change Ideal.Quotient.mk J' (algebraMap S T (b * m) * y0) =
          Ideal.Quotient.mk J' ((t : T) * algebraMap S T (a * m'))
        congr 1
        simp only [map_mul]
        linear_combination (algebraMap S T b) * hy - (algebraMap S T a) * ht
    · intro x₁ x₂ h
      obtain ⟨x₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
      obtain ⟨x₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
      change LocalizedModule.mk (Ideal.Quotient.mk J' (algebraMap S T x₁)) 1 =
        LocalizedModule.mk (Ideal.Quotient.mk J' (algebraMap S T x₂)) 1 at h
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h
      rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def] at hu
      change Ideal.Quotient.mk J' ((u : T) * algebraMap S T x₁) =
        Ideal.Quotient.mk J' ((u : T) * algebraMap S T x₂) at hu
      rw [Ideal.Quotient.eq] at hu
      obtain ⟨⟨c, m''⟩, hc⟩ := IsLocalization.surj M (u : T)
      simp only at hc
      have hcW : c ∉ W := hden u c m'' u.2 hc
      have hmem : algebraMap S T (c * (x₁ - x₂)) ∈ J' := by
        have := J'.mul_mem_left (algebraMap S T m'') hu
        convert this using 1
        rw [map_mul, map_sub, ← hc]
        ring
      obtain ⟨m3, hm3, hJ⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := M) (S := T) J _).mp hmem
      refine ⟨⟨m3 * c, W.primeCompl.mul_mem (hm ⟨m3, hm3⟩) hcW⟩, ?_⟩
      rw [Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq]
      convert hJ using 1
      ring
  let e : LocalizedModule W.primeCompl (S ⧸ J) ≃ₗ[S] N := IsLocalizedModule.iso W.primeCompl g
  rw [(e.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq]
  exact Module.length_eq_of_surjective σ.surjective
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericCycleCorresp
