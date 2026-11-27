-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SubQuotient_proof_e6af52f4a40d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:06:31.866562+00:00
-- url     : https://prove2.me/submissions/70d9d87e-c9ed-4549-a16e-f3c03f042761

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_join_f492f2ad5885
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagPair_join_61f48e399a76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psum_e0d98b62ae64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SubQuotient
theorem _root_.solution (hF : FlagIndependence.Statement) : SubQuotient.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hmod N r E U V _ _ _ _ _ _ B B' BU BU' BV BV' j π hj hπ
    hjπ hsame hlat w w' x x' f g hfl wU wU' xU xU' fU gU hflU wV wV' xV xV' fV gV hflV k Gs GsU GsV
    hGs hGsU hGsV Q hQ

  have hrN : r ≤ N := by
    have : FiniteDimensional Ω E := Module.Finite.of_basis w
    have h1 := Module.finrank_eq_card_basis wU
    have h2 := Module.finrank_eq_card_basis w
    have h3 := LinearMap.finrank_le_finrank_of_injective hj
    simp only [Fintype.card_fin] at h1 h2
    omega

  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.mpr hπ)
  have hπs : ∀ v, π (s v) = v := fun v => LinearMap.congr_fun hs v
  have hπj : ∀ u, π (j u) = 0 := fun u =>
    LinearMap.mem_ker.1 (hjπ ▸ LinearMap.mem_range_self j u)
  have hbij : Function.Bijective (LinearMap.coprod j s) := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ h
      simp only [LinearMap.coprod_apply] at h
      have hv : v = v' := by simpa [hπs, hπj] using congrArg π h
      subst hv
      have hu : u = u' := hj (add_right_cancel h)
      rw [hu]
    · intro z
      have hz : z - s (π z) ∈ LinearMap.range j := by
        rw [hjπ, LinearMap.mem_ker, map_sub, hπs, sub_self]
      obtain ⟨u, hu⟩ := hz
      exact ⟨(u, π z), by simp [LinearMap.coprod_apply, hu]⟩
  set φ : (U × V) ≃ₗ[Ω] E := LinearEquiv.ofBijective _ hbij with hφdef
  have hφ : ∀ p : U × V, φ p = j p.1 + s p.2 := fun p => rfl
  have hφu : ∀ u, φ (u, 0) = j u := fun u => by simp [hφ]
  have hφπ : ∀ z, (φ.symm z).2 = π z := fun z => by
    conv_rhs => rw [← φ.apply_symm_apply z, hφ]
    simp [hπs, hπj]

  have hN : r + (N - r) = N := by omega
  set e : Fin r ⊕ Fin (N - r) ≃ Fin N := finSumFinEquiv.trans (finCongr hN) with hedef
  have he : ∀ t, ((e t : Fin N) : ℕ) =
      Sum.elim (fun a : Fin r => (a : ℕ)) (fun b : Fin (N - r) => r + b) t := by
    intro t
    rcases t with a | b <;> simp [hedef]

  have hU : ∀ c, segreVec y c ≠ 0 → ∀ u,
      (u ∈ BU.lat c ↔ φ (u, 0) ∈ B.lat c) ∧ (u ∈ BU'.lat c ↔ φ (u, 0) ∈ B'.lat c) := by
    intro c hc u
    rw [hφu]
    exact ⟨(hlat c hc).1 u, (hlat c hc).2.1 u⟩
  have hV : ∀ c, segreVec y c ≠ 0 → ∀ q,
      (q ∈ BV.lat c ↔ ∃ z ∈ B.lat c, (φ.symm z).2 = q) ∧
        (q ∈ BV'.lat c ↔ ∃ z ∈ B'.lat c, (φ.symm z).2 = q) := by
    intro c hc q
    simp only [hφπ]
    exact ⟨(hlat c hc).2.2.1 q, (hlat c hc).2.2.2 q⟩
  have hsU : SameGenericFibre ϖ BU BU' := by
    intro c hc
    obtain ⟨h1, h2⟩ := hsame c hc
    obtain ⟨hu, hu', -, -⟩ := hlat c hc
    refine ⟨fun u hu0 => ?_, fun u hu0 => ?_⟩
    · obtain ⟨n, hn⟩ := h1 (j u) ((hu u).1 hu0)
      exact ⟨n, (hu' _).2 (by rwa [map_smul])⟩
    · obtain ⟨n, hn⟩ := h2 (j u) ((hu' u).1 hu0)
      exact ⟨n, (hu _).2 (by rwa [map_smul])⟩
  have hsV : SameGenericFibre ϖ BV BV' := by
    intro c hc
    obtain ⟨h1, h2⟩ := hsame c hc
    obtain ⟨-, -, hv, hv'⟩ := hlat c hc
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨z, hz, rfl⟩ := (hv q).1 hq
      obtain ⟨n, hn⟩ := h1 z hz
      exact ⟨n, (hv' _).2 ⟨_, hn, map_smul π _ z⟩⟩
    · obtain ⟨z, hz, rfl⟩ := (hv' q).1 hq
      obtain ⟨n, hn⟩ := h2 z hz
      exact ⟨n, (hv _).2 ⟨_, hn, map_smul π _ z⟩⟩

  have hpc := isFlagPair_join ϖ y B B' BU BU' BV BV' φ e he hU hV hflU hflV
  have hE := hF O ϖ hϖ Ω K ι y d hmod N E B B' hsame w w' _ _ x x' _ _ f g _ _ hfl hpc k
    (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric (Fin N) ℤ k) Gs _ hGs
    (isPairExpansion_psum N k) Q hQ
  have hEU := hF O ϖ hϖ Ω K ι y d hmod r U BU BU' hsU wU wU' wU wU' xU xU' xU xU' fU gU fU gU
    hflU hflU k (psum (Fin r) ℤ k) (isHomogeneous_psum r k) (psum_isSymmetric (Fin r) ℤ k) GsU _ hGsU
    (isPairExpansion_psum r k) Q hQ
  have hEV := hF O ϖ hϖ Ω K ι y d hmod (N - r) V BV BV' hsV wV wV' wV wV' xV xV' xV xV' fV gV fV gV
    hflV hflV k (psum (Fin (N - r)) ℤ k) (isHomogeneous_psum (N - r) k) (psum_isSymmetric (Fin (N - r)) ℤ k) GsV _
    hGsV (isPairExpansion_psum (N - r) k) Q hQ
  rw [hE, pairNum_join, hEU, hEV]
end SubQuotient
end GroundTheory.Heights₂.Heights.NumbersDVR
