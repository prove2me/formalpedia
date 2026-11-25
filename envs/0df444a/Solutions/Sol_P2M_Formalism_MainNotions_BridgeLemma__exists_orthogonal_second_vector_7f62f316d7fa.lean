-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__exists_orthogonal_second_vector_7f62f316d7fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:33.005591+00:00
-- url     : https://prove2.me/submissions/78ecb0d2-198c-4607-beef-68f311dccecc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ExistsSmallMemFractionalIdeal
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__exists_small_mem_fractional_ideal_90c2b6906406
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_self_orthCompanion_423800da9f53
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_eq_zero_bc0ab590ad79
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__lagrange_identity_orthCompanion_f9c10244c23d
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_self_ne_zero_of_orthonormal_5dc73cdd2eeb
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__star_mem_integers_6f5fb9ce5b0a
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_orthCompanion_symm_be982e5d4152

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L 2)
    (M : Submodule (𝓞 K) V) (hlat : Submodule.IsLattice K M) (hint : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (huni : Formalism.HermitianLatticesTheory.dual h M = M) (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) :
    ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K := by
  obtain ⟨e, -, hspan, -, ho⟩ := hL
  have : IsTotallyComplex K := hK.1
  have hcm := hK.2.1
  set y0 := orthCompanion h e x with hy0
  have hα : h x x ≠ 0 := inner_self_ne_zero_of_orthonormal h e hcm hspan ho x hx0
  have hy0y0 : h y0 y0 = h x x := inner_self_orthCompanion h e hspan ho x
  have hy0ne : y0 ≠ 0 := by
    intro h0
    apply hα
    rw [← hy0y0, h0]
    simp
  have hI : ∀ u ∈ M, ∀ v ∈ M, h u v ∈ Set.range (algebraMap (𝓞 K) K) := fun u hu v hv => by
    have := hint u hu v hv
    rwa [Submodule.mem_one] at this
  have hLag : ∀ v ∈ M, ∀ v' ∈ M, h y0 v * star (h y0 v') ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro v hv v' hv'
    rw [hy0, lagrange_identity_orthCompanion h e hspan ho x v v']
    obtain ⟨a, ha⟩ := hI x hx x hx
    obtain ⟨b, hb⟩ := hI v' hv' v hv
    obtain ⟨c, hc⟩ := hI x hx v hv
    obtain ⟨d, hd⟩ := hI v' hv' x hx
    exact ⟨a * b - c * d, by rw [map_sub, map_mul, map_mul, ha, hb, hc, hd]⟩
  suffices hb : ∃ b : K, b ≠ 0 ∧ (∀ v ∈ M, b * star (h y0 v) ∈ Set.range (algebraMap (𝓞 K) K)) ∧
      ∀ φ : K →+* ℂ, ‖φ b‖ ^ 2 ≤ rootDiscriminant K by
    obtain ⟨b, hb0, hbM, hbφ⟩ := hb
    refine ⟨b • y0, ?_, smul_ne_zero hb0 hy0ne, ?_, ?_⟩
    · rw [← huni]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
      intro v hv
      rw [Submodule.mem_one]
      have h1 : h v (b • y0) = b * star (h y0 v) := by
        rw [map_smul, smul_eq_mul, hy0, inner_orthCompanion_symm h e hspan ho x v]
      obtain ⟨c, hc⟩ := hbM v hv
      exact ⟨c, by rw [hc]; exact h1.symm⟩
    · rw [map_smul, hy0, inner_orthCompanion_eq_zero h e hspan ho x, smul_zero]
    · intro φ
      have h1 : h (b • y0) (b • y0) = star b * (b * h x x) := by
        have h2 : h (b • y0) (b • y0) = star b * (b * h y0 y0) := by
          simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
          ring
        rw [h2, hy0y0]
      rw [h1, map_mul, map_mul, hcm, norm_mul, norm_mul, RCLike.norm_conj]
      calc ‖φ b‖ * (‖φ b‖ * ‖φ (h x x)‖) = ‖φ (h x x)‖ * ‖φ b‖ ^ 2 := by ring
        _ ≤ ‖φ (h x x)‖ * rootDiscriminant K := mul_le_mul_of_nonneg_left (hbφ φ) (norm_nonneg _)
  let cc : Submodule (𝓞 K) K := M.map ((h y0).restrictScalars (𝓞 K))
  have hfg : cc.FG := hlat.fg.map _
  let ccF : FractionalIdeal (𝓞 K)⁰ K := ⟨cc, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ c, c ∈ ccF ↔ ∃ v ∈ M, h y0 v = c := by
    intro c
    change c ∈ cc ↔ _
    simp only [cc, Submodule.mem_map, LinearMap.restrictScalars_apply]
  have hne : ccF ≠ 0 := by
    intro h0
    have hz : ∀ v ∈ M, h y0 v = 0 := fun v hv => by
      have h1 : h y0 v ∈ ccF := (hmem _).2 ⟨v, hv, rfl⟩
      rw [h0] at h1
      exact (FractionalIdeal.mem_zero_iff _).1 h1
    have hy : y0 ∈ Submodule.span K (M : Set V) := hlat.span_eq_top ▸ Submodule.mem_top
    have hle : Submodule.span K (M : Set V) ≤ LinearMap.ker (h y0) :=
      Submodule.span_le.2 fun v hv => LinearMap.mem_ker.2 (hz v hv)
    exact hα (hy0y0 ▸ LinearMap.mem_ker.1 (hle hy))
  have hprod : FractionalIdeal.absNorm ccF * FractionalIdeal.absNorm ccF⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  by_cases hc : FractionalIdeal.absNorm ccF ≤ 1
  · obtain ⟨a, ha, ha0, hw⟩ := exists_small_mem_fractional_ideal K (Units.mk0 ccF hne) hc
    obtain ⟨v', hv', rfl⟩ := (hmem a).1 ha
    exact ⟨h y0 v', ha0, fun v hv => hLag v' hv' v hv, fun φ => by
      rw [← InfinitePlace.apply]; exact hw _⟩
  · have hc' : FractionalIdeal.absNorm ccF⁻¹ ≤ 1 := by
      by_contra hlt
      rw [not_le] at hlt hc
      nlinarith
    obtain ⟨a, ha, ha0, hw⟩ := exists_small_mem_fractional_ideal K (Units.mk0 ccF hne)⁻¹ (by simpa using hc')
    have ha' : a ∈ ccF⁻¹ := by simpa using ha
    rw [FractionalIdeal.mem_inv_iff hne] at ha'
    refine ⟨star a, star_ne_zero.2 ha0, fun v hv => ?_, fun φ => ?_⟩
    · have h1 := ha' (h y0 v) ((hmem _).2 ⟨v, hv, rfl⟩)
      rw [FractionalIdeal.mem_one_iff] at h1
      rw [← star_mul']
      exact star_mem_integers h1
    · rw [hcm, RCLike.norm_conj, ← InfinitePlace.apply]
      exact hw _
end Formalism.MainNotions.BridgeLemma₂
