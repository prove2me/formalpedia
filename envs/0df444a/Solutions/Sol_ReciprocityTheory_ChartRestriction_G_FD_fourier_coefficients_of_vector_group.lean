-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.fourier_coefficients_of_vector_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:00.684831+00:00
-- url     : https://prove2.me/submissions/9e63c1a7-bb11-4e08-b3b8-ba56dc167c0b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCubeIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentVectorGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientsOfVectorGroup
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_herm___020bf96602f4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_exists_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_Zb_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_chiOf_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_chiOf_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_chiOf_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_chiOf_pair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_fac_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_pnorm_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_th_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeIntegral_Ich_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeIntegral_Ich_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeIntegral_Ich_coeff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Bv_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Ich_diff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_Ich_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_psi_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCubeVolume_psi_per
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_descend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_mF_tproj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MeasureTheory FourierCoefficientMatrices FourierCubeVolume FourierCubeIntegral
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (hL1 : UnipotentVectorGroup (E := E)) : FourierCoefficientProperties (E := E) := by
  intro r X u g hiso hg la G hGd hB hper χ
  classical
  obtain ⟨hadd, hH⟩ := hL1 r X u hiso
  have hunit : ∀ b, IsHermFam b → X.IsUnitaryC (X.zmat u b) := fun b hb => (hH b hb).1
  have hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom := fun b hb => (hH b hb).2.2.2.1
  have hex : ∃ ω, X.IsLZBasis g ω := FixedPointImaginarySpan.exists_basis X g hg
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = hex.choose := ⟨_, rfl⟩
  have hω : X.IsLZBasis g ω := hωdef ▸ hex.choose_spec
  have hfz : ∀ ψ x, X.fz u g ψ G x =
      if IsHermFam ψ ∧ X.IsFreqZ g ψ then Ich X u ω G ψ x else 0 := by
    intro ψ x
    unfold Data.fz
    rw [dif_pos hex, ← hωdef]
    rfl
  have hsum : ∀ x ∈ X.dom, Summable (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g ψ G x‖) →
      HasSum (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) (G x) := by
    intro x hx hs
    have hωh := herm_ω hω
    have hli := hω.2.2
    obtain ⟨c, hc⟩ : ∃ c : (Fin (4 * Fintype.card X.Ψ) → ℤ) → X.Ψ → Fin 2 → Fin 2 → ℂ,
        c = fun m => chiOf ω hωh hli rfl fun j => (m j : ℝ) := ⟨_, rfl⟩
    have hcm : ∀ m, c m = chiOf ω hωh hli rfl fun j => (m j : ℝ) := fun m => by rw [hc]
    have hc_inj : Function.Injective c := by
      intro m m' h
      rw [hcm, hcm] at h
      have h' := chiOf_inj ω hωh hli rfl h
      funext j
      exact_mod_cast congrFun h' j
    have hcfreq : ∀ m, IsHermFam (c m) ∧ X.IsFreqZ g (c m) := by
      intro m
      refine ⟨by rw [hcm]; exact chiOf_herm ω hωh hli rfl _, ?_⟩
      intro b hb
      obtain ⟨n, hn, -⟩ := hω.2.1 b hb
      refine ⟨∑ j, n j * m j, ?_⟩
      have hb' : b = ∑ j, ((n j : ℝ) : ℂ) • ω j := by
        rw [hn]
        simp only [Complex.ofReal_intCast]
      show 2 * pr (c m) b = _
      rw [hb', pr_sum, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      have hp : 2 * pr (c m) (ω j) = (m j : ℝ) := by
        rw [hcm]
        exact chiOf_pair ω hωh hli rfl _ j
      calc 2 * ((n j : ℝ) * pr (c m) (ω j)) = (n j : ℝ) * (2 * pr (c m) (ω j)) := by ring
        _ = (n j : ℝ) * (m j : ℝ) := by rw [hp]
    obtain ⟨D, hD⟩ := I2.DimB.descend (fun t => G (X.Zb u (Bv ω t) x))
      (psi_cont hω hdomH hGd hx) (fun n t => psi_per hω hadd hdomH hper hx n t)
    have hcoef : ∀ m, X.fz u g (c m) G x = UnitAddTorus.mFourierCoeff D m := by
      intro m
      rw [hfz, if_pos (hcfreq m)]
      refine Ich_coeff (fun j => ?_) D hD
      show 2 * pr (c m) (ω j) = (m j : ℝ)
      rw [hcm]
      exact chiOf_pair ω hωh hli rfl _ j
    have hsupp : ∀ ψ ∉ Set.range c, X.fz u g ψ G x = 0 := by
      intro ψ hψ
      rw [hfz]
      split_ifs with h
      · exfalso
        apply hψ
        choose k hk using fun j => h.2 (ω j) (hω.1 j)
        refine ⟨k, ?_⟩
        rw [hcm]
        exact (chiOf_eq ω hωh hli rfl h.1 (m := fun j => (k j : ℝ)) hk).symm
      · rfl
    have hsm : Summable (UnitAddTorus.mFourierCoeff D) := by
      refine Summable.of_norm ((hs.comp_injective hc_inj).congr fun m => ?_)
      simp only [Function.comp, hcoef]
    have hG0 : D (I2.DimB.tproj 0) = G x := by
      rw [hD, Bv_zero, Zb_zero]
    have hF := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsm (I2.DimB.tproj 0)
    rw [hG0] at hF
    have hF' : HasSum (UnitAddTorus.mFourierCoeff D) (G x) := by
      simpa [I2.DimB.mF_tproj] using hF
    rw [← hc_inj.hasSum_iff hsupp]
    have hcomp : (fun ψ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g ψ G x) ∘ c =
        UnitAddTorus.mFourierCoeff D := funext fun m => hcoef m
    rw [hcomp]
    exact hF'
  by_cases hχ : IsHermFam χ ∧ X.IsFreqZ g χ
  · have hfe : X.fz u g χ G = Ich X u ω G χ := funext fun x => by rw [hfz, if_pos hχ]
    have hfreq : ∀ j, ∃ k : ℤ, 2 * X.pairR χ (ω j) = k := fun j => hχ.2 (ω j) (hω.1 j)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact Ich_diff hω hdomH hGd χ
    · intro x hx b hb
      rw [hfe]
      exact Ich_rmul la hB hω hdomH χ hx hb
    · intro b hb x hx
      rw [hfe]
      exact Ich_Zb hω hadd hdomH hGd hper hfreq hb hx
    · intro x hx M hM
      rw [pnorm_eq, hfe]
      exact Ich_bound hω hunit la χ x hM
  · have hfe : X.fz u g χ G = fun _ => 0 := funext fun x => by rw [hfz, if_neg hχ]
    have hh0 : IsHermFam (0 : X.Ψ → Fin 2 → Fin 2 → ℂ) := by
      have h := th_herm (0 : X.Ψ → Fin 2 → Fin 2 → ℝ)
      rwa [th_zero] at h
    refine ⟨⟨?_, ?_, ?_⟩, ?_, hsum⟩
    · rw [hfe]
      exact differentiableOn_const 0
    · intro x hx b hb
      rw [hfe]
      simp
    · intro b hb x hx
      rw [hfe]
      simp
    · intro x hx M hM
      have h0 := hM 0 hh0
      rw [Zb_zero, pnorm_eq] at h0
      rw [pnorm_eq, hfe]
      simp only [norm_zero, zero_mul]
      exact (mul_nonneg (norm_nonneg _) (fac_nonneg X la x)).trans h0
end ReciprocityTheory.ChartRestriction.G.FD
