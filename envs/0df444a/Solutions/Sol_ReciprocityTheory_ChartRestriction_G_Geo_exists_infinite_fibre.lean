-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_infinite_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:07.73251+00:00
-- url     : https://prove2.me/submissions/b197d7b9-ac91-4a57-a973-dcdcd8df90f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eventually_surjective_clm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Set Filter Topology Module
variable {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {W : Set (Fin e → ℂ)} (hW : IsOpen W) (hne : W.Nonempty)
    {Q : (Fin e → ℂ) → (Fin e → ℂ)} (hQ : AnalyticOnNhd ℂ Q W)
    (hdet : ∀ u ∈ W, LinearMap.det (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) :
    ∃ y, (W ∩ Q ⁻¹' {y}).Infinite := by
  classical
  set rk : (Fin e → ℂ) → ℕ := fun u =>
    finrank ℂ (LinearMap.range (fderiv ℂ Q u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) with hrk
  have hbdd : BddAbove (rk '' W) := ⟨e, by
    rintro _ ⟨u, -, rfl⟩
    exact (Submodule.finrank_le _).trans (le_of_eq (finrank_fin_fun ℂ))⟩
  have hmax : ∀ u ∈ W, rk u ≤ sSup (rk '' W) := fun u hu => le_csSup hbdd ⟨u, hu, rfl⟩
  obtain ⟨u0, hu0, hru0⟩ := Nat.sSup_mem (hne.image rk) hbdd
  generalize hrdef : sSup (rk '' W) = r at hru0 hmax
  set L0 : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) := fderiv ℂ Q u0
  set R0 := LinearMap.range (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
  have hR0 : finrank ℂ R0 = r := hru0
  have hr_lt : r < e := by
    by_contra hge
    have hre : finrank ℂ R0 = finrank ℂ (Fin e → ℂ) := by
      rw [hR0, finrank_fin_fun]
      exact le_antisymm (hru0 ▸ (Submodule.finrank_le _).trans (le_of_eq (finrank_fin_fun ℂ)))
        (not_lt.mp hge)
    have htop : R0 = ⊤ := Submodule.eq_top_of_finrank_eq hre
    have hsurj : Function.Surjective (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
      LinearMap.range_eq_top.mp htop
    have hbij : Function.Bijective (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) :=
      ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩
    have hu : IsUnit (L0 : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := (Module.End.isUnit_iff _).mpr hbij
    exact ((LinearMap.isUnit_iff_isUnit_det _).mp hu).ne_zero (hdet u0 hu0)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl R0
  set PL : (Fin e → ℂ) →L[ℂ] R0 := LinearMap.toContinuousLinearMap (R0.projectionOnto C hC)
  have hPL : ∀ x : R0, PL x = x := fun x => Submodule.projectionOnto_apply_left hC x
  set Df0 : (Fin e → ℂ) →L[ℂ] R0 := PL.comp L0
  have hDf0 : Function.Surjective Df0 := by
    intro w
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp w.2
    refine ⟨v, ?_⟩
    show PL (L0 v) = w
    rw [show L0 v = (w : Fin e → ℂ) from hv]
    exact hPL w
  set K0 := LinearMap.ker (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0)
  have hK0 : finrank ℂ K0 = e - r := by
    show finrank ℂ (LinearMap.ker (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0)) = e - r
    have := LinearMap.finrank_range_add_finrank_ker (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0)
    rw [LinearMap.range_eq_top.mpr hDf0, finrank_top, hR0, finrank_fin_fun] at this
    omega
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl K0
  set gL : (Fin e → ℂ) →L[ℂ] K0 := LinearMap.toContinuousLinearMap (K0.projectionOnto C' hC')
  have hgL : ∀ x : K0, gL x = x := fun x => Submodule.projectionOnto_apply_left hC' x
  set Φl : (Fin e → ℂ) →ₗ[ℂ] R0 × K0 :=
    LinearMap.prod (Df0 : (Fin e → ℂ) →ₗ[ℂ] R0) (gL : (Fin e → ℂ) →ₗ[ℂ] K0)
  have hinj : Function.Injective Φl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : Df0 v = 0 := congrArg Prod.fst hv
    have h2 : gL v = 0 := congrArg Prod.snd hv
    have hvK : v ∈ K0 := h1
    have := hgL ⟨v, hvK⟩
    rw [h2] at this
    exact (congrArg Subtype.val this).symm
  have hdim : finrank ℂ (Fin e → ℂ) = finrank ℂ (R0 × K0) := by
    rw [finrank_prod, finrank_fin_fun, hR0, hK0]; omega
  have hbij : Function.Bijective Φl :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  set Φ' : (Fin e → ℂ) ≃L[ℂ] R0 × K0 := (LinearEquiv.ofBijective Φl hbij).toContinuousLinearEquiv
  have hΦ'c : (Φ' : (Fin e → ℂ) →L[ℂ] R0 × K0) = Df0.prod gL := by ext1 v; rfl
  set Φ : (Fin e → ℂ) → R0 × K0 := fun u => (PL (Q u), gL u) with hΦdef
  have hQa0 := hQ u0 hu0
  have hΦd : ∀ u ∈ W, HasFDerivAt Φ ((PL.comp (fderiv ℂ Q u)).prod gL) u := fun u hu =>
    (PL.hasFDerivAt.comp u (hQ u hu).differentiableAt.hasFDerivAt).prodMk gL.hasFDerivAt
  have hΦa : ∀ u ∈ W, AnalyticAt ℂ Φ u := fun u hu =>
    ((PL.analyticAt _).comp (hQ u hu)).prod (gL.analyticAt u)
  have hstrict : HasStrictFDerivAt Φ (Φ' : (Fin e → ℂ) →L[ℂ] R0 × K0) u0 := by
    rw [hΦ'c]
    have := (hΦa u0 hu0).hasStrictFDerivAt
    rwa [(hΦd u0 hu0).fderiv] at this
  set H := hstrict.toOpenPartialHomeomorph Φ
  have hHc : (H : (Fin e → ℂ) → R0 × K0) = Φ := hstrict.toOpenPartialHomeomorph_coe
  have hus : u0 ∈ H.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hpt : Φ u0 ∈ H.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hsym0 : H.symm (Φ u0) = u0 := by have := H.left_inv hus; rwa [hHc] at this
  have hsa : AnalyticAt ℂ H.symm (Φ u0) := by
    refine H.analyticAt_symm (i := Φ') hpt ?_ ?_
    · rw [hsym0, hHc]; exact hΦa u0 hu0
    · rw [hsym0, hHc, (hΦd u0 hu0).fderiv, hΦ'c]
  have hA : ContinuousAt (fun u => PL.comp (fderiv ℂ Q u)) u0 :=
    continuousAt_const.clm_comp hQa0.fderiv.continuousAt
  have hev_u : ∀ᶠ u in 𝓝 u0, u ∈ W ∧ Function.Surjective (PL.comp (fderiv ℂ Q u)) :=
    (Filter.eventually_of_mem (hW.mem_nhds hu0) fun u hu => hu).and (eventually_surjective_clm hA hDf0)
  have hev : ∀ᶠ p in 𝓝 (Φ u0), p ∈ H.target ∧ AnalyticAt ℂ H.symm p ∧ H.symm p ∈ W ∧
      Function.Surjective (PL.comp (fderiv ℂ Q (H.symm p))) := by
    have h1 : ∀ᶠ p in 𝓝 (Φ u0), H.symm p ∈ W ∧
        Function.Surjective (PL.comp (fderiv ℂ Q (H.symm p))) :=
      (H.continuousAt_symm hpt).eventually (by rw [hsym0]; exact hev_u)
    filter_upwards [H.open_target.mem_nhds hpt, hsa.eventually_analyticAt, h1] with p h2 h3 h4
    exact ⟨h2, h3, h4⟩
  have hkey : ∀ p, p ∈ H.target → AnalyticAt ℂ H.symm p → H.symm p ∈ W →
      Function.Surjective (PL.comp (fderiv ℂ Q (H.symm p))) → ∀ κ : K0,
      fderiv ℂ (Q ∘ H.symm) p (0, κ) = 0 := by
    intro p hp han hW' hs κ
    have hcomp : HasFDerivAt (Φ ∘ H.symm)
        (((PL.comp (fderiv ℂ Q (H.symm p))).prod gL).comp (fderiv ℂ H.symm p)) p :=
      (hΦd _ hW').comp p han.differentiableAt.hasFDerivAt
    have hid : HasFDerivAt (Φ ∘ H.symm) (ContinuousLinearMap.id ℂ (R0 × K0)) p := by
      refine (hasFDerivAt_id p).congr_of_eventuallyEq ?_
      filter_upwards [H.open_target.mem_nhds hp] with p' hp'
      show Φ (H.symm p') = p'
      rw [← hHc]; exact H.right_inv hp'
    have heq := hcomp.unique hid
    have hw := congrArg (fun T => T (0, κ)) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply] at hw
    have hw1 : PL (fderiv ℂ Q (H.symm p) (fderiv ℂ H.symm p (0, κ))) = 0 := congrArg Prod.fst hw
    have hker : LinearMap.ker (fderiv ℂ Q (H.symm p) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
        LinearMap.ker ((PL.comp (fderiv ℂ Q (H.symm p))) : (Fin e → ℂ) →ₗ[ℂ] R0) := by
      apply Submodule.eq_of_le_of_finrank_le
      · intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        show PL (fderiv ℂ Q (H.symm p) v) = 0
        rw [show (fderiv ℂ Q (H.symm p)) v = 0 from hv, map_zero]
      · have h1 := LinearMap.finrank_range_add_finrank_ker
          ((PL.comp (fderiv ℂ Q (H.symm p))) : (Fin e → ℂ) →ₗ[ℂ] R0)
        have h2 := LinearMap.finrank_range_add_finrank_ker
          (fderiv ℂ Q (H.symm p) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
        rw [LinearMap.range_eq_top.mpr hs, finrank_top, hR0] at h1
        have h3 : finrank ℂ (LinearMap.range (fderiv ℂ Q (H.symm p) :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) ≤ r := hmax _ hW'
        omega
    have hwker : fderiv ℂ H.symm p (0, κ) ∈
        LinearMap.ker (fderiv ℂ Q (H.symm p) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
      rw [hker]; exact hw1
    rw [fderiv_comp p (hQ _ hW').differentiableAt han.differentiableAt]
    exact hwker
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set c0 := Φ u0
  set ι : K0 → R0 × K0 := fun k => (c0.1, c0.2 + k) with hιdef
  have hιball : ∀ k ∈ Metric.ball (0 : K0) ε, ι k ∈ Metric.ball c0 ε := by
    intro k hk
    have h0 : ι k - c0 = (0, k) := by
      simp only [hιdef]
      ext <;> simp
    rw [Metric.mem_ball, dist_eq_norm, h0, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg k)]
    rwa [Metric.mem_ball, dist_zero_right] at hk
  have hιd : ∀ k, HasFDerivAt ι (ContinuousLinearMap.inr ℂ R0 K0) k := fun k =>
    (hasFDerivAt_const c0.1 k).prodMk ((hasFDerivAt_id k).const_add c0.2)
  have hGd : ∀ k ∈ Metric.ball (0 : K0) ε, HasFDerivAt (fun k => Q (H.symm (ι k))) (0 : K0 →L[ℂ] (Fin e → ℂ)) k := by
    intro k hk
    obtain ⟨hp, han, hW', hs⟩ := hball _ (hιball k hk)
    have hG : HasFDerivAt (Q ∘ H.symm) (fderiv ℂ (Q ∘ H.symm) (ι k)) (ι k) :=
      ((hQ _ hW').differentiableAt.comp _ han.differentiableAt).hasFDerivAt
    have := hG.comp k (hιd k)
    have h0 : (fderiv ℂ (Q ∘ H.symm) (ι k)).comp (ContinuousLinearMap.inr ℂ R0 K0) = 0 := by
      ext1 κ
      simp [hkey _ hp han hW' hs κ]
    rw [h0] at this
    exact this
  have hconst : ∀ k ∈ Metric.ball (0 : K0) ε, Q (H.symm (ι k)) = Q (H.symm (ι 0)) := by
    intro k hk
    exact (convex_ball (0 : K0) ε).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
      (fun k' hk' => (hGd k' hk').differentiableAt.differentiableWithinAt)
      (fun k' hk' => by
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hk']; exact (hGd k' hk').fderiv)
      hk (Metric.mem_ball_self hε)
  have hι0 : ι 0 = c0 := by simp [hιdef]
  have : Nontrivial K0 := Module.nontrivial_of_finrank_pos (by rw [hK0]; omega)
  have hinf : (Metric.ball (0 : K0) ε).Infinite :=
    infinite_of_mem_nhds (0 : K0) (Metric.ball_mem_nhds 0 hε)
  refine ⟨Q u0, (Set.Infinite.image (f := fun k => H.symm (ι k)) ?_ hinf).mono ?_⟩
  · intro k hk k' hk' hkk
    have h1 := (hball _ (hιball k hk)).1
    have h2 := (hball _ (hιball k' hk')).1
    have : ι k = ι k' := H.symm.injOn h1 h2 hkk
    simpa [hιdef] using this
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨(hball _ (hιball k hk)).2.2.1, ?_⟩
    show Q (H.symm (ι k)) = Q u0
    rw [hconst k hk, hι0, hsym0]
end ReciprocityTheory.ChartRestriction.G.Geo
