-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodPointBranch_exists_branch_4c088d9197c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:14:25.050527+00:00
-- url     : https://prove2.me/submissions/0240060d-92a2-4af0-ba80-9dff05812ecb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointBranchExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_analyticOnNhd_of_differentiableOn_bf6eac09d233
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consCLM_apply_1d763c4552d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_apply_zero_f8796c3b106b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_mem_ball_d53da24c5d41
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_consZero_tail_d132be48cbd8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_slice_chart_fc0789027df7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodPointBranch_tail_mem_ball_2a892ce3fe7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_firstCoords_mem_zeroSet_92c58088a2c7


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
open MvPolynomial Filter Topology Matrix ComplexSets Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.GoodPointBranch
namespace GroundTheory.Heights₂.Heights.GoodPointBranch
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    {u q : Fin n → ℂ} (hqu : linEval u q = 0)
    {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)} {V : Set (Fin n → ℂ)}
    {g : (Fin d → ℂ) → Fin n → ℂ} (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hS : zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O)
    {N₀ : Set (Fin n → ℂ)} (hN₀ : N₀ ∈ 𝓝 q)
    (hdouble : ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N₀ → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0)
    {w : Fin n ⊕ Fin M.m → ℂ} (hwq : IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q)
    {r : ℝ} {φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ} {k : ℕ} (hr : 0 < r)
    (hφd : DifferentiableOn ℂ φ (ball 0 r)) (hφi : InjOn φ (ball 0 r)) (hφ0 : φ 0 = w)
    (hφZ : MapsTo φ (ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal))
    (hφU : ∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' ball 0 s)
    (hvan : VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k)
    (hinjD : ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
      fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0)
    {G : Set (Fin n ⊕ Fin M.m → ℂ)} (hG : G ∈ 𝓝 w) :
    ∃ γ : VarBranch J (d + 1) q,
      (∃ U ∈ 𝓝 w, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius k ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
  set ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ := fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t) with hψdef
  have hψd : DifferentiableOn ℂ ψ (ball 0 r) :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.1 hφd (Sum.inl i)
  have h0r : (0 : Fin (d + 1) → ℂ) ∈ ball 0 r := mem_ball_self hr
  have hψ : HasStrictFDerivAt ψ (fderiv ℂ ψ 0) 0 :=
    (analyticOnNhd_of_differentiableOn isOpen_ball hψd 0 h0r).hasStrictFDerivAt
  have hψ0 : ψ 0 = q := by simp only [hψdef, hφ0, hwq]
  obtain ⟨H, hHd, hH0, hF⟩ := hvan
  have hk : k ≠ 0 := by
    intro hk0
    have h : linEval u (ψ 0) = (0 : Fin (d + 1) → ℂ) 0 ^ k * H 0 := hF 0 h0r
    rw [hψ0, hqu, hk0, pow_zero, one_mul] at h
    exact hH0 0 h0r h.symm
  have hzero : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, linEval u (ψ t) = 0 ↔ t 0 = 0 := by
    intro t ht
    have h : linEval u (ψ t) = t 0 ^ k * H t := hF t ht
    rw [h, mul_eq_zero, pow_eq_zero_iff hk]
    exact or_iff_left (hH0 t ht)
  have hψZ : ∀ t ∈ ball (0 : Fin (d + 1) → ℂ) r, ψ t ∈ zeroSet J := fun t ht =>
    NormalModelFibre.firstCoords_mem_zeroSet M (hφZ ht)
  have hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ zeroSet J ∩ {x | linEval u x = 0} := by
    filter_upwards [ball_mem_nhds (0 : Fin d → ℂ) hr] with v hv
    have hv' := consZero_mem_ball hv
    exact ⟨hψZ _ hv', (hzero _ hv').2 (consZero_apply_zero v)⟩
  obtain ⟨ha, W, hW, hWinj, hcov⟩ := slice_chart hψ hψ0 hinjD hV hqV hg hAg hS hslice
  have hE : ball (0 : Fin (d + 1) → ℂ) r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ ∈ 𝓝 (0 : Fin (d + 1) → ℂ) := by
    have hφc : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    have hψc : ContinuousAt ψ 0 := hψd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
    exact inter_mem (inter_mem (ball_mem_nhds 0 hr) (hφc.preimage_mem_nhds (by rw [hφ0]; exact hG)))
      (hψc.preimage_mem_nhds (by rw [hψ0]; exact hN₀))
  obtain ⟨ε₁, hε₁, hε₁E⟩ := Metric.mem_nhds_iff.1 hE
  obtain ⟨ε₂, hε₂, hε₂W⟩ := Metric.mem_nhds_iff.1 hW
  have hs : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hs1 : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r ∩ φ ⁻¹' G ∩ ψ ⁻¹' N₀ :=
    (ball_subset_ball (min_le_left _ _)).trans hε₁E
  have hsr : ball (0 : Fin (d + 1) → ℂ) (min ε₁ ε₂) ⊆ ball 0 r := fun t ht => (hs1 ht).1.1
  have hs2 : ball (0 : Fin d → ℂ) (min ε₁ ε₂) ⊆ W := (ball_subset_ball (min_le_right _ _)).trans hε₂W
  have hinj : InjOn ψ (ball 0 (min ε₁ ε₂)) := by
    intro t ht t' ht' htt
    by_cases hφe : φ t = φ t'
    · exact hφi (hsr ht) (hsr ht') hφe
    · have hu : linEval u (ψ t) = 0 :=
        hdouble _ (hφZ (hsr ht)) _ (hφZ (hsr ht')) htt (hs1 ht).2 hφe
      have ht0 : t 0 = 0 := (hzero t (hsr ht)).1 hu
      have ht'0 : t' 0 = 0 := (hzero t' (hsr ht')).1 (by rw [← htt]; exact hu)
      have htail : Fin.tail t = Fin.tail t' := hWinj (hs2 (tail_mem_ball ht)) (hs2 (tail_mem_ball ht'))
        (by show ψ (consZero d (Fin.tail t)) = ψ (consZero d (Fin.tail t'))
            rw [consZero_tail t ht0, consZero_tail t' ht'0]
            exact htt)
      calc t = consZero d (Fin.tail t) := (consZero_tail t ht0).symm
        _ = t' := by rw [htail, consZero_tail t' ht'0]
  let γ : VarBranch J (d + 1) q :=
    { radius := min ε₁ ε₂, radius_pos := hs, toFun := ψ, differentiableOn := hψd.mono hsr, injOn := hinj,
      map_zero := hψ0, mapsTo := fun t ht => hψZ t (hsr ht) }
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUs⟩ := hφU (min ε₁ ε₂) hs
    refine ⟨U, hU, fun w' hw' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hUs hw'
    exact ⟨t, ht, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨(hs1 ht).2, φ t, ⟨hφZ (hsr ht), (hs1 ht).1.2⟩, rfl⟩
  · obtain ⟨N, hN, hNS⟩ := hcov (ball 0 (min ε₁ ε₂)) (ball_mem_nhds 0 hs) hs2
    refine ⟨N, hN, fun x hx hxu => ?_⟩
    obtain ⟨v, hv, hvx⟩ := hNS ⟨⟨hx.1, hxu⟩, hx.2⟩
    exact ⟨consZero d v, ⟨consZero_mem_ball hv, consZero_apply_zero v⟩, hvx⟩
  · exact ⟨H, hHd.mono hsr, fun t ht => hH0 t (hsr ht), fun t ht => hF t (hsr ht)⟩
  · have hπ : ∀ x : Fin n → ℂ, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ x = A x :=
      fun x => LinearMap.toMatrix'_mulVec _ x
    have h1 : HasFDerivAt (fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)))
        ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) 0 :=
      (hasFDerivAt_apply 0 0).prodMk (A.hasFDerivAt.comp 0 hψ.hasFDerivAt)
    have h2 : HasFDerivAt (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ))
        ((consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0)))) 0 := by
      have h3 := (consCLM d).hasFDerivAt.comp 0 h1
      have hfun : (fun τ => vecCons (τ 0)
          (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) =
          ⇑(consCLM d) ∘ fun τ : Fin (d + 1) → ℂ => (τ 0, A (ψ τ)) := by
        funext τ
        rw [Function.comp_apply, consCLM_apply, hπ]
      rw [hfun]
      exact h3
    rw [h2.fderiv]
    set L := (consCLM d).comp ((ContinuousLinearMap.proj 0).prod (A.comp (fderiv ℂ ψ 0))) with hL
    have hLinj : Function.Injective L := by
      refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
      have hLv : L v = vecCons (v 0) (A (fderiv ℂ ψ 0 v)) := by
        rw [hL, ContinuousLinearMap.comp_apply, consCLM_apply]
        rfl
      have hv' : vecCons (v 0) (A (fderiv ℂ ψ 0 v)) = 0 := by rw [← hLv]; exact hv
      have h0 : v 0 = 0 := by simpa using congrFun hv' 0
      have hA : A (fderiv ℂ ψ 0 v) = 0 := by
        funext j
        simpa using congrFun hv' j.succ
      exact ha v h0 hA
    exact ⟨hLinj, LinearMap.injective_iff_surjective
      (f := (L : (Fin (d + 1) → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ))).1 hLinj⟩
end GroundTheory.Heights₂.Heights.GoodPointBranch
