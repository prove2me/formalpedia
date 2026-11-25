-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_coordChart_fe9e1808ce1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:10.998711+00:00
-- url     : https://prove2.me/submissions/4a5a6a6d-44bd-403d-a02b-185556917d97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointChartLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
open MvPolynomial Topology
open scoped ContDiff
noncomputable section
namespace GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
theorem _root_.solution {σ κ ι : Type} [Fintype σ] [Fintype κ] [Fintype ι]
    (q : κ ⊕ ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ))
    (hq : ∀ k, AnalyticAt ℂ (q k) a)
    (hinj : ∀ v : σ → ℂ, (∀ k, fderiv ℂ (q k) a v = 0) → v = 0)
    (hcard : Fintype.card κ + Fintype.card ι = Fintype.card σ) (hW : W ∈ 𝓝 a) :
    ∃ (V : Set (σ → ℂ)) (O : Set (κ → ℂ)) (φ : (κ → ℂ) → σ → ℂ),
      IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧ IsOpen O ∧ AnalyticOnNhd ℂ φ O ∧
      (∀ y ∈ O, φ y ∈ V) ∧ (∀ y ∈ O, ∀ i, q (Sum.inl i) (φ y) = y i) ∧
      (∀ y ∈ O, ∀ j, q (Sum.inr j) (φ y) = 0) ∧
      (∀ z ∈ V, (∀ j, q (Sum.inr j) z = 0) →
        (fun i => q (Sum.inl i) z) ∈ O ∧ φ (fun i => q (Sum.inl i) z) = z) ∧
      (∀ y ∈ O, ∀ v, (∀ i, fderiv ℂ (q (Sum.inl i)) (φ y) (fderiv ℂ φ y v) = v i) ∧
        ∀ j, fderiv ℂ (q (Sum.inr j)) (φ y) (fderiv ℂ φ y v) = 0) := by
  classical
  set P : (σ → ℂ) →L[ℂ] (κ ⊕ ι → ℂ) := ContinuousLinearMap.pi fun k => fderiv ℂ (q k) a with hP
  have hPinj : Function.Injective P := by
    intro v v' hvv
    rw [← sub_eq_zero]
    refine hinj _ fun k => ?_
    have := congrFun hvv k
    simp only [hP, ContinuousLinearMap.pi_apply] at this
    rw [map_sub, this, sub_self]
  have hPbij : Function.Bijective (P : (σ → ℂ) →ₗ[ℂ] (κ ⊕ ι → ℂ)) :=
    ⟨hPinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, hcard])).1 hPinj⟩
  set Pe : (σ → ℂ) ≃L[ℂ] (κ ⊕ ι → ℂ) :=
    (LinearEquiv.ofBijective _ hPbij).toContinuousLinearEquiv with hPe
  have hPeP : (Pe : (σ → ℂ) →L[ℂ] (κ ⊕ ι → ℂ)) = P := by ext1 x; rfl
  set F : (σ → ℂ) → κ ⊕ ι → ℂ := fun z k => q k z with hF
  have hFan : ∀ z, (∀ k, AnalyticAt ℂ (q k) z) → AnalyticAt ℂ F z := fun z hz => analyticAt_pi_iff.2 hz
  have hFd : HasFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    rw [hPeP]
    exact hasFDerivAt_pi.2 fun k => (hq k).differentiableAt.hasFDerivAt
  have hst : HasStrictFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    have := (hFan a hq).hasStrictFDerivAt; rwa [hFd.fderiv] at this
  set Φ := hst.toOpenPartialHomeomorph F with hΦ
  have hev : ∀ᶠ t in 𝓝 a, (∀ k, AnalyticAt ℂ (q k) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (κ ⊕ ι → ℂ)) → _) := by
    refine (Filter.eventually_all.2 fun k => (hq k).eventually_analyticAt).and
      ((show ∀ᶠ t in 𝓝 a, t ∈ W from hW).and ?_)
    exact (hFan a hq).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨Pe, hFd.fderiv.symm⟩)
  obtain ⟨V₀, hV₀, hV₀o, haV₀⟩ := eventually_nhds_iff.1 hev
  set Ψ := Φ.restrOpen V₀ hV₀o with hΨ
  have hΨs : Ψ.source = Φ.source ∩ V₀ := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΨF : ∀ z, Ψ z = F z := fun z => rfl
  have haΨ : a ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, haV₀⟩
  have hsrc : ∀ t ∈ Ψ.source, (∀ k, AnalyticAt ℂ (q k) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (κ ⊕ ι → ℂ)) → _) :=
    fun t ht => hV₀ t (hΨs ▸ ht).2
  have hembA : ∀ y, AnalyticAt ℂ (fun y : κ → ℂ => Sum.elim y (0 : ι → ℂ)) y := fun y =>
    analyticAt_pi_iff.2 fun k => by
      rcases k with i | j
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) i).analyticAt y
      · exact analyticAt_const
  have hemb : Continuous (fun y : κ → ℂ => Sum.elim y (0 : ι → ℂ)) :=
    continuous_iff_continuousAt.2 fun y => (hembA y).continuousAt
  set O : Set (κ → ℂ) := (fun y => Sum.elim y (0 : ι → ℂ)) ⁻¹' Ψ.target with hO
  have hOo : IsOpen O := Ψ.open_target.preimage hemb
  have hφV : ∀ y ∈ O, Ψ.symm (Sum.elim y 0) ∈ Ψ.source := fun y hy => Ψ.map_target hy
  have hFφ : ∀ y ∈ O, F (Ψ.symm (Sum.elim y 0)) = Sum.elim y 0 := fun y hy => Ψ.right_inv hy
  have hφan : AnalyticOnNhd ℂ (fun y => Ψ.symm (Sum.elim y 0)) O := by
    intro y hy
    have hp : Sum.elim y (0 : ι → ℂ) ∈ Ψ.target := hy
    obtain ⟨han, -, e', he'⟩ := hsrc _ (Ψ.map_target hp)
    have hFe : HasFDerivAt Ψ (e' : (σ → ℂ) →L[ℂ] _) (Ψ.symm (Sum.elim y 0)) := by
      rw [he']; exact (hFan _ han).differentiableAt.hasFDerivAt
    have hc : ContDiffAt ℂ ω Ψ.symm (Sum.elim y 0) :=
      Ψ.contDiffAt_symm hp hFe (hFan _ han).contDiffAt
    exact AnalyticAt.comp (g := Ψ.symm) (f := fun y : κ → ℂ => Sum.elim y (0 : ι → ℂ)) (x := y)
      hc.analyticAt (hembA y)
  refine ⟨Ψ.source, O, fun y => Ψ.symm (Sum.elim y 0), Ψ.open_source, haΨ,
    fun t ht => (hsrc t ht).2.1, hOo, hφan, hφV, ?_, ?_, ?_, ?_⟩
  · intro y hy i
    exact congrFun (hFφ y hy) (Sum.inl i)
  · intro y hy j
    exact congrFun (hFφ y hy) (Sum.inr j)
  · intro z hz hz0
    have hFz : F z = Sum.elim (fun i => q (Sum.inl i) z) 0 := by
      funext k
      rcases k with i | j
      · rfl
      · exact hz0 j
    have ht : F z ∈ Ψ.target := by rw [← hΨF]; exact Ψ.map_source hz
    refine ⟨show Sum.elim (fun i => q (Sum.inl i) z) (0 : ι → ℂ) ∈ Ψ.target from hFz ▸ ht, ?_⟩
    show Ψ.symm (Sum.elim (fun i => q (Sum.inl i) z) (0 : ι → ℂ)) = z
    rw [← hFz, ← hΨF]
    exact Ψ.left_inv hz
  · intro y hy v
    have hyn : O ∈ 𝓝 y := hOo.mem_nhds hy
    have hφd : HasFDerivAt (fun y => Ψ.symm (Sum.elim y 0))
        (fderiv ℂ (fun y => Ψ.symm (Sum.elim y 0)) y) y :=
      (hφan y hy).differentiableAt.hasFDerivAt
    have hcomp : ∀ k, fderiv ℂ (fun y' => q k (Ψ.symm (Sum.elim y' 0))) y =
        (fderiv ℂ (q k) (Ψ.symm (Sum.elim y 0))).comp (fderiv ℂ (fun y => Ψ.symm (Sum.elim y 0)) y) :=
      fun k => ((((hsrc _ (hφV y hy)).1 k).differentiableAt.hasFDerivAt).comp y hφd).fderiv
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have he : (fun y' => q (Sum.inl i) (Ψ.symm (Sum.elim y' 0))) =ᶠ[𝓝 y] fun y' => y' i :=
        Filter.eventually_of_mem hyn fun y' hy' => congrFun (hFφ y' hy') (Sum.inl i)
      have := congrArg (fun L : (κ → ℂ) →L[ℂ] ℂ => L v)
        ((hcomp (Sum.inl i)).symm.trans (he.fderiv_eq.trans (hasFDerivAt_apply i y).fderiv))
      simpa using this
    · have he : (fun y' => q (Sum.inr j) (Ψ.symm (Sum.elim y' 0))) =ᶠ[𝓝 y] fun _ => (0 : ℂ) :=
        Filter.eventually_of_mem hyn fun y' hy' => congrFun (hFφ y' hy') (Sum.inr j)
      have := congrArg (fun L : (κ → ℂ) →L[ℂ] ℂ => L v)
        ((hcomp (Sum.inr j)).symm.trans (he.fderiv_eq.trans (hasFDerivAt_const (0 : ℂ) y).fderiv))
      simpa using this
end GroundTheory.Heights₂.Heights.NormalModelGoodPointChart
