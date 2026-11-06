-- Prove2me | solution 1 for SunNLSDP.Equiv.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:03:42.358311+00:00
-- url     : https://prove2.me/submissions/8834b24a-8221-4a12-bc5e-bbfa96ad478b

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology NNReal
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDPLemma1Aux

variable {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem tendsto_comp_clm {F : ℕ → Y →L[ℝ] Z} {G : ℕ → X →L[ℝ] Y} {F0 : Y →L[ℝ] Z}
    {G0 : X →L[ℝ] Y} (hF : Tendsto F atTop (𝓝 F0)) (hG : Tendsto G atTop (𝓝 G0)) :
    Tendsto (fun k => (F k).comp (G k)) atTop (𝓝 (F0.comp G0)) :=
  ((isBoundedBilinearMap_comp (𝕜 := ℝ) (E := X) (F := Y) (G := Z)).continuous.tendsto
    (F0, G0)).comp (hF.prodMk_nhds hG)

/-- Directional information transfers from `Ξ ∘ Ψ` to `Ξ` along `J Ψ`. -/
theorem line_transfer {Ξ : Y → Z} {Ψ : X → Y} {x : X} {M : X →L[ℝ] Y} {A : X →L[ℝ] Z}
    {K : ℝ≥0} {S : Set Y} (hS : S ∈ 𝓝 (Ψ x)) (hlip : LipschitzOnWith K Ξ S)
    (hΨ : HasFDerivAt Ψ M x) (hΦ : HasFDerivAt (fun x => Ξ (Ψ x)) A x) (h : X) :
    HasLineDerivAt ℝ Ξ (A h) (Ψ x) (M h) := by
  have h1 : HasDerivAt (fun t : ℝ => Ξ (Ψ (x + t • h))) (A h) 0 := hΦ.hasLineDerivAt h
  have h2 : HasDerivAt (fun t : ℝ => Ψ (x + t • h)) (M h) 0 := hΨ.hasLineDerivAt h
  set e : ℝ → Z := fun t => Ξ (Ψ x + t • M h) - Ξ (Ψ (x + t • h))
  have he : HasDerivAt e 0 0 := by
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hc1 : Tendsto (fun t : ℝ => Ψ x + t • M h) (𝓝 0) (𝓝 (Ψ x)) := by
      have : Continuous (fun t : ℝ => Ψ x + t • M h) := by fun_prop
      simpa using this.tendsto 0
    have hc2 : Tendsto (fun t : ℝ => Ψ (x + t • h)) (𝓝 0) (𝓝 (Ψ x)) := by
      simpa using h2.differentiableAt.continuousAt.tendsto
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h2
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Ψ x + t • M h ∈ S ∧ Ψ (x + t • h) ∈ S :=
      (hc1.eventually hS).and (hc2.eventually hS)
    have hO : (fun t : ℝ => e (0 + t) - e 0 - t • (0 : Z)) =O[𝓝 0]
        (fun t : ℝ => Ψ (x + (0 + t) • h) - Ψ (x + (0 : ℝ) • h) - t • M h) := by
      refine Asymptotics.IsBigO.of_bound (K : ℝ) ?_
      filter_upwards [hev] with t ht
      simp only [e, zero_add, zero_smul, add_zero, sub_self, smul_zero, sub_zero]
      have := hlip.norm_sub_le ht.1 ht.2
      calc ‖Ξ (Ψ x + t • M h) - Ξ (Ψ (x + t • h))‖ ≤ K * ‖Ψ x + t • M h - Ψ (x + t • h)‖ := this
        _ = K * ‖Ψ (x + t • h) - Ψ x - t • M h‖ := by
          congr 1; rw [← norm_neg]; congr 1; abel
    exact hO.trans_isLittleO h2
  have h3 := h1.add he
  simp only [add_zero] at h3
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [e]

/-- Lipschitz near `y` + line derivatives given by one continuous linear map ⇒ Fréchet. -/
theorem fderiv_of_line [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    {Ξ : Y → Z} {y : Y} {L : Y →L[ℝ] Z} {K : ℝ≥0} {S : Set Y} (hS : S ∈ 𝓝 y)
    (hlip : LipschitzOnWith K Ξ S) (hL : ∀ w, HasLineDerivAt ℝ Ξ (L w) y w) :
    HasFDerivAt Ξ L y := by
  obtain ⟨g, hg, hEq⟩ := hlip.extend_finite_dimension
  have hev : g =ᶠ[𝓝 y] Ξ := Filter.mem_of_superset hS (fun z hz => (hEq hz).symm)
  have hgL : ∀ w ∈ (Set.univ : Set Y), HasLineDerivAt ℝ g (L w) y w := by
    intro w _
    exact (hL w).congr_of_eventuallyEq hev
  have := hg.hasFDerivAt_of_hasLineDerivAt_of_closure (s := Set.univ) (by simp) hgL
  exact this.congr_of_eventuallyEq hev.symm

/-- Key lemma: if `Ξ ∘ Ψ` is differentiable at `x` and `J Ψ(x)` is onto, `Ξ` is differentiable
at `Ψ x`. -/
theorem diff_of_comp [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    {Ξ : Y → Z} {Ψ : X → Y} {x : X} {M : X →L[ℝ] Y}
    {K : ℝ≥0} {S : Set Y} (hS : S ∈ 𝓝 (Ψ x)) (hlip : LipschitzOnWith K Ξ S)
    (hΨ : HasFDerivAt Ψ M x) (hM : Function.Surjective M)
    (hΦ : DifferentiableAt ℝ (fun x => Ξ (Ψ x)) x) : DifferentiableAt ℝ Ξ (Ψ x) := by
  obtain ⟨R, hR⟩ := M.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hM)
  have hMR : ∀ w, M (R w) = w := fun w => by
    simpa using congrArg (fun T : Y →L[ℝ] Y => T w) hR
  set A := fderiv ℝ (fun x => Ξ (Ψ x)) x
  refine (fderiv_of_line (L := A.comp R) hS hlip fun w => ?_).differentiableAt
  have := line_transfer hS hlip hΨ hΦ.hasFDerivAt (R w)
  rw [hMR w] at this
  simpa using this

end SunNLSDPLemma1Aux

open SunNLSDPLemma1Aux in
theorem solution {X Y Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (Ψ : X → Y) (Ξ : Y → Z) (xbar : X) (N : Set X) (O : Set Y)
    (hN : IsOpen N) (hxN : xbar ∈ N) (hΨ : ContDiffOn ℝ 1 Ψ N)
    (hO : IsOpen O) (hyO : Ψ xbar ∈ O)
    (hΞlip : ∀ y ∈ O, ∃ K, ∃ V ∈ 𝓝 y, LipschitzOnWith K Ξ V)
    (hΞdir : ∀ y ∈ O, ∀ v : Y, ∃ w : Z, NonsmoothNewton.Local.HasDirDerivAt Ξ y v w)
    (honto : Function.Surjective (fderiv ℝ Ψ xbar)) :
    bJac (fun x => Ξ (Ψ x)) xbar = (fun W => W.comp (fderiv ℝ Ψ xbar)) '' bJac Ξ (Ψ xbar) := by
  set J := fderiv ℝ Ψ
  obtain ⟨K, S, hS, hlip⟩ := hΞlip (Ψ xbar) hyO
  set T := interior S ∩ O
  have hTopen : IsOpen T := isOpen_interior.inter hO
  have hyT : Ψ xbar ∈ T := ⟨mem_interior_iff_mem_nhds.2 hS, hyO⟩
  have hSnhds : ∀ y ∈ T, S ∈ 𝓝 y := fun y hy => mem_interior_iff_mem_nhds.1 hy.1
  have hdiffΨ : ∀ x ∈ N, HasFDerivAt Ψ (J x) x := fun x hx =>
    (((hΨ.differentiableOn one_ne_zero) x hx).differentiableAt (hN.mem_nhds hx)).hasFDerivAt
  have hJcont : ContinuousAt J xbar :=
    (hΨ.continuousOn_fderiv_of_isOpen hN le_rfl).continuousAt (hN.mem_nhds hxN)
  have hΨcont : ContinuousAt Ψ xbar := (hdiffΨ xbar hxN).continuousAt
  obtain ⟨R0, hR0⟩ :=
    (J xbar).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 honto)
  have hsurj_ev : ∀ᶠ x in 𝓝 xbar, Function.Surjective (J x) := by
    have h1 : Tendsto (fun x => (J x).comp R0) (𝓝 xbar) (𝓝 ((J xbar).comp R0)) :=
      ((isBoundedBilinearMap_comp (𝕜 := ℝ) (E := Y) (F := X) (G := Y)).continuous.tendsto
        _).comp (hJcont.prodMk_nhds tendsto_const_nhds)
    rw [hR0] at h1
    have h2 : ∀ᶠ x in 𝓝 xbar, IsUnit ((J x).comp R0) :=
      h1.eventually (Units.isOpen.mem_nhds (show IsUnit (ContinuousLinearMap.id ℝ Y) from isUnit_one))
    filter_upwards [h2] with x hx
    intro w
    obtain ⟨u, hu⟩ := hx
    refine ⟨R0 ((↑u⁻¹ : Y →L[ℝ] Y) w), ?_⟩
    have : ((↑u * ↑u⁻¹ : Y →L[ℝ] Y)) w = w := by simp
    rw [hu] at this
    simpa using this
  ext V
  constructor
  · rintro ⟨u, hu, hd, hT⟩
    have hΨu : Tendsto (fun k => Ψ (u k)) atTop (𝓝 (Ψ xbar)) := hΨcont.tendsto.comp hu
    have hev : ∀ᶠ k in atTop, (u k ∈ N ∧ Ψ (u k) ∈ T) ∧ Function.Surjective (J (u k)) :=
      ((hu.eventually (hN.mem_nhds hxN)).and (hΨu.eventually (hTopen.mem_nhds hyT))).and
        (hu.eventually hsurj_ev)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    set v : ℕ → X := fun k => u (k + N0)
    have hv : ∀ k, (v k ∈ N ∧ Ψ (v k) ∈ T) ∧ Function.Surjective (J (v k)) :=
      fun k => hN0 _ (by omega)
    have hΞd : ∀ k, DifferentiableAt ℝ Ξ (Ψ (v k)) := fun k =>
      diff_of_comp (hSnhds _ (hv k).1.2) hlip (hdiffΨ _ (hv k).1.1) (hv k).2 (hd _)
    have hchain : ∀ k, fderiv ℝ (fun x => Ξ (Ψ x)) (v k) =
        (fderiv ℝ Ξ (Ψ (v k))).comp (J (v k)) := fun k =>
      ((hΞd k).hasFDerivAt.comp (v k) (hdiffΨ _ (hv k).1.1)).fderiv
    have hbd : ∀ k, fderiv ℝ Ξ (Ψ (v k)) ∈ Metric.closedBall (0 : Y →L[ℝ] Z) K := fun k => by
      rw [mem_closedBall_zero_iff]
      exact norm_fderiv_le_of_lipschitzOn ℝ (hSnhds _ (hv k).1.2) hlip
    obtain ⟨W, -, φ, hφ, hW⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
    have hvt : Tendsto v atTop (𝓝 xbar) := hu.comp (tendsto_add_atTop_nat N0)
    have hvφ : Tendsto (fun k => v (φ k)) atTop (𝓝 xbar) := hvt.comp hφ.tendsto_atTop
    refine ⟨W, ⟨fun k => Ψ (v (φ k)), hΨcont.tendsto.comp hvφ, fun k => hΞd _, hW⟩, ?_⟩
    have h1 : Tendsto (fun k => fderiv ℝ (fun x => Ξ (Ψ x)) (v (φ k))) atTop (𝓝 V) :=
      (hT.comp (tendsto_add_atTop_nat N0)).comp hφ.tendsto_atTop
    have h2 : Tendsto (fun k => fderiv ℝ (fun x => Ξ (Ψ x)) (v (φ k))) atTop
        (𝓝 (W.comp (J xbar))) := by
      simp_rw [hchain]
      exact tendsto_comp_clm hW (hJcont.tendsto.comp hvφ)
    exact tendsto_nhds_unique h2 h1
  · rintro ⟨W, ⟨w, hw, hwd, hwT⟩, rfl⟩
    have hΨs : HasStrictFDerivAt Ψ (J xbar) xbar :=
      (hΨ.contDiffAt (hN.mem_nhds hxN)).hasStrictFDerivAt one_ne_zero
    set g : Y → Y := fun v => Ψ (xbar + R0 v)
    have hg : HasStrictFDerivAt g ((ContinuousLinearEquiv.refl ℝ Y : Y ≃L[ℝ] Y) : Y →L[ℝ] Y) 0 := by
      have h1 : HasStrictFDerivAt (fun v : Y => xbar + R0 v) R0 0 :=
        R0.hasStrictFDerivAt.const_add xbar
      have h2 : HasStrictFDerivAt Ψ (J xbar) (xbar + R0 0) := by simpa using hΨs
      have := h2.comp (0 : Y) h1
      rw [hR0] at this
      simpa using this
    have hg0 : g 0 = Ψ xbar := by simp [g]
    set ℓ := HasStrictFDerivAt.localInverse g _ 0 hg
    have hℓ : Tendsto ℓ (𝓝 (g 0)) (𝓝 0) := hg.localInverse_tendsto
    have hright : ∀ᶠ y in 𝓝 (g 0), g (ℓ y) = y := hg.eventually_right_inverse
    rw [hg0] at hℓ hright
    set x : ℕ → X := fun k => xbar + R0 (ℓ (w k))
    have hx : Tendsto x atTop (𝓝 xbar) := by
      have : Tendsto (fun k => xbar + R0 (ℓ (w k))) atTop (𝓝 (xbar + R0 0)) :=
        tendsto_const_nhds.add ((R0.continuous.tendsto 0).comp (hℓ.comp hw))
      simpa using this
    have hev : ∀ᶠ k in atTop, x k ∈ N ∧ Ψ (x k) = w k :=
      (hx.eventually (hN.mem_nhds hxN)).and (hw.eventually hright)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
    have hfd : ∀ k, HasFDerivAt (fun x => Ξ (Ψ x)) ((fderiv ℝ Ξ (w (k + N0))).comp
        (J (x (k + N0)))) (x (k + N0)) := by
      intro k
      obtain ⟨h1, h2⟩ := hN0 (k + N0) (by omega)
      have := (hwd (k + N0)).hasFDerivAt
      rw [← h2] at this ⊢
      exact this.comp (x (k + N0)) (hdiffΨ _ h1)
    refine ⟨fun k => x (k + N0), hx.comp (tendsto_add_atTop_nat N0),
      fun k => (hfd k).differentiableAt, ?_⟩
    simp_rw [fun k => (hfd k).fderiv]
    exact tendsto_comp_clm (hwT.comp (tendsto_add_atTop_nat N0))
      (hJcont.tendsto.comp (hx.comp (tendsto_add_atTop_nat N0)))
