-- Prove2me | solution 1 for SP4Mission.local_diffeomorphAt_of_invertible_mfderiv
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-06T10:42:34.90585+00:00
-- url     : https://prove2.me/submissions/292fb307-b34f-47f1-b01c-e071e2572e96

import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Set Manifold Filter

set_option backward.isDefEq.respectTransparency false

namespace SP4Mission

/-- The smooth inverse function theorem on an open subset of a Banach space. -/
theorem local_diffeomorph_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ContDiffOn ℝ ∞ f s)
    (hD : (fderiv ℝ f x).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  have hf₀ : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hs.mem_nhds hx)
  have hDnear : ∀ᶠ y in 𝓝 x, (fderiv ℝ f y).IsInvertible :=
    hf₀.continuousAt_fderiv (by simp) (ContinuousLinearEquiv.isOpen.mem_nhds hD)
  obtain ⟨u, hu, huo, hxu⟩ := mem_nhds_iff.mp (inter_mem (hs.mem_nhds hx) hDnear)
  obtain ⟨L, hL⟩ := hD
  have hDf : HasFDerivAt f (L : E →L[ℝ] F) x := by
    rw [hL]
    exact (hf₀.differentiableAt (by simp)).hasFDerivAt
  let e := hf₀.toOpenPartialHomeomorph f hDf (by simp)
  let er := e.restr u
  have her : (er : E → F) = f := rfl
  have hsource {z : E} (hz : z ∈ er.source) : z ∈ s ∧ (fderiv ℝ f z).IsInvertible :=
    hu (interior_subset hz.2)
  let φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ := {
    toPartialEquiv := er.toPartialEquiv
    open_source := er.open_source
    open_target := er.open_target
    contMDiffOn_toFun := by
      intro z hz
      exact ((hf.contDiffAt (hs.mem_nhds (hsource hz).1)).contMDiffAt).contMDiffWithinAt
    contMDiffOn_invFun := by
      intro y hy
      have hz := hsource (er.map_target hy)
      obtain ⟨Lz, hLz⟩ := hz.2
      have hfz := hf.contDiffAt (hs.mem_nhds hz.1)
      have hDz : HasFDerivAt er (Lz : E →L[ℝ] F) (er.symm y) := by
        rw [her, hLz]
        exact (hfz.differentiableAt (by simp)).hasFDerivAt
      exact ((er.contDiffAt_symm hy hDz hfz).contMDiffAt).contMDiffWithinAt }
  refine ⟨φ, ?_, fun _ _ => rfl⟩
  change x ∈ er.source
  exact ⟨hf₀.mem_toOpenPartialHomeomorph_source hDf (by simp), by rwa [huo.interior_eq]⟩

/-- The local diffeomorphism property depends only on the germ of the map. -/
theorem local_diffeomorphAt_congr
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N]
    {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (heq : f =ᶠ[𝓝 x] g) : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x := by
  obtain ⟨φ, hx, hφ⟩ := hf
  obtain ⟨u, hu, huo, hxu⟩ := mem_nhds_iff.mp heq
  let e := φ.toOpenPartialHomeomorph.restr u
  let ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := φ.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨ψ, ⟨hx, by rwa [huo.interior_eq]⟩, ?_⟩
  intro z hz
  exact (hu (interior_subset hz.2)).symm.trans (hφ hz.1)


end SP4Mission

open SP4Mission

theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
    {f : M → N} {x : M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hD : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
  let c := chartAt E x
  let d := chartAt F (f x)
  let Ff : E → F := d ∘ f ∘ c.symm
  let s := c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source)
  have hs : IsOpen s := c.isOpen_inter_preimage_symm (d.open_source.preimage hf.continuous)
  have hcx : c x ∈ s := by simp [s, c, d, mem_chart_source]
  have hF : ContDiffOn ℝ ∞ Ff s := by
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_chart (I := 𝓘(ℝ, F)) (x := f x)).comp
      ((hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x))).mono
        inter_subset_left) inter_subset_right
  have hDF : HasFDerivAt Ff (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) (c x) := by
    apply HasFDerivWithinAt.hasFDerivAt_of_univ
    have h := ((hf x).mdifferentiableAt (by simp)).hasMFDerivAt.2
    simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, Ff, c, d] using h
  have hDFinv : (fderiv ℝ Ff (c x)).IsInvertible := by rwa [hDF.fderiv]
  have hFlocal := local_diffeomorph_of_contDiffOn hs hcx hF hDFinv
  let pc : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  let pd : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) N F ∞ := {
    toPartialEquiv := d.toPartialEquiv
    open_source := d.open_source
    open_target := d.open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hc := pc.isLocalDiffeomorphAt _ _ _ (mem_chart_source E x)
  have hd := pd.symm.isLocalDiffeomorphAt _ _ _ (d.map_source (mem_chart_source F (f x)))
  have hFx : Ff (c x) = d (f x) := by simp [Ff, c, mem_chart_source]
  have hlocal := (hc.comp 𝓘(ℝ, F) F hFlocal).comp 𝓘(ℝ, F) N (hFx.symm ▸ hd)
  apply local_diffeomorphAt_congr hlocal
  filter_upwards [c.open_source.mem_nhds (mem_chart_source E x),
    hf.continuous.continuousAt (d.open_source.mem_nhds (mem_chart_source F (f x)))] with z hzc hzd
  change d.symm (d (f (c.symm (c z)))) = f z
  rw [c.left_inv hzc, d.left_inv hzd]
