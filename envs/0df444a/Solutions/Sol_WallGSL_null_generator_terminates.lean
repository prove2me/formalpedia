-- Prove2me | solution 1 for WallGSL.null_generator_terminates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:52:59.980994+00:00
-- url     : https://prove2.me/submissions/f2a6c1ec-8b48-4873-9302-5edd5811b50f

import Mathlib
import Definitions.Def_WallGSL_GeneralizedEntropy

set_option linter.all false

open scoped Manifold Topology ContDiff
open Set Filter

namespace WallGSL
namespace LorentzianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable (st : LorentzianMetric E M)

lemma exists_timelikeStep_near (x : M) (U : Set M) (hU : U ∈ 𝓝 x) :
    ∃ q ∈ U, st.TimelikeStep q x := by
  set φ := extChartAt 𝓘(ℝ, E) x with hφ
  set y0 := φ x
  have hy0 : y0 ∈ φ.target := mem_extChartAt_target x
  have htgt : IsOpen φ.target := isOpen_extChartAt_target x
  have hxs : x ∈ φ.source := mem_extChartAt_source x
  set D : E → E →L[ℝ] E := fun y => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm y
  set u : M → E := fun z => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ z (st.timeField z)
  set w : E := u x
  set c : ℝ → E := fun τ => y0 + τ • w
  set γ : ℝ → M := fun τ => φ.symm (c τ)
  have hc : Continuous c := by fun_prop
  have hc0 : c 0 = y0 := by simp [c]
  have hγ0 : γ 0 = x := by simp only [γ, hc0]; exact φ.left_inv hxs
  -- inverse relation of chart derivatives
  have hinv : ∀ y ∈ φ.target, ∀ v, D y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ (φ.symm y) v) = v := by
    intro y hy v
    have := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ, E)) (x := x) hy
    simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at this
    exact congrArg (fun L : E →L[ℝ] E => L v) this
  have hT : ∀ y ∈ φ.target, st.timeField (φ.symm y) = D y (u (φ.symm y)) := by
    intro y hy; exact (hinv y hy _).symm
  have hD0 : D y0 w = st.timeField x := by
    have := hinv y0 hy0 (st.timeField x)
    rw [φ.left_inv hxs] at this
    exact this
  -- continuity of the chart coordinates of the time field
  have hu : ContinuousAt u x := by
    have h1 := (FiberBundle.continuousAt_totalSpace (F := E) (E := TangentSpace 𝓘(ℝ, E) (M := M))
      (fun z => (⟨z, st.timeField z⟩ : TangentBundle 𝓘(ℝ, E) M)) (x₀ := x)).1
      st.continuous_timeField.continuousAt
    refine h1.2.congr ?_
    have hsrc : (chartAt E x).source ∈ 𝓝 x := (chartAt E x).open_source.mem_nhds (mem_chart_source E x)
    filter_upwards [hsrc] with z hz
    simp only [u, TangentBundle.trivializationAt_apply]
    have hmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ z := mdifferentiableAt_extChartAt hz
    rw [hmd.mfderiv]
    simp [writtenInExtChartAt, extChartAt_model_space_eq_id, φ, extChartAt, chartAt_self_eq]
    rfl
  have hmdS : ∀ y ∈ φ.target, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm y := by
    intro y hy
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x) hy
    simp only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] at this
    exact this
  have hcd : ∀ t, HasDerivAt c w t := by
    intro t
    simpa [c] using ((hasDerivAt_id t).smul_const w).const_add y0
  have hvel : ∀ a b t, a < b → t ∈ Icc a b → c t ∈ φ.target →
      velocityWithin γ (Icc a b) t = D (c t) w := by
    intro a b t hab ht hct
    have hU' : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffOn_Icc hab t ht
    have hcm : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c (Icc a b) t :=
      (hcd t).differentiableAt.differentiableWithinAt.mdifferentiableWithinAt
    unfold velocityWithin
    rw [show γ = φ.symm ∘ c from rfl, mfderiv_comp_mfderivWithin t (hmdS _ hct) hcm
      hU'.uniqueMDiffWithinAt, mfderivWithin_eq_fderivWithin,
      (hcd t).hasDerivWithinAt.hasFDerivWithinAt.fderivWithin hU']
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rfl
  have hsm : ∀ a b, (∀ t ∈ Icc a b, c t ∈ φ.target) →
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b) := by
    intro a b h
    have h1 := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := ∞) x)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c := by
      rw [contMDiff_iff_contDiff]; fun_prop
    exact (h1.comp h2.contMDiffOn h).of_le (by norm_cast)
  -- continuity of the relevant quantities at τ = 0
  have hcmc : ContinuousAt (st.coordMetric x) y0 :=
    (st.smooth x).continuousOn.continuousAt (htgt.mem_nhds hy0)
  have hcτ : ContinuousAt (fun τ => st.coordMetric x (c τ)) 0 :=
    hcmc.comp_of_eq hc.continuousAt hc0
  have hγc : ContinuousAt γ 0 :=
    (continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) x).comp_of_eq hc.continuousAt hc0
  set F1 : ℝ → ℝ := fun τ => st.coordMetric x (c τ) w w
  set F2 : ℝ → ℝ := fun τ => st.coordMetric x (c τ) w (u (γ τ))
  have hF1 : ContinuousAt F1 0 := (hcτ.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hF2 : ContinuousAt F2 0 :=
    (hcτ.clm_apply continuousAt_const).clm_apply (hu.comp_of_eq hγc hγ0)
  have hF10 : F1 0 = st.g x (st.timeField x) (st.timeField x) := by
    show st.coordMetric x (c 0) w w = _
    rw [hc0]
    show st.g (φ.symm y0) (D y0 w) (D y0 w) = _
    rw [hD0, show φ.symm y0 = x from φ.left_inv hxs]
  have hF20 : F2 0 = F1 0 := by simp only [F2, F1, hγ0]; rfl
  have hneg := st.timelike x
  have e1 : ∀ᶠ τ in 𝓝 (0:ℝ), F1 τ < 0 := hF1.eventually_lt continuousAt_const (by rw [hF10]; exact hneg)
  have e2 : ∀ᶠ τ in 𝓝 (0:ℝ), F2 τ < 0 :=
    hF2.eventually_lt continuousAt_const (by rw [hF20, hF10]; exact hneg)
  have e3 : ∀ᶠ τ in 𝓝 (0:ℝ), c τ ∈ φ.target :=
    hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact htgt.mem_nhds hy0)
  have e4 : ∀ᶠ τ in 𝓝 (0:ℝ), γ τ ∈ U := hγc.preimage_mem_nhds (by rw [hγ0]; exact hU)
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 (((e1.and e2).and e3).and e4)
  have hP' : ∀ t ∈ Icc (-(ε / 2)) 0, (F1 t < 0 ∧ F2 t < 0) ∧ c t ∈ φ.target := by
    intro t ht
    have : dist t 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    exact (hP this).1
  refine ⟨γ (-(ε / 2)), (hP (by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith)).2,
    γ, -(ε / 2), 0, by linarith, rfl, hγ0, hsm _ _ fun t ht => (hP' t ht).2, fun t ht => ?_⟩
  obtain ⟨⟨h1, h2⟩, hct⟩ := hP' t ht
  rw [hvel _ _ t (by linarith) ht hct]
  refine ⟨h1, ?_⟩
  show st.g (φ.symm (c t)) (D (c t) w) (st.timeField (φ.symm (c t))) < 0
  rw [hT _ hct]
  exact h2

theorem main_terminates
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (st : LorentzianMetric E M) (Sgen : Set M → ℝ) (N X : Set M) (g₀ : M)
    (hN : st.IsAchronal N)
    (hdec : st.EntropyDecreasingAt Sgen X g₀)
    (hSC : st.TheoremOneComparisonAt Sgen N X g₀)
    (hGSL : st.FineGrainedGSL Sgen)
    (W : ℝ → M) (a : ℝ) (hW : st.IsFutureInfiniteNullRay W a) (hWa : W a = g₀) :
    ¬ (W '' Ici a ⊆ N) := by
  intro hsub
  set P := st.chronPast (W '' Ici a)
  have hobs : st.IsFutureObserver W a := Or.inr hW
  have hdisj : N ∩ P = ∅ := by
    ext p
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hp ⟨q, hq, hpq⟩
    exact hN p hp q (hsub hq) hpq
  have hseg : ∃ (γ : ℝ → M) (s b : ℝ), s < b ∧ γ s = g₀ ∧ ContinuousWithinAt γ (Ici s) s ∧
      st.IsGeodesicOn γ (Ioo s b) ∧ (∀ t ∈ Ioo s b, st.IsFutureNull (γ t) (velocity γ t)) ∧
      γ '' Ico s b ⊆ N ∩ frontier P := by
    refine ⟨W, a, a + 1, by linarith, hWa, hW.2.1, ?_, fun t ht => hW.2.2 t ht.1, ?_⟩
    · exact ⟨hW.1.1.mono Ioo_subset_Ioi_self, fun t₀ ht₀ => hW.1.2 t₀ (Ioo_subset_Ioi_self ht₀)⟩
    · rintro _ ⟨t, ht, rfl⟩
      have hWt : W t ∈ W '' Ici a := ⟨t, ht.1, rfl⟩
      refine ⟨hsub hWt, ?_, ?_⟩
      · rw [mem_closure_iff_nhds]
        intro U hU
        obtain ⟨q, hqU, hq⟩ := st.exists_timelikeStep_near (W t) U hU
        exact ⟨q, hqU, W t, hWt, Relation.TransGen.single hq⟩
      · intro hint
        have : W t ∈ P := interior_subset hint
        have h2 : W t ∈ N ∩ P := ⟨hsub hWt, this⟩
        rw [hdisj] at h2; exact h2
  obtain ⟨S, hS, -, hS'⟩ := hSC W a hobs hdisj hseg hdec
  obtain ⟨S', ⟨hS'c, -, hS'f⟩, hlt⟩ := hS' univ univ_mem
  have := hGSL W a hobs S S' hS hS'c hS'f
  linarith

end LorentzianMetric
end WallGSL

open WallGSL in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (st : LorentzianMetric E M) (Sgen : Set M → ℝ) (N X : Set M) (g₀ : M)
    (hN : st.IsAchronal N)
    (hdec : st.EntropyDecreasingAt Sgen X g₀)
    (hSC : st.TheoremOneComparisonAt Sgen N X g₀)
    (hGSL : st.FineGrainedGSL Sgen)
    (W : ℝ → M) (a : ℝ) (hW : st.IsFutureInfiniteNullRay W a) (hWa : W a = g₀) :
    ¬ (W '' Ici a ⊆ N) :=
  WallGSL.LorentzianMetric.main_terminates st Sgen N X g₀ hN hdec hSC hGSL W a hW hWa
