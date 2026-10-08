-- Prove2me | solution 1 for PhilipponMultiplicity.exists_normalized_analytic_group_chart
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-03T09:32:07.104123+00:00
-- url     : https://prove2.me/submissions/f82b3114-c841-46ff-9051-f24a6ddee002

import Theorems.Thm_PhilipponMultiplicity_exists_nonsingular_normalized_polynomial_presentation
import Theorems.Thm_PhilipponMultiplicity_normalized_group_neighborhood_zariski_interior
import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity.ImplicitPolynomialChart

/-- An invertible augmented polynomial Jacobian gives analytic parameters for
the zero fiber, with local inverse the prescribed linear projection. -/
theorem exists_analytic_fiber_chart
    {K σ : Type*} [NontriviallyNormedField K] [CompleteSpace K] [Fintype σ]
    (r d : ℕ) (P : Fin r → MvPolynomial σ K) (a : σ → K)
    (ρ : (σ → K) →L[K] (Fin d → K))
    (L : (σ → K) ≃L[K] ((Fin r → K) × (Fin d → K)))
    (hP : ∀ i, MvPolynomial.eval a (P i) = 0)
    (hderiv : HasFDerivAt
      (fun v : σ → K => ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
      (L : (σ → K) →L[K] ((Fin r → K) × (Fin d → K))) a) :
    ∃ g : (Fin d → K) → (σ → K), g 0 = a ∧ AnalyticAt K g 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K),
        (∀ i, MvPolynomial.eval (g u) (P i) = 0) ∧ ρ (g u-a) = u) ∧
      (∀ᶠ v in 𝓝 a, (∀ i, MvPolynomial.eval v (P i) = 0) →
        g (ρ (v-a)) = v) := by
  classical
  let F (v : σ → K) := ((fun i => MvPolynomial.eval v (P i)), ρ (v-a))
  have hFa : F a = 0 := by
    apply Prod.ext
    · funext i
      exact hP i
    · simp [F]
  have hF : AnalyticAt K F a := by
    have hcoord (j : σ) : AnalyticAt K (fun v : σ → K => v j) a :=
      (ContinuousLinearMap.proj (R := K) j).analyticAt a
    have hpoly : AnalyticAt K (fun v : σ → K => fun i => MvPolynomial.eval v (P i)) a :=
      AnalyticAt.pi (fun i => AnalyticAt.aeval_mvPolynomial hcoord (P i))
    have hproj : AnalyticAt K (fun v : σ → K => ρ (v-a)) a :=
      (ρ.analyticAt _).comp (f := fun v : σ → K => v-a) (x := a)
        (analyticAt_id.sub analyticAt_const)
    exact hpoly.prod hproj
  have hs : HasStrictFDerivAt F
      (L : (σ → K) →L[K] ((Fin r → K) × (Fin d → K))) a := by
    rw [← hderiv.fderiv]
    exact hF.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph F
  have he : a ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hinv : AnalyticAt K e.symm (F a) :=
    e.analyticAt_symm' he hF hderiv.fderiv
  have hi0 : AnalyticAt K e.symm 0 := by simpa only [hFa] using hinv
  let g (u : Fin d → K) := e.symm (0, u)
  have hg : AnalyticAt K g 0 := hi0.comp
    (f := fun u : Fin d → K => ((0 : Fin r → K), u)) (x := (0 : Fin d → K))
    (analyticAt_const.prod analyticAt_id)
  have hg0 : g 0 = a := by
    change e.symm 0 = a
    rw [← hFa]
    exact e.left_inv he
  have hright : ∀ᶠ y in 𝓝 (0 : (Fin r → K) × (Fin d → K)), F (e.symm y) = y := by
    have h : ∀ᶠ y in 𝓝 (F a), F (e.symm y) = y := e.eventually_right_inverse' he
    simpa only [hFa] using h
  have hleft : ∀ᶠ v in 𝓝 a, e.symm (F v) = v := e.eventually_left_inverse he
  have haxis : Tendsto (fun u : Fin d → K => ((0 : Fin r → K), u)) (𝓝 0) (𝓝 0) :=
    (continuous_const.prodMk continuous_id).continuousAt
  refine ⟨g, hg0, hg, ?_, ?_⟩
  · filter_upwards [haxis.eventually hright] with u hu
    exact ⟨fun i => congrFun (congrArg Prod.fst hu) i, congrArg Prod.snd hu⟩
  · filter_upwards [hleft] with v hv hPv
    have hFv : F v = (0, ρ (v-a)) := by
      apply Prod.ext
      · funext i
        exact hPv i
      · rfl
    change e.symm (0, ρ (v-a)) = v
    simpa only [hFv] using hv

end PhilipponMultiplicity.ImplicitPolynomialChart

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Filter MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity.ImplicitPolynomialChart

theorem eq_of_common_lift
    {K : Type*} [Field K] (G : EmbeddedGroupProduct K)
    (v : G.ambient.Variable → K) (x y : G.Point)
    (hx : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i)
    (hy : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding y i) : x = y := by
  funext i
  apply Subtype.ext
  obtain ⟨hn, he⟩ := hx i
  obtain ⟨hn', he'⟩ := hy i
  exact he.symm.trans he'

/-- Extend the implicit analytic parameterization by the identity outside a
small neighborhood, and recover genuine group points from their lifts. -/
theorem normalized_chart_of_polynomial_presentation
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (d r : ℕ)
    (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
    (a : G.ambient.Variable → K)
    (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing)
    (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
    (L : (G.ambient.Variable → K) ≃L[K] ((Fin r → K) × (Fin d → K)))
    (ha : ∀ i, a ⟨i, c i⟩ = 1)
    (harep : ∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i)
    (hH : MvPolynomial.eval a H ≠ 0)
    (hP : ∀ i, MvPolynomial.eval a (P i) = 0)
    (hderiv : HasFDerivAt
      (fun v : G.ambient.Variable → K =>
        ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
      (L : (G.ambient.Variable → K) →L[K] ((Fin r → K) × (Fin d → K))) a)
    (hcut : ∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
      ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
        ((∀ i, v ⟨i, c i⟩ = 1) ∧
          ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))) :
    ∃ (φ : (Fin d → K) → G.Point) (f : (Fin d → K) → G.ambient.Variable → K),
      φ 0 = 0 ∧ AnalyticAt K f 0 ∧
      (∀ u i, f u ⟨i, c i⟩ = 1) ∧
      (∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), ρ (f u - f 0) = u) ∧
      (∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
        ∀ x : G.Point,
          (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
          φ (ρ (v - f 0)) = x) := by
  classical
  obtain ⟨g, hg0, hg, hgfiber, hginv⟩ := exists_analytic_fiber_chart r d P a ρ L hP hderiv
  have hHg : AnalyticAt K (fun u => MvPolynomial.eval (g u) H) 0 :=
    AnalyticAt.aeval_mvPolynomial (fun j => analyticAt_pi_iff.mp hg j) H
  have hHnear : ∀ᶠ u in 𝓝 (0 : Fin d → K), MvPolynomial.eval (g u) H ≠ 0 :=
    hHg.continuousAt.eventually_ne (by simpa only [hg0] using hH)
  let U : Set (Fin d → K) :=
    {u | MvPolynomial.eval (g u) H ≠ 0 ∧ ∀ i, MvPolynomial.eval (g u) (P i) = 0}
  have hU : U ∈ 𝓝 (0 : Fin d → K) := by
    filter_upwards [hHnear, hgfiber] with u hu hu'
    exact ⟨hu, hu'.1⟩
  let f (u : Fin d → K) := if u ∈ U then g u else a
  have hfg : f =ᶠ[𝓝 0] g := by
    filter_upwards [hU] with u hu
    exact if_pos hu
  have hf0 : f 0 = a := hfg.self_of_nhds.trans hg0
  have hf : AnalyticAt K f 0 := hg.congr hfg.symm
  have hffacts (u : Fin d → K) : (∀ i, f u ⟨i, c i⟩ = 1) ∧
      ∃ x : G.Point, ∀ i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding x i := by
    dsimp only [f]
    split_ifs with hu
    · exact (hcut (g u) hu.1).mp hu.2
    · exact ⟨ha, 0, harep⟩
  choose φ hφrep using fun u => (hffacts u).2
  have hφ0 : φ 0 = 0 := eq_of_common_lift G a (φ 0) 0
    (by simpa only [hf0] using hφrep 0) harep
  refine ⟨φ, f, hφ0, hf, fun u => (hffacts u).1, hφrep, ?_, ?_⟩
  · filter_upwards [hfg, hgfiber] with u hu hu'
    simpa only [hu, hf0] using hu'.2
  · rw [hf0]
    have hcoord (j : G.ambient.Variable) :
        AnalyticAt K (fun v : G.ambient.Variable → K => v j) a :=
      (ContinuousLinearMap.proj (R := K) j).analyticAt a
    have hHa : AnalyticAt K (fun v : G.ambient.Variable → K => MvPolynomial.eval v H) a :=
      AnalyticAt.aeval_mvPolynomial hcoord H
    have hproj : Continuous (fun v : G.ambient.Variable → K => ρ (v-a)) :=
      ρ.continuous.comp (continuous_id.sub continuous_const)
    have ht : Tendsto (fun v : G.ambient.Variable → K => ρ (v-a)) (𝓝 a) (𝓝 0) := by
      simpa only [sub_self, map_zero] using hproj.tendsto a
    filter_upwards [hHa.continuousAt.eventually_ne hH, ht.eventually hU, hginv]
      with v hvH hvU hvinv hvnorm x hvrep
    have hPv : ∀ i, MvPolynomial.eval v (P i) = 0 :=
      (hcut v hvH).mpr ⟨hvnorm, x, hvrep⟩
    have hfv : f (ρ (v-a)) = v := (if_pos hvU).trans (hvinv hPv)
    exact eq_of_common_lift G v (φ (ρ (v-a))) x
      (by simpa only [hfv] using hφrep (ρ (v-a))) hvrep

end PhilipponMultiplicity.ImplicitPolynomialChart

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology

namespace PhilipponMultiplicity

/-- A local inverse projection transfers density of actual coordinate
neighborhoods to the image of every parameter neighborhood. -/
theorem parameter_image_thick_of_coordinate_neighborhoods
    {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) (d : ℕ)
    (φ : (Fin d → K) → G.Point) (f : (Fin d → K) → G.ambient.Variable → K)
    (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
    (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
    (hright : ∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
      ∀ x : G.Point,
        (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
          Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
        φ (ρ (v-f 0)) = x)
    (hdense : ∀ V : Set (G.ambient.Variable → K), V ∈ 𝓝 (f 0) →
      (@interior _ G.zariskiTopology
        (@closure _ G.zariskiTopology
          {x : G.Point | ∃ v ∈ V, (∀ i, v ⟨i, c i⟩ = 1) ∧
            ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i})).Nonempty) :
    ∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
      (@interior _ G.zariskiTopology
        (@closure _ G.zariskiTopology (φ '' U))).Nonempty := by
  intro U hU
  let V : Set (G.ambient.Variable → K) := {v |
    ((∀ i, v ⟨i, c i⟩ = 1) → ∀ x : G.Point,
      (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
        φ (ρ (v-f 0)) = x) ∧ ρ (v-f 0) ∈ U}
  have hproj : Continuous (fun v : G.ambient.Variable → K => ρ (v-f 0)) :=
    ρ.continuous.comp (continuous_id.sub continuous_const)
  have ht : Tendsto (fun v : G.ambient.Variable → K => ρ (v-f 0)) (𝓝 (f 0)) (𝓝 0) := by
    simpa only [sub_self, map_zero] using hproj.tendsto (f 0)
  have hV : V ∈ 𝓝 (f 0) := hright.and (ht.eventually hU)
  letI : TopologicalSpace G.Point := G.zariskiTopology
  apply (hdense V hV).mono
  apply interior_mono
  apply closure_mono
  rintro x ⟨v, hv, hn, hr⟩
  exact ⟨ρ (v-f 0), hv.2, hv.1 hn x hr⟩

end PhilipponMultiplicity

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter Topology

namespace PhilipponMultiplicity

private theorem implicitChart_complete {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem normalized_analytic_chart_of_polynomial_presentation_and_density
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (hpresentation : ∃ (d r : ℕ)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (a : G.ambient.Variable → K)
      (P : Fin r → G.CoordinateRing) (H : G.CoordinateRing)
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K))
      (L : (G.ambient.Variable → K) ≃L[K] ((Fin r → K) × (Fin d → K))),
      (∀ i, a ⟨i, c i⟩ = 1) ∧
      (∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i) ∧
      MvPolynomial.eval a H ≠ 0 ∧
      (∀ i, MvPolynomial.eval a (P i) = 0) ∧
      HasFDerivAt
        (fun v : G.ambient.Variable → K =>
          ((fun i => MvPolynomial.eval v (P i)), ρ (v-a)))
        (L : (G.ambient.Variable → K) →L[K] ((Fin r → K) × (Fin d → K))) a ∧
      (∀ v : G.ambient.Variable → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ((∀ i, v ⟨i, c i⟩ = 1) ∧
            ∃ x : G.Point, ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
              Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i))))
    (hdensity : ∀ (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
    (a : G.ambient.Variable → K)
    (ha : ∀ i, a ⟨i, c i⟩ = 1)
    (harep : ∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i)
    (V : Set (G.ambient.Variable → K)) (hV : V ∈ 𝓝 a),
    (@interior _ G.zariskiTopology
      (@closure _ G.zariskiTopology
        {x : G.Point | ∃ v ∈ V, (∀ i, v ⟨i, c i⟩ = 1) ∧
          ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i})).Nonempty) :
    ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (f : (Fin d → K) → G.ambient.Variable → K)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K f 0 ∧
      (∀ u i, f u ⟨i, c i⟩ = 1) ∧
      (∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), ρ (f u - f 0) = u) ∧
      (∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
        ∀ x : G.Point,
          (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
          φ (ρ (v - f 0)) = x) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty) := by
  letI : CompleteSpace K := implicitChart_complete hK
  obtain ⟨d, r, c, a, P, H, ρ, L, ha, harep, hH, hP, hderiv, hcut⟩ := hpresentation
  obtain ⟨φ, f, hφ, hf, hc, hrep, hleft, hright⟩ :=
    ImplicitPolynomialChart.normalized_chart_of_polynomial_presentation
      G d r c a P H ρ L ha harep hH hP hderiv hcut
  refine ⟨d, φ, f, c, ρ, hφ, hf, hc, hrep, hleft, hright, ?_⟩
  apply parameter_image_thick_of_coordinate_neighborhoods G d φ f c ρ hright
  intro V hV
  exact hdensity c (f 0) (hc 0) (by simpa only [hφ] using hrep 0) V hV

end PhilipponMultiplicity

end

open PhilipponMultiplicity Filter Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (f : (Fin d → K) → G.ambient.Variable → K)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K f 0 ∧
      (∀ u i, f u ⟨i, c i⟩ = 1) ∧
      (∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), ρ (f u - f 0) = u) ∧
      (∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
        ∀ x : G.Point,
          (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
          φ (ρ (v - f 0)) = x) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty) := by
  exact normalized_analytic_chart_of_polynomial_presentation_and_density K hK G
    (exists_nonsingular_normalized_polynomial_presentation K hK G)
    (normalized_group_neighborhood_zariski_interior K hK G)
