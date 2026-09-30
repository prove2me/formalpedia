-- Prove2me | solution 1 for PhilipponMultiplicity.normalized_jet_translation_germ
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T10:45:42.126987+00:00
-- url     : https://prove2.me/submissions/a6f3239b-6edb-4066-9e6f-3960afd15c53

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  {G : EmbeddedGroupProduct K}

theorem projective_ratios_eq {ι : Type*} (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk K v hv = Projectivization.mk K w hw) (i j : ι) :
    v i / v j = w i / w j := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff K v w hv hw).mp h
  have he (k : ι) : v k = (a : K) * w k := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm
  rw [he i,he j,mul_div_mul_left _ _ a.ne_zero]

/-- Move the base point of a normalized analytic lift by a small group parameter.
The equality is a germ in the second parameter; its neighborhood may depend on
the first one, exactly as allowed by the original analytic-subgroup data. -/
theorem normalizedPullback_shift_germ (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing) :
    ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      normalizedPullback A g' b P (g + x + A.map ⟨z,hz⟩) =ᶠ[𝓝 0]
        (fun w => normalizedPullback A (g + g') b P x (z + w)) := by
  let q := g + g' + x
  have hrep := A.lift_represents q
  have hrepnear : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace),
      ∀ᶠ t in 𝓝 z, ∃ ht : t ∈ A.domain, ∀ i : G.FactorIndex,
        ∃ h : (fun j => A.lift q t ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => A.lift q t ⟨i,j⟩) h =
            G.embedding (q + A.map ⟨t,ht⟩) i := hrep.eventually_nhds
  filter_upwards [A.domain_open.mem_nhds A.zero_mem,hrepnear] with z hz hrepsz
  refine ⟨hz,?_⟩
  have hadd : Tendsto (fun w : A.ParameterSpace => z + w) (𝓝 0) (𝓝 z) := by
    have hc : ContinuousAt (fun w : A.ParameterSpace => z + w) 0 :=
      continuousAt_const.add continuousAt_id
    simpa only [add_zero] using hc.tendsto
  filter_upwards [A.lift_represents (g' + (g + x + A.map ⟨z,hz⟩)),
      hadd.eventually hrepsz] with w hleft hright
  obtain ⟨hw,hl⟩ := hleft
  obtain ⟨hzw,hr⟩ := hright
  have heq : g' + (g + x + A.map ⟨z,hz⟩) + A.map ⟨w,hw⟩ =
      q + A.map ⟨z+w,hzw⟩ := by
    rw [A.map_add ⟨z,hz⟩ ⟨w,hw⟩ hzw]
    dsimp only [q]
    abel
  unfold normalizedPullback
  apply congrArg (fun f : G.ambient.Variable → K => MvPolynomial.eval f P)
  funext v
  obtain ⟨hvl,hpl⟩ := hl v.1
  obtain ⟨hvr,hpr⟩ := hr v.1
  exact projective_ratios_eq _ _ hvl hvr
    (hpl.trans ((congrArg (fun y => G.embedding y v.1) heq).trans hpr.symm)) v.2 (b v.1)

/-- A translated normalized jet is the same jet of the original orbit germ
at the displaced parameter. This is the analytic step on printed p. 374. -/
theorem normalizedJet_translate_germ (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    {T : ℕ} (j : JetIndex A.parameterDimension T) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
      normalizedJet A g' b P j (g + x + A.map ⟨z,hz⟩) else 0) =ᶠ[𝓝 0]
      (fun z => iteratedFDeriv K j.order (normalizedPullback A (g+g') b P x) z
        (fun i => Pi.single (j.directions i) 1)) := by
  filter_upwards [normalizedPullback_shift_germ A g g' x b P] with z hz
  obtain ⟨hz,he⟩ := hz
  rw [dif_pos hz]
  unfold normalizedJet
  rw [(he.iteratedFDeriv (𝕜 := K) j.order).self_of_nhds]
  rw [iteratedFDeriv_comp_add_left]
  simp only [add_zero]


end PhilipponMultiplicity.OperatorSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' x : G.Point) (b : CoordinateChart G) (P : G.CoordinateRing)
    (T : ℕ) (j : JetIndex A.parameterDimension T) :
    (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
      normalizedJet A g' b P j (g + x + A.map ⟨z,hz⟩) else 0) =ᶠ[𝓝 0]
      (fun z => iteratedFDeriv K j.order (normalizedPullback A (g+g') b P x) z
        (fun i => Pi.single (j.directions i) 1)) := by
  exact OperatorSupport.normalizedJet_translate_germ A g g' x b P j
