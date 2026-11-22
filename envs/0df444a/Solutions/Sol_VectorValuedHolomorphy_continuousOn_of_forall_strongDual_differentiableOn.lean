-- Prove2me | solution 1 for VectorValuedHolomorphy.continuousOn_of_forall_strongDual_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:55:14.144814+00:00
-- url     : https://prove2.me/submissions/5586e064-56fb-4207-b908-1b7871b1ff97

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_continuousOn_of_forall_strongDual_differentiableOn

/-- The vector space `E`, regarded as a seminormed space for the seminorm `p`. -/
def SN {E : Type*} [AddCommGroup E] [Module ℂ E] (_p : Seminorm ℂ E) : Type _ := E

section SN

variable {E : Type*} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E)

noncomputable instance : SeminormedAddCommGroup (SN p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := E) p.toAddGroupSeminorm

noncomputable instance : Module ℂ (SN p) := inferInstanceAs (Module ℂ E)

noncomputable instance : NormedSpace ℂ (SN p) :=
  ⟨fun c x => (map_smul_eq_mul p c x).le⟩

/-- The identity map from `E` to the seminormed space `(E, p)`. -/
def toSN : E →ₗ[ℂ] SN p := LinearMap.id

theorem norm_toSN (x : E) : ‖toSN p x‖ = p x := rfl

end SN

/-- **Mackey's theorem**, seminorm form: a subset of a topological vector space on which every
continuous linear functional is bounded is bounded for every continuous seminorm. -/
theorem exists_seminorm_le_of_dual_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (p : Seminorm ℂ E) (hp : Continuous p)
    {s : Set E} (h : ∀ ℓ : StrongDual ℂ E, ∃ C : ℝ, ∀ x ∈ s, ‖ℓ x‖ ≤ C) :
    ∃ C : ℝ, ∀ x ∈ s, p x ≤ C := by
  have hι : Continuous (toSN p) := by
    refine (Metric.continuous_iff' (f := fun y : E => toSN p y)).mpr fun x ε hε => ?_
    have hcont : Continuous (fun y : E => p (y - x)) :=
      hp.comp (continuous_id.sub continuous_const)
    have hsmall := (hcont.continuousAt (x := x)).eventually_lt continuousAt_const
      (show p (x - x) < ε by simpa using hε)
    simp only [dist_eq_norm, ← map_sub, norm_toSN]
    exact hsmall
  let ev (x : s) : StrongDual ℂ (StrongDual ℂ (SN p)) :=
    NormedSpace.inclusionInDoubleDual ℂ (SN p) (toSN p x)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := ev) fun ℓ => by
    obtain ⟨C, hC⟩ := h (ℓ.comp ⟨toSN p, hι⟩)
    exact ⟨C, fun x => hC x x.property⟩
  refine ⟨C, fun x hx => ?_⟩
  rw [← norm_toSN p x, ← (NormedSpace.inclusionInDoubleDualLi (E := SN p) ℂ).norm_map (toSN p x)]
  exact hC ⟨x, hx⟩

end Sol_VectorValuedHolomorphy_continuousOn_of_forall_strongDual_differentiableOn

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → E} (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U) :
    ContinuousOn f U := by
  intro z hz
  rw [continuousWithinAt_iff_continuousAt (hU.mem_nhds hz)]
  unfold ContinuousAt
  rw [(PolynormableSpace.withSeminorms ℂ E).tendsto_nhds f (f z)]
  intro q ε hε
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  -- the difference quotients of `f` at `z` form a weakly bounded set
  have hD : ∀ ℓ : StrongDual ℂ E, ∃ C : ℝ,
      ∀ x ∈ (fun w : ℂ => (w - z)⁻¹ • (f w - f z)) '' (closedBall z R \ {z}), ‖ℓ x‖ ≤ C := by
    intro ℓ
    have hd : DifferentiableOn ℂ (dslope (fun w => ℓ (f w)) z) U :=
      (Complex.differentiableOn_dslope (hU.mem_nhds hz)).2 (hf ℓ)
    obtain ⟨C, hC⟩ := ((isCompact_closedBall z R).image_of_continuousOn
      (hd.continuousOn.mono hsub)).isBounded.exists_norm_le
    refine ⟨C, ?_⟩
    rintro _ ⟨w, ⟨hw, hwz⟩, rfl⟩
    have hval := hC _ ⟨w, hw, rfl⟩
    rw [dslope_of_ne _ hwz, slope_def_module] at hval
    simpa only [map_smul, map_sub] using hval
  obtain ⟨M, hM⟩ :=
    Sol_VectorValuedHolomorphy_continuousOn_of_forall_strongDual_differentiableOn.exists_seminorm_le_of_dual_bounded
      q.1 q.2 hD
  have hM1 : 0 < max M 0 + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds z (lt_min hR (div_pos hε hM1))] with w hw
  rcases eq_or_ne w z with rfl | hwz
  · simpa using hε
  · have hwd : ‖w - z‖ < min R (ε / (max M 0 + 1)) := by
      simpa [dist_eq_norm] using hw
    have hwR : w ∈ closedBall z R := by
      rw [mem_closedBall, dist_eq_norm]
      exact (hwd.trans_le (min_le_left _ _)).le
    have h1 : q.1 ((w - z)⁻¹ • (f w - f z)) ≤ M := hM _ ⟨w, ⟨hwR, hwz⟩, rfl⟩
    have h2 : f w - f z = (w - z) • ((w - z)⁻¹ • (f w - f z)) := by
      rw [smul_inv_smul₀ (sub_ne_zero.2 hwz)]
    have h3 : ‖w - z‖ * (max M 0 + 1) < ε := by
      have := hwd.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hM1] at this
    show q.1 (f w - f z) < ε
    rw [h2, map_smul_eq_mul]
    calc ‖w - z‖ * q.1 ((w - z)⁻¹ • (f w - f z))
        ≤ ‖w - z‖ * (max M 0 + 1) := by
          gcongr
          exact h1.trans ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one))
      _ < ε := h3
