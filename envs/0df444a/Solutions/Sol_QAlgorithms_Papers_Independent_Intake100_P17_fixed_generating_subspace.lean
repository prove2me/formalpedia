-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P17.fixed_generating_subspace
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:38:37.301183+00:00
-- url     : https://prove2.me/submissions/43783f41-0557-4462-b0ca-ca42aab3a104

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17

noncomputable section

open scoped BigOperators Topology

open MeasureTheory

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Intake100.P17 in
theorem solution
    {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (tau : G ≃* G) (htau : Function.Involutive tau) (htaucont : Continuous tau)
    (R : ReflectionAction G tau E) (hcont : ∀ v, Continuous (fun g => R.pi g v))
    (S : Set G) (hone : (1 : G) ∈ closure S)
    (F : Submodule ℂ E) (hclosed : IsClosed (F : Set E))
    (hpos : ThetaPositive R.theta (orbitSpan R S F)) :
    F ≤ orbitSpan R S F ∧
      ((∀ v ∈ F, R.theta v ∈ F) ↔ ∀ v ∈ F, R.theta v = v) := by
  have hsub : F ≤ orbitSpan R S F := by
    intro w hw
    have hmaps : Set.MapsTo (fun g => R.pi g w) S
        (Submodule.span ℂ {v | ∃ s ∈ S, ∃ w ∈ F, v = R.pi s w} : Set E) := by
      intro s hs
      exact Submodule.subset_span ⟨s, hs, w, hw, rfl⟩
    have h1 := map_mem_closure (hcont w) hone hmaps
    simp only [R.one_apply] at h1
    unfold orbitSpan
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact h1
  refine ⟨hsub, ⟨?_, ?_⟩⟩
  · intro hθ v hv
    set u := v - R.theta v with hu
    have huF : u ∈ F := F.sub_mem hv (hθ v hv)
    have hθu : R.theta u = -u := by
      rw [hu, map_sub, R.theta_involutive v, neg_sub]
    have hnn := (hpos u (hsub huF)).2
    rw [hθu, inner_neg_right, Complex.neg_re] at hnn
    have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
    rw [hre] at hnn
    have hn2 : ‖u‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    have hu0 : u = 0 := norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hn2)
    rw [hu, sub_eq_zero] at hu0
    exact hu0.symm
  · intro hfix v hv
    rw [hfix v hv]
    exact hv
