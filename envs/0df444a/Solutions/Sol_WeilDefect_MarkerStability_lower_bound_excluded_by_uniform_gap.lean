-- Prove2me | solution 1 for WeilDefect.MarkerStability.lower_bound_excluded_by_uniform_gap
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T07:12:11.917656+00:00
-- url     : https://prove2.me/submissions/4c7d0e58-0fa5-4375-9530-492f917e84a8

import Definitions.Def_WeilMarker_regularized_cost
open scoped InnerProductSpace ComplexOrder Topology
open Filter WeilDefect.MarkerStability
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
theorem solution {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (G : ι → K →L[ℂ] K) (G₀ : K →L[ℂ] K) (β θ : ℝ) (hβ : β < θ)
    (hself : ∀ᶠ i in l, IsSelfAdjoint (G i))
    (hgap : ∀ᶠ i in l, ¬ β • (1 : K →L[ℂ] K) ≤ G i)
    (hlim : Tendsto G l (nhds G₀)) :
    ¬ θ • (1 : K →L[ℂ] K) ≤ G₀ := by
  intro hhalf
  have hclosed : IsClosed {T : K →L[ℂ] K | star T = T} :=
    isClosed_eq continuous_star continuous_id
  have hself₀ : IsSelfAdjoint G₀ := hclosed.mem_of_tendsto hlim hself
  have hη : 0 < θ - β := sub_pos.mpr hβ
  have hev : ∀ᶠ i in l, ‖G₀ - G i‖ < θ - β := by
    have hd : Tendsto (fun i => ‖G₀ - G i‖) l (nhds (0 : ℝ)) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ι => G₀) l (nhds G₀)).sub hlim).norm
    exact (tendsto_order.mp hd).2 _ (by simpa using hη)
  have hfalse : ∀ᶠ i in l, False := by
    filter_upwards [hself, hgap, hev] with i hi hnot hnorm
    have hd := IsSelfAdjoint.le_algebraMap_norm_self (hself₀.sub hi)
    have he : G₀ - G i ≤ (θ - β) • (1 : K →L[ℂ] K) := by
      exact hd.trans (by simpa only [Algebra.algebraMap_eq_smul_one] using
        smul_le_smul_of_nonneg_right hnorm.le (zero_le_one : (0 : K →L[ℂ] K) ≤ 1))
    apply hnot
    have hh := hhalf.trans (sub_le_iff_le_add.mp he)
    have hs : θ • (1 : K →L[ℂ] K) - (θ - β) • 1 = β • 1 := by
      rw [sub_smul]
      abel
    exact hs ▸ (sub_le_iff_le_add.mpr (by simpa only [add_comm] using hh))
  obtain ⟨i, hi⟩ := hfalse.exists
  exact hi
