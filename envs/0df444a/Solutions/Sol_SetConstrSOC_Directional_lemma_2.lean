-- Prove2me | solution 1 for SetConstrSOC.Directional.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:51:40.59436+00:00
-- url     : https://prove2.me/submissions/c9c77e51-6560-49c9-b8a2-f7376ff9c53e

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

set_option autoImplicit false
open Filter Asymptotics
open scoped Topology
open SetConstrSOC.Directional


theorem solution {m n : ℕ} (C : E m → Set (E n)) (u : E m) (x : E n) :
    Filter.liminf (fun u' => EMetric.infEdist x (C u')) (𝓝 u) =
      EMetric.infEdist x (outerLimit C u) := by
  apply le_antisymm
  · refine le_iInf₂ fun v hv => ?_
    obtain ⟨uk, vk, huk, hvk, hmem⟩ := hv
    calc Filter.liminf (fun u' => EMetric.infEdist x (C u')) (𝓝 u)
        ≤ Filter.liminf (fun u' => EMetric.infEdist x (C u')) (Filter.map uk atTop) :=
          Filter.liminf_le_liminf_of_le huk
      _ = Filter.liminf (fun k => EMetric.infEdist x (C (uk k))) atTop := by
          rw [← Filter.liminf_comp]; rfl
      _ ≤ Filter.liminf (fun k => edist x (vk k)) atTop :=
          Filter.liminf_le_liminf (Eventually.of_forall fun k => Metric.infEDist_le_edist_of_mem (hmem k))
      _ = edist x v := (tendsto_const_nhds.edist hvk).liminf_eq
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, hLc, hcI⟩ := exists_between hlt
    have hfreq : ∃ᶠ u' in 𝓝 u, EMetric.infEdist x (C u') < c :=
      Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hLc
    have hj : ∀ j : ℕ, ∃ u', dist u' u < 1 / ((j : ℝ) + 1) ∧ EMetric.infEdist x (C u') < c := by
      intro j
      obtain ⟨u', hu', h⟩ := (Metric.nhds_basis_ball.frequently_iff.mp hfreq) (1 / ((j : ℝ) + 1))
        (by positivity)
      exact ⟨u', by simpa [Metric.mem_ball] using hu', h⟩
    choose uj huj hfj using hj
    have hv : ∀ j, ∃ v ∈ C (uj j), edist x v < c := fun j => Metric.infEDist_lt_iff.mp (hfj j)
    choose vj hvC hvd using hv
    have hcT : c ≠ ⊤ := (hcI.trans_le le_top).ne
    have hb : ∀ j, vj j ∈ Metric.closedBall x c.toReal := by
      intro j
      have : edist x (vj j) ≤ ENNReal.ofReal c.toReal := by
        rw [ENNReal.ofReal_toReal hcT]; exact (hvd j).le
      rw [Metric.mem_closedBall, dist_comm]
      exact (edist_le_ofReal ENNReal.toReal_nonneg).mp this
    obtain ⟨vb, -, φ, hφ, hvb⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hb
    have hu : Tendsto uj atTop (𝓝 u) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun j => dist_nonneg) (fun j => (huj j).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    have hvbO : vb ∈ outerLimit C u := ⟨uj ∘ φ, vj ∘ φ, hu.comp hφt, hvb, fun k => hvC (φ k)⟩
    have h1 : EMetric.infEdist x (outerLimit C u) ≤ edist x vb :=
      Metric.infEDist_le_edist_of_mem hvbO
    have h2 : edist x vb ≤ c :=
      le_of_tendsto' (tendsto_const_nhds.edist hvb) (fun k => (hvd (φ k)).le)
    exact absurd (h1.trans h2) (not_le.mpr hcI)

