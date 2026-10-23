-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P08.nonnegativeSummandsLocalContinuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:39:41.153791+00:00
-- url     : https://prove2.me/submissions/a7a0681d-2bf5-46c2-ba29-5004f7b27fce

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

noncomputable section

open Filter Topology

open scoped BigOperators ENNReal

theorem x8_main {X : Type*} [MetricSpace X]
    {K : Type*} [Fintype K] (f : K → X → ℝ≥0∞)
    (hf : ∀ i, LowerSemicontinuous (f i))
    (x : ℕ → X) (x0 : X) (hx : Tendsto x atTop (nhds x0))
    (hFinite : (∑ i, f i x0) < ⊤)
    (hSum : Tendsto (fun k => ∑ i, f i (x k)) atTop (nhds (∑ i, f i x0))) :
    ∀ i, f i x0 < ⊤ ∧ Tendsto (fun k => f i (x k)) atTop (nhds (f i x0)) := by
  classical
  intro i
  set R : X → ℝ≥0∞ := fun y => ∑ j ∈ Finset.univ.erase i, f j y with hRdef
  have hS : ∀ y, ∑ j, f j y = f i y + R y := fun y =>
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hR : LowerSemicontinuous R :=
    lowerSemicontinuous_sum (fun j _ => hf j)
  have hRtop : R x0 < ⊤ := lt_of_le_of_lt (by rw [hS]; exact le_add_self) hFinite
  refine ⟨lt_of_le_of_lt (by rw [hS]; exact le_self_add) hFinite, ?_⟩
  rw [tendsto_order]
  refine ⟨fun a ha => hx.eventually (hf i x0 a ha), fun b hb => ?_⟩
  -- find r ≤ R x0 with S0 < b + r and eventually r ≤ R (x k)
  have hlt : f i x0 + R x0 < b + R x0 := ENNReal.add_lt_add_right hRtop.ne hb
  obtain ⟨r, hr1, hr2⟩ : ∃ r, f i x0 + R x0 < b + r ∧ ∀ᶠ k in atTop, r ≤ R (x k) := by
    by_cases h0 : R x0 = 0
    · exact ⟨0, by simpa [h0] using hlt, Eventually.of_forall fun _ => zero_le⟩
    · have hopen : IsOpen {r : ℝ≥0∞ | f i x0 + R x0 < b + r} :=
        isOpen_lt continuous_const (continuous_const.add continuous_id)
      obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds (hopen.mem_nhds hlt)
        ⟨0, pos_iff_ne_zero.mpr h0⟩
      obtain ⟨r, hlr, hrR⟩ := exists_between hl
      refine ⟨r, hsub ⟨hlr, hrR.le⟩, ?_⟩
      exact (hx.eventually (hR x0 r hrR)).mono fun _ h => h.le
  have hev : ∀ᶠ k in atTop, ∑ j, f j (x k) < b + r :=
    (tendsto_order.1 hSum).2 _ (by rw [hS]; exact hr1)
  filter_upwards [hev, hr2] with k h1 h2
  rw [hS] at h1
  by_contra hcon
  push Not at hcon
  exact absurd (add_le_add hcon h2) (not_le.mpr h1)

open QAlgorithms.Papers.Independent.Frontier18.P08 in
theorem solution {X : Type*} [MetricSpace X]
    {K : Type*} [Fintype K] (f : K → X → ℝ≥0∞)
    (hf : ∀ i, LowerSemicontinuous (f i))
    (x : ℕ → X) (x0 : X) (hx : Tendsto x atTop (nhds x0))
    (hFinite : (∑ i, f i x0) < ⊤)
    (hSum : Tendsto (fun k => ∑ i, f i (x k)) atTop (nhds (∑ i, f i x0))) :
    ∀ i, f i x0 < ⊤ ∧ Tendsto (fun k => f i (x k)) atTop (nhds (f i x0)) :=
  x8_main f hf x x0 hx hFinite hSum
