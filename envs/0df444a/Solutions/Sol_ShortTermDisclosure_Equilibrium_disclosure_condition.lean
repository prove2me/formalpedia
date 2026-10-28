-- Prove2me | solution 1 for ShortTermDisclosure.Equilibrium.disclosure_condition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T00:24:41.080915+00:00
-- url     : https://prove2.me/submissions/411f8f6b-f511-411a-be0c-786dc56e3603

import Mathlib
import Definitions.Def_ShortTermDisclosure_Equilibrium_Model

namespace Aux_STD_dc

open ShortTermDisclosure.Equilibrium MeasureTheory

lemma cm_eq (muhi t : ℝ) (ht : t ≤ muhi) : condMeanAbove muhi t = (t + muhi) / 2 := by
  unfold condMeanAbove
  split_ifs with h
  · rw [integral_id]
    have : muhi - t ≠ 0 := by linarith
    field_simp
    ring
  · have : t = muhi := le_antisymm ht (not_lt.mp h)
    rw [this]; ring

lemma thr (η muhi x t : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hx : muhi / 2 < x)
    (hbr : IsSHBestResponse η muhi x t) : (2 - η) * t = 2 * x - η * muhi := by
  obtain ⟨ht0, ht1, hup, hlow⟩ := hbr
  have hcm := cm_eq muhi t ht1
  have hmu : 0 ≤ muhi := le_trans ht0 ht1
  have htpos : 0 < t := by
    by_contra h
    push_neg at h
    have h0 : t = 0 := le_antisymm h ht0
    have := hup 0 ⟨le_rfl, hmu⟩ (by rw [h0])
    unfold netBenefit at this
    rw [hcm, h0] at this
    nlinarith [mul_le_mul_of_nonneg_right hη1 hmu]
  have g1 : 0 ≤ η * ((t + muhi) / 2) + (1 - η) * t - x := by
    have := hup t ⟨ht0, ht1⟩ le_rfl
    unfold netBenefit at this; rwa [hcm] at this
  have g2 : η * ((t + muhi) / 2) + (1 - η) * t - x ≤ 0 := by
    by_contra hg
    push_neg at hg
    set g := η * ((t + muhi) / 2) + (1 - η) * t - x with hgd
    set ε := min t g / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min htpos hg)
    have hεt : ε ≤ t / 2 := by rw [hε]; linarith [min_le_left t g]
    have hεg : ε ≤ g / 2 := by rw [hε]; linarith [min_le_right t g]
    have := hlow (t - ε) ⟨by linarith, by linarith⟩ (by linarith)
    unfold netBenefit at this
    rw [hcm] at this
    nlinarith
  nlinarith

lemma mv (muhi t v : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ muhi) :
    managerValue muhi t v = (t * v + (muhi ^ 2 - t ^ 2) / 2) / muhi := by
  unfold managerValue
  congr 1
  set f : ℝ → ℝ := fun mu => if t ≤ mu then mu else v with hf
  have hae : ∀ᵐ mu ∂(volume : Measure ℝ), mu ≠ t := by
    rw [ae_iff]
    simp
  have e1 : ∀ᵐ mu ∂(volume : Measure ℝ), mu ∈ Set.uIoc 0 t → f mu = v := by
    filter_upwards [hae] with mu hmu hmem
    rw [Set.uIoc_of_le ht0] at hmem
    have : mu < t := lt_of_le_of_ne hmem.2 hmu
    simp [hf, not_le.mpr this]
  have e2 : Set.EqOn f (fun x => x) (Set.uIcc t muhi) := by
    intro mu hmu
    rw [Set.uIcc_of_le ht1] at hmu
    simp [hf, hmu.1]
  have i1 : IntervalIntegrable f volume 0 t := by
    refine (intervalIntegrable_const (c := v)).congr_uIoo (fun mu hm => ?_)
    simp only [Set.uIoo, min_eq_left ht0, max_eq_right ht0, Set.mem_Ioo] at hm
    simp [hf, not_le.mpr hm.2]
  have i2 : IntervalIntegrable f volume t muhi :=
    (continuous_id.intervalIntegrable t muhi).congr
      (fun mu hm => (e2 (Set.uIoc_subset_uIcc hm)).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    intervalIntegral.integral_congr_ae e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul, sub_zero] <;> ring

end Aux_STD_dc

open ShortTermDisclosure.Equilibrium Aux_STD_dc in
theorem solution (P : Params) (hP : P.Standing)
    (η v N tD tN : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv : v ∈ Set.Icc P.vlo P.vhi) (hN : N ∈ Set.Icc P.vlo P.vhi)
    (hD : IsSHBestResponse η P.muhi v tD)
    (hND : IsSHBestResponse η P.muhi N tN) :
    managerValue P.muhi tD v - managerValue P.muhi tN v =
      (v - N) / P.muhi *
        (lam η * (1 + lam η) * P.muhi +
          (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N)) ∧
    (managerValue P.muhi tN v ≤ managerValue P.muhi tD v ↔
      0 ≤ (v - N) *
        (lam η * (1 + lam η) * P.muhi +
          (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N))) ∧
    (N ≤ v → managerValue P.muhi tN v ≤ managerValue P.muhi tD v) := by
  obtain ⟨h1, h2, h3, -, -⟩ := hP
  have hmu : 0 < P.muhi := by linarith [hv.1]
  have hvx : P.muhi / 2 < v := lt_of_lt_of_le h1 hv.1
  have hNx : P.muhi / 2 < N := lt_of_lt_of_le h1 hN.1
  have hvm : v < P.muhi := lt_of_le_of_lt hv.2 h3
  have tDe := thr η P.muhi v tD hη0 hη1 hvx hD
  have tNe := thr η P.muhi N tN hη0 hη1 hNx hND
  have h2η : 0 < 2 - η := by linarith
  have hlam : lam η = η / (2 - η) := rfl
  have tD' : tD = (1 + lam η) * v - lam η * P.muhi := by
    rw [hlam]; field_simp; linarith
  have tN' : tN = (1 + lam η) * N - lam η * P.muhi := by
    rw [hlam]; field_simp; linarith
  rw [mv P.muhi tD v hD.1 hD.2.1, mv P.muhi tN v hND.1 hND.2.1]
  have key : (tD * v + (P.muhi ^ 2 - tD ^ 2) / 2) / P.muhi -
      (tN * v + (P.muhi ^ 2 - tN ^ 2) / 2) / P.muhi =
      (v - N) / P.muhi *
        (lam η * (1 + lam η) * P.muhi +
          (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N)) := by
    rw [tD', tN']
    field_simp
    ring
  refine ⟨key, ?_, ?_⟩
  · rw [← sub_nonneg, key, div_mul_eq_mul_div]
    exact div_nonneg_iff.trans ⟨fun h => by
      rcases h with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · linarith, fun h => Or.inl ⟨h, hmu.le⟩⟩
  · intro hNv
    rw [← sub_nonneg, key]
    have hl0 : 0 ≤ lam η := by rw [hlam]; exact div_nonneg hη0 h2η.le
    have hB : 0 ≤ lam η * (1 + lam η) * P.muhi +
        (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N) := by
      have : lam η * (1 + lam η) * P.muhi +
          (1 + lam η) * ((1 - lam η) / 2 * v - (1 + lam η) / 2 * N) =
          (1 + lam η) * (lam η * (P.muhi - v) + (1 + lam η) / 2 * (v - N)) := by ring
      rw [this]
      apply mul_nonneg (by linarith)
      have := mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ P.muhi - v)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + lam η) / 2) (by linarith : (0:ℝ) ≤ v - N)
      linarith
    exact mul_nonneg (div_nonneg (by linarith) hmu.le) hB
