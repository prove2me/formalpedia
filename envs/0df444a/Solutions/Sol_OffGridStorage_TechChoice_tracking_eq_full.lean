-- Prove2me | solution 1 for OffGridStorage.TechChoice.tracking_eq_full
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:57:58.241298+00:00
-- url     : https://prove2.me/submissions/9982eeee-1395-40f2-a3d8-a1a693c189eb

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

open MeasureTheory

open OffGridStorage.TechChoice in
theorem solution (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hKL : K ≤ p.DL) :
    profitTR p Q K = profitF p Q K := by
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp
  set F : ℝ → ℝ := fun x => min x p.DH + min (p.e * pos (x - p.DH)) K with hFdef
  have hFc : Continuous F := by
    show Continuous (fun x => min x p.DH + min (p.e * max 0 (x - p.DH)) K)
    exact (continuous_id.min continuous_const).add
      ((continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const))).min
        continuous_const)
  have hcharge : ∀ (q : Fin p.T → ℝ) (n : ℕ), charge p K q n = 0 := by
    intro q n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [charge, nextCharge, pos]
      apply max_eq_left
      have := min_le_right (afterDay p (charge p K q n)
        (if h : n < p.T then q ⟨n, h⟩ else 0)) K
      linarith
  have hafter : ∀ q : ℝ, afterDay p 0 q = p.e * pos (q - p.DH) := by
    intro q
    unfold afterDay pos
    rcases le_total q p.DH with h | h
    · rw [max_eq_left (by linarith : q - p.DH ≤ 0), max_eq_right (by linarith : 0 ≤ p.DH - q)]
      rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith : 0 ≤ q - p.DH), max_eq_left (by linarith : p.DH - q ≤ 0)]
      rw [max_eq_right (by nlinarith)]; ring
  have hper : ∀ q : ℝ, periodRevenueTR p K 0 q = F q := by
    intro q
    unfold periodRevenueTR
    rw [hafter, min_eq_left hKL, zero_add]
  have hrev : ∀ u : Fin p.T → ℝ, revenueTR p K (fun t => Q * u t) = ∑ t, F (Q * u t) := by
    intro u
    unfold revenueTR
    apply Finset.sum_congr rfl
    intro t _
    rw [hcharge, hper]
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hcube : IsCompact (unitCube p.T) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hint : ∀ t : Fin p.T, ∫ u in unitCube p.T, F (Q * u t) =
      ∫ v in Set.Icc (0:ℝ) 1, F (Q * v) := by
    intro t
    unfold unitCube
    rw [volume_pi, Measure.restrict_pi_pi]
    have hcF : Continuous (fun v : ℝ => F (Q * v)) := hFc.comp (continuous_const.mul continuous_id)
    exact integral_comp_eval (X := fun _ : Fin p.T => ℝ)
      (μ := fun _ : Fin p.T => volume.restrict (Set.Icc (0:ℝ) 1)) (i := t)
      (f := fun v : ℝ => F (Q * v)) hcF.aestronglyMeasurable
  have hsum : ∫ u in unitCube p.T, revenueTR p K (fun t => Q * u t) =
      (p.T : ℝ) * ∫ v in Set.Icc (0:ℝ) 1, F (Q * v) := by
    simp_rw [hrev]
    rw [integral_finset_sum]
    · simp_rw [hint]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro t _
      exact ((hFc.comp (continuous_const.mul (continuous_apply t))).continuousOn).integrableOn_compact
        hcube
  unfold profitTR profitF
  rw [hsum]
  ring
