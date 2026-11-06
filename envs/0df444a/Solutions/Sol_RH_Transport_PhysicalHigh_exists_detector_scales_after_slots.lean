-- Prove2me | solution 1 for RH.Transport.PhysicalHigh.exists_detector_scales_after_slots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:35.412978+00:00
-- url     : https://prove2.me/submissions/fc36bc4e-e12e-4bbf-9bc9-9c7eac42f3d3

import Definitions.Def_Transport_PhysicalHigh_DistinctSlots
import Definitions.Def_Transport_TunedCandidate
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersDetectorScales
import Definitions.Def_Transport_PhysicalHigh_Parameters
import Theorems.Thm_OAI_SevenEighths_Parameters_exists_detector_scales


set_option autoImplicit false
open RH RH.Transport RH.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators
namespace RH.Transport.PhysicalHigh
theorem _root_.solution
    (t rmin ellMin allowance : ℝ) (K : ℕ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hr : 0 < rmin)
    (hell : 0 < ellMin) (ha : 0 < allowance) :
    Nonempty (DetectorScales t K rmin ellMin allowance) := by
  let small := min allowance (t / ((K : ℝ) + 2000))
  have hsmall : 0 < small := lt_min ha (div_pos ht (by positivity))
  have hsa : small ≤ allowance := min_le_left _ _
  have hst : small ≤ t / ((K : ℝ) + 2000) := min_le_right _ _
  have hst0 : small ≤ t / 2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) K]))
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
      hdet,hphase,_,_,_,_,_⟩ :=
    OAI.SevenEighths.Parameters.exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hell hsmall (by norm_num)
  let eps := small / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepss : eps ≤ small := by dsimp [eps]; linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((K : ℝ) + 2000) * eps ≤ t := by
    have h := (le_div_iff₀ (show 0 < (K : ℝ) + 2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((K : ℝ) + 8) * eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000 * e ≤ t := by linarith only [hea, hst0]
  have hεt : 2000 * ε ≤ t := by linarith only [hεa, hst0]
  have htotal : TunedCandidate.ell ≤ 1/2 := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  let sigma := min (t / 2) (min (ellMin / 4) allowance)
  have hs : 0 < sigma := lt_min (by positivity) (lt_min (by positivity) ha)
  have hst2 : sigma ≤ t / 2 := min_le_left _ _
  have hsell : sigma ≤ ellMin / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsa' : sigma ≤ allowance := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    ε := ε, e := e, κ := κ, cost := cost, eps := eps, sigma := sigma
    epsilon_pos := hε, epsilon_small := hε1, epsilon_gap := hεgap
    epsilon_allowance := hεa.trans hsa
    e_pos := he, e_small := he1, e_slot := heell, e_allowance := hea.trans hsa
    kappa_pos := hκ, kappa_small := hκ1, cost_pos := hcost
    eps_pos := heps, eps_small := heps1, eps_allowance := hepss.trans hsa
    sigma_pos := hs, sigma_t := hst2, sigma_slot := hsell, sigma_allowance := hsa'
    detector_budget := by linarith only [hdet]
    phase_budget := hphase
    central_budget := ?_
    height_choice := ?_ }⟩
  · have htell : t * TunedCandidate.ell ≤ t/2 := by nlinarith
    linarith only [hεt, het, he8, htell, ht]
  · intro J hJ
    let τ := min ((1/200 : ℝ) * cost / 16) (min (1/800) (t / (4 * (J + 7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1/200 : ℝ) * cost / 16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t / (4 * (J + 7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ * (4 * (J + 7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ * J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ, htau, by linarith only [hτd], by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau], by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
end RH.Transport.PhysicalHigh
