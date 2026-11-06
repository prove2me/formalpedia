-- Prove2me | solution 1 for SethiChengSS.Infinite.value_kconvex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:10:34.730342+00:00
-- url     : https://prove2.me/submissions/cb2966fc-f859-4038-b985-b313aa0f750b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model
import Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_9
import Theorems.Thm_SethiChengSS_Infinite_theorem_6_1_eq_6_10
import Theorems.Thm_SethiChengSS_Infinite_vTrunc_kconvex

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

open SethiChengSS.Infinite

theorem solution {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h41 : Cond41 D)
    (h42 : Cond42 D) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ n i, BertsekasKConvex (D.K n i) (fun x => (value D α n i x).toReal) := by
  obtain ⟨hconv, hfin, _, _⟩ := theorem_6_1_eq_6_9 D α hD h42 hα0 hα1
  obtain ⟨_, ⟨û0, hû0B, hû0A⟩, hver⟩ := theorem_6_1_eq_6_10 D α hD h42 hα0 hα1
  have hkc := vTrunc_kconvex D α hD h41 h42 hα0 hα1
  have hval : ∀ n i x, value D α n i x = vLim D α n i x :=
    fun n i x => (hver û0 hû0B hû0A n i x).2.1
  -- real-valued convergence v_{n,k} → v_n
  have hlim : ∀ n i x, Tendsto (fun k => (vTrunc D α n k i x).toReal) atTop
      (𝓝 (value D α n i x).toReal) := by
    intro n i x
    rw [hval]
    exact (ENNReal.tendsto_toReal (hfin n i x).ne).comp (hconv n i x)
  intro n i z b y hz hb
  have hL : Tendsto (fun k => (vTrunc D α n k i y).toReal +
      z / b * ((vTrunc D α n k i y).toReal - (vTrunc D α n k i (y - b)).toReal)) atTop
      (𝓝 ((value D α n i y).toReal +
        z / b * ((value D α n i y).toReal - (value D α n i (y - b)).toReal))) :=
    (hlim n i y).add (((hlim n i y).sub (hlim n i (y - b))).const_mul _)
  have hR : Tendsto (fun k => D.K n i + (vTrunc D α n k i (z + y)).toReal) atTop
      (𝓝 (D.K n i + (value D α n i (z + y)).toReal)) :=
    tendsto_const_nhds.add (hlim n i (z + y))
  exact le_of_tendsto_of_tendsto' hL hR (fun k => hkc n k i z b y hz hb)
