-- Prove2me | solution 1 for StochHiddenConvex.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:34:10.893859+00:00
-- url     : https://prove2.me/submissions/c8090a31-2180-4162-b97b-b056c28e2d4e

import Mathlib
import Definitions.Def_StochHiddenConvex_Model_G
import Definitions.Def_StochHiddenConvex_Model_GlobalModel

open MeasureTheory

open StochHiddenConvex in
theorem solution {d : ℕ} (M : Model d) [IsProbabilityMeasure M.P]
    (hmono : M.MonotoneGlobal) (x : Vec d)
    (hint : ∀ i, Integrable (fun s => M.phi i (M.lo i) (s i)) M.P ∧
      Integrable (fun s => M.phi i (M.hi i) (s i)) M.P ∧
      Integrable (fun s => M.phi i (x i) (s i)) M.P) :
    M.g (M.projBox x) = M.projU (M.g x) := by
  have mono : ∀ i (y y' : ℝ), Integrable (fun s => M.phi i y (s i)) M.P →
      Integrable (fun s => M.phi i y' (s i)) M.P → y ≤ y' → M.gc i y ≤ M.gc i y' := by
    intro i y y' hy hy' hle
    unfold Model.gc
    exact integral_mono_ae hy hy' (hmono.mono fun s hs => hs i hle)
  unfold Model.g Model.projBox Model.projU
  congr 1
  funext i
  show M.gc i (max (M.lo i) (min (M.hi i) (x i))) =
    max (M.gc i (M.lo i)) (min (M.gc i (M.hi i)) (M.gc i (x i)))
  obtain ⟨ha, hb, hc⟩ := hint i
  rcases le_total (M.hi i) (x i) with h1 | h1
  · rw [min_eq_left h1, min_eq_left (mono i _ _ hb hc h1)]
    rcases le_total (M.lo i) (M.hi i) with h2 | h2
    · rw [max_eq_right h2, max_eq_right (mono i _ _ ha hb h2)]
    · rw [max_eq_left h2, max_eq_left (mono i _ _ hb ha h2)]
  · rw [min_eq_right h1, min_eq_right (mono i _ _ hc hb h1)]
    rcases le_total (M.lo i) (x i) with h2 | h2
    · rw [max_eq_right h2, max_eq_right (mono i _ _ ha hc h2)]
    · rw [max_eq_left h2, max_eq_left (mono i _ _ hc ha h2)]
