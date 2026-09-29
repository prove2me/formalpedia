-- Prove2me | solution 1 for QFS.lintegral_swap_of_fibre_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:02.539946+00:00
-- url     : https://prove2.me/submissions/ebb7bc20-3d15-444d-9ea0-7dcfc6eb6061




import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_LebesgueDiff
import Definitions.Def_QFS_LebesgueDiff2
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Definitions.Def_QFS_Section32
import Definitions.Def_QFS_AppendixA
import Definitions.Def_QFS_BeyondThePaper
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Metric Set MeasureTheory
open scoped Real InnerProductSpace ENNReal

open QFS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


set_option autoImplicit false

theorem solution {d : ℕ}
    {W : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))}
    (hWm : ∀ t, MeasurableSet (W t))
    (hgraph : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      p.2 ∈ W p.1})
    {w : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hwm : Measurable w)
    {G : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hG : Measurable G)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hfibm : ∀ z, MeasurableSet {t | z ∈ W t})
    (hfib : ∀ z, ∫⁻ t in {t | z ∈ W t}, w t ≤ Ψ z) :
    ∫⁻ t, w t * ∫⁻ z in W t, G z ≤ ∫⁻ z, G z * Ψ z := by
  have hstep : ∀ t, w t * ∫⁻ z in W t, G z = ∫⁻ z, w t * (W t).indicator G z := by
    intro t
    rw [lintegral_const_mul _ (hG.indicator (hWm t)), lintegral_indicator (hWm t)]
  have hunc : AEMeasurable (Function.uncurry fun t z => w t * (W t).indicator G z) volume := by
    refine Measurable.aemeasurable ?_
    have heq : (Function.uncurry fun t z => w t * (W t).indicator G z)
        = fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          w p.1 * {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ W p.1}.indicator (fun q => G q.2) p := by
      funext p
      obtain ⟨t, z⟩ := p
      simp only [Function.uncurry]
      by_cases hp : z ∈ W t
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
          (show (t, z) ∈ {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ W p.1} from hp)]
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem
          (show (t, z) ∉ {p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
            p.2 ∈ W p.1} from hp)]
    rw [heq]
    exact (hwm.comp measurable_fst).mul ((hG.comp measurable_snd).indicator hgraph)
  calc ∫⁻ t, w t * ∫⁻ z in W t, G z
      = ∫⁻ t, ∫⁻ z, w t * (W t).indicator G z := lintegral_congr hstep
    _ = ∫⁻ z, ∫⁻ t, w t * (W t).indicator G z := lintegral_lintegral_swap hunc
    _ ≤ ∫⁻ z, G z * Ψ z := by
        refine lintegral_mono fun z => ?_
        have hpw : ∀ t, w t * (W t).indicator G z
            = {t | z ∈ W t}.indicator (fun t => G z * w t) t := by
          intro t
          by_cases hp : z ∈ W t
          · rw [Set.indicator_of_mem hp,
              Set.indicator_of_mem (show t ∈ {t | z ∈ W t} from hp)]
            ring
          · rw [Set.indicator_of_notMem hp,
              Set.indicator_of_notMem (show t ∉ {t | z ∈ W t} from hp)]
            simp
        calc ∫⁻ t, w t * (W t).indicator G z
            = ∫⁻ t, {t | z ∈ W t}.indicator (fun t => G z * w t) t := lintegral_congr hpw
          _ = ∫⁻ t in {t | z ∈ W t}, G z * w t := lintegral_indicator (hfibm z) _
          _ = G z * ∫⁻ t in {t | z ∈ W t}, w t := lintegral_const_mul _ hwm
          _ ≤ G z * Ψ z := mul_le_mul' le_rfl (hfib z)
#print axioms solution
