-- Prove2me | solution 1 for QFS.form_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:29:00.242601+00:00
-- url     : https://prove2.me/submissions/0650e34b-6a64-4fe9-9f6c-d5b8dd0ffb89




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
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

open QFS

variable {d : ℕ}


set_option autoImplicit false

theorem solution {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfg : ∀ᵐ x ∂(volume.restrict Ω), f x = g x) : form Ω k f = form Ω k g := by
  have hmeas : volume.restrict (Ω ×ˢ Ω)
      = (volume.restrict Ω).prod (volume.restrict Ω) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  rw [form, form, hmeas]
  refine lintegral_congr_ae ?_
  have h1 : ∀ᵐ p ∂((volume.restrict Ω).prod (volume.restrict Ω)), f p.1 = g p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hfg
  have h2 : ∀ᵐ p ∂((volume.restrict Ω).prod (volume.restrict Ω)), f p.2 = g p.2 :=
    Measure.quasiMeasurePreserving_snd.ae hfg
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]
#print axioms solution
