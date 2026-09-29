-- Prove2me | solution 1 for QFS.osc_weighted_le_planar
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T05:03:06.152126+00:00
-- url     : https://prove2.me/submissions/802a5c71-2aaa-42df-97cb-6391ee29efa1





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



namespace QFSProof_osc_weighted_le_planar

lemma volume_planarBall {vs vt : EuclideanSpace ℝ (Fin 2)} {ϑ : ℝ}
    {s t : EuclideanSpace ℝ (Fin 2)} (hne : s ≠ t)
    (h1 : t - s ∉ doubleCone vs ϑ) (h2 : t - s ∉ doubleCone vt ϑ) :
    volume (planarBall vs vt ϑ s t)
      = ENNReal.ofReal ((‖t - s‖ * Real.sin ϑ ^ 2 / 2) ^ 2) * unitBallVol 2 := by
  have he : planarBall vs vt ϑ s t
      = closedBall (planarCtr vs vt s t) (‖t - s‖ * Real.sin ϑ ^ 2 / 2) := by
    ext z
    simp only [planarBall, Set.mem_ofPred_eq]
    exact ⟨fun h => h.2.2.2, fun h => ⟨hne, h1, h2, h⟩⟩
  rw [he, volume_closedBall_eq _ (by positivity)]

end QFSProof_osc_weighted_le_planar
open QFSProof_osc_weighted_le_planar

set_option autoImplicit false

theorem solution {vs vt : EuclideanSpace ℝ (Fin 2)} {ϑ : ℝ}
    {α : ℝ} (f : EuclideanSpace ℝ (Fin 2) → ℝ) {s t : EuclideanSpace ℝ (Fin 2)}
    (hne : s ≠ t) (h1 : t - s ∉ doubleCone vs ϑ) (h2 : t - s ∉ doubleCone vt ϑ) :
    ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
        (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2)
      ≤ ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ∫⁻ z in planarBall vs vt ϑ s t,
          ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
  have hδ : 0 < ‖s - t‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hne
  have hrev : ‖t - s‖ = ‖s - t‖ := norm_sub_rev t s

  have hflat : ENNReal.ofReal ((f t - f s) ^ 2) * volume (planarBall vs vt ϑ s t)
      ≤ ∫⁻ z in planarBall vs vt ϑ s t,
        ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) := by
    rw [← setLIntegral_const (planarBall vs vt ϑ s t) (ENNReal.ofReal ((f t - f s) ^ 2))]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (f z - f s - (f t - f z)), sq_nonneg (f z - f s + (f t - f z))]

  have hw : ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) * ENNReal.ofReal (Real.sin ϑ ^ 4 / 4)
      = ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
        ENNReal.ofReal ((‖t - s‖ * Real.sin ϑ ^ 2 / 2) ^ 2) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hrev]
    congr 1
    have e : (‖s - t‖ * Real.sin ϑ ^ 2 / 2) ^ 2
        = ‖s - t‖ ^ ((2 : ℕ) : ℝ) * (Real.sin ϑ ^ 4 / 4) := by
      rw [Real.rpow_natCast]; ring
    rw [e, ← mul_assoc, ← Real.rpow_add hδ]
    congr 2
    push_cast
    ring
  calc ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
        (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2)
      = ENNReal.ofReal ((f t - f s) ^ 2) *
          (ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
            (ENNReal.ofReal ((‖t - s‖ * Real.sin ϑ ^ 2 / 2) ^ 2) * unitBallVol 2)) := by
        rw [show ENNReal.ofReal ((f t - f s) ^ 2) * ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
              (ENNReal.ofReal (Real.sin ϑ ^ 4 / 4) * unitBallVol 2)
            = ENNReal.ofReal ((f t - f s) ^ 2) *
              ((ENNReal.ofReal (‖s - t‖ ^ (-(2 : ℝ) - α)) *
                ENNReal.ofReal (Real.sin ϑ ^ 4 / 4)) * unitBallVol 2) from by ring, hw]
        ring
    _ = ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
          (ENNReal.ofReal ((f t - f s) ^ 2) * volume (planarBall vs vt ϑ s t)) := by
        rw [volume_planarBall hne h1 h2]; ring
    _ ≤ ENNReal.ofReal (‖s - t‖ ^ (-(4 : ℝ) - α)) *
          ∫⁻ z in planarBall vs vt ϑ s t,
            ENNReal.ofReal (2 * (f z - f s) ^ 2 + 2 * (f t - f z) ^ 2) :=
        mul_le_mul' le_rfl hflat
#print axioms solution
