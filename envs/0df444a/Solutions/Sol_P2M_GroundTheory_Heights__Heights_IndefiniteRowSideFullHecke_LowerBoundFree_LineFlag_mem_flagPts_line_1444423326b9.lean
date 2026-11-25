-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_mem_flagPts_line_1444423326b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:17.765415+00:00
-- url     : https://prove2.me/submissions/c2b57256-c515-499c-8e4d-15a4feb0b1bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step1_cbe9e2a7f4d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_pluecker_step2_2acaaa52e1fa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
theorem _root_.solution (u : (Σ k : YBlk DL, ιY PL k) → ℂ)
    (hz : ∃ i, zPart PL u ⟨(), i⟩ ≠ 0) (h1 : ∃ m : Fin 2, wPart PL u ((), ⟨0, by decide⟩) m ≠ 0)
    (h2 : wPart PL u ((), ⟨1, by decide⟩) (0 : Fin 1) ≠ 0) : u ∈ flagPts PL := by
  obtain ⟨i0, hi0⟩ := hz
  refine ⟨mem_mcPts_line.2 ⟨i0, hi0⟩, fun τ => ?_⟩
  obtain rfl : τ = () := rfl
  set w1 : Fin 2 → ℂ := wPart PL u ((), ⟨0, by decide⟩) with hw1
  set w2 : ℂ := wPart PL u ((), ⟨1, by decide⟩) (0 : Fin 1) with hw2
  have hw1ne : w1 ≠ 0 := fun h => by obtain ⟨m, hm⟩ := h1; exact hm (congrFun h m)
  set t : Fin 2 → ℂ := if w1 0 ≠ 0 then ![0, 1] else ![1, 0] with ht
  set g : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![w1 0, t 0], ![w1 1, t 1]] with hg
  have hdet : g.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    by_cases h0 : w1 0 ≠ 0
    · simp [hg, ht, h0]
    · have h1' : w1 1 ≠ 0 := by
        intro h1'
        apply hw1ne
        funext p
        fin_cases p
        · simpa using h0
        · simpa using h1'
      simp [hg, ht, h0, h1']
  have hz0 : zPart PL u ⟨(), i0⟩ ≠ 0 := hi0
  refine ⟨fun _ => i0, 1, Pi.basisFun Ω (Fin 2), g,
    fun i => if (i : ℕ) = 0 then 1 else w2 / g.det,
    ⟨segreCoord_line_ne_zero i0, one_mem _, one_ne_zero, (Pi.basisFun Ω (Fin 2)).linearIndependent,
      trivial_frame_iff _ 2 _⟩, inFrameDomain_line hz0, hdet, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs
    · exact one_ne_zero
    · exact div_ne_zero h2 hdet
  · rintro ⟨_ | _ | n, hi⟩ m
    · refine ⟨g m 0, pluecker_step1 i0 (zPart PL u) hz0 g m, ?_⟩
      show wPart PL u ((), ⟨0, hi⟩) m = (if (0 : ℕ) = 0 then 1 else w2 / g.det) * g m 0
      rw [if_pos rfl, one_mul]
      have hm : g m 0 = w1 m := by
        fin_cases m <;> rfl
      rw [hm]
    · refine ⟨g.det, pluecker_step2 i0 (zPart PL u) hz0 g, ?_⟩
      have hm0 : (m : ℕ) = 0 := by
        have h := m.isLt
        change (m : ℕ) < 1 at h
        omega
      show wPart PL u ((), ⟨0 + 1, hi⟩) m = (if (0 + 1 : ℕ) = 0 then 1 else w2 / g.det) * g.det
      rw [if_neg (by omega), div_mul_cancel₀ _ hdet, hw2]
      have : m = (0 : Fin 1) := Fin.ext hm0
      rw [this]
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
