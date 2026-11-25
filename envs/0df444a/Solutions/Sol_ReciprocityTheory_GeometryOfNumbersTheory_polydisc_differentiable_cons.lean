-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.polydisc_differentiable_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:38.82012+00:00
-- url     : https://prove2.me/submissions/9a7b8541-b670-406a-82bf-3720e97776f9

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} :
    Differentiable ℂ (fun p : ℂ × (Fin D → ℂ) => (Fin.cons p.1 p.2 : Fin (D + 1) → ℂ)) := by
  rw [differentiable_pi]
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp
  · have h := (differentiable_pi.1 (differentiable_snd (𝕜 := ℂ) (E := ℂ) (F := Fin D → ℂ))) j
    simpa using h
end ReciprocityTheory.GeometryOfNumbersTheory
