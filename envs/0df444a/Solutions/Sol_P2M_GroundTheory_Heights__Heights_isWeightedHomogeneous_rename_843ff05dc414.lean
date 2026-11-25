-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isWeightedHomogeneous_rename_843ff05dc414
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:33:03.87108+00:00
-- url     : https://prove2.me/submissions/b597f685-4442-4941-8c3b-8d957a4f4b5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {k n : ℕ}
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ τ : Type*} {e : σ → τ} (he : Function.Injective e)
    {w : σ → ℕ} {w' : τ → ℕ} (hw : ∀ x, w' (e x) = w x) {p : MvPolynomial σ R} {a : ℕ}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous w' (rename e p) a := by
  classical
  intro d hd
  have hd' : d ∈ (rename e p).support := mem_support_iff.mpr hd
  rw [support_rename_of_injective he] at hd'
  obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd'
  have := hp (mem_support_iff.mp hd₀)
  rw [← this, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · simp only [Finsupp.sum, hw]
  · intro _; simp
  · intro _ _ _; ring
end GroundTheory.Heights₂.Heights
