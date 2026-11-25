-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WF.cf_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:30.82032+00:00
-- url     : https://prove2.me/submissions/4a7bec59-5abd-43bb-b282-69a8a2a560e8

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WF
theorem _root_.solution {k : ℕ} {K : Set (E d)} {L : List (List (Fin d) × (E d → ℂ))} (hL : Good k K L)
    (n : ℕ) (w : Fin n → Fin d) : ContDiff ℝ ∞ (cf L n w) ∧ ∀ y ∉ K, cf L n w y = 0 := by
  revert hL
  induction L with
  | nil =>
    intro _
    have h0 : cf ([] : List (List (Fin d) × (ZetaZeros.D.EllReg.E d → ℂ))) n w = fun _ => 0 := by
      funext y; simp only [cf, List.map_nil, List.sum_nil]
    rw [h0]; exact ⟨contDiff_const, fun _ _ => rfl⟩
  | cons p L ih =>
    intro hL
    have hp := hL p (by simp)
    have hL' : Good k K L := by
      intro r hr; exact hL r (by simp [hr])
    obtain ⟨ih1, ih2⟩ := ih hL'
    have h1 : cf (p :: L) n w = fun y => (if p.1 = List.ofFn w then p.2 y else 0) + cf L n w y := by
      funext y; simp only [cf, List.map_cons, List.sum_cons]
    rw [h1]
    constructor
    · refine ContDiff.add ?_ ih1
      by_cases hc : p.1 = List.ofFn w
      · simp only [if_pos hc]; exact hp.2.1
      · simp only [if_neg hc]; exact contDiff_const
    · intro y hy
      show (if p.1 = List.ofFn w then p.2 y else 0) + cf L n w y = 0
      rw [ih2 y hy]
      by_cases hc : p.1 = List.ofFn w
      · simp [if_pos hc, hp.2.2 y hy]
      · simp [if_neg hc]
end ZetaZeros.D.EllReg.WF
