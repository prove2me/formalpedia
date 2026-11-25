-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.length_loc_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:54.833715+00:00
-- url     : https://prove2.me/submissions/1a165445-6144-4788-8b7d-738573c9da58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_quot_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_quot_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_length_loc_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (P : Ideal R) [P.IsPrime] : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal R)
    (f : Fin N → R) (q : Fin N → Ideal R), F (Fin.last N) = ⊤ →
    (∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j, q j ≤ P → q j = P) →
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F 0)) =
      ((∑ j : Fin N, if q j = P then 1 else 0 : ℕ) : ℕ∞)
  | 0, F, f, q, hlast, _, _ => by
    rw [show F 0 = F (Fin.last 0) from rfl, hlast, length_loc_top]
    simp
  | N + 1, F, f, q, hlast, hj, hmin => by
    have ih := solution P N (fun j => F j.succ) (fun j => f j.succ) (fun j => q j.succ)
      (by simpa [Fin.succ_last] using hlast)
      (fun j => by
        have h := hj j.succ
        first | rwa [← Fin.succ_castSucc] at h | rwa [Fin.succ_castSucc] at h)
      (fun j => hmin j.succ)
    obtain ⟨h1, _, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h1 h3
    rw [length_loc_step (F 0) (q 0) (f 0) h3 P, ← h1, ih, Fin.sum_univ_succ]
    by_cases hq : q 0 = P
    · rw [if_pos hq, hq, length_loc_quot_self]
      push_cast
      ring
    · rw [if_neg hq, length_loc_quot_eq_zero _ _ (fun h => hq (hmin 0 h))]
      simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
