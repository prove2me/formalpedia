-- Prove2me | solution 1 for PositivityTheory.KReal.cas_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:14.65707+00:00
-- url     : https://prove2.me/submissions/b347f00c-e963-49f0-beb4-3412ce61a097

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Theorems.Thm_PositivityTheory_KReal_sb_symm
import Theorems.Thm_PositivityTheory_KReal_sb_trans
import Theorems.Thm_PI_FockOneDegW_Core_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
variable {r s : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Ix r s → Ix r s → Module.End ℂ M}
    (hρ : GlK ρ) {a b : Ix r s} (hab : sameBlock a b) : casK ρ * ρ a b = ρ a b * casK ρ := by
  have key : ∀ c d : Ix r s,
      ρ a b * (if sameBlock c d then ρ c d * ρ d c else 0) - (if sameBlock c d then ρ c d * ρ d c else 0) * ρ a b =
      ((if b = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0) -
        (if a = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0)) +
      ((if b = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0) -
        (if a = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0)) := by
    intro c d
    by_cases hcd : sameBlock c d
    · have e : ρ a b * (ρ c d * ρ d c) - (ρ c d * ρ d c) * ρ a b =
          (ρ a b * ρ c d - ρ c d * ρ a b) * ρ d c + ρ c d * (ρ a b * ρ d c - ρ d c * ρ a b) := by
        noncomm_ring
      rw [if_pos hcd, e, hρ a b c d hab hcd, hρ a b d c hab (sb_symm hcd), sub_mul, mul_sub]
      congr 2
      · by_cases h : b = c
        · subst h; simp [sb_trans hab hcd]
        · simp [h]
      · by_cases h : a = d
        · subst h; simp [hcd]
        · simp [h, Ne.symm h]
      · by_cases h : b = d
        · subst h; simp [sb_trans hcd (sb_symm hab)]
        · simp [h]
      · by_cases h : a = c
        · subst h; simp [hcd]
        · simp [h, Ne.symm h]
    · have t1 : (if b = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd (sb_trans (sb_symm hab) h2) hcd
        all_goals rfl
      have t2 : (if a = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd h2 hcd
        all_goals rfl
      have t3 : (if b = d then (if sameBlock c a then ρ c b * ρ a c else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd (sb_trans h2 hab) hcd
        all_goals rfl
      have t4 : (if a = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0) = 0 := by
        split_ifs with h1 h2
        · subst h1; exact absurd h2 hcd
        all_goals rfl
      rw [t1, t2, t3, t4, if_neg hcd]
      simp
  have h0 : ρ a b * casK ρ - casK ρ * ρ a b = 0 := by
    unfold casK
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, key]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun c d => if b = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0),
      Finset.sum_comm (f := fun c d => if a = c then (if sameBlock a d then ρ a d * ρ d b else 0) else 0)]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    abel
  exact (sub_eq_zero.1 h0).symm
end PositivityTheory.KReal
