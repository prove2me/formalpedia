-- Prove2me | solution 1 for RevShareCoord.Wholesale.inducing_price
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:29:32.853118+00:00
-- url     : https://prove2.me/submissions/dec35859-3652-4320-b967-e542d6e536ea

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

open RevShareCoord.Wholesale in
theorem RevShareCoord_Wholesale_strict_tangent (M : Model) (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (hx : 0 ≤ x) (hxq : x ≠ q) : M.R x - M.R' q * x < M.R q - M.R' q * q := by
  have hd := M.hasDeriv q hq
  rcases lt_or_gt_of_ne hxq with h | h
  · have := M.strictConcave.lt_slope_of_hasDerivWithinAt (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hq) h hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.2 h)] at this
    nlinarith
  · have := M.strictConcave.slope_lt_of_hasDerivWithinAt (Set.mem_Ici.2 hq) (Set.mem_Ici.2 hx) h hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.2 h)] at this
    nlinarith

open RevShareCoord.Wholesale in
theorem solution (M : Model) (q : ℝ) (hq : 0 ≤ q) :
    IsMaxOn (fun x => M.R x - inducingPrice M.R' q * x) (Set.Ici 0) q ∧
      ∀ x : ℝ, 0 ≤ x →
        IsMaxOn (fun y => M.R y - inducingPrice M.R' q * y) (Set.Ici 0) x → x = q := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Set.mem_ofPred_eq, inducingPrice]
    by_cases hxq : x = q
    · subst hxq; rfl
    · exact (RevShareCoord_Wholesale_strict_tangent M q hq x hx hxq).le
  · intro x hx hmax
    by_contra hxq
    have h1 := RevShareCoord_Wholesale_strict_tangent M q hq x hx hxq
    have h2 := hmax (Set.mem_Ici.2 hq)
    simp only [Set.mem_ofPred_eq, inducingPrice] at h2
    linarith
