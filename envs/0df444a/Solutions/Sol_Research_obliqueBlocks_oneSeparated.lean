-- Prove2me | solution 1 for Research.obliqueBlocks_oneSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:12:42.528375+00:00
-- url     : https://prove2.me/submissions/a95605fb-2e9b-4dcc-bcc6-9a2b8aeb8936

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliquePoint_oneSeparated
public import Theorems.Thm_Research_obliquePoint_coordinate_bounds

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) :
    ∀ q s : Fin m × (Fin 365 × Fin 365), q ≠ s →
      1 ≤ sqDist (obliqueBlocks m q) (obliqueBlocks m s) := by
  intro q s hqs
  by_cases hb : q.1 = s.1
  · have hp : q.2 ≠ s.2 := by
      intro hp
      exact hqs (Prod.ext hb hp)
    have h := obliquePoint_oneSeparated q.2 s.2 hp
    simp only [obliqueBlocks, sqDist] at h ⊢
    rw [hb]
    convert h using 1; ring
  · have hbval : q.1.val ≠ s.1.val := fun h => hb (Fin.ext h)
    rcases lt_or_gt_of_ne hbval with hlt | hgt
    · have hstep : (q.1.val : ℝ) + 1 ≤ (s.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hlt)
      have hq := obliquePoint_coordinate_bounds q.2
      have hs := obliquePoint_coordinate_bounds s.2
      have hdx : 1400 ≤
          (2000 * (s.1.val : ℝ) + (obliquePoint s.2).1) -
            (2000 * (q.1.val : ℝ) + (obliquePoint q.2).1) := by
        nlinarith
      simp only [obliqueBlocks, sqDist]
      nlinarith [sq_nonneg ((obliquePoint q.2).2 - (obliquePoint s.2).2)]
    · have hstep : (s.1.val : ℝ) + 1 ≤ (q.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hgt)
      have hq := obliquePoint_coordinate_bounds q.2
      have hs := obliquePoint_coordinate_bounds s.2
      have hdx : 1400 ≤
          (2000 * (q.1.val : ℝ) + (obliquePoint q.2).1) -
            (2000 * (s.1.val : ℝ) + (obliquePoint s.2).1) := by
        nlinarith
      simp only [obliqueBlocks, sqDist]
      nlinarith [sq_nonneg ((obliquePoint q.2).2 - (obliquePoint s.2).2)]
end Research
