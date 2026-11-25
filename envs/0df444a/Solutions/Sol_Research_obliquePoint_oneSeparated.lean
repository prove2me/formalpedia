-- Prove2me | solution 1 for Research.obliquePoint_oneSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:08:05.474496+00:00
-- url     : https://prove2.me/submissions/60449b29-b0e0-4261-aaef-7d2a290ff5b5

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliqueNormNum_ge_denominator

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    ∀ q s : Fin 365 × Fin 365, q ≠ s →
      1 ≤ sqDist (obliquePoint q) (obliquePoint s) := by
  intro q s hqs
  let d : ℤ × ℤ :=
    ((s.1.val : ℤ) - (q.1.val : ℤ),
      (s.2.val : ℤ) - (q.2.val : ℤ))
  have hdne : d ≠ (0, 0) := by
    intro hd
    have hx : s.1.val = q.1.val := by
      have := congrArg Prod.fst hd
      dsimp [d] at this
      omega
    have hy : s.2.val = q.2.val := by
      have := congrArg Prod.snd hd
      dsimp [d] at this
      omega
    exact hqs (Prod.ext (Fin.ext hx.symm) (Fin.ext hy.symm))
  have hz := obliqueNormNum_ge_denominator d.1 d.2 (by
    simpa [d] using hdne)
  have hzR : (305 : ℝ) ≤ (obliqueNormNum d : ℝ) := by exact_mod_cast hz
  rw [obliquePoint_sqDist_eq]
  change 1 ≤ (obliqueNormNum d : ℝ) / 305

  linarith
end Research
