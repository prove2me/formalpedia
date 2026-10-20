-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.coherence_bell_overlap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:45.915289+00:00
-- url     : https://prove2.me/submissions/b7f008a6-320c-4cb6-8851-caffc506cf51

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

theorem g52b_qf_two {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    star (Pi.single i (1:ℂ) - Pi.single j 1) ⬝ᵥ (M *ᵥ (Pi.single i (1:ℂ) - Pi.single j 1)) =
      M i i - M i j - M j i + M j j := by
  simp only [star_sub, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

/-- PDF pp.12–13, Lemma 4; p.39, Eq.(280): printed (61)'s >= then > fails at
boundary equality. Use the STRICT first antecedent of the source's Appendix XV-G. -/
theorem solution (rho : Op (Key 2)) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (((rho * bellProjector 2).trace.re > 1-eps) → (rho (0,0) (1,1)).re > 1/2-eps) ∧
    ((rho (0,0) (1,1)).re > 1/2-eps → (rho * bellProjector 2).trace.re ≥ 1-2*eps) := by
  have hT : (rho * bellProjector 2).trace.re =
      ((rho (0,0) (0,0)).re + (rho (1,1) (1,1)).re + (rho (0,0) (1,1)).re
        + (rho (1,1) (0,0)).re) / 2 := by
    simp [Matrix.trace, Matrix.mul_apply, bellProjector, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have hH : (rho (1,1) (0,0)).re = (rho (0,0) (1,1)).re := by
    have := hrho.1.1.apply (0,0) (1,1)
    rw [← this]; simp
  have hd : ∀ q : Key 2, 0 ≤ (rho q q).re := fun q =>
    (Complex.nonneg_iff.mp (hrho.1.diag_nonneg (i := q))).1
  have htr : (rho (0,0) (0,0)).re + (rho (0,1) (0,1)).re + (rho (1,0) (1,0)).re
      + (rho (1,1) (1,1)).re = 1 := by
    have := congrArg Complex.re hrho.2
    simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at this
    linarith
  have hx := (Complex.nonneg_iff.mp
    (hrho.1.dotProduct_mulVec_nonneg (Pi.single ((0:Fin 2),(0:Fin 2)) (1:ℂ) - Pi.single (1,1) 1))).1
  rw [g52b_qf_two] at hx
  simp only [Complex.add_re, Complex.sub_re] at hx
  have h01 := hd (0,1)
  have h10 := hd (1,0)
  rw [hT, hH]
  constructor
  · intro h; linarith
  · intro h; linarith


end

