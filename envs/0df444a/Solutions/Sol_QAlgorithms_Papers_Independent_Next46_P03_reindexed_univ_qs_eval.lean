-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P03.reindexed_univ_qs_eval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:53:52.897564+00:00
-- url     : https://prove2.me/submissions/498e6ac0-8492-4677-8278-843b2d52d32c

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03

open QAlgorithms.Papers.Independent.Next46.P03

theorem g62r_one (x : ℝ) (xs : List ℝ) (p : MvPolynomial ℕ ℝ) :
    evalMpoly (x :: xs) p =
      Polynomial.eval x (evalMpolyPoly xs ((mpolyToMpolyPoly 0 p).map lowerPolyZeroOne)) := by
  unfold evalMpolyPoly
  rw [Polynomial.map_map]
  let F : MvPolynomial ℕ ℝ →+* ℝ :=
    (Polynomial.evalRingHom x).comp ((Polynomial.mapRingHom ((evalMpoly xs).comp lowerPolyZeroOne)).comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
        (fun j => if j = 0 then Polynomial.X else Polynomial.C (MvPolynomial.X j))))
  have hF : ∀ q, Polynomial.eval x (Polynomial.map ((evalMpoly xs).comp lowerPolyZeroOne)
      (mpolyToMpolyPoly 0 q)) = F q := fun q => rfl
  rw [hF]
  revert p
  rw [← RingHom.ext_iff]
  apply MvPolynomial.ringHom_ext
  · intro r; simp [F, evalMpoly, lowerPolyZeroOne]
  · intro j
    rcases j with _ | j
    · simp [F, evalMpoly]
    · simp [F, evalMpoly, lowerPolyZeroOne]

theorem solution (qs : List (MvPolynomial ℕ ℝ))
    (x : ℝ) (xs : List ℝ) :
    qs.map (fun p => evalMpoly (x :: xs) p) =
      (((univariateIn qs 0).map (fun p => p.map lowerPolyZeroOne)).map
        (fun q => evalMpolyPoly xs q)).map (fun p => p.eval x) := by
  simp only [univariateIn, List.map_map]
  apply List.map_congr_left
  intro p _
  exact g62r_one x xs p
