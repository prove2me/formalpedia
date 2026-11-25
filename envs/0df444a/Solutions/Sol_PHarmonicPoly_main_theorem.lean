-- Prove2me | solution 1 for PHarmonicPoly.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:47:04.3478+00:00
-- url     : https://prove2.me/submissions/91c5f55c-cd73-4ae6-8faa-58419366a9f3

module
public import Definitions.Def_PHarmonicPoly
public import Definitions.Def_PHarmonicPoly_Solution
public import Theorems.Thm_MainTheorem


set_option autoImplicit false
@[expose] public section
public section
open PHarmonicPoly
open MvPolynomial
namespace PHarmonicPoly
theorem _root_.solution {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : (n : ℝ) - 1 / 13 ≤ p)
    (P : MvPolynomial (Fin n) ℝ)
    (hE : ∀ x : EuclideanSpace ℝ (Fin n),
      EpOp p (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) x = 0) :
    ∃ (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = inner ℝ w x + c :=
  _root_.MainTheorem hn hp P hE
end PHarmonicPoly
