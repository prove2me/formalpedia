-- Prove2me | solution 1 for SmaleNinth.integer_polyhedron_solution_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T17:58:01.975077+00:00
-- url     : https://prove2.me/submissions/cb1ed23d-4634-48a1-996a-902d45993def

import Definitions.Def_Polyhedron
import Theorems.Thm_SmaleNinth_exists_minimal_face_point
import Theorems.Thm_SmaleNinth_integer_subsystem_solution_bound

open Matrix LinearOptimization

theorem solution {m n : ℕ} (U : ℕ) (hU : 1 ≤ U)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hA : ∀ i j, |A i j| ≤ (U : ℤ)) (hb : ∀ i, |b i| ≤ (U : ℤ))
    (hne : (polyhedron (A.map (Int.cast : ℤ → ℝ))
      (fun i => (b i : ℝ))).Nonempty) :
    ∃ x ∈ polyhedron (A.map (Int.cast : ℤ → ℝ)) (fun i => (b i : ℝ)),
      ∀ j, |x j| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by
  -- a point of a minimal face, together with the constraints tight on that face
  obtain ⟨x, I, hxP, hxTight, hIsub⟩ :=
    SmaleNinth.exists_minimal_face_point (A.map (Int.cast : ℤ → ℝ))
      (fun i => (b i : ℝ)) hne
  -- the tight subsystem is a consistent integer system, so it has a small solution
  obtain ⟨y, hySolves, hySmall⟩ :=
    SmaleNinth.integer_subsystem_solution_bound U hU A b I hA hb x hxTight
  -- every solution of the tight subsystem lies in the polyhedron
  exact ⟨y, hIsub y hySolves, hySmall⟩
