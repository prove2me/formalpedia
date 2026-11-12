-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P65.wired_choi_link
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:49:44.40128+00:00
-- url     : https://prove2.me/submissions/cfaa21a0-7e62-45ea-8537-334599831d33

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P65

open Filter QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

variable {A B C D R : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty R]

open QAlgorithms.Papers.Independent.Intakethird100.P65 in
theorem solution (N : Superop B C) (hN : IsChannel N)
    (P : Superop (A × C) (B × D)) (hP : BipartiteNSOperation P) :
    choi (wire N P) = linkChoi (choi N) (choi P) := by
  have hk : ∀ (x1 y1 : A) (u v : C),
      Matrix.kronecker (Matrix.single x1 y1 (1 : ℂ)) (Matrix.single u v (1 : ℂ)) =
        Matrix.single (x1, u) (y1, v) (1 : ℂ) := by
    intro x1 y1 u v
    ext x y
    obtain ⟨x1', x2'⟩ := x
    obtain ⟨y1', y2'⟩ := y
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  ext p q
  simp only [choi, wire, linkChoi, hk]
