-- Prove2me | solution 1 for WeierstrassEllipticZeta.coordinate_stable_quotient_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T01:21:28.925293+00:00
-- url     : https://prove2.me/submissions/f49806a1-5de0-4e42-b3ed-fea84087dfe0

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

theorem solution
    (K σ : Type*) [Field K] (J : Ideal (MvPolynomial σ K))
    (d : ℕ) (v : Fin d → MvPolynomial σ K ⧸ J)
    (hone : (1 : MvPolynomial σ K ⧸ J) ∈ Submodule.span K (Set.range v))
    (hmul : ∀ i : σ, ∀ j : Fin d,
      Ideal.Quotient.mk J (MvPolynomial.X i) * v j ∈ Submodule.span K (Set.range v)) :
    Submodule.span K (Set.range v) = ⊤ ∧
      FiniteDimensional K (MvPolynomial σ K ⧸ J) ∧
      Module.finrank K (MvPolynomial σ K ⧸ J) ≤ d := by
  classical
  let A := MvPolynomial σ K ⧸ J
  let q : MvPolynomial σ K →ₐ[K] A := Ideal.Quotient.mkₐ K J
  let V : Submodule K A := Submodule.span K (Set.range v)
  have hstable (i : σ) (a : A) (ha : a ∈ V) : q (MvPolynomial.X i) * a ∈ V := by
    refine Submodule.span_induction (fun a ha => ?_) ?_
      (fun a b _ _ ha hb => ?_) (fun r a _ ha => ?_) ha
    · obtain ⟨j, rfl⟩ := ha
      exact hmul i j
    · simpa only [mul_zero] using V.zero_mem
    · simpa only [mul_add] using V.add_mem ha hb
    · simpa only [mul_smul_comm] using V.smul_mem r ha
  have hpoly (p : MvPolynomial σ K) : q p ∈ V := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      have hconst : q (MvPolynomial.C r) = r • (1 : A) := by
        simpa only [MvPolynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
          using q.commutes r
      rw [hconst]
      exact V.smul_mem r hone
    | add p r hp hr =>
      simpa only [map_add] using V.add_mem hp hr
    | mul_X p i hp =>
      simpa only [map_mul, mul_comm] using hstable i (q p) hp
  have htop : V = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K J a
    exact hpoly p
  let : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range v)
  have hsurj : Function.Surjective V.subtype := by
    intro a
    refine ⟨⟨a, ?_⟩, rfl⟩
    rw [htop]
    trivial
  refine ⟨htop, FiniteDimensional.of_surjective V.subtype hsurj, ?_⟩
  simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top htop
