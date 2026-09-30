-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_transcendental_parameter_of_no_pair
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T00:25:28.147261+00:00
-- url     : https://prove2.me/submissions/c875d99e-3486-44cc-b69f-d7cfce2ca65a

import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Tactic.FinCases

open WeierstrassEllipticZeta

noncomputable section

private theorem exists_complex_transcendental : ∃ θ : ℂ, Transcendental ℚ θ := by
  by_contra h
  have hall : ∀ θ : ℂ, IsAlgebraic ℚ θ := by
    simpa only [Transcendental, not_exists, not_not] using h
  let : Algebra.IsAlgebraic ℚ ℂ := ⟨hall⟩
  have hcard := Algebra.IsAlgebraic.cardinalMk_le_max ℚ ℂ
  have hbad : Cardinal.continuum ≤ Cardinal.aleph0 := by
    simpa using hcard
  exact (Cardinal.aleph0_lt_continuum.not_ge hbad)

private theorem algebraicIndependent_pair_of_transcendental
    (θ x : ℂ) (hθ : Transcendental ℚ θ)
    (hx : Transcendental (Algebra.adjoin ℚ {θ}) x) :
    AlgebraicIndependent ℚ ![x, θ] := by
  have hind : AlgebraicIndependent ℚ (fun _ : Fin 1 => θ) :=
    algebraicIndependent_unique_type_iff.mpr hθ
  have hx' : Transcendental (Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => θ))) x := by
    have hr : Set.range (fun _ : Fin 1 => θ) = {θ} := by
      ext y
      simp
    rw [hr]
    exact hx
  have hopt := (hind.option_iff_transcendental x).mpr hx'
  let f : Fin 2 → Option (Fin 1) := ![none, some 0]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  convert! hopt.comp f hf using 1
  ext i
  fin_cases i <;> rfl

/-- A finite complex family with no independent pair is algebraic over a
one-parameter rational function field. Algebraicity over `ℚ[θ]` and `ℚ(θ)`
are equivalent by clearing denominators. -/
theorem solution {n : ℕ} (values : Fin n → ℂ)
    (hpair : ¬ HasAlgebraicallyIndependentPair values) :
    ∃ θ : ℂ, Transcendental ℚ θ ∧
      ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ}) (values i) := by
  classical
  by_cases htrans : ∃ j, Transcendental ℚ (values j)
  · obtain ⟨j, hj⟩ := htrans
    refine ⟨values j, hj, fun i => ?_⟩
    by_cases hij : i = j
    · subst i
      exact isAlgebraic_algebraMap
        (⟨values j, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
          Algebra.adjoin ℚ {values j})
    · by_contra hi
      exact hpair ⟨i, j, hij,
        algebraicIndependent_pair_of_transcendental (values j) (values i) hj hi⟩
  · obtain ⟨θ, hθ⟩ := exists_complex_transcendental
    refine ⟨θ, hθ, fun i => ?_⟩
    have hi : IsAlgebraic ℚ (values i) := by
      by_contra hi
      exact htrans ⟨i, hi⟩
    exact hi.extendScalars (FaithfulSMul.algebraMap_injective ℚ (Algebra.adjoin ℚ {θ}))

