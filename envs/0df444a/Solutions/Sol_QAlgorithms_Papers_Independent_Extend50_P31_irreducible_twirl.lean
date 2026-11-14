-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.irreducible_twirl
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:22:44.583203+00:00
-- url     : https://prove2.me/submissions/1911125f-7502-49a9-8adb-6f18823d9081

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [DecidableEq A] {n : ℕ}
private def bundled (U : UnitaryIrrep G n) : Representation ℂ G (Fin n → ℂ) where
  toFun g := (U.rho g).mulVecLin
  map_one' := by ext v i; simp [U.one]
  map_mul' g h := by ext v i; simp [U.mul, Matrix.mulVec_mulVec]

private lemma bundled_irred (U : UnitaryIrrep G n) : Representation.IsIrreducible (bundled U) := by
  have hn : Nonempty (Fin n) := ⟨⟨0, U.positive⟩⟩
  letI := hn
  have hne : (⊥ : Subrepresentation (bundled U)) ≠ ⊤ := by
    intro h
    have hh := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hh
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases U.irreducible S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private lemma bundled_char (U : UnitaryIrrep G n) (g : G) :
    (bundled U).character g = character U g := by
  exact Matrix.trace_toLin'_eq (U.rho g)

noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}
private lemma scalar_of_commute (U : UnitaryIrrep G n) (X : Mat n)
    (hx : ∀ g, X * U.rho g = U.rho g * X) : ∃ c : ℂ, X = c • (1 : Mat n) := by
  letI := bundled_irred U
  let f : Representation.IntertwiningMap (bundled U) (bundled U) :=
    { toLinearMap := X.mulVecLin
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        change X.mulVec ((U.rho g).mulVec v) = (U.rho g).mulVec (X.mulVec v)
        simp only [Matrix.mulVec_mulVec, hx] }
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 f
  refine ⟨c, ?_⟩
  have he := congrArg Representation.IntertwiningMap.toLinearMap hc
  change c • LinearMap.id = X.mulVecLin at he
  have hi : Function.Injective (Matrix.mulVecLin : Mat n → _) := Matrix.toLin'.injective
  apply hi
  simpa using he.symm

open QAlgorithms.Papers.Independent.Dependency50.P16
private lemma conjugation_mul (U : UnitaryIrrep G n) (g h : G) (X : Mat n) :
    conjugationMap U g (conjugationMap U h X) = conjugationMap U (g*h) X := by
  simp [conjugationMap, sandwich, U.mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]


set_option autoImplicit false

set_option autoImplicit false

theorem solution {G : Type*} [Group G] [Fintype G] {n : ℕ} (U : UnitaryIrrep G n) (X : Mat n) :
    (Fintype.card G : ℂ)⁻¹ • (∑ g : G, conjugationMap U g X) =
      (Matrix.trace X / n) • (1 : Mat n) := by
  classical
  let Y : Mat n := (Fintype.card G : ℂ)⁻¹ • (∑ g : G, conjugationMap U g X)
  have hC (g : G) : conjugationMap U g Y = Y := by
    dsimp [Y]
    rw [map_smul, map_sum]
    simp_rw [conjugation_mul]
    congr 1
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => conjugationMap U h X)
  have hc (g : G) : Y * U.rho g = U.rho g * Y := by
    have hh := congrArg (fun Z : Mat n => Z * U.rho g) (hC g)
    change (U.rho g * (Y * (U.rho g)ᴴ)) * U.rho g = Y * U.rho g at hh
    simpa only [Matrix.mul_assoc, (U.unitary g).1, Matrix.mul_one] using hh.symm
  obtain ⟨c, hy⟩ := scalar_of_commute U Y hc
  have ht (g : G) : Matrix.trace (conjugationMap U g X) = Matrix.trace X := by
    change Matrix.trace (U.rho g * (X * (U.rho g)ᴴ)) = _
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, (U.unitary g).1, Matrix.mul_one]
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast U.positive.ne'
  have hg : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hty : Matrix.trace Y = Matrix.trace X := by
    dsimp [Y]
    simp only [Matrix.trace_smul, Matrix.trace_sum, ht, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
    field_simp
  have he : c * n = Matrix.trace X := by
    rw [hy, Matrix.trace_smul, Matrix.trace_one] at hty
    simpa using hty
  have hh : c = Matrix.trace X / n := (eq_div_iff hn).mpr he
  change Y = _
  rw [hy, hh]