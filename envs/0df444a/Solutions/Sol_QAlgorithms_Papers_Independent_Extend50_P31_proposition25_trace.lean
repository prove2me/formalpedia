-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.proposition25_trace
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:14:50.826083+00:00
-- url     : https://prove2.me/submissions/1ef8dbc1-d418-43d6-abbb-96c4f33785cd

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

private lemma chars_orthogonal (F : IrrepFamily G A) (a b : A) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (F.irrep a) g * character (F.irrep b) g⁻¹ =
      if a = b then 1 else 0 := by
  classical
  letI := bundled_irred (F.irrep a)
  letI := bundled_irred (F.irrep b)
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne')
  have he : Nonempty (Representation.Equiv (bundled (F.irrep b)) (bundled (F.irrep a))) ↔ a = b := by
    constructor
    · rintro ⟨e⟩
      exact (F.inequivalent b a ⟨e.toLinearEquiv, fun g x =>
        congrArg (fun f : (Fin (F.dim b) → ℂ) →ₗ[ℂ] (Fin (F.dim a) → ℂ) => f x)
          (e.toIntertwiningMap.isIntertwining' g)⟩).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  simpa only [bundled_char, he, Nat.card_eq_fintype_card, Nat.cast_one, Nat.cast_zero] using
    Representation.char_orthonormal (bundled (F.irrep a)) (bundled (F.irrep b))

private lemma char_average (F : IrrepFamily G A) (a : A) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character (F.irrep a) g⁻¹ =
      if a = F.trivial then 1 else 0 := by
  have ht (g : G) : character (F.irrep F.trivial) g = 1 := by
    simp [character, F.trivial_action, Matrix.trace_one, F.trivial_dim]
  have h := chars_orthogonal F F.trivial a
  simpa only [ht, one_mul, eq_comm] using h

open QAlgorithms.Papers.Independent.Information100.P44
open QAlgorithms.Papers.Independent.Dependency50.P26
private lemma central_trace (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (X : Mat n) :
    Matrix.trace (centralMap U F a X) =
      (if a = F.trivial then 1 else 0) * Matrix.trace X := by
  have ht (g : G) : Matrix.trace (conjugationMap U g X) = Matrix.trace X := by
    change Matrix.trace (U.rho g * (X * (U.rho g)ᴴ)) = _
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, (U.unitary g).1, Matrix.mul_one]
  have hdim : (F.dim a : ℂ) * (if a = F.trivial then 1 else 0) =
      (if a = F.trivial then 1 else 0) := by
    split_ifs with h
    · simp [h, F.trivial_dim]
    · simp
  calc
    Matrix.trace (centralMap U F a X) =
      (F.dim a : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, character (F.irrep a) g⁻¹) * Matrix.trace X := by
      simp only [centralMap, LinearMap.smul_apply, LinearMap.sum_apply,
        Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, ht]
      simp only [Finset.sum_mul, div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [char_average, hdim]

variable [Fintype A]

set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.14, Proposition 25 Eq.(70). No positivity or Hermitian preservation is assumed. -/
theorem solution (D : Data G A n) (l : OccurringIrrep D → ℂ) :
    TracePreserving (spectralMap D l) ↔ trivialCoefficient D l = 1 := by
  have h (X : Mat n) : Matrix.trace (spectralMap D l X) =
      trivialCoefficient D l * Matrix.trace X := by
    simp only [spectralMap, LinearMap.sum_apply, LinearMap.smul_apply,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, central_trace, trivialCoefficient,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp_all
  constructor
  · intro hp
    have hx := hp (1 : Mat n)
    rw [h, Matrix.trace_one] at hx
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast D.U.positive.ne'
    exact (mul_left_inj' hn).mp (by simpa using hx)
  · intro hl X
    rw [h, hl, one_mul]
