-- Prove2me | solution 1 for RelDecoding.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:49:55.898597+00:00
-- url     : https://prove2.me/submissions/2daa967e-150f-485f-88b1-c2d178b8f3eb

import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega
import Definitions.Def_RelDecoding_markedSpace
import Mathlib.Data.ENat.Lattice
import Definitions.Def_RelDecoding_relDist
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_RelDecoding_norm2

set_option autoImplicit false


namespace RelDecoding

variable {nA : Type*} [Fintype nA] [DecidableEq nA] {s : ℕ}
variable (a : Fin s → Matrix nA nA ℂ)

def adjointWord (w : List (Fin s × Bool)) : List (Fin s × Bool) :=
  w.reverse.map (fun l => (l.1, !l.2))

@[simp] theorem adjointWord_length (w : List (Fin s × Bool)) :
    (adjointWord w).length = w.length := by
  simp [adjointWord]

theorem letterEval_adjoint (l : Fin s × Bool) :
    letterEval a (l.1, !l.2) = star (letterEval a l) := by
  rcases l with ⟨i, e⟩
  cases e <;> simp [letterEval]

theorem wordEval_append (u v : List (Fin s × Bool)) :
    wordEval a (u ++ v) = wordEval a u * wordEval a v := by
  simp [wordEval, List.prod_append]

theorem wordEval_adjointWord (w : List (Fin s × Bool)) :
    wordEval a (adjointWord w) = star (wordEval a w) := by
  induction w with
  | nil => simp [adjointWord, wordEval]
  | cons l w ih =>
    have hc : adjointWord (l :: w) = adjointWord w ++ [(l.1, !l.2)] := by
      simp [adjointWord]
    rw [hc, wordEval_append, ih]
    simp [wordEval, letterEval_adjoint, star_mul]

theorem wordEval_mem_markedSpace (w : List (Fin s × Bool)) {d : ℕ}
    (hw : w.length ≤ d) : wordEval a w ∈ markedSpace a d :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem markedSpace_mono {d e : ℕ} (hde : d ≤ e) :
    markedSpace a d ≤ markedSpace a e := by
  apply Submodule.span_mono
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans hde, rfl⟩

theorem markedSpace_star_mul_mem {d e : ℕ} {X Y : genAlg a}
    (hX : X ∈ markedSpace a d) (hY : Y ∈ markedSpace a e) :
    star X * Y ∈ markedSpace a (d + e) := by
  induction hX, hY using Submodule.span_induction₂ with
  | mem_mem X Y hX hY =>
    rcases hX with ⟨u, hu, rfl⟩
    rcases hY with ⟨v, hv, rfl⟩
    rw [← wordEval_adjointWord, ← wordEval_append]
    apply wordEval_mem_markedSpace
    simp only [List.length_append, adjointWord_length]
    omega
  | zero_left Y hY => simp
  | zero_right X hX => simp
  | add_left X Y Z hX hY hZ ihX ihY =>
    simpa [star_add, add_mul] using (markedSpace a (d + e)).add_mem ihX ihY
  | add_right X Y Z hX hY hZ ihY ihZ =>
    simpa [mul_add] using (markedSpace a (d + e)).add_mem ihY ihZ
  | smul_left r X Y hX hY ih =>
    simpa [star_smul, smul_mul_assoc] using
      (markedSpace a (d + e)).smul_mem (star r) ih
  | smul_right r X Y hX hY ih =>
    simpa [mul_smul_comm] using (markedSpace a (d + e)).smul_mem r ih

theorem wordEval_split (w : List (Fin s × Bool)) (D : ℕ) (hw : w.length ≤ 2 * D) :
    ∃ X ∈ markedSpace a D, ∃ Y ∈ markedSpace a D, star X * Y = wordEval a w := by
  refine ⟨wordEval a (adjointWord (w.take D)), ?_, wordEval a (w.drop D), ?_, ?_⟩
  · apply wordEval_mem_markedSpace
    simp only [adjointWord_length, List.length_take]
    exact min_le_left _ _
  · apply wordEval_mem_markedSpace
    simp only [List.length_drop]
    omega
  · rw [wordEval_adjointWord, star_star, ← wordEval_append, List.take_append_drop]

end RelDecoding

namespace RelDecoding

open LIDT.MIPStarRE.Quantum

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]
variable {s : ℕ} (a : Fin s → Matrix nA nA ℂ)
variable (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ)

theorem distance_gt_iff_trace_eq (t : ℕ) :
    (t : ℕ∞) < relDist a π ↔
      ∀ X ∈ markedSpace a t,
        normalizedTrace (π X) = normalizedTrace (X : Matrix nA nA ℂ) := by
  constructor
  · intro h X hX
    by_contra hne
    have hd : relDist a π ≤ (t : ℕ∞) :=
      sInf_le ⟨t, ⟨X, hX, hne⟩, rfl⟩
    exact (not_le_of_gt h) hd
  · intro h
    apply ENat.natCast_add_one_le_iff.mp
    apply le_sInf
    rintro z ⟨k, ⟨X, hX, hne⟩, rfl⟩
    have htk : t < k := by
      by_contra hn
      exact hne (h X ((markedSpace_mono a (Nat.le_of_not_gt hn)) hX))
    simpa only [← ENat.natCast_one, ← ENat.natCast_add] using
      (ENat.natCast_le_natCast.mpr (Nat.succ_le_iff.mpr htk))

end RelDecoding

namespace RelDecoding

open LIDT.MIPStarRE.Quantum
open scoped ComplexOrder

/-- Normalized trace is faithful on matrices of the form `A* A`. Empty index
types cause no exception because there is only one matrix on an empty type. -/
theorem normalizedTrace_star_mul_self_eq_zero_iff {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : normalizedTrace (star A * A) = 0 ↔ A = 0 := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · letI := hn
    have hA : A = 0 := Subsingleton.elim _ _
    simp [hA, normalizedTrace]
  · letI := hn
    have hcard : (Fintype.card n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    unfold normalizedTrace
    simp only [div_eq_zero_iff, hcard, or_false]
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- The normalized squared Hilbert--Schmidt norm is a nonnegative real complex number. -/
theorem normalizedTrace_star_mul_self_nonneg {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : 0 ≤ normalizedTrace (star A * A) := by
  have htrace : 0 ≤ (star A * A).trace :=
    (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp htrace
  unfold normalizedTrace
  rw [Complex.nonneg_iff]
  simp only [Complex.div_natCast_re, Complex.div_natCast_im]
  exact ⟨div_nonneg hre (Nat.cast_nonneg _), by simp [← him]⟩

/-- Zero physical Hilbert--Schmidt norm characterizes the zero matrix, including
the unique matrix on an empty index type. -/
theorem norm2_eq_zero_iff {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    norm2 A = 0 ↔ A = 0 := by
  have hpos := Complex.nonneg_iff.mp (normalizedTrace_star_mul_self_nonneg A)
  rw [norm2, Real.sqrt_eq_zero hpos.1]
  constructor
  · intro hre
    apply (normalizedTrace_star_mul_self_eq_zero_iff A).mp
    apply Complex.ext
    · exact hre
    · exact hpos.2.symm
  · rintro rfl
    simp [normalizedTrace]

end RelDecoding

namespace RelDecoding

open LIDT.MIPStarRE.Quantum

variable {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB] [DecidableEq nB]
variable {s : ℕ} (a : Fin s → Matrix nA nA ℂ)
variable (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ)

theorem distance_gt_iff_inner_eq (D : ℕ) :
    ((2 * D : ℕ) : ℕ∞) < relDist a π ↔
      ∀ X ∈ markedSpace a D, ∀ Y ∈ markedSpace a D,
        normalizedTrace (star (π X) * π Y) =
          normalizedTrace (star (X : Matrix nA nA ℂ) * (Y : Matrix nA nA ℂ)) := by
  constructor
  · intro h X hX Y hY
    have htr := (distance_gt_iff_trace_eq a π (2 * D)).mp h
    have hp : star X * Y ∈ markedSpace a (2 * D) := by
      simpa only [two_mul] using markedSpace_star_mul_mem a hX hY
    simpa only [map_mul, map_star, MulMemClass.coe_mul, StarMemClass.coe_star] using
      htr (star X * Y) hp
  · intro hi
    apply (distance_gt_iff_trace_eq a π (2 * D)).mpr
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      rcases hZ with ⟨w, hw, rfl⟩
      rcases wordEval_split a w D hw with ⟨X, hX, Y, hY, hp⟩
      rw [← hp]
      simpa only [map_mul, map_star, MulMemClass.coe_mul, StarMemClass.coe_star] using
        hi X hX Y hY
    | zero => simp
    | add X Y hX hY ihX ihY =>
      simpa only [map_add, AddMemClass.coe_add, normalizedTrace_add] using
        congrArg₂ (fun x y : ℂ => x + y) ihX ihY
    | smul r X hX ih =>
      simpa only [map_smul, SetLike.val_smul, normalizedTrace_smul] using
        congrArg (fun x : ℂ => r * x) ih

theorem proposition_4_2_proof
    (b : Fin s → Matrix nB nB ℂ) (hπ : ∀ i, π (gen a i) = b i) (D : ℕ) :
    ((((2 * D : ℕ) : ℕ∞) < relDist a π ↔
        ∀ X ∈ markedSpace a D, ∀ Y ∈ markedSpace a D,
          normalizedTrace (star (π X) * π Y) =
            normalizedTrace (star (X : Matrix nA nA ℂ) * (Y : Matrix nA nA ℂ))) ∧
      (((2 * D : ℕ) : ℕ∞) < relDist a π →
        (∀ X ∈ markedSpace a D, norm2 (π X) = norm2 (X : Matrix nA nA ℂ)) ∧
          Set.InjOn π (markedSpace a D : Set (genAlg a)))) := by
  refine ⟨distance_gt_iff_inner_eq a π D, ?_⟩
  intro h
  have hi := (distance_gt_iff_inner_eq a π D).mp h
  constructor
  · intro X hX
    exact congrArg (fun z : ℂ => Real.sqrt z.re) (hi X hX X hX)
  · intro X hX Y hY hXY
    have hsub : X - Y ∈ markedSpace a D := (markedSpace a D).sub_mem hX hY
    have hz := hi (X - Y) hsub (X - Y) hsub
    have hpizero : π (X - Y) = 0 := by
      rw [map_sub, hXY, sub_self]
    have hmat : ((X - Y : genAlg a) : Matrix nA nA ℂ) = 0 := by
      apply (normalizedTrace_star_mul_self_eq_zero_iff _).mp
      simpa only [hpizero, star_zero, zero_mul, normalizedTrace_zero] using hz.symm
    exact sub_eq_zero.mp (Subtype.ext hmat)

end RelDecoding

open RelDecoding
open LIDT.MIPStarRE.Quantum

/-- **Proposition 4.2 (Sharp degree–distance criterion).** For an integer `D ≥ 0`, the condition
`2D < d_rel` (47) is equivalent to `τ_B(π(X)∗π(Y)) = τ_A(X∗Y)` for all `X, Y ∈ 𝓕ᴬ_D` (48). In
particular, when `2D < d_rel`, `π` is an isometry from `𝓕ᴬ_D` onto `𝓕ᴮ_D = π(𝓕ᴬ_D)`:
`∥π(X)∥_{2,B} = ∥X∥_{2,A}` for `X ∈ 𝓕ᴬ_D`, and `π` is injective on `𝓕ᴬ_D`. Shang, Stilck França,
*From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative
Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…), Proposition 4.2, p.18 (and the
sentence after its proof: "In particular, π is injective on 𝓕ᴬ_D").

**Formalization Note.** `A = C∗(I_A, a₁, …, a_s)` is `StarAlgebra.adjoin ℂ (Set.range a)` inside
`Matrix nA nA ℂ` (in finite dimension the generated ∗-subalgebra is the generated C∗-algebra);
`π` is any unital ∗-homomorphism from `A` into `Matrix nB nB ℂ` with `π(aᵢ) = bᵢ`, whose range is
`B = C∗(I_B, b)`; `τ_L = Tr / N_L` (`normalizedTrace`), `∥X∥_{2,L} = √(τ_L(X∗X))` (`norm2`);
`𝓕ᴬ_D` is the span of marked words of length at most `D` (`markedSpace`); `d_rel ∈ ℕ∞` with `+∞`
for the empty minimum (`relDist`). "Onto `𝓕ᴮ_D`" holds by the definition `𝓕ᴮ_D = π(𝓕ᴬ_D)`. The
index types may be empty (then `τ ≡ 0` by Lean's `x / 0 = 0`). -/
theorem solution {nA nB : Type*} [Fintype nA] [DecidableEq nA] [Fintype nB]
    [DecidableEq nB] {s : ℕ} (a : Fin s → Matrix nA nA ℂ) (b : Fin s → Matrix nB nB ℂ)
    (π : genAlg a →⋆ₐ[ℂ] Matrix nB nB ℂ) (hπ : ∀ i, π (gen a i) = b i) (D : ℕ) :
    ((((2 * D : ℕ) : ℕ∞) < relDist a π ↔
        ∀ X ∈ markedSpace a D, ∀ Y ∈ markedSpace a D,
          normalizedTrace (star (π X) * π Y) =
            normalizedTrace (star (X : Matrix nA nA ℂ) * (Y : Matrix nA nA ℂ))) ∧
      (((2 * D : ℕ) : ℕ∞) < relDist a π →
        (∀ X ∈ markedSpace a D, norm2 (π X) = norm2 (X : Matrix nA nA ℂ)) ∧
          Set.InjOn π (markedSpace a D : Set (genAlg a)))) := by
  exact RelDecoding.proposition_4_2_proof a π b hπ D

#print axioms solution
