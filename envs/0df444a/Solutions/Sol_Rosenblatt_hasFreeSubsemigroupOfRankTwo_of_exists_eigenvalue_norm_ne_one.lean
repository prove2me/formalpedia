-- Prove2me | solution 1 for Rosenblatt.hasFreeSubsemigroupOfRankTwo_of_exists_eigenvalue_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-21T17:55:52.661382+00:00
-- url     : https://prove2.me/submissions/241c03e6-74eb-4699-8e29-fb9c9b36135f

import Definitions.Def_Chou_Growth
import Theorems.Thm_Rosenblatt_injective_lift_of_forall_mul_mem_of_forall_mul_ne
import Mathlib

/-!
# Rosenblatt, Theorem 4.17 (p. 47)

*Invariant measures and growth conditions*, Trans. Amer. Math. Soc. 193 (1974).

Given an extension `e → ℤ^r → G → H → e`, if conjugation by some `g ∈ G` acts on `ℤ^r` with an
eigenvalue off the unit circle, then `G` has a free subsemigroup on two generators.

This file builds the two ingredients Rosenblatt's proof uses besides Corollary 2.5.

* **Lemma 4.16** (p. 46): if `|x| ≥ 3` then two `±1`-coefficient combinations of distinct
  positive powers of `x` agree only if they are the same combination.  Equivalently — and this
  is the form Theorem 4.17 actually uses, where it concludes that two polynomials "are
  identical" — a nonzero polynomial whose coefficients all lie in `{-1, 0, 1}` has no complex
  root of modulus `≥ 3`.  In Mathlib this is a corollary of Cauchy's bound on the roots: the
  bound is `(sup of the lower coefficients)/(leading coefficient) + 1`, which for such a
  polynomial is at most `2`.

* **Lemma 4.15** (p. 46): for a real `n × n` matrix `T` with eigenvalue `φ`, there are constants
  `K₁, …, Kₙ ∈ ℂ`, not all zero, such that any relation `∑ Pᵢ(T) aᵢ = ∑ Qᵢ(T) aᵢ` between
  polynomial combinations of the standard basis forces `∑ Pᵢ(φ) Kᵢ = ∑ Qᵢ(φ) Kᵢ`.  The
  constants are the coordinates of an eigenvector of the transpose.

Neither is published as its own leaf: 4.16 is a short consequence of a Mathlib bound, and 4.15
is linear algebra local to this argument.  The published leaf is Corollary 2.5, which is the
general tool, and Theorem 4.17 itself.
-/

namespace Rosenblatt

open Polynomial
open scoped Matrix

/-! ### Lemma 4.16 -/

/-- **Lemma 4.16**, in the form Theorem 4.17 uses it: a nonzero integer polynomial whose
coefficients all lie in `{-1, 0, 1}` has no complex root of modulus at least `3`.  Cauchy's
bound on the roots is `(sup of the lower coefficients)/(leading coefficient) + 1`, which here is
at most `2`. -/
theorem aeval_ne_zero_of_abs_coeff_le_one {p : Polynomial ℤ} (hp : p ≠ 0)
    (hc : ∀ n, |p.coeff n| ≤ 1) {x : ℂ} (hx : 3 ≤ ‖x‖) :
    Polynomial.aeval x p ≠ 0 := by
  intro hroot
  have hinj : Function.Injective (Int.castRingHom ℂ) := fun a b h => by simpa using h
  set q := p.map (Int.castRingHom ℂ) with hq
  have hq0 : q ≠ 0 := by
    rw [hq, Ne, Polynomial.map_eq_zero_iff hinj]
    exact hp
  have hrootq : q.IsRoot x := by
    have heq : Polynomial.aeval x p = q.eval x := by
      rw [hq, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]
    rw [Polynomial.IsRoot.def, ← heq]
    exact hroot
  have hbound := Polynomial.IsRoot.norm_lt_cauchyBound hq0 hrootq
  have hcoeff : ∀ i, ‖q.coeff i‖₊ ≤ 1 := by
    intro i
    have hci : q.coeff i = ((p.coeff i : ℤ) : ℂ) := by simp [hq]
    rw [hci, ← NNReal.coe_le_coe]
    have h1 : ((|p.coeff i| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hc i
    simpa [Int.norm_eq_abs] using h1
  have hlc : ‖q.leadingCoeff‖₊ = 1 := by
    rw [hq, Polynomial.leadingCoeff_map_of_injective hinj]
    have hne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp
    have habs : |p.leadingCoeff| = 1 := le_antisymm (hc _) (Int.one_le_abs hne)
    rw [← NNReal.coe_inj]
    have h2 : ((|p.leadingCoeff| : ℤ) : ℝ) = 1 := by exact_mod_cast habs
    simpa [Int.norm_eq_abs] using h2
  have hcb : Polynomial.cauchyBound q ≤ 2 := by
    rw [Polynomial.cauchyBound, hlc, div_one]
    have hs : Finset.sup (Finset.range q.natDegree) (fun i => ‖q.coeff i‖₊) ≤ 1 :=
      Finset.sup_le fun i _ => hcoeff i
    calc Finset.sup (Finset.range q.natDegree) (fun i => ‖q.coeff i‖₊) + 1
        ≤ 1 + 1 := add_le_add hs le_rfl
      _ = 2 := by norm_num
  have hlt : ‖x‖₊ < 2 := lt_of_lt_of_le hbound hcb
  rw [← NNReal.coe_lt_coe] at hlt
  simp only [coe_nnnorm, NNReal.coe_ofNat] at hlt
  linarith

/-! ### Lemma 4.15 -/

/-- If `φ` is an eigenvalue of `T` then it is an eigenvalue of the transpose, i.e. `T` has a
*left* eigenvector.  Both conditions say `det (T - φ) = 0`, and a determinant is invariant under
transposition. -/
theorem exists_vecMul_eq_smul {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (φ : ℂ)
    (hφ : ∃ v : Fin n → ℂ, v ≠ 0 ∧ T *ᵥ v = φ • v) :
    ∃ K : Fin n → ℂ, K ≠ 0 ∧ K ᵥ* T = φ • K := by
  obtain ⟨v, hv0, hv⟩ := hφ
  have hdet : (T - φ • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
  have hdetT : (Tᵀ - φ • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    have hT : (Tᵀ - φ • (1 : Matrix (Fin n) (Fin n) ℂ))
        = (T - φ • (1 : Matrix (Fin n) (Fin n) ℂ))ᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hT, Matrix.det_transpose, hdet]
  obtain ⟨K, hK0, hK⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdetT
  refine ⟨K, hK0, ?_⟩
  rw [← Matrix.mulVec_transpose]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hK
  exact hK

/-- The functional `v ↦ K ⬝ᵥ v` attached to a left eigenvector turns `T` into multiplication by
`φ`, on every power. -/
theorem dotProduct_pow_mulVec {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} {φ : ℂ} {K : Fin n → ℂ}
    (hK : K ᵥ* T = φ • K) (v : Fin n → ℂ) (m : ℕ) :
    K ⬝ᵥ ((T ^ m) *ᵥ v) = φ ^ m * (K ⬝ᵥ v) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hK,
        smul_dotProduct, ih, pow_succ']
      ring

/-- The same for an arbitrary polynomial in `T`. -/
theorem dotProduct_aeval_mulVec {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} {φ : ℂ} {K : Fin n → ℂ}
    (hK : K ᵥ* T = φ • K) (v : Fin n → ℂ) (R : Polynomial ℂ) :
    K ⬝ᵥ ((Polynomial.aeval T R) *ᵥ v) = Polynomial.aeval φ R * (K ⬝ᵥ v) := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, Matrix.add_mulVec, dotProduct_add, hp, hq, add_mul]
  | monomial m c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul,
        Matrix.smul_mulVec, dotProduct_smul, dotProduct_pow_mulVec hK]
      ring

/-- **Lemma 4.15** (p. 46), in the form Theorem 4.17 uses it: for a complex eigenvalue `φ` of
`T` there is a basis index `i` such that any polynomial killing the `i`-th basis vector under
`T` also vanishes at `φ`.

Rosenblatt states it as the existence of constants `K₁, …, Kₙ`, not all zero, converting a
relation `∑ Pᵢ(T) aᵢ = ∑ Qᵢ(T) aᵢ` into `∑ Pᵢ(φ) Kᵢ = ∑ Qᵢ(φ) Kᵢ`; the constants are the
coordinates of a left eigenvector, and Theorem 4.17 uses only the single index where the
eigenvector is nonzero, which is what is recorded here. -/
theorem exists_index_aeval_eq_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (φ : ℂ)
    (hφ : ∃ v : Fin n → ℂ, v ≠ 0 ∧ T *ᵥ v = φ • v) :
    ∃ i : Fin n, ∀ R : Polynomial ℂ,
      (Polynomial.aeval T R) *ᵥ (Pi.single i 1) = 0 → Polynomial.aeval φ R = 0 := by
  obtain ⟨K, hK0, hK⟩ := exists_vecMul_eq_smul T φ hφ
  obtain ⟨i, hi⟩ : ∃ i, K i ≠ 0 := by
    by_contra h
    exact hK0 (funext fun i => by simpa using not_not.1 (fun hh => h ⟨i, hh⟩))
  refine ⟨i, fun R hR => ?_⟩
  have h1 := dotProduct_aeval_mulVec hK (Pi.single i 1) R
  rw [hR, dotProduct_zero] at h1
  have h2 : K ⬝ᵥ (Pi.single i (1 : ℂ)) = K i := by simp
  rw [h2] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_right hi

end Rosenblatt

/-!
# Theorem 4.17: the group-theoretic infrastructure

Rosenblatt, p. 47.  Setting: a group `G` with a normal subgroup `A` isomorphic to `ℤ^r`, an
element `g`, and an integer matrix `T` giving conjugation by `g` in coordinates.

Two facts carry all the group theory of the proof; the rest is polynomial bookkeeping.

* `pow_mul_emb` — conjugation iterated: `gᵏ · ι(w) = ι(Tᵏ w) · gᵏ`.  This is what lets the
  computation push every `g` to the right and collect the abelian parts, which is how
  Rosenblatt's set `𝒜` is closed under left multiplication by his `x` and `y`.
* `pow_matrix_eq_one_of_mem` — if some power of `g` lands in `A`, then that power of `T` is the
  identity.  Conjugation by an element of `A` is trivial on `A`, because `A` is abelian; so
  `T ^ M` acts as the identity and injectivity of the embedding finishes it.  Rosenblatt uses
  this in a single clause ("since otherwise there is some `M ≥ 1` with `g^M ∈ ℤ^r` and thus
  `r_g` would have all eigenvalues of absolute value 1"), and `norm_eq_one_of_pow_eq_one` draws
  the consequence for the eigenvalue.
-/

namespace Rosenblatt

open scoped Matrix

section Emb

variable {G : Type*} [Group G] {r : ℕ} (A : Subgroup G)
  (e : A ≃* Multiplicative (Fin r → ℤ))

/-- The embedding of `ℤ^r` into `G` determined by the isomorphism. -/
def emb (z : Fin r → ℤ) : G := ((e.symm (Multiplicative.ofAdd z) : A) : G)

theorem emb_mem (z : Fin r → ℤ) : emb A e z ∈ A := (e.symm (Multiplicative.ofAdd z)).2

theorem emb_injective : Function.Injective (emb A e) := fun z w h =>
  Multiplicative.ofAdd.injective (e.symm.injective (Subtype.ext h))

end Emb

section Conj

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

/-- Conjugation by `g`, moved to the other side. -/
theorem mul_emb (z : Fin r → ℤ) : g * emb A e z = emb A e (T *ᵥ z) * g := by
  have h := hT z
  calc g * emb A e z = (g * emb A e z * g⁻¹) * g := by group
    _ = emb A e (T *ᵥ z) * g := by rw [h]

/-- Conjugation by `g ^ k`, iterated: the abelian part is hit by `T ^ k`. -/
theorem pow_mul_emb (k : ℕ) (z : Fin r → ℤ) :
    g ^ k * emb A e z = emb A e ((T ^ k) *ᵥ z) * g ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc g ^ (k + 1) * emb A e z = g * (g ^ k * emb A e z) := by rw [pow_succ']; group
        _ = g * (emb A e ((T ^ k) *ᵥ z) * g ^ k) := by rw [ih]
        _ = (g * emb A e ((T ^ k) *ᵥ z)) * g ^ k := by group
        _ = (emb A e (T *ᵥ ((T ^ k) *ᵥ z)) * g) * g ^ k := by rw [mul_emb hT]
        _ = emb A e ((T ^ (k + 1)) *ᵥ z) * g ^ (k + 1) := by
              rw [Matrix.mulVec_mulVec, ← pow_succ']
              group

/-- If a power of `g` lies in `A`, that power of `T` is the identity: conjugation by an element
of the abelian group `A` is trivial on `A`. -/
theorem pow_matrix_eq_one_of_mem {M : ℕ} (hM : g ^ M ∈ A) : (T ^ M) = 1 := by
  have key : ∀ z : Fin r → ℤ, (T ^ M) *ᵥ z = z := by
    intro z
    refine emb_injective A e ?_
    have hmem : emb A e z ∈ A := emb_mem A e z
    have hcomm : g ^ M * emb A e z = emb A e z * g ^ M := by
      have h1 : (⟨g ^ M, hM⟩ : A) * ⟨emb A e z, hmem⟩ = ⟨emb A e z, hmem⟩ * ⟨g ^ M, hM⟩ :=
        e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
      exact congrArg Subtype.val h1
    have h3 := pow_mul_emb hT M z
    rw [hcomm] at h3
    exact (mul_right_cancel h3).symm
  refine Matrix.ext_of_mulVec_single ?_
  intro j
  rw [Matrix.one_mulVec]
  exact key (Pi.single j 1)

end Conj

/-- Casting a matrix identity to `ℂ`. -/
theorem map_pow_eq_one {r M : ℕ} {T : Matrix (Fin r) (Fin r) ℤ} (hpow : T ^ M = 1) :
    (T.map (fun z : ℤ => (z : ℂ))) ^ M = 1 := by
  have hmap : T.map (fun z : ℤ => (z : ℂ)) = (Int.castRingHom ℂ).mapMatrix T := rfl
  rw [hmap, ← map_pow, hpow, map_one]

/-- Powers of a matrix act on an eigenvector by powers of the eigenvalue. -/
theorem mulVec_pow_smul {r : ℕ} {S : Matrix (Fin r) (Fin r) ℂ} {φ : ℂ} {v : Fin r → ℂ}
    (hev : S *ᵥ v = φ • v) : ∀ k : ℕ, (S ^ k) *ᵥ v = φ ^ k • v := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hev, smul_smul,
        pow_succ', mul_comm (φ ^ k) φ]

/-- An eigenvalue of a complex matrix some power of which is the identity has modulus one. -/
theorem norm_eq_one_of_pow_eq_one {r M : ℕ} (hM : M ≠ 0) {S : Matrix (Fin r) (Fin r) ℂ}
    (hpow : S ^ M = 1) {φ : ℂ} {v : Fin r → ℂ} (hv : v ≠ 0) (hev : S *ᵥ v = φ • v) :
    ‖φ‖ = 1 := by
  have h1 : φ ^ M • v = v := by rw [← mulVec_pow_smul hev M, hpow, Matrix.one_mulVec]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.1 fun hh => h ⟨i, hh⟩)
  have h2 : φ ^ M = 1 := by
    have h := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact mul_right_cancel₀ hi (by rw [one_mul]; exact h)
  have h3 : ‖φ‖ ^ M = 1 := by rw [← norm_pow, h2, norm_one]
  rcases lt_trichotomy ‖φ‖ 1 with h | h | h
  · exact absurd (h3 ▸ pow_lt_one₀ (norm_nonneg φ) h hM) (lt_irrefl 1)
  · exact h
  · exact absurd (h3 ▸ one_lt_pow₀ h hM) (lt_irrefl 1)

/-! ### Rosenblatt's polynomials: coefficients `0` or `1`, no constant term -/

/-- The polynomials Rosenblatt's set `𝒜` is built from: every coefficient is `0` or `1`, and
there is no constant term. -/
def Good (P : Polynomial ℤ) : Prop :=
  (∀ k, P.coeff k = 0 ∨ P.coeff k = 1) ∧ P.coeff 0 = 0

theorem Good.abs_coeff_le_one {P : Polynomial ℤ} (h : Good P) (k : ℕ) : |P.coeff k| ≤ 1 := by
  rcases h.1 k with hk | hk <;> simp [hk]

/-- `y` sends `P` to `X * P`, which is again good. -/
theorem good_X_mul {P : Polynomial ℤ} (h : Good P) : Good (Polynomial.X * P) := by
  refine ⟨fun k => ?_, Polynomial.coeff_X_mul_zero P⟩
  cases k with
  | zero => exact Or.inl (Polynomial.coeff_X_mul_zero P)
  | succ k => rw [Polynomial.coeff_X_mul]; exact h.1 k

/-- `x` sends `P` to `X * P + X`, which is again good — this is where "no constant term" is
used, to stop the coefficient of `X` reaching `2`. -/
theorem good_X_mul_add_X {P : Polynomial ℤ} (h : Good P) :
    Good (Polynomial.X * P + Polynomial.X) := by
  constructor
  · intro k
    cases k with
    | zero => exact Or.inl (by simp)
    | succ k =>
        rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_X]
        cases k with
        | zero => exact Or.inr (by simp [h.2])
        | succ k =>
            have hne : (1 : ℕ) ≠ k + 1 + 1 := by omega
            rw [if_neg hne, add_zero]
            exact h.1 (k + 1)
  · simp

/-- The degree-one coefficient of `X * P + X` is `1`, while that of `X * Q` is `0`.  This is the
contradiction at the end of the disjointness argument. -/
theorem coeff_one_X_mul_add_X {P : Polynomial ℤ} (h : Good P) :
    (Polynomial.X * P + Polynomial.X).coeff 1 = 1 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, h.2, Polynomial.coeff_X]
  simp

theorem coeff_one_X_mul {Q : Polynomial ℤ} (h : Good Q) : (Polynomial.X * Q).coeff 1 = 0 := by
  rw [Polynomial.coeff_X_mul, h.2]

/-- A difference of good polynomials has coefficients in `{-1, 0, 1}`, which is exactly what
Lemma 4.16 asks for. -/
theorem abs_coeff_sub_le_one {P Q : Polynomial ℤ} (hP : Good P) (hQ : Good Q) (k : ℕ) :
    |(P - Q).coeff k| ≤ 1 := by
  rw [Polynomial.coeff_sub]
  rcases hP.1 k with h1 | h1 <;> rcases hQ.1 k with h2 | h2 <;> simp [h1, h2]

/-! ### Lemma 4.15 for integer matrices and integer polynomials

The group computation happens over `ℤ` while the eigenvalue lives in `ℂ`, so Lemma 4.15 is
needed in the mixed form: an integer polynomial killing a basis vector under an integer matrix
vanishes at the complex eigenvalue.
-/

/-- Evaluating an integer polynomial at an integer matrix commutes with casting to `ℂ`.  Proved
at the `eval₂` level, where the only thing needed is that a ring homomorphism out of `ℤ` is
unique. -/
theorem map_aeval_int {r : ℕ} (T : Matrix (Fin r) (Fin r) ℤ) (R : Polynomial ℤ) :
    ((Int.castRingHom ℂ).mapMatrix) (Polynomial.aeval T R)
      = Polynomial.aeval (((Int.castRingHom ℂ).mapMatrix) T)
          (R.map (Int.castRingHom ℂ)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  try exact Subsingleton.elim _ _

/-- Casting the polynomial does not change its value at a complex number. -/
theorem aeval_map_int (R : Polynomial ℤ) (φ : ℂ) :
    Polynomial.aeval φ (R.map (Int.castRingHom ℂ)) = Polynomial.aeval φ R := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  try exact Subsingleton.elim _ _

theorem exists_index_aeval_int_eq_zero {r : ℕ} (T : Matrix (Fin r) (Fin r) ℤ) (φ : ℂ)
    {v : Fin r → ℂ} (hv : v ≠ 0)
    (hev : (T.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v) :
    ∃ i : Fin r, ∀ R : Polynomial ℤ,
      (Polynomial.aeval T R) *ᵥ (Pi.single i (1 : ℤ)) = 0 → Polynomial.aeval φ R = 0 := by
  obtain ⟨i, hi⟩ :=
    exists_index_aeval_eq_zero (T.map (fun z : ℤ => (z : ℂ))) φ ⟨v, hv, hev⟩
  refine ⟨i, fun R hR => ?_⟩
  have hzero : (Polynomial.aeval T R).map (fun z : ℤ => (z : ℂ)) *ᵥ (Pi.single i (1 : ℂ)) = 0 := by
    funext k
    have h1 := RingHom.map_mulVec (Int.castRingHom ℂ) (Polynomial.aeval T R)
      (Pi.single i (1 : ℤ)) k
    simp only [Int.coe_castRingHom] at h1
    have h2 : ((Int.cast : ℤ → ℂ) ∘ (Pi.single i (1 : ℤ))) = Pi.single i (1 : ℂ) := by
      funext j
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
    rw [h2] at h1
    rw [← h1, hR]
    simp
  have halg := map_aeval_int T R
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at halg
  rw [halg] at hzero
  have := hi (R.map (Int.castRingHom ℂ)) hzero
  rwa [aeval_map_int] at this

/-! ### Rosenblatt's set, and Theorem 4.17 when the eigenvalue is large -/

section Main

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)}

theorem emb_add (z w : Fin r → ℤ) : emb A e (z + w) = emb A e z * emb A e w := by
  show ((e.symm (Multiplicative.ofAdd (z + w)) : A) : G) = _
  rw [show Multiplicative.ofAdd (z + w)
      = Multiplicative.ofAdd z * Multiplicative.ofAdd w from rfl, map_mul]
  rfl

variable (A e) (g : G) (T : Matrix (Fin r) (Fin r) ℤ)

/-- Rosenblatt's set `𝒜` (p. 47): the elements `[P(Tⁿ)a] gᵐ` with `m ≥ 1` and `P` good. -/
def bigA (n : ℕ) (a : Fin r → ℤ) : Set G :=
  { w | ∃ (P : Polynomial ℤ) (m : ℕ), Good P ∧ 1 ≤ m ∧
      w = emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a) * g ^ m }

theorem bigA_nonempty (n : ℕ) (a : Fin r → ℤ) : (bigA A e g T n a).Nonempty := by
  refine ⟨_, Polynomial.X, 1, ⟨fun k => ?_, by simp⟩, le_rfl, rfl⟩
  rw [Polynomial.coeff_X]
  split <;> simp

end Main

section Main2

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

/-- The effect of multiplying by `x = gⁿ a`: the polynomial becomes `X·P + X`. -/
theorem x_mul_eq (n m : ℕ) (a : Fin r → ℤ) (P : Polynomial ℤ) :
    (g ^ n * emb A e a) * (emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a) * g ^ m)
      = emb A e ((Polynomial.aeval (T ^ n) (Polynomial.X * P + Polynomial.X)) *ᵥ a)
          * g ^ (n + m) := by
  have hvec : (Polynomial.aeval (T ^ n) (Polynomial.X * P + Polynomial.X)) *ᵥ a
      = (T ^ n) *ᵥ (a + (Polynomial.aeval (T ^ n) P) *ᵥ a) := by
    rw [map_add, Polynomial.aeval_mul, Polynomial.aeval_X, Matrix.add_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_mulVec]
    ring_nf
    try rw [add_comm]
  rw [hvec]
  calc g ^ n * emb A e a * (emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a) * g ^ m)
      = g ^ n * (emb A e a * emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a)) * g ^ m := by group
    _ = g ^ n * emb A e (a + (Polynomial.aeval (T ^ n) P) *ᵥ a) * g ^ m := by rw [← emb_add]
    _ = (emb A e ((T ^ n) *ᵥ (a + (Polynomial.aeval (T ^ n) P) *ᵥ a)) * g ^ n) * g ^ m := by
          rw [pow_mul_emb hT]
    _ = emb A e ((T ^ n) *ᵥ (a + (Polynomial.aeval (T ^ n) P) *ᵥ a)) * g ^ (n + m) := by
          rw [pow_add]; group

/-- The effect of multiplying by `y = gⁿ`: the polynomial becomes `X·P`. -/
theorem y_mul_eq (n m : ℕ) (a : Fin r → ℤ) (P : Polynomial ℤ) :
    g ^ n * (emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a) * g ^ m)
      = emb A e ((Polynomial.aeval (T ^ n) (Polynomial.X * P)) *ᵥ a) * g ^ (n + m) := by
  have hvec : (Polynomial.aeval (T ^ n) (Polynomial.X * P)) *ᵥ a
      = (T ^ n) *ᵥ ((Polynomial.aeval (T ^ n) P) *ᵥ a) := by
    rw [Polynomial.aeval_mul, Polynomial.aeval_X, Matrix.mulVec_mulVec]
  rw [hvec]
  calc g ^ n * (emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a) * g ^ m)
      = (g ^ n * emb A e ((Polynomial.aeval (T ^ n) P) *ᵥ a)) * g ^ m := by group
    _ = (emb A e ((T ^ n) *ᵥ ((Polynomial.aeval (T ^ n) P) *ᵥ a)) * g ^ n) * g ^ m := by
          rw [pow_mul_emb hT]
    _ = emb A e ((T ^ n) *ᵥ ((Polynomial.aeval (T ^ n) P) *ᵥ a)) * g ^ (n + m) := by
          rw [pow_add]; group

/-- `x = gⁿ a` and `y = gⁿ` carry `𝒜` into itself. -/
theorem mul_mem_bigA (n : ℕ) (a : Fin r → ℤ) {w : G} (hw : w ∈ bigA A e g T n a) :
    (g ^ n * emb A e a) * w ∈ bigA A e g T n a ∧ g ^ n * w ∈ bigA A e g T n a := by
  obtain ⟨P, m, hP, hm, rfl⟩ := hw
  exact ⟨⟨Polynomial.X * P + Polynomial.X, n + m, good_X_mul_add_X hP, by omega,
      x_mul_eq hT n m a P⟩,
    ⟨Polynomial.X * P, n + m, good_X_mul hP, by omega, y_mul_eq hT n m a P⟩⟩

/-- Mismatched `g`-exponents would put a positive power of `g` inside `A`. -/
theorem pow_mem_of_ne {u w : Fin r → ℤ} {k₁ k₂ : ℕ}
    (h : emb A e u * g ^ k₁ = emb A e w * g ^ k₂) (hle : k₂ ≤ k₁) : g ^ (k₁ - k₂) ∈ A := by
  have h1 : emb A e u * g ^ (k₁ - k₂) * g ^ k₂ = emb A e w * g ^ k₂ := by
    rw [← h, mul_assoc, ← pow_add]
    congr 2
    omega
  have h2 : emb A e u * g ^ (k₁ - k₂) = emb A e w := mul_right_cancel h1
  have h3 : g ^ (k₁ - k₂) = (emb A e u)⁻¹ * emb A e w := by rw [← h2]; group
  rw [h3]
  exact A.mul_mem (A.inv_mem (emb_mem A e u)) (emb_mem A e w)

/-- The two translates of `𝒜` are disjoint.  The eigenvalue hypothesis enters twice: `hnotmem`
rules out mismatched `g`-exponents, and `hi` together with Lemma 4.16 rules out equal ones. -/
theorem disjoint_bigA {φ : ℂ} (n : ℕ) (i : Fin r)
    (hi : ∀ R : Polynomial ℤ,
      (Polynomial.aeval (T ^ n) R) *ᵥ (Pi.single i (1 : ℤ)) = 0 → Polynomial.aeval (φ ^ n) R = 0)
    (hlarge : (3 : ℝ) ≤ ‖φ ^ n‖) (hnotmem : ∀ M : ℕ, M ≠ 0 → g ^ M ∉ A)
    {p q : G} (hp : p ∈ bigA A e g T n (Pi.single i 1))
    (hq : q ∈ bigA A e g T n (Pi.single i 1)) :
    (g ^ n * emb A e (Pi.single i 1)) * p ≠ g ^ n * q := by
  obtain ⟨P, m₁, hP, hm₁, rfl⟩ := hp
  obtain ⟨Q, m₂, hQ, hm₂, rfl⟩ := hq
  rw [x_mul_eq hT, y_mul_eq hT]
  intro hcon
  rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · exact hnotmem ((n + m₂) - (n + m₁)) (by omega) (pow_mem_of_ne hT hcon.symm (by omega))
  · subst heq
    have hemb : emb A e ((Polynomial.aeval (T ^ n) (Polynomial.X * P + Polynomial.X)) *ᵥ
          (Pi.single i 1))
        = emb A e ((Polynomial.aeval (T ^ n) (Polynomial.X * Q)) *ᵥ (Pi.single i 1)) :=
      mul_right_cancel hcon
    have hvec := emb_injective A e hemb
    set R := (Polynomial.X * P + Polynomial.X) - (Polynomial.X * Q) with hR
    have hzero : (Polynomial.aeval (T ^ n) R) *ᵥ (Pi.single i (1 : ℤ)) = 0 := by
      rw [hR, map_sub, Matrix.sub_mulVec, hvec, sub_self]
    have hR0 : R ≠ 0 := by
      intro h0
      have h1 : R.coeff 1 = 1 := by
        rw [hR, Polynomial.coeff_sub, coeff_one_X_mul_add_X hP, coeff_one_X_mul hQ, sub_zero]
      rw [h0] at h1
      simp at h1
    exact aeval_ne_zero_of_abs_coeff_le_one hR0
      (abs_coeff_sub_le_one (good_X_mul_add_X hP) (good_X_mul hQ)) hlarge (hi R hzero)
  · exact hnotmem ((n + m₁) - (n + m₂)) (by omega) (pow_mem_of_ne hT hcon (by omega))

end Main2

/-- Casting commutes with taking powers of a matrix. -/
theorem map_pow_comm {r : ℕ} (T : Matrix (Fin r) (Fin r) ℤ) (n : ℕ) :
    (T ^ n).map (fun z : ℤ => (z : ℂ)) = (T.map (fun z : ℤ => (z : ℂ))) ^ n := by
  have h := map_pow ((Int.castRingHom ℂ).mapMatrix) T n
  simpa [RingHom.mapMatrix_apply] using h

section Final

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G}
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

/-- **Theorem 4.17 when the eigenvalue is large.**  Rosenblatt reduces the general case to this
one by replacing `g` with `g⁻¹`. -/
theorem hasFreeSubsemigroup_of_one_lt_norm {φ : ℂ} {v : Fin r → ℂ} (hv : v ≠ 0)
    (hev : (T.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v) (hφ : 1 < ‖φ‖) :
    Chou.HasFreeSubsemigroupOfRankTwo G := by
  -- no positive power of `g` lies in `A`, or every eigenvalue would be on the unit circle
  have hnotmem : ∀ M : ℕ, M ≠ 0 → g ^ M ∉ A := by
    intro M hM hmem
    have h1 : T ^ M = 1 := pow_matrix_eq_one_of_mem hT hmem
    have h2 : ‖φ‖ = 1 :=
      norm_eq_one_of_pow_eq_one hM (map_pow_eq_one h1) hv hev
    rw [h2] at hφ
    exact absurd hφ (lt_irrefl 1)
  -- choose `n` with `‖φⁿ‖ ≥ 3`
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 : ℝ) hφ
  have hlarge : (3 : ℝ) ≤ ‖φ ^ n‖ := by rw [norm_pow]; exact hn.le
  -- Lemma 4.15 at `Tⁿ`, whose eigenvalue is `φⁿ`
  have hevn : ((T ^ n).map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ ^ n • v := by
    rw [map_pow_comm]
    exact mulVec_pow_smul hev n
  obtain ⟨i, hi⟩ := exists_index_aeval_int_eq_zero (T ^ n) (φ ^ n) hv hevn
  refine ⟨g ^ n * emb A e (Pi.single i 1), g ^ n, ?_⟩
  refine injective_lift_of_forall_mul_mem_of_forall_mul_ne _ _
    (bigA A e g T n (Pi.single i 1)) (bigA_nonempty A e g T n _) (fun w hw => ?_)
    (fun w hw w' hw' => disjoint_bigA hT n i hi hlarge hnotmem hw hw')
  exact ⟨(mul_mem_bigA hT n _ hw).1, (mul_mem_bigA hT n _ hw).2⟩

end Final

/-! ### The `‖φ‖ < 1` case: passing to `g⁻¹`

This is where normality of `A` is needed.  Conjugation by `g⁻¹` also preserves `A`, so it too
is given by an integer matrix, and that matrix is a two-sided inverse of `T`.
-/

section Inverse

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G} [hA : A.Normal]
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}

/-- Coordinates of an element of `A`. -/
def embInv (A : Subgroup G) (e : A ≃* Multiplicative (Fin r → ℤ)) (x : A) : Fin r → ℤ :=
  Multiplicative.toAdd (e x)

theorem emb_embInv (x : A) : emb A e (embInv A e x) = (x : G) := by
  show ((e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e x))) : A) : G) = (x : G)
  rw [show Multiplicative.ofAdd (Multiplicative.toAdd (e x)) = e x from rfl,
    MulEquiv.symm_apply_apply]

/-- Conjugation by `g⁻¹`, in coordinates.  Well defined because `A` is normal. -/
def conjInv (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin r → ℤ)) (g : G)
    (z : Fin r → ℤ) : Fin r → ℤ :=
  embInv A e ⟨g⁻¹ * emb A e z * g, by
    simpa using ‹A.Normal›.conj_mem _ (emb_mem A e z) g⁻¹⟩

theorem emb_conjInv (z : Fin r → ℤ) :
    emb A e (conjInv A e g z) = g⁻¹ * emb A e z * g := by
  rw [conjInv, emb_embInv]

theorem conjInv_add (z w : Fin r → ℤ) :
    conjInv A e g (z + w) = conjInv A e g z + conjInv A e g w := by
  refine emb_injective A e ?_
  rw [emb_add, emb_conjInv, emb_conjInv, emb_conjInv, emb_add]
  group

/-- The matrix of conjugation by `g⁻¹`. -/
def invMatrix (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin r → ℤ)) (g : G) :
    Matrix (Fin r) (Fin r) ℤ :=
  LinearMap.toMatrix' (AddMonoidHom.mk' (conjInv A e g) (conjInv_add)).toIntLinearMap

theorem invMatrix_mulVec (z : Fin r → ℤ) :
    (invMatrix A e g) *ᵥ z = conjInv A e g z := by
  rw [← Matrix.toLin'_apply, invMatrix, Matrix.toLin'_toMatrix']
  rfl

/-- Conjugation by `g⁻¹` satisfies the same hypothesis, with the inverse matrix. -/
theorem hT_inv (z : Fin r → ℤ) :
    g⁻¹ * emb A e z * (g⁻¹)⁻¹ = emb A e ((invMatrix A e g) *ᵥ z) := by
  rw [invMatrix_mulVec, emb_conjInv, inv_inv]

variable (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

theorem mulVec_invMatrix (z : Fin r → ℤ) : T *ᵥ ((invMatrix A e g) *ᵥ z) = z := by
  refine emb_injective A e ?_
  rw [← hT, invMatrix_mulVec, emb_conjInv]
  group

theorem invMatrix_mulVec_mulVec (z : Fin r → ℤ) :
    (invMatrix A e g) *ᵥ (T *ᵥ z) = z := by
  refine emb_injective A e ?_
  rw [invMatrix_mulVec, emb_conjInv, ← hT]
  group

theorem invMatrix_mul : (invMatrix A e g) * T = 1 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  exact invMatrix_mulVec_mulVec hT _

end Inverse

/-- Casting a matrix product identity to `ℂ`. -/
theorem map_mul_eq_one {r : ℕ} {M N : Matrix (Fin r) (Fin r) ℤ} (h : M * N = 1) :
    (M.map (fun z : ℤ => (z : ℂ))) * (N.map (fun z : ℤ => (z : ℂ))) = 1 := by
  have h1 := map_mul ((Int.castRingHom ℂ).mapMatrix) M N
  have h2 : ((Int.castRingHom ℂ).mapMatrix (1 : Matrix (Fin r) (Fin r) ℤ)) = 1 := map_one _
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h1 h2
  rw [← h1, h, h2]

section Final2

variable {G : Type*} [Group G] {r : ℕ} {A : Subgroup G} [A.Normal]
  {e : A ≃* Multiplicative (Fin r → ℤ)} {g : G} {T : Matrix (Fin r) (Fin r) ℤ}
  (hT : ∀ z : Fin r → ℤ, g * emb A e z * g⁻¹ = emb A e (T *ᵥ z))

include hT

/-- **Rosenblatt, Theorem 4.17** (p. 47). -/
theorem thm417
    {φ : ℂ} {v : Fin r → ℂ} (hv : v ≠ 0)
    (hev : (T.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v) (hφ : ‖φ‖ ≠ 1) :
    Chou.HasFreeSubsemigroupOfRankTwo G := by
  rcases lt_or_gt_of_ne hφ with hlt | hgt
  · -- pass to `g⁻¹`, whose matrix is the inverse of `T`
    set T' := invMatrix A e g with hT'
    have hinv : T' * T = 1 := invMatrix_mul hT
    have hinvC : (T'.map (fun z : ℤ => (z : ℂ))) * (T.map (fun z : ℤ => (z : ℂ))) = 1 :=
      map_mul_eq_one hinv
    have hcomp : (T'.map (fun z : ℤ => (z : ℂ))) *ᵥ ((T.map (fun z : ℤ => (z : ℂ))) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hinvC, Matrix.one_mulVec]
    have hφ0 : φ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hev
      rw [hev] at hcomp
      simp only [Matrix.mulVec_zero] at hcomp
      exact hv hcomp.symm
    have hev' : (T'.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ⁻¹ • v := by
      have h1 : (T'.map (fun z : ℤ => (z : ℂ))) *ᵥ (φ • v) = v := by rw [← hev]; exact hcomp
      rw [Matrix.mulVec_smul] at h1
      have h2 : φ⁻¹ • (φ • (T'.map (fun z : ℤ => (z : ℂ)) *ᵥ v)) = φ⁻¹ • v := by rw [h1]
      rwa [smul_smul, inv_mul_cancel₀ hφ0, one_smul] at h2
    have hnorm : 1 < ‖φ⁻¹‖ := by
      rw [norm_inv]
      rw [one_lt_inv_iff₀]
      exact ⟨norm_pos_iff.2 hφ0, hlt⟩
    exact hasFreeSubsemigroup_of_one_lt_norm (hT_inv) hv hev' hnorm
  · exact hasFreeSubsemigroup_of_one_lt_norm hT hv hev hgt

end Final2

end Rosenblatt

open scoped Matrix

theorem solution {G : Type*} [Group G]
    {r : ℕ} (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin r → ℤ))
    (g : G) (T : Matrix (Fin r) (Fin r) ℤ)
    (hT : ∀ z : Fin r → ℤ,
      g * ((e.symm (Multiplicative.ofAdd z) : A) : G) * g⁻¹
        = ((e.symm (Multiplicative.ofAdd (T *ᵥ z)) : A) : G))
    (φ : ℂ) (v : Fin r → ℂ) (hv : v ≠ 0)
    (hev : (T.map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v) (hφ : ‖φ‖ ≠ 1) :
    Chou.HasFreeSubsemigroupOfRankTwo G :=
  Rosenblatt.thm417 hT hv hev hφ
