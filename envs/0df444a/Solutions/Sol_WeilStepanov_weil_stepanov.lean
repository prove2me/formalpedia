-- Prove2me | solution 1 for WeilStepanov.weil_stepanov
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T09:00:23.458282+00:00
-- url     : https://prove2.me/submissions/7aa77b99-c636-427c-9bce-2ad72fc75c4a

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Weil.Kloosterman =====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, foundation rungs W0.1 + W3.1 + W1.1

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder, ~13:30 entry). These
are the three cheap foundation nodes the Stepanov core (W4) and the moment layer
(W2) consume; each is either a genuinely new definition (the Kloosterman sum) or a
thin re-export of mature mathlib machinery under clean names.

* **W0.1 — the Kloosterman sum** (`kloosterman`): for `a b : ZMod p`,
  `S(a, b; p) = ∑_{t ∈ (ZMod p)ˣ} ψ(a·t + b·t⁻¹)` with `ψ = ZMod.stdAddChar`.
  Basic facts:
  - `norm_kloosterman_le` : the trivial bound `‖S‖ ≤ #(ZMod p)ˣ`
    (triangle inequality + `‖ψ‖ = 1`); specialised at prime `p` to `‖S‖ ≤ p − 1`
    (`norm_kloosterman_le_sub_one`).
  - `kloosterman_comm` : the symmetry `S(a, b) = S(b, a)` (`t ↦ t⁻¹` reindex).
  - `kloosterman_conj` / `kloosterman_im` : real-valuedness, `conj S = S`
    (`t ↦ −t` pairs a value with its conjugate).
  - `kloosterman_reindex_units` : the unit-rescale twist `S(a·c, b·c⁻¹) = S(a, b)`
    (`t ↦ c·t` reindex, `c` a unit).

* **W3.1 — Hasse-derivative multiplicity** (`X_sub_C_pow_dvd_iff_hasseDeriv`):
  Lemma 8, `(X − C x)^ℓ ∣ h ↔ ∀ k < ℓ, (hasseDeriv k h).eval x = 0`. Assembled from
  `Polynomial.X_sub_C_pow_dvd_iff`, `Polynomial.X_pow_dvd_iff`, `Polynomial.taylor_coeff`.

* **W1.1 — GaloisField plumbing** (`galoisField_*`): thin re-exports fixing the
  cardinality `#𝔽_{p^n} = p^n`, the Frobenius fixed-field fact `x^{p^n} = x`, and the
  absolute trace as a Frobenius-orbit sum `Tr(x) = ∑_{i<n} x^{p^i}`.
-/

namespace Salt.Weil

open scoped BigOperators
open ComplexConjugate

/-! ### W0.1 — the Kloosterman sum -/

variable {p : ℕ} [NeZero p]

/-- The **Kloosterman sum** `S(a, b; p) = ∑_{t ∈ (ZMod p)ˣ} ψ(a·t + b·t⁻¹)`, where
`ψ = ZMod.stdAddChar` is the standard primitive additive character `j ↦ exp(2πi j / p)`.
The sum runs over the *units* of `ZMod p`, so `t⁻¹` is the group inverse. -/
noncomputable def kloosterman (a b : ZMod p) : ℂ :=
  ∑ t : (ZMod p)ˣ, ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p))

/-- **Trivial bound.** `‖S(a, b; p)‖ ≤ #(ZMod p)ˣ` from the triangle inequality and
`‖ψ x‖ = 1`. -/
theorem norm_kloosterman_le (a b : ZMod p) :
    ‖kloosterman a b‖ ≤ (Fintype.card (ZMod p)ˣ : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl (fun t _ => AddChar.norm_apply _ _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Trivial bound, prime form.** For prime `p`, `‖S(a, b; p)‖ ≤ p − 1`. -/
theorem norm_kloosterman_le_sub_one [Fact p.Prime] (a b : ZMod p) :
    ‖kloosterman a b‖ ≤ (p : ℝ) - 1 := by
  have hp : (1 : ℕ) ≤ p := (Fact.out : p.Prime).one_lt.le
  refine (norm_kloosterman_le a b).trans (le_of_eq ?_)
  rw [ZMod.card_units p, Nat.cast_sub hp, Nat.cast_one]

/-- **Symmetry.** `S(a, b; p) = S(b, a; p)`, via the reindex `t ↦ t⁻¹`. -/
theorem kloosterman_comm (a b : ZMod p) : kloosterman a b = kloosterman b a := by
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
    (fun t : (ZMod p)ˣ => ZMod.stdAddChar (b * (t : ZMod p) + a * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.inv_apply, inv_inv]
  congr 1
  ring

/-- **Real-valuedness.** `conj S(a, b; p) = S(a, b; p)`: the reindex `t ↦ −t`
pairs each summand `ψ(a·t + b·t⁻¹)` with its complex conjugate `ψ(−(a·t + b·t⁻¹))`. -/
theorem kloosterman_conj (a b : ZMod p) :
    conj (kloosterman a b) = kloosterman a b := by
  have hR : 0 < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne p)
  unfold kloosterman
  rw [map_sum, ← Equiv.sum_comp (Equiv.neg (ZMod p)ˣ)
    (fun t : (ZMod p)ˣ => ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  simp only [Equiv.neg_apply]
  congr 1
  have hinv : ((-t : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) = -t⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
  rw [hinv]
  simp only [Units.val_neg]
  ring

/-- Real-valuedness, imaginary-part form: `S(a, b; p)` has zero imaginary part. -/
theorem kloosterman_im (a b : ZMod p) : (kloosterman a b).im = 0 :=
  Complex.conj_eq_iff_im.mp (kloosterman_conj a b)

/-- **Unit twist.** For a unit `c`, `S(a·c, b·c⁻¹; p) = S(a, b; p)`, via the
unit-rescale reindex `t ↦ c·t`. Combined with `kloosterman_comm` this yields the
`S(m·a, m·b)` forms. -/
theorem kloosterman_reindex_units (a b : ZMod p) (c : (ZMod p)ˣ) :
    kloosterman (a * (c : ZMod p)) (b * ((c⁻¹ : (ZMod p)ˣ) : ZMod p)) = kloosterman a b := by
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.mulLeft c)
    (fun t : (ZMod p)ˣ => ZMod.stdAddChar (a * (t : ZMod p) + b * ((t⁻¹ : (ZMod p)ˣ) : ZMod p)))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, Units.val_mul]
  congr 1
  ring

/-! ### W3.1 — Hasse-derivative multiplicity (Lemma 8) -/

open Polynomial in
/-- **W3.1 (Lemma 8).** A power `(X − C x)^ℓ` divides `h` iff all Hasse derivatives of
order `< ℓ` vanish at `x`. This is the multiplicity criterion the Stepanov auxiliary
polynomial uses to certify a high-order zero of the auxiliary function at each point of
the `D`-locus. The `←` direction (vanishing derivatives ⇒ high divisibility) is the
load-bearing one. Assembled from `X_sub_C_pow_dvd_iff` (translate to a zero at the origin),
`X_pow_dvd_iff` (divisibility ↔ low coefficients vanish), and `taylor_coeff` (the Taylor
coefficient at `x` is the Hasse derivative evaluated at `x`). -/
theorem X_sub_C_pow_dvd_iff_hasseDeriv {F : Type*} [CommRing F] (h : F[X]) (x : F) (ℓ : ℕ) :
    (X - C x) ^ ℓ ∣ h ↔ ∀ k < ℓ, (hasseDeriv k h).eval x = 0 := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  simp only [← taylor_apply, taylor_coeff]

/-! ### W1.1 — GaloisField plumbing -/

section GaloisFieldPlumbing

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The Galois field `𝔽_{p^n} = GaloisField p n` has exactly `p ^ n` elements. -/
theorem galoisField_card (h : n ≠ 0) : Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n h

/-- **Frobenius fixed field.** Every element of `𝔽_{p^n}` is fixed by the `n`-th iterate of
Frobenius: `x ^ (p ^ n) = x`. -/
theorem galoisField_pow_card (h : n ≠ 0) (x : GaloisField p n) : x ^ p ^ n = x := by
  letI := Fintype.ofFinite (GaloisField p n)
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n h]
  rw [← hcard]; exact FiniteField.pow_card x

/-- The absolute trace `𝔽_{p^n} → 𝔽_p` expanded as the Frobenius-orbit sum, in the raw
mathlib form (`Nat.card (ZMod p)` base, `finrank`-indexed range). -/
theorem galoisField_algebraMap_trace_eq_sum_pow (x : GaloisField p n) :
    algebraMap (ZMod p) (GaloisField p n) (Algebra.trace (ZMod p) (GaloisField p n) x)
      = ∑ i ∈ Finset.range (Module.finrank (ZMod p) (GaloisField p n)),
          x ^ (Nat.card (ZMod p) ^ i) :=
  FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) (GaloisField p n) x

/-- **Absolute trace as Frobenius-orbit sum, clean form.** For `n ≠ 0`,
`algebraMap (Tr x) = ∑_{i < n} x ^ (p ^ i)` — the trace pushed into `𝔽_{p^n}` is the sum of
the Frobenius conjugates of `x`. -/
theorem galoisField_trace_eq_sum_frobenius (h : n ≠ 0) (x : GaloisField p n) :
    algebraMap (ZMod p) (GaloisField p n) (Algebra.trace (ZMod p) (GaloisField p n) x)
      = ∑ i ∈ Finset.range n, x ^ (p ^ i) := by
  rw [galoisField_algebraMap_trace_eq_sum_pow, GaloisField.finrank p h, Nat.card_zmod]

end GaloisFieldPlumbing

end Salt.Weil

-- ===== Salt.Weil.Stepanov =====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, Stepanov's auxiliary polynomial (W4.1a/b)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder, ~13:30 entry), following
Harcos §5 (equations (18)–(19)). This is the heart of the Stepanov method for the
hyperelliptic point count `y² = f(x)`.

* **W4.1a — the ansatz** (`stepanovAux`): for a polynomial `f : F[X]`, exponent `ℓ`,
  parameter `J`, and coefficient data `r s : Fin J → F[X]`,
  `h_a := f^ℓ · ∑_{0≤j<J} (r_j + s_j · f^{(q-1)/2}) · X^{jq}`  (Harcos (18)),
  with `q := Fintype.card F`. Degree bookkeeping: `stepanovAux_summand_natDegree_le`
  (per block) and `stepanovAux_natDegree_le` (the total, used by the dimension count).

* **band separation** (`X_pow_dvd_of_range_sum_eq_zero`): the algebraic heart of the
  non-vanishing argument. If `∑_{j<J} g_j X^{jq} = 0` and the coefficients below the
  minimal index `i` vanish, then `X^q ∣ g_i` — the `X^{jq}` blocks isolate the lowest
  nonzero coefficient modulo `X^q`.

* **W4.1b — non-vanishing** (`stepanovAux_ne_zero`): if `f` is not a square in the
  algebraic closure and the coefficient data is not all zero (with the degree bounds
  (19) and `f(0) ≠ 0`), then `h_a ≠ 0`. Argument: were `h_a = 0`, band separation at the
  minimal nonzero index `i` gives `r_i + s_i f^{(q-1)/2} ≡ 0 (mod X^q)`; squaring and
  multiplying by `f`, together with `f^q ≡ f(0) (mod X^q)`, forces `r_i² f = f(0) s_i²`,
  so `f` is a square in `\overline{F}[X]` — a contradiction.
-/

namespace Salt.Weil

open Polynomial
open scoped BigOperators

/-! ### W4.1a — the Stepanov ansatz and its degree -/

variable {F : Type*} [Field F]

/-- **The Stepanov auxiliary polynomial** (Harcos (18)). For `f : F[X]`, exponent `ℓ`,
parameter `J`, and coefficient data `r s : Fin J → F[X]`,
`h_a := f^ℓ · ∑_{0≤j<J} (r_j + s_j · f^{(q-1)/2}) · X^{jq}`, with `q := Fintype.card F`.
The `(q-1)/2` power is the quadratic-residue twist and the `X^{jq}` windows carry the `J`
free coefficient vectors of the linear system. -/
noncomputable def stepanovAux [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X]) :
    F[X] :=
  f ^ ℓ * ∑ j : Fin J,
    (r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ ((j : ℕ) * Fintype.card F)

/-- **Degree of a single block** (Harcos (18)–(19)). With `deg r_j, deg s_j ≤ B`, the `j`-th
summand `(r_j + s_j f^{(q-1)/2}) X^{jq}` has degree at most `B + (q-1)/2·deg f + jq`. -/
theorem stepanovAux_summand_natDegree_le [Fintype F] {J : ℕ} (f : F[X]) (r s : Fin J → F[X])
    (j : Fin J) {B : ℕ} (hr : (r j).natDegree ≤ B) (hs : (s j).natDegree ≤ B) :
    ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ ((j : ℕ) * Fintype.card F)).natDegree
      ≤ B + (Fintype.card F - 1) / 2 * f.natDegree + (j : ℕ) * Fintype.card F := by
  have hA : (r j + s j * f ^ ((Fintype.card F - 1) / 2)).natDegree
      ≤ B + (Fintype.card F - 1) / 2 * f.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le (hr.trans (Nat.le_add_right _ _)) ?_)
    exact natDegree_mul_le.trans (add_le_add hs natDegree_pow_le)
  calc ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ ((j : ℕ) * Fintype.card F)).natDegree
      ≤ (r j + s j * f ^ ((Fintype.card F - 1) / 2)).natDegree
          + ((X : F[X]) ^ ((j : ℕ) * Fintype.card F)).natDegree := natDegree_mul_le
    _ = (r j + s j * f ^ ((Fintype.card F - 1) / 2)).natDegree + (j : ℕ) * Fintype.card F := by
        rw [natDegree_X_pow]
    _ ≤ B + (Fintype.card F - 1) / 2 * f.natDegree + (j : ℕ) * Fintype.card F := by
        gcongr

/-- **Degree of the auxiliary polynomial** (Harcos, top of p. 12). With `deg r_j, deg s_j ≤ B`
for all `j`, `deg h_a ≤ ℓ·deg f + (B + (q-1)/2·deg f + (J-1)q)`. This is the input to the
dimension count that makes the linear system (22) solvable. -/
theorem stepanovAux_natDegree_le [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    {B : ℕ} (hr : ∀ j, (r j).natDegree ≤ B) (hs : ∀ j, (s j).natDegree ≤ B) :
    (stepanovAux f ℓ r s).natDegree
      ≤ ℓ * f.natDegree
        + (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F) := by
  unfold stepanovAux
  refine natDegree_mul_le.trans (add_le_add natDegree_pow_le ?_)
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (stepanovAux_summand_natDegree_le f r s j (hr j) (hs j)).trans ?_
  have hj : (j : ℕ) ≤ J - 1 := by have := j.isLt; omega
  gcongr

/-! ### Band separation: the lowest `X^{jq}` block modulo `X^q` -/

/-- **Band separation lemma.** In `F[X]` (a domain), suppose the block sum
`∑_{0 ≤ j < J} g_j · X^{jq}` vanishes and every coefficient below the index `i` is zero.
Then `X^q ∣ g_i`: reducing the sum modulo `X^{(i+1)q}` kills every block except the `i`-th,
whose `X^{iq}` factor cancels to leave `X^q ∣ g_i`. This is the mechanism by which the
`X^{jq}` windows separate the coefficients in Harcos's non-vanishing argument. -/
theorem X_pow_dvd_of_range_sum_eq_zero {J q : ℕ} (g : ℕ → F[X])
    (i : ℕ) (hi : i < J) (hlow : ∀ j < i, g j = 0)
    (hsum : ∑ j ∈ Finset.range J, g j * X ^ (j * q) = 0) :
    (X : F[X]) ^ q ∣ g i := by
  -- `X^{(i+1)q}` divides the `i`-th block `g i * X^{iq}`.
  have hmem : i ∈ Finset.range J := Finset.mem_range.mpr hi
  have hdvd : (X : F[X]) ^ ((i + 1) * q) ∣ g i * X ^ (i * q) := by
    -- `g i * X^{iq}` is the negative of the erased sum.
    have hrec : g i * X ^ (i * q) = -∑ j ∈ (Finset.range J).erase i, g j * X ^ (j * q) := by
      have := Finset.sum_erase_add (Finset.range J) (fun j => g j * X ^ (j * q)) hmem
      linear_combination this + hsum
    rw [hrec, dvd_neg]
    refine Finset.dvd_sum fun j hj => ?_
    rcases Finset.mem_erase.mp hj with ⟨hji, _⟩
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hlow j hlt, zero_mul]; exact dvd_zero _
    · have hle : (i + 1) * q ≤ j * q := by gcongr; omega
      exact (pow_dvd_pow X hle).mul_left _
  -- Cancel the common `X^{iq}` factor.
  have hne : (X : F[X]) ^ (i * q) ≠ 0 := pow_ne_zero _ X_ne_zero
  rw [show (i + 1) * q = i * q + q by ring, pow_add, mul_comm (g i)] at hdvd
  exact (mul_dvd_mul_iff_left hne).mp hdvd

/-! ### W4.1b — non-vanishing of the auxiliary polynomial -/

/-- **Non-vanishing** (Harcos §5, p. 11). If `f(0) ≠ 0`, `q := Fintype.card F` is odd, the
coefficient degree bounds (19) `deg r_j, deg s_j < (q - deg f)/2` hold, `f` is *not* a square
in `\overline{F}[X]`, and the coefficient data is not all zero, then `h_a ≠ 0`.

Were `h_a = 0`, dividing by `f^ℓ` and applying band separation at the minimal nonzero index
`i` gives `X^q ∣ (r_i + s_i f^{(q-1)/2})`. Squaring (via the difference of squares) and
multiplying by `f`, together with the Frobenius identity `f^q ≡ f(0) (mod X^q)`, forces
`X^q ∣ (r_i² f - f(0) s_i²)`; the degree bounds make this polynomial have degree `< q`, so it
vanishes: `r_i² f = f(0) s_i²`. Over `\overline{F}`, `f(0)` is a square, hence `f` is a square
in `\overline{F}[X]` — contradicting the hypothesis. -/
theorem stepanovAux_ne_zero [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (hqodd : Odd (Fintype.card F)) (hf0 : f.coeff 0 ≠ 0)
    (hr : ∀ j, (r j).natDegree < (Fintype.card F - f.natDegree) / 2)
    (hs : ∀ j, (s j).natDegree < (Fintype.card F - f.natDegree) / 2)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hnz : ∃ j, r j ≠ 0 ∨ s j ≠ 0) :
    stepanovAux f ℓ r s ≠ 0 := by
  classical
  intro hzero
  unfold stepanovAux at hzero
  set q := Fintype.card F with hq
  set m := f.natDegree with hm
  set e := (q - 1) / 2 with he_def
  set K := AlgebraicClosure F with hK
  set φ := algebraMap F K with hφ
  have hf : f ≠ 0 := fun h => hf0 (by rw [h]; simp)
  -- Extend the coefficient data to `ℕ → F[X]` by zero, and form the block coefficients `g`.
  set R : ℕ → F[X] := fun n => if h : n < J then r ⟨n, h⟩ else 0 with hR
  set S : ℕ → F[X] := fun n => if h : n < J then s ⟨n, h⟩ else 0 with hS
  set g : ℕ → F[X] := fun n => R n + S n * f ^ e with hg
  have hRj : ∀ j : Fin J, R (j : ℕ) = r j := by
    intro j; rw [hR]; simp only [j.isLt, dif_pos]
  have hSj : ∀ j : Fin J, S (j : ℕ) = s j := by
    intro j; rw [hS]; simp only [j.isLt, dif_pos]
  -- `∑_{j<J} g_j X^{jq} = 0`, obtained from `h_a = 0` by cancelling `f^ℓ ≠ 0`.
  have hconv : ∑ j : Fin J, (r j + s j * f ^ e) * X ^ ((j : ℕ) * q)
      = ∑ n ∈ Finset.range J, g n * X ^ (n * q) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => g n * X ^ (n * q)) J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]; simp only [hRj j, hSj j]
  have hsum0 : ∑ n ∈ Finset.range J, g n * X ^ (n * q) = 0 := by
    rw [hconv] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero ℓ hf)
  -- The minimal index `i` with `(r_i, s_i) ≠ 0`.
  have hex : ∃ n, R n ≠ 0 ∨ S n ≠ 0 := by
    obtain ⟨j, hj⟩ := hnz
    exact ⟨(j : ℕ), by rw [hRj j, hSj j]; exact hj⟩
  set i := Nat.find hex with hi_def
  have hi_spec : R i ≠ 0 ∨ S i ≠ 0 := Nat.find_spec hex
  have hi_min : ∀ n < i, R n = 0 ∧ S n = 0 := by
    intro n hn
    simpa only [not_or, not_ne_iff] using Nat.find_min hex hn
  have hiJ : i < J := by
    by_contra hle
    have hR0 : R i = 0 := by simp only [hR, dif_neg hle]
    have hS0 : S i = 0 := by simp only [hS, dif_neg hle]
    exact hi_spec.elim (· hR0) (· hS0)
  -- Band separation: `X^q ∣ g_i = r_i + s_i f^{(q-1)/2}`.
  have hlow : ∀ n < i, g n = 0 := by
    intro n hn; rw [hg]; simp only [(hi_min n hn).1, (hi_min n hn).2, zero_mul, add_zero]
  have hdvd : (X : F[X]) ^ q ∣ R i + S i * f ^ e := by
    have := X_pow_dvd_of_range_sum_eq_zero g i hiJ hlow hsum0
    rwa [hg] at this
  -- Degree facts for `R i, S i`.
  have hRi_deg : (R i).natDegree < (q - m) / 2 := by rw [hRj ⟨i, hiJ⟩]; exact hr _
  have hSi_deg : (S i).natDegree < (q - m) / 2 := by rw [hSj ⟨i, hiJ⟩]; exact hs _
  have hqm : m + 2 ≤ q := by have := hRi_deg; omega
  -- Odd `q` gives `2·e + 1 = q`, hence `f^e · f^e · f = f^q`.
  obtain ⟨k, hk⟩ := hqodd
  have hfe : f ^ e * f ^ e * f = f ^ q := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  -- Frobenius: `X^q ∣ f^q - C (f 0)`.
  obtain ⟨p, hp_char, n, hp_prime, hpn⟩ := FiniteField.card' F
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP F p := hp_char
  have hCcq : (C (f.coeff 0)) ^ q = C (f.coeff 0) := by
    rw [← C_pow]; congr 1; exact FiniteField.pow_card _
  have hpow : (f - C (f.coeff 0)) ^ q = f ^ q - C (f.coeff 0) := by
    have hchar := sub_pow_char_pow f (C (f.coeff 0)) n
    rw [← hpn] at hchar
    rw [hchar, hCcq]
  have hfrob : (X : F[X]) ^ q ∣ f ^ q - C (f.coeff 0) := by
    rw [← hpow]; exact pow_dvd_pow_of_dvd X_dvd_sub_C q
  -- Assemble `X^q ∣ r_i² f - C (f 0) s_i²`.
  have hexp : f * ((R i + S i * f ^ e) * (R i - S i * f ^ e))
      = (R i) ^ 2 * f - (S i) ^ 2 * f ^ q := by
    linear_combination (-(S i) ^ 2) * hfe
  have h2 : (X : F[X]) ^ q ∣ (R i) ^ 2 * f - (S i) ^ 2 * f ^ q := by
    have := (hdvd.mul_right (R i - S i * f ^ e)).mul_left f
    rwa [hexp] at this
  have h3 : (X : F[X]) ^ q ∣ (S i) ^ 2 * f ^ q - (S i) ^ 2 * C (f.coeff 0) := by
    have := hfrob.mul_left ((S i) ^ 2)
    rwa [mul_sub] at this
  have hP : (X : F[X]) ^ q ∣ (R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2 := by
    have hadd := dvd_add h2 h3
    have heq : ((R i) ^ 2 * f - (S i) ^ 2 * f ^ q)
        + ((S i) ^ 2 * f ^ q - (S i) ^ 2 * C (f.coeff 0))
        = (R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2 := by ring
    rwa [heq] at hadd
  -- The degree bounds force the divided polynomial to vanish.
  have hdeg : ((R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2).natDegree < q := by
    have e1 : ((R i) ^ 2 * f).natDegree ≤ 2 * (R i).natDegree + m := by
      have hp2 : ((R i) ^ 2).natDegree ≤ 2 * (R i).natDegree := natDegree_pow_le
      calc ((R i) ^ 2 * f).natDegree ≤ ((R i) ^ 2).natDegree + f.natDegree := natDegree_mul_le
        _ ≤ 2 * (R i).natDegree + m := by omega
    have e2 : (C (f.coeff 0) * (S i) ^ 2).natDegree ≤ 2 * (S i).natDegree := by
      have hp2 : ((S i) ^ 2).natDegree ≤ 2 * (S i).natDegree := natDegree_pow_le
      calc (C (f.coeff 0) * (S i) ^ 2).natDegree
          ≤ (C (f.coeff 0)).natDegree + ((S i) ^ 2).natDegree := natDegree_mul_le
        _ ≤ 2 * (S i).natDegree := by rw [natDegree_C]; omega
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt e1 (by omega)
    · exact lt_of_le_of_lt e2 (by omega)
  have hPzero : (R i) ^ 2 * f - C (f.coeff 0) * (S i) ^ 2 = 0 := by
    by_contra hne
    have := natDegree_le_of_dvd hP hne
    rw [natDegree_X_pow] at this
    omega
  have hEq : (R i) ^ 2 * f = C (f.coeff 0) * (S i) ^ 2 := sub_eq_zero.mp hPzero
  -- `r_i ≠ 0`, so its image under `φ` is nonzero.
  have hCc : C (f.coeff 0) ≠ 0 := by rw [Ne, C_eq_zero]; exact hf0
  have hRine : R i ≠ 0 := by
    intro hR0
    rw [hR0] at hEq
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at hEq
    rcases mul_eq_zero.mp hEq.symm with h | h
    · exact hCc h
    · exact hi_spec.elim (· hR0) (· (sq_eq_zero_iff.mp h))
  -- Pass to `\overline{F}[X]` and extract the square, contradicting `hns`.
  have hinj : Function.Injective φ := φ.injective
  have hmap : (R i).map φ ^ 2 * f.map φ = C (φ (f.coeff 0)) * (S i).map φ ^ 2 := by
    have := congrArg (Polynomial.map φ) hEq
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C] using this
  have hφc : φ (f.coeff 0) ≠ 0 := by
    rw [Ne, ← map_zero φ]; exact fun h => hf0 (hinj h)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (φ (f.coeff 0)) (n := 2) (by norm_num)
  have hCd : C (φ (f.coeff 0)) = (C d) ^ 2 := by rw [← hd, C_pow]
  have hAB : (R i).map φ ^ 2 * f.map φ = (C d * (S i).map φ) ^ 2 := by
    rw [mul_pow, ← hCd]; exact hmap
  have hA : (R i).map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hRine
  have hdvdA : (R i).map φ ∣ C d * (S i).map φ :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by norm_num)).mp ⟨f.map φ, hAB.symm⟩
  obtain ⟨w, hw⟩ := hdvdA
  have hfsq : f.map φ = w ^ 2 := by
    have hB : (C d * (S i).map φ) ^ 2 = (R i).map φ ^ 2 * w ^ 2 := by rw [hw]; ring
    rw [hB] at hAB
    exact mul_left_cancel₀ (pow_ne_zero 2 hA) hAB
  exact hns ⟨w, hfsq⟩

end Salt.Weil

-- ===== Salt.Weil.StepanovCore =====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, the Stepanov core (W4.1c/d/e)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
equations (17)–(23) and Theorem 7. This module carries the three load-bearing steps of the
Stepanov method for the point count of `y² = f(x)`:

* **W4.1d — the dimension count** (`stepanov_dimension_count`, `finrank_degreeLT`,
  `finrank_pi_degreeLT`): the constraints (22) form a homogeneous linear system whose number
  of variables `2·J·B` (with `B := ⌈(q-m)/2⌉` the degree bound (19)) exceeds the number of
  equations; therefore a nonzero coefficient vector `(r, s)` exists. The engine is
  `LinearMap.ker_ne_bot_of_finrank_lt`, and the dimension arithmetic is `finrank_degreeLT`.

* **W4.1c — the vanishing reduction** (`stepanovAux_hasseDeriv_eval`,
  `stepanovAux_dvd_of_reduced_eval_zero`): for `x ∈ F` (a point of the locus `N_a`) the
  `k`-th Hasse derivative of `h_a := stepanovAux f ℓ r s` evaluated at `x` collapses, via the
  characteristic-`p` identity `(X+Y)^{jq} ≡ X^{jq} (mod Y^q)` and `x^{jq} = x^j`, to the linear
  expression `∑_j (E^k(r_j f^ℓ + s_j f^{ℓ+e}))(x) · x^j =: (Q_k).eval x`. Hence if `Q_k` vanishes
  at `x` for every `k < ℓ`, then `x` is a root of `h_a` of multiplicity `≥ ℓ`
  (`X_sub_C_pow_dvd_iff_hasseDeriv`).

* **W4.1e — the count bound** (`stepanov_multiplicity_card_le`): combining the multiplicity
  `≥ ℓ` at each of the `|N_a|` distinct points with `h_a ≠ 0` and the degree bound gives
  `ℓ · |N_a| ≤ deg h_a`, the Stepanov inequality feeding Theorem 7.
-/

namespace Salt.Weil

open Polynomial Module
open scoped BigOperators

/-! ### W4.1d — the dimension count -/

variable {F : Type*} [Field F]

/-- **The abstract dimension count.** A linear map from a strictly larger space has a
genuinely nonzero vector in its kernel. This is the engine behind Harcos's
"more variables than equations ⇒ a nonzero solution" (Harcos p. 12). -/
theorem exists_nonzero_mem_ker_of_finrank_lt
    {V W : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (φ : V →ₗ[F] W) (h : finrank F W < finrank F V) :
    ∃ v : V, v ≠ 0 ∧ φ v = 0 := by
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt h)
  exact ⟨v, hv_ne, hv_mem⟩

/-- The space of polynomials of degree `< n` has dimension `n` (Harcos (19)). -/
theorem finrank_degreeLT (n : ℕ) : finrank F (degreeLT F n) = n := by
  rw [finrank_eq_card_basis (degreeLT.basis F n), Fintype.card_fin]

/-- Dimension of the coefficient space of `J` polynomials each of degree `< n`. -/
theorem finrank_pi_degreeLT (J n : ℕ) : finrank F (Fin J → degreeLT F n) = J * n := by
  rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    finrank_degreeLT, smul_eq_mul]

/-- **The Stepanov dimension count** (Harcos p. 12). The coefficient space of the ansatz
is `(Fin J → degreeLT F B) × (Fin J → degreeLT F B)`: the `r_j`'s and `s_j`'s, each of degree
`< B` (the bound (19), `B = ⌈(q-m)/2⌉`). The constraints (22) are packaged as a linear map
`φ` into a product of `ℓ` degree-`< D` spaces. Whenever the count `ℓ·D < 2·J·B` holds, a
nonzero coefficient vector `(r, s)` lies in the kernel — a nonzero solution of (22). The
consumer (W4.1e) supplies `φ`, `B`, `D` and the count. -/
theorem stepanov_dimension_count {J ℓ B D : ℕ}
    (φ : ((Fin J → degreeLT F B) × (Fin J → degreeLT F B)) →ₗ[F] (Fin ℓ → degreeLT F D))
    (hcount : ℓ * D < 2 * (J * B)) :
    ∃ v : (Fin J → degreeLT F B) × (Fin J → degreeLT F B), v ≠ 0 ∧ φ v = 0 := by
  refine exists_nonzero_mem_ker_of_finrank_lt φ ?_
  rw [finrank_prod, finrank_pi_degreeLT, finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, finrank_degreeLT, smul_eq_mul]
  omega

/-- The degree-shift atom: multiplying a degree-`< d` polynomial by `X^e` lands it in
degree `< e + d` (the `WithBot`-degree bookkeeping for the constraint map). -/
theorem Xpow_mul_mem_degreeLT (e d : ℕ) (u : F[X]) (hu : u ∈ degreeLT F d) :
    X ^ e * u ∈ degreeLT F (e + d) := by
  rw [mem_degreeLT] at hu ⊢
  refine (degree_mul_le _ _).trans_lt ?_
  rw [degree_X_pow, Nat.cast_add]
  exact WithBot.add_lt_add_of_le_of_lt WithBot.coe_ne_bot le_rfl hu

/-! ### W4.1c — the vanishing reduction (Harcos (17)–(22)) -/

/-- Char-`p` monomial fact: `hasseDeriv b (X^q) = 0` for `0 < b < q`, because `p ∣ (p^n).choose b`
(with `q = p^n = #F`). This seeds the `(X+Y)^{jq} ≡ X^{jq} (mod Y^q)` collapse. -/
theorem hasseDeriv_X_pow_card_eq_zero [Fintype F] {b : ℕ} (hb0 : 0 < b)
    (hbq : b < Fintype.card F) : hasseDeriv b ((X : F[X]) ^ Fintype.card F) = 0 := by
  obtain ⟨p, hp_char, n, hp_prime, hpn⟩ := FiniteField.card' F
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI : CharP F p := hp_char
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one]
  have hdvd : p ∣ (Fintype.card F).choose b := by
    rw [hpn]; exact hp_prime.dvd_choose_pow (by omega) (by omega)
  rw [show ((Fintype.card F).choose b : F) = 0 from (CharP.cast_eq_zero_iff F p _).mpr hdvd,
    monomial_zero_right]

/-- The `(X^q)^j` form of the char-`p` vanishing, by induction on `j` via the Leibniz rule. -/
theorem hasseDeriv_X_card_pow_eq_zero [Fintype F] {b : ℕ} (hb0 : 0 < b)
    (hbq : b < Fintype.card F) (j : ℕ) :
    hasseDeriv b (((X : F[X]) ^ Fintype.card F) ^ j) = 0 := by
  induction j with
  | zero => rw [pow_zero]; exact hasseDeriv_apply_one (k := b) hb0
  | succ j ih =>
    rw [pow_succ', hasseDeriv_mul]
    refine Finset.sum_eq_zero fun cd hcd => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hcd
    rcases Nat.eq_zero_or_pos cd.1 with hc | hc
    · have hd : cd.2 = b := by omega
      rw [hd, ih, mul_zero]
    · rw [hasseDeriv_X_pow_card_eq_zero hc (by omega), zero_mul]

/-- The `X^{jq}` form: `hasseDeriv b (X^{jq}) = 0` for `0 < b < q`. -/
theorem hasseDeriv_X_pow_mul_card_eq_zero [Fintype F] {b : ℕ} (hb0 : 0 < b)
    (hbq : b < Fintype.card F) (j : ℕ) :
    hasseDeriv b ((X : F[X]) ^ (j * Fintype.card F)) = 0 := by
  rw [pow_mul']
  exact hasseDeriv_X_card_pow_eq_zero hb0 hbq j

/-- The block identity `hasseDeriv k (g · X^{jq}) = hasseDeriv k g · X^{jq}` for `k < q`: the
window `X^{jq}` carries no cross terms since its lower Hasse derivatives vanish in char `p`. -/
theorem hasseDeriv_mul_X_pow_block [Fintype F] (g : F[X]) {k : ℕ} (j : ℕ)
    (hk : k < Fintype.card F) :
    hasseDeriv k (g * (X : F[X]) ^ (j * Fintype.card F))
      = hasseDeriv k g * (X : F[X]) ^ (j * Fintype.card F) := by
  have hsingle : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
        hasseDeriv ij.1 g * hasseDeriv ij.2 ((X : F[X]) ^ (j * Fintype.card F))
      = hasseDeriv k g * hasseDeriv 0 ((X : F[X]) ^ (j * Fintype.card F)) := by
    refine Finset.sum_eq_single_of_mem (k, 0) (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero k)) ?_
    rintro ⟨c, d⟩ hcd hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hcd
    have hd2 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · exact absurd (by simp only [Prod.mk.injEq]; omega) hne
      · exact hd0
    dsimp only
    rw [hasseDeriv_X_pow_mul_card_eq_zero hd2 (by omega), mul_zero]
  rw [hasseDeriv_mul, hsingle, hasseDeriv_zero']

/-! ### Harcos Lemma 10 — the `f`-power divisibility -/

/-- **Lemma 10 core** (`g = 1`): `f^(n-k) ∣ hasseDeriv k (f^n)` for `k ≤ n`. Induction on `n` via
the Leibniz rule: the `i = 0` term carries the extra factor `f`, and every `i ≥ 1` term already
has a high enough `f`-power. This is the divisibility that — with the matching degree drop —
sharpens the reduced polynomials from the `(20)` form to the `(21)`/`(22)` degree bound. -/
theorem pow_dvd_hasseDeriv_pow (f : F[X]) (n : ℕ) :
    ∀ k, k ≤ n → f ^ (n - k) ∣ hasseDeriv k (f ^ n) := by
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    simp
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hkn | hkn
    · have hklen : k ≤ n := by omega
      rw [pow_succ', hasseDeriv_mul]
      refine Finset.dvd_sum fun ij hij => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      rcases Nat.eq_zero_or_pos ij.1 with hi0 | hi0
      · have hi2 : ij.2 = k := by omega
        rw [hi0, hi2, hasseDeriv_zero']
        calc f ^ (n + 1 - k) = f * f ^ (n - k) := by rw [← pow_succ']; congr 1; omega
          _ ∣ f * hasseDeriv k (f ^ n) := mul_dvd_mul_left f (ih k hklen)
      · have hi2n : ij.2 ≤ n := by omega
        have hle : n + 1 - k ≤ n - ij.2 := by omega
        exact (pow_dvd_pow f hle).trans ((ih ij.2 hi2n).mul_left _)
    · have hz : n + 1 - k = 0 := by omega
      rw [hz, pow_zero]; exact one_dvd _

/-- **Lemma 10** (general `g`): `f^(ℓ-k) ∣ hasseDeriv k (g · f^ℓ)` for `k ≤ ℓ`. This factors each
`E^k(r_j f^ℓ)` as `r_j^{(k)} · f^{ℓ-k}`, the shape behind Harcos (20). -/
theorem pow_dvd_hasseDeriv_mul_pow (f g : F[X]) (ℓ k : ℕ) (hk : k ≤ ℓ) :
    f ^ (ℓ - k) ∣ hasseDeriv k (g * f ^ ℓ) := by
  rw [hasseDeriv_mul]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  have hle : ℓ - k ≤ ℓ - ij.2 := by omega
  exact (pow_dvd_pow f hle).trans ((pow_dvd_hasseDeriv_pow f ℓ ij.2 (by omega)).mul_left _)

/-- **W4.1c — the reduced polynomial** `Q_k := ∑_j E^k(r_j f^ℓ + s_j f^{ℓ+e}) · X^j` (Harcos
(20)–(22)), `F`-linear in the coefficient data `(r, s)`. Evaluating the `k`-th Hasse derivative of
the ansatz at any point returns `(Q_k).eval x`. -/
noncomputable def reducedPoly [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (k : ℕ) : F[X] :=
  ∑ j : Fin J,
    hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + (Fintype.card F - 1) / 2)) * X ^ (j : ℕ)

theorem reducedPoly_eval [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (x : F) (k : ℕ) :
    (reducedPoly f ℓ r s k).eval x
      = ∑ j : Fin J,
          (hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + (Fintype.card F - 1) / 2))).eval x
            * x ^ (j : ℕ) := by
  unfold reducedPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_pow, eval_X]

/-- **W4.1c — the vanishing reduction** (Harcos (20)–(22)). The `k`-th Hasse derivative of the
ansatz, evaluated at any `x ∈ F`, equals `(Q_k).eval x`: the char-`p` identity
`hasseDeriv b (X^{jq}) = 0` collapses the Leibniz sum to the `X^{jq}` window, and `x^{jq} = x^j`
on the finite field folds the windows onto the reduced polynomial. -/
theorem stepanovAux_hasseDeriv_eval [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ)
    (r s : Fin J → F[X]) (x : F) {k : ℕ} (hk : k < Fintype.card F) :
    (hasseDeriv k (stepanovAux f ℓ r s)).eval x = (reducedPoly f ℓ r s k).eval x := by
  rw [reducedPoly_eval]
  set q := Fintype.card F with hq
  set e := (q - 1) / 2 with he
  have hrw : stepanovAux f ℓ r s
      = ∑ j : Fin J, (r j * f ^ ℓ + s j * f ^ (ℓ + e)) * X ^ ((j : ℕ) * q) := by
    unfold stepanovAux
    rw [← hq, ← he, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  rw [hrw, map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_mul_X_pow_block _ _ hk, eval_mul, eval_pow, eval_X]
  congr 1
  rw [pow_mul]
  exact FiniteField.pow_card _

/-- **W4.1c — the multiplicity certificate** (Harcos (17)). If the reduced polynomial `Q_k`
vanishes *at* `x` for every `k < ℓ` (with `ℓ ≤ q`), then `x` is a root of the ansatz of
multiplicity `≥ ℓ`. At a point of the locus `N_a`, where `f(x)^{(q-1)/2} = a` folds the `(22)`
linear conditions into `Q_k(x) = 0`, this delivers the high-order zeros; note `Q_k(x) = 0` is the
honest per-point condition — the *global* identity `Q_k = 0` collapses to the zero ansatz. -/
theorem stepanovAux_dvd_of_reduced_eval_zero [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ)
    (r s : Fin J → F[X]) (x : F) (hℓq : ℓ ≤ Fintype.card F)
    (hred : ∀ k, k < ℓ → (reducedPoly f ℓ r s k).eval x = 0) :
    (X - C x) ^ ℓ ∣ stepanovAux f ℓ r s := by
  rw [X_sub_C_pow_dvd_iff_hasseDeriv]
  intro k hk
  rw [stepanovAux_hasseDeriv_eval f ℓ r s x (lt_of_lt_of_le hk hℓq)]
  exact hred k hk

/-! ### W4.1e — the count bound -/

/-- **W4.1e — the Stepanov count bound.** If `h ≠ 0` and each element of a finite set `T` of
distinct field elements is a root of `h` of multiplicity `≥ ℓ`, then `ℓ · |T| ≤ deg h`. With
`h = h_a` and `T = N_a` this is Harcos's `ℓ(N₀ + N_a) ≤ deg h_a` feeding Theorem 7. -/
theorem stepanov_multiplicity_card_le {h : F[X]} (hh : h ≠ 0) (ℓ : ℕ) (T : Finset F)
    (hT : ∀ x ∈ T, (X - C x) ^ ℓ ∣ h) : ℓ * T.card ≤ h.natDegree := by
  have hdvd : (∏ x ∈ T, (X - C x) ^ ℓ) ∣ h := by
    refine Finset.prod_dvd_of_coprime ?_ hT
    intro x _ y _ hxy
    exact (pairwise_coprime_X_sub_C Function.injective_id hxy).pow
  have hdeg := natDegree_le_of_dvd hdvd hh
  rw [natDegree_prod _ _ (fun x _ => pow_ne_zero ℓ (monic_X_sub_C x).ne_zero)] at hdeg
  have hterm : ∀ x ∈ T, ((X - C x) ^ ℓ).natDegree = ℓ := by
    intro x _; rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul] at hdeg
  rw [mul_comm ℓ T.card]; exact hdeg

end Salt.Weil

-- ===== Salt.Weil.PointCount =====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, the point count (W5): the tight-degree bridge and Theorem 7

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
equations (12)–(23), Theorem 7 and Remark 4. This module carries the last analytic step of
the Stepanov face: the sharp degree control on the reduced polynomials (Harcos (21)), the
`a`-form of the constraint system (22) on the locus `N_a`, and the Weil–Stepanov point-count
bound (Theorem 7) for `y² = f(x)`.

* **the tight-degree bridge** (`exists_quotient_hasseDeriv_mul_pow`,
  `reducedPoly_dvd`): the degree companion to `pow_dvd_hasseDeriv_mul_pow` (Harcos Lemma 10,
  eq. (16)/(21)). Not only does `f^{ℓ-k}` divide `hasseDeriv k (g·f^ℓ)`; the quotient `g^{(k)}`
  has `natDegree ≤ deg g + k·(m-1)` with `m := deg f`. Consequently `f^{ℓ-k} ∣ reducedPoly` and
  `reducedPoly` has a controlled degree — the degree input (21) to the equation count on p. 12.
-/

namespace Salt.Weil

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-! ### The tight-degree bridge (Harcos Lemma 10, eq. (16)/(21)) -/

/-- **The tight-degree bridge** (Harcos Lemma 10, the degree half, eq. (16)/(21)). Companion to
`pow_dvd_hasseDeriv_mul_pow`: not only does `f^{ℓ-k}` divide `hasseDeriv k (g·f^ℓ)`, but the
quotient `g^{(k)}` has controlled degree. With `f ≠ 0`, `m := deg f ≥ 1` and `k ≤ ℓ`,
`hasseDeriv k (g·f^ℓ) = f^{ℓ-k}·u` for some `u` with `deg u ≤ deg g + k·(m-1)`.

Proof: the divisibility gives `u`; the degree drop `deg (E^k h) ≤ deg h − k`
(`natDegree_hasseDeriv_le`) together with `deg h = (ℓ-k)·m + deg u` (domain factorisation)
pins `deg u` after the `ℕ`-arithmetic identities `(ℓ-k)m + km = ℓm` and `k(m-1) + k = km`. -/
theorem exists_quotient_hasseDeriv_mul_pow (f g : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree)
    (ℓ k : ℕ) (hk : k ≤ ℓ) :
    ∃ u : F[X], hasseDeriv k (g * f ^ ℓ) = f ^ (ℓ - k) * u ∧
      u.natDegree ≤ g.natDegree + k * (f.natDegree - 1) := by
  obtain ⟨u, hu⟩ := pow_dvd_hasseDeriv_mul_pow f g ℓ k hk
  refine ⟨u, hu, ?_⟩
  set m := f.natDegree with hm_def
  set h := hasseDeriv k (g * f ^ ℓ) with hh_def
  -- Numerator degree, keeping the `- k` for tightness.
  have hnd : h.natDegree ≤ (g * f ^ ℓ).natDegree - k := natDegree_hasseDeriv_le _ _
  have hmul : (g * f ^ ℓ).natDegree ≤ g.natDegree + ℓ * m := by
    refine natDegree_mul_le.trans ?_
    gcongr
    exact natDegree_pow_le
  rcases eq_or_ne h 0 with h0 | h0
  · -- `h = 0` forces `u = 0` since `f^{ℓ-k} ≠ 0`.
    have hzero : f ^ (ℓ - k) * u = 0 := by rw [← hu]; exact h0
    have hu0 : u = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hf)
    rw [hu0]; simp
  · -- `h ≠ 0`: factor the degree and finish with `ℕ`-arithmetic.
    have hpow_ne : f ^ (ℓ - k) ≠ 0 := pow_ne_zero _ hf
    have hne : f ^ (ℓ - k) * u ≠ 0 := by rw [← hu]; exact h0
    have hu_ne : u ≠ 0 := right_ne_zero_of_mul hne
    have hfact : h.natDegree = (ℓ - k) * m + u.natDegree := by
      rw [hu, natDegree_mul hpow_ne hu_ne, natDegree_pow]
    have p1 : (ℓ - k) * m + k * m = ℓ * m := by rw [← Nat.add_mul, Nat.sub_add_cancel hk]
    have p2 : k * (m - 1) + k = k * m := by rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- **`f^{ℓ-k}` divides the reduced polynomial** (Harcos (20)). Every summand of `reducedPoly`
is `hasseDeriv k` of `r_j f^ℓ + s_j f^{ℓ+e}`, and both `f^ℓ` and `f^{ℓ+e}` carry a factor `f^ℓ`,
so `f^{ℓ-k}` divides each `hasseDeriv k` term (via `pow_dvd_hasseDeriv_mul_pow`). -/
theorem reducedPoly_dvd [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    {k : ℕ} (hk : k ≤ ℓ) :
    f ^ (ℓ - k) ∣ reducedPoly f ℓ r s k := by
  unfold reducedPoly
  refine Finset.dvd_sum fun j _ => ?_
  refine Dvd.dvd.mul_right ?_ _
  rw [map_add]
  refine dvd_add (pow_dvd_hasseDeriv_mul_pow f (r j) ℓ k hk) ?_
  -- `s_j f^{ℓ+e} = (s_j f^e) f^ℓ`, so the same divisibility applies with `g := s_j f^e`.
  have hrw : s j * f ^ (ℓ + (Fintype.card F - 1) / 2)
      = (s j * f ^ ((Fintype.card F - 1) / 2)) * f ^ ℓ := by rw [pow_add]; ring
  rw [hrw]
  exact pow_dvd_hasseDeriv_mul_pow f (s j * f ^ ((Fintype.card F - 1) / 2)) ℓ k hk

/-! ### The `a`-form of the constraint system (Harcos (22)) and the count bound (13) -/

/-- **`N_0` is automatic** (Harcos (17), the `f(x) = 0` branch). At a root of `f` the reduced
polynomial `Q_k` vanishes for every `k < ℓ`, with no constraint on `(r, s)`: `Q_k = f^{ℓ-k}·P_k`
by `reducedPoly_dvd` and `f(x)^{ℓ-k} = 0` since `ℓ - k ≥ 1`. -/
theorem reducedPoly_eval_eq_zero_of_eval_zero [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ)
    (r s : Fin J → F[X]) {x : F} (hx : f.eval x = 0) {k : ℕ} (hk : k < ℓ) :
    (reducedPoly f ℓ r s k).eval x = 0 := by
  obtain ⟨P, hP⟩ := reducedPoly_dvd f ℓ r s (le_of_lt hk)
  rw [hP, eval_mul, eval_pow, hx, zero_pow (by omega : ℓ - k ≠ 0), zero_mul]

/-- **The `a`-form** (Harcos (20)→(22)). On the locus `N_a = {x : f(x)^{(q-1)/2} = a}`, the reduced
polynomial `Q_k` evaluated at `x` factors as `f(x)^{ℓ-k}` times the value at `x` of the
*`a`-linear combination* `∑_j (r_j^{(k)} + a·s_j^{(k)}) X^j` — the Harcos (22) polynomial. The
quotients `r_j^{(k)}, s_j^{(k)}` come from the tight-degree bridge, so they satisfy the (21)
degree bound `deg ≤ deg r_j + k(m-1)`. Substituting `f(x)^{(q-1)/2} = a` collapses the extra
`f^{(q-1)/2}` on the `s`-block to the constant `a`. -/
theorem reducedPoly_eval_on_Na [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (a : F) {k : ℕ} (hk : k ≤ ℓ) (x : F)
    (hx : (f.eval x) ^ ((Fintype.card F - 1) / 2) = a) :
    ∃ rk sk : Fin J → F[X],
      (∀ j, (rk j).natDegree ≤ (r j).natDegree + k * (f.natDegree - 1)) ∧
      (∀ j, (sk j).natDegree ≤ (s j).natDegree + k * (f.natDegree - 1)) ∧
      (reducedPoly f ℓ r s k).eval x
        = (f.eval x) ^ (ℓ - k) * (∑ j : Fin J, (rk j + C a * sk j) * X ^ (j : ℕ)).eval x := by
  classical
  set e := (Fintype.card F - 1) / 2 with he
  choose rk hrk hrk_deg using fun j =>
    exists_quotient_hasseDeriv_mul_pow f (r j) hf hm ℓ k hk
  choose sk hsk hsk_deg using fun j =>
    exists_quotient_hasseDeriv_mul_pow f (s j) hf hm (ℓ + e) k (by omega)
  refine ⟨rk, sk, hrk_deg, hsk_deg, ?_⟩
  rw [reducedPoly_eval]
  have hRHS : (∑ j : Fin J, (rk j + C a * sk j) * X ^ (j : ℕ)).eval x
      = ∑ j : Fin J, ((rk j).eval x + a * (sk j).eval x) * x ^ (j : ℕ) := by
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [hRHS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpow : (f.eval x) ^ ((ℓ + e) - k) = (f.eval x) ^ (ℓ - k) * a := by
    rw [← hx, ← pow_add]; congr 1; omega
  rw [map_add, eval_add, hrk j, hsk j]
  simp only [eval_mul, eval_pow]
  rw [hpow]; ring

/-- **The Stepanov count bound** (Harcos (13), numerator). If the auxiliary polynomial `h_a` is
nonzero and, at every point of a finite locus `T` where `f(x) ≠ 0`, the reduced polynomials
`Q_k` (`k < ℓ`) vanish — i.e. `(r, s)` solves (22) on `T` — then `ℓ·|T| ≤ deg h_a`. The `f(x)=0`
points of `T` are handled automatically (`reducedPoly_eval_eq_zero_of_eval_zero`); the assembly
is `stepanovAux_dvd_of_reduced_eval_zero` (multiplicity `≥ ℓ` at each point) fed into
`stepanov_multiplicity_card_le`. Combined with `stepanovAux_natDegree_le` this yields (13). -/
theorem stepanov_locus_card_le [Fintype F] {J : ℕ} (f : F[X]) (ℓ : ℕ) (r s : Fin J → F[X])
    (hℓq : ℓ ≤ Fintype.card F) (hne : stepanovAux f ℓ r s ≠ 0) (T : Finset F)
    (hNa : ∀ k, k < ℓ → ∀ x ∈ T, f.eval x ≠ 0 → (reducedPoly f ℓ r s k).eval x = 0) :
    ℓ * T.card ≤ (stepanovAux f ℓ r s).natDegree := by
  refine stepanov_multiplicity_card_le hne ℓ T (fun x hx => ?_)
  refine stepanovAux_dvd_of_reduced_eval_zero f ℓ r s x hℓq (fun k hk => ?_)
  rcases eq_or_ne (f.eval x) 0 with h0 | h0
  · exact reducedPoly_eval_eq_zero_of_eval_zero f ℓ r s h0 hk
  · exact hNa k hk x hx h0

/-! ### The dimension-count arithmetic (Harcos p. 12)

The constraints (22) form a homogeneous linear system in the coefficients of `r_j, s_j`. By (19)
the number of variables is `2·J·⌈(q-m)/2⌉ ≥ J(q-m)`; by (21) the number of equations for fixed
`k` is `≤ (q-m)/2 + k(m-1) + J`, so summing over `0 ≤ k < ℓ` the total is
`< ℓ((q-m)/2 + J) + (ℓ²/2)(m-1)`. A nonzero solution exists once variables exceed equations,
i.e. `J(q-m) ≥ ℓ((q-m)/2 + J) + (ℓ²/2)(m-1)`, equivalently `(J - ℓ/2)(q-m-ℓ) ≥ ℓ²m/2`. Imposing
`ℓ ≤ q/3` and `m < q/6` (the Theorem 7 hypotheses) gives `q-m-ℓ ≥ q/2`, so `J := ⌈ℓ/2 + ℓ²m/q⌉`
suffices; with `ℓ := ⌈√q⌉` the final bound `ℓ(N₀+N_a) ≤ deg h_a` yields `N₀+N_a < q/2 + O_m(√q)`,
which is Harcos (13).

The landed engine `stepanov_dimension_count` uses a *uniform* degree bound `D` on the `ℓ`
constraint blocks, i.e. `D := (q-m)/2 + (ℓ-1)(m-1) + J` (the maximal `D_k`), so it needs
`ℓ·D < 2·J·B`. This is looser than Harcos's exact `∑_k D_k` by a factor ≈ 2 on the `(m-1)`-term,
absorbed by taking `J` slightly above the optimum. A concrete Harcos-shaped instance: -/

/-- Sanity check that the (uniform-`D`) dimension count fires for Harcos-shaped parameters
`q = 100`, `m = 10`, `ℓ = 10 = ⌈√q⌉`, `B = (q-m)/2 = 45`, `J = 16` (the optimum `15` bumped by
one to absorb the uniform bound), `D = (q-m)/2 + (ℓ-1)(m-1) + J = 45 + 81 + 16 = 142`: the count
`ℓ·D = 1420 < 1440 = 2·J·B` holds, so a nonzero coefficient vector exists. -/
example :
    ∃ v : (Fin 16 → degreeLT F 45) × (Fin 16 → degreeLT F 45),
      v ≠ 0 ∧ (0 : ((Fin 16 → degreeLT F 45) × (Fin 16 → degreeLT F 45)) →ₗ[F]
        (Fin 10 → degreeLT F 142)) v = 0 :=
  stepanov_dimension_count 0 (by norm_num)

/-! ### Theorem 7 — the Weil–Stepanov point count for `y² = f(x)` -/

/-- **The point count** `N := #{(x, y) : y² = f(x)}` for the hyperelliptic curve of Theorem 7. -/
noncomputable def pointCount [Fintype F] (f : F[X]) : ℕ :=
  Nat.card {p : F × F // p.2 ^ 2 = f.eval p.1}

/-- **Harcos (12) — the elementary point-count identity.** Fibering over `x` and counting the
solutions of `y² = f(x)` with the quadratic character (`quadraticChar_card_sqrts`: a point `x`
contributes `1 + χ(f(x))`), the point count is `N = q + ∑_x χ(f(x))`. This is `N − q = N₁ − N₋₁`,
the honest elementary route: the character sum is exactly the quantity Stepanov's (13) bounds. -/
theorem pointCount_sub_card [Fintype F] [DecidableEq F] (f : F[X]) (hF : ringChar F ≠ 2) :
    (pointCount f : ℤ) = Fintype.card F + ∑ x : F, quadraticChar F (f.eval x) := by
  have hfib : ∀ x : F, (Nat.card {y : F // y ^ 2 = f.eval x} : ℤ)
      = quadraticChar F (f.eval x) + 1 := by
    intro x
    have hcard : Nat.card {y : F // y ^ 2 = f.eval x}
        = {y : F | y ^ 2 = f.eval x}.toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card']
      exact Nat.card_coe_set_eq _
    rw [hcard]
    exact_mod_cast quadraticChar_card_sqrts hF (f.eval x)
  unfold pointCount
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : F => b ^ 2 = f.eval a)),
    Nat.card_sigma]
  push_cast
  simp_rw [hfib]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

/-- **The Weil–Stepanov combine** (Harcos, end of §5). Given the two Stepanov locus bounds
`N₀ + N₁ ≤ B` and `N₀ + N₋₁ ≤ B` (from `stepanov_locus_card_le` for `a = ±1`), together with
`N₀ + N₁ + N₋₁ = q`, the deviation `N − q = N₁ − N₋₁` of the point count satisfies
`|N₁ − N₋₁| ≤ 2B − q`. With `B < q/2 + O_m(√q)` this is `|N − q| < O_m(√q)` — Theorem 7. Pure
`ℤ`-arithmetic, isolating the counting glue from the (Fable-blocked) `(22)`-solution existence. -/
theorem pointCount_abs_sub_le {N₀ N₁ Nm1 q B : ℤ} (hq : N₀ + N₁ + Nm1 = q)
    (h0 : 0 ≤ N₀) (hb1 : N₀ + N₁ ≤ B) (hbm1 : N₀ + Nm1 ≤ B) :
    |N₁ - Nm1| ≤ 2 * B - q := by
  rw [abs_le]; constructor <;> omega

end Salt.Weil

-- ===== Salt.Weil.StepanovSolve =====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, the φ-bundling and the one-sided Stepanov bound (W5B)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
equations (20)–(23) and Theorem 7. This is the last node before Theorem 7 assembles: it
bundles the Harcos (22) constraint system into a single `F`-linear map `stepanovConstraint`
feeding `stepanov_dimension_count`, produces a nonzero degree-bounded solution `(r, s)` of
(22), and composes the landed pieces (`stepanovAux_ne_zero`, `stepanov_locus_card_le`,
`stepanovAux_natDegree_le`) into the one-sided count bound `ℓ·|T| ≤ deg h_a` on the locus
`N₀ ∪ N_a`.

* **the Hasse-derivative quotient** (`hasseQuot`): the honest linearity route. The map
  `g ↦ hasseDeriv k (g·f^p) / f^{p-k}` is `F`-linear — realised as a bundled `LinearMap`
  via the divisibility `pow_dvd_hasseDeriv_mul_pow` (no conditional-division constructor;
  additivity and homogeneity come from left-cancelling `f^{p-k} ≠ 0`).

* **the constraint map** (`stepanovConstraint`): for each `k < ℓ`, the `a`-form (22)
  polynomial `∑_j (r_j^{(k)} + a·s_j^{(k)}) X^j`, packaged with `LinearMap.pi` +
  `codRestrict` into `Fin ℓ → degreeLT F D`. Its kernel elements solve (22) on `N_a`.

* **the solution** (`stepanov_solution_exists`): `stepanov_dimension_count` applied to
  `stepanovConstraint` at the (Harcos + 1)-bumped parameters yields a nonzero `(r, s)`.

* **the one-sided bound** (`stepanov_one_sided_card_le`): `ℓ·|T| ≤ deg h_a` for any finite
  `T ⊆ N₀ ∪ N_a`, the shape Theorem 7's assembly consumes.
-/

namespace Salt.Weil

open Polynomial Module
open scoped BigOperators

variable {F : Type*} [Field F]

/-! ### Degree ↔ `degreeLT` membership bridges -/

/-- `natDegree p < n` implies `p ∈ degreeLT F n` (handles `p = 0` uniformly). -/
theorem mem_degreeLT_of_natDegree_lt {p : F[X]} {n : ℕ} (h : p.natDegree < n) :
    p ∈ degreeLT F n := by
  rw [mem_degreeLT]
  calc p.degree ≤ (p.natDegree : WithBot ℕ) := degree_le_natDegree
    _ < (n : WithBot ℕ) := by exact_mod_cast h

/-- `p ∈ degreeLT F n` gives `natDegree p ≤ n - 1` (valid for every `n`, including `0`). -/
theorem natDegree_le_sub_one_of_mem_degreeLT {p : F[X]} {n : ℕ}
    (h : p ∈ degreeLT F n) : p.natDegree ≤ n - 1 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [mem_degreeLT, degree_eq_natDegree hp] at h
    have : p.natDegree < n := by exact_mod_cast h
    omega

/-- `p ∈ degreeLT F n` with `1 ≤ n` gives `natDegree p < n`. -/
theorem natDegree_lt_of_mem_degreeLT {p : F[X]} {n : ℕ} (hn : 1 ≤ n)
    (h : p ∈ degreeLT F n) : p.natDegree < n := by
  have := natDegree_le_sub_one_of_mem_degreeLT h; omega

/-! ### The Hasse-derivative quotient as a bundled linear map -/

/-- **The Hasse-derivative quotient** (Harcos (20)/(21)). The map
`g ↦ hasseDeriv k (g·f^p) / f^{p-k}` (the quotient guaranteed by the tight-degree bridge) is
`F`-linear. The underlying function is `Classical.choose` of the divisibility witness; additivity
and homogeneity follow by left-cancelling the nonzero factor `f^{p-k}`. -/
noncomputable def hasseQuot (f : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (p k : ℕ)
    (hk : k ≤ p) : F[X] →ₗ[F] F[X] where
  toFun g := Classical.choose (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)
  map_add' g₁ g₂ := by
    have s1 := (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g₁ hf hm p k hk)).1
    have s2 := (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g₂ hf hm p k hk)).1
    have s12 :=
      (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f (g₁ + g₂) hf hm p k hk)).1
    refine mul_left_cancel₀ (pow_ne_zero (p - k) hf) ?_
    rw [mul_add, ← s1, ← s2, ← s12, add_mul, map_add]
  map_smul' c g := by
    have sg := (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)).1
    have scg :=
      (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f (c • g) hf hm p k hk)).1
    simp only [RingHom.id_apply]
    refine mul_left_cancel₀ (pow_ne_zero (p - k) hf) ?_
    rw [mul_smul_comm, ← sg, ← scg, smul_mul_assoc, map_smul]

/-- Defining relation of `hasseQuot`: `f^{p-k} · (g^{(k)}) = hasseDeriv k (g·f^p)`. -/
theorem hasseQuot_mul (f : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (p k : ℕ)
    (hk : k ≤ p) (g : F[X]) :
    f ^ (p - k) * hasseQuot f hf hm p k hk g = hasseDeriv k (g * f ^ p) :=
  ((Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)).1).symm

/-- The tight-degree bound (Harcos (21)) for `hasseQuot`. -/
theorem hasseQuot_natDegree_le (f : F[X]) (hf : f ≠ 0) (hm : 1 ≤ f.natDegree) (p k : ℕ)
    (hk : k ≤ p) (g : F[X]) :
    (hasseQuot f hf hm p k hk g).natDegree ≤ g.natDegree + k * (f.natDegree - 1) :=
  (Classical.choose_spec (exists_quotient_hasseDeriv_mul_pow f g hf hm p k hk)).2

/-! ### The bundled constraint map (Harcos (22)) -/

/-- **The `a`-form constraint map** (Harcos (22)). For each `k < ℓ` it returns the
`a`-combination `∑_j (r_j^{(k)} + C a · s_j^{(k)}) X^j` of the Hasse-derivative quotients, a
degree-`< D` polynomial (`D := B + (ℓ-1)(m-1) + J`). Bundled as an `F`-linear map into
`Fin ℓ → degreeLT F D` — the exact domain/codomain of `stepanov_dimension_count`. -/
noncomputable def stepanovConstraint [Fintype F] (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F) (ℓ J B : ℕ) :
    ((Fin J → degreeLT F B) × (Fin J → degreeLT F B)) →ₗ[F]
      (Fin ℓ → degreeLT F (B + (ℓ - 1) * (f.natDegree - 1) + J)) :=
  LinearMap.pi fun k =>
    LinearMap.codRestrict _
      (∑ j : Fin J,
        (LinearMap.mulRight F (X ^ (j : ℕ))).comp
          ((hasseQuot f hf hm ℓ (k : ℕ) (le_of_lt k.isLt)).comp
              ((degreeLT F B).subtype.comp ((LinearMap.proj j).comp (LinearMap.fst F _ _)))
            + (LinearMap.mulLeft F (C a)).comp
                ((hasseQuot f hf hm (ℓ + (Fintype.card F - 1) / 2) (k : ℕ)
                    ((le_of_lt k.isLt).trans (Nat.le_add_right ℓ _))).comp
                  ((degreeLT F B).subtype.comp ((LinearMap.proj j).comp (LinearMap.snd F _ _))))))
      (by
        intro v
        rw [LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun j _ => ?_
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
          LinearMap.mulLeft_apply, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply,
          Submodule.coe_subtype]
        apply mem_degreeLT_of_natDegree_lt
        have hj1 := j.isLt
        have hqr := hasseQuot_natDegree_le f hf hm ℓ (k : ℕ) (le_of_lt k.isLt) (v.1 j).val
        have hqs := hasseQuot_natDegree_le f hf hm (ℓ + (Fintype.card F - 1) / 2) (k : ℕ)
          ((le_of_lt k.isLt).trans (Nat.le_add_right ℓ _)) (v.2 j).val
        have hdrB : (v.1 j).val.natDegree ≤ B - 1 :=
          natDegree_le_sub_one_of_mem_degreeLT (v.1 j).2
        have hdsB : (v.2 j).val.natDegree ≤ B - 1 :=
          natDegree_le_sub_one_of_mem_degreeLT (v.2 j).2
        have hk1 := k.isLt
        set m := f.natDegree with hm_def
        have hkm : (k : ℕ) * (m - 1) ≤ (ℓ - 1) * (m - 1) := by gcongr; omega
        refine lt_of_le_of_lt (natDegree_mul_le) ?_
        rw [natDegree_X_pow]
        refine lt_of_le_of_lt
          (Nat.add_le_add_right (?_ : _ ≤ B - 1 + (k : ℕ) * (m - 1)) (j : ℕ)) ?_
        · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
          · exact hqr.trans (by omega)
          · exact (natDegree_C_mul_le _ _).trans (hqs.trans (by omega))
        · omega)

/-- The coefficient form of `stepanovConstraint`: its `k`-th component, coerced to `F[X]`, is the
`a`-combination `∑_j (r_j^{(k)} + C a · s_j^{(k)}) X^j`. -/
theorem stepanovConstraint_apply_coe [Fintype F] {ℓ J B : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F)
    (v : (Fin J → degreeLT F B) × (Fin J → degreeLT F B)) (k : Fin ℓ) :
    ((stepanovConstraint f hf hm a ℓ J B v k : degreeLT F _) : F[X])
      = ∑ j : Fin J, (hasseQuot f hf hm ℓ (k : ℕ) (le_of_lt k.isLt) (v.1 j).val
          + C a * hasseQuot f hf hm (ℓ + (Fintype.card F - 1) / 2) (k : ℕ)
              ((le_of_lt k.isLt).trans (Nat.le_add_right ℓ _)) (v.2 j).val) * X ^ (j : ℕ) := by
  simp only [stepanovConstraint, LinearMap.pi_apply, LinearMap.codRestrict_apply,
    LinearMap.coe_sum, Finset.sum_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.proj_apply, Submodule.coe_subtype]

/-! ### The kernel bridge (Harcos (22) ⇒ the vanishing hypothesis) -/

/-- **The kernel bridge.** If the `a`-form constraint polynomial (the `k`-th component of
`stepanovConstraint`) is the zero polynomial, then the reduced polynomial `Q_k` vanishes at
every point `x` of the locus `N_a` (`f(x)^{(q-1)/2} = a`). This is the per-point specialisation
used to feed `stepanov_locus_card_le`: at such `x`, `Q_k(x) = f(x)^{ℓ-k}·(constraint)(x) = 0`. -/
theorem reducedPoly_eval_zero_of_constraint [Fintype F] {J : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (ℓ : ℕ) (r s : Fin J → F[X]) (a : F) {k : ℕ} (hk : k < ℓ)
    (x : F)
    (hx : (f.eval x) ^ ((Fintype.card F - 1) / 2) = a)
    (hcon : ∑ j : Fin J,
        (hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)
          + C a * hasseQuot f hf hm (ℓ + (Fintype.card F - 1) / 2) k
              ((le_of_lt hk).trans (Nat.le_add_right ℓ _)) (s j)) * X ^ (j : ℕ) = 0) :
    (reducedPoly f ℓ r s k).eval x = 0 := by
  rw [reducedPoly_eval]
  set e := (Fintype.card F - 1) / 2 with he
  have hconx : ∑ j : Fin J,
      ((hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)).eval x
        + a * (hasseQuot f hf hm (ℓ + e) k ((le_of_lt hk).trans (Nat.le_add_right ℓ _))
            (s j)).eval x) * x ^ (j : ℕ) = 0 := by
    have h := congrArg (Polynomial.eval x) hcon
    simpa only [eval_finsetSum, eval_mul, eval_add, eval_C, eval_pow, eval_X, eval_zero] using h
  have key : ∀ j : Fin J,
      (hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + e))).eval x
        = (f.eval x) ^ (ℓ - k) * ((hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)).eval x
            + a * (hasseQuot f hf hm (ℓ + e) k ((le_of_lt hk).trans (Nat.le_add_right ℓ _))
                (s j)).eval x) := by
    intro j
    have hr := hasseQuot_mul f hf hm ℓ k (le_of_lt hk) (r j)
    have hs := hasseQuot_mul f hf hm (ℓ + e) k
      ((le_of_lt hk).trans (Nat.le_add_right ℓ _)) (s j)
    rw [map_add, ← hr, ← hs, eval_add, eval_mul, eval_mul, eval_pow, eval_pow]
    have hpow : (f.eval x) ^ ((ℓ + e) - k) = (f.eval x) ^ (ℓ - k) * a := by
      rw [← hx, ← pow_add]; congr 1; omega
    rw [hpow]; ring
  have hstep : ∑ j : Fin J,
        (hasseDeriv k (r j * f ^ ℓ + s j * f ^ (ℓ + e))).eval x * x ^ (j : ℕ)
      = (f.eval x) ^ (ℓ - k) * ∑ j : Fin J,
          ((hasseQuot f hf hm ℓ k (le_of_lt hk) (r j)).eval x
            + a * (hasseQuot f hf hm (ℓ + e) k ((le_of_lt hk).trans (Nat.le_add_right ℓ _))
                (s j)).eval x) * x ^ (j : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key j]; ring
  rw [hstep, hconx, mul_zero]

/-! ### The nonzero degree-bounded solution of (22) -/

/-- **The Stepanov solution** (Harcos p. 12). At the (Harcos + 1)-bumped parameters — the count
`ℓ·D < 2·J·B` with `D = B + (ℓ-1)(m-1) + J` — there is a nonzero degree-`< B` coefficient
vector `(r, s)` solving the (22) system on `N_a` for every `k < ℓ`: the reduced polynomials
vanish on the locus. Obtained by feeding `stepanovConstraint` to `stepanov_dimension_count`. -/
theorem stepanov_solution_exists [Fintype F] {ℓ J B : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F)
    (hcount : ℓ * (B + (ℓ - 1) * (f.natDegree - 1) + J) < 2 * (J * B)) :
    ∃ r s : Fin J → F[X], (∃ j, r j ≠ 0 ∨ s j ≠ 0)
      ∧ (∀ j, (r j).natDegree ≤ B - 1) ∧ (∀ j, (s j).natDegree ≤ B - 1)
      ∧ ∀ k, k < ℓ → ∀ x : F, (f.eval x) ^ ((Fintype.card F - 1) / 2) = a
          → (reducedPoly f ℓ r s k).eval x = 0 := by
  obtain ⟨v, hv_ne, hv_ker⟩ :=
    stepanov_dimension_count (stepanovConstraint f hf hm a ℓ J B) hcount
  refine ⟨fun j => (v.1 j).val, fun j => (v.2 j).val, ?_, ?_, ?_, ?_⟩
  · by_contra hc
    apply hv_ne
    have hj : ∀ j, (v.1 j).val = 0 ∧ (v.2 j).val = 0 := by
      intro j
      have hnj := not_exists.mp hc j
      rw [not_or, not_ne_iff, not_ne_iff] at hnj
      exact hnj
    have h1 : v.1 = 0 := funext fun j => Subtype.ext (by simpa using (hj j).1)
    have h2 : v.2 = 0 := funext fun j => Subtype.ext (by simpa using (hj j).2)
    exact Prod.ext h1 h2
  · intro j; exact natDegree_le_sub_one_of_mem_degreeLT (v.1 j).2
  · intro j; exact natDegree_le_sub_one_of_mem_degreeLT (v.2 j).2
  · intro k hk x hx
    refine reducedPoly_eval_zero_of_constraint f hf hm ℓ _ _ a hk x hx ?_
    have hc : ((stepanovConstraint f hf hm a ℓ J B v ⟨k, hk⟩ : degreeLT F _) : F[X]) = 0 := by
      have hz := congrFun hv_ker ⟨k, hk⟩
      rw [hz]; simp
    rw [stepanovConstraint_apply_coe] at hc
    exact hc

/-! ### The one-sided Stepanov count bound (Harcos (13)) -/

/-- **The one-sided bound** (Harcos (13), the numerator half). For `q` odd, `f` a non-square with
`f(0) ≠ 0` and `deg f = m ≥ 1`, and parameters satisfying the (Harcos + 1) dimension count, any
finite locus `T ⊆ N₀ ∪ N_a` (each point either a root of `f` or on `f(x)^{(q-1)/2} = a`) obeys
`ℓ·|T| ≤ deg h_a`, with the explicit degree bound of `stepanovAux_natDegree_le` on the right.
This is the shape Theorem 7's assembly consumes for `a = ±1` (with `2·bound/ℓ − q < O_m(√q)`). -/
theorem stepanov_one_sided_card_le [Fintype F] {ℓ J B : ℕ} (f : F[X]) (hf : f ≠ 0)
    (hm : 1 ≤ f.natDegree) (a : F) (hB1 : 1 ≤ B) (hℓq : ℓ ≤ Fintype.card F)
    (hqodd : Odd (Fintype.card F)) (hf0 : f.coeff 0 ≠ 0)
    (hB : B ≤ (Fintype.card F - f.natDegree) / 2)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hcount : ℓ * (B + (ℓ - 1) * (f.natDegree - 1) + J) < 2 * (J * B))
    (T : Finset F)
    (hT : ∀ x ∈ T, f.eval x = 0 ∨ (f.eval x) ^ ((Fintype.card F - 1) / 2) = a) :
    ℓ * T.card ≤ ℓ * f.natDegree
        + (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F) := by
  obtain ⟨r, s, hnz, hrd, hsd, hvanish⟩ := stepanov_solution_exists f hf hm a hcount
  have hne : stepanovAux f ℓ r s ≠ 0 :=
    stepanovAux_ne_zero f ℓ r s hqodd hf0
      (fun j => lt_of_le_of_lt (hrd j) (by omega)) (fun j => lt_of_le_of_lt (hsd j) (by omega))
      hns hnz
  have hcard : ℓ * T.card ≤ (stepanovAux f ℓ r s).natDegree := by
    refine stepanov_locus_card_le f ℓ r s hℓq hne T (fun k hk x hxT hfx => ?_)
    rcases hT x hxT with h0 | ha
    · exact absurd h0 hfx
    · exact hvanish k hk x ha
  exact hcard.trans
    (stepanovAux_natDegree_le f ℓ r s (fun j => (hrd j).trans (Nat.sub_le B 1))
      (fun j => (hsd j).trans (Nat.sub_le B 1)))

end Salt.Weil

-- ===== Salt.Weil.WeilStepanov =====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, Theorem 7 assembly: the Weil–Stepanov point-count bound (W-T7)

Blueprint: `docs/exploration/pilot.md` (the W-R0 gold ladder), following Harcos §5,
Theorem 7. This is the summit of the Stepanov face. It composes the one-sided Stepanov
count bound (`stepanov_one_sided_card_le`) for the two loci `N₀ ∪ N₁` and `N₀ ∪ N₋₁`
(characters `a = ±1`) with the elementary point-count identity `pointCount = q + ∑ χ(f)`
(`pointCount_sub_card`) and the counting glue (`pointCount_abs_sub_le`) to obtain the
`O_m(√q)` deviation bound
`|pointCount f − q| ≤ 8·(deg f)·(⌊√q⌋ + 1)` for `y² = f(x)`.

Parameter choice (Harcos, uniform-`D` variant): `ℓ := ⌊√q⌋ + 1`, `B := (q − m)/2`,
`J := ℓ/2 + 2m + 1`. Under `q ≥ 16 m²` the dimension count (`hcount`) fires and the
rounded division by `ℓ` collapses to the stated `√q`-shape. The constant `8` is not
load-bearing: the descent (Cor 3) consumes any explicit `C·m·√q`.

* `hcount_arith` / `final_arith`: the two `ℤ`-arithmetic facts (dimension count and the
  post-division bound) isolated from the counting glue.
* `weil_stepanov`: Theorem 7 itself.
-/

namespace Salt.Weil

open Polynomial Finset
open scoped BigOperators

variable {F : Type*} [Field F]

/-- **The dimension-count inequality** (Harcos p. 12) at the chosen parameters, over `ℤ`.
With `ℓ = s + 1`, `s = ⌊√q⌋` (`s·s ≤ q`), `4m ≤ s` (from `16m² ≤ q`), `B ≈ (q−m)/2`
(`q ≤ 2B + m + 1`) and `J ≈ ℓ/2 + 2m` (`2J` two-sided), the count `ℓ·D < 2·J·B` holds. -/
theorem hcount_arith {s m q B J : ℤ}
    (hs0 : 0 ≤ s) (hm : 1 ≤ m) (hB0 : 0 ≤ B)
    (hsq : s * s ≤ q) (h4m : 4 * m ≤ s) (hBhi : q ≤ 2 * B + m + 1)
    (hJlo : (s + 1) + 4 * m + 1 ≤ 2 * J) (hJhi : 2 * J ≤ (s + 1) + 4 * m + 2) :
    (s + 1) * (B + s * (m - 1) + J) < 2 * (J * B) := by
  have hm0 : (0:ℤ) ≤ m := by linarith
  have hm1 : (0:ℤ) ≤ m - 1 := by linarith
  have h4ms : (0:ℤ) ≤ s - 4 * m := by linarith
  have hJk : (0:ℤ) ≤ 2 * J - (s + 1) - 4 * m - 1 := by linarith
  nlinarith [mul_nonneg h4ms hm0, mul_nonneg h4ms hs0, mul_nonneg h4ms hm1,
    mul_nonneg hB0 hJk, mul_nonneg hs0 hm1, mul_nonneg hs0 hm0,
    mul_nonneg hs0 hs0, mul_nonneg hB0 hm1, mul_nonneg hB0 hm0,
    mul_nonneg (by linarith : (0:ℤ) ≤ q - s * s) hm0, mul_nonneg hm1 hs0]

/-- **The post-division bound** (Harcos (13) → Theorem 7), over `ℤ`. Twice the one-sided
degree bound `R = ℓm + B + em + (J−1)q` is `≤ ℓq + 8mℓ²`, so `2⌊R/ℓ⌋ − q ≤ 8mℓ`. Uses
`q < ℓ²`, `2B + m ≤ q`, `2e + 1 = q` (q odd) and `2(J−1) ≤ ℓ + 4m`. -/
theorem final_arith {m q lu B J e : ℤ}
    (hm : 1 ≤ m) (hl : 1 ≤ lu) (he0 : 0 ≤ e) (hJ1 : 1 ≤ J)
    (hqu : q < lu * lu) (hBlo : 2 * B + m ≤ q) (he : 2 * e + 1 = q)
    (hJhi : 2 * (J - 1) ≤ lu + 4 * m) :
    2 * (lu * m + B + e * m + (J - 1) * q) ≤ lu * q + 8 * m * (lu * lu) := by
  have hm0 : (0:ℤ) ≤ m := by linarith
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ lu * lu - q) hm0,
    mul_nonneg (by linarith : (0:ℤ) ≤ lu - 1) hm0,
    mul_le_mul_of_nonneg_left hBlo (by linarith : (0:ℤ) ≤ lu),
    mul_nonneg he0 hm0]

/-! ### Theorem 7 — the Weil–Stepanov point count for `y² = f(x)` -/

/-- **Theorem 7 (Weil–Stepanov).** For `q = #F` odd, `f` a non-square (in the algebraic
closure) with `f(0) ≠ 0`, `deg f ≥ 1` and `q ≥ 16·(deg f)²`, the hyperelliptic point count
`N = #{(x, y) : y² = f(x)}` deviates from `q` by `O_m(√q)`:
`|N − q| ≤ 8·(deg f)·(⌊√q⌋ + 1)`. Assembled from the two one-sided Stepanov bounds
(`stepanov_one_sided_card_le` at `a = ±1`), the fibre identity `N = q + ∑ₓ χ(f(x))`
(`pointCount_sub_card`) and the counting glue (`pointCount_abs_sub_le`). -/
theorem weil_stepanov [Fintype F] (f : F[X])
    (hqodd : Odd (Fintype.card F)) (hm : 1 ≤ f.natDegree) (hf0 : f.coeff 0 ≠ 0)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hq : 16 * f.natDegree ^ 2 ≤ Fintype.card F) :
    |(pointCount f : ℤ) - Fintype.card F|
      ≤ 8 * f.natDegree * (Nat.sqrt (Fintype.card F) + 1) := by
  classical
  have hF : ringChar F ≠ 2 := by
    intro h; have := FiniteField.even_card_of_char_two h
    rcases hqodd with ⟨k, hk⟩; omega
  have hf : f ≠ 0 := fun h => hf0 (by rw [h, coeff_zero])
  have hqm : Fintype.card F % 2 = 1 := Nat.odd_iff.mp hqodd
  set s := Nat.sqrt (Fintype.card F) with hs_def
  set ℓ := s + 1 with hℓ_def
  set e := (Fintype.card F - 1) / 2 with he_def
  set B := (Fintype.card F - f.natDegree) / 2 with hB_def
  set J := ℓ / 2 + 2 * f.natDegree + 1 with hJ_def
  set R := ℓ * f.natDegree + (B + e * f.natDegree + (J - 1) * Fintype.card F) with hR_def
  set Bp := R / ℓ with hBp_def
  -- parameter facts (ℕ)
  have hmq : f.natDegree + 2 ≤ Fintype.card F := by nlinarith [hq, hm]
  have hsq : s * s ≤ Fintype.card F := by rw [hs_def]; exact Nat.sqrt_le _
  have h4m : 4 * f.natDegree ≤ s := by
    rw [hs_def]; exact Nat.le_sqrt.mpr (by nlinarith [hq])
  have hℓq : ℓ ≤ Fintype.card F := by
    rw [hℓ_def, hs_def]
    have := Nat.sqrt_lt_self (show 1 < Fintype.card F by omega); omega
  have hqlt : Fintype.card F < ℓ * ℓ := by
    rw [hℓ_def, hs_def]; exact Nat.lt_succ_sqrt _
  have hℓpos : 0 < ℓ := by omega
  have hB1 : 1 ≤ B := by rw [hB_def]; omega
  have hB : B ≤ (Fintype.card F - f.natDegree) / 2 := hB_def.le
  have hBhi : Fintype.card F ≤ 2 * B + f.natDegree + 1 := by rw [hB_def]; omega
  have hBlo : 2 * B + f.natDegree ≤ Fintype.card F := by rw [hB_def]; omega
  have hJlo : s + 1 + 4 * f.natDegree + 1 ≤ 2 * J := by rw [hJ_def, hℓ_def]; omega
  have hJhi : 2 * J ≤ s + 1 + 4 * f.natDegree + 2 := by rw [hJ_def, hℓ_def]; omega
  have hJ1 : 1 ≤ J := by rw [hJ_def]; omega
  -- the dimension count (ℕ)
  have hcount : ℓ * (B + (ℓ - 1) * (f.natDegree - 1) + J) < 2 * (J * B) := by
    rw [hℓ_def, Nat.add_sub_cancel]
    zify [hm]
    exact hcount_arith (s := (s:ℤ)) (m := (f.natDegree:ℤ)) (q := (Fintype.card F:ℤ))
      (B := (B:ℤ)) (J := (J:ℤ)) (by positivity) (by exact_mod_cast hm) (by positivity)
      (by exact_mod_cast hsq) (by exact_mod_cast h4m) (by exact_mod_cast hBhi)
      (by exact_mod_cast hJlo) (by exact_mod_cast hJhi)
  -- the character sum and the partition
  have hsum : ∑ x : F, quadraticChar F (f.eval x)
      = ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card : ℤ)
        - (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card := by
    rw [← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by
      rcases quadraticChar_isQuadratic F (f.eval x) with h | h | h <;> simp [h])
  have hpart : ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card : ℤ)
        + (univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card
        + (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card
        = Fintype.card F := by
    have hone : (Fintype.card F : ℤ) = ∑ _x : F, (1:ℤ) := by simp [Finset.card_univ]
    rw [hone, ← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_boole,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by
      rcases quadraticChar_isQuadratic F (f.eval x) with h | h | h <;> simp [h])
  -- the two one-sided bounds
  have onesided : ∀ (a : F) (c : ℤ), (c = 1 ∨ c = -1) → ((c : F) = a) →
      (univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card
        + (univ.filter (fun x : F => quadraticChar F (f.eval x) = c)).card ≤ Bp := by
    intro a c hc hca
    have hdisj : Disjoint (univ.filter (fun x : F => quadraticChar F (f.eval x) = 0))
        (univ.filter (fun x : F => quadraticChar F (f.eval x) = c)) := by
      rw [Finset.disjoint_left]; intro x hx0 hxc
      have h0 := (Finset.mem_filter.mp hx0).2
      have hcc := (Finset.mem_filter.mp hxc).2
      rw [h0] at hcc
      rcases hc with h | h <;> · rw [h] at hcc; exact absurd hcc (by norm_num)
    have hT : ∀ x ∈ (univ.filter (fun x : F => quadraticChar F (f.eval x) = 0))
          ∪ (univ.filter (fun x : F => quadraticChar F (f.eval x) = c)),
        f.eval x = 0 ∨ (f.eval x) ^ ((Fintype.card F - 1) / 2) = a := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx0 | hxc
      · exact Or.inl (quadraticChar_eq_zero_iff.mp (Finset.mem_filter.mp hx0).2)
      · right
        have hcx : quadraticChar F (f.eval x) = c := (Finset.mem_filter.mp hxc).2
        have hpow := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
        rw [hcx] at hpow
        rw [show (Fintype.card F - 1) / 2 = Fintype.card F / 2 from by omega, ← hpow, hca]
    have hstep : ℓ * ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0))
          ∪ (univ.filter (fun x : F => quadraticChar F (f.eval x) = c))).card ≤ R :=
      stepanov_one_sided_card_le (ℓ := ℓ) (J := J) (B := B) f hf hm a hB1 hℓq hqodd hf0 hB
        hns hcount _ hT
    rw [Finset.card_union_of_disjoint hdisj] at hstep
    rw [hBp_def]
    exact (Nat.le_div_iff_mul_le hℓpos).mpr (by rw [Nat.mul_comm]; exact hstep)
  have hb1 := onesided (1:F) (1:ℤ) (Or.inl rfl) (by norm_num)
  have hbm := onesided (-1:F) (-1:ℤ) (Or.inr rfl) (by norm_num)
  -- the point-count deviation
  have hpc : (pointCount f : ℤ) - Fintype.card F
      = ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card : ℤ)
        - (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card := by
    rw [pointCount_sub_card f hF, hsum]; ring
  -- discharge `2·⌊R/ℓ⌋ − q ≤ 8·m·ℓ`
  -- make the nested `set` parameters opaque so the final `nlinarith` does not
  -- unfold them (avoids a `whnf` heartbeat blow-up).
  clear_value Bp R J B e ℓ s
  have hℓs : (ℓ : ℤ) = (s : ℤ) + 1 := by rw [hℓ_def]; push_cast; ring
  have hdiv : (Bp : ℤ) * ℓ ≤ R := by rw [hBp_def]; exact_mod_cast Nat.div_mul_le_self R ℓ
  have h2R : 2 * (R : ℤ) ≤ (ℓ:ℤ) * (Fintype.card F : ℤ)
      + 8 * (f.natDegree : ℤ) * ((ℓ:ℤ) * ℓ) := by
    have hfin := final_arith (m := (f.natDegree:ℤ)) (q := (Fintype.card F:ℤ)) (lu := (ℓ:ℤ))
      (B := (B:ℤ)) (J := (J:ℤ)) (e := (e:ℤ))
      (by exact_mod_cast hm) (by exact_mod_cast (show 1 ≤ ℓ from by omega)) (by positivity)
      (by exact_mod_cast hJ1) (by exact_mod_cast hqlt) (by exact_mod_cast hBlo)
      (by exact_mod_cast (show 2 * e + 1 = Fintype.card F from by rw [he_def]; omega))
      (by exact_mod_cast (show 2 * (J - 1) ≤ ℓ + 4 * f.natDegree from by
        rw [hJ_def, hℓ_def]; omega))
    rw [hR_def]; push_cast [Nat.cast_sub hJ1]; nlinarith [hfin]
  have hfinal : 2 * (Bp:ℤ) - (Fintype.card F : ℤ) ≤ 8 * (f.natDegree : ℤ) * ℓ := by
    refine le_of_mul_le_mul_left ?_ (show (0:ℤ) < ℓ by exact_mod_cast hℓpos)
    have e1 : (ℓ:ℤ) * (2 * (Bp:ℤ) - (Fintype.card F : ℤ))
        = 2 * ((Bp:ℤ) * ℓ) - (ℓ:ℤ) * (Fintype.card F : ℤ) := by ring
    have e2 : (ℓ:ℤ) * (8 * (f.natDegree : ℤ) * ℓ)
        = 8 * (f.natDegree : ℤ) * ((ℓ:ℤ) * ℓ) := by ring
    rw [e1, e2]; linarith [hdiv, h2R]
  rw [hℓs] at hfinal
  have hb1' : ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card : ℤ)
      + (univ.filter (fun x : F => quadraticChar F (f.eval x) = 1)).card ≤ (Bp : ℤ) := by
    exact_mod_cast hb1
  have hbm' : ((univ.filter (fun x : F => quadraticChar F (f.eval x) = 0)).card : ℤ)
      + (univ.filter (fun x : F => quadraticChar F (f.eval x) = -1)).card ≤ (Bp : ℤ) := by
    exact_mod_cast hbm
  have habs := pointCount_abs_sub_le (B := (Bp:ℤ)) hpart (Int.natCast_nonneg _) hb1' hbm'
  rw [hpc]
  exact le_trans habs hfinal

end Salt.Weil




open Polynomial in
theorem solution {F : Type*} [Field F] [Fintype F] (f : Polynomial F)
    (hqodd : Odd (Fintype.card F)) (hm : 1 ≤ f.natDegree) (hf0 : f.coeff 0 ≠ 0)
    (hns : ¬ ∃ g : (AlgebraicClosure F)[X],
      f.map (algebraMap F (AlgebraicClosure F)) = g ^ 2)
    (hq : 16 * f.natDegree ^ 2 ≤ Fintype.card F) :
    |(Nat.card {p : F × F // p.2 ^ 2 = f.eval p.1} : ℤ) - Fintype.card F|
      ≤ 8 * f.natDegree * (Nat.sqrt (Fintype.card F) + 1) :=
  Salt.Weil.weil_stepanov f hqodd hm hf0 hns hq

