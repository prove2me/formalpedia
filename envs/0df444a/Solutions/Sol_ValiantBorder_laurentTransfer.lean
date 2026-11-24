-- Prove2me | solution 1 for ValiantBorder.laurentTransfer
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:00:04.371113+00:00
-- url     : https://prove2.me/submissions/9e87e7a1-04f8-47ef-b55a-d33ddbc8ce7d

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
SPDX-License-Identifier: Apache-2.0

Adapted from Claude (Anthropic), VP ≠ VNP over every field, Appendix N, Lemma N.2.
Sources at https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp
include Nc/Rate/Truncate.lean, Nc/Rate/Transfer.lean, and Paper/Transfer.lean.
The adapter below supplies local circuit definitions and coefficient transport
so the solution imports only the published mission definition.
-/
import Definitions.Def_VP_VNP_all_fields

namespace LaurentTransferProof

open MvPolynomial

def IsStep {R X : Type*} [CommSemiring R] (l : ℕ → MvPolynomial X R) (k : ℕ) : Prop :=
  (∃ v : X, l k = MvPolynomial.X v) ∨ (∃ a : R, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

def Computes {R X : Type*} [CommSemiring R] (f : MvPolynomial X R) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial X R, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = f

theorem Computes.map {R S X : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {f : MvPolynomial X R} {s : ℕ} (h : Computes f s) :
    Computes (MvPolynomial.map φ f) s := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  refine ⟨fun i => MvPolynomial.map φ (l i), ?_, k, hk, rfl⟩
  intro j hj
  rcases hl j hj with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨i, hi, t, ht, he⟩ | ⟨i, hi, t, ht, he⟩
  · exact Or.inl ⟨v, by simp [hv]⟩
  · exact Or.inr (Or.inl ⟨φ a, by simp [ha]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, by simp [he]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, by simp [he]⟩))

def Approximates {R X : Type*} [Field R] (f : MvPolynomial X R) (s : ℕ) : Prop :=
  ∃ q : MvPolynomial X (LaurentSeries R), Computes q s ∧
    ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d q).coeff i = if i = 0 then coeff d f else 0


open MvPolynomial

section Steps

variable {A R X : Type*} [CommSemiring A] [CommSemiring R]

/-- A circuit with t gates is extended by one gate g, which is a variable, a constant, or the sum or product of two of
the t gates. -/
theorem isStep_update {L : ℕ → MvPolynomial X A} {t : ℕ} (h : ∀ k < t, IsStep L k) {g : MvPolynomial X A}
    (hg : (∃ i : X, g = MvPolynomial.X i) ∨ (∃ a : A, g = C a) ∨ (∃ i < t, ∃ j < t, g = L i + L j) ∨
      (∃ i < t, ∃ j < t, g = L i * L j)) :
    ∀ k < t + 1, IsStep (Function.update L t g) k := by
  have e : ∀ i < t, Function.update L t g i = L i := fun i hi => Function.update_of_ne (by omega) _ _
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · rcases h k hk with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by rw [e k hk, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by rw [e k hk, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [e k hk, e i (by omega), e j (by omega), h1]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [e k hk, e i (by omega), e j (by omega), h1]⟩))
  · rcases hg with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
    · exact Or.inl ⟨i, by rw [Function.update_self, h1]⟩
    · exact Or.inr (Or.inl ⟨c, by rw [Function.update_self, h1]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, by rw [Function.update_self, e i hi, e j hj, h1]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, by rw [Function.update_self, e i hi, e j hj, h1]⟩))

/-- A circuit over R all of whose constants are images of elements of A under a homomorphism φ is the image under φ,
gate by gate, of a circuit over A. -/
theorem exists_lift_steps (φ : A →+* R) {l : ℕ → MvPolynomial X R} {s : ℕ} (hl : ∀ k < s, IsStep l k)
    (hc : ∀ k < s, ∀ c, l k = C c → c ∈ Set.range φ) :
    ∃ L : ℕ → MvPolynomial X A, (∀ k < s, IsStep L k) ∧ ∀ k < s, map φ (L k) = l k := by
  induction s with
  | zero => exact ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    obtain ⟨L, hL, hm⟩ := ih (fun k hk => hl k (by omega)) (fun k hk => hc k (by omega))
    have key : ∃ g : MvPolynomial X A, ((∃ i : X, g = MvPolynomial.X i) ∨ (∃ a : A, g = C a) ∨
        (∃ i < t, ∃ j < t, g = L i + L j) ∨ (∃ i < t, ∃ j < t, g = L i * L j)) ∧ map φ g = l t := by
      rcases hl t (by omega) with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
      · exact ⟨MvPolynomial.X i, Or.inl ⟨i, rfl⟩, by rw [h1, map_X]⟩
      · obtain ⟨a, rfl⟩ := hc t (by omega) c h1
        exact ⟨C a, Or.inr (Or.inl ⟨a, rfl⟩), by rw [h1, map_C]⟩
      · exact ⟨L i + L j, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)), by rw [h1, map_add, hm i hi, hm j hj]⟩
      · exact ⟨L i * L j, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩)), by rw [h1, map_mul, hm i hi, hm j hj]⟩
    obtain ⟨g, hg, hgm⟩ := key
    refine ⟨Function.update L t g, isStep_update hL hg, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega), hm k hk]
    · rw [Function.update_self, hgm]

end Steps

section Series

variable {F : Type*} [CommRing F]

/-- A Laurent polynomial in ε, read as a Laurent series in ε. -/
noncomputable def laurentToSeries (F : Type*) [CommRing F] : LaurentPolynomial F →+* LaurentSeries F :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C
    { toFun := fun n => HahnSeries.single n.toAdd 1
      map_one' := rfl
      map_mul' := fun a b => by rw [HahnSeries.single_mul_single, toAdd_mul, one_mul] }
    fun _ _ => Commute.all _ _

/-- The series of a Laurent polynomial has the same coefficients. -/
@[simp] theorem coeff_laurentToSeries (x : LaurentPolynomial F) (i : ℤ) :
    (laurentToSeries F x).coeff i = x.coeff i := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    classical
    rw [laurentToSeries, AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
    change a * (HahnSeries.single n (1 : F)).coeff i = _
    rw [HahnSeries.coeff_single]
    by_cases h : i = n
    · simp [h]
    · simp [h, Ne.symm h]

/-- Every Laurent series agrees below any given power ε ^ n with a Laurent polynomial. -/
theorem exists_laurentPolynomial_coeff (c : LaurentSeries F) (n : ℤ) :
    ∃ c' : LaurentPolynomial F, ∀ i < n, c'.coeff i = c.coeff i := by
  refine ⟨.ofCoeff (Finsupp.onFinset (Finset.Ico c.order n) (fun i => if i < n then c.coeff i else 0) ?_), ?_⟩
  · intro i hi
    by_cases h : i < n
    · rw [if_pos h] at hi
      refine Finset.mem_Ico.2 ⟨?_, h⟩
      by_contra h'
      exact hi (HahnSeries.coeff_eq_zero_of_lt_order (not_le.1 h'))
    · exact absurd (if_neg h) hi
  · intro i hi
    simp [hi]

end Series

section Order

variable {F : Type*} [CommRing F] {X : Type*}

/-- All coefficients of the polynomial u are Laurent series without terms below ε ^ n. -/
def OrdGe (n : ℤ) (u : MvPolynomial X (LaurentSeries F)) : Prop :=
  ∀ (d : X →₀ ℕ) (i : ℤ), i < n → (coeff d u).coeff i = 0

theorem OrdGe.mono {m n : ℤ} {u : MvPolynomial X (LaurentSeries F)} (h : OrdGe n u) (hmn : m ≤ n) : OrdGe m u :=
  fun d i hi => h d i (by omega)

theorem OrdGe.zero (n : ℤ) : OrdGe n (0 : MvPolynomial X (LaurentSeries F)) := fun d i _ => by simp

theorem OrdGe.add {n : ℤ} {u v : MvPolynomial X (LaurentSeries F)} (hu : OrdGe n u) (hv : OrdGe n v) :
    OrdGe n (u + v) := fun d i hi => by rw [coeff_add, HahnSeries.coeff_add, hu d i hi, hv d i hi, add_zero]

/-- The product of a series without terms below ε ^ m and one without terms below ε ^ n has none below ε ^ (m + n). -/
theorem coeff_mul_eq_zero {m n : ℤ} {x y : LaurentSeries F} (hx : ∀ i < m, x.coeff i = 0)
    (hy : ∀ i < n, y.coeff i = 0) {i : ℤ} (hi : i < m + n) : (x * y).coeff i = 0 := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have h := (Finset.mem_antidiagonal.1 hij).2.2
  by_cases h1 : ij.1 < m
  · rw [hx _ h1, zero_mul]
  · rw [hy ij.2 (by omega), mul_zero]

theorem OrdGe.mul {m n : ℤ} {u v : MvPolynomial X (LaurentSeries F)} (hu : OrdGe m u) (hv : OrdGe n v) :
    OrdGe (m + n) (u * v) := fun d i hi => by
  classical
  rw [coeff_mul, HahnSeries.coeff_sum]
  exact Finset.sum_eq_zero fun x _ => coeff_mul_eq_zero (hu x.1) (hv x.2) hi

/-- The poles of the coefficients of finitely many polynomials over the Laurent series have bounded order. -/
theorem exists_ordGe (l : ℕ → MvPolynomial X (LaurentSeries F)) (s : ℕ) :
    ∃ B : ℤ, 0 ≤ B ∧ ∀ k < s, OrdGe (-B) (l k) := by
  have one : ∀ u : MvPolynomial X (LaurentSeries F), ∃ B : ℤ, 0 ≤ B ∧ OrdGe (-B) u := by
    intro u
    induction u using MvPolynomial.induction_on' with
    | monomial e a =>
      refine ⟨|a.order|, abs_nonneg _, fun d i hi => ?_⟩
      classical
      rw [coeff_monomial]
      split_ifs
      · exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi (neg_abs_le _))
      · rfl
    | add p q hp hq =>
      obtain ⟨B, hB, h⟩ := hp
      obtain ⟨B', hB', h'⟩ := hq
      exact ⟨B + B', by omega, (h.mono (by omega)).add (h'.mono (by omega))⟩
  induction s with
  | zero => exact ⟨0, le_rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    obtain ⟨B, hB, h⟩ := ih
    obtain ⟨B', hB', h'⟩ := one (l t)
    refine ⟨B + B', by omega, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact (h k hk).mono (by omega)
    · exact h'.mono (by omega)

end Order

section Truncate

variable {F : Type*} [CommRing F] {X : Type*}

/-- If every constant of a circuit over the Laurent series is cut off
at a sufficiently high power of ε, every gate changes only by terms from ε ^ n on: for every circuit over the Laurent
series and every n there is a circuit of the same shape over the Laurent polynomials whose gates differ from the given
ones by polynomials all of whose coefficients have no terms below ε ^ n. -/
theorem exists_truncated_steps {l : ℕ → MvPolynomial X (LaurentSeries F)} {s : ℕ} (hl : ∀ k < s, IsStep l k) (n : ℤ) :
    ∃ L : ℕ → MvPolynomial X (LaurentPolynomial F), (∀ k < s, IsStep L k) ∧
      ∀ k < s, ∃ r, OrdGe n r ∧ map (laurentToSeries F) (L k) = l k + r := by
  obtain ⟨B, hB, hlB⟩ := exists_ordGe l s
  suffices H : ∀ t ≤ s, ∀ n : ℤ, 0 ≤ n → ∃ L : ℕ → MvPolynomial X (LaurentPolynomial F), (∀ k < t, IsStep L k) ∧
      ∀ k < t, ∃ r, OrdGe n r ∧ map (laurentToSeries F) (L k) = l k + r by
    obtain ⟨L, hL, h⟩ := H s le_rfl |n| (abs_nonneg n)
    exact ⟨L, hL, fun k hk => let ⟨r, hr, e⟩ := h k hk; ⟨r, hr.mono (le_abs_self n), e⟩⟩
  intro t
  induction t with
  | zero =>
    exact fun _ _ _ => ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero k), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ t ih =>
    intro ht n hn
    obtain ⟨L, hL, hr⟩ := ih (by omega) (n + B) (by omega)
    have key : ∃ g : MvPolynomial X (LaurentPolynomial F), ((∃ i : X, g = MvPolynomial.X i) ∨ (∃ a, g = C a) ∨
        (∃ i < t, ∃ j < t, g = L i + L j) ∨ (∃ i < t, ∃ j < t, g = L i * L j)) ∧
        ∃ r, OrdGe n r ∧ map (laurentToSeries F) g = l t + r := by
      rcases hl t (by omega) with ⟨i, h1⟩ | ⟨c, h1⟩ | ⟨i, hi, j, hj, h1⟩ | ⟨i, hi, j, hj, h1⟩
      · exact ⟨MvPolynomial.X i, Or.inl ⟨i, rfl⟩, 0, OrdGe.zero n, by rw [h1, map_X, add_zero]⟩
      · obtain ⟨c', hc'⟩ := exists_laurentPolynomial_coeff c n
        refine ⟨C c', Or.inr (Or.inl ⟨c', rfl⟩), C (laurentToSeries F c' - c), fun d i hi => ?_, ?_⟩
        · classical
          rw [coeff_C]
          split_ifs
          · rw [HahnSeries.coeff_sub, coeff_laurentToSeries, hc' i hi, sub_self]
          · rfl
        · rw [h1, map_C, ← C_add, add_sub_cancel]
      · obtain ⟨ri, hri, ei⟩ := hr i hi
        obtain ⟨rj, hrj, ej⟩ := hr j hj
        exact ⟨L i + L j, Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, rfl⟩)), ri + rj,
          (hri.add hrj).mono (by omega), by rw [h1, map_add, ei, ej]; ring⟩
      · obtain ⟨ri, hri, ei⟩ := hr i hi
        obtain ⟨rj, hrj, ej⟩ := hr j hj
        refine ⟨L i * L j, Or.inr (Or.inr (Or.inr ⟨i, hi, j, hj, rfl⟩)), ri * l j + l i * rj + ri * rj,
          ((?_ : OrdGe n _).add ?_).add ?_, by rw [h1, map_mul, ei, ej]; ring⟩
        · exact (hri.mul (hlB j (by omega))).mono (by omega)
        · exact ((hlB i (by omega)).mul hrj).mono (by omega)
        · exact (hri.mul hrj).mono (by omega)
    obtain ⟨g, hg, hgr⟩ := key
    refine ⟨Function.update L t g, isStep_update hL hg, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      obtain ⟨r, h, e⟩ := hr k hk
      exact ⟨r, h.mono (by omega), e⟩
    · rw [Function.update_self]
      exact hgr

end Truncate

section Approx

variable {F X : Type*} [Field F] {s : ℕ}

/-- A polynomial f that is approximated by a circuit with s gates is approximated
by one whose constants are Laurent polynomials in ε: this circuit computes a polynomial p over the Laurent polynomials
in which no negative power of ε occurs and in which the terms without ε are those of f. -/
theorem Approximates.exists_laurentPolynomial {f : MvPolynomial X F} (h : Approximates f s) :
    ∃ p : MvPolynomial X (LaurentPolynomial F), Computes p s ∧
      ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0 := by
  obtain ⟨_, ⟨l, hl, k, hk, rfl⟩, hp⟩ := h
  obtain ⟨L, hL, hr⟩ := exists_truncated_steps hl 1
  obtain ⟨r, hr, e⟩ := hr k hk
  refine ⟨L k, ⟨L, hL, k, hk, rfl⟩, fun d i hi => ?_⟩
  rw [← hp d i hi, ← coeff_laurentToSeries, ← coeff_map, e, coeff_add, HahnSeries.coeff_add, hr d i (by omega), add_zero]

end Approx


open MvPolynomial
open scoped TensorProduct

section Rings

/-- Two fields of the same characteristic have homomorphisms to a common nonzero ring, namely their tensor product over
the prime field. -/
theorem exists_common_ring.{w} (F : Type w) (KK : Type) [Field F] [Field KK] (p : ℕ) [CharP F p] [CharP KK p] :
    ∃ (T : Type w) (_ : CommRing T) (_ : Nontrivial T), Nonempty (F →+* T) ∧ Nonempty (KK →+* T) := by
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    let : Algebra (ZMod p) F := ZMod.algebra F p
    let : Algebra (ZMod p) KK := ZMod.algebra KK p
    exact ⟨F ⊗[ZMod p] KK, inferInstance, inferInstance,
      ⟨(Algebra.TensorProduct.includeLeft : F →ₐ[ZMod p] F ⊗[ZMod p] KK).toRingHom⟩,
      ⟨(Algebra.TensorProduct.includeRight : KK →ₐ[ZMod p] F ⊗[ZMod p] KK).toRingHom⟩⟩
  · have : CharZero F := CharP.charP_to_charZero F
    have : CharZero KK := CharP.charP_to_charZero KK
    exact ⟨F ⊗[ℚ] KK, inferInstance, inferInstance,
      ⟨(Algebra.TensorProduct.includeLeft : F →ₐ[ℚ] F ⊗[ℚ] KK).toRingHom⟩,
      ⟨(Algebra.TensorProduct.includeRight : KK →ₐ[ℚ] F ⊗[ℚ] KK).toRingHom⟩⟩

/-- Zariski's lemma, in the form of Hilbert's Nullstellensatz: finitely many elements of a nonzero ring T that contains
an image of the algebraically closed field KK lie in a subring of T that has a homomorphism to KK. -/
theorem exists_specialisation {KK T : Type*} [Field KK] [IsAlgClosed KK] [CommRing T] [Nontrivial T] (g : KK →+* T)
    (S : Finset T) : ∃ A : Subring T, (S : Set T) ⊆ A ∧ Nonempty (A →+* KK) := by
  let φ : MvPolynomial S KK →+* T := eval₂Hom g Subtype.val
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (RingHom.ker φ) (RingHom.ker_ne_top φ)
  obtain ⟨x, rfl⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  have hx : ∀ a ∈ RingHom.ker φ, (aeval x : MvPolynomial S KK →ₐ[KK] KK).toRingHom a = 0 := fun a ha =>
    mem_vanishingIdeal_iff.1 (hle ha) x rfl
  refine ⟨φ.range, fun a ha => ⟨X ⟨a, ha⟩, by simp [φ]⟩, ⟨?_⟩⟩
  exact (Ideal.Quotient.lift (RingHom.ker φ) _ hx).comp (RingHom.quotientKerEquivRange φ).symm.toRingHom

/-- A Laurent polynomial over T with all coefficients in the subring A comes from a Laurent polynomial over A. -/
theorem mem_range_mapRingHom_subtype {T : Type*} [CommRing T] (A : Subring T) (c : LaurentPolynomial T)
    (h : ∀ i, c.coeff i ∈ A) : c ∈ Set.range (AddMonoidAlgebra.mapRingHom ℤ A.subtype) := by
  refine ⟨.ofCoeff (Finsupp.onFinset c.coeff.support (fun i => ⟨c.coeff i, h i⟩) fun i hi => ?_), ?_⟩
  · exact Finsupp.mem_support_iff.2 fun h0 => hi (Subtype.ext h0)
  · ext i
    simp

end Rings


variable {F : Type*} {KK : Type} [Field F] [Field KK] [IsAlgClosed KK] {X : Type*}
/-- **Paper: Lemma lem:transfer-approx.** "An approximating circuit for a polynomial with integer coefficients, over a
field of characteristic p, gives one of the same size with constants in KK[ε,ε⁻¹] and output in f + εKK[ε][x]": the
constants are cut off, and the argument of Lemma lem:transfer is applied to their coefficients. -/
theorem lem_transfer_approx (p : ℕ) [CharP F p] [CharP KK p] (q : MvPolynomial X ℤ) {s : ℕ}
    (h : Approximates (MvPolynomial.map (Int.castRingHom F) q) s) :
    ∃ P : MvPolynomial X (LaurentPolynomial KK), Computes P s ∧
      ∀ d : X →₀ ℕ, (∀ i : ℤ, i < 0 → (coeff d P).coeff i = 0) ∧
        (coeff d P).coeff 0 = coeff d (MvPolynomial.map (Int.castRingHom KK) q) := by
  suffices main : ∃ P : MvPolynomial X (LaurentPolynomial KK), Computes P s ∧ ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 →
      (coeff d P).coeff i = if i = 0 then coeff d (MvPolynomial.map (Int.castRingHom KK) q) else 0 by
    obtain ⟨P, hP, hc⟩ := main
    exact ⟨P, hP, fun d => ⟨fun i hi => by rw [hc d i hi.le, if_neg hi.ne], by rw [hc d 0 le_rfl, if_pos rfl]⟩⟩
  obtain ⟨T, _, _, ⟨f⟩, ⟨g⟩⟩ := exists_common_ring F KK p
  obtain ⟨P₀, hP₀, hc₀⟩ := h.exists_laurentPolynomial
  obtain ⟨l, hl, k, hk, e⟩ := Computes.map (AddMonoidAlgebra.mapRingHom ℤ f) hP₀
  classical
  obtain ⟨A, hA, ⟨ψ⟩⟩ := exists_specialisation g
    ((Finset.range s).biUnion fun k => (coeff 0 (l k)).coeff.support.image fun i => (coeff 0 (l k)).coeff i)
  obtain ⟨L, hL, hm⟩ := exists_lift_steps (AddMonoidAlgebra.mapRingHom ℤ A.subtype) hl fun k hk c hc => by
    refine mem_range_mapRingHom_subtype A c fun i => ?_
    by_cases hi : c.coeff i = 0
    · rw [hi]
      exact A.zero_mem
    · refine hA (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, Finset.mem_image.2 ⟨i, ?_, ?_⟩⟩))
      · rw [hc, coeff_zero_C]
        exact Finsupp.mem_support_iff.2 hi
      · rw [hc, coeff_zero_C]
  refine ⟨map (AddMonoidAlgebra.mapRingHom ℤ ψ) (L k), Computes.map _ ⟨L, hL, k, hk, rfl⟩, fun d i hi => ?_⟩
  have e1 : (coeff d (L k)).coeff i = if i = 0 then ((coeff d q : ℤ) : A) else 0 := by
    apply A.subtype_injective
    rw [← AddMonoidAlgebra.coeff_mapRingHom, ← coeff_map, hm k hk, e, coeff_map, AddMonoidAlgebra.coeff_mapRingHom,
      hc₀ d i hi, coeff_map]
    split_ifs <;> simp
  rw [coeff_map, AddMonoidAlgebra.coeff_mapRingHom, e1, coeff_map]
  split_ifs <;> simp

end LaurentTransferProof

theorem solution.{u} {F : Type u} {K V : Type}
    [Field F] [Field K] [IsAlgClosed K] (p : ℕ) [CharP F p] [CharP K p]
    (f : MvPolynomial V ℤ) {s : ℕ}
    (h : Statement.Approximates (MvPolynomial.map (Int.castRingHom F) f) s) :
    ∃ q : MvPolynomial V (LaurentPolynomial K), Statement.Computes q s ∧
      ∀ d : V →₀ ℕ, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d q).coeff i = 0) ∧
        (MvPolynomial.coeff d q).coeff 0 =
          MvPolynomial.coeff d (MvPolynomial.map (Int.castRingHom K) f) := by
  exact LaurentTransferProof.lem_transfer_approx p f h
