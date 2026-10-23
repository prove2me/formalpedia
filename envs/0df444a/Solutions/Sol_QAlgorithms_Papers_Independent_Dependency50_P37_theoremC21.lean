-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.theoremC21
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:01:07.670873+00:00
-- url     : https://prove2.me/submissions/9963d23a-929b-4c0b-b49f-f943db51f045

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

open scoped BigOperators Matrix ComplexOrder ComplexConjugate
open Filter Topology

namespace X7Q10G

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P37
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Information100.P62

variable {d : ℕ}

lemma X7_gen_mem {Φ : Dynamics d} {m : ℕ} {E : Fin m → Matrix (Fin d) (Fin d) ℂ}
    (hE : IsKrausFamily E) (hΦ : ∀ ρ, Φ ρ = krausApply E ρ) (a b : Fin m) :
    (E a)ᴴ * E b ∈ graph Φ :=
  Submodule.subset_span ⟨m, E, hE, hΦ, a, b, rfl⟩

lemma X7_one_mem {Φ : Dynamics d} {m : ℕ} {E : Fin m → Matrix (Fin d) (Fin d) ℂ}
    (hE : IsKrausFamily E) (hΦ : ∀ ρ, Φ ρ = krausApply E ρ) : (1 : Operator d) ∈ graph Φ := by
  rw [← hE]
  exact Submodule.sum_mem _ fun a _ => X7_gen_mem hE hΦ a a

lemma X7_inner_act (v w : EuclideanSpace ℂ (Fin d)) (X : Operator d) :
    inner ℂ v (act X w) = ∑ p, star (v p) * (X *ᵥ (WithLp.ofLp w)) p := by
  simp [act, PiLp.inner_apply, mul_comm]

lemma X7_inner_single (X : Operator d) (i j : Fin d) :
    inner ℂ (EuclideanSpace.single i (1 : ℂ)) (act X (EuclideanSpace.single j 1)) = X i j := by
  rw [X7_inner_act]
  simp [Matrix.mulVec_single]

lemma X7_kraus_entry {m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (a b i j : Fin d) :
    krausApply E (Matrix.single a b 1) i j = ∑ k, E k i a * star (E k j b) := by
  simp only [krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma X7_kraus_vecMulVec {m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (y x : Fin d → ℂ) (q p : Fin d) :
    krausApply E (Matrix.vecMulVec y (star x)) q p = ∑ a, (E a *ᵥ y) q * star ((E a *ᵥ x) p) := by
  simp only [krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
    dotProduct, Pi.star_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

lemma X7_reorder {α β : Type} [Fintype α] [Fintype β] (T : β → β → α → α → ℂ) :
    ∑ q, ∑ p, ∑ a, ∑ b, T a b p q = ∑ a, ∑ b, ∑ p, ∑ q, T a b p q := by
  calc _ = ∑ q, ∑ a, ∑ p, ∑ b, T a b p q := Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ a, ∑ q, ∑ p, ∑ b, T a b p q := Finset.sum_comm
    _ = ∑ a, ∑ q, ∑ b, ∑ p, T a b p q :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ q, ∑ p, T a b p q := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ p, ∑ q, T a b p q :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- the pairing identity -/
lemma X7_pairing {m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (x y z u : Fin d → ℂ) :
    ∑ q, ∑ p, krausApply E (Matrix.vecMulVec y (star x)) q p *
        krausApply E (Matrix.vecMulVec z (star u)) p q =
      ∑ a, ∑ b, (∑ p, star ((E a *ᵥ x) p) * (E b *ᵥ z) p) *
        (∑ q, star ((E b *ᵥ u) q) * (E a *ᵥ y) q) := by
  let T : Fin m → Fin m → Fin d → Fin d → ℂ := fun a b p q =>
    star ((E a *ᵥ x) p) * (E b *ᵥ z) p * (star ((E b *ᵥ u) q) * (E a *ᵥ y) q)
  have h1 : ∑ q, ∑ p, krausApply E (Matrix.vecMulVec y (star x)) q p *
      krausApply E (Matrix.vecMulVec z (star u)) p q = ∑ q, ∑ p, ∑ a, ∑ b, T a b p q := by
    simp only [X7_kraus_vecMulVec, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp only [T]; ring
  have h2 : ∑ a, ∑ b, (∑ p, star ((E a *ᵥ x) p) * (E b *ᵥ z) p) *
      (∑ q, star ((E b *ᵥ u) q) * (E a *ᵥ y) q) = ∑ a, ∑ b, ∑ p, ∑ q, T a b p q := by
    simp only [Finset.sum_mul_sum]
    rfl
  rw [h1, h2, X7_reorder]

lemma X7_alpha_le_one (S : Submodule ℂ (Operator d))
    (h : ∀ v w : EuclideanSpace ℂ (Fin d), IsState v → IsState w →
      (∀ X ∈ S, inner ℂ v (act X w) = 0) → False) : alpha S ≤ 1 := by
  unfold alpha
  apply csSup_le'
  rintro m ⟨v, hv, horth⟩
  by_contra hm
  push Not at hm
  exact h (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) (hv _) (hv _)
    (horth _ _ (by simp [Fin.ext_iff]))

lemma X7_cap_zero {Φ : Dynamics d} (h : alpha (graph Φ) ≤ 1) : classicalCapacity Φ = 0 := by
  unfold classicalCapacity logTwo
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

lemma X7_act_one (w : EuclideanSpace ℂ (Fin d)) : act (1 : Operator d) w = w := by
  simp [act]

lemma X7_alpha_ge_two (S : Submodule ℂ (Operator d)) (hone : (1 : Operator d) ∈ S) {i j : Fin d}
    (hij : i ≠ j) (h : ∀ X ∈ S, X i j = 0 ∧ X j i = 0) : 2 ≤ alpha S := by
  unfold alpha
  apply le_csSup
  · refine ⟨d, fun m ⟨v, hv, horth⟩ => ?_⟩
    have hon : Orthonormal ℂ v := ⟨fun i => hv i, fun a b hab => by
      have := horth a b hab 1 hone
      rwa [X7_act_one] at this⟩
    have := hon.linearIndependent.fintype_card_le_finrank
    simpa using this
  · refine ⟨![EuclideanSpace.single i 1, EuclideanSpace.single j 1], fun a => ?_, fun a b hab X hX => ?_⟩
    · fin_cases a <;> simp [IsState]
    · fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one]
        rw [X7_inner_single]; exact (h X hX).1
      · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one]
        rw [X7_inner_single]; exact (h X hX).2
      · exact absurd rfl hab

lemma X7_cap_ne_zero {Φ : Dynamics d} (h : 2 ≤ alpha (graph Φ)) : classicalCapacity Φ ≠ 0 := by
  unfold classicalCapacity logTwo
  have h2 : (1 : ℝ) < (alpha (graph Φ) : ℝ) := by exact_mod_cast (by omega : 1 < alpha (graph Φ))
  exact div_ne_zero (Real.log_pos h2).ne' (Real.log_pos one_lt_two).ne'

lemma X7_inner_kraus (v w : EuclideanSpace ℂ (Fin d)) (P Q : Operator d) :
    inner ℂ v (act (Pᴴ * Q) w) = ∑ p, star ((P *ᵥ (WithLp.ofLp v)) p) * (Q *ᵥ (WithLp.ofLp w)) p := by
  rw [X7_inner_act]
  have : ∑ p, star ((P *ᵥ (WithLp.ofLp v)) p) * (Q *ᵥ (WithLp.ofLp w)) p =
      star (P *ᵥ (WithLp.ofLp v)) ⬝ᵥ (Q *ᵥ (WithLp.ofLp w)) := rfl
  rw [this, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rfl

theorem X7_cap_iff (Φ : Dynamics d) (A : Operator d) (hA : ColumnStochastic A) (hch : IsChannel Φ)
    (hdiagS : ∀ i p, Φ (Matrix.single i i 1) p p = A p i)
    (hpair : ∀ k l, k ≠ l → ∀ v w : Fin d → ℂ,
      ∑ q, ∑ p, Φ (Matrix.vecMulVec (Pi.single k 1) (star v)) q p *
        Φ (Matrix.vecMulVec w (star (Pi.single l 1))) p q = (∑ q, A q k * A q l) * star (v k) * w l) :
    classicalCapacity Φ = 0 ↔ MatrixScrambling A := by
  obtain ⟨m, E, hE, hΦE⟩ := hch
  have hAre : ∀ p i, (A p i).re = ∑ c, ‖E c p i‖ ^ 2 := by
    intro p i
    rw [← hdiagS, hΦE, X7_kraus_entry, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj']; norm_cast
  constructor
  · intro hcap
    by_contra hns
    unfold MatrixScrambling at hns
    push Not at hns
    obtain ⟨i, j, hij0⟩ := hns
    have hzero : ∀ k, (A k i).re * (A k j).re = 0 := fun k =>
      le_antisymm (hij0 k) (mul_nonneg (hA.1 k i).2 (hA.1 k j).2)
    have hij : i ≠ j := by
      intro h; subst h
      have hsum : ∑ k, (A k i).re = 1 := by
        rw [← Complex.re_sum, hA.2 i]; simp
      have : ∀ k, (A k i).re = 0 := fun k => by
        have := hzero k; rcases mul_self_eq_zero.1 this with h; exact h
      simp [this] at hsum
    -- vanishing of Kraus entries
    have hvan : ∀ (r : ℕ) (F : Fin r → Matrix (Fin d) (Fin d) ℂ), (∀ R, Φ R = krausApply F R) →
        ∀ (a b : Fin r) (s t : Fin d), (A · s) = (A · s) → (∀ k, (A k s).re * (A k t).re = 0) →
          ((F a)ᴴ * F b) s t = 0 := by
      intro r F hF a b s t _ hst
      have hFre : ∀ p u, (A p u).re = ∑ c, ‖F c p u‖ ^ 2 := by
        intro p u
        rw [← hdiagS, hF, X7_kraus_entry, Complex.re_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.star_def, Complex.mul_conj']; norm_cast
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun p _ => ?_
      rcases mul_eq_zero.1 (hst p) with h | h
      · rw [hFre] at h
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg ‖F c p s‖)).1 h a
          (Finset.mem_univ _)
        have h0 : F a p s = 0 := by simpa using this
        simp [Matrix.conjTranspose_apply, h0]
      · rw [hFre] at h
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg ‖F c p t‖)).1 h b
          (Finset.mem_univ _)
        have h0 : F b p t = 0 := by simpa using this
        simp [h0]
    have hgraph : ∀ X ∈ graph Φ, X i j = 0 ∧ X j i = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨r, F, -, hF, a, b, rfl⟩ := hx
        exact ⟨hvan r F hF a b i j rfl hzero,
          hvan r F hF a b j i rfl fun k => by rw [mul_comm]; exact hzero k⟩
      | zero => simp
      | add x y _ _ hx hy => simp [hx.1, hx.2, hy.1, hy.2]
      | smul c x _ hx => simp [hx.1, hx.2]
    exact X7_cap_ne_zero (X7_alpha_ge_two _ (X7_one_mem hE hΦE) hij hgraph) hcap
  · intro hscr
    apply X7_cap_zero
    apply X7_alpha_le_one
    intro v w hv hw horth
    have hab : ∀ a b, ∑ p, star ((E a *ᵥ (WithLp.ofLp v)) p) * (E b *ᵥ (WithLp.ofLp w)) p = 0 :=
      fun a b => by rw [← X7_inner_kraus]; exact horth _ (X7_gen_mem hE hΦE a b)
    have hvw : ∑ p, star (v p) * w p = 0 := by
      have := horth 1 (X7_one_mem hE hΦE)
      rw [X7_inner_act] at this; simpa using this
    have hkl : ∀ k l, k ≠ l → star (v k) * w l = 0 := by
      intro k l hkl
      have h1 := hpair k l hkl (WithLp.ofLp v) (WithLp.ofLp w)
      simp only [hΦE] at h1
      rw [X7_pairing] at h1
      simp only [hab, zero_mul, Finset.sum_const_zero] at h1
      have hpos : (∑ q, A q k * A q l).re ≠ 0 := by
        rw [Complex.re_sum]
        obtain ⟨q0, hq0⟩ := hscr k l
        have : ∀ q, (A q k * A q l).re = (A q k).re * (A q l).re := fun q => by
          simp [Complex.mul_re, (hA.1 q k).1, (hA.1 q l).1]
        simp only [this]
        refine (lt_of_lt_of_le hq0 (Finset.single_le_sum (f := fun q => (A q k).re * (A q l).re)
          (fun q _ => mul_nonneg (hA.1 q k).2 (hA.1 q l).2) (Finset.mem_univ q0))).ne'
      have hne : (∑ q, A q k * A q l) ≠ 0 := fun h => hpos (by rw [h]; simp)
      have := h1.symm
      rw [mul_assoc] at this
      exact (mul_eq_zero.1 this).resolve_left hne
    have hv0 : ∃ k, v k ≠ 0 := by
      by_contra h; push Not at h
      have : v = 0 := by ext i; simp [h i]
      rw [IsState, this] at hv; simp at hv
    obtain ⟨k, hk⟩ := hv0
    have hwl : ∀ l, l ≠ k → w l = 0 := fun l hl => by
      have := hkl k l (Ne.symm hl)
      exact (mul_eq_zero.1 this).resolve_left (by simpa using hk)
    have hwk : w k ≠ 0 := by
      intro h0
      have : w = 0 := by
        ext l; by_cases hl : l = k
        · subst hl; simp [h0]
        · simp [hwl l hl]
      rw [IsState, this] at hw; simp at hw
    have hvl : ∀ l, l ≠ k → v l = 0 := fun l hl => by
      have := hkl l k hl
      have h2 := (mul_eq_zero.1 this).resolve_right hwk
      simpa using h2
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hvl l hl]; simp) (by simp)] at hvw
    exact (mul_ne_zero (by simpa using hk) hwk) hvw

lemma X7_cduc_pair (A B : Operator d) (k l : Fin d) (hkl : k ≠ l) (v w : Fin d → ℂ) :
    ∑ q, ∑ p, cduc A B (Matrix.vecMulVec (Pi.single k 1) (star v)) q p *
      cduc A B (Matrix.vecMulVec w (star (Pi.single l 1))) p q =
        (∑ q, A q k * A q l) * star (v k) * w l := by
  have hX : ∀ q p, cduc A B (Matrix.vecMulVec (Pi.single k 1) (star v)) q p *
      cduc A B (Matrix.vecMulVec w (star (Pi.single l 1))) p q =
        if q = p then A q k * A q l * star (v k) * w l else 0 := by
    intro q p
    by_cases hqp : q = p
    · subst hqp
      simp [cduc, Matrix.vecMulVec_apply, Pi.single_apply]
      ring
    · rw [if_neg hqp]
      simp only [cduc, if_neg hqp, if_neg (Ne.symm hqp), Matrix.vecMulVec_apply, Pi.single_apply,
        Pi.star_apply]
      by_cases hq : q = k
      · subst hq; simp [hkl]
      · simp [hq]
  simp_rw [hX]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]

lemma X7_duc_pair (A C : Operator d) (k l : Fin d) (hkl : k ≠ l) (v w : Fin d → ℂ) :
    ∑ q, ∑ p, duc A C (Matrix.vecMulVec (Pi.single k 1) (star v)) q p *
      duc A C (Matrix.vecMulVec w (star (Pi.single l 1))) p q =
        (∑ q, A q k * A q l) * star (v k) * w l := by
  have hX : ∀ q p, duc A C (Matrix.vecMulVec (Pi.single k 1) (star v)) q p *
      duc A C (Matrix.vecMulVec w (star (Pi.single l 1))) p q =
        if q = p then A q k * A q l * star (v k) * w l else 0 := by
    intro q p
    by_cases hqp : q = p
    · subst hqp
      simp [duc, Matrix.vecMulVec_apply, Pi.single_apply]
      ring
    · rw [if_neg hqp]
      simp only [duc, if_neg hqp, if_neg (Ne.symm hqp), Matrix.vecMulVec_apply, Pi.single_apply,
        Pi.star_apply]
      by_cases hp : p = k
      · subst hp; simp [hkl]
      · simp [hp]
  simp_rw [hX]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul]

end X7Q10G

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)
open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)
open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P37 X7Q10G in
theorem solution {d : ℕ} (hd : 0 < d) (A : Operator d)
    (hA : ColumnStochastic A) :
    (∀ B : Operator d, IsChannel (cduc A B) → (classicalCapacity (cduc A B) = 0 ↔ MatrixScrambling A)) ∧
    (∀ C : Operator d, IsChannel (duc A C) → (classicalCapacity (duc A C) = 0 ↔ MatrixScrambling A)) := by
  constructor
  · intro B hch
    exact X7_cap_iff (cduc A B) A hA hch (fun i p => by simp [cduc, Matrix.single_apply])
      (fun k l hkl v w => X7_cduc_pair A B k l hkl v w)
  · intro C hch
    exact X7_cap_iff (duc A C) A hA hch (fun i p => by simp [duc, Matrix.single_apply])
      (fun k l hkl v w => X7_duc_pair A C k l hkl v w)
