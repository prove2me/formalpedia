-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P19.compressionPure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:25:55.049662+00:00
-- url     : https://prove2.me/submissions/1578de6b-d275-4c82-82ee-9c92d26b3754

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

lemma g55d_norm_one {Y : Type*} [Fintype Y] (ψ : EuclideanSpace ℂ Y) (h : ‖ψ‖ = 1) :
    ∑ y, ψ y * conj (ψ y) = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  have : ∀ y, ψ y * conj (ψ y) = ((‖ψ y‖ ^ 2 : ℝ) : ℂ) := by
    intro y; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this]
  exact_mod_cast h

lemma g55d_factor {R X : Type*} [Fintype R] [Fintype X] (φ : EuclideanSpace ℂ (R × X))
    (hφ : ‖φ‖ = 1) (v : EuclideanSpace ℂ X) (hv : ‖v‖ = 1)
    (h : traceLeft (pureDensity φ) = pureDensity v) :
    (∀ r x, φ (r, x) = (∑ y, conj (v y) * φ (r, y)) * v x) ∧
      ∑ r, (∑ y, conj (v y) * φ (r, y)) * conj (∑ y, conj (v y) * φ (r, y)) = 1 := by
  set c : R → ℂ := fun r => ∑ y, conj (v y) * φ (r, y) with hcdef
  have hρ : ∀ x y, ∑ r, φ (r, x) * conj (φ (r, y)) = v x * conj (v y) := by
    intro x y
    have := congrFun (congrFun h x) y
    simpa [traceLeft, pureDensity] using this
  have hvn := g55d_norm_one v hv
  have hφn : ∑ r, ∑ x, φ (r, x) * conj (φ (r, x)) = 1 := by
    rw [← Fintype.sum_prod_type']; exact g55d_norm_one φ hφ
  have hc : ∑ r, c r * conj (c r) = 1 := by
    have e1 : ∑ r, c r * conj (c r) =
        ∑ y, ∑ x, (conj (v x) * v y) * ∑ r, φ (r, x) * conj (φ (r, y)) := by
      simp only [hcdef, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [e1]
    simp only [hρ]
    calc ∑ y, ∑ x, conj (v x) * v y * (v x * conj (v y))
        = (∑ y, v y * conj (v y)) * (∑ x, v x * conj (v x)) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = 1 := by rw [hvn]; ring
  refine ⟨?_, hc⟩
  set d : R → X → ℂ := fun r x => φ (r, x) - c r * v x with hd
  have hsum : ∑ r, ∑ x, d r x * conj (d r x) = 0 := by
    have h1 : ∀ r, ∑ x, φ (r, x) * conj (v x) = c r := by
      intro r; simp only [hcdef]; exact Finset.sum_congr rfl fun x _ => by ring
    have h2 : ∀ r, ∑ x, v x * conj (φ (r, x)) = conj (c r) := by
      intro r; simp only [hcdef, map_sum, map_mul, Complex.conj_conj]
    have : ∀ r, ∑ x, d r x * conj (d r x) =
        ∑ x, φ (r, x) * conj (φ (r, x)) - conj (c r) * (∑ x, φ (r, x) * conj (v x))
          - c r * (∑ x, v x * conj (φ (r, x)))
          + c r * conj (c r) * ∑ x, v x * conj (v x) := by
      intro r
      simp only [hd, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_sub, map_mul]; ring
    simp only [this, h1, h2, hvn, Finset.sum_add_distrib, Finset.sum_sub_distrib, hφn, mul_one]
    have : ∑ r, conj (c r) * c r = ∑ r, c r * conj (c r) :=
      Finset.sum_congr rfl fun r _ => by ring
    rw [this, hc]; ring
  have hns : ∀ r x, d r x * conj (d r x) = ((Complex.normSq (d r x) : ℝ) : ℂ) := by
    intro r x; rw [Complex.mul_conj]
  simp only [hns] at hsum
  have hsumR : ∑ r, ∑ x, Complex.normSq (d r x) = 0 := by exact_mod_cast hsum
  intro r x
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ =>
    Finset.sum_nonneg fun x _ => Complex.normSq_nonneg (d r x))).1 hsumR r (Finset.mem_univ _)
  have h00 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    Complex.normSq_nonneg (d r x))).1 h0 x (Finset.mem_univ _)
  rw [Complex.normSq_eq_zero] at h00
  exact sub_eq_zero.1 h00

/-- The trace channel to a one-dimensional output. -/
def g55d_trch (X : Type*) [Fintype X] : Superop X (Fin 1) :=
  fun Y => Matrix.of fun _ _ => Y.trace

lemma g55d_trch_chan {X : Type*} [Fintype X] {_ : DecidableEq X} : IsChannel (g55d_trch X) := by
  let e := Fintype.equivFin X
  refine ⟨Fintype.card X, fun j => Matrix.of fun _ a => if a = e.symm j then 1 else 0, ?_, ?_⟩
  · unfold IsKrausFamily
    ext a b
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply]
    simp only [Fin.sum_univ_one]
    rw [e.symm.sum_comp (fun x => star (if a = x then (1:ℂ) else 0) * if b = x then 1 else 0)]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  · intro ρ
    ext i j
    simp only [g55d_trch, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    exact (e.symm.sum_comp (fun x => ρ x x)).symm

theorem solution {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi)
    (hpure : ∃ v : EuclideanSpace ℂ (A × B), IsState v ∧
      traceLeft (pureDensity phi) = pureDensity v) :
    compressionRegion (pureDensity phi) = {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by
  obtain ⟨v, hv, hvφ⟩ := hpure
  obtain ⟨c, hfac, hc⟩ : ∃ c : R → ℂ, (∀ r x, phi (r, x) = c r * v x) ∧
      ∑ r, c r * conj (c r) = 1 := ⟨_, g55d_factor phi hphi v hv hvφ⟩
  ext q
  constructor
  · intro hq
    have hsub : compressionAchievable (pureDensity phi) ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} :=
      fun q hq => ⟨hq.1, hq.2.1⟩
    exact closure_minimal hsub ((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)) hq
  · rintro ⟨h1, h2⟩
    apply subset_closure
    refine ⟨h1, h2, fun eps heps => ⟨0, fun n _ => ?_⟩⟩
    let Cn : (Fin n → R) → ℂ := fun rr => ∏ t, c (rr t)
    let Wn : (Fin n → A) × (Fin n → B) → ℂ := fun p => ∏ t, v (p.1 t, p.2 t)
    have hS : ∀ i j, sourceCopies n (pureDensity phi) i j =
        Cn i.1 * Wn i.2 * conj (Cn j.1 * Wn j.2) := by
      intro i j
      simp only [sourceCopies, pureDensity, Matrix.of_apply, hfac, Cn, Wn, map_mul, map_prod,
        ← Finset.prod_mul_distrib]
    have hC : ∑ rr, Cn rr * conj (Cn rr) = 1 := by
      simp only [Cn, map_prod, ← Finset.prod_mul_distrib]
      rw [← Fintype.prod_sum (fun _ r => c r * conj (c r))]
      simp [hc]
    have hv1 := g55d_norm_one v hv
    rw [Fintype.sum_prod_type] at hv1
    have hW : ∑ p, Wn p * conj (Wn p) = 1 := by
      simp only [Wn, map_prod, ← Finset.prod_mul_distrib, Fintype.sum_prod_type]
      have : ∀ aa : Fin n → A, ∑ bb : Fin n → B, ∏ t, v (aa t, bb t) * conj (v (aa t, bb t)) =
          ∏ t, ∑ b, v (aa t, b) * conj (v (aa t, b)) := fun aa =>
        (Fintype.prod_sum (fun t b => v (aa t, b) * conj (v (aa t, b)))).symm
      simp only [this]
      rw [← Fintype.prod_sum (fun _ a => ∑ b, v (a, b) * conj (v (a, b)))]
      simp [hv1]
    set S := sourceCopies n (pureDensity phi) with hSdef
    let EA := g55d_trch (Fin n → A)
    let EB := g55d_trch (Fin n → B)
    let K : Fin 1 → Matrix ((Fin n → A) × (Fin n → B)) (Fin 1 × Fin 1) ℂ :=
      fun _ => Matrix.of fun x _ => Wn x
    have hK : IsKrausFamily K := by
      unfold IsKrausFamily; ext a b
      have hab : a = b := Subsingleton.elim a b
      subst hab
      simp only [Fin.sum_univ_one, Matrix.mul_apply, Matrix.conjTranspose_apply, K,
        Matrix.of_apply, Matrix.one_apply_eq]
      rw [← hW]
      exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]; rfl
    refine ⟨1, 1, one_pos, one_pos, by simp; positivity, by simp; positivity, EA,
      g55d_trch_chan, EB, g55d_trch_chan, krausApply K, ⟨1, K, hK, fun _ => rfl⟩, ?_⟩
    have hT : ∀ p q, idTensorSuperop (krausApply K ∘ both EA EB) S p q =
        (∑ x, S (p.1, x) (q.1, x)) * Wn p.2 * conj (Wn q.2) := by
      intro p q
      simp only [idTensorSuperop, Function.comp, both, first, krausApply, EA, EB, g55d_trch,
        K, Matrix.of_apply, Fin.sum_univ_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      rw [Finset.sum_comm (f := fun i i_1 => S (p.1, i_1, i) (q.1, i_1, i))]
      simp only [Complex.star_def]; ring
    have hT' : ∀ p q, idTensorSuperop (krausApply K ∘ both EA EB) S p q =
        Cn p.1 * conj (Cn q.1) * Wn p.2 * conj (Wn q.2) := by
      intro p q
      rw [hT]
      have : ∑ x, S (p.1, x) (q.1, x) = Cn p.1 * conj (Cn q.1) * ∑ x, Wn x * conj (Wn x) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by rw [hS]; simp only [map_mul]; ring
      rw [this, hW, mul_one]
    have htr : (S * idTensorSuperop (krausApply K ∘ both EA EB) S).trace = 1 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hT']
      have hf : ∑ i : (Fin n → R) × ((Fin n → A) × (Fin n → B)),
          Cn i.1 * conj (Cn i.1) * (Wn i.2 * conj (Wn i.2)) = 1 := by
        rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum, ← Finset.sum_mul, hW, mul_one, hC]
      calc ∑ i, ∑ j, S i j * (Cn j.1 * conj (Cn i.1) * Wn j.2 * conj (Wn i.2))
          = (∑ i : (Fin n → R) × ((Fin n → A) × (Fin n → B)),
              Cn i.1 * conj (Cn i.1) * (Wn i.2 * conj (Wn i.2))) *
            (∑ j : (Fin n → R) × ((Fin n → A) × (Fin n → B)),
              Cn j.1 * conj (Cn j.1) * (Wn j.2 * conj (Wn j.2))) := by
            rw [Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hS]; simp only [map_mul]; ring
        _ = 1 := by rw [hf, one_mul]
    rw [htr]; simp; linarith
