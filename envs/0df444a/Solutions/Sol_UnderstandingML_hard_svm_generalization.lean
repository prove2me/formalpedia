-- Prove2me | solution 1 for UnderstandingML.hard_svm_generalization
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:44:41.079346+00:00
-- url     : https://prove2.me/submissions/65151a58-96dd-4f2b-8621-2709c2e14146

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Pointwise
import Definitions.Def_UnderstandingML_SVM

open MeasureTheory ProbabilityTheory

namespace HardSVMAux

variable {Z : Type*} [MeasurableSpace Z]

/-- Integrability of a bounded measurable function against a finite measure. -/
theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun x ↦ by
    simpa [Real.norm_eq_abs] using hM x)

/-- **McDiarmid's inequality, moment generating function form.** -/
theorem mcdiarmid_mgf (D : Measure Z) [IsProbabilityMeasure D] (c : ℝ) :
    ∀ (n : ℕ) (f : (Fin n → Z) → ℝ), Measurable f → (∃ M, ∀ x, |f x| ≤ M) →
      (∀ x i z, |f x - f (Function.update x i z)| ≤ c) → ∀ s : ℝ, 0 < s →
      ∫ x, Real.exp (s * (f x - ∫ y, f y ∂(Measure.pi fun _ ↦ D))) ∂(Measure.pi fun _ ↦ D) ≤
        Real.exp (n * (c ^ 2 / 4) * s ^ 2 / 2) := by
  intro n
  induction n with
  | zero =>
    intro f _ _ _ s _
    have hconst : ∀ x y : Fin 0 → Z, f x = f y := fun x y ↦ by
      rw [Subsingleton.elim x y]
    have : ∀ x : Fin 0 → Z, f x - ∫ y, f y ∂(Measure.pi fun _ ↦ D) = 0 := by
      intro x
      rw [show (fun y ↦ f y) = fun _ ↦ f x from funext fun y ↦ hconst y x]
      simp
    simp [this]
  | succ n ih =>
    intro f hf ⟨M, hM⟩ hc s hs
    have hne : Nonempty Z := by
      by_contra h
      rw [not_nonempty_iff] at h
      have h1 := measure_univ (μ := D)
      rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
      exact zero_ne_one h1
    obtain ⟨z0⟩ := hne
    have : Nonempty Z := ⟨z0⟩
    have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc (fun _ ↦ z0) 0 z0)
    set π := Measure.pi fun _ : Fin n ↦ D with hπ
    set π' := Measure.pi fun _ : Fin (n + 1) ↦ D with hπ'
    have mp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Z) 0)
        π' (D.prod π) := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ D) 0
    have hsymm : ∀ p : Z × (Fin n → Z),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Z) 0).symm p = Fin.cons p.1 p.2 := by
      intro p
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
      rfl
    have htrans : ∀ φ : (Fin (n + 1) → Z) → ℝ,
        ∫ x, φ x ∂π' = ∫ p, φ (Fin.cons p.1 p.2) ∂(D.prod π) := by
      intro φ
      rw [← mp.symm.integral_comp' φ]
      simp only [hsymm]
    set F : Z × (Fin n → Z) → ℝ := fun p ↦ f (Fin.cons p.1 p.2) with hFdef
    have hF_meas : Measurable F := by
      have : F = f ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Z) 0).symm := by
        funext p; simp only [hFdef, Function.comp_apply, hsymm]
      rw [this]; exact hf.comp (MeasurableEquiv.measurable _)
    have hFbdd : ∀ p, |F p| ≤ M := fun p ↦ hM _
    set g : (Fin n → Z) → ℝ := fun x ↦ ∫ a, F (a, x) ∂D with hgdef
    have hg_meas : Measurable g :=
      (hF_meas.stronglyMeasurable.integral_prod_left' (μ := D)).measurable
    have hFint : ∀ x, Integrable (fun a ↦ F (a, x)) D := fun x ↦
      integrable_of_bdd (hF_meas.comp (measurable_id.prodMk measurable_const)) M fun a ↦ hFbdd _
    have hg_bdd : ∀ x, |g x| ≤ M := by
      intro x
      have := norm_integral_le_of_norm_le_const (μ := D) (f := fun a ↦ F (a, x)) (C := M)
        (Filter.Eventually.of_forall fun a ↦ by simpa [Real.norm_eq_abs] using hFbdd (a, x))
      simpa [Real.norm_eq_abs] using this
    have hg_diff : ∀ x i z, |g x - g (Function.update x i z)| ≤ c := by
      intro x i z
      have e1 : g x - g (Function.update x i z) =
          ∫ a, (F (a, x) - F (a, Function.update x i z)) ∂D := by
        rw [integral_sub (hFint x) (hFint _)]
      rw [e1]
      have := norm_integral_le_of_norm_le_const (μ := D)
        (f := fun a ↦ F (a, x) - F (a, Function.update x i z)) (C := c)
        (Filter.Eventually.of_forall fun a ↦ by
          rw [Real.norm_eq_abs]
          simp only [hFdef, Fin.cons_update]
          exact hc _ _ _)
      simpa [Real.norm_eq_abs] using this
    have hEF : ∫ y, f y ∂π' = ∫ x, g x ∂π := by
      rw [htrans]
      exact integral_prod_symm F (integrable_of_bdd hF_meas M hFbdd)
    -- inner Hoeffding step
    set K : ℝ := c ^ 2 / 4 * s ^ 2 / 2 with hK
    have hinner : ∀ x, ∫ a, Real.exp (s * (F (a, x) - g x)) ∂D ≤ Real.exp K := by
      intro x
      have hbdd : BddBelow (Set.range fun a ↦ F (a, x)) :=
        ⟨-M, by rintro _ ⟨a, rfl⟩; linarith [abs_le.mp (hFbdd (a, x))]⟩
      set L := ⨅ a, F (a, x) with hL
      have hlow : ∀ a, L ≤ F (a, x) := fun a ↦ ciInf_le hbdd a
      have hup : ∀ a, F (a, x) ≤ L + c := by
        intro a
        have : F (a, x) - c ≤ L := by
          apply le_ciInf
          intro a'
          have h1 := hc (Fin.cons a x) 0 a'
          simp only [Fin.update_cons_zero] at h1
          have h2 := (abs_le.mp h1).2
          simp only [hFdef]
          linarith
        linarith
      set X : Z → ℝ := fun a ↦ F (a, x) - g x with hX
      have hXmeas : Measurable X :=
        (hF_meas.comp (measurable_id.prodMk measurable_const)).sub measurable_const
      have hX0 : ∫ a, X a ∂D = 0 := by
        simp only [hX]
        rw [integral_sub (hFint x) (integrable_const _), integral_const]
        simp [hgdef]
      have hmgf := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (μ := D) (X := X)
        (a := L - g x) (b := L + c - g x) hXmeas.aemeasurable
        (Filter.Eventually.of_forall fun a ↦ ⟨by simp only [hX]; linarith [hlow a],
          by simp only [hX]; linarith [hup a]⟩) hX0 hs
      have hcoe : ((‖L + c - g x - (L - g x)‖₊ : ℝ)) = c := by
        rw [show L + c - g x - (L - g x) = c by ring, coe_nnnorm, Real.norm_eq_abs,
          abs_of_nonneg hc0]
      rw [hcoe] at hmgf
      have e2 : (c / 2) ^ 2 * s ^ 2 / 2 = K := by rw [hK]; ring
      rw [e2] at hmgf
      simpa [mgf, hX, hK] using hmgf
    have hExpInt : ∀ (φ : (Fin n → Z) → ℝ), Measurable φ → (∀ x, |φ x| ≤ M) → ∀ C : ℝ,
        Integrable (fun x ↦ Real.exp (s * (φ x - C))) π := by
      intro φ hφ hφb C
      refine integrable_of_bdd (by fun_prop) (Real.exp (s * (M - C))) fun x ↦ ?_
      rw [abs_of_pos (Real.exp_pos _)]
      gcongr
      linarith [abs_le.mp (hφb x)]
    have hih := ih g hg_meas ⟨M, hg_bdd⟩ hg_diff s hs
    set EF := ∫ y, f y ∂π' with hEFdef
    calc ∫ x, Real.exp (s * (f x - EF)) ∂π'
        = ∫ p, Real.exp (s * (F p - EF)) ∂(D.prod π) := by rw [htrans]
      _ = ∫ x, ∫ a, Real.exp (s * (F (a, x) - EF)) ∂D ∂π := by
          refine integral_prod_symm _ (integrable_of_bdd (by fun_prop)
            (Real.exp (s * (M - EF))) fun p ↦ ?_)
          rw [abs_of_pos (Real.exp_pos _)]
          gcongr
          linarith [abs_le.mp (hFbdd p)]
      _ = ∫ x, Real.exp (s * (g x - EF)) * ∫ a, Real.exp (s * (F (a, x) - g x)) ∂D ∂π := by
          congr 1; funext x
          rw [← integral_const_mul]
          congr 1; funext a
          rw [← Real.exp_add]; ring_nf
      _ ≤ ∫ x, Real.exp (s * (g x - EF)) * Real.exp K ∂π := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun x ↦
              mul_nonneg (Real.exp_pos _).le (integral_nonneg fun a ↦ (Real.exp_pos _).le)
          · exact (hExpInt g hg_meas hg_bdd EF).mul_const _
          · exact Filter.Eventually.of_forall fun x ↦
              mul_le_mul_of_nonneg_left (hinner x) (Real.exp_pos _).le
      _ = Real.exp K * ∫ x, Real.exp (s * (g x - ∫ y, g y ∂π)) ∂π := by
          rw [integral_mul_const, hEF, mul_comm]
      _ ≤ Real.exp K * Real.exp (n * (c ^ 2 / 4) * s ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hih (Real.exp_pos _).le
      _ = Real.exp (↑(n + 1) * (c ^ 2 / 4) * s ^ 2 / 2) := by
          rw [← Real.exp_add, hK]; push_cast; ring_nf

/-- **McDiarmid's inequality** (upper tail). -/
theorem mcdiarmid_tail (D : Measure Z) [IsProbabilityMeasure D] (n : ℕ) (hn : 0 < n)
    (f : (Fin n → Z) → ℝ) (hf : Measurable f) (hbdd : ∃ M, ∀ x, |f x| ≤ M) (c : ℝ) (hc0 : 0 < c)
    (hc : ∀ x i z, |f x - f (Function.update x i z)| ≤ c) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n ↦ D) {x | (∫ y, f y ∂(Measure.pi fun _ ↦ D)) + t ≤ f x} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (n * c ^ 2))) := by
  set π := Measure.pi fun _ : Fin n ↦ D with hπ
  set EF := ∫ y, f y ∂π with hEF
  obtain ⟨M, hM⟩ := hbdd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := 4 * t / (n * c ^ 2) with hs
  have hs0 : 0 < s := by positivity
  have hint : Integrable (fun x ↦ Real.exp (s * (f x - EF))) π := by
    refine integrable_of_bdd (by fun_prop) (Real.exp (s * (M - EF))) fun x ↦ ?_
    rw [abs_of_pos (Real.exp_pos _)]
    gcongr
    linarith [abs_le.mp (hM x)]
  have h1 := measure_ge_le_exp_mul_mgf (μ := π) (X := fun x ↦ f x - EF) t hs0.le hint
  have h2 := mcdiarmid_mgf D c n f hf ⟨M, hM⟩ hc s hs0
  have hset : {x | EF + t ≤ f x} = {x | t ≤ f x - EF} := by
    ext x; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  rw [hset, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine h1.trans ?_
  calc Real.exp (-s * t) * mgf (fun x ↦ f x - EF) π s
      ≤ Real.exp (-s * t) * Real.exp (n * (c ^ 2 / 4) * s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-2 * t ^ 2 / (n * c ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hs]
        field_simp
        ring

end HardSVMAux


open scoped InnerProductSpace

namespace HardSVMAux

/-- The sign `±1` encoded by a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

theorem sgn_not (b : Bool) : sgn (!b) = - sgn b := by cases b <;> simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- Sum of two suprema bounded by a common bound on all pairs. -/
theorem ciSup_add_ciSup_le {T : Type*} [Nonempty T] {f g : T → ℝ} {C : ℝ}
    (h : ∀ t t', f t + g t' ≤ C) : (⨆ t, f t) + (⨆ t, g t) ≤ C := by
  have h1 : ∀ t, f t + ⨆ t', g t' ≤ C := by
    intro t
    have : (⨆ t', g t') ≤ C - f t := ciSup_le fun t' ↦ by linarith [h t t']
    linarith
  have : (⨆ t, f t) ≤ C - ⨆ t', g t' := ciSup_le fun t ↦ by linarith [h1 t]
  linarith

theorem bddAbove_of_abs_le {T : Type*} {f : T → ℝ} {K : ℝ} (h : ∀ t, |f t| ≤ K) :
    BddAbove (Set.range f) := ⟨K, by rintro _ ⟨t, rfl⟩; exact (abs_le.mp (h t)).2⟩

/-- One-coordinate contraction step. -/
theorem sup_pair_contract {T : Type*} [Nonempty T] (R u : T → ℝ) (K : ℝ)
    (hR : ∀ t, |R t| ≤ K) (hu : ∀ t, |u t| ≤ K) (φ : ℝ → ℝ)
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (s : ℝ) (hs : |s| = 1) :
    (⨆ t, (R t + s * φ (u t))) + (⨆ t, (R t - s * φ (u t))) ≤
      (⨆ t, (R t + s * u t)) + (⨆ t, (R t - s * u t)) := by
  have hb1 : BddAbove (Set.range fun t ↦ R t + s * u t) :=
    bddAbove_of_abs_le (K := K + K) fun t ↦ by
      rw [abs_le]; have := abs_le.mp (hR t); have := abs_le.mp (hu t)
      rcases abs_eq (zero_le_one) |>.mp hs with h | h <;> subst h <;> constructor <;> linarith
  have hb2 : BddAbove (Set.range fun t ↦ R t - s * u t) :=
    bddAbove_of_abs_le (K := K + K) fun t ↦ by
      rw [abs_le]; have := abs_le.mp (hR t); have := abs_le.mp (hu t)
      rcases abs_eq (zero_le_one) |>.mp hs with h | h <;> subst h <;> constructor <;> linarith
  have hb3 : BddAbove (Set.range fun t ↦ R t - s * φ (u t)) :=
    bddAbove_of_abs_le (K := K + (|φ 0| + K)) fun t ↦ by
      have h1 := hφ (u t) 0
      simp only [sub_zero] at h1
      have h2 : |φ (u t)| ≤ |φ 0| + K := by
        have := abs_sub_abs_le_abs_sub (φ (u t)) (φ 0)
        linarith [hu t]
      rw [abs_le]; have := abs_le.mp (hR t); have := abs_le.mp h2
      rcases abs_eq (zero_le_one) |>.mp hs with h | h <;> subst h <;> constructor <;> linarith
  apply ciSup_add_ciSup_le
  intro t t'
  have key : s * (φ (u t) - φ (u t')) ≤ |u t - u t'| := by
    calc s * (φ (u t) - φ (u t')) ≤ |s * (φ (u t) - φ (u t'))| := le_abs_self _
      _ = |φ (u t) - φ (u t')| := by rw [abs_mul, hs, one_mul]
      _ ≤ |u t - u t'| := hφ _ _
  rcases le_total 0 (s * (u t - u t')) with hpos | hneg
  · have hle : |u t - u t'| ≤ s * (u t - u t') := by
      rcases abs_eq (zero_le_one) |>.mp hs with h | h <;> subst h
      · simp only [one_mul] at hpos ⊢; rw [abs_of_nonneg hpos]
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg (u t - u t')]
    calc R t + s * φ (u t) + (R t' - s * φ (u t'))
        ≤ (R t + s * u t) + (R t' - s * u t') := by nlinarith
      _ ≤ (⨆ t, (R t + s * u t)) + (⨆ t, (R t - s * u t)) :=
          add_le_add (le_ciSup hb1 t) (le_ciSup hb2 t')
  · have hle : |u t - u t'| ≤ -(s * (u t - u t')) := by
      rw [← abs_neg (u t - u t')]
      rcases abs_eq (zero_le_one) |>.mp hs with h | h <;> subst h
      · simp only [one_mul] at hneg ⊢; rw [abs_of_nonneg (by linarith)]
      · simp only [neg_one_mul, neg_neg] at hneg ⊢; rw [abs_le]; constructor <;> linarith
    calc R t + s * φ (u t) + (R t' - s * φ (u t'))
        ≤ (R t' + s * u t') + (R t - s * u t) := by nlinarith
      _ ≤ (⨆ t, (R t + s * u t)) + (⨆ t, (R t - s * u t)) :=
          add_le_add (le_ciSup hb1 t') (le_ciSup hb2 t)

/-- Sum over sign vectors is invariant under flipping one coordinate. -/
theorem sum_flip {m : ℕ} (j : Fin m) (F : (Fin m → Bool) → ℝ) :
    ∑ σ, F σ = ∑ σ, F (Function.update σ j (!σ j)) := by
  have hinv : Function.Involutive (fun σ : Fin m → Bool ↦ Function.update σ j (!σ j)) := by
    intro σ; funext i; by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  exact (Fintype.sum_equiv hinv.toPerm (fun σ ↦ F (Function.update σ j (!σ j))) F
    (fun σ ↦ rfl)).symm

/-- The contraction lemma for sums over sign vectors (Lemma 26.9). -/
theorem contraction {m : ℕ} {T : Type*} [Nonempty T] (a : T → Fin m → ℝ) (K : ℝ)
    (hK : ∀ t i, |a t i| ≤ K) (φ : ℝ → ℝ) (hφ : ∀ u v, |φ u - φ v| ≤ |u - v|) :
    ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * φ (a t i) ≤
      ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * a t i := by
  classical
  set ψ : ℕ → Fin m → ℝ → ℝ := fun k i u ↦ if (i : ℕ) < k then u else φ u with hψ
  set G : ℕ → ℝ := fun k ↦ ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * ψ k i (a t i) with hG
  have hψb : ∀ k i t, |ψ k i (a t i)| ≤ |φ 0| + K := by
    intro k i t
    simp only [hψ]
    split_ifs
    · have := abs_nonneg (φ 0); linarith [hK t i]
    · have h1 := hφ (a t i) 0
      have := abs_sub_abs_le_abs_sub (φ (a t i)) (φ 0)
      simp only [sub_zero] at h1
      linarith [hK t i]
  have step : ∀ k, k < m → G k ≤ G (k + 1) := by
    intro k hk
    set j : Fin m := ⟨k, hk⟩ with hj
    have hK0 : 0 ≤ K := by
      obtain ⟨t⟩ := ‹Nonempty T›
      exact le_trans (abs_nonneg _) (hK t j)
    set K' : ℝ := m * (|φ 0| + K) + K with hK'
    -- rest of the sum, outside coordinate `j`
    set R : (Fin m → Bool) → T → ℝ := fun σ t ↦
      ∑ i ∈ Finset.univ.erase j, sgn (σ i) * ψ (k + 1) i (a t i) with hR
    have hRb : ∀ σ t, |R σ t| ≤ K' := by
      intro σ t
      simp only [hR]
      calc |∑ i ∈ Finset.univ.erase j, sgn (σ i) * ψ (k + 1) i (a t i)|
          ≤ ∑ i ∈ Finset.univ.erase j, |sgn (σ i) * ψ (k + 1) i (a t i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.univ.erase j, (|φ 0| + K) := by
            apply Finset.sum_le_sum; intro i _
            rw [abs_mul, abs_sgn, one_mul]; exact hψb _ _ _
        _ ≤ ∑ _i : Fin m, (|φ 0| + K) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun _ _ _ ↦ by positivity)
        _ ≤ K' := by simp [hK']; linarith
    have hau : ∀ t, |a t j| ≤ K' := fun t ↦ by
      have : 0 ≤ (m : ℝ) * (|φ 0| + K) := by positivity
      linarith [hK t j]
    have hagree : ∀ i, i ≠ j → ∀ u, ψ k i u = ψ (k + 1) i u := by
      intro i hi u
      simp only [hψ]
      have : (i : ℕ) ≠ k := fun h ↦ hi (Fin.ext h)
      by_cases h1 : (i : ℕ) < k
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
    have hsplit : ∀ (σ : Fin m → Bool) (k' : ℕ) (t : T),
        ∑ i, sgn (σ i) * ψ k' i (a t i) =
          sgn (σ j) * ψ k' j (a t j) + ∑ i ∈ Finset.univ.erase j, sgn (σ i) * ψ k' i (a t i) := by
      intro σ k' t
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    have hk_j : ∀ u, ψ k j u = φ u := fun u ↦ by simp [hψ, hj]
    have hk1_j : ∀ u, ψ (k + 1) j u = u := fun u ↦ by simp [hψ, hj]
    have hrest : ∀ σ t, ∑ i ∈ Finset.univ.erase j, sgn (σ i) * ψ k i (a t i) = R σ t := by
      intro σ t
      simp only [hR]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hagree i (Finset.ne_of_mem_erase hi)]
    have hflipR : ∀ σ t, R (Function.update σ j (!σ j)) t = R σ t := by
      intro σ t
      simp only [hR]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hFk : ∀ σ, (⨆ t, ∑ i, sgn (σ i) * ψ k i (a t i)) =
        ⨆ t, (R σ t + sgn (σ j) * φ (a t j)) := by
      intro σ; congr 1; funext t
      rw [hsplit, hrest, hk_j]; ring
    have hFk1 : ∀ σ, (⨆ t, ∑ i, sgn (σ i) * ψ (k + 1) i (a t i)) =
        ⨆ t, (R σ t + sgn (σ j) * a t j) := by
      intro σ; congr 1; funext t
      rw [hsplit, hk1_j]; simp only [hR]; ring
    have hflip_j : ∀ σ : Fin m → Bool, sgn ((Function.update σ j (!σ j)) j) = - sgn (σ j) := by
      intro σ; simp [sgn_not]
    have h2k : 2 * G k = ∑ σ : Fin m → Bool,
        ((⨆ t, (R σ t + sgn (σ j) * φ (a t j))) + (⨆ t, (R σ t - sgn (σ j) * φ (a t j)))) := by
      have hGk : G k = ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * ψ k i (a t i) := rfl
      rw [two_mul]
      nth_rewrite 2 [hGk]
      rw [sum_flip j, hGk, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      rw [hFk, hFk, hflip_j]
      congr 1; congr 1; funext t; rw [hflipR]; ring
    have h2k1 : 2 * G (k + 1) = ∑ σ : Fin m → Bool,
        ((⨆ t, (R σ t + sgn (σ j) * a t j)) + (⨆ t, (R σ t - sgn (σ j) * a t j))) := by
      have hGk : G (k + 1) = ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * ψ (k + 1) i (a t i) := rfl
      rw [two_mul]
      nth_rewrite 2 [hGk]
      rw [sum_flip j, hGk, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      rw [hFk1, hFk1, hflip_j]
      congr 1; congr 1; funext t; rw [hflipR]; ring
    have : 2 * G k ≤ 2 * G (k + 1) := by
      rw [h2k, h2k1]
      apply Finset.sum_le_sum
      intro σ _
      exact sup_pair_contract (R σ) (fun t ↦ a t j) K' (hRb σ) hau φ hφ (sgn (σ j)) (abs_sgn _)
    linarith
  have hmono : ∀ k, k ≤ m → G 0 ≤ G k := by
    intro k
    induction k with
    | zero => intro _; exact le_refl _
    | succ k ih => intro hk; exact (ih (by omega)).trans (step k (by omega))
  have h0 : G 0 = ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * φ (a t i) := by
    simp [hG, hψ]
  have hm : G m = ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * a t i := by
    simp only [hG, hψ]
    apply Finset.sum_congr rfl; intro σ _
    congr 1; funext t
    apply Finset.sum_congr rfl; intro i _
    rw [if_pos i.isLt]
  rw [← h0, ← hm]
  exact hmono m le_rfl

theorem card_signs (m : ℕ) : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
  simp [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]

theorem sum_sgn_mul_sgn {m : ℕ} (i j : Fin m) :
    ∑ σ : Fin m → Bool, sgn (σ i) * sgn (σ j) = if i = j then (2 : ℝ) ^ m else 0 := by
  split_ifs with hij
  · subst hij
    simp only [sgn_sq, Finset.sum_const, card_signs, nsmul_eq_mul, mul_one]
    push_cast; ring
  · have h := sum_flip i (fun σ ↦ sgn (σ i) * sgn (σ j))
    simp only [Function.update_self, sgn_not, Function.update_of_ne (Ne.symm hij)] at h
    rw [show (∑ σ : Fin m → Bool, -sgn (σ i) * sgn (σ j)) =
      -∑ σ : Fin m → Bool, sgn (σ i) * sgn (σ j) by
        rw [← Finset.sum_neg_distrib]; congr 1; funext σ; ring] at h
    linarith

theorem sum_norm_sq_signs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) :
    ∑ σ : Fin m → Bool, ‖∑ i, sgn (σ i) • v i‖ ^ 2 = 2 ^ m * ∑ i, ‖v i‖ ^ 2 := by
  have hexp : ∀ σ : Fin m → Bool, ‖∑ i, sgn (σ i) • v i‖ ^ 2 =
      ∑ i, ∑ j, (sgn (σ i) * sgn (σ j)) * ⟪v i, v j⟫_ℝ := by
    intro σ
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    apply Finset.sum_congr rfl; intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  simp only [hexp]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_sgn_mul_sgn]
  rw [Finset.sum_eq_single i]
  · simp [real_inner_self_eq_norm_sq]
  · intro j _ hji; simp [Ne.symm hji]
  · simp

theorem sum_norm_signs_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (v : Fin m → E) :
    ∑ σ : Fin m → Bool, ‖∑ i, sgn (σ i) • v i‖ ≤ 2 ^ m * Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m → Bool)))
    (f := fun σ ↦ ‖∑ i, sgn (σ i) • v i‖)
  rw [card_signs, sum_norm_sq_signs] at hcs
  have hnn : 0 ≤ ∑ σ : Fin m → Bool, ‖∑ i, sgn (σ i) • v i‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hS : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ by positivity
  calc ∑ σ : Fin m → Bool, ‖∑ i, sgn (σ i) • v i‖
      = Real.sqrt ((∑ σ : Fin m → Bool, ‖∑ i, sgn (σ i) • v i‖) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (((2 ^ m : ℕ) : ℝ) * (2 ^ m * ∑ i, ‖v i‖ ^ 2)) := Real.sqrt_le_sqrt hcs
    _ = 2 ^ m * Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
        push_cast
        rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]

/-- The Rademacher bound for a Lipschitz loss of a norm-bounded linear class. -/
theorem rad_linear_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (hm : 0 < m) {T : Type*} [Nonempty T] (w : T → E) (B : ℝ) (hw : ∀ t, ‖w t‖ ≤ B)
    (v : Fin m → E) (ρ : ℝ) (hv : ∀ i, ‖v i‖ ≤ ρ) (φ : ℝ → ℝ)
    (hφ : ∀ u u', |φ u - φ u'| ≤ |u - u'|) :
    (1 / 2 ^ m) * ∑ σ : Fin m → Bool, ⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * φ ⟪w t, v i⟫_ℝ ≤
      B * ρ / Real.sqrt m := by
  obtain ⟨t0⟩ := ‹Nonempty T›
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hw t0)
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) (hv ⟨0, hm⟩)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hK : ∀ t i, |⟪w t, v i⟫_ℝ| ≤ B * ρ := fun t i ↦
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hw t) (hv i) (norm_nonneg _) hB)
  have h1 : ∀ σ : Fin m → Bool, (⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * φ ⟪w t, v i⟫_ℝ) =
      (1 / (m : ℝ)) * ⨆ t, ∑ i, sgn (σ i) * φ ⟪w t, v i⟫_ℝ := fun σ ↦
    (Real.mul_iSup_of_nonneg (by positivity) _).symm
  simp only [h1, ← Finset.mul_sum]
  have hcon := contraction (fun t i ↦ ⟪w t, v i⟫_ℝ) (B * ρ) hK φ hφ
  have hlin : ∀ σ : Fin m → Bool, (⨆ t, ∑ i, sgn (σ i) * ⟪w t, v i⟫_ℝ) ≤
      B * ‖∑ i, sgn (σ i) • v i‖ := by
    intro σ
    apply ciSup_le
    intro t
    have : ∑ i, sgn (σ i) * ⟪w t, v i⟫_ℝ = ⟪w t, ∑ i, sgn (σ i) • v i⟫_ℝ := by
      rw [inner_sum]; apply Finset.sum_congr rfl; intro i _; rw [real_inner_smul_right]
    rw [this]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hw t) (norm_nonneg _))
  have hsum : ∑ σ : Fin m → Bool, (⨆ t, ∑ i, sgn (σ i) * φ ⟪w t, v i⟫_ℝ) ≤
      B * (2 ^ m * (ρ * Real.sqrt m)) := by
    refine hcon.trans ((Finset.sum_le_sum fun σ _ ↦ hlin σ).trans ?_)
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hB
    refine (sum_norm_signs_le v).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : ∑ i, ‖v i‖ ^ 2 ≤ m * ρ ^ 2 := by
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin m, ρ ^ 2 :=
            Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
        _ = m * ρ ^ 2 := by simp
    calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt (m * ρ ^ 2) := Real.sqrt_le_sqrt this
      _ = ρ * Real.sqrt m := by
          rw [Real.sqrt_mul hmR.le, Real.sqrt_sq hρ, mul_comm]
  have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hmR.le
  have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  calc 1 / 2 ^ m * (1 / (m : ℝ) * ∑ σ : Fin m → Bool, ⨆ t, ∑ i, sgn (σ i) * φ ⟪w t, v i⟫_ℝ)
      ≤ 1 / 2 ^ m * (1 / (m : ℝ) * (B * (2 ^ m * (ρ * Real.sqrt m)))) := by gcongr
    _ = B * ρ / Real.sqrt m := by
        rw [eq_div_iff hsm0.ne']
        have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
        field_simp
        linear_combination (B * ρ) * hsm

end HardSVMAux


open MeasureTheory ProbabilityTheory

namespace HardSVMAux

variable {Z : Type*} [MeasurableSpace Z]

/-- Empirical average of `h t` on the sample `S`. -/
noncomputable def empR {T : Type*} {m : ℕ} (h : T → Z → ℝ) (S : Fin m → Z) (t : T) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, h t (S i)

/-- Representativeness `sup_t (L_D(h_t) − L_S(h_t))`. -/
noncomputable def repr {T : Type*} {m : ℕ} (D : Measure Z) (h : T → Z → ℝ) (S : Fin m → Z) : ℝ :=
  ⨆ t, (∫ z, h t z ∂D - empR h S t)

/-- Empirical Rademacher complexity of `{h_t}` on `S`. -/
noncomputable def radC {T : Type*} {m : ℕ} (h : T → Z → ℝ) (S : Fin m → Z) : ℝ :=
  (1 / 2 ^ m) * ∑ σ : Fin m → Bool, ⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (S i)

theorem abs_ciSup_le {T : Type*} [Nonempty T] {f : T → ℝ} {K : ℝ} (h : ∀ t, |f t| ≤ K) :
    |⨆ t, f t| ≤ K := by
  obtain ⟨t0⟩ := ‹Nonempty T›
  rw [abs_le]
  constructor
  · exact le_trans (abs_le.mp (h t0)).1 (le_ciSup (bddAbove_of_abs_le h) t0)
  · exact ciSup_le fun t ↦ (abs_le.mp (h t)).2

section Sym

variable {T : Type*} [Countable T] [Nonempty T] (D : Measure Z) [IsProbabilityMeasure D]
  (h : T → Z → ℝ) (hmeas : ∀ t, Measurable (h t)) (h01 : ∀ t z, 0 ≤ h t z ∧ h t z ≤ 1)

include h01 in
theorem abs_empR_le {m : ℕ} (S : Fin m → Z) (t : T) : |empR h S t| ≤ 1 := by
  unfold empR
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : 0 ≤ ∑ i, h t (S i) := Finset.sum_nonneg fun i _ ↦ (h01 t _).1
    have h2 : ∑ i, h t (S i) ≤ m := by
      calc ∑ i, h t (S i) ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (h01 t _).2
        _ = m := by simp
    rw [abs_of_nonneg (by positivity), div_mul_eq_mul_div, one_mul, div_le_one hmR]
    exact h2

include hmeas in
theorem measurable_empR {m : ℕ} (t : T) : Measurable (fun S : Fin m → Z ↦ empR h S t) := by
  unfold empR
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦ (hmeas t).comp (measurable_pi_apply i))

theorem integral_empR {m : ℕ} (hm : 0 < m) (t : T) (hmt : Measurable (h t))
    (hb : ∀ z, |h t z| ≤ 1) :
    ∫ S, empR h S t ∂(Measure.pi fun _ : Fin m ↦ D) = ∫ z, h t z ∂D := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold empR
  rw [integral_const_mul, integral_finset_sum]
  · simp only [integral_comp_eval (μ := fun _ : Fin m ↦ D) (f := h t)
      hmt.aestronglyMeasurable]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact integrable_of_bdd ((hmt).comp (measurable_pi_apply i)) 1 fun S ↦ hb _

theorem abs_avg_le {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |(1 / (m : ℝ)) * ∑ i, a i| ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
    have : |∑ i, a i| ≤ m := (Finset.abs_sum_le_sum_abs _ _).trans
      (by simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ ha i)
    calc 1 / (m : ℝ) * |∑ i, a i| ≤ 1 / m * m := by gcongr
      _ = 1 := by field_simp

/-- Coordinatewise swap of two samples according to `σ`. -/
def swapS {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → Z) × (Fin m → Z)) :
    (Fin m → Z) × (Fin m → Z) :=
  (fun i ↦ if σ i then p.1 i else p.2 i, fun i ↦ if σ i then p.2 i else p.1 i)

theorem measurePreserving_swapS {m : ℕ} (σ : Fin m → Bool) :
    MeasurePreserving (swapS σ) ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ ↦ D))
      ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ ↦ D)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin m)
  have he := measurePreserving_arrowProdEquivProdArrow Z Z (Fin m) (fun _ ↦ D) (fun _ ↦ D)
  have hf : ∀ i : Fin m, MeasurePreserving (fun q : Z × Z ↦ if σ i then q else q.swap)
      (D.prod D) (D.prod D) := by
    intro i
    by_cases hi : σ i
    · simp only [hi, if_true]; exact MeasurePreserving.id _
    · simp only [hi]; exact Measure.measurePreserving_swap
  have hpi := measurePreserving_pi (fun _ : Fin m ↦ D.prod D) (fun _ ↦ D.prod D) hf
  have hcomp := (he.comp hpi).comp he.symm
  convert hcomp using 1
  funext p
  simp only [Function.comp_apply, swapS]
  ext i <;> by_cases hi : σ i <;> simp [e, hi, MeasurableEquiv.arrowProdEquivProdArrow,
    Equiv.arrowProdEquivProdArrow]

include hmeas h01 in
/-- **Symmetrization** (Lemma 26.2). -/
theorem repr_le_two_rad {m : ℕ} (hm : 0 < m) :
    ∫ S, repr D h S ∂(Measure.pi fun _ : Fin m ↦ D) ≤
      2 * ∫ S, radC h S ∂(Measure.pi fun _ : Fin m ↦ D) := by
  set π := Measure.pi fun _ : Fin m ↦ D with hπ
  have hb : ∀ t z, |h t z| ≤ 1 := fun t z ↦ by
    rw [abs_le]; constructor <;> linarith [h01 t z]
  set Psi : (Fin m → Z) × (Fin m → Z) → ℝ := fun p ↦ ⨆ t, (empR h p.2 t - empR h p.1 t)
  have hPsib : ∀ p, |Psi p| ≤ 2 := fun p ↦ abs_ciSup_le fun t ↦ by
    have := abs_empR_le h h01 p.1 t; have := abs_empR_le h h01 p.2 t
    rw [abs_le] at *; constructor <;> linarith
  have hPsim : Measurable Psi := Measurable.iSup fun t ↦
    ((measurable_empR h hmeas t).comp measurable_snd).sub ((measurable_empR h hmeas t).comp measurable_fst)
  have hPsii : Integrable Psi (π.prod π) := integrable_of_bdd hPsim 2 hPsib
  -- Step 1
  have hstep1 : ∀ S, repr D h S ≤ ∫ S', Psi (S, S') ∂π := by
    intro S
    apply ciSup_le
    intro t
    rw [← integral_empR D h hm t (hmeas t) (hb t)]
    have hi1 : Integrable (fun S' ↦ empR h S' t) π :=
      integrable_of_bdd (measurable_empR h hmeas t) 1 fun S' ↦ abs_empR_le h h01 S' t
    have hi2 : Integrable (fun S' ↦ Psi (S, S')) π :=
      integrable_of_bdd (hPsim.comp measurable_prodMk_left) 2 fun S' ↦ hPsib _
    calc ∫ S', empR h S' t ∂π - empR h S t = ∫ S', (empR h S' t - empR h S t) ∂π := by
          rw [integral_sub hi1 (integrable_const _)]; simp
      _ ≤ ∫ S', Psi (S, S') ∂π := by
          apply integral_mono (hi1.sub (integrable_const _)) hi2
          intro S'
          simp only [Pi.sub_apply]
          exact le_ciSup (f := fun t ↦ empR h S' t - empR h S t)
            (bddAbove_of_abs_le (K := 2) fun t ↦ by
              have := abs_empR_le h h01 S t; have := abs_empR_le h h01 S' t
              rw [abs_le] at *; constructor <;> linarith) t
  have hreprm : Measurable (fun S : Fin m → Z ↦ repr D h S) := Measurable.iSup fun t ↦
    measurable_const.sub (measurable_empR h hmeas t)
  have hreprb : ∀ S : Fin m → Z, |repr D h S| ≤ 2 := fun S ↦ abs_ciSup_le fun t ↦ by
    have := abs_empR_le h h01 S t
    have h1 : |∫ z, h t z ∂D| ≤ 1 := by
      have := norm_integral_le_of_norm_le_const (μ := D) (f := h t) (C := 1)
        (Filter.Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs] using hb t z)
      simpa [Real.norm_eq_abs] using this
    rw [abs_le] at *; constructor <;> linarith
  have hA : ∫ S, repr D h S ∂π ≤ ∫ p, Psi p ∂(π.prod π) := by
    rw [integral_prod Psi hPsii]
    exact integral_mono (integrable_of_bdd hreprm 2 hreprb) hPsii.integral_prod_left hstep1
  -- Step 2: symmetrize
  set g : (Fin m → Bool) → (Fin m → Z) × (Fin m → Z) → ℝ := fun σ p ↦
    ⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * (h t (p.2 i) - h t (p.1 i))
  have hgPsi : ∀ σ p, Psi (swapS σ p) = g σ p := by
    intro σ p
    simp only [Psi, g, empR, swapS]
    congr 1; funext t
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _
    by_cases hi : σ i <;> simp [hi, sgn]
  have hgb : ∀ σ p, |g σ p| ≤ 2 := fun σ p ↦ by rw [← hgPsi]; exact hPsib _
  have hgm : ∀ σ, Measurable (g σ) := fun σ ↦ by
    have : g σ = Psi ∘ swapS σ := by funext p; simp [hgPsi]
    rw [this]; exact hPsim.comp (measurePreserving_swapS D σ).measurable
  have hgint : ∀ σ, ∫ p, g σ p ∂(π.prod π) = ∫ p, Psi p ∂(π.prod π) := by
    intro σ
    have hmp := measurePreserving_swapS D σ
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hPsim.aestronglyMeasurable,
      hmp.map_eq]
    simp [hgPsi]
  have hB : ∫ p, Psi p ∂(π.prod π) = ∫ p, (1 / 2 ^ m) * ∑ σ, g σ p ∂(π.prod π) := by
    rw [integral_const_mul, integral_finset_sum _ fun σ _ ↦ integrable_of_bdd (hgm σ) 2 (hgb σ)]
    simp only [hgint, Finset.sum_const, card_signs, nsmul_eq_mul]
    push_cast
    field_simp
  -- Step 3: split
  have hC : ∀ p, (1 / 2 ^ m) * ∑ σ, g σ p ≤ radC h p.2 + radC h p.1 := by
    intro p
    have hsplit : ∀ σ, g σ p ≤ (⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (p.2 i)) +
        (⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (!σ i) * h t (p.1 i)) := by
      intro σ
      apply ciSup_le; intro t
      have e1 : (1 / (m : ℝ)) * ∑ i, sgn (σ i) * (h t (p.2 i) - h t (p.1 i)) =
          (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (p.2 i) +
            (1 / (m : ℝ)) * ∑ i, sgn (!σ i) * h t (p.1 i) := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1; apply Finset.sum_congr rfl; intro i _; rw [sgn_not]; ring
      rw [e1]
      apply add_le_add
      · exact le_ciSup (f := fun t ↦ (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (p.2 i))
          (bddAbove_of_abs_le fun t ↦ abs_avg_le _ fun i ↦ by
            rw [abs_mul, abs_sgn, one_mul]; exact hb _ _) t
      · exact le_ciSup (f := fun t ↦ (1 / (m : ℝ)) * ∑ i, sgn (!σ i) * h t (p.1 i))
          (bddAbove_of_abs_le fun t ↦ abs_avg_le _ fun i ↦ by
            rw [abs_mul, abs_sgn, one_mul]; exact hb _ _) t
    have hneg : ∑ σ : Fin m → Bool, (⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (!σ i) * h t (p.1 i)) =
        ∑ σ : Fin m → Bool, (⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (p.1 i)) := by
      have hinv : Function.Involutive (fun σ : Fin m → Bool ↦ fun i ↦ !σ i) := by
        intro σ; funext i; simp only [Bool.not_not]
      exact Fintype.sum_equiv hinv.toPerm _ _ fun σ ↦ rfl
    have := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) ↦ hsplit σ
    rw [Finset.sum_add_distrib, hneg] at this
    unfold radC
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hradm : Measurable (fun S : Fin m → Z ↦ radC h S) := by
    unfold radC
    exact measurable_const.mul (Finset.measurable_sum _ fun σ _ ↦ Measurable.iSup fun t ↦
      measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
        measurable_const.mul ((hmeas t).comp (measurable_pi_apply i))))
  have hradb : ∀ S : Fin m → Z, |radC h S| ≤ 1 := fun S ↦ by
    unfold radC
    have : |∑ σ : Fin m → Bool, ⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (S i)| ≤ 2 ^ m := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _σ : Fin m → Bool, (1 : ℝ) := Finset.sum_le_sum fun σ _ ↦
            abs_ciSup_le fun t ↦ abs_avg_le _ fun i ↦ by
              rw [abs_mul, abs_sgn, one_mul]; exact hb _ _
        _ = 2 ^ m := by simp [card_signs]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m)]
    calc 1 / 2 ^ m * _ ≤ 1 / 2 ^ m * (2 : ℝ) ^ m := by gcongr
      _ = 1 := by field_simp
  have hradi : Integrable (fun S : Fin m → Z ↦ radC h S) π := integrable_of_bdd hradm 1 hradb
  have hD : ∫ p, (1 / 2 ^ m) * ∑ σ, g σ p ∂(π.prod π) ≤
      ∫ p, (radC h p.2 + radC h p.1) ∂(π.prod π) := by
    apply integral_mono _ _ hC
    · exact integrable_of_bdd (measurable_const.mul (Finset.measurable_sum _ fun σ _ ↦ hgm σ))
        (1 / 2 ^ m * (2 ^ m * 2)) fun p ↦ by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m)]
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc _ ≤ ∑ _σ : Fin m → Bool, (2 : ℝ) := Finset.sum_le_sum fun σ _ ↦ hgb σ p
            _ = 2 ^ m * 2 := by simp [card_signs]
    · exact (integrable_of_bdd (hradm.comp measurable_snd) 1 fun p ↦ hradb _).add
        (integrable_of_bdd (hradm.comp measurable_fst) 1 fun p ↦ hradb _)
  have hE : ∫ p, (radC h p.2 + radC h p.1) ∂(π.prod π) = 2 * ∫ S, radC h S ∂π := by
    rw [integral_add (f := fun p : (Fin m → Z) × (Fin m → Z) ↦ radC h p.2)
      (g := fun p : (Fin m → Z) × (Fin m → Z) ↦ radC h p.1)
      (integrable_of_bdd (hradm.comp measurable_snd) 1 fun p ↦ hradb _)
      (integrable_of_bdd (hradm.comp measurable_fst) 1 fun p ↦ hradb _)]
    rw [integral_fun_snd (f := fun S ↦ radC h S), integral_fun_fst (f := fun S ↦ radC h S)]
    simp; ring
  linarith

end Sym

end HardSVMAux


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace HardSVMAux

open UnderstandingML

/-- The ramp profile `u ↦ min 1 (max 0 (1 - u))`. -/
noncomputable def rampPhi (u : ℝ) : ℝ := min 1 (max 0 (1 - u))

theorem rampPhi_lip (a b : ℝ) : |rampPhi a - rampPhi b| ≤ |a - b| := by
  unfold rampPhi
  simp only [min_def, max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;>
    first | linarith | (rw [abs_le] at *; linarith) | (cases abs_cases (a - b) <;> linarith)

theorem ramp_eq {d : ℕ} (w : Vec d) (z : Vec d × ℝ) :
    rampLoss w z = rampPhi ⟪w, z.2 • z.1⟫_ℝ := by
  simp [rampLoss, hingeLoss, rampPhi, real_inner_smul_right]

theorem ramp_mem {d : ℕ} (w : Vec d) (z : Vec d × ℝ) : 0 ≤ rampLoss w z ∧ rampLoss w z ≤ 1 := by
  unfold rampLoss hingeLoss
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem ramp_lip {d : ℕ} (w w' : Vec d) (z : Vec d × ℝ) :
    |rampLoss w z - rampLoss w' z| ≤ ‖w - w'‖ * ‖z.2 • z.1‖ := by
  rw [ramp_eq, ramp_eq]
  refine (rampPhi_lip _ _).trans ?_
  rw [← inner_sub_left]
  exact abs_real_inner_le_norm _ _

theorem zeroOne_le_ramp {d : ℕ} (w : Vec d) (z : Vec d × ℝ) : zeroOneLoss w z ≤ rampLoss w z := by
  unfold zeroOneLoss rampLoss hingeLoss
  split_ifs with h
  · exact le_min le_rfl (le_max_of_le_right (by linarith))
  · exact le_min zero_le_one (le_max_left _ _)

theorem zeroOne_nonneg {d : ℕ} (w : Vec d) (z : Vec d × ℝ) : 0 ≤ zeroOneLoss w z := by
  unfold zeroOneLoss; split_ifs <;> norm_num

theorem ramp_zero_of_margin {d : ℕ} (w : Vec d) (z : Vec d × ℝ) (h : 1 ≤ z.2 * ⟪w, z.1⟫_ℝ) :
    rampLoss w z = 0 := by
  unfold rampLoss hingeLoss
  rw [max_eq_left (by linarith)]; simp

theorem measurable_ramp {d : ℕ} (w : Vec d) : Measurable (fun z : Vec d × ℝ ↦ rampLoss w z) := by
  have : Continuous (fun z : Vec d × ℝ ↦ rampLoss w z) := by
    unfold rampLoss hingeLoss; fun_prop
  exact this.measurable

theorem abs_ciSup_sub_ciSup_le {T : Type*} [Nonempty T] {f g : T → ℝ} {K c : ℝ}
    (hf : ∀ t, |f t| ≤ K) (hg : ∀ t, |g t| ≤ K) (hfg : ∀ t, |f t - g t| ≤ c) :
    |(⨆ t, f t) - ⨆ t, g t| ≤ c := by
  rw [abs_le]
  constructor
  · have : (⨆ t, g t) ≤ (⨆ t, f t) + c := ciSup_le fun t ↦ by
      have := le_ciSup (bddAbove_of_abs_le hf) t
      have := (abs_le.mp (hfg t)).1
      linarith
    linarith
  · have : (⨆ t, f t) ≤ (⨆ t, g t) + c := ciSup_le fun t ↦ by
      have := le_ciSup (bddAbove_of_abs_le hg) t
      have := (abs_le.mp (hfg t)).2
      linarith
    linarith

section

variable {Z : Type*} [MeasurableSpace Z] {T : Type*} [Countable T] [Nonempty T]
  (D : Measure Z) [IsProbabilityMeasure D]
  (h : T → Z → ℝ) (hmeas : ∀ t, Measurable (h t)) (h01 : ∀ t z, 0 ≤ h t z ∧ h t z ≤ 1)

include h01 in
theorem abs_empR_update {m : ℕ} (hm : 0 < m) (S : Fin m → Z) (i : Fin m) (z : Z) (t : T) :
    |empR h S t - empR h (Function.update S i z) t| ≤ 1 / m := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold empR
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have : ∑ j, (h t (S j) - h t (Function.update S i z j)) =
      ∑ j, (if j = i then h t (S i) - h t z else 0) := by
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, Function.update_of_ne hj]
  rw [this, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / m)]
  have h1 := h01 t (S i); have h2 := h01 t z
  have : |h t (S i) - h t z| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc 1 / (m : ℝ) * |h t (S i) - h t z| ≤ 1 / m * 1 := by gcongr
    _ = 1 / m := by ring

include h01 in
theorem abs_int_le (t : T) : |∫ z, h t z ∂D| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := D) (f := h t) (C := 1)
    (Filter.Eventually.of_forall fun z ↦ by
      have := h01 t z; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
  simpa [Real.norm_eq_abs] using this

include h01 in
theorem abs_repr_le {m : ℕ} (S : Fin m → Z) : |repr D h S| ≤ 2 :=
  abs_ciSup_le fun t ↦ by
    have := abs_empR_le h h01 S t
    have := abs_int_le D h h01 t
    rw [abs_le] at *; constructor <;> linarith

include hmeas in
theorem measurable_repr {m : ℕ} : Measurable (fun S : Fin m → Z ↦ repr D h S) :=
  Measurable.iSup fun t ↦ measurable_const.sub (measurable_empR h hmeas t)

include h01 in
theorem abs_radC_le {m : ℕ} (S : Fin m → Z) : |radC h S| ≤ 1 := by
  unfold radC
  have hb : ∀ t z, |h t z| ≤ 1 := fun t z ↦ by
    rw [abs_le]; constructor <;> linarith [h01 t z]
  have : |∑ σ : Fin m → Bool, ⨆ t, (1 / (m : ℝ)) * ∑ i, sgn (σ i) * h t (S i)| ≤ 2 ^ m := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _σ : Fin m → Bool, (1 : ℝ) := Finset.sum_le_sum fun σ _ ↦
          abs_ciSup_le fun t ↦ abs_avg_le _ fun i ↦ by
            rw [abs_mul, abs_sgn, one_mul]; exact hb _ _
      _ = 2 ^ m := by simp [card_signs]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ m)]
  calc 1 / 2 ^ m * _ ≤ 1 / 2 ^ m * (2 : ℝ) ^ m := by gcongr
    _ = 1 := by field_simp

include hmeas in
theorem measurable_radC {m : ℕ} : Measurable (fun S : Fin m → Z ↦ radC h S) := by
  unfold radC
  exact measurable_const.mul (Finset.measurable_sum _ fun σ _ ↦ Measurable.iSup fun t ↦
    measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
      measurable_const.mul ((hmeas t).comp (measurable_pi_apply i))))

end

theorem hard_svm_main {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    {γ ρ : ℝ} (hγ : 0 < γ) (hsep : HomSeparableWithMargin D γ ρ)
    (hlab : ∀ᵐ z ∂D, z.2 = 1 ∨ z.2 = -1) (A : Learner (Vec d × ℝ) (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → Vec d × ℝ), (∃ w : Vec d, ∀ i, 1 ≤ (S i).2 * ⟪w, (S i).1⟫_ℝ) →
      IsHomHardSVM (fun i ↦ (S i).1) (fun i ↦ (S i).2) (A m S))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 0 < m) :
    iidLaw D m {S | Real.sqrt (4 * (ρ / γ) ^ 2 / m) + Real.sqrt (2 * Real.log (2 / δ) / m) <
        risk zeroOneLoss D (A m S)} ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨wst, hwst1, hwst⟩ := hsep
  have hρ : 0 ≤ ρ := by
    obtain ⟨z, hz⟩ := hwst.exists
    exact (norm_nonneg _).trans hz.2
  set B : ℝ := 1 / γ with hBdef
  have hB : 0 < B := by positivity
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense (Metric.closedBall (0 : Vec d) B)
  haveI : Countable s := hsc.to_subtype
  haveI : Nonempty (Metric.closedBall (0 : Vec d) B) := ⟨⟨0, by simp [hB.le]⟩⟩
  haveI : Nonempty s := hsd.nonempty.to_subtype
  set wt : s → Vec d := fun t ↦ ((t : Metric.closedBall (0 : Vec d) B) : Vec d) with hwt
  have hwtB : ∀ t, ‖wt t‖ ≤ B := fun t ↦ mem_closedBall_zero_iff.1 (t : Metric.closedBall (0 : Vec d) B).2
  set h : s → Vec d × ℝ → ℝ := fun t z ↦ rampLoss (wt t) z with hh
  have hmeas : ∀ t, Measurable (h t) := fun t ↦ measurable_ramp (wt t)
  have h01 : ∀ t z, 0 ≤ h t z ∧ h t z ≤ 1 := fun t z ↦ ramp_mem _ _
  set π := Measure.pi fun _ : Fin m ↦ D with hπ
  have hiid : iidLaw D m = π := rfl
  set good : Vec d × ℝ → Prop := fun z ↦
    (z.2 = 1 ∨ z.2 = -1) ∧ (γ ≤ z.2 * ⟪wst, z.1⟫_ℝ ∧ ‖z.1‖ ≤ ρ) with hgood
  have hgoodD : ∀ᵐ z ∂D, good z := hlab.and hwst
  have hgoodS : ∀ᵐ S ∂π, ∀ i, good (S i) :=
    ae_all_iff.2 fun i ↦ (Measure.tendsto_eval_ae_ae (i := i)).eventually hgoodD
  have hnormv : ∀ z, good z → ‖z.2 • z.1‖ ≤ ρ := by
    intro z hz
    rw [norm_smul]
    rcases hz.1 with h1 | h1 <;> rw [h1] <;> simpa using hz.2.2
  -- key deterministic step
  have hkey : ∀ S : Fin m → Vec d × ℝ, (∀ i, good (S i)) →
      risk zeroOneLoss D (A m S) ≤ repr D h S := by
    intro S hS
    have hfeasw : ∀ i, 1 ≤ (S i).2 * ⟪B • wst, (S i).1⟫_ℝ := by
      intro i
      rw [real_inner_smul_left]
      have := (hS i).2.1
      have : (S i).2 * (B * ⟪wst, (S i).1⟫_ℝ) = B * ((S i).2 * ⟪wst, (S i).1⟫_ℝ) := by ring
      rw [this]
      calc (1 : ℝ) = B * γ := by rw [hBdef]; field_simp
        _ ≤ _ := by gcongr
    obtain ⟨hc, hmin⟩ := hA m S ⟨_, hfeasw⟩
    set w0 := A m S with hw0
    have hnorm : ‖w0‖ ≤ B := (hmin _ hfeasw).trans (by rw [norm_smul, hwst1]; simp [abs_of_pos hB])
    have hint0 : Integrable (fun z ↦ rampLoss w0 z) D :=
      integrable_of_bdd (measurable_ramp w0) 1 fun z ↦ by
        have := ramp_mem w0 z; rw [abs_le]; constructor <;> linarith
    have h1 : risk zeroOneLoss D w0 ≤ ∫ z, rampLoss w0 z ∂D :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun z ↦ zeroOne_nonneg w0 z) hint0
        (Filter.Eventually.of_forall fun z ↦ zeroOne_le_ramp w0 z)
    have h2 : ∀ ε, 0 < ε → ∫ z, rampLoss w0 z ∂D ≤ repr D h S + ε := by
      intro ε hε
      set η := ε / (2 * ρ + 1) with hη
      have hηpos : 0 < η := by positivity
      obtain ⟨y, hys, hy⟩ := hsd.exists_dist_lt
        (⟨w0, mem_closedBall_zero_iff.2 hnorm⟩ : Metric.closedBall (0 : Vec d) B) hηpos
      set t : s := ⟨y, hys⟩
      have hdist : ‖w0 - wt t‖ < η := by rw [← dist_eq_norm]; exact hy
      have hlip : ∀ z, good z → |rampLoss w0 z - h t z| ≤ η * ρ := by
        intro z hz
        refine (ramp_lip _ _ z).trans ?_
        exact mul_le_mul hdist.le (hnormv z hz) (norm_nonneg _) hηpos.le
      have hA1 : ∫ z, rampLoss w0 z ∂D - ∫ z, h t z ∂D ≤ η * ρ := by
        have hit : Integrable (h t) D := integrable_of_bdd (hmeas t) 1 fun z ↦ by
          have := h01 t z; rw [abs_le]; constructor <;> linarith
        rw [← integral_sub hint0 hit]
        calc ∫ z, (rampLoss w0 z - h t z) ∂D ≤ ∫ _z, η * ρ ∂D :=
              integral_mono_ae (hint0.sub hit) (integrable_const _)
                (hgoodD.mono fun z hz ↦ (le_abs_self _).trans (hlip z hz))
          _ = η * ρ := by simp
      have hA2 : empR h S t ≤ η * ρ := by
        unfold empR
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have : ∑ i, h t (S i) ≤ ∑ _i : Fin m, η * ρ := Finset.sum_le_sum fun i _ ↦ by
          have := hlip (S i) (hS i)
          rw [ramp_zero_of_margin w0 (S i) (hc i)] at this
          rw [abs_le] at this; linarith
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        calc 1 / (m : ℝ) * ∑ i, h t (S i) ≤ 1 / m * (m * (η * ρ)) := by gcongr
          _ = η * ρ := by field_simp
      have hA3 : ∫ z, h t z ∂D - empR h S t ≤ repr D h S :=
        le_ciSup (f := fun t ↦ ∫ z, h t z ∂D - empR h S t) (bddAbove_of_abs_le (K := 2) fun t ↦ by
          have := abs_empR_le h h01 S t; have := abs_int_le D h h01 t
          rw [abs_le] at *; constructor <;> linarith) t
      have hA4 : 2 * (η * ρ) ≤ ε := by
        rw [hη, div_mul_eq_mul_div, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    have h3 : ∫ z, rampLoss w0 z ∂D ≤ repr D h S := le_of_forall_pos_le_add h2
    exact h1.trans h3
  -- expected Rademacher complexity
  have hrad : ∫ S, radC h S ∂π ≤ B * ρ / Real.sqrt m := by
    have hae : ∀ᵐ S ∂π, radC h S ≤ B * ρ / Real.sqrt m := hgoodS.mono fun S hS ↦ by
      have := rad_linear_bound hm wt B hwtB (fun i ↦ (S i).2 • (S i).1) ρ
        (fun i ↦ hnormv _ (hS i)) rampPhi rampPhi_lip
      unfold radC
      simpa only [hh, ramp_eq] using this
    calc ∫ S, radC h S ∂π ≤ ∫ _S, B * ρ / Real.sqrt m ∂π :=
          integral_mono_ae (integrable_of_bdd (measurable_radC h hmeas) 1 (abs_radC_le h h01))
            (integrable_const _) hae
      _ = B * ρ / Real.sqrt m := by simp
  have hE : ∫ S, repr D h S ∂π ≤ 2 * (B * ρ / Real.sqrt m) :=
    (repr_le_two_rad D h hmeas h01 hm).trans (by linarith)
  -- McDiarmid
  set τ := Real.sqrt (2 * Real.log (2 / δ) / m) with hτdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hτ : 0 < τ := Real.sqrt_pos.2 (by positivity)
  have hmc := mcdiarmid_tail D m hm (fun S ↦ repr D h S) (measurable_repr D h hmeas)
    ⟨2, abs_repr_le D h h01⟩ (1 / m) (by positivity)
    (fun S i z ↦ abs_ciSup_sub_ciSup_le (K := 2)
      (fun t ↦ by
        have := abs_empR_le h h01 S t; have := abs_int_le D h h01 t
        rw [abs_le] at *; constructor <;> linarith)
      (fun t ↦ by
        have := abs_empR_le h h01 (Function.update S i z) t; have := abs_int_le D h h01 t
        rw [abs_le] at *; constructor <;> linarith)
      (fun t ↦ by
        have := abs_empR_update h h01 hm S i z t
        have e : ∫ z, h t z ∂D - empR h S t - (∫ z, h t z ∂D - empR h (Function.update S i z) t)
            = -(empR h S t - empR h (Function.update S i z) t) := by ring
        rw [e, abs_neg]; exact this)) τ hτ
  have hexp : Real.exp (-2 * τ ^ 2 / (m * (1 / m) ^ 2)) ≤ δ := by
    have hτsq : τ ^ 2 = 2 * Real.log (2 / δ) / m := Real.sq_sqrt (by positivity)
    have : -2 * τ ^ 2 / (m * (1 / m) ^ 2) = -4 * Real.log (2 / δ) := by
      rw [hτsq]; field_simp; ring
    rw [this]
    have h2d : 1 ≤ 2 / δ := by rw [le_div_iff₀ hδ0]; linarith
    calc Real.exp (-4 * Real.log (2 / δ)) ≤ Real.exp (- Real.log (2 / δ)) := by
          apply Real.exp_le_exp.2; nlinarith
      _ = δ / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
      _ ≤ δ := by linarith
  have hsq : Real.sqrt (4 * (ρ / γ) ^ 2 / m) = 2 * (B * ρ / Real.sqrt m) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    rw [hBdef]
    field_simp
    rw [Real.sq_sqrt hmR.le]
    ring
  calc iidLaw D m {S | Real.sqrt (4 * (ρ / γ) ^ 2 / m) + Real.sqrt (2 * Real.log (2 / δ) / m) <
        risk zeroOneLoss D (A m S)}
      ≤ π ({S | ¬ ∀ i, good (S i)} ∪ {S | (∫ y, repr D h y ∂π) + τ ≤ repr D h S}) := by
        rw [hiid]
        apply measure_mono
        intro S hS
        by_cases hg : ∀ i, good (S i)
        · right
          have := hkey S hg
          simp only [Set.mem_setOf_eq] at hS ⊢
          rw [hsq] at hS
          linarith
        · left; exact hg
    _ ≤ π {S | ¬ ∀ i, good (S i)} + π {S | (∫ y, repr D h y ∂π) + τ ≤ repr D h S} :=
        measure_union_le _ _
    _ = π {S | (∫ y, repr D h y ∂π) + τ ≤ repr D h S} := by
        rw [ae_iff.1 hgoodS, zero_add]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * τ ^ 2 / (m * (1 / m) ^ 2))) := hmc
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hexp

end HardSVMAux

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

/-- **Theorem 15.4** (Hard-SVM generalization bound). -/
theorem solution {d : ℕ} (D : Measure (Vec d × ℝ)) [IsProbabilityMeasure D]
    {γ ρ : ℝ} (hγ : 0 < γ) (hsep : HomSeparableWithMargin D γ ρ)
    (hlab : ∀ᵐ z ∂D, z.2 = 1 ∨ z.2 = -1) (A : Learner (Vec d × ℝ) (Vec d))
    (hA : ∀ (m : ℕ) (S : Fin m → Vec d × ℝ), (∃ w : Vec d, ∀ i, 1 ≤ (S i).2 * ⟪w, (S i).1⟫_ℝ) →
      IsHomHardSVM (fun i ↦ (S i).1) (fun i ↦ (S i).2) (A m S))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : 0 < m) :
    iidLaw D m {S | Real.sqrt (4 * (ρ / γ) ^ 2 / m) + Real.sqrt (2 * Real.log (2 / δ) / m) <
        risk zeroOneLoss D (A m S)} ≤ ENNReal.ofReal δ :=
  HardSVMAux.hard_svm_main D hγ hsep hlab A hA hδ0 hδ1 m hm
