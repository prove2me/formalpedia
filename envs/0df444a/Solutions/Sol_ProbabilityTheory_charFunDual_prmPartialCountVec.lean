-- Prove2me | solution 1 for ProbabilityTheory.charFunDual_prmPartialCountVec
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:15:43.539716+00:00
-- url     : https://prove2.me/submissions/4caa11f8-9dd8-4e15-a9e8-b4e503d74b78

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_ProbabilityTheory_charFunDual_pi_thinnedCount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Complex ProbabilityTheory
open scoped ENNReal NNReal Topology
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E]
  {μ : Measure Ω} {A B : Set E} {ω : Ω}
open Classical in
private lemma measurable_filterCard {E D : Type} [MeasurableSpace E] [MeasurableSpace D] {A : Set E}
    (hA : MeasurableSet A) (cnt : D → ℕ) (pt : ℕ → D → E)
    (hcnt : Measurable cnt) (hpt : ∀ n', Measurable (pt n')) :
    Measurable fun g => ((Finset.range (cnt g)).filter fun n' => pt n' g ∈ A).card := by
  classical
  have hcard : (fun g => ((Finset.range (cnt g)).filter fun n' => pt n' g ∈ A).card)
      = fun g => ∑ n' ∈ Finset.range (cnt g), (if pt n' g ∈ A then (1 : ℕ) else 0) := by
    funext g; rw [Finset.card_filter]
  rw [hcard]
  have hP : Measurable
      fun p : D × ℕ => ∑ n' ∈ Finset.range p.2, (if pt n' p.1 ∈ A then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n' _ =>
        Measurable.ite (hpt n' hA) measurable_const measurable_const
  exact hP.comp (measurable_id.prodMk hcnt)

private lemma indepFun_prmPartialCountVec_thinnedCountVec {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    IndepFun (fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ))
      (fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℝ)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;> simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → (ι → ℕ) :=
    fun g (i : ι) => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A i).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → (ι → ℕ) :=
    fun g (i : ι) =>
      ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A i).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun k _ =>
      measurable_filterCard (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        (hA i) (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact measurable_pi_lambda _ fun i =>
      measurable_filterCard (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
        (hA i) (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω)
      = fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℕ) := by
    funext ω i
    simp only [hG_def]
    unfold prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X (A i) j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℕ) := by
    funext ω i; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rw [hGeq, hHeq] at key
  have hcast := key.comp (φ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (ψ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (measurable_pi_lambda _ fun i => measurable_from_top.comp (measurable_pi_apply i))
    (measurable_pi_lambda _ fun i => measurable_from_top.comp (measurable_pi_apply i))
  simpa only [Function.comp_def] using hcast

private lemma measurable_prmPartialCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) (n : ℕ) :
    Measurable (prmPartialCount K X A n) :=
  Finset.measurable_sum _ fun k _ => measurable_thinnedCount (hK k) (hX k) hA

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A)) (n : ℕ)
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L
      = ∏ i, Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
          * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  induction n with
  | zero =>
    have h0 : (fun ω (i : ι) => (prmPartialCount K X (A i) 0 ω : ℝ))
        = fun ω (i : ι) => (thinnedCount K X (A i) 0 ω : ℝ) := by
      funext ω i; rw [prmPartialCount, Finset.sum_range_one]
    rw [h0, charFunDual_pi_thinnedCount hd hA hdisj L]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  | succ n ih =>
    have mPn : Measurable fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ) :=
      measurable_pi_lambda _ fun i => measurable_from_top.comp
        (measurable_prmPartialCount hd.measurable_count hd.measurable_point (hA i) n)
    have mQn : Measurable fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℝ) :=
      measurable_pi_lambda _ fun i => measurable_from_top.comp
        (measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) (hA i))
    have hsucc : (fun ω (i : ι) => (prmPartialCount K X (A i) (n + 1) ω : ℝ))
        = fun ω => (fun i => (prmPartialCount K X (A i) n ω : ℝ))
            + fun i => (thinnedCount K X (A i) (n + 1) ω : ℝ) := by
      funext ω i
      simp only [Pi.add_apply]
      rw [prmPartialCount, Finset.sum_range_succ, Nat.cast_add]; rfl
    rw [hsucc, IndepFun.charFunDual_map_fun_add_eq_mul mPn.aemeasurable mQn.aemeasurable
        (indepFun_prmPartialCountVec_thinnedCountVec hd hA n), Pi.mul_apply, ih,
      charFunDual_pi_thinnedCount hd hA hdisj L, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A i)).toReal) (n + 1), ← Complex.exp_add]
    congr 1
    push_cast
    ring
