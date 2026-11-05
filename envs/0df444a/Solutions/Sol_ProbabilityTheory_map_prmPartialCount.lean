-- Prove2me | solution 1 for ProbabilityTheory.map_prmPartialCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:14:45.562766+00:00
-- url     : https://prove2.me/submissions/5eae44e4-be76-47c1-a663-4c26328e1140

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PrMPartialCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
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

private lemma measurable_prmPartialCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) (n : ℕ) :
    Measurable (prmPartialCount K X A n) :=
  Finset.measurable_sum _ fun k _ => measurable_thinnedCount (hK k) (hX k) hA

private lemma indepFun_prmPartialCount_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (n : ℕ) :
    IndepFun (prmPartialCount K X A n) (thinnedCount K X A (n + 1)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;>
      simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → ℕ :=
    fun g => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → ℕ :=
    fun g => ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact Finset.measurable_sum _ fun k _ =>
      measurable_filterCard
        (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        hA (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact measurable_filterCard
      (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
      hA (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
      (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω) = prmPartialCount K X A n := by
    funext ω
    simp only [hG_def]
    unfold prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X A j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = thinnedCount K X A (n + 1) := by
    funext ω; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rwa [hGeq, hHeq] at key

private lemma poissonMeasure_conv (a b : ℝ≥0) :
    poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b) :=
  poissonMeasure_add_conv a b

theorem solution [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (n : ℕ) :
    μ.map (prmPartialCount K X A n)
      = poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal) := by
  induction n with
  | zero =>
    have h0 : prmPartialCount K X A 0 = thinnedCount K X A 0 := by
      funext ω; rw [prmPartialCount, Finset.sum_range_one]
    rw [h0, map_thinnedCount hd hA, Finset.sum_range_one]
  | succ n ih =>
    have hsucc : prmPartialCount K X A (n + 1)
        = prmPartialCount K X A n + thinnedCount K X A (n + 1) := by
      funext ω; simp only [prmPartialCount, Pi.add_apply, Finset.sum_range_succ]
    have hlawP : HasLaw (prmPartialCount K X A n)
        (poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal)) μ :=
      ⟨(measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n).aemeasurable, ih⟩
    have hlawT : HasLaw (thinnedCount K X A (n + 1))
        (poissonMeasure (m (prmPiece m (n + 1) ∩ A)).toNNReal) μ :=
      ⟨(measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) hA).aemeasurable,
        map_thinnedCount hd hA⟩
    have hsum := (indepFun_prmPartialCount_thinnedCount hd hA n).hasLaw_add hlawP hlawT
    rw [hsucc, hsum.map_eq, poissonMeasure_conv]
    congr 1
    exact (Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A)).toNNReal) (n + 1)).symm
