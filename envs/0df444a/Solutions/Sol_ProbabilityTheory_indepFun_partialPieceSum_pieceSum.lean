-- Prove2me | solution 1 for ProbabilityTheory.indepFun_partialPieceSum_pieceSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:16:59.457777+00:00
-- url     : https://prove2.me/submissions/e59def6c-cac9-4812-b3ec-94bb018b38d8

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}
private lemma measurable_pieceSumExtract {D : Type*} [MeasurableSpace D] {f : ℝ × ℝ → ℝ}
    (hf : Measurable f) (cnt : D → ℕ) (pt : ℕ → D → ℝ × ℝ) (hcnt : Measurable cnt)
    (hpt : ∀ n, Measurable (pt n)) :
    Measurable fun g => ∑ n ∈ Finset.range (cnt g), f (pt n g) := by
  have hP : Measurable fun p : D × ℕ => ∑ n ∈ Finset.range p.2, f (pt n p.1) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ => hf.comp (hpt n)
  exact hP.comp (measurable_id.prodMk hcnt)

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (n : ℕ) :
    IndepFun (fun ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
      (pieceSum K X f (n + 1)) μ := by
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
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType (ℝ × ℝ) (φ i)) → ℝ :=
    fun g => ∑ k : Fin (n + 1),
      ∑ n' ∈ Finset.range (g (Sum.inl k)), f (g (Sum.inr (k, n'))) with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType (ℝ × ℝ) (ψ j)) → ℝ :=
    fun g => ∑ n' ∈ Finset.range (g (Sum.inl ())), f (g (Sum.inr n')) with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact Finset.measurable_sum _ fun k _ =>
      measurable_pieceSumExtract (D := ∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ,
          pointFamilyIndexType (ℝ × ℝ) (φ i))
        hf (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H :=
    measurable_pieceSumExtract (D := ∀ j : Unit ⊕ ℕ, pointFamilyIndexType (ℝ × ℝ) (ψ j))
      hf (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
      (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω)
      = fun ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω := by
    funext ω
    simp only [hG_def]
    rw [← Fin.sum_univ_eq_sum_range (fun j => pieceSum K X f j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω) = pieceSum K X f (n + 1) := by
    funext ω; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rwa [hGeq, hHeq] at key
