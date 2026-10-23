-- Prove2me | solution 1 for RiskFunctionals.Duality.acceptabilityOfSet_properties
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:38:29.89678+00:00
-- url     : https://prove2.me/submissions/e7d3d1eb-7f8c-4ce1-9581-e3914f8c2939

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals

open MeasureTheory ProbabilityTheory RiskFunctionals.Duality Filter Topology

theorem g79s_nonatomic (G : Measure ℝ) [IsProbabilityMeasure G] (h0 : ∀ x : ℝ, G {x} = 0) :
    IsNonAtomic G := by
  rintro A ⟨hA, hpos, hat⟩
  have hfin : ∀ s, G s ≠ ⊤ := fun s => measure_ne_top G s
  -- values in {0, G A}
  have hval : ∀ t : ℝ, G (A ∩ Set.Iic t) = G A ∨ G (A ∩ Set.Iic t) = 0 :=
    fun t => hat _ Set.inter_subset_left (hA.inter measurableSet_Iic)
  set S : Set ℝ := {t | G (A ∩ Set.Iic t) = 0} with hS
  have hdown : ∀ t ∈ S, ∀ u ≤ t, u ∈ S := by
    intro t ht u hu
    exact measure_mono_null (Set.inter_subset_inter_right _ (Set.Iic_subset_Iic.mpr hu)) ht
  -- tends to 0 at -∞
  have hlim0 : Tendsto (fun n : ℕ => G (A ∩ Set.Iic (-(n:ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => G (A ∩ Set.Iic (-(n:ℝ)))) atTop
        (𝓝 (G (⋂ n : ℕ, A ∩ Set.Iic (-(n:ℝ))))) := by
      apply tendsto_measure_iInter_atTop
      · intro n; exact (hA.inter measurableSet_Iic).nullMeasurableSet
      · intro m n hmn
        apply Set.inter_subset_inter_right
        apply Set.Iic_subset_Iic.mpr
        have : (m:ℝ) ≤ n := by exact_mod_cast hmn
        linarith
      · exact ⟨0, hfin _⟩
    have h2 : (⋂ n : ℕ, A ∩ Set.Iic (-(n:ℝ))) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, fun h => by linarith [h.2]⟩
    rw [h2, measure_empty] at h1
    exact h1
  have hlim1 : Tendsto (fun n : ℕ => G (A ∩ Set.Iic (n:ℝ))) atTop (𝓝 (G A)) := by
    have h1 : Tendsto (fun n : ℕ => G (A ∩ Set.Iic (n:ℝ))) atTop
        (𝓝 (G (⋃ n : ℕ, A ∩ Set.Iic (n:ℝ)))) := by
      apply tendsto_measure_iUnion_atTop
      intro m n hmn
      apply Set.inter_subset_inter_right
      apply Set.Iic_subset_Iic.mpr
      exact_mod_cast hmn
    have h2 : (⋃ n : ℕ, A ∩ Set.Iic (n:ℝ)) = A := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iic]
      constructor
      · rintro ⟨n, h, -⟩; exact h
      · intro h; obtain ⟨n, hn⟩ := exists_nat_ge x; exact ⟨n, h, hn⟩
    rw [h2] at h1
    exact h1
  have hne : S.Nonempty := by
    have := hlim0.eventually (gt_mem_nhds hpos)
    obtain ⟨n, hn⟩ := this.exists
    refine ⟨-(n:ℝ), ?_⟩
    rcases hval (-(n:ℝ)) with h | h
    · rw [h] at hn; exact absurd hn (lt_irrefl _)
    · exact h
  have hbdd : BddAbove S := by
    have := hlim1.eventually (lt_mem_nhds hpos)
    obtain ⟨n, hn⟩ := this.exists
    refine ⟨n, fun t ht => ?_⟩
    by_contra hlt
    replace hlt := lt_of_not_ge hlt
    have := hdown t ht n hlt.le
    simp only [hS, Set.mem_setOf_eq] at this
    rw [this] at hn
    exact absurd hn (lt_irrefl _)
  set s := sSup S with hs
  -- left part null
  have hleft : G (A ∩ Set.Iio s) = 0 := by
    have hsub : A ∩ Set.Iio s ⊆ ⋃ n : ℕ, A ∩ Set.Iic (s - 1 / ((n:ℝ) + 1)) := by
      rintro x ⟨hx, hxs⟩
      have hxs' : 0 < s - x := by simp at hxs; linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hxs'
      exact Set.mem_iUnion.mpr ⟨n, hx, by simp only [Set.mem_Iic]; linarith⟩
    refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
    have hlt : s - 1 / ((n:ℝ) + 1) < s := by
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    obtain ⟨t, ht, hlt'⟩ := exists_lt_of_lt_csSup hne hlt
    exact hdown t ht _ hlt'.le
  have hright : G (A ∩ Set.Ioi s) = 0 := by
    have hsub : A ∩ Set.Ioi s ⊆ ⋃ n : ℕ, A \ Set.Iic (s + 1 / ((n:ℝ) + 1)) := by
      rintro x ⟨hx, hxs⟩
      have hxs' : 0 < x - s := by simp at hxs; linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hxs'
      exact Set.mem_iUnion.mpr ⟨n, hx, by simp only [Set.mem_Iic, not_le]; linarith⟩
    refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
    have hgt : s < s + 1 / ((n:ℝ) + 1) := by
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    have hnot : s + 1 / ((n:ℝ) + 1) ∉ S := fun h => absurd (le_csSup hbdd h) (not_le.mpr hgt)
    have hv : G (A ∩ Set.Iic (s + 1 / ((n:ℝ) + 1))) = G A := by
      rcases hval (s + 1 / ((n:ℝ) + 1)) with h | h
      · exact h
      · exact absurd h hnot
    have hd := measure_diff (μ := G) (s₁ := A) (s₂ := A ∩ Set.Iic (s + 1 / ((n:ℝ) + 1)))
      Set.inter_subset_left ((hA.inter measurableSet_Iic).nullMeasurableSet) (hfin _)
    rw [Set.diff_self_inter] at hd
    rw [hd, hv, tsub_self]
  have hcover : A ⊆ (A ∩ Set.Iio s) ∪ {s} ∪ (A ∩ Set.Ioi s) := by
    intro x hx
    rcases lt_trichotomy x s with h | h | h
    · exact Or.inl (Or.inl ⟨hx, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨hx, h⟩
  have : G A = 0 := measure_mono_null hcover
    (measure_union_null (measure_union_null hleft (h0 s)) hright)
  exact absurd this hpos.ne'

theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (S : Set (Lp ℝ p P)),
    (IsClosed S → UpperSemicontinuous (acceptabilityOfSet P S)) ∧
    TranslationEquivariant P (acceptabilityOfSet P S) ∧
    (_root_.Convex ℝ S → ConcaveFunctional (acceptabilityOfSet P S)) ∧
    (MonotoneSet P S → PointwiseMonotone P (acceptabilityOfSet P S)) ∧
    (IsConeSet S → PositivelyHomogeneous (acceptabilityOfSet P S)) ∧
    ((∀ Y ∈ S, 0 ≤ expectation Y) → Strict (acceptabilityOfSet P S))) := by
  intro h
  set G := gaussianReal 0 1 with hG
  have hac := gaussianReal_absolutelyContinuous 0 (v := 1) one_ne_zero
  have h0 : ∀ x : ℝ, G {x} = 0 := fun x => hac (Real.volume_singleton)
  haveI : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨-, -, -, -, hcone, -⟩ := h G (g79s_nonatomic G h0) 1 ENNReal.one_ne_top
    (∅ : Set (Lp ℝ 1 G))
  have hc : IsConeSet (∅ : Set (Lp ℝ 1 G)) := fun Y hY => absurd hY (Set.notMem_empty Y)
  have := hcone hc 0 0 le_rfl
  simp [acceptabilityOfSet] at this
