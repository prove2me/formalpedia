-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P50.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:08:51.728809+00:00
-- url     : https://prove2.me/submissions/dc668964-7e65-41dd-ac5f-747c5ac1d1f8

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50
noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set



attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Bridge50.P50

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)






theorem solution {X : Type*} [MetricSpace X]
    (Theta : ℕ → Set X) (hc : ∀ n, IsCompact (Theta n)) (hn : Antitone Theta)
    (hi : (⋂ n, Theta n).Nonempty) (f : Theta 0 → ℝ) (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Tendsto (fun n => restrictedInf Theta f (Theta n)) atTop
      (𝓝 (restrictedInf Theta f (⋂ n, Theta n))) := by
  obtain ⟨C, hC⟩ := hb
  obtain ⟨x0, hx0⟩ := hi
  have hx0n : ∀ n, x0 ∈ Theta n := Set.mem_iInter.mp hx0
  have hsub : ∀ n, Theta n ⊆ Theta 0 := fun n => hn (Nat.zero_le n)
  let p0 : Theta 0 := ⟨x0, hx0n 0⟩
  have hbdd : ∀ A : Set X, BddBelow {r | ∃ x : Theta 0, x.val ∈ A ∧ r = f x} := by
    intro A
    refine ⟨-C, ?_⟩
    rintro r ⟨x, -, rfl⟩
    have := hC x; rw [abs_le] at this; linarith
  have hne : ∀ A : Set X, x0 ∈ A → {r | ∃ x : Theta 0, x.val ∈ A ∧ r = f x}.Nonempty :=
    fun A hA => ⟨f p0, p0, hA, rfl⟩
  set m := restrictedInf Theta f (⋂ n, Theta n) with hm
  set a := fun n => restrictedInf Theta f (Theta n) with ha
  have hmono : Monotone a := by
    intro i j hij
    show restrictedInf Theta f (Theta i) ≤ restrictedInf Theta f (Theta j)
    unfold restrictedInf
    apply csInf_le_csInf (hbdd (Theta i)) (hne _ (hx0n j))
    rintro r ⟨x, hx, rfl⟩
    exact ⟨x, hn hij hx, rfl⟩
  have hle : ∀ n, a n ≤ m := by
    intro n
    show restrictedInf Theta f (Theta n) ≤ restrictedInf Theta f (⋂ n, Theta n)
    unfold restrictedInf
    apply csInf_le_csInf (hbdd (Theta n)) (hne _ hx0)
    rintro r ⟨x, hx, rfl⟩
    exact ⟨x, Set.mem_iInter.mp hx n, rfl⟩
  have hsup : ∀ ε > 0, ∃ n, m - ε < a n := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    haveI : CompactSpace (Theta 0) := isCompact_iff_compactSpace.mp (hc 0)
    let K : ℕ → Set (Theta 0) := fun n => {x | x.val ∈ Theta n ∧ f x ≤ m - ε / 2}
    have hKne : ∀ n, (K n).Nonempty := by
      intro n
      have h1 : sInf {r | ∃ x : Theta 0, x.val ∈ Theta n ∧ r = f x} < m - ε / 2 := by
        have := hcon n; simp only [ha, restrictedInf] at this; linarith
      obtain ⟨r, ⟨x, hx, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (hne _ (hx0n n)) h1
      exact ⟨x, hx, hr.le⟩
    have hKcl : ∀ n, IsClosed (K n) := by
      intro n
      apply IsClosed.inter
      · exact (hc n).isClosed.preimage continuous_subtype_val
      · exact isClosed_le hf continuous_const
    have hKanti : ∀ n, K (n + 1) ⊆ K n := by
      intro n x hx
      exact ⟨hn (Nat.le_succ n) hx.1, hx.2⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKanti
      hKne ((hKcl 0).isCompact) hKcl
    rw [Set.mem_iInter] at hx
    have hxI : x.val ∈ ⋂ n, Theta n := Set.mem_iInter.mpr (fun n => (hx n).1)
    have : m ≤ f x := csInf_le (hbdd _) ⟨x, hxI, rfl⟩
    have := (hx 0).2
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hsup ε hε
  refine ⟨N, fun n hn' => ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hmono hn']
  · linarith [hle n]
