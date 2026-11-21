-- Prove2me | solution 1 for SuperPareto.step_d_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:41:08.305867+00:00
-- url     : https://prove2.me/submissions/c735a163-a09e-4b26-835d-7c600558cd29

import Mathlib

open MeasureTheory

theorem solution {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι] (θ : ι → ℝ)
    (hθ : θ ∈ stdSimplex ℝ ι) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (A₀ : Set Ω) (hA₀ : P.real A₀ = ∑ i, θ i * P.real (A i)) :
    (∀ S : Finset ι, 0 ≤ ∑ i ∈ S, θ i ∧ ∑ i ∈ S, θ i ≤ 1) ∧
      ∑ S : Finset ι, P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) * (∑ i ∈ S, θ i) =
        ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S),
          P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) ∧
      ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S),
          P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) =
        ∑ j, θ j * P.real (A j) ∧
      ∑ j, θ j * P.real (A j) = P.real A₀ := by
  -- the atoms `B S`
  let B : Finset ι → Set Ω := fun S => (⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)
  change (∀ S : Finset ι, 0 ≤ ∑ i ∈ S, θ i ∧ ∑ i ∈ S, θ i ≤ 1) ∧
      ∑ S : Finset ι, P.real (B S) * (∑ i ∈ S, θ i) =
        ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S), P.real (B S) ∧
      ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S), P.real (B S) =
        ∑ j, θ j * P.real (A j) ∧
      ∑ j, θ j * P.real (A j) = P.real A₀
  classical
  -- part 1: subset sums of the simplex weights lie in `[0,1]`
  have hpart1 : ∀ S : Finset ι, 0 ≤ ∑ i ∈ S, θ i ∧ ∑ i ∈ S, θ i ≤ 1 := by
    intro S
    simp only [stdSimplex, Set.mem_ofPred_eq] at hθ
    constructor
    · exact Finset.sum_nonneg (fun i _ => hθ.1 i)
    · calc ∑ i ∈ S, θ i ≤ ∑ i, θ i := Finset.sum_le_univ_sum_of_nonneg (fun i => hθ.1 i)
        _ = 1 := hθ.2
  -- pointwise description of the atoms
  have hBmem : ∀ (S : Finset ι) (ω : Ω), ω ∈ B S ↔ ∀ i, (ω ∈ A i ↔ i ∈ S) := by
    intro S ω
    simp only [B, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ S
      · exact ⟨fun _ => hi, fun _ => h1 i hi⟩
      · exact ⟨fun h => absurd h (h2 i hi), fun h => absurd h hi⟩
    · intro h
      exact ⟨fun i hi => (h i).mpr hi, fun i hi hc => hi ((h i).mp hc)⟩
  -- the atoms are measurable
  have hBmeas : ∀ S : Finset ι, MeasurableSet (B S) := by
    intro S
    have h1 : MeasurableSet (⋂ i ∈ S, A i) := Finset.measurableSet_biInter S (fun i _ => hA i)
    have h2 : MeasurableSet (⋂ (i) (_ : i ∉ S), (A i)ᶜ) := by
      have h := Finset.measurableSet_biInter (Sᶜ) (fun i _ => (hA i).compl)
      simpa [Finset.mem_compl] using h
    exact MeasurableSet.inter h1 h2
  -- distinct atoms are disjoint
  have hdisj : ∀ S T : Finset ι, S ≠ T → Disjoint (B S) (B T) := by
    intro S T hST
    rw [Set.disjoint_left]
    intro ω hS hT
    apply hST
    ext i
    exact ((hBmem S ω).mp hS i).symm.trans ((hBmem T ω).mp hT i)
  -- the atoms indexed by sets containing `j` partition `A j`
  have hUnion : ∀ j : ι, (⋃ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S), B S) = A j := by
    intro j
    ext ω
    constructor
    · intro hω
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hω
      obtain ⟨S, hjS, hωS⟩ := hω
      exact ((hBmem S ω).mp hωS j).mpr hjS
    · intro hω
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Finset.univ.filter (fun i => ω ∈ A i), ?_, ?_⟩
      · simpa using hω
      · exact (hBmem _ ω).mpr (fun i => by simp)
  -- the measure of the corresponding finite union
  have hsum_measure : ∀ j : ι,
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S), P.real (B S) = P.real (A j) := by
    intro j
    rw [← hUnion j]
    refine (measureReal_biUnion_finset (s := Finset.univ.filter (fun S : Finset ι => j ∈ S))
      (f := B) ?_ ?_ (fun b _ => measure_ne_top P (B b))).symm
    · intro a _ b _ hab
      exact hdisj a b hab
    · intro b _
      exact hBmeas b
  -- part 2: exchange the two sums
  have hpart2 : ∑ S : Finset ι, P.real (B S) * (∑ i ∈ S, θ i) =
      ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S), P.real (B S) := by
    calc ∑ S : Finset ι, P.real (B S) * (∑ i ∈ S, θ i)
        = ∑ S : Finset ι, ∑ i : ι, if i ∈ S then P.real (B S) * θ i else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.mul_sum, ← Finset.sum_filter]
          apply Finset.sum_congr
          · ext i
            simp
          · intro i _
            rfl
      _ = ∑ i : ι, ∑ S : Finset ι, if i ∈ S then P.real (B S) * θ i else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            P.real (B S) * θ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_filter]
      _ = ∑ i : ι, θ i * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => i ∈ S),
            P.real (B S) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          exact mul_comm _ _
  -- part 3: the inner sums are the probabilities of the `A j`
  have hpart3 : ∑ j, θ j * ∑ S ∈ Finset.univ.filter (fun S : Finset ι => j ∈ S), P.real (B S) =
      ∑ j, θ j * P.real (A j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hsum_measure j]
  exact ⟨hpart1, hpart2, hpart3, hA₀.symm⟩
