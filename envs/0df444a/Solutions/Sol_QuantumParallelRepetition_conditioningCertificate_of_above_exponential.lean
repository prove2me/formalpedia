-- Prove2me | solution 1 for QuantumParallelRepetition.conditioningCertificate_of_above_exponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T06:01:24.515453+00:00
-- url     : https://prove2.me/submissions/ed5031d5-e8ef-480d-b512-e9743854900b

/-
Reorganization of the existing quantum parallel repetition driver.
Supporting proofs adapted from OpenAI's ten-proofs, QuantumParallelRepetition.lean,
commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 (Apache-2.0), as published in
Prove2Me submission f7cea14e-2b4d-4d58-988d-602c87bbeb52.
The two stage boundaries and their composition are the new organization.
-/

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Theorems.Thm_QuantumParallelRepetition_entangledValue_nonneg
import Theorems.Thm_QuantumParallelRepetition_fullCoordinateAliceEntropyIncrement_nonneg
import Theorems.Thm_QuantumParallelRepetition_aliceMartingaleEntropyBudget
import Theorems.Thm_QuantumParallelRepetition_answerLogCost_nonneg_of_postselection

namespace QuantumParallelRepetition

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*}

namespace Game

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem marginalX_nonneg (G : Game X Y A B) (x : X) :
    0 ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.sum_nonneg fun y _ => G.weight_nonneg x y

theorem marginalY_nonneg (G : Game X Y A B) (y : Y) :
    0 ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.sum_nonneg fun x _ => G.weight_nonneg x y

@[simp] theorem repeat_predicate_eq_true (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (G.repeat n).predicate xs ys as bs = true ↔
      ∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true := by
  simp [«repeat»]

end Game

end

noncomputable section

open scoped BigOperators

namespace FiniteEventLaw

variable {Ω ι : Type*} [Fintype Ω]

theorem eventMass_univ (law : FiniteEventLaw Ω) :
    law.eventMass Finset.univ = 1 := by
  simpa [eventMass] using law.weight_sum

theorem eventMass_mono
    (law : FiniteEventLaw Ω) {s t : Finset Ω} (h : s ⊆ t) :
    law.eventMass s ≤ law.eventMass t := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun ω _ _ => law.weight_nonneg ω)

theorem winEvent_empty [Fintype ι] (wins : ι → Ω → Bool) :
    winEvent wins ∅ = Finset.univ := by
  classical
  simp [winEvent]

theorem winEvent_antitone [Fintype ι]
    (wins : ι → Ω → Bool) {D E : Finset ι} (h : D ⊆ E) :
    winEvent wins E ⊆ winEvent wins D := by
  classical
  intro ω hω
  have h_all : ∀ i ∈ E, wins i ω = true := by
    simpa [winEvent] using hω
  simp only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi => h_all i (h hi)

theorem allWinMass_le_partial [Fintype ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) :
    law.eventMass (winEvent wins Finset.univ) ≤
      law.eventMass (winEvent wins D) := by
  apply law.eventMass_mono
  exact winEvent_antitone wins (Finset.subset_univ D)

theorem exists_greedy_stopping [Fintype ι] [DecidableEq ι]
    (mass : Finset ι → ℝ) {θ η : ℝ} {T : ℕ}
    (_hθ : 0 < θ)
    (_hη : 0 < η)
    (hη_one : η ≤ 1)
    (hT : T ≤ Fintype.card ι)
    (hempty : mass ∅ = 1)
    (hfloor : ∀ D : Finset ι, θ ≤ mass D)
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset ι,
      D.card < T ∧
      θ ≤ mass D ∧
      (∑ i ∈ Finset.univ \ D,
        (mass D - mass (insert i D)))
        < ((Finset.univ \ D).card : ℝ) * (η * mass D) := by
  classical
  let candidates : Finset (Finset ι) :=
    Finset.univ.powerset.filter
      (fun D => D.card ≤ T ∧ mass D ≤ (1 - η) ^ D.card)
  have h_candidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, hempty]
  obtain ⟨D, hD, hmax⟩ :=
    Finset.exists_max_image candidates (fun E : Finset ι => E.card)
      h_candidates
  have hD_data : D.card ≤ T ∧ mass D ≤ (1 - η) ^ D.card :=
    (Finset.mem_filter.mp hD).2
  have hD_lt : D.card < T := by
    have hne : D.card ≠ T := by
      intro heq
      have hupper : mass D ≤ (1 - η) ^ T := by
        simpa [heq] using hD_data.2
      linarith [hfloor D]
    exact lt_of_le_of_ne hD_data.1 hne
  refine ⟨D, hD_lt, hfloor D, ?_⟩
  by_contra h_not_stopped
  have h_sum :
      ((Finset.univ \ D).card : ℝ) * (η * mass D)
        ≤ ∑ i ∈ Finset.univ \ D,
          (mass D - mass (insert i D)) :=
    le_of_not_gt h_not_stopped
  have h_card : D.card < (Finset.univ : Finset ι).card := by
    simpa using hD_lt.trans_le hT
  have h_remaining : (Finset.univ \ D).Nonempty :=
    Finset.sdiff_nonempty_of_card_lt_card h_card
  have h_sum_constant :
      (∑ _i ∈ Finset.univ \ D, η * mass D)
        ≤ ∑ i ∈ Finset.univ \ D,
          (mass D - mass (insert i D)) := by
    simpa using h_sum
  obtain ⟨i, hi, hfailure⟩ :=
    Finset.exists_le_of_sum_le h_remaining h_sum_constant
  have hi_not : i ∉ D := (Finset.mem_sdiff.mp hi).2
  have hnext_card : (insert i D).card ≤ T := by
    rw [Finset.card_insert_of_notMem hi_not]
    omega
  have hshrink :
      mass (insert i D) ≤ (1 - η) * mass D := by
    linarith
  have hnext_bound :
      mass (insert i D) ≤
        (1 - η) ^ (insert i D).card := by
    calc
      mass (insert i D) ≤ (1 - η) * mass D := hshrink
      _ ≤ (1 - η) * (1 - η) ^ D.card :=
        mul_le_mul_of_nonneg_left hD_data.2
          (sub_nonneg.mpr hη_one)
      _ = (1 - η) ^ (insert i D).card := by
        rw [Finset.card_insert_of_notMem hi_not, pow_succ]
        ring
  have hnext_mem : insert i D ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hnext_card, hnext_bound⟩
  have h_impossible := hmax (insert i D) hnext_mem
  rw [Finset.card_insert_of_notMem hi_not] at h_impossible
  omega

theorem exists_conditioned_win_set [Fintype ι] [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη : 0 < η)
    (hη_one : η ≤ 1)
    (hT : T ≤ Fintype.card ι)
    (hwin : θ ≤ law.eventMass (winEvent wins Finset.univ))
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset ι,
      D.card < T ∧
      θ ≤ law.eventMass (winEvent wins D) ∧
      (∑ i ∈ Finset.univ \ D, failureMass law wins D i)
        < ((Finset.univ \ D).card : ℝ) *
          (η * law.eventMass (winEvent wins D)) := by
  let mass : Finset ι → ℝ :=
    fun D => law.eventMass (winEvent wins D)
  have hempty : mass ∅ = 1 := by
    dsimp [mass]
    rw [winEvent_empty]
    exact law.eventMass_univ
  have hfloor : ∀ D : Finset ι, θ ≤ mass D := by
    intro D
    exact hwin.trans (law.allWinMass_le_partial wins D)
  obtain ⟨D, hD, hp, hstop⟩ :=
    exists_greedy_stopping mass hθ hη hη_one hT hempty hfloor
      h_terminal
  refine ⟨D, hD, hp, ?_⟩
  simpa [failureMass, mass] using hstop

end FiniteEventLaw

section StrategyEventLaw

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem strategyEventLaw_winEvent
    (G : Game X Y A B) (S : Strategy G) :
    (strategyEventLaw G S).eventMass (strategyWinEvent G) =
      S.winProbability := by
  classical
  unfold FiniteEventLaw.eventMass strategyWinEvent
  simp only [Finset.sum_filter]
  change
    (∑ ω : X × Y × A × B,
      if G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true
      then G.questionWeight ω.1 ω.2.1 *
        S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
      else 0) =
      S.winProbability
  simp_rw [Fintype.sum_prod_type]
  unfold Strategy.winProbability
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp

theorem repeated_allWinEvent_eq
    (G : Game X Y A B) (n : ℕ) :
    FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
      (Finset.univ : Finset (Fin n)) =
      strategyWinEvent (G.repeat n) := by
  classical
  ext ω
  simp [FiniteEventLaw.winEvent, strategyWinEvent,
    repeatedCoordinateWin, Game.repeat_predicate_eq_true]

theorem repeated_allWinMass_eq
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) :
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (Finset.univ : Finset (Fin n))) =
      S.winProbability := by
  rw [repeated_allWinEvent_eq]
  exact strategyEventLaw_winEvent (G.repeat n) S

theorem repeatedStrategy_exists_greedy_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {θ η : ℝ} {T : ℕ}
    (hθ : 0 < θ)
    (hη : 0 < η)
    (hη_one : η ≤ 1)
    (hT : T ≤ n)
    (hwin : θ ≤ S.winProbability)
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset (Fin n),
      D.card < T ∧
      θ ≤ (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) ∧
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i)
        <
      ((Finset.univ \ D).card : ℝ) *
        (η * (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D)) := by
  have h_card : T ≤ Fintype.card (Fin n) := by
    simpa using hT
  have h_full :
      θ ≤ (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n)
          (Finset.univ : Finset (Fin n))) := by
    rw [repeated_allWinMass_eq]
    exact hwin
  exact FiniteEventLaw.exists_conditioned_win_set
    (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n)
    hθ hη hη_one h_card h_full h_terminal

end StrategyEventLaw

end

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section CoordinateWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateBaseWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (h : FullCoordinateRevealHistory X Y n D L i) :
    0 ≤ fullCoordinateBaseWeight G D L i h := by
  unfold fullCoordinateBaseWeight
  exact mul_nonneg
    (mul_nonneg
      (Finset.prod_nonneg fun j _ =>
        G.weight_nonneg (h.aliceConditioned j) (h.bobConditioned j))
      (Finset.prod_nonneg fun j _ =>
        G.marginalX_nonneg (h.aliceRevealed j)))
    (Finset.prod_nonneg fun j _ => G.marginalY_nonneg (h.bobRemaining j))

end CoordinateWeights

end

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem fullCoordinateBaseWinIndicator_nonneg
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B) :
    0 ≤ fullCoordinateBaseWinIndicator G D L i r α β := by
  classical
  unfold fullCoordinateBaseWinIndicator
  split <;> norm_num

theorem fullCoordinateAliceTotalEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) (hiL : i ∉ L) :
    0 ≤ fullCoordinateAliceTotalEntropyIncrement G n S D L i := by
  unfold fullCoordinateAliceTotalEntropyIncrement
  exact Finset.sum_nonneg fun r _ =>
    Finset.sum_nonneg fun α _ =>
      Finset.sum_nonneg fun β _ =>
        mul_nonneg
          (mul_nonneg (fullCoordinateBaseWeight_nonneg G D L i r)
            (fullCoordinateBaseWinIndicator_nonneg G D L i r α β))
          (fullCoordinateAliceEntropyIncrement_nonneg
            G n S D L i hiD hiL r α β)

end

noncomputable section

open scoped BigOperators

@[simp] theorem sourceRemainingPermutationRank_coordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationRank D π
      (sourceRemainingPermutationCoordinateSubtype D π k) = k := by
  simp [sourceRemainingPermutationCoordinateSubtype]

theorem sourceRemainingPermutationCoordinate_not_mem
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationCoordinate D π k ∉ D := by
  have h := (sourceRemainingPermutationCoordinateSubtype D π k).property
  exact (Finset.mem_sdiff.mp h).2

theorem sourceRemainingPermutationCoordinate_not_mem_prefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationCoordinate D π k ∉
      sourceRemainingPermutationPrefix D π k.castSucc := by
  classical
  intro hmem
  obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hmem
  have heq : j = sourceRemainingPermutationCoordinateSubtype D π k := by
    apply Subtype.ext
    exact hval
  subst j
  have hlt := (Finset.mem_filter.mp hj).2
  simp [sourceRemainingPermutationRank_coordinate] at hlt

section ActualEntropyBudgets

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem sourcePermutationAliceEntropyIncrement_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    0 ≤ sourcePermutationAliceEntropyIncrement G n S D π k := by
  apply fullCoordinateAliceTotalEntropyIncrement_nonneg
  · exact sourceRemainingPermutationCoordinate_not_mem D π k
  · exact sourceRemainingPermutationCoordinate_not_mem_prefix D π k

theorem sourceUniformPermutationAverage_nonneg
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ)
    (hf : ∀ π k, 0 ≤ f π k) :
    0 ≤ sourceUniformPermutationAverage D f := by
  classical
  apply div_nonneg
  · exact Finset.sum_nonneg fun π _ =>
      Finset.sum_nonneg fun k _ => hf π k
  · exact mul_nonneg
      (Nat.cast_nonneg (Fintype.card (SourceRemainingPermutation D)))
      (Nat.cast_nonneg (Finset.univ \ D).card)

end ActualEntropyBudgets

end

noncomputable section

open scoped BigOperators

section FiniteSamples

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

theorem allWinMass_le_postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) :
    law.eventMass (FiniteEventLaw.winEvent wins Finset.univ) ≤
      postselectionMass law wins C :=
  law.allWinMass_le_partial wins C

theorem uniformRemainingFailure_lt_of_failure_sum
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) {η : ℝ}
    (hp : 0 < postselectionMass law wins C)
    (hm : 0 < (Finset.univ \ C).card)
    (hfailure :
      (∑ i ∈ Finset.univ \ C,
        FiniteEventLaw.failureMass law wins C i) <
        ((Finset.univ \ C).card : ℝ) *
          (η * postselectionMass law wins C)) :
    uniformRemainingFailure law wins C < η := by
  have hmreal : 0 < ((Finset.univ \ C).card : ℝ) := by
    exact_mod_cast hm
  unfold uniformRemainingFailure conditionalCoordinateFailure
  rw [← Finset.sum_div]
  apply (div_lt_iff₀ hmreal).mpr
  apply (div_lt_iff₀ hp).mpr
  nlinarith

end FiniteSamples

section ActualRepeatedStrategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem repeated_winProbability_le_postselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) :
    S.winProbability ≤ repeatedPostselectionMass G n S C := by
  rw [← repeated_allWinMass_eq G n S]
  exact allWinMass_le_postselectionMass
    (strategyEventLaw (G.repeat n) S) (repeatedCoordinateWin G n) C

theorem repeatedPostselectionMass_pos
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n))
    (hwin : 0 < S.winProbability) :
    0 < repeatedPostselectionMass G n S C :=
  lt_of_lt_of_le hwin
    (repeated_winProbability_le_postselectionMass G n S C)

theorem remainingCoordinates_card
    {n : ℕ} (C : Finset (Fin n)) :
    (Finset.univ \ C).card = n - C.card := by
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ C)]

theorem repeatedStrategy_exists_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} {q : ℕ}
    (hwin : 0 < S.winProbability)
    (hη : 0 < η) (hη_one : η ≤ 1)
    (hq : q ≤ n)
    (hterminal : (1 - η) ^ q < S.winProbability) :
    ∃ C : Finset (Fin n),
      C.card < q ∧
      S.winProbability ≤ repeatedPostselectionMass G n S C ∧
      0 < repeatedPostselectionMass G n S C ∧
      0 < (Finset.univ \ C).card ∧
      uniformRemainingFailure
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) C < η := by
  obtain ⟨C, hC, hmass, hfailure⟩ :=
    repeatedStrategy_exists_greedy_conditioning G n S
      hwin hη hη_one hq (le_refl _) hterminal
  have hremaining : 0 < (Finset.univ \ C).card := by
    rw [remainingCoordinates_card]
    omega
  have hp : 0 < repeatedPostselectionMass G n S C :=
    repeatedPostselectionMass_pos G n S C hwin
  refine ⟨C, hC, ?_, hp, hremaining, ?_⟩
  · simpa [repeatedPostselectionMass, postselectionMass] using hmass
  · apply uniformRemainingFailure_lt_of_failure_sum
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) C
      (by simpa [repeatedPostselectionMass] using hp)
      hremaining
    simpa [postselectionMass] using hfailure

end ActualRepeatedStrategy

end

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem martingaleRate_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card)
    (hp : 0 < repeatedPostselectionMass G n S D) :
    0 ≤ martingaleRate G n S D := by
  have hnonnegative := sourceUniformPermutationAverage_nonneg D
    (sourcePermutationAliceEntropyIncrement G n S D)
    (fun π k => sourcePermutationAliceEntropyIncrement_nonneg
      G n S D π k)
  have hbudget := aliceMartingaleEntropyBudget
    G n S D hm hp
  nlinarith

end

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactSourceClassicalInformationRate_le_three_martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactSourceClassicalInformationRate G n S D ≤
      3 * martingaleRate G n S D := by
  have answer_nonnegative :=
    answerLogCost_nonneg_of_postselection
      G n S D positive
  unfold exactSourceClassicalInformationRate
    martingaleRate
  have denominator_nonnegative :
      0 ≤ ((Finset.univ \ D).card : ℝ) := by positivity
  by_cases denominator_zero : ((Finset.univ \ D).card : ℝ) = 0
  · simp [denominator_zero]
  have denominator_positive :
      0 < ((Finset.univ \ D).card : ℝ) :=
    lt_of_le_of_ne denominator_nonnegative (Ne.symm denominator_zero)
  apply (div_le_iff₀ denominator_positive).2
  field_simp
  linarith

end

noncomputable section

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem pdfGreedyCeilingHorizon_le
    (n : ℕ) (τ d : ℝ)
    (threshold : 0 < τ)
    (small : d ≤ τ / 2) :
    ⌈d * (n : ℝ) / τ⌉₊ ≤ n := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ threshold).mpr
  have actual := mul_le_mul_of_nonneg_right small
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem pdfGreedyCeilingHorizon_pow_le_exp
    (n : ℕ) (τ d : ℝ)
    (threshold : 0 < τ)
    (at_most_one : τ ≤ 1) :
    (1 - τ) ^ ⌈d * (n : ℝ) / τ⌉₊ ≤
      Real.exp (-d * (n : ℝ)) := by
  let T : ℕ := ⌈d * (n : ℝ) / τ⌉₊
  have base_nonnegative : 0 ≤ 1 - τ := sub_nonneg.mpr at_most_one
  have base_le : 1 - τ ≤ Real.exp (-τ) := by
    have actual := Real.add_one_le_exp (-τ)
    linarith
  have ceiling : d * (n : ℝ) / τ ≤ (T : ℝ) := by
    exact Nat.le_ceil (d * (n : ℝ) / τ)
  have exponent : -τ * (T : ℝ) ≤ -d * (n : ℝ) := by
    have cleared := (div_le_iff₀ threshold).mp ceiling
    nlinarith
  change (1 - τ) ^ T ≤ Real.exp (-d * (n : ℝ))
  calc
    (1 - τ) ^ T ≤ Real.exp (-τ) ^ T := by
      exact pow_le_pow_left₀ base_nonnegative base_le T
    _ = Real.exp (-τ * (T : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-d * (n : ℝ)) := Real.exp_le_exp.mpr exponent

theorem pdfGreedyCard_lt_of_ceil
    (k n : ℕ) (τ d : ℝ)
    (below : k < ⌈d * (n : ℝ) / τ⌉₊) :
    (k : ℝ) < d * (n : ℝ) / τ :=
  Nat.lt_ceil.mp below

theorem pdfQuantitativeGreedyConditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (τ d θ : ℝ)
    (_n_positive : 0 < n)
    (threshold : 0 < τ)
    (threshold_lt_one : τ < 1)
    (_rate_positive : 0 < d)
    (rate_small : d ≤ τ / 2)
    (above_exponential : Real.exp (-d * (n : ℝ)) < θ)
    (realized : θ ≤ S.winProbability) :
    ∃ D : Finset (Fin n),
      (D.card : ℝ) < d * (n : ℝ) / τ ∧
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ) ∧
      θ ≤ repeatedPostselectionMass G n S D ∧
      S.winProbability ≤ repeatedPostselectionMass G n S D ∧
      0 < repeatedPostselectionMass G n S D ∧
      0 < (Finset.univ \ D).card ∧
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < τ := by
  let T : ℕ := ⌈d * (n : ℝ) / τ⌉₊
  have winning : 0 < S.winProbability :=
    lt_of_lt_of_le ((Real.exp_pos _).trans above_exponential) realized
  have legal : T ≤ n :=
    pdfGreedyCeilingHorizon_le n τ d threshold rate_small
  have terminal : (1 - τ) ^ T < S.winProbability :=
    lt_of_le_of_lt
      (pdfGreedyCeilingHorizon_pow_le_exp
        n τ d threshold threshold_lt_one.le)
      (above_exponential.trans_le realized)
  obtain ⟨D, selected, floor, positive, remaining, failure⟩ :=
    repeatedStrategy_exists_conditioning G n S
      winning threshold threshold_lt_one.le legal terminal
  have strict_card : (D.card : ℝ) < d * (n : ℝ) / τ :=
    pdfGreedyCard_lt_of_ceil D.card n τ d selected
  have half_rate : d * (n : ℝ) / τ ≤ (n : ℝ) / 2 := by
    apply (div_le_iff₀ threshold).mpr
    have actual := mul_le_mul_of_nonneg_right rate_small
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  have selected_le : D.card ≤ n := by
    have actual := Finset.card_le_card (Finset.subset_univ D)
    simpa using actual
  have remaining_real :
      ((Finset.univ \ D).card : ℝ) =
        (n : ℝ) - (D.card : ℝ) := by
    rw [remainingCoordinates_card, Nat.cast_sub selected_le]
  have more_than_half :
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ) := by
    rw [remaining_real]
    nlinarith
  exact ⟨D, strict_card, more_than_half,
    realized.trans floor, floor, positive, remaining, failure⟩

end

noncomputable section

theorem pdfUniversalRate_pos
    {B : ℝ} (positive : 0 < B) :
    0 < pdfUniversalRate B := by
  unfold pdfUniversalRate
  positivity

theorem pdfGapRate_pos
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    0 < pdfGapRate B ε ell := by
  unfold pdfGapRate
  have universal := pdfUniversalRate_pos constant
  positivity

theorem pdfGapRate_eq_scaled_twelfth_power
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell =
      ε / (8 * (ε + ell)) * (ε / (4 * B)) ^ 12 := by
  have nonzero : B ≠ 0 := ne_of_gt constant
  have denominator : ε + ell ≠ 0 := ne_of_gt (by linarith)
  unfold pdfGapRate pdfUniversalRate
  field_simp

theorem pdfGapBase_le_gap
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) :
    0 < ε / (4 * B) ∧ ε / (4 * B) ≤ ε := by
  have denominator : 0 < 4 * B := by nlinarith
  constructor
  · exact div_pos gap denominator
  · apply (div_le_iff₀ denominator).2
    nlinarith

theorem pdfGapBase_twelfth_le_gap
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ ε := by
  obtain ⟨nonnegative, bounded⟩ :=
    pdfGapBase_le_gap constant gap
  calc
    (ε / (4 * B)) ^ 12 ≤ ε ^ 12 :=
      pow_le_pow_left₀ nonnegative.le bounded 12
    _ = ε * ε ^ 11 := by ring
    _ ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ gap.le unit) gap.le
    _ = ε := by ring

theorem pdfGapRate_le_gap_div_eight
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell ≤ ε / 8 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  have denominator : 0 < ε + ell := by linarith
  have fraction : ε / (ε + ell) ≤ 1 := by
    apply (div_le_iff₀ denominator).2
    linarith
  have root := pdfGapBase_twelfth_le_gap constant gap unit
  rw [pdfGapRate_eq_scaled_twelfth_power
    Bpositive gap alphabet]
  have nonnegative : 0 ≤ (ε / (4 * B)) ^ 12 := by positivity
  calc
    ε / (8 * (ε + ell)) * (ε / (4 * B)) ^ 12 =
        (ε / (ε + ell)) * (ε / (4 * B)) ^ 12 / 8 := by
          field_simp [ne_of_gt denominator, ne_of_gt Bpositive]
    _ ≤ 1 * ε / 8 := by
          gcongr
    _ = ε / 8 := by ring

theorem pdfConditioningTolerance_bounds
    {ε : ℝ} (gap : 0 < ε) (unit : ε ≤ 1) :
    0 < pdfConditioningTolerance ε ∧
      pdfConditioningTolerance ε ≤ 1 / 4 := by
  unfold pdfConditioningTolerance
  constructor <;> nlinarith

theorem pdfGapRate_le_half_conditioningTolerance
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell) :
    pdfGapRate B ε ell ≤
      pdfConditioningTolerance ε / 2 := by
  have exact_rate := pdfGapRate_le_gap_div_eight
    constant gap unit alphabet
  calc
    pdfGapRate B ε ell ≤ ε / 8 := exact_rate
    _ = pdfConditioningTolerance ε / 2 := by
      unfold pdfConditioningTolerance
      ring

theorem pdfGapRate_entropy_factor
    {B ε ell : ℝ}
    (constant : 0 < B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) =
      (ε / (4 * B)) ^ 12 *
        ((ε + 4 * ell) / (4 * (ε + ell))) := by
  have nonzero : B ≠ 0 := ne_of_gt constant
  have gap_nonzero : ε ≠ 0 := ne_of_gt gap
  have denominator : ε + ell ≠ 0 := ne_of_gt (by linarith)
  rw [pdfGapRate_eq_scaled_twelfth_power
    constant gap alphabet]
  field_simp
  ring

theorem pdfAlphabetEntropyFactor_le_one
    {ε ell : ℝ} (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    (ε + 4 * ell) / (4 * (ε + ell)) ≤ 1 := by
  have denominator : 0 < 4 * (ε + ell) := by positivity
  apply (div_le_iff₀ denominator).2
  nlinarith

theorem pdfGapRate_entropy_le_twelfth_power
    {B ε ell : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (alphabet : 0 ≤ ell) :
    2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) ≤
      (ε / (4 * B)) ^ 12 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  rw [pdfGapRate_entropy_factor Bpositive gap alphabet]
  have nonnegative : 0 ≤ (ε / (4 * B)) ^ 12 := by positivity
  calc
    (ε / (4 * B)) ^ 12 *
        ((ε + 4 * ell) / (4 * (ε + ell))) ≤
        (ε / (4 * B)) ^ 12 * 1 :=
          mul_le_mul_of_nonneg_left
            (pdfAlphabetEntropyFactor_le_one gap alphabet)
            nonnegative
    _ = _ := by ring

theorem pdfQuantitativeEntropyRate_lt
    {n m k : ℕ} {t d τ ell : ℝ}
    (length : 0 < n) (rate : 0 < d) (tolerance : 0 < τ)
    (alphabet : 0 ≤ ell)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection : t < d * (n : ℝ))
    (conditioned : (k : ℝ) < d * (n : ℝ) / τ) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      2 * d * (1 + ell / τ) := by
  have length_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast length
  have mpositive : (0 : ℝ) < (m : ℝ) := by nlinarith
  have ratio_nonnegative : 0 ≤ ell / τ :=
    div_nonneg alphabet tolerance.le
  have factor : 0 < d * (1 + ell / τ) := by
    exact mul_pos rate (by linarith)
  have alphabet_bound :
      (k : ℝ) * ell ≤ (d * (n : ℝ) / τ) * ell :=
    mul_le_mul_of_nonneg_right (le_of_lt conditioned) alphabet
  have numerator :
      t + (k : ℝ) * ell < d * (n : ℝ) * (1 + ell / τ) := by
    calc
      t + (k : ℝ) * ell <
          d * (n : ℝ) + (d * (n : ℝ) / τ) * ell :=
        add_lt_add_of_lt_of_le postselection alphabet_bound
      _ = d * (n : ℝ) * (1 + ell / τ) := by ring
  apply (div_lt_iff₀ mpositive).2
  have horizon : (n : ℝ) < 2 * (m : ℝ) := by nlinarith
  have scaled := mul_lt_mul_of_pos_left horizon factor
  nlinarith

theorem pdfQuantitativeEntropyRate_lt_twelfth_power
    {B ε ell : ℝ} {n m k : ℕ} {t : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (unit : ε ≤ 1) (alphabet : 0 ≤ ell)
    (length : 0 < n)
    (remaining : (n : ℝ) / 2 < (m : ℝ))
    (postselection :
      t < pdfGapRate B ε ell * (n : ℝ))
    (conditioned :
      (k : ℝ) <
        pdfGapRate B ε ell * (n : ℝ) /
          pdfConditioningTolerance ε) :
    (t + (k : ℝ) * ell) / (m : ℝ) <
      (ε / (4 * B)) ^ 12 := by
  have Bpositive : 0 < B := lt_of_lt_of_le (by norm_num) constant
  have dpositive := pdfGapRate_pos Bpositive gap alphabet
  have taupositive : 0 < pdfConditioningTolerance ε :=
    (pdfConditioningTolerance_bounds gap unit).1
  have entropy := pdfQuantitativeEntropyRate_lt
    length dpositive taupositive alphabet remaining
    postselection conditioned
  have rewrite :
      2 * pdfGapRate B ε ell *
          (1 + ell / pdfConditioningTolerance ε) =
        2 * pdfGapRate B ε ell * (1 + 4 * ell / ε) := by
    unfold pdfConditioningTolerance
    have nonzero : ε ≠ 0 := ne_of_gt gap
    field_simp
  rw [rewrite] at entropy
  exact lt_of_lt_of_le entropy
    (pdfGapRate_entropy_le_twelfth_power
      constant gap alphabet)

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem pdfUniversalErrorCeiling_pos
    {K : ℝ} (constant : 1 ≤ K) :
    0 < universalErrorCeiling K := by
  have nonnegative : 0 ≤ K := by linarith
  unfold universalErrorCeiling
  positivity

theorem pdfRoundingCoefficient_two_le
    {K : ℝ} (constant : 1 ≤ K) :
    2 ≤ pdfRoundingCoefficient K := by
  have nonnegative : 0 ≤ K := by linarith
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K :=
    (pdfUniversalErrorCeiling_pos constant).le
  have first_nonnegative :
      0 ≤ (5 + 2 * universalErrorCeiling K) *
        Real.sqrt (3 / 2 : ℝ) := by positivity
  have quantum_nonnegative :
      0 ≤ 2 * K * (32 : ℝ) ^ (1 / 12 : ℝ) := by positivity
  have eight : 1 ≤ Real.sqrt (8 : ℝ) :=
    Real.one_le_sqrt.mpr (by norm_num)
  unfold pdfRoundingCoefficient
  nlinarith

theorem pdfRoundingCoefficient_one_le
    {K : ℝ} (constant : 1 ≤ K) :
    1 ≤ pdfRoundingCoefficient K := by
  have lower := pdfRoundingCoefficient_two_le constant
  linarith

end

noncomputable section

theorem pdfAlphabetEntropy_nonneg
    {A B : Type} [Fintype A] [Fintype B]
    (alice : Nonempty A) (bob : Nonempty B) :
    0 ≤ Real.log
      ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)) := by
  have alice_card : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr alice
  have bob_card : 0 < Fintype.card B :=
    Fintype.card_pos_iff.mpr bob
  have alice_real : (1 : ℝ) ≤ (Fintype.card A : ℝ) := by
    exact_mod_cast alice_card
  have bob_real : (1 : ℝ) ≤ (Fintype.card B : ℝ) := by
    exact_mod_cast bob_card
  apply Real.log_nonneg
  nlinarith [mul_nonneg (sub_nonneg.mpr alice_real)
    (sub_nonneg.mpr bob_real)]

theorem pdfGap_le_one
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    1 - entangledValue G ≤ 1 := by
  have nonnegative := entangledValue_nonneg G
  linarith

theorem pdfPostselectionLogCost_lt_of_exponential
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (d : ℝ)
    (above : Real.exp (-d * (n : ℝ)) <
      repeatedPostselectionMass G n S D) :
    postselectionLogCost G n S D < d * (n : ℝ) := by
  have logarithm := Real.log_lt_log (Real.exp_pos (-d * (n : ℝ))) above
  rw [Real.log_exp] at logarithm
  unfold postselectionLogCost
  rw [one_div, Real.log_inv]
  linarith

theorem pdfPinskerRate_le_sqrt_martingaleRate
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactSourcePinskerRate G n S D ≤
      Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D) := by
  unfold exactSourcePinskerRate
  apply Real.sqrt_le_sqrt
  have information :=
    exactSourceClassicalInformationRate_le_three_martingaleRate
      G n S D positive
  nlinarith

theorem pdfActualMartingaleRate_lt_twelfth_power
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (Bqs ε ell : ℝ)
    (constant : 1 ≤ Bqs)
    (gap : 0 < ε)
    (unit : ε ≤ 1)
    (alphabet : 0 ≤ ell)
    (alphabet_eq : ell =
      Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))
    (length : 0 < n)
    (remaining :
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ))
    (above :
      Real.exp
        (-pdfGapRate Bqs ε ell * (n : ℝ)) <
        repeatedPostselectionMass G n S D)
    (conditioned :
      (D.card : ℝ) <
        pdfGapRate Bqs ε ell * (n : ℝ) /
          pdfConditioningTolerance ε) :
    martingaleRate G n S D < (ε / (4 * Bqs)) ^ 12 := by
  have postselection :=
    pdfPostselectionLogCost_lt_of_exponential
      G n S D (pdfGapRate Bqs ε ell) above
  have actual := pdfQuantitativeEntropyRate_lt_twelfth_power
    constant gap unit alphabet length remaining postselection conditioned
  simpa [martingaleRate, answerLogCost, alphabet_eq]
    using actual

end

end QuantumParallelRepetition

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


theorem solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (K : ℝ) (constant : 1 ≤ K)
    (alice : Nonempty A) (bob : Nonempty B)
    (gap : 0 < 1 - entangledValue G) (length : 0 < n)
    (winning :
      Real.exp
        (-pdfGapRate (pdfRoundingCoefficient K) (1 - entangledValue G)
          (Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))) * (n : ℝ)) <
        S.winProbability) :
    ∃ D : Finset (Fin n),
      0 < (Finset.univ \ D).card ∧
      0 < repeatedPostselectionMass G n S D ∧
      uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D < (1 - entangledValue G) / 2 ∧
      0 ≤ martingaleRate G n S D ∧
      martingaleRate G n S D <
        ((1 - entangledValue G) / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ) ∧
      exactSourcePinskerRate G n S D ≤
        Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D) := by
  let ε : ℝ := 1 - entangledValue G
  let ell : ℝ := Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))
  let Bqs : ℝ := pdfRoundingCoefficient K
  let d : ℝ := pdfGapRate Bqs ε ell
  let τ : ℝ := pdfConditioningTolerance ε
  have coefficient : 1 ≤ Bqs := pdfRoundingCoefficient_one_le constant
  have unit : ε ≤ 1 := pdfGap_le_one G
  have alphabet : 0 ≤ ell := pdfAlphabetEntropy_nonneg alice bob
  have tolerance := pdfConditioningTolerance_bounds gap unit
  have tolerance_positive : 0 < τ := tolerance.1
  have tolerance_lt_one : τ < 1 := by
    have at_most := tolerance.2
    dsimp [τ]
    linarith
  have rate_positive : 0 < d := pdfGapRate_pos (by linarith) gap alphabet
  have rate_small : d ≤ τ / 2 :=
    pdfGapRate_le_half_conditioningTolerance coefficient gap unit alphabet
  obtain ⟨D, selected, remaining_real, postselection_floor,
      _strategy_floor, positive, remaining, failure⟩ :=
    pdfQuantitativeGreedyConditioning G n S τ d S.winProbability length
      tolerance_positive tolerance_lt_one rate_positive rate_small winning (le_refl _)
  have above : Real.exp (-d * (n : ℝ)) < repeatedPostselectionMass G n S D :=
    winning.trans_le postselection_floor
  have small : martingaleRate G n S D < (ε / (4 * Bqs)) ^ (12 : ℕ) := by
    exact pdfActualMartingaleRate_lt_twelfth_power G n S D Bqs ε ell
      coefficient gap unit alphabet rfl length remaining_real above selected
  have source_failure :
      uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D < ε / 2 := by
    have actual :
        uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < ε / 4 := by
      simpa [τ, pdfConditioningTolerance] using failure
    linarith
  exact ⟨D, remaining, positive, source_failure,
    martingaleRate_nonneg G n S D remaining positive, small,
    pdfPinskerRate_le_sqrt_martingaleRate G n S D positive⟩
