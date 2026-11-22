-- Prove2me | solution 1 for ZhangYeung.shannonCone_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:56:02.752655+00:00
-- url     : https://prove2.me/submissions/d167ab5f-0abf-4fde-8fca-d3429a18d498

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_EntropyRegion
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem3
public import Definitions.Def_LeanPool_ZhangYeungInequality_Theorem4
public import Theorems.Thm_ZhangYeung_FWitness_eq_cast
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq


section
@[expose] public section
namespace ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
private lemma fullBonus_nonneg (S : Finset (Fin 4)) : 0 ≤ fullBonus S := by
  by_cases h : S = Finset.univ <;> simp [fullBonus, h]
private lemma FWitnessℚ_eq_base_add_pair :
    ∀ S : Finset (Fin 4), FWitnessℚ S = baseWitness S + pairBonus S := by
  intro S
  by_cases h0 : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp h0
    subst hEmpty
    have hFull : (∅ : Finset (Fin 4)) ≠ Finset.univ := by decide
    have hPairLit : (∅ : Finset (Fin 4)) ≠ ({0, 1} : Finset (Fin 4)) := by decide
    simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, pair01, hFull, hPairLit]
  · by_cases h1 : S.card = 1
    · have hPair : S ≠ pair01 := by
        intro h
        rw [h, pair01] at h1
        norm_num at h1
      have hFull : S ≠ Finset.univ := by
        intro h
        simp_all
      have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
      simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, h1, hPair, hFull,
        hNonempty]
      norm_num
    · by_cases hPair : S = pair01
      · subst hPair
        have hFullLit : ({0, 1} : Finset (Fin 4)) ≠ Finset.univ := by decide
        simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, pair01, hFullLit]
        norm_num
      · by_cases h2 : S.card = 2
        · have hFull : S ≠ Finset.univ := by
            intro h
            simp_all
          have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
          have hPairLit : S ≠ ({0, 1} : Finset (Fin 4)) := by simpa [pair01] using hPair
          simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, h2, hPair,
            hPairLit, hFull, hNonempty]
          norm_num
        · have hCardLe : S.card ≤ 4 := by simpa using Finset.card_le_univ S
          have h34 : S.card = 3 ∨ S.card = 4 := by omega
          cases h34 with
          | inl h3 =>
              have hFull : S ≠ Finset.univ := by
                intro h
                simp_all
              have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
              have hPairLit : S ≠ ({0, 1} : Finset (Fin 4)) := by simpa [pair01] using hPair
              simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, h3, hPair,
                hPairLit, hFull, hNonempty]
              norm_num
          | inr h4 =>
              have hFull : S = Finset.univ := by
                exact S.card_eq_iff_eq_univ.mp (by simpa using h4)
              have hPairUniv : (Finset.univ : Finset (Fin 4)) ≠ pair01 := by decide
              have hPairUnivLit : (Finset.univ : Finset (Fin 4)) ≠ ({0,
                1} : Finset (Fin 4)) := by decide
              have hNonempty : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
              simp [FWitnessℚ, baseWitness, nonemptyBonus, fullBonus, pairBonus, hFull,
                hPairUniv, hPairUnivLit]
private lemma card_modular (α β : Finset (Fin 4)) :
    ((α ∪ β).card : ℚ) + (α ∩ β).card = (α.card : ℚ) + β.card := by
  exact_mod_cast Finset.card_union_add_card_inter α β
private lemma nonemptyBonus_submodular (α β : Finset (Fin 4)) :
    nonemptyBonus (α ∪ β) + nonemptyBonus (α ∩ β) ≤ nonemptyBonus α + nonemptyBonus
      β := by
  by_cases hα : α.Nonempty
  · by_cases hβ : β.Nonempty
    · have hUnion : (α ∪ β).Nonempty := Finset.union_nonempty.2 (Or.inl hα)
      by_cases hInter : (α ∩ β).Nonempty <;>
        simp [nonemptyBonus, hα, hβ, hUnion, hInter]
    · simp_all
  · have hα' : α = ∅ := Finset.not_nonempty_iff_eq_empty.mp hα
    rw [hα']
    simp [nonemptyBonus]
private lemma fullBonus_supermodular (α β : Finset (Fin 4)) :
    fullBonus α + fullBonus β ≤ fullBonus (α ∪ β) + fullBonus (α ∩ β) := by
  by_cases hα : α = Finset.univ
  · subst hα
    by_cases hβ : β = Finset.univ
    · simp_all
    · simp [fullBonus, hβ]
  · by_cases hβ : β = Finset.univ
    · subst hβ
      simp [fullBonus, hα]
    · have hUnion : 0 ≤ fullBonus (α ∪ β) := fullBonus_nonneg _
      have hInter : 0 ≤ fullBonus (α ∩ β) := fullBonus_nonneg _
      have hSum : 0 ≤ fullBonus (α ∪ β) + fullBonus (α ∩ β) := by
        linarith
      simpa [fullBonus, hα, hβ] using hSum
private lemma baseWitness_submodular (α β : Finset (Fin 4)) :
    baseWitness (α ∪ β) + baseWitness (α ∩ β) ≤ baseWitness α + baseWitness β := by
  have hCard := card_modular α β
  have hNonempty := nonemptyBonus_submodular α β
  have hFull := fullBonus_supermodular α β
  unfold baseWitness
  linarith
private lemma exceptional_of_union_pair :
    ∀ α β : Finset (Fin 4),
      α ∪ β = pair01 → α ≠ pair01 → β ≠ pair01 → PairBonusExceptional α β := by
  decide
private lemma exceptional_of_inter_pair :
    ∀ α β : Finset (Fin 4),
      α ∩ β = pair01 → α ≠ pair01 → β ≠ pair01 → PairBonusExceptional α β := by
  decide
private lemma pairBonus_submodular_left_pair (β : Finset (Fin 4)) :
    pairBonus (pair01 ∪ β) + pairBonus (pair01 ∩ β) ≤ pairBonus pair01 + pairBonus β := by
  by_cases hSub : β ⊆ pair01
  · by_cases hSup : pair01 ⊆ β
    · have hβ : β = pair01 := Finset.Subset.antisymm hSub hSup
      simp_all
    · have hβ : β ≠ pair01 := by
        intro h
        simp_all
      have hUnion : pair01 ∪ β = pair01 := Finset.union_eq_left.mpr hSub
      have hInter : pair01 ∩ β ≠ pair01 := by
        simp_all
      simp [pairBonus, hUnion, hInter, hβ]
  · by_cases hSup : pair01 ⊆ β
    · have hβ : β ≠ pair01 := by
        intro h
        simp_all
      have hUnion : pair01 ∪ β ≠ pair01 := by
        simp_all
      have hInter : pair01 ∩ β = pair01 := Finset.inter_eq_left.mpr hSup
      simp [pairBonus, hUnion, hInter, hβ]
    · have hβ : β ≠ pair01 := by
        intro h
        simp_all
      have hUnion : pair01 ∪ β ≠ pair01 := by
        simp_all
      have hInter : pair01 ∩ β ≠ pair01 := by
        simp_all
      simp [pairBonus, hUnion, hInter, hβ]
private lemma pairBonus_submodular_outside_exceptional :
    ∀ α β : Finset (Fin 4), ¬ PairBonusExceptional α β →
      pairBonus (α ∪ β) + pairBonus (α ∩ β) ≤ pairBonus α + pairBonus β := by
  intro α β hExceptional
  by_cases hα : α = pair01
  · subst hα
    simpa [pairBonus] using pairBonus_submodular_left_pair β
  · by_cases hβ : β = pair01
    · subst hβ
      simpa [Finset.union_comm, Finset.inter_comm, pairBonus, add_comm, add_left_comm,
        add_assoc] using
        pairBonus_submodular_left_pair α
    · by_cases hUnion : α ∪ β = pair01
      · exact False.elim (hExceptional (exceptional_of_union_pair α β hUnion hα hβ))
      · by_cases hInter : α ∩ β = pair01
        · exact False.elim (hExceptional (exceptional_of_inter_pair α β hInter hα hβ))
        · simp [pairBonus, hα, hβ, hUnion, hInter]
private lemma FWitnessℚ_submodular :
    ∀ α β : Finset (Fin 4),
      FWitnessℚ (α ∪ β) + FWitnessℚ (α ∩ β) ≤ FWitnessℚ α +
        FWitnessℚ β := by
  intro α β
  by_cases hExceptional : PairBonusExceptional α β
  · rcases hExceptional with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [show FWitnessℚ (({0} : Finset (Fin 4)) ∪ {1}) = 4 from by decide,
          show FWitnessℚ (({0} : Finset (Fin 4)) ∩ {1}) = 0 from by decide,
          show FWitnessℚ ({0} : Finset (Fin 4)) = 2 from by decide,
          show FWitnessℚ ({1} : Finset (Fin 4)) = 2 from by decide]
      norm_num
    · rw [show FWitnessℚ (({1} : Finset (Fin 4)) ∪ {0}) = 4 from by decide,
          show FWitnessℚ (({1} : Finset (Fin 4)) ∩ {0}) = 0 from by decide,
          show FWitnessℚ ({1} : Finset (Fin 4)) = 2 from by decide,
          show FWitnessℚ ({0} : Finset (Fin 4)) = 2 from by decide]
      norm_num
    · rw [show FWitnessℚ (({0, 1, 2} : Finset (Fin 4)) ∪ {0, 1, 3}) = 4 from by decide,
          show FWitnessℚ (({0, 1, 2} : Finset (Fin 4)) ∩ {0, 1, 3}) = 4 from by decide,
          show FWitnessℚ ({0, 1, 2} : Finset (Fin 4)) = 4 from by decide,
          show FWitnessℚ ({0, 1, 3} : Finset (Fin 4)) = 4 from by decide]
    · rw [show FWitnessℚ (({0, 1, 3} : Finset (Fin 4)) ∪ {0, 1, 2}) = 4 from by decide,
          show FWitnessℚ (({0, 1, 3} : Finset (Fin 4)) ∩ {0, 1, 2}) = 4 from by decide,
          show FWitnessℚ ({0, 1, 3} : Finset (Fin 4)) = 4 from by decide,
          show FWitnessℚ ({0, 1, 2} : Finset (Fin 4)) = 4 from by decide]
  · rw [FWitnessℚ_eq_base_add_pair (α ∪ β), FWitnessℚ_eq_base_add_pair (α ∩ β),
      FWitnessℚ_eq_base_add_pair α, FWitnessℚ_eq_base_add_pair β]
    have hBase := baseWitness_submodular α β
    have hPair := pairBonus_submodular_outside_exceptional α β hExceptional
    linarith
section EntropyFnEvaluation
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Fin 4 → Type u}
  [∀ i, MeasurableSpace (S i)] [∀ i, Finite (S i)]
  [∀ i, MeasurableSingletonClass (S i)]
  (X : ∀ i : Fin 4, Ω → S i) (μ : Measure Ω) [IsProbabilityMeasure μ]
end EntropyFnEvaluation
end ZhangYeung
end
end

set_option autoImplicit true
@[expose] public section
public section
open ZhangYeung
open MeasureTheory ProbabilityTheory
open scoped Topology ZhangYeungPFR
universe u
namespace ZhangYeung
theorem _root_.solution : shannonCone FWitness := by
  refine ⟨?_, ?_, ?_⟩
  · -- `FWitness ∅ = 0`
    change ((FWitnessℚ ∅ : ℚ) : ℝ) = 0
    have h : FWitnessℚ ∅ = 0 := by decide
    exact_mod_cast h
  · -- Monotonicity.
    intro α β hαβ
    have h : ∀ α β : Finset (Fin 4), α ⊆ β → FWitnessℚ α ≤ FWitnessℚ β := by
      decide
    simp only [FWitness_eq_cast]
    exact_mod_cast h α β hαβ
  · -- Submodularity.
    intro α β
    simp only [FWitness_eq_cast]
    exact_mod_cast FWitnessℚ_submodular α β
end ZhangYeung
