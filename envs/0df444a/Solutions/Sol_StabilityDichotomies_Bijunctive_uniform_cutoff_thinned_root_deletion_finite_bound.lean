-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.uniform_cutoff_thinned_root_deletion_finite_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:10:43.548454+00:00
-- url     : https://prove2.me/submissions/0da7de4e-cbb9-499f-b0d1-d5aa8d27355f

import Theorems.Thm_StabilityDichotomies_Bijunctive_thinning_feasibility_chain_total_changes_harmonic_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_uniform_cutoff_prefix_deletions_le_chain_budget
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical BigOperators

private def prefixSet {α : Type} [Fintype α] (t : ℕ) : Finset α :=
  Finset.univ.filter (fun a => (Fintype.equivFin α a).val < t)

private def prefixLast {α : Type} [Fintype α] [Nonempty α] (t : ℕ) : α :=
  if h : 0 < t ∧ t ≤ Fintype.card α then (Fintype.equivFin α).symm ⟨t-1, by omega⟩ else Classical.choice inferInstance

private theorem prefixLast_mem {α : Type} [Fintype α] [Nonempty α] {t : ℕ}
    (ht : 0 < t) (ht' : t ≤ Fintype.card α) : prefixLast (α := α) t ∈ prefixSet t := by
  simp [prefixLast,prefixSet,ht,ht']

private theorem prefix_erase_last {α : Type} [Fintype α] [Nonempty α] {t : ℕ}
    (ht : t < Fintype.card α) : (prefixSet (α := α) (t+1)).erase (prefixLast (t+1)) = prefixSet t := by
  classical
  have hle : t+1 ≤ Fintype.card α := by omega
  have hpos : 0 < t+1 := by omega
  ext a
  simp only [Finset.mem_erase,prefixSet,Finset.mem_filter,Finset.mem_univ,true_and]
  have he : (Fintype.equivFin α) (prefixLast (t+1)) = ⟨t,ht⟩ := by
    simp [prefixLast,hpos,hle]
  constructor
  · rintro ⟨hne,hlt⟩
    by_contra hnot
    have htval : (Fintype.equivFin α a).val = t := by omega
    apply hne
    apply (Fintype.equivFin α).injective
    apply Fin.ext
    rw [he]
    exact htval
  · intro ha
    constructor
    · intro heq
      have h := congrArg (fun x : α => (Fintype.equivFin α x).val) heq
      rw [he] at h
      simp only at h
      omega
    · omega

private def augmentedMask {α : Type} {Γ : Language} {V : Type} (I : Instance Γ V)
    (m : Fin I.constraints.card → Bool) (σ : α → Fin I.constraints.card) (A : Finset α) : Fin I.constraints.card → Bool :=
  fun i => m i || decide (∃ a ∈ A, σ a = i)

private def chainBit {α : Type} {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (m : Fin I.constraints.card → Bool)
    (σ : α → Fin I.constraints.card) (A : Finset α) (δ : Literal V → ℝ) (v : V) : Bool :=
  decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (augmentedMask I m σ A)) δ (v,false) <
    literalScore rep (thinnedInstance I m) (thinnedInstance I (augmentedMask I m σ A)) δ (v,true))

private def deletionCost {α : Type} [DecidableEq α] {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (m : Fin I.constraints.card → Bool)
    (σ : α → Fin I.constraints.card) (β : ℝ) (A : Finset α) (a : α) : ℝ :=
  ∑ v : V, (Measure.pi (fun _ : Literal V => expMeasure β)
    {δ | chainBit rep I m σ A δ v ≠ chainBit rep I m σ (A.erase a) δ v}).toReal

private theorem finite_uniform_outside_root_cost_bound {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (m : Fin I.constraints.card → Bool) (σ : α → Fin I.constraints.card) (β : ℝ) (hβ : 0 < β) :
    (∑ q : Fin (Fintype.card α + 1), ∑ π : Equiv.Perm α,
      ∑ i ∈ prefixSet (α := α) q.val, deletionCost rep I m σ β ((prefixSet q.val).image π) (π i)) ≤
      (Fintype.card α + 1 : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) *
        ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  classical
  let k := Fintype.card α
  let S : Fin (k+1) → Finset α := fun q => prefixSet q.val
  let last : Fin (k+1) → α := fun q => prefixLast q.val
  let cost : Fin (k+1) → Finset α → α → ℝ := fun _ A a => deletionCost rep I m σ β A a
  let D : ℝ := (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)
  have htgt : (∑ q : Fin (k+1), ∑ π : Equiv.Perm α, ∑ i ∈ S q, cost q ((S q).image π) (π i)) ≤
      (Fintype.card (Fin (k+1)) : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) * D := by
    apply uniform_cutoff_prefix_deletions_le_chain_budget S last cost D
    · intro q
      have hh := Finset.card_le_univ (S q)
      simp only [Fintype.card_fin] at ⊢
      omega
    · intro q hne
      have hq : 0 < q.val := by
        by_contra h
        have hz : q.val = 0 := by omega
        apply hne
        simp [S,prefixSet,hz]
      have hq' : q.val ≤ Fintype.card α := by dsimp [k] at q; omega
      exact prefixLast_mem hq hq'
    · intro q π
      apply Finset.sum_nonneg
      intro v hv
      exact ENNReal.toReal_nonneg
    · intro π
      let mask : ℕ → Fin I.constraints.card → Bool := fun t => augmentedMask I m σ ((prefixSet t).image π)
      have hmask0 : mask 0 = m := by
        funext i
        simp [mask,augmentedMask,prefixSet]
      have hbase : ∀ t ≤ k, ∀ i, mask 0 i = true → mask t i = true := by
        intro t ht i hi
        rw [hmask0] at hi
        simp [mask,augmentedMask,hi]
      have hchain : ∀ t < k, ∀ i, mask t i = true → mask (t+1) i = true := by
        intro t ht i hi
        simp only [mask,augmentedMask,Bool.or_eq_true,decide_eq_true_eq] at hi ⊢
        rcases hi with hi | ⟨a,ha,hσ⟩
        · exact Or.inl hi
        · right
          refine ⟨a,?_,hσ⟩
          rcases Finset.mem_image.mp ha with ⟨b,hb,rfl⟩
          refine Finset.mem_image.mpr ⟨b,?_,rfl⟩
          simp only [prefixSet,Finset.mem_filter,Finset.mem_univ,true_and] at hb ⊢
          omega
      have hf := thinning_feasibility_chain_total_changes_harmonic_bound rep I hI mask k hbase hchain β hβ
      rw [hmask0] at hf
      have hEdge (t : ℕ) (ht : t < k) :
          deletionCost rep I m σ β ((prefixSet (t+1)).image π) (π (prefixLast (t+1))) =
            ∑ v : V, (Measure.pi (fun _ : Literal V => expMeasure β)
              {δ | decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask t)) δ (v,false) <
                     literalScore rep (thinnedInstance I m) (thinnedInstance I (mask t)) δ (v,true)) ≠
                   decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask (t+1))) δ (v,false) <
                     literalScore rep (thinnedInstance I m) (thinnedInstance I (mask (t+1))) δ (v,true))}).toReal := by
        have hp : ((prefixSet (t+1)).image π).erase (π (prefixLast (t+1))) = (prefixSet t).image π := by
          rw [← Finset.image_erase π.injective]
          congr 1
          ext a
          have he := congrArg (fun s : Finset α => a ∈ s) (prefix_erase_last (α := α) (t := t) (by simpa [k] using ht))
          simp only [Finset.mem_erase] at he
          simp only [Finset.mem_erase]
          exact Iff.of_eq he
        unfold deletionCost
        apply Finset.sum_congr rfl
        intro v hv
        apply congrArg ENNReal.toReal
        apply congrArg (Measure.pi (fun _ : Literal V => expMeasure β))
        ext δ
        change (chainBit rep I m σ _ δ v ≠ chainBit rep I m σ _ δ v) ↔ _
        simp only [Set.mem_setOf_eq,chainBit,hp,mask,ne_comm]
      rw [Fin.sum_univ_succ]
      have hS0 : S 0 = ∅ := by simp [S,prefixSet]
      simp only [hS0, ↓reduceIte, zero_add]
      have hterm (t : Fin k) :
          (if S t.succ = ∅ then 0 else cost t.succ ((S t.succ).image π) (π (last t.succ))) =
          ∑ v : V, (Measure.pi (fun _ : Literal V => expMeasure β)
            {δ | decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask t.val)) δ (v,false) <
                   literalScore rep (thinnedInstance I m) (thinnedInstance I (mask t.val)) δ (v,true)) ≠
                 decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask (t.val+1))) δ (v,false) <
                   literalScore rep (thinnedInstance I m) (thinnedInstance I (mask (t.val+1))) δ (v,true))}).toReal := by
        have hp : prefixSet (α := α) (t.val+1) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨prefixLast (t.val+1), prefixLast_mem (by omega) (by dsimp [k] at *; omega)⟩
        simpa [S,last,cost,hp] using hEdge t.val t.isLt
      simp_rw [hterm]
      rw [Finset.sum_range] at hf
      exact hf
  simpa [S,cost,D,k] using htgt

theorem solution
    {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (m : Fin I.constraints.card → Bool) (σ : α → Fin I.constraints.card) (β : ℝ) (hβ : 0 < β) :
    let S := fun t : ℕ => Finset.univ.filter (fun a : α => (Fintype.equivFin α a).val < t)
    let mask := fun (A : Finset α) (i : Fin I.constraints.card) => m i || decide (∃ a ∈ A, σ a = i)
    let bit := fun (A : Finset α) (δ : Literal V → ℝ) (v : V) =>
      decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask A)) δ (v,false) <
        literalScore rep (thinnedInstance I m) (thinnedInstance I (mask A)) δ (v,true))
    let cost := fun (A : Finset α) (a : α) => ∑ v : V,
      (Measure.pi (fun _ : Literal V => expMeasure β) {δ | bit A δ v ≠ bit (A.erase a) δ v}).toReal
    (∑ q : Fin (Fintype.card α + 1), ∑ π : Equiv.Perm α,
      ∑ i ∈ S q.val, cost ((S q.val).image π) (π i)) ≤
      (Fintype.card α + 1 : ℝ) * (Fintype.card (Equiv.Perm α) : ℝ) *
        ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  classical
  exact finite_uniform_outside_root_cost_bound rep I hI m σ β hβ

