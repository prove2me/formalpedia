-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.uniform_order_thinned_root_edge_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:10:44.803224+00:00
-- url     : https://prove2.me/submissions/af28308b-fba9-4621-963d-42ab0c064b17

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

private theorem fixed_order_inside_deletion_cost_bound {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I)
    (m : Fin I.constraints.card → Bool) (σ : α → Fin I.constraints.card) (β : ℝ) (hβ : 0 < β)
    (π : Equiv.Perm α) :
    (∑ i : α, deletionCost rep I m σ β ((prefixSet ((Fintype.equivFin α i).val+1)).image π) (π i)) ≤
      (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ) := by
  classical
  let k := Fintype.card α
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

  let f : α → ℝ := fun i => deletionCost rep I m σ β ((prefixSet ((Fintype.equivFin α i).val+1)).image π) (π i)
  have hre : (∑ i : α, f i) = ∑ t : Fin k, f ((Fintype.equivFin α).symm t) :=
    (Equiv.sum_comp (Fintype.equivFin α).symm f).symm
  change (∑ i : α, f i) ≤ _
  rw [hre]
  have hterm (t : Fin k) : f ((Fintype.equivFin α).symm t) =
      ∑ v : V, (Measure.pi (fun _ : Literal V => expMeasure β)
        {δ | decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask t.val)) δ (v,false) <
               literalScore rep (thinnedInstance I m) (thinnedInstance I (mask t.val)) δ (v,true)) ≠
             decide (literalScore rep (thinnedInstance I m) (thinnedInstance I (mask (t.val+1))) δ (v,false) <
               literalScore rep (thinnedInstance I m) (thinnedInstance I (mask (t.val+1))) δ (v,true))}).toReal := by
    have hpos : 0 < t.val+1 := by omega
    have hle : t.val+1 ≤ Fintype.card α := by dsimp [k] at t; omega
    have hlast : prefixLast (α := α) (t.val+1) = (Fintype.equivFin α).symm t := by
      simp [prefixLast,hpos,hle]
    simpa [f,hlast] using hEdge t.val t.isLt
  simp_rw [hterm]
  rw [Finset.sum_range] at hf
  exact hf

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
    (∑ π : Equiv.Perm α, ∑ i : α, cost ((S ((Fintype.equivFin α i).val+1)).image π) (π i)) ≤
      (Fintype.card (Equiv.Perm α) : ℝ) *
        ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  classical
  change (∑ π : Equiv.Perm α, ∑ i : α, deletionCost rep I m σ β ((prefixSet ((Fintype.equivFin α i).val+1)).image π) (π i)) ≤
    (Fintype.card (Equiv.Perm α) : ℝ) * ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ))
  simpa using Finset.sum_le_card_nsmul (Finset.univ : Finset (Equiv.Perm α))
    (fun π => ∑ i : α, deletionCost rep I m σ β ((prefixSet ((Fintype.equivFin α i).val+1)).image π) (π i))
    ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ))
    (fun π _ => fixed_order_inside_deletion_cost_bound rep I hI m σ β hβ π)
