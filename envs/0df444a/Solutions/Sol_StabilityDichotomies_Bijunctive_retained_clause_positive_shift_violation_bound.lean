-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.retained_clause_positive_shift_violation_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:45:42.827491+00:00
-- url     : https://prove2.me/submissions/408f6d24-9a42-41d4-bf44-3fcb56f11032

import Theorems.Thm_StabilityDichotomies_Bijunctive_violated_clause_has_close_root_maxima
import Theorems.Thm_StabilityDichotomies_Bijunctive_disjoint_subsets_maxima_close_probability
import Theorems.Thm_StabilityDichotomies_Bijunctive_satisfiable_positive_shift_has_positive_literal_score
import Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_cannot_reach_clause_negations
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem distance_walk {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G : Instance Γ V) (a b : Literal V) (n : ℕ)
    (hd : implicationDistance rep G a b = some n) : WalkLength (implicationArc rep G) n a b := by
  unfold implicationDistance at hd
  split at hd
  next h =>
    have hn : Nat.find h = n := Option.some.inj hd
    simpa [← hn] using Nat.find_spec h
  next h => simp at hd

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (c : Constraint Γ V) (hc : c ∈ G.constraints)
    (q : Clause (Fin c.rel.val.arity)) (hq : q ∈ rep.clauses c.rel)
    (ht : (substituteClause c q).1 ≠ literalNeg (substituteClause c q).2)
    (β : ℝ) (hβ : 0 < β) :
    ((Measure.pi (fun _ : Literal V => expMeasure β))
      {δ : Literal V → ℝ | (∀ a, 0 < δ a) ∧
        ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
          literalScore rep G F δ (v,true))) (substituteClause c q)}).toReal ≤
      1 - Real.exp (-β) := by
  classical
  letI : IsProbabilityMeasure (expMeasure β) := isProbabilityMeasure_expMeasure hβ
  let a := literalNeg (substituteClause c q).1
  let b := literalNeg (substituteClause c q).2
  let S : Finset (Literal V) := Finset.univ.filter (fun r => feasibleLiteral F r ∧
    ∃ n, implicationDistance rep G r a = some n)
  let T : Finset (Literal V) := Finset.univ.filter (fun r => feasibleLiteral F r ∧
    ∃ n, implicationDistance rep G r b = some n)
  have hS (r : Literal V) : r ∈ S ↔ feasibleLiteral F r ∧ ∃ n, implicationDistance rep G r a = some n := by simp [S]
  have hT (r : Literal V) : r ∈ T ↔ feasibleLiteral F r ∧ ∃ n, implicationDistance rep G r b = some n := by simp [T]
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro r hrS hrT
    obtain ⟨hfr,n,hn⟩ := (hS r).mp hrS
    obtain ⟨_,m,hm⟩ := (hT r).mp hrT
    exact feasible_root_cannot_reach_clause_negations rep G F hsub c hc q hq r hfr
      ⟨n,m,distance_walk rep G r a n hn,distance_walk rep G r b m hm⟩
  let d : Literal V → ℝ := fun r => if r ∈ S then (implicationDistance rep G r a).getD 0
    else (implicationDistance rep G r b).getD 0
  have hdS (r : Literal V) (n : ℕ) (hr : r ∈ S) (hn : implicationDistance rep G r a = some n) : d r = n := by simp [d,hr,hn]
  have hdT (r : Literal V) (n : ℕ) (hr : r ∈ T) (hn : implicationDistance rep G r b = some n) : d r = n := by
    have hnS : r ∉ S := fun h => Finset.disjoint_left.mp hST h hr
    simp [d,hnS,hn]
  let E : Set (Literal V → ℝ) := {δ | (∀ a, 0 < δ a) ∧
    ¬ clauseSatisfied (fun v => decide (literalScore rep G F δ (v,false) <
      literalScore rep G F δ (v,true))) (substituteClause c q)}
  let H : Set (Literal V → ℝ) := {δ | ∃ u ∈ S, ∃ v ∈ T,
    (∀ r ∈ S, δ r - d r ≤ δ u - d u) ∧
    (∀ r ∈ T, δ r - d r ≤ δ v - d v) ∧
    (δ u - d u) - (δ v - d v) ≤ 1 ∧ (δ v - d v) - (δ u - d u) ≤ 1}
  have hEH : E ⊆ H := by
    intro δ hδ
    have hp : ∀ v, ∃ z : Bool, (0 : WithBot ℝ) < literalScore rep G F δ (v,z) :=
      fun v => satisfiable_positive_shift_has_positive_literal_score rep G F hF δ hδ.1 v
    obtain ⟨u,v,n,m,huv,hfu,hfv,hua,hvb,hmaxu,hmaxv,hgap1,hgap2⟩ :=
      violated_clause_has_close_root_maxima rep G F δ hsub hp c hc q hq ht hδ.2
    have hu : u ∈ S := (hS u).mpr ⟨hfu,n,hua⟩
    have hv : v ∈ T := (hT v).mpr ⟨hfv,m,hvb⟩
    have hdu := hdS u n hu hua
    have hdv := hdT v m hv hvb
    refine ⟨u,hu,v,hv,?_,?_,?_,?_⟩
    · intro x hx
      obtain ⟨hf,k,hk⟩ := (hS x).mp hx
      simpa [hdS x k hx hk,hdu] using hmaxu x k hf hk
    · intro x hx
      obtain ⟨hf,k,hk⟩ := (hT x).mp hx
      simpa [hdT x k hx hk,hdv] using hmaxv x k hf hk
    · simpa [hdu,hdv] using hgap1
    · simpa [hdu,hdv] using hgap2
  by_cases hneS : S.Nonempty
  · by_cases hneT : T.Nonempty
    · have hbound := disjoint_subsets_maxima_close_probability S T hneS hneT hST β 1 hβ (by norm_num) d
      haveI : IsProbabilityMeasure (Measure.pi (fun _ : Literal V => expMeasure β)) := by infer_instance
      have hm := ENNReal.toReal_mono (measure_ne_top (Measure.pi (fun _ : Literal V => expMeasure β)) H) (measure_mono hEH)
      exact hm.trans (by simpa [H] using hbound)
    · have hempty : E = ∅ := by
        apply Set.Subset.antisymm ?_ (Set.empty_subset _)
        intro x hx
        obtain ⟨_,_,v,hv,_⟩ := hEH hx
        exact hneT ⟨v,hv⟩
      rw [show ((Measure.pi (fun _ : Literal V => expMeasure β)) E).toReal = 0 by rw [hempty,measure_empty]; rfl]
      have := Real.add_one_le_exp (-β)
      have he : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
  · have hempty : E = ∅ := by
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      intro x hx
      obtain ⟨u,hu,_⟩ := hEH hx
      exact hneS ⟨u,hu⟩
    rw [show ((Measure.pi (fun _ : Literal V => expMeasure β)) E).toReal = 0 by rw [hempty,measure_empty]; rfl]
    have he : Real.exp (-β) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
