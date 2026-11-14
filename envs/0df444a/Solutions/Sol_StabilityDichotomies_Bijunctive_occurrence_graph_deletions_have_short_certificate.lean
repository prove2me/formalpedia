-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.occurrence_graph_deletions_have_short_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:11:27.460211+00:00
-- url     : https://prove2.me/submissions/b5191388-ad91-4314-a743-d933230c6e4d

import Theorems.Thm_StabilityDichotomies_Bijunctive_graph_deletion_sensitive_indices_have_short_certificate
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem thinned_member_iff {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (c : Constraint Γ V) :
    c ∈ (thinnedInstance I mask).constraints ↔
      ∃ i, mask i = true ∧ occurrenceAt I i = c := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn]
  constructor
  · rintro ⟨⟨i,d⟩,⟨⟨j,hj⟩,hm⟩,hd⟩
    cases hj
    exact ⟨i,hm,hd⟩
  · rintro ⟨i,hi,hic⟩
    exact ⟨(i,occurrenceAt I i),⟨⟨i,rfl⟩,hi⟩,hic⟩

theorem solution
    {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (v : V) (w : Bool)
    (hw : w = decide (literalScore rep (thinnedInstance I mask) F δ (v,false) <
      literalScore rep (thinnedInstance I mask) F δ (v,true)))
    (hpos : (0 : WithBot ℝ) < literalScore rep (thinnedInstance I mask) F δ (v,w)) :
    ∃ root : Literal V, ∃ n : ℕ, ∃ S : Finset (Fin I.constraints.card),
      S.card ≤ n ∧ (n : ℝ) < δ root ∧
      ∀ j ∉ S, decide (literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,false) <
        literalScore rep (thinnedInstance I (fun i => mask i && decide (i ≠ j))) F δ (v,true)) = w := by
  classical
  let G := thinnedInstance I mask
  let Gdel := fun j : Fin I.constraints.card => thinnedInstance I (fun i => mask i && decide (i ≠ j))
  let label := fun (i : Fin I.constraints.card) (a b : Literal V) => mask i = true ∧
    ∃ q ∈ rep.clauses (occurrenceAt I i).rel,
      let z := substituteClause (occurrenceAt I i) q
      z.1 ≠ literalNeg z.2 ∧
        ((a = literalNeg z.1 ∧ b = z.2) ∨ (a = literalNeg z.2 ∧ b = z.1))
  have hsub : ∀ j a b, implicationArc rep (Gdel j) a b → implicationArc rep G a b := by
    intro j a b harc
    obtain ⟨c,hc,q,hq,ht,harc⟩ := harc
    obtain ⟨i,hi,hic⟩ := (thinned_member_iff I _ c).mp hc
    have hm : mask i = true := by simpa [Gdel] using (Bool.and_eq_true_iff.mp hi).1
    have hc' : c ∈ G.constraints := (thinned_member_iff I mask c).mpr ⟨i,hm,hic⟩
    exact ⟨c,hc',q,hq,ht,harc⟩
  have hlabel : ∀ a b, implicationArc rep G a b → ∃ i, label i a b := by
    intro a b harc
    obtain ⟨c,hc,q,hq,ht,harc⟩ := harc
    obtain ⟨i,hi,hic⟩ := (thinned_member_iff I mask c).mp hc
    subst c
    exact ⟨i,hi,q,hq,ht,harc⟩
  have hretain : ∀ i j a b, i ≠ j → label i a b → implicationArc rep (Gdel j) a b := by
    intro i j a b hne h
    obtain ⟨hi,q,hq,ht,harc⟩ := h
    have hm : (mask i && decide (i ≠ j)) = true := by simp [hi,hne]
    have hc : occurrenceAt I i ∈ (Gdel j).constraints := (thinned_member_iff I _ _).mpr ⟨i,hm,rfl⟩
    exact ⟨occurrenceAt I i,hc,q,hq,ht,harc⟩
  exact graph_deletion_sensitive_indices_have_short_certificate rep G F Gdel δ label hsub hlabel hretain v w hw hpos
