-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.graph_deleted_bit_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:27:46.636219+00:00
-- url     : https://prove2.me/submissions/cd185f66-8e4e-4d05-a24b-ba3a4b47d3df

import Theorems.Thm_StabilityDichotomies_Bijunctive_score_compare_measurable
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private abbrev Seed (m : ℕ) (V : Type) := (Fin m → ℝ) × ℝ × (Literal V → ℝ)
private def firstMask {m : ℕ} {V : Type} (ε : ℝ) (s : Seed m V) : Fin m → Bool :=
  fun i => decide (s.1 i ≤ 1 - ε / 2)
private def secondMask {m : ℕ} {V : Type} (s : Seed m V) : Fin m → Bool :=
  fun i => decide (s.1 i ≤ s.2.1)
private theorem decide_le_measurable {Ω : Type} [MeasurableSpace Ω] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun ω => decide (f ω ≤ g ω)) := by
  have hs : MeasurableSet {ω | f ω ≤ g ω} := measurableSet_le hf hg
  have hm : Measurable (fun ω => if f ω ≤ g ω then true else false) :=
    Measurable.ite hs measurable_const measurable_const
  convert hm using 1
  funext ω
  by_cases h : f ω ≤ g ω <;> simp [h]
private theorem firstMask_measurable {m : ℕ} {V : Type} (ε : ℝ) :
    Measurable (firstMask (m := m) (V := V) ε) := by
  apply measurable_pi_lambda
  intro i
  apply decide_le_measurable
  · exact (measurable_pi_apply (X := fun _ : Fin m => ℝ) i).comp measurable_fst
  · exact measurable_const
private theorem secondMask_measurable {m : ℕ} {V : Type} :
    Measurable (secondMask (m := m) (V := V)) := by
  apply measurable_pi_lambda
  intro i
  apply decide_le_measurable
  · exact (measurable_pi_apply (X := fun _ : Fin m => ℝ) i).comp measurable_fst
  · exact measurable_fst.comp measurable_snd

private theorem dynamic_score_comparison_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V)
    (m1 m2 : Seed I.constraints.card V → Fin I.constraints.card → Bool)
    (h1 : Measurable m1) (h2 : Measurable m2) (v : V) :
    MeasurableSet {s : Seed I.constraints.card V |
      literalScore rep (thinnedInstance I (m1 s)) (thinnedInstance I (m2 s)) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I (m1 s)) (thinnedInstance I (m2 s)) s.2.2 (v,true)} := by
  have heq : {s : Seed I.constraints.card V |
      literalScore rep (thinnedInstance I (m1 s)) (thinnedInstance I (m2 s)) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I (m1 s)) (thinnedInstance I (m2 s)) s.2.2 (v,true)} =
      ⋃ a : Fin I.constraints.card → Bool, ⋃ b : Fin I.constraints.card → Bool,
      ({s : Seed I.constraints.card V | m1 s = a} ∩ {s | m2 s = b}) ∩
      {s | literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,false) <
        literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,true)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hs; exact ⟨m1 s,m2 s,⟨rfl,rfl⟩,hs⟩
    · rintro ⟨a,b,⟨ha,hb⟩,hs⟩
      subst a; subst b; exact hs
  rw [heq]
  apply MeasurableSet.iUnion; intro a
  apply MeasurableSet.iUnion; intro b
  have ha : MeasurableSet {s : Seed I.constraints.card V | m1 s = a} := measurableSet_eq.preimage h1
  have hb : MeasurableSet {s : Seed I.constraints.card V | m2 s = b} := measurableSet_eq.preimage h2
  have hs : MeasurableSet {s : Seed I.constraints.card V |
      literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,true)} :=
    (score_compare_measurable rep (thinnedInstance I a) (thinnedInstance I b) (v,true) (v,false)).preimage
    (measurable_snd.comp measurable_snd)
  exact (ha.inter hb).inter hs

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (j : Fin I.constraints.card) (v : V) :
    MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
        (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I (fun i => decide (s.1 i ≤ 1 - ε / 2) && decide (i ≠ j)))
        (thinnedInstance I (fun i => decide (s.1 i ≤ s.2.1))) s.2.2 (v,true)} := by
  let f : (Fin I.constraints.card → Bool) → (Fin I.constraints.card → Bool) :=
    fun a i => a i && decide (i ≠ j)
  have hf : Measurable f := measurable_of_countable f
  have hm1 : Measurable (fun s : Seed I.constraints.card V => f (firstMask ε s)) :=
    hf.comp (firstMask_measurable ε)
  have hm2 : Measurable (secondMask (m := I.constraints.card) (V := V)) := secondMask_measurable
  exact dynamic_score_comparison_measurable rep I _ _ hm1 hm2 v
