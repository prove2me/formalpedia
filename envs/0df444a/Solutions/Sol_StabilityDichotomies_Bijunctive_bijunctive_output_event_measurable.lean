-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_output_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:00:49.567946+00:00
-- url     : https://prove2.me/submissions/d6134ed6-4e83-4f09-9dd8-bbdf950b32c7

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem score_lt_shift_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (target root : Literal V) (n : ℕ) :
    MeasurableSet {δ : Literal V → ℝ |
      literalScore rep G F δ target < ((δ root - n : ℝ) : WithBot ℝ)} := by
  have hform : {δ : Literal V → ℝ |
      literalScore rep G F δ target < ((δ root - n : ℝ) : WithBot ℝ)} =
      ⋂ r : Literal V, {δ : Literal V → ℝ |
        (if feasibleLiteral F r then
          match implicationDistance rep G r target with
          | some k => ((δ r - k : ℝ) : WithBot ℝ)
          | none => ⊥
        else ⊥) < ((δ root - n : ℝ) : WithBot ℝ)} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    unfold literalScore
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe (δ root - n))]
    simp only [Finset.mem_univ, true_implies]
    constructor <;> intro h r
    all_goals
      have hh := h r
      rw [lt_iff_le_not_ge] at hh ⊢
      exact hh
  rw [hform]
  apply MeasurableSet.iInter
  intro r
  by_cases hr : feasibleLiteral F r
  · cases hd : implicationDistance rep G r target with
    | none => simp [hr,hd]
    | some k =>
      have hm : MeasurableSet {δ : Literal V → ℝ | δ r - k < δ root - n} :=
        measurableSet_lt ((measurable_pi_apply (X := fun _ : Literal V => ℝ) r).sub_const (k : ℝ))
          ((measurable_pi_apply (X := fun _ : Literal V => ℝ) root).sub_const (n : ℝ))
      simpa [hr,hd] using hm
  · simp [hr]

private theorem score_compare_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (a b : Literal V) :
    MeasurableSet {δ : Literal V → ℝ | literalScore rep G F δ b < literalScore rep G F δ a} := by
  have hform : {δ : Literal V → ℝ | literalScore rep G F δ b < literalScore rep G F δ a} =
      ⋃ r : Literal V, {δ : Literal V → ℝ |
        literalScore rep G F δ b < (if feasibleLiteral F r then
          match implicationDistance rep G r a with
          | some k => ((δ r - k : ℝ) : WithBot ℝ)
          | none => ⊥
        else ⊥)} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    unfold literalScore at *
    rw [Finset.lt_sup_iff]
    simp only [Finset.mem_univ, true_and]
    constructor <;> rintro ⟨r,hr⟩ <;> refine ⟨r, ?_⟩
    all_goals
      rw [lt_iff_le_not_ge] at hr ⊢
      exact hr
  rw [hform]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : feasibleLiteral F r
  · cases hd : implicationDistance rep G r a with
    | none => simp [hr,hd]
    | some k => simpa [hr,hd] using score_lt_shift_measurable rep G F b r k
  · simp [hr]

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

private theorem output_bit_event_measurable {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (v : V) :
    MeasurableSet {s : Seed I.constraints.card V |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v = true} := by
  have hform : {s : Seed I.constraints.card V |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v = true} =
      ⋃ a : Fin I.constraints.card → Bool, ⋃ b : Fin I.constraints.card → Bool,
        ({s : Seed I.constraints.card V | firstMask ε s = a} ∩
         {s : Seed I.constraints.card V | secondMask s = b}) ∩
        {s : Seed I.constraints.card V |
          literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,false) <
          literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,true)} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    have hm1 : firstMask ε s = (fun i => decide (s.1 i ≤ 1 - ε / 2)) := by
      funext i
      by_cases hi : s.1 i ≤ 1 - ε / 2 <;> simp [firstMask,hi]
    have hm2 : secondMask s = (fun i => decide (s.1 i ≤ s.2.1)) := by
      funext i
      by_cases hi : s.1 i ≤ s.2.1 <;> simp [secondMask,hi]
    constructor
    · intro hs
      refine ⟨firstMask ε s, secondMask s, ⟨rfl,rfl⟩, ?_⟩
      simpa only [bijunctiveOutput, decide_eq_true_eq, hm1, hm2] using hs
    · rintro ⟨a,b,⟨ha,hb⟩,hs⟩
      subst a
      subst b
      simpa only [bijunctiveOutput, decide_eq_true_eq, hm1, hm2] using hs
  rw [hform]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  have ha : MeasurableSet {s : Seed I.constraints.card V | firstMask ε s = a} :=
    measurableSet_eq.preimage (firstMask_measurable ε)
  have hb : MeasurableSet {s : Seed I.constraints.card V | secondMask s = b} :=
    measurableSet_eq.preimage secondMask_measurable
  have hs : MeasurableSet {s : Seed I.constraints.card V |
      literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,false) <
      literalScore rep (thinnedInstance I a) (thinnedInstance I b) s.2.2 (v,true)} :=
    (score_compare_measurable rep (thinnedInstance I a) (thinnedInstance I b) (v,true) (v,false)).preimage
      (measurable_snd.comp measurable_snd)
  exact (ha.inter hb).inter hs

private theorem bijunctive_output_event_measurable_aux {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (x : V → Bool) :
    MeasurableSet {s : Seed I.constraints.card V |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x} := by
  have hform : {s : Seed I.constraints.card V |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x} =
      ⋂ v : V, {s : Seed I.constraints.card V |
        bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v = x v} := by
    ext s
    simp [funext_iff]
  rw [hform]
  apply MeasurableSet.iInter
  intro v
  have h := output_bit_event_measurable rep I ε v
  cases hx : x v with
  | false =>
    have heq : {s : Seed I.constraints.card V |
        bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v = false} =
        {s : Seed I.constraints.card V |
        bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v = true}ᶜ := by
      ext s
      cases ht : bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 v <;> simp [ht]
    rw [heq]
    exact h.compl
  | true => simpa [hx] using h


theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (ε : ℝ) (x : V → Bool) :
    MeasurableSet {s : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) |
      bijunctiveOutput rep I ε s.1 s.2.1 s.2.2 = x} := by
  exact bijunctive_output_event_measurable_aux rep I ε x
