-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.isolated_variable_graph_deletion_score_unchanged
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:30:02.806604+00:00
-- url     : https://prove2.me/submissions/3d7e5592-96cf-4cc4-b678-0a67101726cd

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem thinned_member {Γ : Language} {V : Type} (I : Instance Γ V)
    (mask : Fin I.constraints.card → Bool) (c : Constraint Γ V)
    (hc : c ∈ (thinnedInstance I mask).constraints) : c ∈ I.constraints := by
  simp only [thinnedInstance, Multiset.mem_coe, List.mem_map, List.mem_filter, List.mem_ofFn] at hc
  obtain ⟨⟨i,d⟩,⟨⟨j,hj⟩,hm⟩,hd⟩ := hc
  cases hj
  simp only [Prod.snd] at hd
  subst c
  simp only [occurrenceAt]
  exact Multiset.mem_toList.mp (List.get_mem _ _)

private theorem no_walk_to_isolated {α : Type} {arc : α → α → Prop} (target : α)
    (hno : ∀ a, ¬ arc a target) {n : ℕ} {a : α} (hw : WalkLength arc n a target) :
    a = target ∧ n = 0 := by
  induction hw with
  | zero => exact ⟨rfl,rfl⟩
  | @step n a b c hab hbc ih =>
    obtain ⟨hbt,hn⟩ := ih hno
    subst b
    exact False.elim (hno a hab)

private theorem isolated_distance {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G : Instance Γ V) (target : Literal V)
    (hno : ∀ a, ¬ implicationArc rep G a target) (root : Literal V) :
    implicationDistance rep G root target = if root = target then some 0 else none := by
  classical
  by_cases heq : root = target
  · subst root
    have hreach : ∃ n, WalkLength (implicationArc rep G) n target target := ⟨0,WalkLength.zero _⟩
    have hfind : Nat.find hreach = 0 := by
      have h := Nat.find_min' hreach (WalkLength.zero target)
      omega
    simp [implicationDistance,hreach,hfind]
  · have hreach : ¬ ∃ n, WalkLength (implicationArc rep G) n root target := by
      rintro ⟨n,hn⟩
      exact heq (no_walk_to_isolated target hno hn).1
    simp [implicationDistance,hreach,heq]

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I F : Instance Γ V) (v : V)
    (hiso : ∀ c ∈ I.constraints, ∀ k : Fin c.rel.val.arity, c.scope k ≠ v)
    (mask mask' : Fin I.constraints.card → Bool) (δ : Literal V → ℝ) (b : Bool) :
    literalScore rep (thinnedInstance I mask) F δ (v,b) =
      literalScore rep (thinnedInstance I mask') F δ (v,b) := by
  have hno (m : Fin I.constraints.card → Bool) :
      ∀ a, ¬ implicationArc rep (thinnedInstance I m) a (v,b) := by
    intro a harc
    obtain ⟨c,hc,q,hq,ht,harc⟩ := harc
    have hc' := thinned_member I m c hc
    rcases harc with ⟨_,ha⟩ | ⟨_,ha⟩
    · have heq : c.scope q.2.1 = v := by
        have h := congrArg Prod.fst ha
        simpa [substituteClause] using h.symm
      exact hiso c hc' q.2.1 heq
    · have heq : c.scope q.1.1 = v := by
        have h := congrArg Prod.fst ha
        simpa [substituteClause] using h.symm
      exact hiso c hc' q.1.1 heq
  have hdist (root : Literal V) : implicationDistance rep (thinnedInstance I mask) root (v,b) =
      implicationDistance rep (thinnedInstance I mask') root (v,b) := by
    rw [isolated_distance rep _ _ (hno mask), isolated_distance rep _ _ (hno mask')]
  unfold literalScore
  apply Finset.sup_congr rfl
  intro root hr
  rw [hdist]
