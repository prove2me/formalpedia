-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.isolated_subinstance_literal_score_eq_own_shift
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:10:38.967235+00:00
-- url     : https://prove2.me/submissions/0d331fe4-6b9d-4b0a-8942-c7522d1daefe

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
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (v : V)
    (hiso : ∀ c ∈ I.constraints, ∀ k : Fin c.rel.val.arity, c.scope k ≠ v)
    (G F : Instance Γ V) (hG : ∀ c ∈ G.constraints, c ∈ I.constraints)
    (hF : ∀ c ∈ F.constraints, c ∈ I.constraints) (δ : Literal V → ℝ) (b : Bool) :
    literalScore rep G F δ (v,b) =
      ((δ (v,b) : ℝ) : WithBot ℝ) := by
  classical
  have hf : feasibleLiteral F (v,b) := by
    obtain ⟨x,hx⟩ := hI
    let y := Function.update x v b
    have hy : Solution F y := by
      intro c hc
      have hc' := hF c hc
      have heq : (fun i => y (c.scope i)) = (fun i => x (c.scope i)) := by
        funext i
        simp [y,Function.update,hiso c hc' i]
      simpa [Constraint.Satisfied,heq] using hx c hc'
    refine ⟨y,hy,?_⟩
    simp [literalValue,y]
  have hno : ∀ a, ¬ implicationArc rep G a (v,b) := by
    intro a harc
    obtain ⟨c,hc,q,hq,ht,harc⟩ := harc
    have hc' := hG c hc
    rcases harc with ⟨_,ha⟩ | ⟨_,ha⟩
    · have heq : c.scope q.2.1 = v := by
        have h := congrArg Prod.fst ha
        simpa [substituteClause] using h.symm
      exact hiso c hc' q.2.1 heq
    · have heq : c.scope q.1.1 = v := by
        have h := congrArg Prod.fst ha
        simpa [substituteClause] using h.symm
      exact hiso c hc' q.1.1 heq
  have hd (root : Literal V) : implicationDistance rep G root (v,b) =
      if root = (v,b) then some 0 else none := isolated_distance rep G (v,b) hno root
  change literalScore rep G F δ (v,b) = ((δ (v,b) : ℝ) : WithBot ℝ)
  unfold literalScore
  apply le_antisymm
  · apply Finset.sup_le
    intro root hr
    by_cases he : root = (v,b)
    · subst root
      simp [hf,hd]
    · simp [hd,he]
  · apply Finset.le_sup_of_le (Finset.mem_univ (v,b))
    simp [hf,hd]
