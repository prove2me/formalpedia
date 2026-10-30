-- Prove2me | solution 1 for PutermanMDP.Unichain.policy_iteration_terminates
-- status  : ACCEPTED   (disprove)
-- author  : @queelius
-- created : 2026-10-29T15:46:22.715986+00:00
-- url     : https://prove2.me/submissions/60a4fedf-219f-4594-a3a5-9fce7f1dc47d

import Definitions.Def_PutermanMDP_Unichain_Iteration
import Mathlib
set_option autoImplicit false
namespace Queelius.UnichainCycle
open MarkovDecisionProcesses PutermanMDP.Unichain

def next (s : Fin 3) (a : Fin 2) : Fin 3 :=
  if s.val=0 then (if a.val=0 then 1 else 2) else if s.val=1 then (if a.val=0 then 0 else 2) else (if a.val=0 then 0 else 1)
def reward (s : Fin 3) (a : Fin 2) : ℝ :=
  if s.val=0 then (if a.val=0 then 0 else -1) else if s.val=1 then 0 else (if a.val=0 then 1 else 0)
def model : StationaryMDP (Fin 3) (Fin 2) where
  admissible _ := Finset.univ
  admissible_nonempty _ := Finset.univ_nonempty
  reward := reward
  trans s a j := if j=next s a then 1 else 0
  trans_nonneg _ _ _ := by split_ifs <;> norm_num
  trans_sum s a := by simp

lemma next_ne (s : Fin 3) (a : Fin 2) : next s a≠s := by
  fin_cases s <;> fin_cases a <;> decide

lemma three_unichain (P : Fin 3 → Fin 3 → ℝ)
    (hoff : ∀ i,∃ k,k≠i ∧ 0 < P i k) : IsUnichainMatrix P := by
  intro i j hi hj
  by_cases hij : i=j
  · subst j;exact Relation.ReflTransGen.refl
  obtain ⟨k,hki,hik⟩ := hoff i
  have hik' : Accessible P i k := Relation.ReflTransGen.single hik
  by_cases hkj : k=j
  · simpa only [hkj] using hik'
  obtain ⟨l,hlj,hjl⟩ := hoff j
  have hli : l=i ∨ l=k := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  have hjl' : Accessible P j l := Relation.ReflTransGen.single hjl
  have hji : Accessible P j i := by
    rcases hli with rfl | rfl
    · exact hjl'
    · exact hjl'.trans (hi _ hik')
  exact hj i hji

lemma model_unichain : IsUnichain model := by
  intro d hd
  apply three_unichain
  intro s
  exact ⟨next s (d s),next_ne s (d s),by simp [transMatrix,model]⟩

def actions (k : Fin 3) (s : Fin 3) : Fin 2 :=
  if k.val=0 then 0 else if k.val=1 then (if s.val=2 then 0 else 1) else (if s.val=0 then 0 else 1)
def bias (k : Fin 3) (s : Fin 3) : ℝ :=
  if k.val=0 then (if s.val=2 then 1 else 0) else if k.val=1 then (if s.val=0 then 0 else 1) else 0
def rule (k : Fin 3) : Rule model := ⟨actions k,fun s => Finset.mem_univ _⟩
def successor (k : Fin 3) : Fin 3 := ⟨(k.val+1)%3,Nat.mod_lt _ (by decide)⟩

lemma expectation (s : Fin 3) (a : Fin 2) (h : Fin 3 → ℝ) :
    (∑ j,model.trans s a j*h j)=h (next s a) := by
  change (∑ j : Fin 3,(if j=next s a then (1:ℝ) else 0)*h j)=h (next s a)
  simp

lemma evaluation (k : Fin 3) : Evaluates model (rule k) 0 (bias k) := by
  intro s
  rw [expectation]
  fin_cases k <;> fin_cases s <;>
    norm_num [model,rule,actions,bias,reward,next]

lemma dominates (k : Fin 3) (s : Fin 3) (a : Fin 2) :
    model.reward s a+∑ j,model.trans s a j*bias k j ≤
      model.reward s ((rule (successor k)).val s)+
        ∑ j,model.trans s ((rule (successor k)).val s) j*bias k j := by
  rw [expectation,expectation]
  fin_cases k <;> fin_cases s <;> fin_cases a <;>
    norm_num [model,rule,actions,bias,reward,next,successor]

lemma maximizing_next (k : Fin 3) : IsImproving model (bias k) (rule (successor k)).val := by
  intro s
  refine ⟨Finset.mem_univ _,le_antisymm ?_ ?_⟩
  · exact Finset.le_sup' (fun a : Fin 2 => model.reward s a+∑ j,model.trans s a j*bias k j) (show (rule (successor k)).val s ∈ model.admissible s from Finset.mem_univ _)
  · exact Finset.sup'_le _ _ (fun a ha => dominates k s a)

lemma improving_dominates (h : Fin 3 → ℝ) (d : Fin 3 → Fin 2)
    (hd : IsImproving model h d) (s : Fin 3) (a : Fin 2) :
    model.reward s a+∑ j,model.trans s a j*h j ≤ model.reward s (d s)+∑ j,model.trans s (d s) j*h j := by
  calc
    _ ≤ (model.admissible s).sup' (model.admissible_nonempty s)
      (fun a => model.reward s a+∑ j,model.trans s a j*h j) :=
      Finset.le_sup' _ (show a ∈ model.admissible s from Finset.mem_univ _)
    _ = _ := (hd s).2.symm

lemma incumbent_not_maximizing (k : Fin 3) : ¬IsImproving model (bias k) (rule k).val := by
  intro h
  have h0 := improving_dominates (bias k) (rule k).val h 0 0
  have h1 := improving_dominates (bias k) (rule k).val h 1 1
  have h2 := improving_dominates (bias k) (rule k).val h 2 0
  simp only [expectation] at h0 h1 h2
  fin_cases k
  · norm_num [model,rule,actions,bias,reward,next] at h1
  · norm_num [model,rule,actions,bias,reward,next] at h0
  · norm_num [model,rule,actions,bias,reward,next] at h2

lemma improvement (k : Fin 3) : Improves model (rule k) (rule (successor k)) (bias k) :=
  ⟨maximizing_next k,fun h => (incumbent_not_maximizing k h).elim⟩

lemma rule_changes (k : Fin 3) : rule (successor k)≠rule k := by
  intro h
  have h0 := congrArg (fun d : Rule model => (d.val 0).val) h
  have h1 := congrArg (fun d : Rule model => (d.val 1).val) h
  fin_cases k
  · norm_num [rule,actions,successor] at h0
  · norm_num [rule,actions,successor] at h0
  · norm_num [rule,actions,successor] at h1

def phase (n : ℕ) : Fin 3 := ⟨n%3,Nat.mod_lt _ (by decide)⟩
def policy (n : ℕ) : Rule model := rule (phase n)
def evaluationBias (n : ℕ) : Fin 3 → ℝ := bias (phase n)
lemma phase_succ (n : ℕ) : phase (n+1)=successor (phase n) := by
  apply Fin.ext
  simp [phase,successor,Nat.add_mod]

lemma infinite_run : IsRun model policy (fun _ => 0) evaluationBias := by
  constructor
  · intro n;exact evaluation (phase n)
  · intro n
    change Improves model (rule (phase n)) (rule (phase (n+1))) (bias (phase n))
    rw [phase_succ]
    exact improvement (phase n)
lemma never_stops (n : ℕ) : ¬StopsAt model policy n := by
  intro h
  have he := h.1
  change rule (phase (n+1))=rule (phase n) at he
  rw [phase_succ] at he
  exact rule_changes (phase n) he
end Queelius.UnichainCycle

theorem solution : (
  Not
    (∀ {S A : Type} [inst : Fintype S] [inst_1 : Fintype A] [inst_2 : DecidableEq A] [Nonempty S]
      (M : @MarkovDecisionProcesses.StationaryMDP S A inst inst_1),
      @MarkovDecisionProcesses.IsUnichain S A inst inst_1 M →
        ∀ (d₀ : @PutermanMDP.Unichain.Rule S A inst inst_1 M),
          And
            (@Exists (Nat → @PutermanMDP.Unichain.Rule S A inst inst_1 M)
              fun (d : Nat → @PutermanMDP.Unichain.Rule S A inst inst_1 M) =>
              @Exists (Nat → Real) fun (g : Nat → Real) =>
                @Exists (Nat → S → Real) fun (h : Nat → S → Real) =>
                  And
                    (@Eq (@PutermanMDP.Unichain.Rule S A inst inst_1 M)
                      (d (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) d₀)
                    (@PutermanMDP.Unichain.IsRun S A inst inst_1 M d g h))
            (∀ (d : Nat → @PutermanMDP.Unichain.Rule S A inst inst_1 M) (g : Nat → Real) (h : Nat → S → Real),
              @Eq (@PutermanMDP.Unichain.Rule S A inst inst_1 M)
                  (d (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) d₀ →
                @PutermanMDP.Unichain.IsRun S A inst inst_1 M d g h →
                  @Exists Nat fun (n : Nat) =>
                    And (@PutermanMDP.Unichain.StopsAt S A inst inst_1 M d n)
                      (And
                        (∀ (s : S),
                          @Eq Real (@MarkovDecisionProcesses.optimalityResidual S A inst inst_1 M (g n) (h n) s)
                            (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)))
                        (And
                          (@MarkovDecisionProcesses.IsAverageOptimal S A inst inst_1 M
                            (@MarkovDecisionProcesses.stationaryPolicy S A inst inst_1 M inst_2
                              (@Subtype.val (S → A)
                                (fun (d : S → A) =>
                                  ∀ (s : S),
                                    @Membership.mem A (Finset A)
                                      (@SetLike.instMembership (Finset A) A (@Finset.instSetLike A))
                                      (@MarkovDecisionProcesses.StationaryMDP.admissible S A inst inst_1 M s) (d s))
                                (d n))
                              (@Subtype.property (S → A)
                                (fun (d : S → A) =>
                                  ∀ (s : S),
                                    @Membership.mem A (Finset A)
                                      (@SetLike.instMembership (Finset A) A (@Finset.instSetLike A))
                                      (@MarkovDecisionProcesses.StationaryMDP.admissible S A inst inst_1 M s) (d s))
                                (d n))))
                          (∀ (s : S),
                            And (@Eq Real (@MarkovDecisionProcesses.optGainSup S A inst inst_1 M s) (g n))
                              (@Eq Real (@MarkovDecisionProcesses.optGainInf S A inst inst_1 M s) (g n)))))))
) := by
  intro hclaim
  have h := (hclaim Queelius.UnichainCycle.model Queelius.UnichainCycle.model_unichain
    (Queelius.UnichainCycle.rule 0)).2 Queelius.UnichainCycle.policy (fun _ => 0)
      Queelius.UnichainCycle.evaluationBias (by rfl) Queelius.UnichainCycle.infinite_run
  obtain ⟨n,hn,_⟩ := h
  exact Queelius.UnichainCycle.never_stops n hn
