-- Prove2me | solution 1 for ServiceParts.UnitDecomp.theorem4_decomposition
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:22:56.424245+00:00
-- url     : https://prove2.me/submissions/c5908fe6-e7d5-4649-8575-9f7e593d1b39

/- Exact whole-statement disproof of ServiceParts.UnitDecomp.theorem4_decomposition.
The Bellman recursion is reused from accepted submission ccf0d9ee-ba9f-4c2f-acf3-6896f9361da7.
The counterexample concerns nonmonotone tie-breaking under lowest-index matching. -/
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Definitions.Def_ServiceParts_UnitDecomp_System
import Mathlib.Probability.Distributions.Uniform

-- Bellman core reused from the accepted subsystem proof ccf0d9ee-ba9f-4c2f-acf3-6896f9361da7.

namespace ServiceParts.UnitDecomp.CounterexampleDP
open scoped ENNReal NNReal
variable {σ : Type} [Fintype σ]

noncomputable def V (M : Model σ) : ℕ → σ → SubState → ℝ≥0∞
  | 0, _, _ => 0
  | k + 1, s, x => min
      (∑' d : ℕ, M.demand s d * (M.subStage (M.subPost x Decision.release d) +
        (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * V M k s' (M.subPost x Decision.release d)))
      (∑' d : ℕ, M.demand s d * (M.subStage (M.subPost x Decision.hold d) +
        (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * V M k s' (M.subPost x Decision.hold d)))

noncomputable def Q (M : Model σ) (k : ℕ) (s : σ) (x : SubState) (a : Decision) : ℝ≥0∞ :=
  ∑' d : ℕ, M.demand s d * (M.subStage (M.subPost x a d) +
        (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * V M k s' (M.subPost x a d))

lemma V_succ (M : Model σ) (k : ℕ) (s : σ) (x : SubState) :
    V M (k + 1) s x = min (Q M k s x Decision.release) (Q M k s x Decision.hold) := rfl

lemma costToGo_succ (M : Model σ) (ρ : SubPolicy σ) (k n : ℕ) (s : σ) (x : SubState) :
    M.costToGo M.subPost M.subStage ρ (k + 1) n s x =
      ∑' d : ℕ, M.demand s d * (M.subStage (M.subPost x (ρ n s x) d) +
        (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' *
          M.costToGo M.subPost M.subStage ρ k (n + 1) s' (M.subPost x (ρ n s x) d)) := rfl

lemma V_le_cost (M : Model σ) (ρ : SubPolicy σ) (k : ℕ) :
    ∀ n s x, V M k s x ≤ M.costToGo M.subPost M.subStage ρ k n s x := by
  induction k with
  | zero => intros; simp [V]
  | succ k ih =>
    intro n s x
    rw [costToGo_succ, V_succ]
    have hQ : min (Q M k s x Decision.release) (Q M k s x Decision.hold) ≤ Q M k s x (ρ n s x) := by
      cases ρ n s x
      · exact min_le_left _ _
      · exact min_le_right _ _
    refine hQ.trans ?_
    refine ENNReal.tsum_le_tsum fun d => mul_le_mul' le_rfl (add_le_add le_rfl
      (mul_le_mul' le_rfl (Finset.sum_le_sum fun s' _ => mul_le_mul' le_rfl (ih _ _ _))))

lemma cost_of_greedy (M : Model σ) (N : ℕ) (ρ : SubPolicy σ) (P : SubState → Prop)
    (hP : ∀ x a d, P x → P (M.subPost x a d))
    (hg : ∀ n s x, n ≤ N → P x → Q M (N - n) s x (ρ n s x) = V M (N - n + 1) s x) :
    ∀ k n s x, k = N + 1 - n → P x →
      M.costToGo M.subPost M.subStage ρ k n s x = V M k s x := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro n s x hk hx
    have hn : n ≤ N := by omega
    have hk' : k = N - n := by omega
    rw [costToGo_succ, hk', ← hg n s x hn hx, Q]
    congr 1; funext d; congr 3; refine Finset.sum_congr rfl fun s' _ => ?_
    have := ih (n + 1) s' (M.subPost x (ρ n s x) d) (by omega) (hP _ _ _ hx)
    rw [hk'] at this; rw [this]

noncomputable def rstar (M : Model σ) (N : ℕ) : SubPolicy σ := fun n s x =>
  if Q M (N - n) s x Decision.release ≤ Q M (N - n) s x Decision.hold then Decision.release
  else Decision.hold

lemma subOpt_eq (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) :
    M.subOpt N n s x = V M (N + 1 - n) s x := by
  apply le_antisymm
  · refine iInf_le_of_le (rstar M N) (le_of_eq ?_)
    refine cost_of_greedy M N (rstar M N) (fun _ => True) (fun _ _ _ _ => trivial) ?_ _ n s x rfl trivial
    intro n s x _ _
    rw [V_succ, rstar]
    split_ifs with h
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
  · exact le_iInf fun ρ => V_le_cost M ρ _ n s x

end ServiceParts.UnitDecomp.CounterexampleDP


open scoped ENNReal NNReal
open ServiceParts.UnitDecomp Classical

namespace ServiceParts.UnitDecomp.Counterexample

noncomputable def M : Model Bool where
  trans _ := PMF.pure true
  demand s := if s then PMF.pure 0 else PMF.uniformOfFinset {0, 2} (by simp)
  m := 1
  h := 1
  b := 2
  α := 1
  one_le_m := by decide
  h_pos := by norm_num
  h_lt_b := by norm_num
  α_pos := by norm_num
  α_le_one := le_rfl

@[simp] lemma model_m : M.m = 1 := rfl
@[simp] lemma model_h : M.h = 1 := rfl
@[simp] lemma model_b : M.b = 2 := rfl
@[simp] lemma model_alpha : M.α = 1 := rfl
@[simp] lemma decision_hold_ne_release : Decision.hold ≠ Decision.release := by decide
@[simp] lemma decision_release_ne_hold : Decision.release ≠ Decision.hold := by decide
@[simp] lemma trans_true (s : Bool) : M.trans s true = 1 := by simp [M, PMF.pure_apply]
@[simp] lemma trans_false (s : Bool) : M.trans s false = 0 := by simp [M, PMF.pure_apply]
@[simp] lemma demand_B_apply (d : ℕ) : M.demand true d = if d = 0 then 1 else 0 := by
  simp [M, PMF.pure_apply]
@[simp] lemma encard_pair01 : ({0, 1} : Set ℕ).encard = 2 := Set.encard_pair (by decide)
@[simp] lemma set_pair01_imp : {i : ℕ | i ≠ 0 → i = 1} = {0, 1} := by
  ext i
  by_cases hi : i = 0 <;> simp [hi]
@[simp] lemma half_two : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
  ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
@[simp] lemma half_four : (2 : ℝ≥0∞)⁻¹ * 4 = 2 := by
  calc
    (2 : ℝ≥0∞)⁻¹ * 4 = 2⁻¹ * (2 * 2) := by congr 1; norm_num
    _ = 2 := ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)

lemma sysState_ext {x y : SysState} (hz : x.loc = y.loc) (hy : x.dist = y.dist) : x = y := by
  cases x
  cases y
  cases hz
  cases hy
  rfl

@[simp] lemma demand_A (f : ℕ → ℝ≥0∞) :
    ∑' d, M.demand false d * f d = (2 : ℝ≥0∞)⁻¹ * f 0 + (2 : ℝ≥0∞)⁻¹ * f 2 := by
  rw [tsum_eq_sum (s := ({0, 2} : Finset ℕ))]
  · norm_num [M, PMF.uniformOfFinset_apply]
  · intro d hd
    simp only [M, Bool.false_eq_true, ite_false, PMF.uniformOfFinset_apply]
    rw [if_neg hd, zero_mul]

@[simp] lemma demand_B (f : ℕ → ℝ≥0∞) : ∑' d, M.demand true d * f d = f 0 := by
  simp [M, PMF.pure_apply, ite_mul]

@[simp] lemma trans_sum (s : Bool) (f : Bool → ℝ≥0∞) : ∑ t, M.trans s t * f t = f true := by
  simp [M, PMF.pure_apply, ite_mul]

@[simp] lemma custMove_no_demand (y : ℕ) : custMove 0 y = y := by
  unfold custMove
  split_ifs <;> omega

@[simp] lemma V_one_B (x : SubState) :
    CounterexampleDP.V M 1 true x = min (M.subStage (M.subPost x Decision.release 0))
      (M.subStage (M.subPost x Decision.hold 0)) := by
  simp [CounterexampleDP.V]

@[simp] lemma Q_zero_B (x : SubState) (a : Decision) :
    CounterexampleDP.Q M 0 true x a = M.subStage (M.subPost x a 0) := by
  simp only [CounterexampleDP.Q, CounterexampleDP.V, mul_zero, Finset.sum_const_zero, add_zero]
  exact demand_B _

@[simp] lemma Q_one_A (x : SubState) (a : Decision) :
    CounterexampleDP.Q M 1 false x a =
      (2 : ℝ≥0∞)⁻¹ * (M.subStage (M.subPost x a 0) + CounterexampleDP.V M 1 true (M.subPost x a 0)) +
      (2 : ℝ≥0∞)⁻¹ * (M.subStage (M.subPost x a 2) + CounterexampleDP.V M 1 true (M.subPost x a 2)) := by
  simp [CounterexampleDP.Q]

lemma tie_at_two : CounterexampleDP.Q M 1 false (2, 2) Decision.hold = CounterexampleDP.V M 2 false (2, 2) := by
  rw [CounterexampleDP.V_succ]
  norm_num [Model.subPost, Model.subStage, unitMove, custMove]

/-- Break just one valid indifference in the otherwise Bellman-greedy policy. -/
noncomputable def rho : SubPolicy Bool := fun n s x =>
  if n = 1 ∧ s = false ∧ x = (2, 2) then Decision.hold else CounterexampleDP.rstar M 2 n s x

lemma rho_greedy (n : ℕ) (s : Bool) (x : SubState) :
    CounterexampleDP.Q M (2 - n) s x (rho n s x) = CounterexampleDP.V M (2 - n + 1) s x := by
  by_cases h : n = 1 ∧ s = false ∧ x = (2, 2)
  · rcases h with ⟨rfl, rfl, rfl⟩
    simpa [rho] using tie_at_two
  · simp only [rho, h, ite_false, CounterexampleDP.rstar, CounterexampleDP.V_succ]
    split_ifs with hQ
    · exact (min_eq_left hQ).symm
    · exact (min_eq_right (le_of_not_ge hQ)).symm

lemma rho_optimal (n : ℕ) (_hn : 1 ≤ n) (_hnN : n ≤ 2) (s : Bool) (x : SubState) :
    M.subCost 2 rho n s x = M.subOpt 2 n s x := by
  rw [CounterexampleDP.subOpt_eq, Model.subCost]
  exact CounterexampleDP.cost_of_greedy M 2 rho (fun _ => True) (fun _ _ _ _ => trivial)
    (fun n s x _ _ => rho_greedy n s x) _ n s x rfl trivial

lemma rho_first (y : ℕ) : rho 1 false (2, y) = Decision.release ↔ y = 1 ∨ y = 3 := by
  by_cases hy0 : y = 0
  · subst y
    norm_num [rho, CounterexampleDP.rstar, Model.subPost, Model.subStage, unitMove, custMove]
  by_cases hy1 : y = 1
  · subst y
    norm_num [rho, CounterexampleDP.rstar, Model.subPost, Model.subStage, unitMove, custMove]
  by_cases hy2 : y = 2
  · subst y
    norm_num [rho]
  by_cases hy3 : y = 3
  · subst y
    norm_num [rho, CounterexampleDP.rstar, Model.subPost, Model.subStage, unitMove, custMove]
  have hge : 4 ≤ y := by omega
  have hge2 : 2 ≤ y := by omega
  have hnot1 : ¬ y ≤ 1 := by omega
  have hnot3 : ¬ y ≤ 3 := by omega
  have hsub : y - 2 ≠ 1 := by omega
  simp [rho, CounterexampleDP.rstar, Model.subPost, Model.subStage, unitMove, custMove,
    hy0, hy1, hy2, hy3, hge2, hnot1, hnot3, hsub]

lemma rho_last (y : ℕ) : rho 2 true (2, y) = Decision.release ↔ y = 1 := by
  by_cases hy : y = 1 <;>
    simp [rho, CounterexampleDP.rstar, Model.subPost, Model.subStage, unitMove, hy]

def releaseSet (n : ℕ) (s : Bool) (x : SysState) : Set ℕ :=
  {j | x.loc j = 2 ∧ rho n s (x.loc j, x.dist j) = Decision.release}

noncomputable def badPolicy : SPolicy Bool where
  act n s x := if (releaseSet n s x).Finite then releaseSet n s x else ∅
  finite n s x := by split_ifs with h; exact h; exact Set.finite_empty

lemma badPolicy_follows (n : ℕ) (s : Bool) (x : SysState)
    (h : {j | x.loc j = M.m + 1 ∧ rho n s (x.loc j, x.dist j) = Decision.release}.Finite) :
    badPolicy.act n s x = {j | x.loc j = M.m + 1 ∧ rho n s (x.loc j, x.dist j) = Decision.release} := by
  exact if_pos h

noncomputable def x0 : SysState := M.initState (fun _ => 0) 0
def xNo : SysState := ⟨fun j => if j = 1 then 1 else 2, fun j => j + 2⟩
def xDemand : SysState := ⟨fun j => if j = 1 then 0 else 2, fun j => if j = 0 then 0 else j⟩
def xBacklog : SysState := ⟨fun _ => 2, fun j => if j < 2 then 1 else j⟩
def xClear : SysState := ⟨fun j => if j < 2 then 0 else 2, fun j => if j < 2 then 0 else j⟩
def xGoodNo : SysState := ⟨fun j => if j < 2 then 1 else 2, fun j => j + 2⟩

@[simp] lemma x0_loc (j : ℕ) : x0.loc j = 2 := by simp [x0, Model.initState]
@[simp] lemma x0_dist (j : ℕ) : x0.dist j = j + 2 := by simp [x0, Model.initState]

lemma badPolicy_first : badPolicy.act 1 false x0 = {1} := by
  have hs : releaseSet 1 false x0 = {1} := by
    ext j
    simp only [releaseSet, Set.mem_ofPred_eq, x0_loc, x0_dist, rho_first, true_and, Set.mem_singleton_iff]
    omega
  simp [badPolicy, hs]

lemma badPolicy_last_No : badPolicy.act 2 true xNo = ∅ := by
  have hs : releaseSet 2 true xNo = ∅ := by
    ext j
    by_cases hj : j = 1
    · simp [releaseSet, xNo, hj]
    · simp [releaseSet, xNo, hj, rho_last]
  simp [badPolicy, hs]

lemma badPolicy_last_Demand : badPolicy.act 2 true xDemand = ∅ := by
  have hs : releaseSet 2 true xDemand = ∅ := by
    ext j
    by_cases hj : j = 1
    · simp [releaseSet, xDemand, hj]
    · by_cases hj0 : j = 0
      · simp [releaseSet, xDemand, hj0, rho_last]
      · simp [releaseSet, xDemand, hj, hj0, rho_last]
  simp [badPolicy, hs]

@[simp] lemma unitMove_hold (z : ℕ) : unitMove 1 z false = z := by
  unfold unitMove
  split_ifs <;> simp_all <;> omega

lemma post_empty_noWaiting (x : SysState) (hy : ∀ j, x.dist j ≠ 1) :
    M.sysPost x ∅ 0 = x := by
  have hset : {i | x.dist i = 1} = ∅ := by ext i; simp [hy]
  apply sysState_ext <;> funext j <;>
    simp [Model.sysPost, hy, hset]

lemma post_empty_noStock (x : SysState) (hz : ∀ j, x.loc j ≠ 1) :
    M.sysPost x ∅ 0 = x := by
  have hset : {i | x.loc i = 1} = ∅ := by ext i; simp [hz]
  apply sysState_ext <;> funext j <;>
    simp [Model.sysPost, hz, hset]

lemma x0_move_stock_one : {i | unitMove M.m (x0.loc i) (decide (i ∈ ({1} : Set ℕ))) = 1} = {1} := by
  ext i
  by_cases hi : i = 1 <;> simp [unitMove, hi]

lemma x0_move_stock_two : {i | unitMove M.m (x0.loc i) (decide (i ∈ ({0, 1} : Set ℕ))) = 1} = {0, 1} := by
  ext i
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> simp [unitMove, hi0, hi1]

lemma x0_move_wait_none : {i | custMove 0 (x0.dist i) = 1} = ∅ := by
  ext i
  simp

lemma x0_move_wait_two : {i | custMove 2 (x0.dist i) = 1} = {0, 1} := by
  ext i
  simp only [x0_dist, custMove, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  split_ifs <;> omega

lemma post_first_No : M.sysPost x0 {1} 0 = xNo := by
  apply sysState_ext <;> funext j
  · simp only [Model.sysPost, x0_move_wait_none, Set.encard_empty]
    by_cases hj : j = 1 <;> simp [unitMove, xNo, hj]
  · simp only [Model.sysPost, x0_move_stock_one, Set.encard_singleton]
    simp [xNo]

lemma post_first_Demand : M.sysPost x0 {1} 2 = xDemand := by
  apply sysState_ext <;> funext j
  · simp only [Model.sysPost, x0_move_wait_two]
    by_cases hj : j = 1
    · subst j
      norm_num [unitMove, rankIn, xDemand]
    · simp [unitMove, xDemand, hj]
  · simp only [Model.sysPost, x0_move_stock_one, Set.encard_singleton]
    by_cases hj0 : j = 0
    · subst j
      norm_num [custMove, unitMove, rankIn, Finset.filter_singleton, xDemand]
    by_cases hj1 : j = 1
    · subst j
      norm_num [custMove, unitMove, rankIn, Finset.filter_singleton, xDemand]
    have hjge : 2 ≤ j := by omega
    have hgt : ¬ j + 2 ≤ 3 := by omega
    simp [custMove, xDemand, hj0, hj1, hgt]

lemma post_good_No : M.sysPost x0 {0, 1} 0 = xGoodNo := by
  apply sysState_ext <;> funext j
  · simp only [Model.sysPost, x0_move_wait_none, Set.encard_empty]
    by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;>
      simp [unitMove, xGoodNo, hj0, hj1] <;> omega
  · simp only [Model.sysPost, x0_move_stock_two]
    simp [xGoodNo]

lemma post_good_Demand : M.sysPost x0 {0, 1} 2 = xClear := by
  apply sysState_ext <;> funext j
  · simp only [Model.sysPost, x0_move_wait_two]
    by_cases hj0 : j = 0
    · subst j
      norm_num [unitMove, rankIn, Finset.filter_singleton, xClear]
    by_cases hj1 : j = 1
    · subst j
      norm_num [unitMove, rankIn, Finset.filter_singleton, xClear]
    have hge : ¬ j < 2 := by omega
    simp [unitMove, xClear, hj0, hj1, hge]
    omega
  · simp only [Model.sysPost, x0_move_stock_two]
    by_cases hj0 : j = 0
    · subst j
      norm_num [custMove, unitMove, rankIn, Finset.filter_singleton, xClear]
    by_cases hj1 : j = 1
    · subst j
      norm_num [custMove, unitMove, rankIn, Finset.filter_singleton, xClear]
    have hjge : ¬ j < 2 := by omega
    have hgt : ¬ j + 2 ≤ 3 := by omega
    simp [custMove, xClear, hj0, hj1, hjge, hgt]
    omega

@[simp] lemma post_No_stays : M.sysPost xNo ∅ 0 = xNo := by
  apply post_empty_noWaiting
  intro j
  simp [xNo]

@[simp] lemma post_Demand_stays : M.sysPost xDemand ∅ 0 = xDemand := by
  apply post_empty_noStock
  intro j
  by_cases hj : j = 1 <;> simp [xDemand, hj]

@[simp] lemma post_GoodNo_stays : M.sysPost xGoodNo ∅ 0 = xGoodNo := by
  apply post_empty_noWaiting
  intro j
  simp [xGoodNo]

@[simp] lemma post_Clear_stays : M.sysPost xClear ∅ 0 = xClear := by
  apply post_empty_noStock
  intro j
  dsimp only [xClear]
  split_ifs <;> norm_num

@[simp] lemma stage_No : M.sysStage xNo = 1 := by
  have hz : {j | xNo.loc j = 1} = {1} := by
    ext j
    by_cases hj : j = 1 <;> simp [xNo, hj]
  have hy : {j | xNo.dist j = 1} = ∅ := by ext j; simp [xNo]
  simp [Model.sysStage, hz, hy]

@[simp] lemma stage_Demand : M.sysStage xDemand = 2 := by
  have hz : {j | xDemand.loc j = 1} = ∅ := by
    ext j
    by_cases hj : j = 1 <;> simp [xDemand, hj]
  have hy : {j | xDemand.dist j = 1} = {1} := by
    ext j
    by_cases hj : j = 0 <;> simp [xDemand, hj]
  simp [Model.sysStage, hz, hy]

@[simp] lemma stage_GoodNo : M.sysStage xGoodNo = 2 := by
  have hz : {j | xGoodNo.loc j = 1} = {0, 1} := by
    ext j
    simp only [xGoodNo, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs <;> omega
  have hy : {j | xGoodNo.dist j = 1} = ∅ := by ext j; simp [xGoodNo]
  norm_num [Model.sysStage, hz, hy]

@[simp] lemma stage_Clear : M.sysStage xClear = 0 := by
  have hz : {j | xClear.loc j = 1} = ∅ := by
    ext j
    simp only [xClear, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    split_ifs <;> norm_num
  have hy : {j | xClear.dist j = 1} = ∅ := by
    ext j
    simp only [xClear, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    split_ifs <;> simp_all <;> omega
  simp [Model.sysStage, hz, hy]

def goodPolicy : SPolicy Bool where
  act n _ _ := if n = 1 then {0, 1} else ∅
  finite n _ _ := by split_ifs <;> simp

lemma badPolicy_cost : M.sysCost 2 badPolicy 1 false x0 = 3 := by
  norm_num [Model.sysCost, Model.costToGo, badPolicy_first, post_first_No, post_first_Demand,
    badPolicy_last_No, badPolicy_last_Demand]

lemma goodPolicy_cost : M.sysCost 2 goodPolicy 1 false x0 = 2 := by
  norm_num [Model.sysCost, Model.costToGo, goodPolicy, post_good_No, post_good_Demand]

end ServiceParts.UnitDecomp.Counterexample

open ServiceParts.UnitDecomp.Counterexample

theorem solution : ¬ (∀ {σ : Type} [Fintype σ] (M : Model σ) (N : ℕ),
    (∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
      M.sysOpt N 1 s (M.initState a v₀) =
        ∑' w : ℕ, M.subOpt N 1 s ((M.initState a v₀).loc w, (M.initState a v₀).dist w)) ∧
    ∀ ρ : SubPolicy σ,
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SubState),
        M.subCost N ρ n s x = M.subOpt N n s x) →
      ∀ π : SPolicy σ,
        (∀ (n : ℕ) (s : σ) (x : SysState),
          {j | x.loc j = M.m + 1 ∧ ρ n s (x.loc j, x.dist j) = Decision.release}.Finite →
            π.act n s x = {j | x.loc j = M.m + 1 ∧ ρ n s (x.loc j, x.dist j) = Decision.release}) →
        ∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
          M.sysCost N π 1 s (M.initState a v₀) = M.sysOpt N 1 s (M.initState a v₀)) := by
  intro h
  have hb := (@h Bool inferInstance Counterexample.M 2).2 rho rho_optimal badPolicy
    badPolicy_follows false (fun _ => 0) 0
  change Counterexample.M.sysCost 2 badPolicy 1 false x0 =
    Counterexample.M.sysOpt 2 1 false x0 at hb
  have hc : Counterexample.M.sysOpt 2 1 false x0 ≤ 2 :=
    (iInf_le _ goodPolicy).trans_eq goodPolicy_cost
  rw [badPolicy_cost] at hb
  have hbad : (3 : ℝ≥0∞) ≤ 2 := hb.le.trans hc
  norm_num at hbad
