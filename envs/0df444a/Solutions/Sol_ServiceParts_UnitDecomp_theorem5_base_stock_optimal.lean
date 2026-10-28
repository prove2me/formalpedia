-- Prove2me | solution 1 for ServiceParts.UnitDecomp.theorem5_base_stock_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:58:45.706086+00:00
-- url     : https://prove2.me/submissions/2824a0b9-0b2e-42c9-968e-a6a05bc9e037

/- Corrected exact Theorem 5 reduction. The sole open theorem dependency is
Lemma 1; the disproved Theorem 4 is not used. Standalone diagnostic candidate. -/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Lean.Elab.Tactic.Omega
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem
import Definitions.Def_ServiceParts_UnitDecomp_System
import Mathlib.Tactic.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_ServiceParts_UnitDecomp_lemma1_monotone_committed

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_SubsystemCore.lean -/
-- Local reuse of the verified subsystem proof cached as critical_accepted.lean.



namespace ServiceParts.UnitDecomp

open scoped ENNReal NNReal

variable {σ : Type} [Fintype σ]

namespace SPD

def mt (w y : ℕ) : SubState := if w = 1 ∧ y = 1 then (0, 0) else (w, y)

def tpost (x : SubState) (d : ℕ) : SubState :=
  mt (if 2 ≤ x.1 then x.1 - 1 else x.1) (custMove d x.2)

noncomputable def U (M : Model σ) : ℕ → σ → SubState → ℝ≥0∞
  | 0, _, _ => 0
  | k + 1, s, x => ∑' d : ℕ, M.demand s d *
      (M.subStage (tpost x d) + (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * U M k s' (tpost x d))

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

lemma subPost_eq (M : Model σ) (x : SubState) (a : Decision) (d : ℕ) :
    M.subPost x a d = mt (unitMove M.m x.1 (decide (a = Decision.release))) (custMove d x.2) := by
  rfl

/-- combination lemma -/
lemma comb {ι : Type*} (p : ι → ℝ≥0∞) (f1 f2 g1 g2 : ι → ℝ≥0∞)
    (h : ∀ i, f1 i + f2 i ≤ g1 i + g2 i) :
    ∑' i, p i * f1 i + ∑' i, p i * f2 i ≤ ∑' i, p i * g1 i + ∑' i, p i * g2 i := by
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← mul_add, ← mul_add]
  exact mul_le_mul' le_rfl (h i)

lemma combF (p : σ → ℝ≥0∞) (c : ℝ≥0∞) (f1 f2 g1 g2 : σ → ℝ≥0∞)
    (h : ∀ i, f1 i + f2 i ≤ g1 i + g2 i) :
    c * ∑ i, p i * f1 i + c * ∑ i, p i * f2 i ≤ c * ∑ i, p i * g1 i + c * ∑ i, p i * g2 i := by
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_add, ← mul_add]
  exact mul_le_mul' le_rfl (h i)

lemma add4 {a b c d e f g h : ℝ≥0∞} (h1 : a + c ≤ e + g) (h2 : b + d ≤ f + h) :
    (a + b) + (c + d) ≤ (e + f) + (g + h) := by
  calc (a + b) + (c + d) = (a + c) + (b + d) := add_add_add_comm _ _ _ _
    _ ≤ (e + g) + (f + h) := add_le_add h1 h2
    _ = (e + f) + (g + h) := add_add_add_comm _ _ _ _

lemma custMove_mono (d : ℕ) {y y' : ℕ} (h : y ≤ y') : custMove d y ≤ custMove d y' := by
  unfold custMove; split_ifs <;> omega

lemma custMove_pos (d : ℕ) {y : ℕ} (h : 1 ≤ y) : 1 ≤ custMove d y := by
  unfold custMove; split_ifs <;> omega

lemma stage_ineq (M : Model σ) {w y y' : ℕ} (hw : 1 ≤ w) (hy : 1 ≤ y) (hyy : y ≤ y') :
    M.subStage (mt w y) + M.subStage (mt (w + 1) y') ≤
      M.subStage (mt w y') + M.subStage (mt (w + 1) y) := by
  unfold mt Model.subStage
  by_cases hw1 : w = 1 <;> by_cases h1 : y = 1 <;> by_cases h2 : y' = 1 <;>
    simp [hw1, h1, h2, show w ≠ 0 by omega] <;> omega


lemma custMove_zero (d : ℕ) : custMove d 0 = 0 := by unfold custMove; simp
lemma custMove_one (d : ℕ) : custMove d 1 = 1 := by unfold custMove; simp

lemma U_zero_zero (M : Model σ) (k : ℕ) (s : σ) : U M k s (0, 0) = 0 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [U, tpost, custMove_zero]
    simp [mt, Model.subStage, ih]

lemma U_one_one (M : Model σ) (k : ℕ) (s : σ) : U M k s (1, 1) = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [U, tpost, custMove_one]
    simp [mt, Model.subStage, U_zero_zero]

lemma U_mt (M : Model σ) (k : ℕ) (s : σ) (w y : ℕ) : U M k s (mt w y) = U M k s (w, y) := by
  unfold mt; split_ifs with h
  · rw [h.1, h.2, U_zero_zero, U_one_one]
  · rfl

lemma stage_le (M : Model σ) (x : SubState) : M.subStage x ≤ (M.h : ℝ≥0∞) + M.b := by
  unfold Model.subStage
  gcongr <;> split_ifs <;> simp

lemma step_bound (M : Model σ) (s : σ) (W : σ → SubState → ℝ≥0∞) (c : ℝ≥0∞)
    (hW : ∀ s x, W s x ≤ c) (f : ℕ → SubState) :
    ∑' d : ℕ, M.demand s d * (M.subStage (f d) + (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * W s' (f d))
      ≤ ((M.h : ℝ≥0∞) + M.b) + c := by
  have hα : (M.α : ℝ≥0∞) ≤ 1 := by exact_mod_cast M.α_le_one
  have hT : ∑ s' : σ, M.trans s s' = 1 := by
    have := (M.trans s).tsum_coe; rwa [tsum_fintype] at this
  calc _ ≤ ∑' d : ℕ, M.demand s d * (((M.h : ℝ≥0∞) + M.b) + c) := by
        refine ENNReal.tsum_le_tsum fun d => mul_le_mul' le_rfl (add_le_add (stage_le M _) ?_)
        calc (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' * W s' (f d)
            ≤ 1 * ∑ s' : σ, M.trans s s' * c :=
              mul_le_mul' hα (Finset.sum_le_sum fun s' _ => mul_le_mul' le_rfl (hW _ _))
          _ = c := by rw [one_mul, ← Finset.sum_mul, hT, one_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, (M.demand s).tsum_coe, one_mul]

lemma U_bound (M : Model σ) (k : ℕ) : ∀ s x, U M k s x ≤ k * ((M.h : ℝ≥0∞) + M.b) := by
  induction k with
  | zero => intro s x; simp [U]
  | succ k ih =>
    intro s x
    refine (step_bound M s (U M k) _ ih _).trans (le_of_eq ?_)
    push_cast; ring

lemma V_bound (M : Model σ) (k : ℕ) : ∀ s x, V M k s x ≤ k * ((M.h : ℝ≥0∞) + M.b) := by
  induction k with
  | zero => intro s x; simp [V]
  | succ k ih =>
    intro s x
    refine (min_le_left _ _).trans ((step_bound M s (V M k) _ ih _).trans (le_of_eq ?_))
    push_cast; ring

lemma Q_bound (M : Model σ) (k : ℕ) (s : σ) (x : SubState) (a : Decision) :
    Q M k s x a ≤ ((M.h : ℝ≥0∞) + M.b) + k * ((M.h : ℝ≥0∞) + M.b) :=
  step_bound M s (V M k) _ (V_bound M k) _

lemma fin_of_bound {a : ℝ≥0∞} {k : ℕ} {h b : ℝ≥0} (ha : a ≤ k * ((h : ℝ≥0∞) + b)) : a ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top]) ha

lemma U_ne_top (M : Model σ) (k : ℕ) (s : σ) (x : SubState) : U M k s x ≠ ⊤ :=
  fin_of_bound (U_bound M k s x)

lemma Q_ne_top (M : Model σ) (k : ℕ) (s : σ) (x : SubState) (a : Decision) : Q M k s x a ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top]) (Q_bound M k s x a)

lemma delta (M : Model σ) (k : ℕ) : ∀ (s : σ) (z y y' : ℕ), 1 ≤ z → 1 ≤ y → y ≤ y' →
    U M k s (z, y) + U M k s (z + 1, y') ≤ U M k s (z, y') + U M k s (z + 1, y) := by
  induction k with
  | zero => intros; simp [U]
  | succ k ih =>
    intro s z y y' hz hy hyy
    simp only [U]
    apply comb
    intro d
    rcases (by omega : z = 1 ∨ 2 ≤ z) with rfl | hz2
    · have e : ∀ y, tpost (1 + 1, y) d = tpost (1, y) d := by
        intro y; simp [tpost]
      rw [e, e]
      apply add4
      · rw [add_comm]
      · apply combF; intro s'; rw [add_comm]
    · have e1 : ∀ y, tpost (z, y) d = mt (z - 1) (custMove d y) := by
        intro y; simp only [tpost]; rw [if_pos hz2]
      have e2 : ∀ y, tpost (z + 1, y) d = mt (z - 1 + 1) (custMove d y) := by
        intro y; simp only [tpost]; rw [if_pos (by omega)]; congr 1; omega
      rw [e1, e1, e2, e2]
      apply add4
      · exact stage_ineq M (by omega) (custMove_pos d hy) (custMove_mono d hyy)
      · apply combF; intro s'
        rw [U_mt, U_mt, U_mt, U_mt]
        exact ih s' (z - 1) _ _ (by omega) (custMove_pos d hy) (custMove_mono d hyy)


lemma mt_fst_le (w y : ℕ) : (mt w y).1 ≤ w := by
  unfold mt; split_ifs <;> simp

lemma subPost_low (M : Model σ) (x : SubState) (hx : x.1 ≤ M.m) (a : Decision) (d : ℕ) :
    M.subPost x a d = tpost x d := by
  rw [subPost_eq, tpost]; unfold unitMove
  congr 1
  by_cases h2 : 2 ≤ x.1
  · simp [h2, hx]
  · simp [h2]; omega

lemma tpost_low (M : Model σ) (x : SubState) (hx : x.1 ≤ M.m) (d : ℕ) : (tpost x d).1 ≤ M.m := by
  unfold tpost
  refine (mt_fst_le _ _).trans ?_
  split_ifs <;> omega

lemma subPost_rel (M : Model σ) (y d : ℕ) :
    M.subPost (M.m + 1, y) Decision.release d = mt M.m (custMove d y) := by
  rw [subPost_eq]; unfold unitMove; simp

lemma subPost_hold (M : Model σ) (y d : ℕ) :
    M.subPost (M.m + 1, y) Decision.hold d = (M.m + 1, custMove d y) := by
  rw [subPost_eq]; unfold unitMove mt; have := M.one_le_m; simp; omega

lemma V_eq_U (M : Model σ) (k : ℕ) : ∀ s x, x.1 ≤ M.m → V M k s x = U M k s x := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro s x hx
    have hQ : ∀ a, Q M k s x a = U M (k + 1) s x := by
      intro a
      simp only [Q, U, subPost_low M x hx]
      congr 1; funext d; congr 3; refine Finset.sum_congr rfl fun s' _ => ?_
      rw [ih s' _ (tpost_low M x hx d)]
    rw [V_succ, hQ, hQ, min_self]

lemma Qrel_eq (M : Model σ) (k : ℕ) (s : σ) (y : ℕ) :
    Q M k s (M.m + 1, y) Decision.release = U M (k + 1) s (M.m + 1, y) := by
  have ht : ∀ d, tpost (M.m + 1, y) d = mt M.m (custMove d y) := by
    intro d; simp [tpost, M.one_le_m]
  simp only [Q, U, subPost_rel, ht]
  congr 1; funext d; congr 3; refine Finset.sum_congr rfl fun s' _ => ?_
  rw [V_eq_U M k s' _ (mt_fst_le _ _)]

lemma GStar (M : Model σ) (k : ℕ) :
    (∀ s y y', 1 ≤ y → y ≤ y' →
      U M k s (M.m + 1, y) + V M k s (M.m + 1, y') ≤ U M k s (M.m + 1, y') + V M k s (M.m + 1, y)) ∧
    (∀ s y y', 1 ≤ y → y ≤ y' →
      Q M k s (M.m + 1, y) Decision.release + Q M k s (M.m + 1, y') Decision.hold ≤
        Q M k s (M.m + 1, y') Decision.release + Q M k s (M.m + 1, y) Decision.hold) := by
  have star : ∀ k, (∀ s y y', 1 ≤ y → y ≤ y' →
      U M k s (M.m + 1, y) + V M k s (M.m + 1, y') ≤ U M k s (M.m + 1, y') + V M k s (M.m + 1, y)) →
    (∀ s y y', 1 ≤ y → y ≤ y' →
      Q M k s (M.m + 1, y) Decision.release + Q M k s (M.m + 1, y') Decision.hold ≤
        Q M k s (M.m + 1, y') Decision.release + Q M k s (M.m + 1, y) Decision.hold) := by
    intro k G s y y' hy hyy
    simp only [Q, subPost_rel, subPost_hold]
    apply comb
    intro d
    have h1 := custMove_pos d hy
    have h2 := custMove_mono d hyy
    have hm1 : ∀ y, mt (M.m + 1) y = (M.m + 1, y) := by
      intro y; unfold mt; have := M.one_le_m; simp; omega
    apply add4
    · have := stage_ineq M M.one_le_m h1 h2
      rwa [hm1, hm1] at this
    · apply combF; intro s'
      rw [V_eq_U M k s' _ (mt_fst_le _ _), V_eq_U M k s' _ (mt_fst_le _ _), U_mt, U_mt]
      have hd := delta M k s' M.m _ _ M.one_le_m h1 h2
      have hg := G s' _ _ h1 h2
      have hfin : U M k s' (M.m + 1, custMove d y') + U M k s' (M.m + 1, custMove d y) ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨U_ne_top _ _ _ _, U_ne_top _ _ _ _⟩
      refine ENNReal.le_of_add_le_add_right hfin ?_
      calc _ = (U M k s' (M.m, custMove d y) + U M k s' (M.m + 1, custMove d y')) +
            (U M k s' (M.m + 1, custMove d y) + V M k s' (M.m + 1, custMove d y')) := by ring
        _ ≤ (U M k s' (M.m, custMove d y') + U M k s' (M.m + 1, custMove d y)) +
            (U M k s' (M.m + 1, custMove d y') + V M k s' (M.m + 1, custMove d y)) :=
              add_le_add hd hg
        _ = _ := by ring
  have G : ∀ k, ∀ s y y', 1 ≤ y → y ≤ y' →
      U M k s (M.m + 1, y) + V M k s (M.m + 1, y') ≤ U M k s (M.m + 1, y') + V M k s (M.m + 1, y) := by
    intro k
    induction k with
    | zero => intros; simp [U, V]
    | succ k ih =>
      intro s y y' hy hyy
      have hs := star k ih s y y' hy hyy
      rw [← Qrel_eq, ← Qrel_eq, V_succ, V_succ]
      rcases le_total (Q M k s (M.m + 1, y) Decision.release) (Q M k s (M.m + 1, y) Decision.hold)
        with hc | hc
      · rw [min_eq_left hc, add_comm (Q M k s (M.m + 1, y') Decision.release)]
        exact add_le_add le_rfl (min_le_left _ _)
      · rw [min_eq_right hc]
        exact (add_le_add le_rfl (min_le_right _ _)).trans hs
  exact ⟨G k, star k (G k)⟩


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

lemma subQ_eq (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) (a : Decision) :
    M.subQ N n s x a = Q M (N - n) s x a := by
  simp only [Model.subQ, Q, subOpt_eq, Nat.add_sub_add_right]

lemma down_closed (M : Model σ) (N n : ℕ) (s : σ) {y y'' : ℕ} (hy : 1 ≤ y) (hyy : y ≤ y'')
    (h : Decision.release ∈ M.optDecisions N n s y'') :
    Decision.release ∈ M.optDecisions N n s y := by
  simp only [Model.optDecisions, Set.mem_setOf_eq, subQ_eq] at h ⊢
  intro a'
  cases a'
  · exact le_rfl
  · have hs := (GStar M (N - n)).2 s y y'' hy hyy
    have h2 := h Decision.hold
    refine ENNReal.le_of_add_le_add_right (Q_ne_top M (N - n) s (M.m + 1, y'') Decision.hold) ?_
    rw [add_comm (Q M (N - n) s (M.m + 1, y) Decision.hold)]
    exact hs.trans (add_le_add h2 le_rfl)

theorem lemma2_core {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (s : σ) (y : ℕ) (hy : 1 ≤ y)
    (hrel : M.optDecisions N n s (y + 1) = {Decision.release}) :
    Decision.release ∈ M.optDecisions N n s y :=
  down_closed M N n s hy (Nat.le_succ y) (by rw [hrel]; rfl)

lemma unitMove_ne (m z : ℕ) (r : Bool) (hz : z ≠ m + 1) : unitMove m z r ≠ m + 1 := by
  unfold unitMove; split_ifs <;> omega

lemma unitMove_indep (m z : ℕ) (r r' : Bool) (hz : z ≠ m + 1) : unitMove m z r = unitMove m z r' := by
  unfold unitMove; split_ifs <;> simp_all

theorem crit_core {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (s : σ) (z y : ℕ) (hzy : z = M.m + 1 → 1 ≤ y) :
    M.subCost N (M.criticalPolicy N) n s (z, y) = M.subOpt N n s (z, y) := by
  rw [subOpt_eq, Model.subCost]
  refine cost_of_greedy M N _ (fun x => x.1 = M.m + 1 → 1 ≤ x.2) ?_ ?_ _ n s _ rfl hzy
  · intro x a d hx hx'
    rw [subPost_eq] at hx' ⊢
    by_cases h : x.1 = M.m + 1
    · have hx2 := hx h
      cases a
      · exfalso
        have hu : unitMove M.m x.1 (decide (Decision.release = Decision.release)) = M.m := by
          rw [h]; simp [unitMove]
        rw [hu] at hx'
        have := mt_fst_le M.m (custMove d x.2)
        omega
      · rw [h] at hx' ⊢
        unfold unitMove mt at hx' ⊢
        have := M.one_le_m
        simp at hx' ⊢
        split_ifs at hx' ⊢ <;> simp_all <;> exact custMove_pos d hx2
    · exfalso
      have h1 := unitMove_ne M.m x.1 (decide (a = Decision.release)) h
      unfold mt at hx'; split_ifs at hx' <;> simp_all
  · intro n s x hn hx
    rw [V_succ]
    by_cases h : x.1 = M.m + 1
    · obtain ⟨z, y⟩ := x
      simp only at h; subst h
      have hy := hx rfl
      have hopt : ∀ a, Q M (N - n) s (M.m + 1, y) a = M.subQ N n s (M.m + 1, y) a := by
        intro a; rw [subQ_eq]
      simp only [Model.criticalPolicy]
      split_ifs with hc
      · have hmem : Decision.release ∈ M.optDecisions N n s y := by
          by_contra hne
          have : M.criticalDistance N n s ≤ ((y - 1 : ℕ) : ℕ∞) := by
            refine iSup₂_le fun y'' hy'' => ?_
            have : y'' < y := by
              by_contra hge
              exact hne (down_closed M N n s hy (by omega) hy'')
            exact_mod_cast (by omega : y'' ≤ y - 1)
          have := hc.trans this
          have : y ≤ y - 1 := by exact_mod_cast this
          omega
        have := hmem Decision.hold
        rw [← hopt, ← hopt] at this
        rw [min_eq_left this]
      · have hmem : Decision.release ∉ M.optDecisions N n s y := by
          intro hm
          exact hc (le_iSup₂_of_le (f := fun (y : ℕ) (_ : Decision.release ∈ M.optDecisions N n s y) =>
            (y : ℕ∞)) y hm le_rfl)
        have : ¬ (Q M (N - n) s (M.m + 1, y) Decision.release ≤
            Q M (N - n) s (M.m + 1, y) Decision.hold) := by
          intro hle
          apply hmem
          intro a'
          rw [← hopt, ← hopt]
          cases a'
          · exact le_rfl
          · exact hle
        rw [min_eq_right (le_of_not_ge this)]
    · have : Q M (N - n) s x Decision.release = Q M (N - n) s x Decision.hold := by
        simp only [Q, subPost_eq, unitMove_indep M.m x.1 _ false h]
      have h2 : ∀ a, Q M (N - n) s x a = Q M (N - n) s x Decision.hold := by
        intro a; cases a
        · exact this
        · rfl
      rw [h2, this, min_self]

end SPD
end ServiceParts.UnitDecomp
/- END INLINED Sol_ServiceParts_UnitDecomp_SubsystemCore.lean -/

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_Foundations.lean -/
open scoped ENNReal NNReal
open ServiceParts.UnitDecomp
open Classical

namespace ServiceParts.UnitDecomp.Proof

lemma rankIn_lt_encard {p : ℕ → Prop} [DecidablePred p] {j : ℕ} (hj : p j) :
    (rankIn p j : ℕ∞) < {i | p i}.encard := by
  classical
  have hs : (↑((Finset.range j).filter p) : Set ℕ) ⊂ {i | p i} := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro heq
      have : j ∈ ((Finset.range j).filter p : Finset ℕ) := by
        change j ∈ (↑((Finset.range j).filter p) : Set ℕ)
        rw [heq]
        exact hj
      exact (Nat.lt_irrefl j) (Finset.mem_range.mp (Finset.mem_filter.mp this).1)
  simpa only [rankIn, Set.encard_coe_eq_coe_finsetCard] using
    ((Finset.finite_toSet _).encard_lt_encard hs)

lemma encard_le_rankIn {p q : ℕ → Prop} [DecidablePred p] {j : ℕ}
    (h : ∀ i, q i → i < j ∧ p i) :
    {i | q i}.encard ≤ (rankIn p j : ℕ∞) := by
  have hsub : {i | q i} ⊆ (↑((Finset.range j).filter p) : Set ℕ) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (h i hi).1, (h i hi).2⟩
  simpa only [rankIn, Set.encard_coe_eq_coe_finsetCard] using Set.encard_mono hsub

/-- In an ordered state with identically indexed consumed units and customers,
lowest-index matching agrees with pairing each unit with its own customer. -/
lemma match_iff (z y : ℕ → ℕ) (hz : Monotone z) (hy : Monotone y)
    (hzero : ∀ i, z i = 0 ↔ y i = 0) (j : ℕ) :
    (z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard) ↔
      z j = 1 ∧ y j = 1 := by
  constructor
  · rintro ⟨hzj, hlt⟩
    refine ⟨hzj, ?_⟩
    have hy0 : y j ≠ 0 := by simpa [hzj] using (hzero j).symm
    by_contra hy1
    have hbound : {i | y i = 1}.encard ≤ (rankIn (fun i => z i = 1) j : ℕ∞) := by
      apply encard_le_rankIn
      intro i hi
      have hij : i < j := by
        by_contra h
        have := hy (Nat.le_of_not_gt h)
        omega
      refine ⟨hij, ?_⟩
      have hzi := hz (Nat.le_of_lt hij)
      have hzi0 : z i ≠ 0 := by simpa [hi] using hzero i
      omega
    exact (not_lt_of_ge hbound) hlt
  · rintro ⟨hzj, hyj⟩
    refine ⟨hzj, ?_⟩
    have hrank : rankIn (fun i => z i = 1) j = rankIn (fun i => y i = 1) j := by
      unfold rankIn
      congr 1
      apply Finset.filter_congr
      intro i hi
      have hzle := hz (Nat.le_of_lt (Finset.mem_range.mp hi))
      have hyle := hy (Nat.le_of_lt (Finset.mem_range.mp hi))
      have := hzero i
      omega
    rw [hrank]
    exact rankIn_lt_encard hyj

lemma unitMove_zero_iff (m z : ℕ) (hm : 1 ≤ m) (rel : Bool) :
    unitMove m z rel = 0 ↔ z = 0 := by
  unfold unitMove
  split_ifs <;> omega

lemma custMove_zero_iff (d y : ℕ) : custMove d y = 0 ↔ y = 0 := by
  unfold custMove
  split_ifs <;> try omega
  constructor
  · exact False.elim
  · intro h
    omega

lemma custMove_monotone (d : ℕ) : Monotone (custMove d) := by
  intro i j hij
  unfold custMove
  split_ifs <;> omega

variable {σ : Type} [Fintype σ]

lemma unitMove_monotone (M : Model σ) (x : SysState) (R : Set ℕ)
    (hz : Monotone x.loc)
    (hR : ∀ j k, j ∈ R → x.loc j = M.m + 1 → x.loc k = M.m + 1 → k < j → k ∈ R) :
    Monotone (fun j => unitMove M.m (x.loc j) (decide (j ∈ R))) := by
  classical
  intro i j hij
  have hloc := hz hij
  by_cases heq : i = j
  · subst j
    exact le_rfl
  have hij' : i < j := by omega
  have hm := M.one_le_m
  by_cases hi : i ∈ R <;> by_cases hj : j ∈ R <;>
    simp only [unitMove, decide_eq_true_eq, hi, hj, and_true, and_false, ite_false]
  all_goals split_ifs <;> try omega
  by_contra hle
  exact hi (hR j i hj (by omega) (by omega) hij')

lemma paired_monotone (z y : ℕ → ℕ) (hz : Monotone z) (hy : Monotone y)
    (hzero : ∀ i, z i = 0 ↔ y i = 0) :
    Monotone (fun j => if z j = 1 ∧ y j = 1 then 0 else z j) := by
  intro i j hij
  have hzi := hz hij
  have hyi := hy hij
  have hi0 := hzero i
  dsimp only
  split_ifs <;> omega

lemma sysPost_ordered (M : Model σ) (x : SysState) (R : Set ℕ) (d : ℕ)
    (hz : Monotone x.loc) (hy : Monotone x.dist)
    (hzero : ∀ i, x.loc i = 0 ↔ x.dist i = 0)
    (hR : ∀ j k, j ∈ R → x.loc j = M.m + 1 → x.loc k = M.m + 1 → k < j → k ∈ R) :
    Monotone (M.sysPost x R d).loc ∧ Monotone (M.sysPost x R d).dist ∧
      ∀ i, (M.sysPost x R d).loc i = 0 ↔ (M.sysPost x R d).dist i = 0 := by
  let z := fun j => unitMove M.m (x.loc j) (decide (j ∈ R))
  let y := fun j => custMove d (x.dist j)
  have hzm : Monotone z := unitMove_monotone M x R hz hR
  have hym : Monotone y := (custMove_monotone d).comp hy
  have hzy : ∀ i, z i = 0 ↔ y i = 0 := by
    intro i
    exact (unitMove_zero_iff M.m (x.loc i) M.one_le_m _).trans
      ((hzero i).trans (custMove_zero_iff d (x.dist i)).symm)
  have hloc : (M.sysPost x R d).loc = fun j => if z j = 1 ∧ y j = 1 then 0 else z j := by
    funext j
    change (if z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard
      then 0 else z j) = _
    simp only [match_iff z y hzm hym hzy]
  have hdist : (M.sysPost x R d).dist = fun j => if y j = 1 ∧ z j = 1 then 0 else y j := by
    funext j
    change (if y j = 1 ∧ (rankIn (fun i => y i = 1) j : ℕ∞) < {i | z i = 1}.encard
      then 0 else y j) = _
    simp only [match_iff y z hym hzm (fun i => (hzy i).symm)]
  rw [hloc, hdist]
  refine ⟨paired_monotone z y hzm hym hzy,
    paired_monotone y z hym hzm (fun i => (hzy i).symm), ?_⟩
  intro i
  have := hzy i
  dsimp only
  split_ifs <;> omega

lemma initState_ordered (M : Model σ) (a : ℕ → ℕ) (v : ℕ) :
    Monotone (M.initState a v).loc ∧ Monotone (M.initState a v).dist ∧
      ∀ i, (M.initState a v).loc i = 0 ↔ (M.initState a v).dist i = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply Nat.add_le_add_left
    apply Finset.card_le_card
    intro l hl
    obtain ⟨hl, hli⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hl, hli.trans hij⟩
  · intro i j hij
    dsimp [Model.initState]
    split_ifs <;> omega
  · intro i
    simp [Model.initState]
    split_ifs <;> simp

lemma monotone_committed (M : Model σ) (π : SPolicy σ) (hπ : M.IsMonotone π) :
    M.IsCommitted π := by
  intro a v s D k j
  have h : ∀ k, Monotone (M.trajectory π (M.initState a v) s D k).loc ∧
      Monotone (M.trajectory π (M.initState a v) s D k).dist ∧
      ∀ i, (M.trajectory π (M.initState a v) s D k).loc i = 0 ↔
        (M.trajectory π (M.initState a v) s D k).dist i = 0 := by
    intro k
    induction k with
    | zero => exact initState_ordered M a v
    | succ k ih =>
      exact sysPost_ordered M _ _ _ ih.1 ih.2.1 ih.2.2 (hπ (k + 1) (s (k + 1)) _)
  exact (h k).2.2 j

lemma rankIn_strict {p : ℕ → Prop} [DecidablePred p] {i j : ℕ}
    (hi : p i) (hij : i < j) : rankIn p i < rankIn p j := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.le_of_lt hij))
  · intro heq
    have hm : i ∈ (Finset.range j).filter p :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hij, hi⟩
    rw [← heq] at hm
    exact (Nat.lt_irrefl i) (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)

lemma baseStockRelease_finite (M : Model σ) (L : ℤ) (x : SysState) :
    (M.baseStockRelease L x).Finite := by
  let p := fun i => x.loc i = M.m + 1
  refine Set.Finite.of_injOn (f := rankIn p)
    (t := Set.Iio (L - M.inventoryPosition x).toNat) ?_ ?_ (Set.finite_Iio _)
  · intro i hi
    change rankIn p i < (L - M.inventoryPosition x).toNat
    have := hi.2
    change (rankIn p i : ℤ) < L - M.inventoryPosition x at this
    omega
  · intro i hi j hj heq
    rcases lt_trichotomy i j with hij | hij | hij
    · have := rankIn_strict (p := p) hi.1 hij
      omega
    · exact hij
    · have := rankIn_strict (p := p) hj.1 hij
      omega

lemma baseStockRelease_monotone (M : Model σ) (L : ℤ) (x : SysState)
    (j k : ℕ) (hj : j ∈ M.baseStockRelease L x)
    (_ : x.loc j = M.m + 1) (hk : x.loc k = M.m + 1) (hkj : k < j) :
    k ∈ M.baseStockRelease L x := by
  refine ⟨hk, ?_⟩
  have hr := rankIn_strict (p := fun i => x.loc i = M.m + 1) hk hkj
  have hbound := hj.2
  change (rankIn (fun i => x.loc i = M.m + 1) k : ℤ) < L - M.inventoryPosition x
  omega

noncomputable def baseStockPolicy (M : Model σ) (N : ℕ) : SPolicy σ where
  act n s x := M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x
  finite _ _ x := baseStockRelease_finite M _ x

lemma baseStockPolicy_monotone (M : Model σ) (N : ℕ) :
    M.IsMonotone (baseStockPolicy M N) := by
  intro n s x j k
  exact baseStockRelease_monotone M _ x j k

lemma baseStockPolicy_committed (M : Model σ) (N : ℕ) :
    M.IsCommitted (baseStockPolicy M N) :=
  monotone_committed M _ (baseStockPolicy_monotone M N)

lemma baseStock_exists (M : Model σ) (N : ℕ) :
    ∃ π : SPolicy σ, ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SysState),
      M.criticalDistance N n s ≠ ⊤ →
        π.act n s x = M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x := by
  exact ⟨baseStockPolicy M N, fun _ _ _ _ _ _ => rfl⟩

lemma sysStage_eq_tsum (M : Model σ) (x : SysState) :
    M.sysStage x = ∑' j : ℕ, M.subStage (x.loc j, x.dist j) := by
  have hc (p : ℕ → Prop) (c : ℝ≥0∞) :
      c * ENat.toENNReal {j | p j}.encard = ∑' j : ℕ, if p j then c else 0 := by
    rw [mul_comm, ← ENNReal.tsum_set_const]
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
      (tsum_subtype {j | p j} (fun _ : ℕ => c))
  simp only [Model.sysStage, Model.subStage, hc, ← ENNReal.tsum_add]
  congr 1
  funext j
  by_cases hz : x.loc j = 1 <;> by_cases hy : x.dist j = 1 <;> simp only [hz, hy, ite_true, ite_false]

lemma sysPost_subPost (M : Model σ) (x : SysState) (R : Set ℕ) (d j : ℕ)
    (hz : Monotone x.loc) (hy : Monotone x.dist)
    (hzero : ∀ i, x.loc i = 0 ↔ x.dist i = 0)
    (hR : ∀ j k, j ∈ R → x.loc j = M.m + 1 → x.loc k = M.m + 1 → k < j → k ∈ R) :
    ((M.sysPost x R d).loc j, (M.sysPost x R d).dist j) =
      M.subPost (x.loc j, x.dist j) (if j ∈ R then Decision.release else Decision.hold) d := by
  let z := fun j => unitMove M.m (x.loc j) (decide (j ∈ R))
  let y := fun j => custMove d (x.dist j)
  have hzm : Monotone z := unitMove_monotone M x R hz hR
  have hym : Monotone y := (custMove_monotone d).comp hy
  have hzy : ∀ i, z i = 0 ↔ y i = 0 := by
    intro i
    exact (unitMove_zero_iff M.m (x.loc i) M.one_le_m _).trans
      ((hzero i).trans (custMove_zero_iff d (x.dist i)).symm)
  have hdec : decide ((if j ∈ R then Decision.release else Decision.hold) = Decision.release) =
      decide (j ∈ R) := by split_ifs <;> simp_all
  simp only [Model.subPost, hdec]
  change ((if z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard
      then 0 else z j),
    (if y j = 1 ∧ (rankIn (fun i => y i = 1) j : ℕ∞) < {i | z i = 1}.encard
      then 0 else y j)) = if z j = 1 ∧ y j = 1 then (0, 0) else (z j, y j)
  simp only [match_iff z y hzm hym hzy, match_iff y z hym hzm (fun i => (hzy i).symm)]
  split_ifs <;> simp_all

lemma costToGo_decomposes (M : Model σ) (π : SPolicy σ) (ρ : SubPolicy σ)
    (P : ℕ → SysState → Prop)
    (hP : ∀ n s x, P n x → ∀ d, P (n + 1) (M.sysPost x (π.act n s x) d))
    (hpost : ∀ n s x, P n x → ∀ d j,
      ((M.sysPost x (π.act n s x) d).loc j, (M.sysPost x (π.act n s x) d).dist j) =
        M.subPost (x.loc j, x.dist j) (ρ n s (x.loc j, x.dist j)) d)
    (k n : ℕ) (s : σ) (x : SysState) (hx : P n x) :
    M.costToGo M.sysPost M.sysStage π.act k n s x =
      ∑' j : ℕ, M.costToGo M.subPost M.subStage ρ k n s (x.loc j, x.dist j) := by
  induction k generalizing n s x with
  | zero => simp only [Model.costToGo, tsum_zero]
  | succ k ih =>
    simp only [Model.costToGo]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro d
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    congr 1
    apply congrArg₂ (· + ·)
    · simpa only [hpost n s x hx d] using sysStage_eq_tsum M (M.sysPost x (π.act n s x) d)
    · congr 1
      simp only [ih _ _ _ (hP n s x hx d), hpost n s x hx d, ← ENNReal.tsum_mul_left]
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun s' j => M.trans s s' *
          M.costToGo M.subPost M.subStage ρ k (n + 1) s'
            (M.subPost (x.loc j, x.dist j) (ρ n s (x.loc j, x.dist j)) d)))

end ServiceParts.UnitDecomp.Proof
/- END INLINED Sol_ServiceParts_UnitDecomp_Foundations.lean -/

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_Canonical.lean -/
open scoped ENNReal NNReal
open ServiceParts.UnitDecomp Classical

namespace ServiceParts.UnitDecomp.Proof

/-- The three indices record the consumed prefix, the arrived-customer prefix,
and the prefix of units already withdrawn from the supplier. -/
structure Canonical {σ : Type} [Fintype σ] (M : Model σ) (x : SysState)
    (u v r : ℕ) : Prop where
  used_le_arrived : u ≤ v
  used_le_ordered : u ≤ r
  loc_monotone : Monotone x.loc
  loc_le : ∀ j, x.loc j ≤ M.m + 1
  loc_zero : ∀ j, x.loc j = 0 ↔ j < u
  supplier : ∀ j, x.loc j = M.m + 1 ↔ r ≤ j
  distance : ∀ j, x.dist j = if j < u then 0 else if j < v then 1 else j - v + 2

variable {σ : Type} [Fintype σ] {M : Model σ} {x : SysState} {u v r : ℕ}

lemma Canonical.dist_monotone (hx : Canonical M x u v r) : Monotone x.dist := by
  intro i j hij
  simp only [hx.distance]
  split_ifs <;> omega

lemma Canonical.zero_iff (hx : Canonical M x u v r) (j : ℕ) :
    x.loc j = 0 ↔ x.dist j = 0 := by
  rw [hx.loc_zero, hx.distance]
  split_ifs <;> simp_all

lemma Canonical.inventoryPosition (hx : Canonical M x u v r) :
    M.inventoryPosition x = (r : ℤ) - v := by
  have hstock : {j | 1 ≤ x.loc j ∧ x.loc j ≤ M.m} = (↑(Finset.Ico u r) : Set ℕ) := by
    ext j
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ico]
    have := hx.loc_zero j
    have := hx.supplier j
    have := hx.loc_le j
    omega
  have hwaiting : {j | x.dist j = 1} = (↑(Finset.Ico u v) : Set ℕ) := by
    ext j
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ico, hx.distance]
    split_ifs <;> simp_all
  rw [Model.inventoryPosition, hstock, hwaiting]
  simp only [Set.ncard_coe_finset, Nat.card_Ico]
  have := hx.used_le_arrived
  have := hx.used_le_ordered
  omega

lemma Canonical.rank_supplier (hx : Canonical M x u v r) (j : ℕ) :
    rankIn (fun i => x.loc i = M.m + 1) j = j - r := by
  have hfilter : (Finset.range j).filter (fun i => x.loc i = M.m + 1) = Finset.Ico r j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, hx.supplier, Finset.mem_Ico, and_comm]
  simp only [rankIn, hfilter, Nat.card_Ico]

lemma Canonical.baseStockRelease_eq (hx : Canonical M x u v r) (Y : ℕ) (hY : 1 ≤ Y) :
    M.baseStockRelease ((Y : ℤ) - 1) x = {j | x.loc j = M.m + 1 ∧ x.dist j ≤ Y} := by
  ext j
  change (x.loc j = M.m + 1 ∧
      (rankIn (fun i => x.loc i = M.m + 1) j : ℤ) < (Y : ℤ) - 1 - M.inventoryPosition x) ↔ _
  rw [hx.rank_supplier, hx.inventoryPosition]
  simp only [Set.mem_ofPred_eq, hx.distance, hx.supplier]
  have := hx.used_le_ordered
  split_ifs <;> omega

lemma Canonical.supplier_infinite (hx : Canonical M x u v r) :
    {j | x.loc j = M.m + 1}.Infinite := by
  have heq : {j | x.loc j = M.m + 1} = Set.Ici r := by
    ext j
    exact hx.supplier j
  rw [heq]
  exact Set.Ici_infinite r

lemma Canonical.offSupplier_finite (hx : Canonical M x u v r) :
    {j | x.loc j ≠ M.m + 1}.Finite := by
  have heq : {j | x.loc j ≠ M.m + 1} = Set.Iio r := by
    ext j
    change (¬ x.loc j = M.m + 1) ↔ j < r
    rw [hx.supplier]
    omega
  rw [heq]
  exact Set.finite_Iio r

lemma Canonical.futureTail (hx : Canonical M x u v r) :
    ∀ j, v ≤ j → x.dist j = j - v + 2 := by
  intro j hj
  have hju : ¬ j < u := by have := hx.used_le_arrived; omega
  have hjv : ¬ j < v := by omega
  simp only [hx.distance, hju, hjv, ite_false]

lemma canonical_initState (M : Model σ) (a : ℕ → ℕ) (v : ℕ) :
    Canonical M (M.initState a v) 0 v (∑ i ∈ Finset.Icc 1 M.m, a i) := by
  have hcard : (Finset.Icc 1 M.m).card = M.m := by simp
  refine ⟨Nat.zero_le _, Nat.zero_le _, (initState_ordered M a v).1, ?_, ?_, ?_, ?_⟩
  · intro j
    have hc := Finset.card_filter_le (Finset.Icc 1 M.m)
      (fun l => ∑ i ∈ Finset.Icc 1 l, a i ≤ j)
    dsimp [Model.initState]
    rw [hcard] at hc
    omega
  · intro j
    simp [Model.initState]
  · intro j
    change 1 + ((Finset.Icc 1 M.m).filter (fun l => ∑ i ∈ Finset.Icc 1 l, a i ≤ j)).card =
      M.m + 1 ↔ _
    constructor
    · intro h
      have heq : (Finset.Icc 1 M.m).filter (fun l => ∑ i ∈ Finset.Icc 1 l, a i ≤ j) =
          Finset.Icc 1 M.m := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        omega
      have hm : M.m ∈ (Finset.Icc 1 M.m).filter (fun l => ∑ i ∈ Finset.Icc 1 l, a i ≤ j) := by
        rw [heq]
        exact Finset.mem_Icc.mpr ⟨M.one_le_m, le_rfl⟩
      exact (Finset.mem_filter.mp hm).2
    · intro h
      have heq : (Finset.Icc 1 M.m).filter (fun l => ∑ i ∈ Finset.Icc 1 l, a i ≤ j) =
          Finset.Icc 1 M.m := by
        apply Finset.filter_eq_self.mpr
        intro l hl
        apply le_trans ?_ h
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨hi1, hil⟩ := Finset.mem_Icc.mp hi
          exact Finset.mem_Icc.mpr ⟨hi1, hil.trans (Finset.mem_Icc.mp hl).2⟩
        · intros
          exact Nat.zero_le _
      rw [heq, hcard]
      omega
  · intro j
    simp only [Model.initState, Nat.not_lt_zero, ite_false]

/-- Only finitely many units have been withdrawn from the supplier. This property
is preserved even by nonmonotone policies. -/
lemma offSupplier_finite_post (M : Model σ) (x : SysState) (R : Set ℕ) (d : ℕ)
    (hx : {j | x.loc j ≠ M.m + 1}.Finite) (hR : R.Finite) :
    {j | (M.sysPost x R d).loc j ≠ M.m + 1}.Finite := by
  apply (hx.union hR).subset
  intro j hj
  by_contra h
  have hh : x.loc j = M.m + 1 ∧ j ∉ R := by simpa using h
  have hz : x.loc j = M.m + 1 := hh.1
  have hjR : j ∉ R := hh.2
  have hm := M.one_le_m
  have hstay : unitMove M.m (x.loc j) (decide (j ∈ R)) = M.m + 1 := by
    simp [hz, unitMove, hjR]
  apply hj
  simp only [Model.sysPost, hstay]
  split_ifs <;> omega

lemma futureTail_post (M : Model σ) (x : SysState) (R : Set ℕ) (v d : ℕ)
    (hx : ∀ j, v ≤ j → x.dist j = j - v + 2) :
    ∀ j, v + d ≤ j → (M.sysPost x R d).dist j = j - (v + d) + 2 := by
  intro j hj
  have hvj : v ≤ j := by omega
  have hmove : custMove d (x.dist j) = j - (v + d) + 2 := by
    rw [hx j hvj]
    unfold custMove
    split_ifs <;> omega
  simp only [Model.sysPost, hmove]
  split_ifs <;> omega

lemma available_future_infinite (M : Model σ) (x : SysState) (v : ℕ)
    (hx : {j | x.loc j ≠ M.m + 1}.Finite)
    (hy : ∀ j, v ≤ j → x.dist j = j - v + 2) :
    {j | x.loc j = M.m + 1 ∧ x.dist j ≠ 0}.Infinite := by
  apply ((Set.Ici_infinite v).sdiff hx).mono
  intro j hj
  obtain ⟨hjv, hjloc⟩ := hj
  refine ⟨by simpa using hjloc, ?_⟩
  rw [hy j hjv]
  omega

lemma canonical_baseStock_post (hx : Canonical M x u v r) (Y d : ℕ) (hY : 1 ≤ Y) :
    ∃ u', Canonical M (M.sysPost x (M.baseStockRelease ((Y : ℤ) - 1) x) d)
      u' (v + d) (max r (v + Y - 1)) := by
  let R := M.baseStockRelease ((Y : ℤ) - 1) x
  let z := fun j => unitMove M.m (x.loc j) (decide (j ∈ R))
  let y := fun j => custMove d (x.dist j)
  let r' := max r (v + Y - 1)
  have hR : ∀ j k, j ∈ R → x.loc j = M.m + 1 → x.loc k = M.m + 1 → k < j → k ∈ R :=
    baseStockRelease_monotone M _ x
  have hzm : Monotone z := unitMove_monotone M x R hx.loc_monotone hR
  have hym : Monotone y := (custMove_monotone d).comp hx.dist_monotone
  have hz0 (j : ℕ) : z j = 0 ↔ j < u :=
    (unitMove_zero_iff M.m (x.loc j) M.one_le_m _).trans (hx.loc_zero j)
  have hzb (j : ℕ) : z j ≤ M.m + 1 := by
    have := hx.loc_le j
    dsimp [z, unitMove]
    split_ifs <;> omega
  have hzs (j : ℕ) : z j = M.m + 1 ↔ r' ≤ j := by
    have hmem : j ∈ R ↔ x.loc j = M.m + 1 ∧ x.dist j ≤ Y := by
      change j ∈ M.baseStockRelease ((Y : ℤ) - 1) x ↔ _
      rw [hx.baseStockRelease_eq Y hY]
      rfl
    have hloc := hx.loc_le j
    have hsup := hx.supplier j
    have hdist := hx.distance j
    have hur := hx.used_le_ordered
    have hm := M.one_le_m
    dsimp only [z, r']
    unfold unitMove
    simp only [decide_eq_true_eq, hmem]
    split_ifs <;> split_ifs at hdist <;> omega
  have hzy : ∀ j, z j = 0 ↔ y j = 0 := by
    intro j
    exact (unitMove_zero_iff M.m (x.loc j) M.one_le_m _).trans
      ((hx.zero_iff j).trans (custMove_zero_iff d (x.dist j)).symm)
  have hyform (j : ℕ) : y j = if j < u then 0 else if j < v + d then 1 else j - (v + d) + 2 := by
    have huv := hx.used_le_arrived
    dsimp only [y]
    rw [hx.distance]
    by_cases hju : j < u
    · simp [hju, custMove]
    · simp only [hju, ite_false]
      by_cases hjv : j < v
      · have hjvd : j < v + d := by omega
        simp [hjv, hjvd, custMove]
      · simp only [hjv, ite_false]
        unfold custMove
        split_ifs <;> omega
  have hex : ∃ q, 2 ≤ z q := by
    refine ⟨r', ?_⟩
    rw [(hzs r').mpr le_rfl]
    have := M.one_le_m
    omega
  let q := Nat.find hex
  have hq : 2 ≤ z q := Nat.find_spec hex
  have huq : u ≤ q := by
    have := hz0 q
    omega
  have hqr : q ≤ r' := Nat.find_min' hex (by
    rw [(hzs r').mpr le_rfl]
    have := M.one_le_m
    omega)
  have hz1 (j : ℕ) : z j = 1 ↔ u ≤ j ∧ j < q := by
    have hj0 := hz0 j
    constructor
    · intro hj1
      refine ⟨by omega, ?_⟩
      by_contra h
      have := hzm (Nat.le_of_not_gt h)
      omega
    · rintro ⟨huj, hjq⟩
      have := Nat.find_min hex hjq
      omega
  have hloc (j : ℕ) : (M.sysPost x R d).loc j = if z j = 1 ∧ y j = 1 then 0 else z j := by
    change (if z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard
      then 0 else z j) = _
    simp only [match_iff z y hzm hym hzy]
  have hdist (j : ℕ) : (M.sysPost x R d).dist j = if z j = 1 ∧ y j = 1 then 0 else y j := by
    change (if y j = 1 ∧ (rankIn (fun i => y i = 1) j : ℕ∞) < {i | z i = 1}.encard
      then 0 else y j) = _
    simp only [match_iff y z hym hzm (fun i => (hzy i).symm), and_comm]
  refine ⟨min q (v + d), min_le_right _ _, (min_le_left _ _).trans hqr,
    (sysPost_ordered M x R d hx.loc_monotone hx.dist_monotone hx.zero_iff hR).1, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hloc]
    have := hzb j
    split_ifs <;> omega
  · intro j
    rw [hloc, hyform]
    have := hz0 j
    have := hz1 j
    have := hx.used_le_arrived
    split_ifs <;> omega
  · intro j
    rw [hloc]
    have hm := M.one_le_m
    change (if z j = 1 ∧ y j = 1 then 0 else z j) = M.m + 1 ↔ r' ≤ j
    by_cases hmatch : z j = 1 ∧ y j = 1
    · rw [if_pos hmatch]
      have hnot : ¬ r' ≤ j := by
        intro h
        have := (hzs j).mpr h
        omega
      simp [hnot]
    · rw [if_neg hmatch]
      exact hzs j
  · intro j
    rw [hdist, hyform]
    have := hz0 j
    have := hz1 j
    have := hx.used_le_arrived
    split_ifs <;> omega

lemma canonical_post (hx : Canonical M x u v r) (R : Set ℕ) (d r' : ℕ)
    (hR : ∀ j k, j ∈ R → x.loc j = M.m + 1 → x.loc k = M.m + 1 → k < j → k ∈ R)
    (hsupplier : ∀ j, unitMove M.m (x.loc j) (decide (j ∈ R)) = M.m + 1 ↔ r' ≤ j) :
    ∃ u', Canonical M (M.sysPost x R d) u' (v + d) r' := by
  let z := fun j => unitMove M.m (x.loc j) (decide (j ∈ R))
  let y := fun j => custMove d (x.dist j)
  have hzm : Monotone z := unitMove_monotone M x R hx.loc_monotone hR
  have hym : Monotone y := (custMove_monotone d).comp hx.dist_monotone
  have hz0 (j : ℕ) : z j = 0 ↔ j < u :=
    (unitMove_zero_iff M.m (x.loc j) M.one_le_m _).trans (hx.loc_zero j)
  have hzb (j : ℕ) : z j ≤ M.m + 1 := by
    have := hx.loc_le j
    dsimp [z, unitMove]
    split_ifs <;> omega
  have hzs (j : ℕ) : z j = M.m + 1 ↔ r' ≤ j := hsupplier j
  have hzy : ∀ j, z j = 0 ↔ y j = 0 := by
    intro j
    exact (unitMove_zero_iff M.m (x.loc j) M.one_le_m _).trans
      ((hx.zero_iff j).trans (custMove_zero_iff d (x.dist j)).symm)
  have hyform (j : ℕ) : y j = if j < u then 0 else if j < v + d then 1 else j - (v + d) + 2 := by
    have huv := hx.used_le_arrived
    dsimp only [y]
    rw [hx.distance]
    by_cases hju : j < u
    · simp [hju, custMove]
    · simp only [hju, ite_false]
      by_cases hjv : j < v
      · have hjvd : j < v + d := by omega
        simp [hjv, hjvd, custMove]
      · simp only [hjv, ite_false]
        unfold custMove
        split_ifs <;> omega
  have hex : ∃ q, 2 ≤ z q := by
    refine ⟨r', ?_⟩
    rw [(hzs r').mpr le_rfl]
    have := M.one_le_m
    omega
  let q := Nat.find hex
  have hq : 2 ≤ z q := Nat.find_spec hex
  have huq : u ≤ q := by
    have := hz0 q
    omega
  have hqr : q ≤ r' := Nat.find_min' hex (by
    rw [(hzs r').mpr le_rfl]
    have := M.one_le_m
    omega)
  have hz1 (j : ℕ) : z j = 1 ↔ u ≤ j ∧ j < q := by
    have hj0 := hz0 j
    constructor
    · intro hj1
      refine ⟨by omega, ?_⟩
      by_contra h
      have := hzm (Nat.le_of_not_gt h)
      omega
    · rintro ⟨huj, hjq⟩
      have := Nat.find_min hex hjq
      omega
  have hloc (j : ℕ) : (M.sysPost x R d).loc j = if z j = 1 ∧ y j = 1 then 0 else z j := by
    change (if z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard
      then 0 else z j) = _
    simp only [match_iff z y hzm hym hzy]
  have hdist (j : ℕ) : (M.sysPost x R d).dist j = if z j = 1 ∧ y j = 1 then 0 else y j := by
    change (if y j = 1 ∧ (rankIn (fun i => y i = 1) j : ℕ∞) < {i | z i = 1}.encard
      then 0 else y j) = _
    simp only [match_iff y z hym hzm (fun i => (hzy i).symm), and_comm]
  refine ⟨min q (v + d), min_le_right _ _, (min_le_left _ _).trans hqr,
    (sysPost_ordered M x R d hx.loc_monotone hx.dist_monotone hx.zero_iff hR).1, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hloc]
    have := hzb j
    split_ifs <;> omega
  · intro j
    rw [hloc, hyform]
    have := hz0 j
    have := hz1 j
    have := hx.used_le_arrived
    split_ifs <;> omega
  · intro j
    rw [hloc]
    have hm := M.one_le_m
    change (if z j = 1 ∧ y j = 1 then 0 else z j) = M.m + 1 ↔ r' ≤ j
    by_cases hmatch : z j = 1 ∧ y j = 1
    · rw [if_pos hmatch]
      have hnot : ¬ r' ≤ j := by
        intro h
        have := (hzs j).mpr h
        omega
      simp [hnot]
    · rw [if_neg hmatch]
      exact hzs j
  · intro j
    rw [hdist, hyform]
    have := hz0 j
    have := hz1 j
    have := hx.used_le_arrived
    split_ifs <;> omega


lemma canonical_empty_post (hx : Canonical M x u v r) (d : ℕ) :
    ∃ u', Canonical M (M.sysPost x ∅ d) u' (v + d) r := by
  apply canonical_post hx ∅ d r
  · intro j k hj
    exact False.elim hj
  · intro j
    rw [← hx.supplier j]
    simp only [Set.mem_empty_iff_false, decide_false, unitMove, Bool.false_eq_true,
      and_false, ite_false]
    split_ifs <;> omega

end ServiceParts.UnitDecomp.Proof
/- END INLINED Sol_ServiceParts_UnitDecomp_Canonical.lean -/

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_Terminal.lean -/
open scoped ENNReal NNReal
open ServiceParts.UnitDecomp Classical

namespace ServiceParts.UnitDecomp.Proof

variable {σ : Type} [Fintype σ]

/-- Backlog cost before the associated unit can possibly arrive. -/
noncomputable def customerOnlyCost (M : Model σ) : ℕ → ℕ → σ → ℕ → ℝ≥0∞
  | 0, _, _, _ => 0
  | k + 1, n, s, y =>
      ∑' d : ℕ, M.demand s d *
        ((if custMove d y = 1 then (M.b : ℝ≥0∞) else 0) +
          (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' *
            customerOnlyCost M k (n + 1) s' (custMove d y))

lemma subCostToGo_far (M : Model σ) (ρ : SubPolicy σ) (k n : ℕ) (s : σ) (z y : ℕ)
    (hk : k + 1 < z) (hz : z ≤ M.m + 1) :
    M.costToGo M.subPost M.subStage ρ k n s (z, y) = customerOnlyCost M k n s y := by
  induction k generalizing n s z y with
  | zero => rfl
  | succ k ih =>
    let w := unitMove M.m z (decide (ρ n s (z, y) = Decision.release))
    have hw : k + 1 < w := by
      have hm := M.one_le_m
      dsimp [w, unitMove]
      split_ifs <;> omega
    have hwm : w ≤ M.m + 1 := by
      dsimp [w, unitMove]
      split_ifs <;> omega
    have hw1 : w ≠ 1 := by omega
    have hpost (d : ℕ) : M.subPost (z, y) (ρ n s (z, y)) d = (w, custMove d y) := by
      change (if w = 1 ∧ custMove d y = 1 then (0, 0) else (w, custMove d y)) =
        (w, custMove d y)
      simp only [hw1, false_and, ite_false]
    simp only [Model.costToGo, customerOnlyCost, hpost]
    apply tsum_congr
    intro d
    simp only [Model.subStage, hw1, ite_false, zero_add, ih _ _ w _ hw hwm]

lemma subOpt_far (M : Model σ) (N n : ℕ) (s : σ) (z y : ℕ)
    (hk : (N + 1 - n) + 1 < z) (hz : z ≤ M.m + 1) :
    M.subOpt N n s (z, y) = customerOnlyCost M (N + 1 - n) n s y := by
  haveI : Nonempty (SubPolicy σ) := ⟨fun _ _ _ => Decision.hold⟩
  simp only [Model.subOpt, Model.subCost, subCostToGo_far M _ _ _ _ _ _ hk hz, iInf_const]

lemma subQ_terminal (M : Model σ) (N n : ℕ) (s : σ) (y : ℕ)
    (hnN : n ≤ N) (hterminal : N + 1 - n < M.m) (a : Decision) :
    M.subQ N n s (M.m + 1, y) a = customerOnlyCost M (N - n + 1) n s y := by
  let w := unitMove M.m (M.m + 1) (decide (a = Decision.release))
  have hm := M.one_le_m
  have hw : N - n + 1 < w := by
    cases a <;> simp [w, unitMove] <;> omega
  have hwm : w ≤ M.m + 1 := by
    cases a <;> simp [w, unitMove]
  have hw1 : w ≠ 1 := by omega
  have hpost (d : ℕ) : M.subPost (M.m + 1, y) a d = (w, custMove d y) := by
    change (if w = 1 ∧ custMove d y = 1 then (0, 0) else (w, custMove d y)) =
      (w, custMove d y)
    simp only [hw1, false_and, ite_false]
  simp only [Model.subQ, customerOnlyCost, hpost]
  apply tsum_congr
  intro d
  simp only [Model.subStage, hw1, ite_false, zero_add]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro s' _
  rw [subOpt_far M N (n + 1) s' w (custMove d y) (by omega) hwm]
  simp only [Nat.add_sub_add_right]

lemma criticalDistance_terminal_top (M : Model σ) (N n : ℕ) (s : σ)
    (hnN : n ≤ N) (hterminal : N + 1 - n < M.m) :
    M.criticalDistance N n s = ⊤ := by
  have hrel (y : ℕ) : Decision.release ∈ M.optDecisions N n s y := by
    intro a
    rw [subQ_terminal M N n s y hnN hterminal, subQ_terminal M N n s y hnN hterminal]
  apply top_le_iff.mp
  rw [← ENat.iSup_natCast]
  apply iSup_le
  intro y
  exact le_iSup₂_of_le y (hrel y) le_rfl

/-- States agree on customers and on every unit close enough to arrive during the
remaining horizon. Far-away locations need not agree. -/
def NearEq (k : ℕ) (x y : SysState) : Prop :=
  x.dist = y.dist ∧ ∀ j, x.loc j = y.loc j ∨ (k + 1 < x.loc j ∧ k + 1 < y.loc j)

lemma unitMove_near (M : Model σ) (k z z' : ℕ) (r r' : Bool)
    (hk : k + 1 < M.m) (hz : z = z' ∨ (k + 2 < z ∧ k + 2 < z')) :
    unitMove M.m z r = unitMove M.m z' r' ∨
      (k + 1 < unitMove M.m z r ∧ k + 1 < unitMove M.m z' r') := by
  rcases hz with hz | ⟨hz, hz'⟩
  · subst z'
    by_cases hs : z = M.m + 1
    · right
      rw [hs]
      constructor <;> unfold unitMove <;> split_ifs <;> omega
    · left
      simp only [unitMove, hs, false_and, ite_false]
  · right
    constructor <;> unfold unitMove <;> split_ifs <;> omega

lemma nearEq_stage (M : Model σ) {k : ℕ} {x y : SysState} (hxy : NearEq k x y) :
    M.sysStage x = M.sysStage y := by
  have hz : {j | x.loc j = 1} = {j | y.loc j = 1} := by
    ext j
    change x.loc j = 1 ↔ y.loc j = 1
    rcases hxy.2 j with h | ⟨h, h'⟩
    · rw [h]
    · omega
  simp only [Model.sysStage, hz, hxy.1]

lemma nearEq_post (M : Model σ) {k : ℕ} {x x' : SysState} (R R' : Set ℕ) (d : ℕ)
    (hk : k + 1 < M.m) (hxx' : NearEq (k + 1) x x') :
    NearEq k (M.sysPost x R d) (M.sysPost x' R' d) := by
  let z := fun j => unitMove M.m (x.loc j) (decide (j ∈ R))
  let z' := fun j => unitMove M.m (x'.loc j) (decide (j ∈ R'))
  let y := fun j => custMove d (x.dist j)
  have hy (j : ℕ) : custMove d (x'.dist j) = y j := by rw [← hxx'.1]
  have hz (j : ℕ) : z j = z' j ∨ (k + 1 < z j ∧ k + 1 < z' j) :=
    unitMove_near M k (x.loc j) (x'.loc j) _ _ hk (hxx'.2 j)
  have hon : (fun j => z j = 1) = (fun j => z' j = 1) := by
    funext j
    apply propext
    rcases hz j with h | ⟨h, h'⟩
    · rw [h]
    · omega
  have hsets : {j | z j = 1} = {j | z' j = 1} := by
    ext j
    exact Iff.of_eq (congr_fun hon j)
  have hdist : (M.sysPost x R d).dist = (M.sysPost x' R' d).dist := by
    funext j
    simp only [Model.sysPost, hy]
    change (if y j = 1 ∧ (rankIn (fun i => y i = 1) j : ℕ∞) < {i | z i = 1}.encard
      then 0 else y j) =
      (if y j = 1 ∧ (rankIn (fun i => y i = 1) j : ℕ∞) < {i | z' i = 1}.encard
      then 0 else y j)
    rw [hsets]
  refine ⟨hdist, ?_⟩
  intro j
  have hloc : (M.sysPost x R d).loc j =
      if z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard then 0 else z j := rfl
  have hloc' : (M.sysPost x' R' d).loc j =
      if z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard then 0 else z' j := by
    simp only [Model.sysPost, hy]
    change (if z' j = 1 ∧ (rankIn (fun i => z' i = 1) j : ℕ∞) < {i | y i = 1}.encard
      then 0 else z' j) = _
    simp only [← congr_fun hon j, ← hon]
  rw [hloc, hloc']
  by_cases hmatch : z j = 1 ∧ (rankIn (fun i => z i = 1) j : ℕ∞) < {i | y i = 1}.encard
  · simp [hmatch]
  · simp only [if_neg hmatch]
    exact hz j

/-- An order that cannot arrive before the horizon cannot change any stage cost,
even when the policies release different labelled units. -/
lemma terminal_cost_independent (M : Model σ) (π τ : SPolicy σ)
    (k n : ℕ) (s : σ) (x x' : SysState) (hk : k < M.m) (hxx' : NearEq k x x') :
    M.costToGo M.sysPost M.sysStage π.act k n s x =
      M.costToGo M.sysPost M.sysStage τ.act k n s x' := by
  induction k generalizing n s x x' with
  | zero => rfl
  | succ k ih =>
    simp only [Model.costToGo]
    apply tsum_congr
    intro d
    have hp := nearEq_post M (π.act n s x) (τ.act n s x') d hk hxx'
    rw [nearEq_stage M hp]
    congr 2
    congr 1
    apply Finset.sum_congr rfl
    intro s' _
    congr 1
    exact ih (n + 1) s' _ _ (by omega) hp

end ServiceParts.UnitDecomp.Proof
/- END INLINED Sol_ServiceParts_UnitDecomp_Terminal.lean -/

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_Distance.lean -/
open scoped ENNReal NNReal Topology
open Filter MeasureTheory ServiceParts.UnitDecomp

namespace ServiceParts.UnitDecomp.Proof
variable {σ : Type} [Fintype σ]

private lemma pmf_limit (p : PMF ℕ) (C L : ℝ≥0∞) (hC : C ≠ ⊤)
    (F : ℕ → ℕ → ℝ≥0∞) (hF : ∀ y d, F y d ≤ C)
    (hlim : ∀ d, Tendsto (fun y => F y d) atTop (𝓝 L)) :
    Tendsto (fun y => ∑' d, p d * F y d) atTop (𝓝 L) := by
  have ht := tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
    (F := fun y d => p d * F y d) (f := fun d => p d * L)
    (fun d => p d * C) (fun _ => measurable_of_countable _)
    (fun y => Filter.Eventually.of_forall fun d => mul_le_mul' le_rfl (hF y d))
    (by rw [lintegral_count, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]; exact hC)
    (Filter.Eventually.of_forall fun d =>
      ENNReal.Tendsto.const_mul (hlim d) (Or.inr (p.apply_ne_top d)))
  simpa only [lintegral_count, ENNReal.tsum_mul_right, p.tsum_coe, one_mul] using ht

private lemma custMove_tendsto (d : ℕ) :
    Tendsto (custMove d) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b+d+2)] with y hy
  unfold custMove
  split_ifs <;> omega

private lemma custMove_large (d : ℕ) : ∀ᶠ y in atTop, 2 ≤ custMove d y :=
  (custMove_tendsto d).eventually (eventually_ge_atTop 2)

private lemma transition_mass (M : Model σ) (s : σ) : ∑ s', M.trans s s'=1 := by
  simpa only [tsum_fintype] using (M.trans s).tsum_coe

private lemma stage_cont_bound (M : Model σ) (k : ℕ) (s : σ)
    (W : σ → SubState → ℝ≥0∞) (hW : ∀ s x, W s x ≤ k*((M.h:ℝ≥0∞)+M.b))
    (x : SubState) :
    M.subStage x+(M.α:ℝ≥0∞)*∑ s', M.trans s s'*W s' x ≤
      ((M.h:ℝ≥0∞)+M.b)+k*((M.h:ℝ≥0∞)+M.b) := by
  apply add_le_add (SPD.stage_le M x)
  have hα : (M.α:ℝ≥0∞) ≤ 1 := by exact_mod_cast M.α_le_one
  calc
    _ ≤ 1*∑ s', M.trans s s'*(k*((M.h:ℝ≥0∞)+M.b)) :=
      mul_le_mul' hα (Finset.sum_le_sum fun s' _ => mul_le_mul' le_rfl (hW s' x))
    _ = _ := by rw [one_mul,←Finset.sum_mul,transition_mass,one_mul]

/-- Cost when the paired customer never arrives within the horizon. -/
noncomputable def absentCost (M : Model σ) : ℕ → ℕ → ℝ≥0∞
  | 0, _ => 0
  | k+1,z =>
      let w := if 2 ≤ z then z-1 else z
      (if w=1 then (M.h:ℝ≥0∞) else 0)+(M.α:ℝ≥0∞)*absentCost M k w

lemma U_tendsto_absent (M : Model σ) (k : ℕ) (s : σ) (z : ℕ) :
    Tendsto (fun y => SPD.U M k s (z,y)) atTop (𝓝 (absentCost M k z)) := by
  classical
  induction k generalizing s z with
  | zero => simpa only [SPD.U,absentCost] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
  | succ k ih =>
    let w := if 2 ≤ z then z-1 else z
    apply pmf_limit (M.demand s)
      (((M.h:ℝ≥0∞)+M.b)+k*((M.h:ℝ≥0∞)+M.b)) (absentCost M (k+1) z)
      (by simp [ENNReal.mul_eq_top])
      (fun y d => M.subStage (SPD.tpost (z,y) d)+(M.α:ℝ≥0∞)*
        ∑ s', M.trans s s'*SPD.U M k s' (SPD.tpost (z,y) d))
    · intro y d
      exact stage_cont_bound M k s (SPD.U M k) (SPD.U_bound M k) _
    · intro d
      have hs := tendsto_finsetSum Finset.univ fun s' _ =>
        ENNReal.Tendsto.const_mul ((ih s' w).comp (custMove_tendsto d))
          (Or.inr ((M.trans s).apply_ne_top s'))
      have hs' : Tendsto (fun y => ∑ s', M.trans s s'*SPD.U M k s' (w,custMove d y))
          atTop (𝓝 (absentCost M k w)) := by
        simpa only [Function.comp_def,←Finset.sum_mul,transition_mass,one_mul] using hs
      have ht := (tendsto_const_nhds : Tendsto
          (fun _ : ℕ => if w=1 then (M.h:ℝ≥0∞) else 0) atTop
          (𝓝 (if w=1 then (M.h:ℝ≥0∞) else 0))).add
        (ENNReal.Tendsto.const_mul (a := (M.α:ℝ≥0∞)) hs' (Or.inr ENNReal.coe_ne_top))
      have he : (fun y => M.subStage (SPD.tpost (z,y) d)+(M.α:ℝ≥0∞)*
          ∑ s', M.trans s s'*SPD.U M k s' (SPD.tpost (z,y) d)) =ᶠ[atTop]
          (fun y => (if w=1 then (M.h:ℝ≥0∞) else 0)+(M.α:ℝ≥0∞)*
            ∑ s', M.trans s s'*SPD.U M k s' (w,custMove d y)) := by
        filter_upwards [custMove_large d] with y hy
        have hn : custMove d y ≠ 1 := by omega
        simp [SPD.tpost,SPD.mt,Model.subStage,hn,w]
      simpa only [absentCost,w] using ht.congr' he.symm

lemma absentCost_pos (M : Model σ) (k z : ℕ) (hk : 0 < k) (hz : 1 ≤ z)
    (hzk : z ≤ k+1) : 0 < absentCost M k z := by
  have hh : 0 < (M.h:ℝ≥0∞) := by exact_mod_cast M.h_pos
  have hα : 0 < (M.α:ℝ≥0∞) := by exact_mod_cast M.α_pos
  induction k generalizing z with
  | zero => omega
  | succ k ih =>
    by_cases hz2 : z ≤ 2
    · have hw : (if 2 ≤ z then z-1 else z)=1 := by split_ifs <;> omega
      simp only [absentCost,hw,ite_true]
      exact hh.trans_le le_self_add
    · have hz3 : 3 ≤ z := by omega
      have hpos := ih (z-1) (by omega) (by omega) (by omega)
      simp only [absentCost,if_pos (by omega : 2 ≤ z),if_neg (by omega : z-1≠1),zero_add]
      exact ENNReal.mul_pos_iff.mpr ⟨hα,hpos⟩

/-- The supplier is kept idle for all remaining periods. -/
noncomputable def idleCost (M : Model σ) : ℕ → σ → ℕ → ℝ≥0∞
  | 0,_,_ => 0
  | k+1,s,y => ∑' d, M.demand s d *
      ((if custMove d y=1 then (M.b:ℝ≥0∞) else 0)+(M.α:ℝ≥0∞)*
        ∑ s', M.trans s s'*idleCost M k s' (custMove d y))

lemma idleCost_eq (M : Model σ) (k n : ℕ) (s : σ) (y : ℕ) :
    M.costToGo M.subPost M.subStage (fun _ _ _ => Decision.hold) k n s (M.m+1,y) =
      idleCost M k s y := by
  induction k generalizing n s y with
  | zero => rfl
  | succ k ih =>
    have hm : M.m+1≠1 := by have := M.one_le_m; omega
    simp only [Model.costToGo,SPD.subPost_hold,Model.subStage,hm,ite_false,zero_add,
      ih,idleCost]

lemma idleCost_bound (M : Model σ) (k : ℕ) (s : σ) (y : ℕ) :
    idleCost M k s y ≤ k*((M.h:ℝ≥0∞)+M.b) := by
  induction k generalizing s y with
  | zero => simp [idleCost]
  | succ k ih =>
    have hm : M.m+1≠1 := by have := M.one_le_m; omega
    have ht := SPD.step_bound M s (fun s x => idleCost M k s x.2)
      (k*((M.h:ℝ≥0∞)+M.b)) (fun s x => ih s x.2)
      (fun d => (M.m+1,custMove d y))
    simp only [Model.subStage,hm,ite_false,zero_add] at ht
    refine ht.trans_eq ?_
    push_cast
    ring

lemma idleCost_tendsto_zero (M : Model σ) (k : ℕ) (s : σ) :
    Tendsto (idleCost M k s) atTop (𝓝 0) := by
  classical
  induction k generalizing s with
  | zero => simpa only [idleCost] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
  | succ k ih =>
    apply pmf_limit (M.demand s)
      (((M.h:ℝ≥0∞)+M.b)+k*((M.h:ℝ≥0∞)+M.b)) 0
      (by simp [ENNReal.mul_eq_top])
      (fun y d => (if custMove d y=1 then (M.b:ℝ≥0∞) else 0)+(M.α:ℝ≥0∞)*
        ∑ s', M.trans s s'*idleCost M k s' (custMove d y))
    · intro y d
      have hm : M.m+1≠1 := by have := M.one_le_m; omega
      have ht := stage_cont_bound M k s (fun s x => idleCost M k s x.2)
        (fun s x => idleCost_bound M k s x.2) (M.m+1,custMove d y)
      simpa only [Model.subStage,hm,ite_false,zero_add] using ht
    · intro d
      have hs := tendsto_finsetSum Finset.univ fun s' _ =>
        ENNReal.Tendsto.const_mul ((ih s').comp (custMove_tendsto d))
          (Or.inr ((M.trans s).apply_ne_top s'))
      have hs' : Tendsto (fun y => ∑ s', M.trans s s'*idleCost M k s' (custMove d y))
          atTop (𝓝 0) := by simpa using hs
      have hb : Tendsto (fun y => if custMove d y=1 then (M.b:ℝ≥0∞) else 0)
          atTop (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [custMove_large d] with y hy
        simp [show custMove d y≠1 by omega]
      simpa using hb.add (ENNReal.Tendsto.const_mul (a := (M.α:ℝ≥0∞)) hs' (Or.inr ENNReal.coe_ne_top))

lemma Qhold_le_idle (M : Model σ) (k : ℕ) (s : σ) (y : ℕ) :
    SPD.Q M k s (M.m+1,y) Decision.hold ≤ idleCost M (k+1) s y := by
  have hm : M.m+1≠1 := by have := M.one_le_m; omega
  simp only [SPD.Q,SPD.subPost_hold,Model.subStage,hm,ite_false,zero_add,idleCost]
  apply ENNReal.tsum_le_tsum
  intro d
  apply mul_le_mul' le_rfl
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro s' _
  apply mul_le_mul' le_rfl
  simpa only [idleCost_eq] using SPD.V_le_cost M (fun _ _ _ => Decision.hold) k 0 s'
    (M.m+1,custMove d y)


lemma criticalDistance_finite (M : Model σ) (N n : ℕ) (s : σ)
    (hearly : M.m ≤ N+1-n) : M.criticalDistance N n s ≠ ⊤ := by
  have hnN : n ≤ N := by have := M.one_le_m; omega
  have hpos : 0 < absentCost M (N-n+1) (M.m+1) :=
    absentCost_pos M _ _ (by omega) (by omega) (by omega)
  have he := (idleCost_tendsto_zero M (N-n+1) s).eventually_lt
    (U_tendsto_absent M (N-n+1) s (M.m+1)) hpos
  obtain ⟨Y,hY⟩ := eventually_atTop.1 he
  have hbound : M.criticalDistance N n s ≤ (Y:ℕ∞) := by
    apply iSup₂_le
    intro y hrel
    have hy : y ≤ Y := by
      by_contra hh
      have hgt := hY y (Nat.le_of_lt (Nat.lt_of_not_ge hh))
      have hq := hrel Decision.hold
      simp only [SPD.subQ_eq] at hq
      have hle := hq.trans (Qhold_le_idle M (N-n) s y)
      rw [SPD.Qrel_eq] at hle
      exact (not_lt_of_ge hle) hgt
    exact_mod_cast hy
  exact ne_top_of_le_ne_top (by simp) hbound

/-- Backlog cost of a customer already waiting, when the unit is moved immediately. -/
noncomputable def waitingCost (M : Model σ) : ℕ → ℕ → ℝ≥0∞
  | 0,_ => 0
  | k+1,z => if z≤2 then 0 else (M.b:ℝ≥0∞)+(M.α:ℝ≥0∞)*waitingCost M k (z-1)

lemma waitingCost_mono (M : Model σ) (k : ℕ) : Monotone (waitingCost M k) := by
  induction k with
  | zero => intro z z' h; exact le_rfl
  | succ k ih =>
    intro z z' h
    by_cases hz : z≤2
    · simp only [waitingCost,if_pos hz]
      exact bot_le
    · have hz' : ¬ z'≤2 := by omega
      simp only [waitingCost,if_neg hz,if_neg hz']
      exact add_le_add le_rfl (mul_le_mul' le_rfl (ih (Nat.sub_le_sub_right h 1)))

lemma U_waiting (M : Model σ) (k : ℕ) (s : σ) (z : ℕ) (hz : 1≤z) :
    SPD.U M k s (z,1) = waitingCost M k z := by
  classical
  induction k generalizing s z with
  | zero => rfl
  | succ k ih =>
    rcases (by omega : z=1 ∨ z=2 ∨ 3≤z) with rfl|rfl|hz3
    · simp [SPD.U_one_one,waitingCost]
    · simp [SPD.U,SPD.tpost,SPD.mt,SPD.custMove_one,Model.subStage,
        SPD.U_zero_zero,waitingCost]
    · have hz2 : 2≤z := by omega
      have hznot : ¬ z≤2 := by omega
      have hzn : z-1≠1 := by omega
      simp only [SPD.U,SPD.tpost,if_pos hz2,SPD.custMove_one,SPD.mt,hzn,false_and,
        ite_false,Model.subStage,ite_true,zero_add,waitingCost,if_neg hznot]
      have hU : ∀ s', SPD.U M k s' (z-1,1) = waitingCost M k (z-1) :=
        fun s' => ih s' (z-1) (by omega)
      simp only [hU]
      rw [←Finset.sum_mul,transition_mass,one_mul,ENNReal.tsum_mul_right,
        (M.demand s).tsum_coe,one_mul]

lemma waiting_release_le_hold (M : Model σ) (k : ℕ) :
    waitingCost M (k+1) (M.m+1) ≤ (M.b:ℝ≥0∞)+(M.α:ℝ≥0∞)*waitingCost M k (M.m+1) := by
  by_cases hm : M.m+1≤2
  · simp only [waitingCost,if_pos hm]
    exact bot_le
  · simp only [waitingCost,if_neg hm,Nat.add_sub_cancel]
    exact add_le_add le_rfl (mul_le_mul' le_rfl (waitingCost_mono M k (Nat.le_succ _)))

lemma V_waiting (M : Model σ) (k : ℕ) (s : σ) :
    SPD.V M k s (M.m+1,1) = waitingCost M k (M.m+1) := by
  classical
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have hm : M.m+1≠1 := by have := M.one_le_m; omega
    have hr : SPD.Q M k s (M.m+1,1) Decision.release = waitingCost M (k+1) (M.m+1) := by
      rw [SPD.Qrel_eq,U_waiting M _ _ _ (by omega)]
    have hh : SPD.Q M k s (M.m+1,1) Decision.hold =
        (M.b:ℝ≥0∞)+(M.α:ℝ≥0∞)*waitingCost M k (M.m+1) := by
      simp only [SPD.Q,SPD.subPost_hold,SPD.custMove_one,Model.subStage,hm,ite_false,
        ite_true,zero_add,ih]
      rw [←Finset.sum_mul,transition_mass,one_mul,ENNReal.tsum_mul_right,
        (M.demand s).tsum_coe,one_mul]
    rw [SPD.V_succ,hr,hh,min_eq_left (waiting_release_le_hold M k)]

lemma criticalDistance_one_le (M : Model σ) (N n : ℕ) (s : σ) :
    (1:ℕ∞) ≤ M.criticalDistance N n s := by
  classical
  have hrel : Decision.release ∈ M.optDecisions N n s 1 := by
    intro a
    cases a with
    | release => exact le_rfl
    | hold =>
      simp only [SPD.subQ_eq]
      rw [SPD.Qrel_eq,U_waiting M _ _ _ (by omega)]
      have hm : M.m+1≠1 := by have := M.one_le_m; omega
      simp only [SPD.Q,SPD.subPost_hold,SPD.custMove_one,Model.subStage,hm,ite_false,
        ite_true,zero_add,V_waiting]
      rw [←Finset.sum_mul,transition_mass,one_mul,ENNReal.tsum_mul_right,
        (M.demand s).tsum_coe,one_mul]
      exact waiting_release_le_hold M (N-n)
  exact le_iSup₂_of_le 1 hrel le_rfl

lemma criticalDistance_toNat_pos (M : Model σ) (N n : ℕ) (s : σ)
    (hfin : M.criticalDistance N n s ≠ ⊤) : 1 ≤ (M.criticalDistance N n s).toNat := by
  have he : ((M.criticalDistance N n s).toNat:ℕ∞)=M.criticalDistance N n s :=
    ENat.coe_toNat hfin
  have hh := criticalDistance_one_le M N n s
  rw [←he] at hh
  exact_mod_cast hh

end ServiceParts.UnitDecomp.Proof
/- END INLINED Sol_ServiceParts_UnitDecomp_Distance.lean -/

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_Monotone.lean -/
open scoped ENNReal NNReal
open ServiceParts.UnitDecomp Classical

namespace ServiceParts.UnitDecomp.Proof

variable {σ : Type} [Fintype σ]

lemma sumQ_eq_systemStep (M : Model σ) (k : ℕ) (s : σ) (x : SysState) (R : Set ℕ)
    (hz : Monotone x.loc) (hy : Monotone x.dist)
    (hzero : ∀ j, x.loc j = 0 ↔ x.dist j = 0)
    (hR : ∀ j i, j ∈ R → x.loc j = M.m + 1 → x.loc i = M.m + 1 → i < j → i ∈ R) :
    (∑' j : ℕ, SPD.Q M k s (x.loc j, x.dist j)
      (if j ∈ R then Decision.release else Decision.hold)) =
      ∑' d : ℕ, M.demand s d *
        (M.sysStage (M.sysPost x R d) +
          (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' *
            ∑' j : ℕ, SPD.V M k s' ((M.sysPost x R d).loc j, (M.sysPost x R d).dist j)) := by
  simp only [SPD.Q]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro d
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  congr 1
  apply congrArg₂ (· + ·)
  · rw [sysStage_eq_tsum]
    apply tsum_congr
    intro j
    rw [sysPost_subPost M x R d j hz hy hzero hR]
  · congr 1
    calc
      (∑' j : ℕ, ∑ s' : σ, M.trans s s' *
        SPD.V M k s' (M.subPost (x.loc j, x.dist j)
          (if j ∈ R then Decision.release else Decision.hold) d)) =
          ∑ s' : σ, ∑' j : ℕ, M.trans s s' *
            SPD.V M k s' (M.subPost (x.loc j, x.dist j)
              (if j ∈ R then Decision.release else Decision.hold) d) := by
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comm (f := fun j s' => M.trans s s' *
            SPD.V M k s' (M.subPost (x.loc j, x.dist j)
              (if j ∈ R then Decision.release else Decision.hold) d)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s' _
        rw [ENNReal.tsum_mul_left]
        congr 1
        apply tsum_congr
        intro j
        rw [sysPost_subPost M x R d j hz hy hzero hR]

/-- The full system state may guide the release decision; the subsystem Bellman
value is still a lower bound, so no independence assumption is needed here. -/
lemma sumV_le_monotone_cost (M : Model σ) (π : SPolicy σ) (hπ : M.IsMonotone π)
    (k n : ℕ) (s : σ) (x : SysState)
    (hz : Monotone x.loc) (hy : Monotone x.dist)
    (hzero : ∀ j, x.loc j = 0 ↔ x.dist j = 0) :
    (∑' j : ℕ, SPD.V M k s (x.loc j, x.dist j)) ≤
      M.costToGo M.sysPost M.sysStage π.act k n s x := by
  induction k generalizing n s x with
  | zero => simp [SPD.V, Model.costToGo]
  | succ k ih =>
    have hR := hπ n s x
    have hstep : (∑' j : ℕ, SPD.V M (k + 1) s (x.loc j, x.dist j)) ≤
        ∑' j : ℕ, SPD.Q M k s (x.loc j, x.dist j)
          (if j ∈ π.act n s x then Decision.release else Decision.hold) := by
      apply ENNReal.tsum_le_tsum
      intro j
      rw [SPD.V_succ]
      split_ifs
      · exact min_le_left _ _
      · exact min_le_right _ _
    apply hstep.trans
    rw [sumQ_eq_systemStep M k s x (π.act n s x) hz hy hzero hR, Model.costToGo]
    apply ENNReal.tsum_le_tsum
    intro d
    apply mul_le_mul' le_rfl
    apply add_le_add_right
    apply mul_le_mul' le_rfl
    apply Finset.sum_le_sum
    intro s' _
    apply mul_le_mul' le_rfl
    have hp := sysPost_ordered M x (π.act n s x) d hz hy hzero hR
    exact ih (n + 1) s' (M.sysPost x (π.act n s x) d) hp.1 hp.2.1 hp.2.2

lemma sum_subOpt_le_monotone_cost (M : Model σ) (N : ℕ) (π : SPolicy σ)
    (hπ : M.IsMonotone π) (s : σ) (a : ℕ → ℕ) (v : ℕ) :
    (∑' j : ℕ, M.subOpt N 1 s ((M.initState a v).loc j, (M.initState a v).dist j)) ≤
      M.sysCost N π 1 s (M.initState a v) := by
  simp only [SPD.subOpt_eq, Model.sysCost]
  have hx := initState_ordered M a v
  exact sumV_le_monotone_cost M π hπ _ 1 s _ hx.1 hx.2.1 hx.2.2

lemma monotone_greedy_cost (M : Model σ) (N : ℕ) (π : SPolicy σ)
    (hπ : M.IsMonotone π) (P : ℕ → SysState → Prop)
    (horder : ∀ n x, P n x → Monotone x.loc ∧ Monotone x.dist ∧
      ∀ j, x.loc j = 0 ↔ x.dist j = 0)
    (hP : ∀ n s x, n ≤ N → P n x → ∀ d, P (n + 1) (M.sysPost x (π.act n s x) d))
    (hgreedy : ∀ n s x, n ≤ N → P n x → ∀ j,
      SPD.Q M (N - n) s (x.loc j, x.dist j)
        (if j ∈ π.act n s x then Decision.release else Decision.hold) =
          SPD.V M (N - n + 1) s (x.loc j, x.dist j))
    (k n : ℕ) (s : σ) (x : SysState) (hk : k = N + 1 - n) (hx : P n x) :
    M.costToGo M.sysPost M.sysStage π.act k n s x =
      ∑' j : ℕ, SPD.V M k s (x.loc j, x.dist j) := by
  induction k generalizing n s x with
  | zero => simp [Model.costToGo, SPD.V]
  | succ k ih =>
    have hnN : n ≤ N := by omega
    have hk' : k = N - n := by omega
    have ho := horder n x hx
    have heq : (∑' j : ℕ, SPD.V M (k + 1) s (x.loc j, x.dist j)) =
        ∑' j : ℕ, SPD.Q M k s (x.loc j, x.dist j)
          (if j ∈ π.act n s x then Decision.release else Decision.hold) := by
      apply tsum_congr
      intro j
      rw [hk']
      exact (hgreedy n s x hnN hx j).symm
    rw [heq, sumQ_eq_systemStep M k s x (π.act n s x) ho.1 ho.2.1 ho.2.2 (hπ n s x),
      Model.costToGo]
    apply tsum_congr
    intro d
    congr 2
    congr 1
    apply Finset.sum_congr rfl
    intro s' _
    congr 1
    exact ih (n + 1) s' _ (by omega) (hP n s x hnN hx d)

end ServiceParts.UnitDecomp.Proof
/- END INLINED Sol_ServiceParts_UnitDecomp_Monotone.lean -/

/- BEGIN INLINED Sol_ServiceParts_UnitDecomp_RootCorrect.lean -/
open scoped ENNReal NNReal
open ServiceParts.UnitDecomp Classical

namespace ServiceParts.UnitDecomp.Proof

variable {σ : Type} [Fintype σ]

noncomputable def monotoneCriticalPolicy (M : Model σ) (N : ℕ) : SPolicy σ where
  act n s x := if M.criticalDistance N n s ≠ ⊤
    then M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x else ∅
  finite n s x := by
    split_ifs
    · exact baseStockRelease_finite M _ x
    · exact Set.finite_empty

lemma monotoneCriticalPolicy_monotone (M : Model σ) (N : ℕ) :
    M.IsMonotone (monotoneCriticalPolicy M N) := by
  intro n s x j k hj hzj hzk hkj
  by_cases hc : M.criticalDistance N n s ≠ ⊤
  · simp only [monotoneCriticalPolicy, if_pos hc] at hj ⊢
    exact baseStockRelease_monotone M _ x j k hj hzj hzk hkj
  · simp only [monotoneCriticalPolicy, if_neg hc, Set.mem_empty_iff_false] at hj

lemma monotoneCriticalPolicy_preserves (M : Model σ) (N n : ℕ) (s : σ) (x : SysState)
    (u v r d : ℕ) (hx : Canonical M x u v r) :
    ∃ u' v' r', Canonical M (M.sysPost x ((monotoneCriticalPolicy M N).act n s x) d) u' v' r' := by
  by_cases hc : M.criticalDistance N n s ≠ ⊤
  · simp only [monotoneCriticalPolicy, if_pos hc]
    obtain ⟨u', hu'⟩ := canonical_baseStock_post hx (M.criticalDistance N n s).toNat d
      (criticalDistance_toNat_pos M N n s hc)
    exact ⟨u', _, _, hu'⟩
  · simp only [monotoneCriticalPolicy, if_neg hc]
    obtain ⟨u', hu'⟩ := canonical_empty_post hx d
    exact ⟨u', _, _, hu'⟩

lemma subPost_valid_state (M : Model σ) (x : SubState) (a : Decision) (d : ℕ)
    (hx : x.1 = M.m + 1 → 1 ≤ x.2) :
    (M.subPost x a d).1 = M.m + 1 → 1 ≤ (M.subPost x a d).2 := by
  have hm := M.one_le_m
  by_cases hz : x.1 = M.m + 1
  · have hy := hx hz
    have hymove : 1 ≤ custMove d x.2 := SPD.custMove_pos d hy
    cases a <;> simp only [Model.subPost, hz, unitMove]
    all_goals split_ifs <;> simp_all <;> omega
  · have hmove := SPD.unitMove_ne M.m x.1 (decide (a = Decision.release)) hz
    simp only [Model.subPost]
    split_ifs <;> simp_all <;> omega

lemma critical_greedy (M : Model σ) (N n : ℕ) (s : σ) (x : SubState) (hnN : n ≤ N)
    (hx : x.1 = M.m + 1 → 1 ≤ x.2) :
    SPD.Q M (N - n) s x (M.criticalPolicy N n s x) = SPD.V M (N - n + 1) s x := by
  have hk : N + 1 - n = N - n + 1 := by omega
  calc
    SPD.Q M (N - n) s x (M.criticalPolicy N n s x) = M.subCost N (M.criticalPolicy N) n s x := by
      rw [Model.subCost, hk, Model.costToGo, SPD.Q]
      apply tsum_congr
      intro d
      congr 2
      congr 1
      apply Finset.sum_congr rfl
      intro s' _
      congr 1
      have hv := SPD.crit_core M N (n + 1) s'
        (M.subPost x (M.criticalPolicy N n s x) d).1
        (M.subPost x (M.criticalPolicy N n s x) d).2
        (subPost_valid_state M x _ d hx)
      rw [Model.subCost, SPD.subOpt_eq] at hv
      simpa only [Nat.add_sub_add_right] using hv.symm
    _ = SPD.V M (N - n + 1) s x := by
      rw [SPD.crit_core M N n s x.1 x.2 hx, SPD.subOpt_eq, hk]

lemma nonsupplier_greedy (M : Model σ) (k : ℕ) (s : σ) (x : SubState)
    (hx : x.1 ≠ M.m + 1) (a : Decision) :
    SPD.Q M k s x a = SPD.V M (k + 1) s x := by
  have heq : ∀ a', SPD.Q M k s x a' = SPD.Q M k s x Decision.hold := by
    intro a'
    simp only [SPD.Q, SPD.subPost_eq, SPD.unitMove_indep M.m x.1 _ false hx]
  rw [SPD.V_succ, heq a, heq Decision.release, min_self]

lemma monotoneCriticalPolicy_greedy (M : Model σ) (N n : ℕ) (s : σ) (x : SysState)
    (u v r : ℕ) (hx : Canonical M x u v r) (hnN : n ≤ N) (j : ℕ) :
    SPD.Q M (N - n) s (x.loc j, x.dist j)
      (if j ∈ (monotoneCriticalPolicy M N).act n s x then Decision.release else Decision.hold) =
        SPD.V M (N - n + 1) s (x.loc j, x.dist j) := by
  by_cases hz : x.loc j = M.m + 1
  · by_cases hc : M.criticalDistance N n s ≠ ⊤
    · have hY := criticalDistance_toNat_pos M N n s hc
      have hdist : 1 ≤ x.dist j := by
        have hzero := hx.zero_iff j
        have hm := M.one_le_m
        omega
      have hact : (if j ∈ (monotoneCriticalPolicy M N).act n s x then Decision.release else Decision.hold) =
          M.criticalPolicy N n s (x.loc j, x.dist j) := by
        simp only [monotoneCriticalPolicy, if_pos hc, hx.baseStockRelease_eq _ hY,
          Set.mem_ofPred_eq, hz, true_and, Model.criticalPolicy]
        rw [← ENat.coe_toNat hc]
        simp
        rfl
      rw [hact]
      exact critical_greedy M N n s _ hnN (fun _ => hdist)
    · have hterminal : N + 1 - n < M.m := by
        by_contra h
        exact hc (criticalDistance_finite M N n s (Nat.le_of_not_gt h))
      simp only [monotoneCriticalPolicy, if_neg hc, Set.mem_empty_iff_false, ite_false]
      rw [hz, SPD.V_succ]
      have hq : SPD.Q M (N - n) s (M.m + 1, x.dist j) Decision.release =
          SPD.Q M (N - n) s (M.m + 1, x.dist j) Decision.hold := by
        rw [← SPD.subQ_eq, ← SPD.subQ_eq,
          subQ_terminal M N n s (x.dist j) hnN hterminal,
          subQ_terminal M N n s (x.dist j) hnN hterminal]
      rw [hq, min_self]
  · exact nonsupplier_greedy M (N - n) s _ hz _

lemma monotoneCriticalPolicy_cost (M : Model σ) (N : ℕ) (s : σ) (a : ℕ → ℕ) (v : ℕ) :
    M.sysCost N (monotoneCriticalPolicy M N) 1 s (M.initState a v) =
      ∑' j : ℕ, M.subOpt N 1 s ((M.initState a v).loc j, (M.initState a v).dist j) := by
  simp only [Model.sysCost, SPD.subOpt_eq]
  apply monotone_greedy_cost M N (monotoneCriticalPolicy M N) (monotoneCriticalPolicy_monotone M N)
    (fun _ x => ∃ u v r, Canonical M x u v r)
  · rintro n x ⟨u, v, r, hx⟩
    exact ⟨hx.loc_monotone, hx.dist_monotone, hx.zero_iff⟩
  · rintro n s x _ ⟨u, v, r, hx⟩ d
    exact monotoneCriticalPolicy_preserves M N n s x u v r d hx
  · rintro n s x hnN ⟨u, v, r, hx⟩ j
    exact monotoneCriticalPolicy_greedy M N n s x u v r hx hnN j
  · rfl
  · exact ⟨0, v, _, canonical_initState M a v⟩

lemma monotoneCriticalPolicy_optimal (M : Model σ) (N : ℕ) (s : σ) (a : ℕ → ℕ) (v : ℕ) :
    M.sysCost N (monotoneCriticalPolicy M N) 1 s (M.initState a v) =
      M.sysOpt N 1 s (M.initState a v) := by
  obtain ⟨τ, hτ, hopt⟩ := (lemma1_monotone_committed M N).1
  apply le_antisymm
  · rw [monotoneCriticalPolicy_cost, ← hopt s a v]
    exact sum_subOpt_le_monotone_cost M N τ hτ s a v
  · exact iInf_le _ (monotoneCriticalPolicy M N)

lemma arbitraryBaseStock_cost_eq (M : Model σ) (N : ℕ) (π : SPolicy σ)
    (hπ : ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SysState),
      M.criticalDistance N n s ≠ ⊤ →
        π.act n s x = M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x)
    (k n : ℕ) (s : σ) (x : SysState) (u v r : ℕ)
    (hk : k = N + 1 - n) (hn : 1 ≤ n) (hx : Canonical M x u v r) :
    M.costToGo M.sysPost M.sysStage π.act k n s x =
      M.costToGo M.sysPost M.sysStage (monotoneCriticalPolicy M N).act k n s x := by
  induction k generalizing n s x u v r with
  | zero => rfl
  | succ k ih =>
    by_cases hterminal : k + 1 < M.m
    · exact terminal_cost_independent M π (monotoneCriticalPolicy M N) (k + 1) n s x x hterminal
        ⟨rfl, fun _ => Or.inl rfl⟩
    · have hnN : n ≤ N := by omega
      have hc := criticalDistance_finite M N n s (by omega)
      have hact := hπ n hn hnN s x hc
      have ha : (monotoneCriticalPolicy M N).act n s x = π.act n s x := by
        simp only [monotoneCriticalPolicy, if_pos hc, hact]
      simp only [Model.costToGo, ha]
      apply tsum_congr
      intro d
      obtain ⟨u', hu'⟩ := canonical_baseStock_post hx (M.criticalDistance N n s).toNat d
        (criticalDistance_toNat_pos M N n s hc)
      have hnext : Canonical M (M.sysPost x (π.act n s x) d) u' (v + d)
          (max r (v + (M.criticalDistance N n s).toNat - 1)) := by
        simpa only [hact] using hu'
      congr 2
      congr 1
      apply Finset.sum_congr rfl
      intro s' _
      congr 1
      exact ih (n + 1) s' _ u' (v + d) _ (by omega) (by omega) hnext

end ServiceParts.UnitDecomp.Proof

open ServiceParts.UnitDecomp.Proof

theorem solution {σ : Type} [Fintype σ] (M : Model σ) (N : ℕ) :
    (∃ π : SPolicy σ, ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SysState),
      M.criticalDistance N n s ≠ ⊤ →
        π.act n s x = M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x) ∧
    ∀ π : SPolicy σ,
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SysState),
        M.criticalDistance N n s ≠ ⊤ →
          π.act n s x = M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x) →
      ∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
        M.sysCost N π 1 s (M.initState a v₀) = M.sysOpt N 1 s (M.initState a v₀) := by
  constructor
  · exact baseStock_exists M N
  · intro π hπ s a v
    calc
      M.sysCost N π 1 s (M.initState a v) =
          M.sysCost N (monotoneCriticalPolicy M N) 1 s (M.initState a v) := by
        exact arbitraryBaseStock_cost_eq M N π hπ (N + 1 - 1) 1 s (M.initState a v)
          0 v (∑ i ∈ Finset.Icc 1 M.m, a i) rfl (by omega) (canonical_initState M a v)
      _ = M.sysOpt N 1 s (M.initState a v) := monotoneCriticalPolicy_optimal M N s a v
/- END INLINED Sol_ServiceParts_UnitDecomp_RootCorrect.lean -/

