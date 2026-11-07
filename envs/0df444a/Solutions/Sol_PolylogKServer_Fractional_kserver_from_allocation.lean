-- Prove2me | solution 1 for PolylogKServer.Fractional.kserver_from_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T07:23:07.817193+00:00
-- url     : https://prove2.me/submissions/9684a105-acde-4df7-a449-bc99e040f8cf

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PolylogKServer_Fractional_KServer
import Definitions.Def_PolylogKServer_Allocation_Problem

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 1000000


/-!
D1 (17428d40 relay 1): the integral count-trajectory optimum on the tree is at most the integral
offline k-server optimum on the leaf metric.
-/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Number of servers of `C` at the point `m`, as a real number. -/
noncomputable def cntR {k : ℕ} {M : Type} (C : KServer.Config k M) (m : M) : ℝ := by
  classical
  exact ((univ.filter fun i => C i = m).card : ℝ)

open Classical in
theorem cntR_eq {k : ℕ} {M : Type} (C : KServer.Config k M) (m : M) :
    cntR C m = ∑ i, if C i = m then (1 : ℝ) else 0 := by
  unfold cntR
  rw [Finset.sum_boole]

theorem sum_cntR {k : ℕ} {M : Type} [Fintype M] (C : KServer.Config k M) :
    ∑ m, cntR C m = k := by
  classical
  simp_rw [cntR_eq]
  rw [Finset.sum_comm]
  simp

theorem cntR_nonneg {k : ℕ} {M : Type} (C : KServer.Config k M) (m : M) : 0 ≤ cntR C m := by
  unfold cntR; positivity

theorem cntR_of_injective {k : ℕ} {M : Type} (C : KServer.Config k M) (hC : Function.Injective C)
    (m : M) : cntR C m = indicatorState C m := by
  classical
  rw [cntR_eq]
  unfold indicatorState
  by_cases hm : m ∈ Set.range C
  · obtain ⟨i0, rfl⟩ := hm
    rw [if_pos ⟨i0, rfl⟩]
    rw [Finset.sum_eq_single i0]
    · simp
    · intro b _ hb; rw [if_neg]; exact fun h => hb (hC h)
    · simp
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]; exact fun h => hm ⟨i, h⟩

theorem one_le_cntR {k : ℕ} {M : Type} (C : KServer.Config k M) (i : Fin k) :
    1 ≤ cntR C (C i) := by
  classical
  unfold cntR
  have : 1 ≤ (univ.filter fun j => C j = C i).card :=
    Finset.card_pos.2 ⟨i, by simp⟩
  exact_mod_cast this

open Classical in
theorem subtreeMass_cntR (T : WTree V) {k : ℕ} {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (C : KServer.Config k M) (v : V) :
    subtreeMass T e (cntR C) v = ∑ i, if T.IsAnc v (e (C i) : V) then (1 : ℝ) else 0 := by
  unfold subtreeMass
  have : ∀ m, (if T.IsAnc v (e m : V) then cntR C m else 0) =
      ∑ i, if C i = m then (if T.IsAnc v (e m : V) then (1 : ℝ) else 0) else 0 := by
    intro m
    rw [cntR_eq]
    split_ifs with h
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> rfl
    · simp
  calc (∑ m, if T.IsAnc v (e m : V) then cntR C m else 0)
      = ∑ m, ∑ i, if C i = m then (if T.IsAnc v (e m : V) then (1 : ℝ) else 0) else 0 := by
        convert Finset.sum_congr rfl fun m _ => this m
    _ = ∑ i, ∑ m, if C i = m then (if T.IsAnc v (e m : V) then (1 : ℝ) else 0) else 0 :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single (C i)]
        · simp
        · intro b _ hb; rw [if_neg]; exact fun h => hb h.symm
        · simp

/-- One step: the tree movement cost of the count vectors is at most the server movement. -/
theorem fracMoveCost_cntR_le (T : WTree V) {k : ℕ} {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (C C' : KServer.Config k M) :
    fracMoveCost T e (cntR C) (cntR C') ≤ ∑ i, T.treeDist (e (C i)) (e (C' i)) := by
  classical
  unfold fracMoveCost
  have key : ∀ v ∈ univ.filter (fun v => v ≠ T.root),
      T.W v * |subtreeMass T e (cntR C') v - subtreeMass T e (cntR C) v| ≤
        ∑ i, (if (T.IsAnc v (e (C i) : V) ↔ T.IsAnc v (e (C' i) : V)) then 0 else T.W v) := by
    intro v hv
    have hW : 0 < T.W v := T.W_pos v (Finset.mem_filter.1 hv).2
    rw [subtreeMass_cntR, subtreeMass_cntR, ← Finset.sum_sub_distrib]
    calc T.W v * |∑ i, ((if T.IsAnc v (e (C' i) : V) then (1 : ℝ) else 0) -
            (if T.IsAnc v (e (C i) : V) then (1 : ℝ) else 0))|
        ≤ T.W v * ∑ i, |(if T.IsAnc v (e (C' i) : V) then (1 : ℝ) else 0) -
            (if T.IsAnc v (e (C i) : V) then (1 : ℝ) else 0)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hW.le
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases a : T.IsAnc v (e (C i) : V) <;> by_cases b : T.IsAnc v (e (C' i) : V) <;>
            simp [a, b]
  calc _ ≤ ∑ v ∈ univ.filter (fun v => v ≠ T.root), ∑ i,
          (if (T.IsAnc v (e (C i) : V) ↔ T.IsAnc v (e (C' i) : V)) then 0 else T.W v) :=
        Finset.sum_le_sum key
    _ = ∑ i, ∑ v ∈ univ.filter (fun v => v ≠ T.root),
          (if (T.IsAnc v (e (C i) : V) ↔ T.IsAnc v (e (C' i) : V)) then 0 else T.W v) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold WTree.treeDist
        congr 1

theorem fracMoveCost_nonneg (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (x x' : M → ℝ) :
    0 ≤ fracMoveCost T e x x' := by
  unfold fracMoveCost
  refine Finset.sum_nonneg fun v hv => mul_nonneg (T.W_pos v (Finset.mem_filter.1 hv).2).le
    (abs_nonneg _)

/-- An integral count trajectory serving `ρ` from `C₀` (counts are naturals, read as reals). -/
def CountTraj (k : ℕ) {M : Type} [Fintype M] (C₀ : KServer.Config k M) (ρ : List M)
    (c : ℕ → M → ℝ) : Prop :=
  c 0 = indicatorState C₀ ∧ (∀ t m, ∃ n : ℕ, c t m = n) ∧ (∀ t, ∑ m, c t m = k) ∧
    ∀ j : Fin ρ.length, 1 ≤ c (j + 1) (ρ.get j)

/-- Tree cost of a count trajectory. -/
noncomputable def trajCost (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (ρ : List M)
    (c : ℕ → M → ℝ) : ℝ :=
  ∑ t ∈ range ρ.length, fracMoveCost T e (c t) (c (t + 1))

/-- The integral count-trajectory optimum on the tree. -/
noncomputable def treeOPT (T : WTree V) {k : ℕ} {M : Type} [Fintype M] (e : M ≃ T.Leaf)
    (C₀ : KServer.Config k M) (ρ : List M) : ℝ :=
  sInf {x : ℝ | ∃ c, CountTraj k C₀ ρ c ∧ x = trajCost T e ρ c}

theorem trajCost_nonneg (T : WTree V) {M : Type} [Fintype M] (e : M ≃ T.Leaf) (ρ : List M)
    (c : ℕ → M → ℝ) : 0 ≤ trajCost T e ρ c :=
  Finset.sum_nonneg fun _ _ => fracMoveCost_nonneg T e _ _

/-- D1: the count optimum is at most the integral offline optimum (k ≥ 1, C₀ injective). -/
theorem treeOPT_le_offlineCost (T : WTree V) {k : ℕ} (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    [Fintype M] (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e) (C₀ : KServer.Config k M)
    (hC₀ : Function.Injective C₀) (ρ : List M) :
    treeOPT T e C₀ ρ ≤ KServer.offlineCost C₀ ρ := by
  classical
  unfold KServer.offlineCost
  apply le_csInf
  · -- a serving schedule: all servers jump to the request
    let i0 : Fin k := ⟨0, hk⟩
    refine ⟨_, fun j => if j = 0 then C₀ else fun _ => ρ.getD (j - 1) (C₀ i0), ⟨rfl, ?_⟩, rfl⟩
    intro j
    refine ⟨i0, ?_⟩
    simp [List.getD_eq_getElem?_getD]
  · rintro x ⟨S, ⟨hS0, hS⟩, rfl⟩
    have hmem : trajCost T e ρ (fun t => cntR (S t)) ∈
        {x : ℝ | ∃ c, CountTraj k C₀ ρ c ∧ x = trajCost T e ρ c} := by
      refine ⟨_, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
      · funext m; show cntR (S 0) m = indicatorState C₀ m; rw [hS0]; exact cntR_of_injective C₀ hC₀ m
      · intro t m; exact ⟨_, rfl⟩
      · intro t; exact sum_cntR _
      · intro j
        obtain ⟨i, hi⟩ := hS j
        show 1 ≤ cntR (S (↑j + 1)) (ρ.get j)
        rw [← hi]; exact one_le_cntR _ i
    have hbdd : BddBelow {x : ℝ | ∃ c, CountTraj k C₀ ρ c ∧ x = trajCost T e ρ c} :=
      ⟨0, by rintro x ⟨c, _, rfl⟩; exact trajCost_nonneg T e ρ c⟩
    refine (csInf_le hbdd hmem).trans ?_
    unfold trajCost
    refine Finset.sum_le_sum fun t _ => ?_
    refine (fracMoveCost_cntR_le T e (S t) (S (t + 1))).trans (le_of_eq ?_)
    unfold KServer.moveCost
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hM]

end K17428


/-!
D3a (17428d40): augmenting-path reachability on a finite digraph. If the antisymmetrised net flow
`D u v = d u v - d v u` has net outflow `1` at `s`, `-1` at `t` and `0` elsewhere, then `t` is
reachable from `s` along arcs with `D > 0`.
-/

namespace K17428

open Finset

variable {N : Type} [Fintype N] [DecidableEq N]

theorem reach_of_unit_flow (d : N → N → ℤ) (s t : N) (hst : s ≠ t)
    (hnet : ∀ u, ∑ v, (d u v - d v u) = (if u = s then 1 else 0) - (if u = t then 1 else 0)) :
    Relation.ReflTransGen (fun u v => 0 < d u v - d v u) s t := by
  classical
  by_contra hT
  set R : Finset N := univ.filter (fun u => Relation.ReflTransGen (fun u v => 0 < d u v - d v u) s u)
    with hR
  have hsR : s ∈ R := by
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl
  have htR : t ∉ R := by simpa [hR] using hT
  -- sum of the net outflows over R
  have h1 : ∑ u ∈ R, ∑ v, (d u v - d v u) = 1 := by
    rw [Finset.sum_congr rfl fun u _ => hnet u, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_eq' R s (fun _ => (1 : ℤ)), Finset.sum_ite_eq' R t (fun _ => (1 : ℤ))]
    simp [hsR, htR]
  have hsplit : ∀ u, ∑ v, (d u v - d v u) =
      ∑ v ∈ R, (d u v - d v u) + ∑ v ∈ univ.filter (fun v => v ∉ R), (d u v - d v u) := by
    intro u
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun v => v ∈ R)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v; simp
  have hin : ∑ u ∈ R, ∑ v ∈ R, (d u v - d v u) = 0 := by
    have : ∑ u ∈ R, ∑ v ∈ R, (d u v - d v u) =
        ∑ u ∈ R, ∑ v ∈ R, d u v - ∑ u ∈ R, ∑ v ∈ R, d v u := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_sub_distrib]
    rw [this, Finset.sum_comm (s := R) (t := R) (f := fun u v => d v u)]
    ring
  have hout : ∑ u ∈ R, ∑ v ∈ univ.filter (fun v => v ∉ R), (d u v - d v u) ≤ 0 := by
    refine Finset.sum_nonpos fun u hu => Finset.sum_nonpos fun v hv => ?_
    by_contra hpos
    push Not at hpos
    have hu' : Relation.ReflTransGen (fun u v => 0 < d u v - d v u) s u := by
      simpa [hR] using hu
    have hv' : v ∈ R := by
      simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hu'.tail hpos
    exact (Finset.mem_filter.1 hv).2 hv'
  have : ∑ u ∈ R, ∑ v, (d u v - d v u) ≤ 0 := by
    rw [Finset.sum_congr rfl fun u _ => hsplit u, Finset.sum_add_distrib, hin, zero_add]
    exact hout
  omega

end K17428


/-! D3b (17428d40): reachability gives a walk without repeated nodes (shortest walk). -/

namespace K17428

/-- A walk of length `n` from `s` to `t` along `r`, as a function on `ℕ`. -/
def IsWalk {N : Type} (r : N → N → Prop) (s t : N) (n : ℕ) (p : ℕ → N) : Prop :=
  p 0 = s ∧ p n = t ∧ ∀ i < n, r (p i) (p (i + 1))

theorem walk_of_rtg {N : Type} (r : N → N → Prop) {s t : N} (h : Relation.ReflTransGen r s t) :
    ∃ n p, IsWalk r s t n p := by
  induction h with
  | refl => exact ⟨0, fun _ => s, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, p, h0, hn, hstep⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then p i else c, by simp [h0], by simp, ?_⟩
    intro i hi
    by_cases hin : i + 1 ≤ n
    · simp only [hin, if_true, show i ≤ n by omega]
      exact hstep i (by omega)
    · have : i = n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ i + 1 ≤ i by omega, if_false]
      rw [hn]; exact hbc

theorem exists_inj_walk {N : Type} (r : N → N → Prop) {s t : N}
    (h : ∃ n p, IsWalk r s t n p) :
    ∃ n p, IsWalk r s t n p ∧ ∀ i j, i ≤ n → j ≤ n → p i = p j → i = j := by
  classical
  let n := Nat.find h
  obtain ⟨p, hp⟩ := Nat.find_spec h
  refine ⟨n, p, hp, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨i, j, hi, hj, hpij, hij⟩ := hne
  -- wlog i < j
  have key : ∀ a b, a < b → b ≤ n → p a = p b → False := by
    intro a b hab hb hpab
    obtain ⟨h0, hn, hstep⟩ := hp
    have hlt : n - (b - a) < n := by omega
    have : ∃ q, IsWalk r s t (n - (b - a)) q := by
      refine ⟨fun k => if k ≤ a then p k else p (k + (b - a)), ?_, ?_, ?_⟩
      · simp [h0]
      · by_cases hna : n - (b - a) ≤ a
        · have : n - (b - a) = a := by omega
          simp only [hna, if_true]
          rw [this, hpab]
          have : b = n := by omega
          rw [this, hn]
        · simp only [hna, if_false]
          rw [show n - (b - a) + (b - a) = n by omega, hn]
      · intro k hk
        by_cases hka : k + 1 ≤ a
        · simp only [hka, if_true, show k ≤ a by omega]
          exact hstep k (by omega)
        · by_cases hk' : k = a
          · subst hk'
            simp only [le_refl, if_true, hka, if_false]
            rw [hpab, show k + 1 + (b - k) = b + 1 by omega]
            exact hstep b (by omega)
          · simp only [show ¬ k ≤ a by omega, hka, if_false]
            rw [show k + 1 + (b - a) = k + (b - a) + 1 by omega]
            exact hstep _ (by omega)
    exact absurd (Nat.find_min h hlt) (not_not.2 this)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hj hpij
  · exact key j i hlt hi hpij.symm

end K17428


/-! D3c (17428d40): conformal unit path in an antisymmetric integer flow with net `1_s - 1_z`.
Needs D3a (reach_of_unit_flow) and D3b (walk_of_rtg, exists_inj_walk). -/

namespace K17428

open Finset

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The signed indicator flow of a walk `p` of length `n`. -/
def walkFlow (p : ℕ → N) (n : ℕ) (u v : N) : ℤ :=
  ∑ i ∈ range n, ((if p i = u ∧ p (i + 1) = v then 1 else 0) -
    (if p i = v ∧ p (i + 1) = u then 1 else 0))

theorem walkFlow_anti (p : ℕ → N) (n : ℕ) (u v : N) : walkFlow p n u v = - walkFlow p n v u := by
  unfold walkFlow
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem walkFlow_net (p : ℕ → N) (n : ℕ) (u : N) :
    ∑ v, walkFlow p n u v = (if p 0 = u then 1 else 0) - (if p n = u then 1 else 0) := by
  unfold walkFlow
  rw [Finset.sum_comm]
  have h1 : ∀ i, ∑ v, ((if p i = u ∧ p (i + 1) = v then (1 : ℤ) else 0) -
      (if p i = v ∧ p (i + 1) = u then 1 else 0)) =
      (if p i = u then 1 else 0) - (if p (i + 1) = u then 1 else 0) := by
    intro i
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp_rw [ite_and]
      by_cases h : p i = u
      · simp [h]
      · simp [h]
    · simp_rw [and_comm (a := p i = _), ite_and]
      by_cases h : p (i + 1) = u
      · simp [h]
      · simp [h]
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  exact Finset.sum_range_sub' (fun i => if p i = u then (1 : ℤ) else 0) n

theorem card_step_le_one (p : ℕ → N) (n : ℕ)
    (hinj : ∀ i j, i ≤ n → j ≤ n → p i = p j → i = j) (u v : N) :
    ((range n).filter fun i => p i = u ∧ p (i + 1) = v).card ≤ 1 := by
  refine Finset.card_le_one.2 fun i hi j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi hj
  exact hinj i j (by omega) (by omega) (hi.2.1.trans hj.2.1.symm)

theorem walkFlow_eq_card (p : ℕ → N) (n : ℕ) (u v : N) :
    walkFlow p n u v = (((range n).filter fun i => p i = u ∧ p (i + 1) = v).card : ℤ) -
      (((range n).filter fun i => p i = v ∧ p (i + 1) = u).card : ℤ) := by
  unfold walkFlow
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]

/-- D3c: a conformal unit `s`-`z` path inside an antisymmetric integer flow of net `1_s - 1_z`. -/
theorem unit_path_exchange (x : N → N → ℤ) (hx : ∀ u v, x u v = - x v u) (s z : N) (hsz : s ≠ z)
    (hnet : ∀ u, ∑ v, x u v = (if u = s then 1 else 0) - (if u = z then 1 else 0)) :
    ∃ P : N → N → ℤ, (∀ u v, P u v = - P v u) ∧
      (∀ u, ∑ v, P u v = (if u = s then 1 else 0) - (if u = z then 1 else 0)) ∧
      (∀ u v, P u v = 0 ∨ (P u v = 1 ∧ 0 < x u v) ∨ (P u v = -1 ∧ x u v < 0)) ∧
      (∀ v, 0 ≤ P v z) ∧ (∀ v, 0 ≤ P s v) := by
  classical
  let d : N → N → ℤ := fun u v => max (x u v) 0
  have hd : ∀ u v, d u v - d v u = x u v := by
    intro u v
    show max (x u v) 0 - max (x v u) 0 = x u v
    rw [hx v u]
    rcases le_total (x u v) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hnet' : ∀ u, ∑ v, (d u v - d v u) = (if u = s then 1 else 0) - (if u = z then 1 else 0) := by
    intro u; simp_rw [hd]; exact hnet u
  have hr := reach_of_unit_flow d s z hsz hnet'
  simp_rw [hd] at hr
  obtain ⟨n, p, ⟨hp0, hpn, hstep⟩, hinj⟩ := exists_inj_walk _ (walk_of_rtg _ hr)
  refine ⟨walkFlow p n, walkFlow_anti p n, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [walkFlow_net, hp0, hpn]
    simp only [eq_comm (a := s), eq_comm (a := z)]
  · intro u v
    rw [walkFlow_eq_card]
    have hA := card_step_le_one p n hinj u v
    have hB := card_step_le_one p n hinj v u
    set A := ((range n).filter fun i => p i = u ∧ p (i + 1) = v).card with hAdef
    set B := ((range n).filter fun i => p i = v ∧ p (i + 1) = u).card with hBdef
    have hApos : 0 < A → 0 < x u v := by
      intro h
      obtain ⟨i, hi⟩ := Finset.card_pos.1 h
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      have := hstep i hi.1
      rwa [hi.2.1, hi.2.2] at this
    have hBpos : 0 < B → x u v < 0 := by
      intro h
      obtain ⟨i, hi⟩ := Finset.card_pos.1 h
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      have := hstep i hi.1
      rw [hi.2.1, hi.2.2] at this
      rw [hx u v]; linarith
    rcases Nat.eq_zero_or_pos A with hA0 | hA0 <;> rcases Nat.eq_zero_or_pos B with hB0 | hB0
    · left; rw [hA0, hB0]; simp
    · right; right
      refine ⟨?_, hBpos hB0⟩
      have : B = 1 := by omega
      rw [hA0, this]; simp
    · right; left
      refine ⟨?_, hApos hA0⟩
      have : A = 1 := by omega
      rw [hB0, this]; simp
    · exact absurd (hApos hA0) (not_lt.2 (le_of_lt (hBpos hB0)))
  · intro v
    rw [walkFlow_eq_card]
    have : ((range n).filter fun i => p i = z ∧ p (i + 1) = v) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun i hi h => ?_
      have hi' := Finset.mem_range.1 hi
      have := hinj i n (by omega) le_rfl (h.1.trans hpn.symm)
      omega
    rw [this]; simp
  · intro v
    rw [walkFlow_eq_card]
    have : ((range n).filter fun i => p i = v ∧ p (i + 1) = s) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun i hi h => ?_
      have hi' := Finset.mem_range.1 hi
      have := hinj (i + 1) 0 (by omega) (Nat.zero_le _) (h.2.trans hp0.symm)
      omega
    rw [this]; simp

end K17428


/-! D3d (17428d40): tree combinatorics for the time-expanded flow encoding: depth along parent
iterates, ancestors, the unique child towards a descendant, and the subtree-sum identity. -/

namespace K17428

open Finset PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V]

theorem depth_parent' (T : WTree V) (y : V) : T.depth (T.parent y) = T.depth y - 1 := by
  by_cases h : y = T.root
  · subst h; rw [T.parent_root, T.depth_root]
  · have := T.depth_parent y h; omega

theorem depth_iter (T : WTree V) (x : V) (i : ℕ) :
    T.depth (T.parent^[i] x) = T.depth x - i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', depth_parent', ih]; omega

theorem eq_root_of_depth (T : WTree V) {y : V} (h : T.depth y = 0) : y = T.root := by
  by_contra hy
  have := T.depth_parent y hy
  omega

theorem isAnc_root (T : WTree V) (x : V) : T.IsAnc T.root x :=
  ⟨T.depth x, eq_root_of_depth T (by rw [depth_iter]; omega)⟩

theorem isAnc_refl (T : WTree V) (x : V) : T.IsAnc x x := ⟨0, rfl⟩

theorem isAnc_trans (T : WTree V) {a b x : V} (hab : T.IsAnc a b) (hbx : T.IsAnc b x) :
    T.IsAnc a x := by
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hbx
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

theorem depth_le_of_isAnc (T : WTree V) {a x : V} (h : T.IsAnc a x) : T.depth a ≤ T.depth x := by
  obtain ⟨i, rfl⟩ := h
  rw [depth_iter]; omega

theorem isAnc_parent_self (T : WTree V) (x : V) : T.IsAnc (T.parent x) x := ⟨1, rfl⟩

theorem not_isAnc_parent (T : WTree V) {v : V} (hv : v ≠ T.root) : ¬ T.IsAnc v (T.parent v) := by
  intro h
  have h1 := depth_le_of_isAnc T h
  have h2 := T.depth_parent v hv
  omega

theorem isAnc_parent_of_ne (T : WTree V) {v u : V} (h : T.IsAnc v u) (hne : u ≠ v) :
    T.IsAnc v (T.parent u) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | zero => exact absurd hi hne
  | succ j => exact ⟨j, by rw [← Function.iterate_succ_apply]; exact hi⟩

theorem eq_of_isAnc_depth (T : WTree V) {a b x : V} (ha : T.IsAnc a x) (hb : T.IsAnc b x)
    (hd : T.depth a = T.depth b) : a = b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rw [depth_iter, depth_iter] at hd
  by_cases h0 : T.depth x - i = 0
  · have h1 : T.depth x - j = 0 := by omega
    rw [eq_root_of_depth T (y := T.parent^[i] x) (by rw [depth_iter]; exact h0),
      eq_root_of_depth T (y := T.parent^[j] x) (by rw [depth_iter]; exact h1)]
  · have : i = j := by omega
    rw [this]

/-- The set of children of `v`. -/
def children (T : WTree V) (v : V) : Finset V := univ.filter fun c => c ≠ T.root ∧ T.parent c = v

theorem mem_children (T : WTree V) {v c : V} : c ∈ children T v ↔ c ≠ T.root ∧ T.parent c = v := by
  simp [children]

theorem exists_child (T : WTree V) {v x : V} (h : T.IsAnc v x) (hne : x ≠ v) :
    ∃ c ∈ children T v, T.IsAnc c x := by
  classical
  let i := Nat.find h
  have hi : T.parent^[i] x = v := Nat.find_spec h
  have hi0 : i ≠ 0 := by
    intro h0; apply hne; have := hi; rw [h0] at this; exact this
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hpc : T.parent (T.parent^[j] x) = v := by
    rw [← Function.iterate_succ_apply' T.parent j x, ← hj]; exact hi
  refine ⟨T.parent^[j] x, (mem_children T).2 ⟨?_, hpc⟩, ⟨j, rfl⟩⟩
  intro hroot
  have hv : v = T.root := by rw [← hpc, hroot, T.parent_root]
  have : T.parent^[j] x = v := by rw [hroot, hv]
  exact Nat.find_min h (show j < i by omega) this

theorem child_unique (T : WTree V) {v x c c' : V} (hc : c ∈ children T v) (hc' : c' ∈ children T v)
    (hx : T.IsAnc c x) (hx' : T.IsAnc c' x) : c = c' := by
  rw [mem_children] at hc hc'
  refine eq_of_isAnc_depth T hx hx' ?_
  have h1 := T.depth_parent c hc.1
  have h2 := T.depth_parent c' hc'.1
  rw [hc.2] at h1; rw [hc'.2] at h2
  omega

theorem isAnc_of_child (T : WTree V) {v c x : V} (hc : c ∈ children T v) (hx : T.IsAnc c x) :
    T.IsAnc v x := by
  rw [mem_children] at hc
  exact isAnc_trans T (by rw [← hc.2]; exact isAnc_parent_self T c) hx

theorem ne_of_child (T : WTree V) {v c x : V} (hc : c ∈ children T v) (hx : T.IsAnc c x) :
    x ≠ v := by
  rintro rfl
  rw [mem_children] at hc
  exact not_isAnc_parent T hc.1 (by rw [hc.2]; exact hx)

open Classical in
/-- Number of children of `v` above `x`: one if `x` is a proper descendant of `v`, else zero. -/
theorem card_children_anc (T : WTree V) (v x : V) :
    ((children T v).filter fun c => T.IsAnc c x).card = if T.IsAnc v x ∧ x ≠ v then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨c, hc, hcx⟩ := exists_child T h.1 h.2
    refine Finset.card_eq_one.2 ⟨c, ?_⟩
    ext c'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc', hx'⟩; exact child_unique T hc' hc hx' hcx
    · rintro rfl; exact ⟨hc, hcx⟩
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun c hc hcx => h ?_)
    exact ⟨isAnc_of_child T hc hcx, ne_of_child T hc hcx⟩

variable {M : Type} [Fintype M]

open Classical in
/-- Integer subtree mass. -/
noncomputable def nsub (T : WTree V) (e : M ≃ T.Leaf) (a : M → ℤ) (v : V) : ℤ :=
  ∑ m, if T.IsAnc v (e m : V) then a m else 0

open Classical in
/-- The amount at the node `x` itself (zero unless `x` is a leaf). -/
noncomputable def cnt (T : WTree V) (e : M ≃ T.Leaf) (a : M → ℤ) (x : V) : ℤ :=
  ∑ m, if (e m : V) = x then a m else 0

theorem nsub_root (T : WTree V) (e : M ≃ T.Leaf) (a : M → ℤ) : nsub T e a T.root = ∑ m, a m := by
  unfold nsub
  exact Finset.sum_congr rfl fun m _ => if_pos (isAnc_root T _)

theorem nsub_split (T : WTree V) (e : M ≃ T.Leaf) (a : M → ℤ) (v : V) :
    nsub T e a v = cnt T e a v + ∑ c ∈ children T v, nsub T e a c := by
  classical
  unfold nsub cnt
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : (∑ c ∈ children T v, if T.IsAnc c (e m : V) then a m else 0) =
      ((children T v).filter fun c => T.IsAnc c (e m : V)).card • a m := by
    rw [← Finset.sum_filter, Finset.sum_const]
  rw [hc, card_children_anc]
  by_cases h1 : (e m : V) = v
  · have : T.IsAnc v (e m : V) := by rw [h1]; exact isAnc_refl T v
    simp [h1, isAnc_refl T v]
  · by_cases h2 : T.IsAnc v (e m : V)
    · simp [h1, h2]
    · simp [h1, h2]

open Classical in
/-- Summing the node amounts over a subtree gives the subtree mass. -/
theorem sum_cnt_subtree (T : WTree V) (e : M ≃ T.Leaf) (a : M → ℤ) (v : V) :
    ∑ u ∈ univ.filter (fun u => T.IsAnc v u), cnt T e a u = nsub T e a v := by
  unfold cnt nsub
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_ite_eq]
  by_cases h : T.IsAnc v (e m : V) <;> simp [h]

end K17428


/-! D3e (17428d40): arc-indexed (incidence) flows on a simple digraph and the conformal unit-path
exchange at the arc level. Needs D3a D3b D3c. -/

namespace K17428

open Finset

variable {A N : Type} [Fintype A] [Fintype N] [DecidableEq N]

/-- The antisymmetric node-pair flow of an arc flow `f`. -/
def gflow (tl hd : A → N) (f : A → ℤ) (u w : N) : ℤ :=
  ∑ α, f α * ((if tl α = u ∧ hd α = w then 1 else 0) - (if tl α = w ∧ hd α = u then 1 else 0))

/-- Net outflow of an arc flow at a node. -/
def anet (tl hd : A → N) (f : A → ℤ) (u : N) : ℤ :=
  ∑ α, f α * ((if tl α = u then 1 else 0) - (if hd α = u then 1 else 0))

theorem gflow_anti (tl hd : A → N) (f : A → ℤ) (u w : N) :
    gflow tl hd f u w = - gflow tl hd f w u := by
  unfold gflow
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

theorem gflow_net (tl hd : A → N) (f : A → ℤ) (u : N) :
    ∑ w, gflow tl hd f u w = anet tl hd f u := by
  unfold gflow anet
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 2
  · simp_rw [ite_and]
    by_cases h : tl α = u
    · simp [h]
    · simp [h]
  · simp_rw [and_comm (a := tl α = _), ite_and]
    by_cases h : hd α = u
    · simp [h]
    · simp [h]

/-- A simple digraph: no parallel arcs, no pair of opposite arcs (in particular no loops). -/
def SimpleArcs (tl hd : A → N) : Prop :=
  ∀ α β, (tl α = tl β → hd α = hd β → α = β) ∧ ¬ (tl α = hd β ∧ hd α = tl β)

theorem gflow_arc (tl hd : A → N) (hs : SimpleArcs tl hd) (f : A → ℤ) (α : A) :
    gflow tl hd f (tl α) (hd α) = f α := by
  classical
  unfold gflow
  rw [Finset.sum_eq_single α]
  · have : ¬ (tl α = hd α ∧ hd α = tl α) := (hs α α).2
    rw [if_pos ⟨rfl, rfl⟩, if_neg this]; ring
  · intro β _ hβ
    have h1 : ¬ (tl β = tl α ∧ hd β = hd α) := fun h => hβ ((hs β α).1 h.1 h.2)
    have h2 : ¬ (tl β = hd α ∧ hd β = tl α) := (hs β α).2
    rw [if_neg h1, if_neg h2]; ring
  · intro h; exact absurd (Finset.mem_univ α) h

theorem gflow_nonarc (tl hd : A → N) (f : A → ℤ) (u w : N)
    (h : ∀ α, ¬ (tl α = u ∧ hd α = w) ∧ ¬ (tl α = w ∧ hd α = u)) : gflow tl hd f u w = 0 := by
  unfold gflow
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [if_neg (h α).1, if_neg (h α).2]; ring

theorem gflow_sub (tl hd : A → N) (f g : A → ℤ) (u w : N) :
    gflow tl hd (fun α => g α - f α) u w = gflow tl hd g u w - gflow tl hd f u w := by
  unfold gflow
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

/-- D3e: arc-level conformal unit path. -/
theorem arc_exchange (tl hd : A → N) (hs : SimpleArcs tl hd) (fa fb : A → ℤ) (s z : N) (hsz : s ≠ z)
    (hnet : ∀ u, anet tl hd (fun α => fb α - fa α) u =
      (if u = s then 1 else 0) - (if u = z then 1 else 0)) :
    ∃ p : A → ℤ, (∀ α, p α = 0 ∨ (p α = 1 ∧ fa α < fb α) ∨ (p α = -1 ∧ fb α < fa α)) ∧
      (∀ u, anet tl hd p u = (if u = s then 1 else 0) - (if u = z then 1 else 0)) ∧
      (∀ α, hd α = z → 0 ≤ p α) ∧ (∀ α, tl α = s → 0 ≤ p α) := by
  classical
  set x := gflow tl hd (fun α => fb α - fa α) with hxdef
  obtain ⟨P, hPa, hPn, hPc, hPz, hPs⟩ := unit_path_exchange x (gflow_anti tl hd _) s z hsz
    (fun u => by rw [hxdef, gflow_net]; exact hnet u)
  have hxarc : ∀ α, x (tl α) (hd α) = fb α - fa α := fun α => gflow_arc tl hd hs _ α
  refine ⟨fun α => P (tl α) (hd α), ?_, ?_, ?_, ?_⟩
  · intro α
    rcases hPc (tl α) (hd α) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · right; left; refine ⟨h1, ?_⟩; rw [hxarc] at h2; linarith
    · right; right; refine ⟨h1, ?_⟩; rw [hxarc] at h2; linarith
  · -- the arc flow of `P` reproduces `P`
    have hP : ∀ u w, gflow tl hd (fun α => P (tl α) (hd α)) u w = P u w := by
      intro u w
      by_cases h1 : ∃ α, tl α = u ∧ hd α = w
      · obtain ⟨α, rfl, rfl⟩ := h1
        exact gflow_arc tl hd hs _ α
      · by_cases h2 : ∃ α, tl α = w ∧ hd α = u
        · obtain ⟨α, rfl, rfl⟩ := h2
          rw [gflow_anti, gflow_arc tl hd hs _ α, hPa]; ring
        · push Not at h1 h2
          rw [gflow_nonarc tl hd _ u w fun α => ⟨fun h => h1 α h.1 h.2, fun h => h2 α h.1 h.2⟩]
          have hx0 : x u w = 0 :=
            gflow_nonarc tl hd _ u w fun α => ⟨fun h => h1 α h.1 h.2, fun h => h2 α h.1 h.2⟩
          rcases hPc u w with h | ⟨_, h⟩ | ⟨_, h⟩
          · exact h.symm
          · rw [hx0] at h; exact absurd h (lt_irrefl 0)
          · rw [hx0] at h; exact absurd h (lt_irrefl 0)
    intro u
    rw [← gflow_net]
    simp_rw [hP]
    exact hPn u
  · intro α hα; show 0 ≤ P (tl α) (hd α); rw [hα]; exact hPz _
  · intro α hα; show 0 ≤ P (tl α) (hd α); rw [hα]; exact hPs _

end K17428


/-! D3f (17428d40): the time-expanded network of count trajectories on a tree, its simplicity,
and the subtree sum of node net flows. Needs D3e (gflow/anet/SimpleArcs) and D3d (tree lemmas). -/

namespace K17428

open Finset PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

/-- Arcs: `src m : s → (0, m)`, `sto (t, m) : (t, m) → (t+1, m)` (or `→ z` at `t = H`),
`tre (t, v) : (t, v) → (t, parent v)`. -/
abbrev XArc (T : WTree V) (M : Type) (H : ℕ) :=
  M ⊕ (Fin (H + 1) × M) ⊕ (Fin (H + 1) × {v : V // v ≠ T.root})

/-- Nodes: layer nodes `(t, v)` and the source `inr true`, sink `inr false`. -/
abbrev XNode (V : Type) (H : ℕ) := (Fin (H + 1) × V) ⊕ Bool

/-- The successor storage node. -/
def nxt {H : ℕ} (t : Fin (H + 1)) (x : V) : XNode V H :=
  if h : (t : ℕ) < H then Sum.inl (⟨t + 1, by omega⟩, x) else Sum.inr false

theorem nxt_eq_inl {H : ℕ} (t t' : Fin (H + 1)) (x y : V) :
    (nxt t x : XNode V H) = Sum.inl (t', y) ↔ (t' : ℕ) = t + 1 ∧ y = x := by
  unfold nxt
  split_ifs with h
  · simp only [Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  · simp only [reduceCtorEq, false_iff, not_and]
    intro h1; have := t'.isLt; omega

theorem nxt_ne_src {H : ℕ} (t : Fin (H + 1)) (x : V) : (nxt t x : XNode V H) ≠ Sum.inr true := by
  unfold nxt; split_ifs <;> simp

variable (T : WTree V) (e : M ≃ T.Leaf) (H : ℕ)

def xtl : XArc T M H → XNode V H
  | Sum.inl _ => Sum.inr true
  | Sum.inr (Sum.inl (t, m)) => Sum.inl (t, (e m : V))
  | Sum.inr (Sum.inr (t, v)) => Sum.inl (t, v.1)

def xhd : XArc T M H → XNode V H
  | Sum.inl m => Sum.inl (0, (e m : V))
  | Sum.inr (Sum.inl (t, m)) => nxt t (e m : V)
  | Sum.inr (Sum.inr (t, v)) => Sum.inl (t, T.parent v.1)

theorem leaf_coe_inj {m m' : M} (h : ((e m : T.Leaf) : V) = (e m' : V)) : m = m' :=
  e.injective (Subtype.ext h)

theorem xsimple : SimpleArcs (xtl T e H) (xhd T e H) := by
  intro α β
  rcases α with m | ⟨t, m⟩ | ⟨t, v⟩ <;> rcases β with m' | ⟨t', m'⟩ | ⟨t', v'⟩ <;>
    refine ⟨fun h1 h2 => ?_, fun h => ?_⟩
  -- src, src
  · simp only [xhd, Sum.inl.injEq, Prod.mk.injEq] at h2
    rw [leaf_coe_inj T e h2.2]
  · simp [xtl, xhd] at h
  · simp [xtl] at h1
  · simp only [xtl, xhd] at h
    exact nxt_ne_src _ _ h.1.symm
  · simp [xtl] at h1
  · simp [xtl, xhd] at h
  -- sto, *
  · simp [xtl] at h1
  · simp only [xtl, xhd] at h
    exact nxt_ne_src t _ h.2
  · simp only [xtl, Sum.inl.injEq, Prod.mk.injEq] at h1
    rw [h1.1, leaf_coe_inj T e h1.2]
  · simp only [xtl, xhd] at h
    obtain ⟨h1, h2⟩ := h
    rw [eq_comm, nxt_eq_inl] at h1
    rw [nxt_eq_inl] at h2
    omega
  · simp only [xhd] at h2
    rw [nxt_eq_inl] at h2
    simp only [xtl, Sum.inl.injEq, Prod.mk.injEq] at h1
    rw [h1.1] at h2; omega
  · simp only [xtl, xhd] at h
    obtain ⟨h1, h2⟩ := h
    rw [nxt_eq_inl] at h2
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h1
    rw [h1.1] at h2; omega
  -- tre, *
  · simp [xtl] at h1
  · simp [xtl, xhd] at h
  · simp only [xhd] at h2
    rw [eq_comm, nxt_eq_inl] at h2
    simp only [xtl, Sum.inl.injEq, Prod.mk.injEq] at h1
    rw [h1.1] at h2; omega
  · simp only [xtl, xhd] at h
    obtain ⟨h1, h2⟩ := h
    rw [eq_comm, nxt_eq_inl] at h1
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h2
    rw [h2.1] at h1; omega
  · simp only [xtl, Sum.inl.injEq, Prod.mk.injEq] at h1
    rw [h1.1, Subtype.ext h1.2]
  · simp only [xtl, xhd, Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ := h
    have hv : T.parent v'.1 ≠ T.root := by rw [← h1]; exact v.2
    have d1 := T.depth_parent _ hv
    have d2 := T.depth_parent v'.1 v'.2
    have h3 : T.parent (T.parent v'.1) = v'.1 := by rw [← h1]; exact h2
    rw [h3] at d1
    omega

open Classical in
/-- Membership of a node in the layer-`t` copy of the subtree `T(x)`. -/
def inS {H : ℕ} (t : Fin (H + 1)) (x : V) : XNode V H → Prop
  | Sum.inl (t', y) => t' = t ∧ T.IsAnc x y
  | Sum.inr _ => False

open Classical in
theorem sum_ind_layer {H : ℕ} (t : Fin (H + 1)) (x : V) (n : XNode V H) :
    (∑ u ∈ univ.filter (fun u => T.IsAnc x u), if n = Sum.inl (t, u) then (1 : ℤ) else 0) =
      if inS T t x n then 1 else 0 := by
  rcases n with ⟨t', y⟩ | b
  · simp only [Sum.inl.injEq, Prod.mk.injEq, inS]
    by_cases ht : t' = t
    · subst ht
      simp only [true_and]
      rw [Finset.sum_ite_eq]
      simp
    · simp [ht]
  · simp [inS]

/-- In-value at layer `t`: the source values at `t = 0`, else the storage values of layer `t - 1`. -/
def inv {H : ℕ} (f : XArc T M H → ℤ) (t : Fin (H + 1)) (m : M) : ℤ :=
  if (t : ℕ) = 0 then f (Sum.inl m) else f (Sum.inr (Sum.inl (⟨t - 1, by omega⟩, m)))

open Classical in
/-- Subtree sum of the node net flows at layer `t`. -/
theorem sum_anet_subtree (f : XArc T M H → ℤ) (t : Fin (H + 1)) (x : V) :
    ∑ u ∈ univ.filter (fun u => T.IsAnc x u), anet (xtl T e H) (xhd T e H) f (Sum.inl (t, u)) =
      nsub T e (fun m => f (Sum.inr (Sum.inl (t, m)))) x - nsub T e (inv T f t) x +
        (if h : x ≠ T.root then f (Sum.inr (Sum.inr (t, ⟨x, h⟩))) else 0) := by
  unfold anet
  rw [Finset.sum_comm]
  have hin : ∀ α, (∑ u ∈ univ.filter (fun u => T.IsAnc x u),
      f α * ((if xtl T e H α = Sum.inl (t, u) then 1 else 0) -
        (if xhd T e H α = Sum.inl (t, u) then 1 else 0))) =
      f α * ((if inS T t x (xtl T e H α) then 1 else 0) - (if inS T t x (xhd T e H α) then 1 else 0)) := by
    intro α
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_ind_layer, sum_ind_layer]
  rw [Finset.sum_congr rfl fun α _ => hin α]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  -- source arcs
  have hsrc : (∑ m : M, f (Sum.inl m) * ((if inS T t x (xtl T e H (Sum.inl m)) then (1 : ℤ) else 0) -
      (if inS T t x (xhd T e H (Sum.inl m)) then 1 else 0))) =
      - if (t : ℕ) = 0 then nsub T e (fun m => f (Sum.inl m)) x else 0 := by
    have hm : ∀ m, f (Sum.inl m) * ((if inS T t x (xtl T e H (Sum.inl m)) then (1 : ℤ) else 0) -
        (if inS T t x (xhd T e H (Sum.inl m)) then 1 else 0)) =
        -(if (t : ℕ) = 0 then (if T.IsAnc x (e m : V) then f (Sum.inl m) else 0) else 0) := by
      intro m
      simp only [xtl, xhd, inS]
      by_cases ht : (t : ℕ) = 0
      · have h0 : (0 : Fin (H + 1)) = t := Fin.ext ht.symm
        by_cases ha : T.IsAnc x (e m : V) <;> simp [h0, ht, ha]
      · have h0 : (0 : Fin (H + 1)) ≠ t := fun h => ht (by rw [← h]; rfl)
        simp [h0, ht]
    rw [Finset.sum_congr rfl fun m _ => hm m, Finset.sum_neg_distrib]
    congr 1
    unfold nsub
    by_cases ht : (t : ℕ) = 0 <;> simp [ht]
  -- storage arcs
  have hsto : (∑ t' : Fin (H + 1), ∑ m : M, f (Sum.inr (Sum.inl (t', m))) *
      ((if inS T t x (xtl T e H (Sum.inr (Sum.inl (t', m)))) then (1 : ℤ) else 0) -
        (if inS T t x (xhd T e H (Sum.inr (Sum.inl (t', m)))) then 1 else 0))) =
      nsub T e (fun m => f (Sum.inr (Sum.inl (t, m)))) x -
        (if h : (t : ℕ) = 0 then 0 else
          nsub T e (fun m => f (Sum.inr (Sum.inl (⟨t - 1, by omega⟩, m)))) x) := by
    have hhd : ∀ t' m, inS T t x (xhd T e H (Sum.inr (Sum.inl (t', m)))) ↔
        ((t : ℕ) = t' + 1 ∧ T.IsAnc x (e m : V)) := by
      intro t' m
      simp only [xhd, nxt]
      split_ifs with h
      · simp only [inS, Fin.ext_iff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2⟩
      · simp only [inS, false_iff, not_and]
        intro h1; have := t.isLt; omega
    simp only [hhd]
    simp only [xtl, inS]
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single t]
      · unfold nsub
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs <;> simp_all
      · intro b _ hb
        refine Finset.sum_eq_zero fun m _ => ?_
        simp [hb]
      · simp
    · split_ifs with ht
      · refine Finset.sum_eq_zero fun t' _ => Finset.sum_eq_zero fun m _ => ?_
        have : ¬ ((t : ℕ) = t' + 1 ∧ T.IsAnc x (e m : V)) := fun h => by omega
        simp [this]
      · rw [Finset.sum_eq_single ⟨t - 1, by omega⟩]
        · unfold nsub
          refine Finset.sum_congr rfl fun m _ => ?_
          have h' : (t : ℕ) - 1 + 1 = t := by omega
          by_cases ha : T.IsAnc x (e m : V) <;> simp [ha, h']
        · intro b _ hb
          refine Finset.sum_eq_zero fun m _ => ?_
          have : ¬ ((t : ℕ) = b + 1 ∧ T.IsAnc x (e m : V)) := by
            rintro ⟨h1, _⟩; apply hb; ext; simp; omega
          simp [this]
        · simp
  -- tree arcs
  have htre : (∑ t' : Fin (H + 1), ∑ v : {v : V // v ≠ T.root}, f (Sum.inr (Sum.inr (t', v))) *
      ((if inS T t x (xtl T e H (Sum.inr (Sum.inr (t', v)))) then (1 : ℤ) else 0) -
        (if inS T t x (xhd T e H (Sum.inr (Sum.inr (t', v)))) then 1 else 0))) =
      (if h : x ≠ T.root then f (Sum.inr (Sum.inr (t, ⟨x, h⟩))) else 0) := by
    simp only [xtl, xhd, inS]
    rw [Finset.sum_eq_single t]
    · simp only [true_and]
      have key : ∀ v : {v : V // v ≠ T.root},
          ((if T.IsAnc x v.1 then (1 : ℤ) else 0) - (if T.IsAnc x (T.parent v.1) then 1 else 0)) =
            if v.1 = x then 1 else 0 := by
        intro v
        by_cases hvx : v.1 = x
        · rw [if_pos hvx, hvx, if_pos (isAnc_refl T x)]
          rw [if_neg (not_isAnc_parent T (hvx ▸ v.2))]; ring
        · rw [if_neg hvx]
          by_cases ha : T.IsAnc x v.1
          · rw [if_pos ha, if_pos (isAnc_parent_of_ne T ha hvx)]; ring
          · have : ¬ T.IsAnc x (T.parent v.1) := fun h' =>
              ha (isAnc_trans T h' (isAnc_parent_self T v.1))
            rw [if_neg ha, if_neg this]; ring
      simp only [key, mul_ite, mul_one, mul_zero]
      split_ifs with hx
      · rw [Finset.sum_eq_single ⟨x, hx⟩]
        · simp
        · intro b _ hb; rw [if_neg]; exact fun h => hb (Subtype.ext h)
        · simp
      · refine Finset.sum_eq_zero fun v _ => ?_
        rw [if_neg]; intro h; exact v.2 (by rw [h]; push Not at hx; exact hx)
    · intro b _ hb
      refine Finset.sum_eq_zero fun v _ => ?_
      simp [hb]
    · simp
  rw [hsrc, hsto, htre]
  unfold inv
  by_cases ht : (t : ℕ) = 0
  · simp only [ht, if_true, dif_pos]
    ring
  · simp only [ht, if_false, dif_neg, not_false_eq_true]
    ring

end K17428


/-! D3g (17428d40): encoding count trajectories as arc flows of the time-expanded network,
decoding, cost identities, and the trajectory exchange (Cote et al. Cor. 2 core).
Needs D3a-D3f. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

theorem anet_sub {A N : Type} [Fintype A] [DecidableEq N] (tl hd : A → N) (f g : A → ℤ) (u : N) :
    anet tl hd (fun α => g α - f α) u = anet tl hd g u - anet tl hd f u := by
  unfold anet; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_; ring

theorem anet_add {A N : Type} [Fintype A] [DecidableEq N] (tl hd : A → N) (f g : A → ℤ) (u : N) :
    anet tl hd (fun α => f α + g α) u = anet tl hd f u + anet tl hd g u := by
  unfold anet; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_; ring

open Classical in
/-- Node-function version of the subtree split. -/
theorem subtree_split (T : WTree V) (φ : V → ℤ) (x : V) :
    ∑ u ∈ univ.filter (fun u => T.IsAnc x u), φ u =
      φ x + ∑ c ∈ children T x, ∑ u ∈ univ.filter (fun u => T.IsAnc c u), φ u := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  have : ∀ u, (∑ c ∈ children T x, if T.IsAnc c u then φ u else 0) =
      if T.IsAnc x u ∧ u ≠ x then φ u else 0 := by
    intro u
    rw [← Finset.sum_filter, Finset.sum_const, card_children_anc]
    split_ifs <;> simp
  simp_rw [this]
  have hx : φ x = ∑ u, if u = x then φ u else 0 := by simp
  rw [hx, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h1 : u = x
  · subst h1; simp [isAnc_refl]
  · by_cases h2 : T.IsAnc x u <;> simp [h1, h2]

variable (T : WTree V) (e : M ≃ T.Leaf) (H : ℕ)

/-- Arc flow of a count trajectory `a`. -/
noncomputable def encA (a : ℕ → M → ℤ) : XArc T M H → ℤ
  | Sum.inl m => a 0 m
  | Sum.inr (Sum.inl (t, m)) => a t m
  | Sum.inr (Sum.inr (t, v)) => nsub T e (a (t - 1)) v - nsub T e (a t) v

/-- Decoded trajectory of an arc flow (storage values). -/
def dec (f : XArc T M H → ℤ) (t : ℕ) (m : M) : ℤ :=
  if h : t ≤ H then f (Sum.inr (Sum.inl (⟨t, by omega⟩, m))) else 0

/-- Tree cost of an arc flow. -/
noncomputable def acost (f : XArc T M H → ℤ) : ℝ :=
  ∑ t : Fin (H + 1), ∑ v : {v : V // v ≠ T.root}, T.W v * |((f (Sum.inr (Sum.inr (t, v))) : ℤ) : ℝ)|

/-- Tree cost of an integer trajectory up to the horizon `H`. -/
noncomputable def tcost (a : ℕ → M → ℤ) : ℝ :=
  ∑ t ∈ range H, fracMoveCost T e (fun m => (a t m : ℝ)) (fun m => (a (t + 1) m : ℝ))

theorem subtreeMass_cast (a : M → ℤ) (v : V) :
    subtreeMass T e (fun m => (a m : ℝ)) v = (nsub T e a v : ℝ) := by
  unfold subtreeMass nsub
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp_all

theorem fracMoveCost_nsub (a b : M → ℤ) :
    fracMoveCost T e (fun m => (a m : ℝ)) (fun m => (b m : ℝ)) =
      ∑ v : {v : V // v ≠ T.root}, T.W v * |((nsub T e b v - nsub T e a v : ℤ) : ℝ)| := by
  unfold fracMoveCost
  rw [Finset.sum_subtype (univ.filter fun v => v ≠ T.root) (p := fun v => v ≠ T.root) (by simp)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [subtreeMass_cast, subtreeMass_cast]; push_cast; ring_nf

theorem acost_eq_tcost (a : ℕ → M → ℤ) (f : XArc T M H → ℤ)
    (h0 : ∀ v, f (Sum.inr (Sum.inr (0, v))) = 0)
    (h : ∀ t : Fin (H + 1), (t : ℕ) ≠ 0 → ∀ v,
      f (Sum.inr (Sum.inr (t, v))) = nsub T e (a (t - 1)) v - nsub T e (a t) v) :
    acost T H f = tcost T e H a := by
  unfold acost tcost
  rw [Fin.sum_univ_succ]
  simp only [h0, Int.cast_zero, abs_zero, mul_zero, Finset.sum_const_zero, zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fracMoveCost_nsub]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [h i.succ (by simp)]
  simp only [Fin.val_succ, Nat.add_sub_cancel]
  push_cast
  rw [abs_sub_comm]

theorem anet_src (f : XArc T M H → ℤ) :
    anet (xtl T e H) (xhd T e H) f (Sum.inr true) = ∑ m, f (Sum.inl m) := by
  unfold anet
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∀ x : Fin (H + 1) × M, f (Sum.inr (Sum.inl x)) *
      ((if xtl T e H (Sum.inr (Sum.inl x)) = Sum.inr true then (1 : ℤ) else 0) -
        (if xhd T e H (Sum.inr (Sum.inl x)) = Sum.inr true then 1 else 0)) = 0 := by
    rintro ⟨t, m⟩
    simp [xtl, xhd, nxt_ne_src]
  have h3 : ∀ x : Fin (H + 1) × {v : V // v ≠ T.root}, f (Sum.inr (Sum.inr x)) *
      ((if xtl T e H (Sum.inr (Sum.inr x)) = Sum.inr true then (1 : ℤ) else 0) -
        (if xhd T e H (Sum.inr (Sum.inr x)) = Sum.inr true then 1 else 0)) = 0 := by
    rintro ⟨t, v⟩
    simp [xtl, xhd]
  simp only [h2, h3, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [xtl, xhd]

theorem nxt_eq_snk {H : ℕ} (t : Fin (H + 1)) (x : V) :
    (nxt t x : XNode V H) = Sum.inr false ↔ (t : ℕ) = H := by
  unfold nxt
  split_ifs with h
  · simp; omega
  · simp; have := t.isLt; omega

theorem anet_snk (f : XArc T M H → ℤ) :
    anet (xtl T e H) (xhd T e H) f (Sum.inr false) =
      - ∑ m, f (Sum.inr (Sum.inl (Fin.last H, m))) := by
  unfold anet
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h1 : ∀ m : M, f (Sum.inl m) *
      ((if xtl T e H (Sum.inl m) = Sum.inr false then (1 : ℤ) else 0) -
        (if xhd T e H (Sum.inl m) = Sum.inr false then 1 else 0)) = 0 := by
    intro m; simp [xtl, xhd]
  have h3 : ∀ x : Fin (H + 1) × {v : V // v ≠ T.root}, f (Sum.inr (Sum.inr x)) *
      ((if xtl T e H (Sum.inr (Sum.inr x)) = Sum.inr false then (1 : ℤ) else 0) -
        (if xhd T e H (Sum.inr (Sum.inr x)) = Sum.inr false then 1 else 0)) = 0 := by
    rintro ⟨t, v⟩
    simp [xtl, xhd]
  simp only [h1, h3, Finset.sum_const_zero, zero_add, add_zero]
  rw [Finset.sum_eq_single (Fin.last H)]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [xtl, xhd, nxt_eq_snk]
  · intro b _ hb
    refine Finset.sum_eq_zero fun m _ => ?_
    have : ¬ ((b : ℕ) = H) := fun h => hb (Fin.ext (by simp [h]))
    simp [xtl, xhd, nxt_eq_snk, this]
  · simp

open Classical in
/-- All subtree sums of the layer nets vanish -> all layer nets vanish. -/
theorem anet_zero_of_subtree (f : XArc T M H → ℤ) (t : Fin (H + 1))
    (hS : ∀ x, ∑ u ∈ univ.filter (fun u => T.IsAnc x u),
      anet (xtl T e H) (xhd T e H) f (Sum.inl (t, u)) = 0) (x : V) :
    anet (xtl T e H) (xhd T e H) f (Sum.inl (t, x)) = 0 := by
  have := subtree_split T (fun u => anet (xtl T e H) (xhd T e H) f (Sum.inl (t, u))) x
  rw [hS x, Finset.sum_eq_zero fun c _ => hS c] at this
  linarith

theorem nsub_root' (a : M → ℤ) : nsub T e a T.root = ∑ m, a m := nsub_root T e a

open Classical in
theorem encA_layer (a : ℕ → M → ℤ) (ha : ∀ t ≤ H, ∑ m, a t m = ∑ m, a 0 m)
    (t : Fin (H + 1)) (x : V) :
    anet (xtl T e H) (xhd T e H) (encA T e H a) (Sum.inl (t, x)) = 0 := by
  refine anet_zero_of_subtree T e H _ t (fun y => ?_) x
  rw [sum_anet_subtree]
  have hinv : inv T (encA T e H a) t = a (t - 1) := by
    funext m; unfold inv
    split_ifs with ht
    · simp [encA, ht]
    · simp [encA]
  rw [hinv]
  simp only [encA]
  split_ifs with hy
  · ring
  · push Not at hy; subst hy
    rw [nsub_root, nsub_root, ha t (by omega), ha (t - 1) (by omega)]
    ring

theorem nsub_leaf (a : M → ℤ) (m : M) : nsub T e a (e m : V) = a m := by
  classical
  unfold nsub
  rw [Finset.sum_eq_single m]
  · rw [if_pos (isAnc_refl T _)]
  · intro b _ hb
    rw [if_neg]
    intro h
    by_cases hbm : (e b : V) = (e m : V)
    · exact hb (leaf_coe_inj T e hbm)
    · obtain ⟨c, hc, _⟩ := exists_child T h hbm
      rw [mem_children] at hc
      exact (e m).2 c hc.1 hc.2
  · simp

/-- Decoding: zero layer nets and zero layer-0 tree flow give a trajectory whose tree moves are
the tree-arc values. -/
theorem dec_spec (f : XArc T M H → ℤ)
    (hlay : ∀ t x, anet (xtl T e H) (xhd T e H) f (Sum.inl (t, x)) = 0)
    (h0 : ∀ v, f (Sum.inr (Sum.inr (0, v))) = 0) :
    (∀ m, dec T H f 0 m = f (Sum.inl m)) ∧
    (∀ t : Fin (H + 1), (t : ℕ) ≠ 0 → ∀ v : {v : V // v ≠ T.root},
      f (Sum.inr (Sum.inr (t, v))) = nsub T e (dec T H f (t - 1)) v - nsub T e (dec T H f t) v) ∧
    (∀ t ≤ H, ∑ m, dec T H f t m = ∑ m, f (Sum.inl m)) := by
  classical
  have hS : ∀ (t : Fin (H + 1)) x, nsub T e (fun m => f (Sum.inr (Sum.inl (t, m)))) x -
      nsub T e (inv T f t) x + (if h : x ≠ T.root then f (Sum.inr (Sum.inr (t, ⟨x, h⟩))) else 0) = 0 := by
    intro t x
    have := sum_anet_subtree T e H f t x
    rw [Finset.sum_eq_zero fun u _ => hlay t u] at this
    linarith
  have hdec : ∀ t : Fin (H + 1), dec T H f t = fun m => f (Sum.inr (Sum.inl (t, m))) := by
    intro t; funext m; unfold dec; rw [dif_pos (by omega)]
  have hinv : ∀ t : Fin (H + 1), (t : ℕ) ≠ 0 → inv T f t = dec T H f (t - 1) := by
    intro t ht; funext m; unfold inv dec; rw [if_neg ht, dif_pos (by omega)]
  have hinv0 : inv T f 0 = fun m => f (Sum.inl m) := by funext m; simp [inv]
  refine ⟨?_, ?_, ?_⟩
  · intro m
    have := hS 0 (e m : V)
    rw [hinv0, nsub_leaf, nsub_leaf] at this
    have h00 : (if h : (e m : V) ≠ T.root then f (Sum.inr (Sum.inr (0, ⟨(e m : V), h⟩))) else 0) = 0 := by
      split_ifs <;> simp [h0]
    rw [h00] at this
    have hd0 : dec T H f 0 m = f (Sum.inr (Sum.inl (0, m))) := by simp [dec]
    rw [hd0]
    linarith
  · intro t ht v
    have := hS t v.1
    rw [hinv t ht, dif_pos v.2, ← hdec t] at this
    linarith
  · intro t
    induction t with
    | zero =>
      intro _
      have h := hS 0 T.root
      rw [hinv0, dif_neg (by simp), nsub_root, nsub_root] at h
      have hd0 : ∀ m, dec T H f 0 m = f (Sum.inr (Sum.inl (0, m))) := fun m => by simp [dec]
      simp_rw [hd0]
      linarith
    | succ n ih =>
      intro hn
      have h := hS ⟨n + 1, by omega⟩ T.root
      rw [hinv ⟨n + 1, by omega⟩ (by simp), dif_neg (by simp), nsub_root, nsub_root] at h
      rw [show dec T H f (n + 1) = dec T H f ((⟨n + 1, by omega⟩ : Fin (H + 1)) : ℕ) from rfl,
        hdec ⟨n + 1, by omega⟩]
      simp only [Fin.val_mk, Nat.add_sub_cancel] at h
      have := ih (by omega)
      linarith

theorem abs_exchange (a b p : ℤ)
    (hp : p = 0 ∨ (p = 1 ∧ a < b) ∨ (p = -1 ∧ b < a)) :
    |((a + p : ℤ) : ℝ)| + |((b - p : ℤ) : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| := by
  have key : |a + p| + |b - p| ≤ |a| + |b| := by
    rcases hp with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · simp
    · rcases abs_cases (a + 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (b - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases a with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
      rcases abs_cases b with ⟨h4, _⟩ | ⟨h4, _⟩ <;> omega
    · rcases abs_cases (a + -1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (b - -1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases a with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
      rcases abs_cases b with ⟨h4, _⟩ | ⟨h4, _⟩ <;> omega
  have : ((|a + p| + |b - p| : ℤ) : ℝ) ≤ ((|a| + |b| : ℤ) : ℝ) := by exact_mod_cast key
  push_cast at this ⊢
  exact this

/-- D3g: trajectory exchange. `b` has one more server than `a` (at `q`), both keep their totals up
to the horizon `H`. Then there are `a'` (with `b`'s start) and `b'` (with `a`'s start) whose
values lie between those of `a` and `b`, with `a' + b' = a + b`, `a' H ≥ a H`, and total tree cost
at most that of `a` and `b`. -/
theorem traj_exchange (a b : ℕ → M → ℤ) (q : M)
    (hb0 : ∀ m, b 0 m = a 0 m + if m = q then 1 else 0)
    (ha : ∀ t ≤ H, ∑ m, a t m = ∑ m, a 0 m) (hb : ∀ t ≤ H, ∑ m, b t m = ∑ m, b 0 m) :
    ∃ a' b' : ℕ → M → ℤ, (∀ m, a' 0 m = b 0 m) ∧ (∀ m, b' 0 m = a 0 m) ∧
      (∀ t ≤ H, ∀ m, a' t m + b' t m = a t m + b t m) ∧
      (∀ t ≤ H, ∀ m, min (a t m) (b t m) ≤ a' t m ∧ a' t m ≤ max (a t m) (b t m)) ∧
      (∀ m, a H m ≤ a' H m) ∧
      (∀ t ≤ H, ∑ m, a' t m = ∑ m, b 0 m) ∧ (∀ t ≤ H, ∑ m, b' t m = ∑ m, a 0 m) ∧
      tcost T e H a' + tcost T e H b' ≤ tcost T e H a + tcost T e H b := by
  classical
  obtain ⟨fa, hfa⟩ : ∃ g : XArc T M H → ℤ, g = encA T e H a := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ g : XArc T M H → ℤ, g = encA T e H b := ⟨_, rfl⟩
  have hsum0 : ∑ m, b 0 m = ∑ m, a 0 m + 1 := by
    simp_rw [hb0]; rw [Finset.sum_add_distrib]; simp
  have hnet : ∀ u, anet (xtl T e H) (xhd T e H) (fun α => fb α - fa α) u =
      (if u = Sum.inr true then 1 else 0) - (if u = Sum.inr false then 1 else 0) := by
    intro u
    rw [anet_sub]
    rcases u with ⟨t, x⟩ | c
    · rw [hfa, hfb, encA_layer T e H b hb, encA_layer T e H a ha]; simp
    · cases c
      · rw [anet_snk, anet_snk]
        simp only [hfa, hfb, encA, Fin.val_last]
        rw [hb H le_rfl, ha H le_rfl, hsum0]; simp
      · rw [anet_src, anet_src]
        simp only [hfa, hfb, encA]
        rw [hsum0]; simp
  obtain ⟨p, hpc, hpn, hpz, hps⟩ :=
    arc_exchange (xtl T e H) (xhd T e H) (xsimple T e H) fa fb (Sum.inr true) (Sum.inr false)
      (by simp) hnet
  obtain ⟨fa', hfa'⟩ : ∃ g : XArc T M H → ℤ, g = fun α => fa α + p α := ⟨_, rfl⟩
  obtain ⟨fb', hfb'⟩ : ∃ g : XArc T M H → ℤ, g = fun α => fb α - p α := ⟨_, rfl⟩
  have hplay : ∀ t x, anet (xtl T e H) (xhd T e H) p (Sum.inl (t, x)) = 0 := by
    intro t x; rw [hpn]; simp
  have hlay' : ∀ t x, anet (xtl T e H) (xhd T e H) fa' (Sum.inl (t, x)) = 0 := by
    intro t x; rw [hfa', anet_add, hfa, encA_layer T e H a ha, hplay]; ring
  have hlayb : ∀ t x, anet (xtl T e H) (xhd T e H) fb' (Sum.inl (t, x)) = 0 := by
    intro t x; rw [hfb', anet_sub, hfb, encA_layer T e H b hb, hplay]; ring
  have htre0 : ∀ v, fa (Sum.inr (Sum.inr (0, v))) = 0 ∧ fb (Sum.inr (Sum.inr (0, v))) = 0 := by
    intro v; simp [hfa, hfb, encA]
  have hp0 : ∀ v, p (Sum.inr (Sum.inr (0, v))) = 0 := by
    intro v
    rcases hpc (Sum.inr (Sum.inr (0, v))) with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · rw [(htre0 v).1, (htre0 v).2] at h; exact absurd h (lt_irrefl 0)
    · rw [(htre0 v).1, (htre0 v).2] at h; exact absurd h (lt_irrefl 0)
  have h0a : ∀ v, fa' (Sum.inr (Sum.inr (0, v))) = 0 := by
    intro v; simp [hfa', (htre0 v).1, hp0 v]
  have h0b : ∀ v, fb' (Sum.inr (Sum.inr (0, v))) = 0 := by
    intro v; simp [hfb', (htre0 v).2, hp0 v]
  obtain ⟨da0, datre, datot⟩ := dec_spec T e H fa' hlay' h0a
  obtain ⟨db0, dbtre, dbtot⟩ := dec_spec T e H fb' hlayb h0b
  -- the source arcs: p = indicator of q
  have hpsrc : ∀ m, p (Sum.inl m) = if m = q then 1 else 0 := by
    have hsrc : ∑ m, p (Sum.inl m) = 1 := by
      have := hpn (Sum.inr true); rw [anet_src] at this; simpa using this
    have hz : ∀ m, m ≠ q → p (Sum.inl m) = 0 := by
      intro m hm
      rcases hpc (Sum.inl m) with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · simp only [hfa, hfb, encA, hb0, if_neg hm] at h; omega
      · simp only [hfa, hfb, encA, hb0, if_neg hm] at h; omega
    rw [Finset.sum_eq_single q (fun m _ hm => hz m hm) (by simp)] at hsrc
    intro m
    split_ifs with hm
    · rw [hm, hsrc]
    · exact hz m hm
  have hdecsto : ∀ (f : XArc T M H → ℤ) (t : ℕ) (ht : t ≤ H) m,
      dec T H f t m = f (Sum.inr (Sum.inl (⟨t, by omega⟩, m))) := by
    intro f t ht m; unfold dec; rw [dif_pos ht]
  refine ⟨dec T H fa', dec T H fb', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; rw [da0, hfa', hfa]; simp only [encA, hpsrc, hb0]
  · intro m; rw [db0, hfb', hfb]; simp only [encA, hpsrc, hb0]; ring
  · intro t ht m
    rw [hdecsto _ t ht, hdecsto _ t ht, hfa', hfb', hfa, hfb]
    simp only [encA, Fin.val_mk]; ring
  · intro t ht m
    rw [hdecsto _ t ht, hfa']
    simp only [hfa, encA, Fin.val_mk]
    rcases hpc (Sum.inr (Sum.inl (⟨t, by omega⟩, m))) with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h]; simp
    · simp only [hfa, hfb, encA, Fin.val_mk] at h2
      rw [h1]; constructor
      · exact (min_le_left _ _).trans (by omega)
      · exact le_trans (by omega) (le_max_right _ _)
    · simp only [hfa, hfb, encA, Fin.val_mk] at h2
      rw [h1]; constructor
      · exact le_trans (min_le_right _ _) (by omega)
      · exact le_trans (by omega) (le_max_left _ _)
  · intro m
    rw [hdecsto _ H le_rfl, hfa']
    simp only [hfa, encA, Fin.val_mk]
    have := hpz (Sum.inr (Sum.inl (⟨H, by omega⟩, m))) (by
      simp only [xhd]; rw [nxt_eq_snk])
    omega
  · intro t ht
    rw [datot t ht, hfa', hfa]
    simp only [encA, hpsrc, hb0]
  · intro t ht
    rw [dbtot t ht, hfb', hfb]
    simp only [encA, hpsrc, hb0]
    simp
  · rw [← acost_eq_tcost T e H _ fa' h0a datre, ← acost_eq_tcost T e H _ fb' h0b dbtre,
      ← acost_eq_tcost T e H a fa (fun v => (htre0 v).1) (fun t _ v => by rw [hfa]; rfl),
      ← acost_eq_tcost T e H b fb (fun v => (htre0 v).2) (fun t _ v => by rw [hfb]; rfl)]
    unfold acost
    rw [hfa', hfb']
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (T.W_pos v.1 v.2).le
    exact abs_exchange _ _ _ (hpc _)

end K17428


/-! D4 (17428d40): integer count trajectories confined to a leaf set `S`, their optimum `Fopt`,
monotonicity in the horizon (h >= 0) and the submodularity / antitone-h inequality from the
trajectory exchange `traj_exchange` (D3g). Needs D3a-D3g. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

/-- Integer count trajectories from `x0` up to horizon `H`, confined to `S`, serving every request
`r s` (`1 ≤ s ≤ H`) that lies in `S`. -/
def ITraj (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (c : ℕ → M → ℤ) : Prop :=
  (∀ m, c 0 m = x0 m) ∧ (∀ s ≤ H, ∀ m, 0 ≤ c s m) ∧ (∀ s ≤ H, ∀ m, m ∉ S → c s m = 0) ∧
  (∀ s ≤ H, ∑ m, c s m = ∑ m, x0 m) ∧ (∀ s, 1 ≤ s → s ≤ H → r s ∈ S → 1 ≤ c s (r s))

/-- The optimum over `ITraj`. -/
noncomputable def Fopt (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) : ℝ :=
  sInf (tcost T e H '' {c | ITraj S r H x0 c})

theorem fracMoveCost_nonneg' (x x' : M → ℝ) : 0 ≤ fracMoveCost T e x x' := by
  unfold fracMoveCost
  refine Finset.sum_nonneg fun v hv => mul_nonneg (T.W_pos v (Finset.mem_filter.1 hv).2).le
    (abs_nonneg _)

theorem fracMoveCost_self (x : M → ℝ) : fracMoveCost T e x x = 0 := by
  unfold fracMoveCost; simp

theorem tcost_nonneg (H : ℕ) (c : ℕ → M → ℤ) : 0 ≤ tcost T e H c :=
  Finset.sum_nonneg fun _ _ => fracMoveCost_nonneg' T e _ _

theorem tcost_succ (H : ℕ) (c : ℕ → M → ℤ) :
    tcost T e (H + 1) c = tcost T e H c +
      fracMoveCost T e (fun m => (c H m : ℝ)) (fun m => (c (H + 1) m : ℝ)) := by
  unfold tcost; rw [Finset.sum_range_succ]

theorem tcost_le_succ (H : ℕ) (c : ℕ → M → ℤ) : tcost T e H c ≤ tcost T e (H + 1) c := by
  rw [tcost_succ]; linarith [fracMoveCost_nonneg' T e (fun m => (c H m : ℝ)) (fun m => (c (H + 1) m : ℝ))]

theorem tcost_congr (H : ℕ) (c d : ℕ → M → ℤ) (h : ∀ s ≤ H, c s = d s) :
    tcost T e H c = tcost T e H d := by
  unfold tcost
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  rw [h s (by omega), h (s + 1) (by omega)]

/-- Constant extension after the horizon. -/
def cext (H : ℕ) (c : ℕ → M → ℤ) (s : ℕ) : M → ℤ := if s ≤ H then c s else c H

theorem cext_eq (H : ℕ) (c : ℕ → M → ℤ) (s : ℕ) (hs : s ≤ H) : cext H c s = c s := by
  simp [cext, hs]

theorem cext_succ (H : ℕ) (c : ℕ → M → ℤ) : cext H c (H + 1) = c H := by
  simp [cext]

theorem tcost_cext (H : ℕ) (c : ℕ → M → ℤ) : tcost T e (H + 1) (cext H c) = tcost T e H c := by
  rw [tcost_succ, cext_succ, cext_eq H c H le_rfl, fracMoveCost_self, add_zero]
  exact tcost_congr T e H _ _ fun s hs => cext_eq H c s hs

theorem ITraj_pred {S : Set M} {r : ℕ → M} {H : ℕ} {x0 : M → ℤ} {c : ℕ → M → ℤ}
    (h : ITraj S r (H + 1) x0 c) : ITraj S r H x0 c :=
  ⟨h.1, fun s hs => h.2.1 s (by omega), fun s hs => h.2.2.1 s (by omega),
    fun s hs => h.2.2.2.1 s (by omega), fun s h1 hs => h.2.2.2.2 s h1 (by omega)⟩

/-- Feasibility: a nonnegative start confined to `S` with positive total. -/
theorem ITraj_nonempty (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ)
    (h0 : ∀ m, 0 ≤ x0 m) (hS : ∀ m, m ∉ S → x0 m = 0) (hpos : 1 ≤ ∑ m, x0 m) :
    ∃ c, ITraj S r H x0 c := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, 0 < x0 q := by
    by_contra hne
    push_neg at hne
    have : ∑ m, x0 m ≤ 0 := Finset.sum_nonpos fun m _ => hne m
    omega
  have hqS : q ∈ S := by
    by_contra hn; have := hS q hn; omega
  set N := ∑ m, x0 m
  let g : ℕ → M := fun s => if r s ∈ S then r s else q
  have hgS : ∀ s, g s ∈ S := by
    intro s; by_cases h : r s ∈ S <;> simp [g, h, hqS]
  refine ⟨fun s m => if s = 0 then x0 m else if m = g s then N else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; simp
  · intro s _ m
    by_cases h : s = 0
    · simp [h, h0 m]
    · simp only [h, if_false]; split_ifs <;> omega
  · intro s _ m hm
    by_cases h : s = 0
    · simp [h, hS m hm]
    · simp only [h, if_false]
      have : m ≠ g s := fun hh => hm (hh ▸ hgS s)
      simp [this]
  · intro s _
    by_cases h : s = 0
    · simp [h]
    · simp [h, N]
  · intro s h1 _ hr
    have hs : s ≠ 0 := by omega
    have : g s = r s := by simp [g, hr]
    simp [hs, this]; omega

theorem Fopt_le {S : Set M} {r : ℕ → M} {H : ℕ} {x0 : M → ℤ} {c : ℕ → M → ℤ}
    (h : ITraj S r H x0 c) : Fopt T e S r H x0 ≤ tcost T e H c :=
  csInf_le ⟨0, by rintro _ ⟨d, _, rfl⟩; exact tcost_nonneg T e H d⟩ ⟨c, h, rfl⟩

theorem Fopt_nonneg (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) : 0 ≤ Fopt T e S r H x0 := by
  unfold Fopt
  rcases Set.eq_empty_or_nonempty (tcost T e H '' {c | ITraj S r H x0 c}) with h | h
  · rw [h, Real.sInf_empty]
  · exact le_csInf h (by rintro _ ⟨d, _, rfl⟩; exact tcost_nonneg T e H d)

theorem le_Fopt {S : Set M} {r : ℕ → M} {H : ℕ} {x0 : M → ℤ} (X : ℝ)
    (hne : ∃ c, ITraj S r H x0 c) (h : ∀ c, ITraj S r H x0 c → X ≤ tcost T e H c) :
    X ≤ Fopt T e S r H x0 := by
  obtain ⟨c, hc⟩ := hne
  exact le_csInf ⟨_, c, hc, rfl⟩ (by rintro _ ⟨d, hd, rfl⟩; exact h d hd)

/-- `h^t ≥ 0`: the optimum is monotone in the horizon (when the longer problem is feasible). -/
theorem Fopt_le_succ (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ)
    (hne : ∃ c, ITraj S r (H + 1) x0 c) : Fopt T e S r H x0 ≤ Fopt T e S r (H + 1) x0 :=
  le_Fopt T e _ hne fun c hc => (Fopt_le T e (ITraj_pred hc)).trans (tcost_le_succ T e H c)

theorem between_of_sum {a b a' b' : ℤ} (hs : a' + b' = a + b) (h1 : min a b ≤ a') (h2 : a' ≤ max a b) :
    min a b ≤ b' ∧ b' ≤ max a b := by
  constructor
  · rcases le_total a b with h | h
    · rw [min_eq_left h] at h1 ⊢; rw [max_eq_right h] at h2; omega
    · rw [min_eq_right h] at h1 ⊢; rw [max_eq_left h] at h2; omega
  · rcases le_total a b with h | h
    · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2 ⊢; omega
    · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2 ⊢; omega

/-- Pairwise exchange on feasible trajectories: from `A` (start `x0`, horizon `H+1`) and `B`
(start `x0 + e_q`, horizon `H`) build `a'` (start `x0 + e_q`, horizon `H+1`) and `b'` (start `x0`,
horizon `H`) with no larger total cost. -/
theorem ITraj_exchange (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (q : M)
    (A B : ℕ → M → ℤ) (hA : ITraj S r (H + 1) x0 A)
    (hB : ITraj S r H (fun m => x0 m + if m = q then 1 else 0) B) :
    ∃ a' b', ITraj S r (H + 1) (fun m => x0 m + if m = q then 1 else 0) a' ∧
      ITraj S r H x0 b' ∧
      tcost T e (H + 1) a' + tcost T e H b' ≤ tcost T e (H + 1) A + tcost T e H B := by
  classical
  set x1 : M → ℤ := fun m => x0 m + if m = q then 1 else 0 with hx1
  set B' := cext H B with hB'
  have hB's : ∀ s ≤ H + 1, ∀ m, B' s m = B (min s H) m := by
    intro s hs m
    rcases Nat.lt_or_ge s (H + 1) with h | h
    · rw [hB', cext_eq H B s (by omega), min_eq_left (by omega)]
    · have : s = H + 1 := by omega
      subst this; rw [hB', cext_succ, min_eq_right (by omega)]
  have hb0 : ∀ m, B' 0 m = A 0 m + if m = q then 1 else 0 := by
    intro m; rw [hB's 0 (by omega), Nat.zero_min, hB.1 m, hA.1 m]
  have ha : ∀ t ≤ H + 1, ∑ m, A t m = ∑ m, A 0 m := by
    intro t ht; rw [hA.2.2.2.1 t ht]; exact (Finset.sum_congr rfl fun m _ => hA.1 m).symm
  have hb : ∀ t ≤ H + 1, ∑ m, B' t m = ∑ m, B' 0 m := by
    intro t ht
    simp_rw [hB's t ht, hB's 0 (by omega), Nat.zero_min]
    rw [hB.2.2.2.1 _ (min_le_right _ _)]
    exact (Finset.sum_congr rfl fun m _ => hB.1 m).symm
  obtain ⟨a', b', h0a, h0b, hsum, hbet, hlast, hta, htb, hcost⟩ :=
    traj_exchange T e (H + 1) A B' q hb0 ha hb
  have hBnn : ∀ s ≤ H + 1, ∀ m, 0 ≤ B' s m := fun s hs m => by
    rw [hB's s hs]; exact hB.2.1 _ (min_le_right _ _) m
  have hBS : ∀ s ≤ H + 1, ∀ m, m ∉ S → B' s m = 0 := fun s hs m hm => by
    rw [hB's s hs]; exact hB.2.2.1 _ (min_le_right _ _) m hm
  have hbet' : ∀ t ≤ H + 1, ∀ m, min (A t m) (B' t m) ≤ b' t m ∧ b' t m ≤ max (A t m) (B' t m) :=
    fun t ht m => between_of_sum (by linarith [hsum t ht m]) (hbet t ht m).1 (hbet t ht m).2
  have hsumB0 : ∑ m, B' 0 m = ∑ m, x1 m := Finset.sum_congr rfl fun m _ => by
    rw [hB's 0 (by omega), Nat.zero_min, hB.1 m]
  have hsumA0 : ∑ m, A 0 m = ∑ m, x0 m := Finset.sum_congr rfl fun m _ => hA.1 m
  refine ⟨a', b', ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
    fun s h1 hs hr => ?_⟩, ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
    fun s h1 hs hr => ?_⟩, ?_⟩
  · rw [h0a m, hB's 0 (by omega), Nat.zero_min, hB.1 m]
  · exact le_trans (le_min (hA.2.1 s hs m) (hBnn s hs m)) (hbet s hs m).1
  · have h1 := (hbet s hs m).1; have h2 := (hbet s hs m).2
    rw [hA.2.2.1 s hs m hm, hBS s hs m hm] at h1 h2; simp at h1 h2; omega
  · rw [hta s hs, hsumB0]
  · rcases Nat.lt_or_ge s (H + 1) with h | h
    · have h1' := (hbet s hs (r s)).1
      have hA1 := hA.2.2.2.2 s h1 hs hr
      have hB1 : 1 ≤ B' s (r s) := by
        rw [hB's s hs, min_eq_left (by omega)]; exact hB.2.2.2.2 s h1 (by omega) hr
      exact le_trans (le_min hA1 hB1) h1'
    · have : s = H + 1 := by omega
      subst this
      exact le_trans (hA.2.2.2.2 _ h1 hs hr) (hlast (r (H + 1)))
  · rw [h0b m, hA.1 m]
  · exact le_trans (le_min (hA.2.1 s (by omega) m) (hBnn s (by omega) m)) (hbet' s (by omega) m).1
  · have h1 := (hbet' s (by omega) m).1; have h2 := (hbet' s (by omega) m).2
    rw [hA.2.2.1 s (by omega) m hm, hBS s (by omega) m hm] at h1 h2; simp at h1 h2; omega
  · rw [htb s (by omega), hsumA0]
  · have h1' := (hbet' s (by omega) (r s)).1
    have hA1 := hA.2.2.2.2 s h1 (by omega) hr
    have hB1 : 1 ≤ B' s (r s) := by
      rw [hB's s (by omega), min_eq_left (by omega)]; exact hB.2.2.2.2 s h1 hs hr
    exact le_trans (le_min hA1 hB1) h1'
  · have e1 := tcost_le_succ T e H b'
    have e2 := tcost_cext T e H B
    rw [← hB'] at e2
    linarith

/-- D4: submodularity, i.e. `h^{H+1}(x0 + e_q) ≤ h^{H+1}(x0)` where `h^{H+1}(x) = F_{H+1}(x) - F_H(x)`.
With nested prefix starts this is "h^t antitone in the server count". -/
theorem Fopt_submod (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (q : M)
    (h0 : ∀ m, 0 ≤ x0 m) (hS : ∀ m, m ∉ S → x0 m = 0) (hpos : 1 ≤ ∑ m, x0 m) (hq : q ∈ S) :
    Fopt T e S r (H + 1) (fun m => x0 m + if m = q then 1 else 0) + Fopt T e S r H x0 ≤
      Fopt T e S r (H + 1) x0 + Fopt T e S r H (fun m => x0 m + if m = q then 1 else 0) := by
  classical
  set x1 : M → ℤ := fun m => x0 m + if m = q then 1 else 0 with hx1
  have h1 : ∀ m, 0 ≤ x1 m := fun m => by
    simp only [hx1]; have := h0 m; split_ifs <;> omega
  have hS1 : ∀ m, m ∉ S → x1 m = 0 := fun m hm => by
    have hmq : m ≠ q := fun h => hm (h ▸ hq)
    simp [hx1, hS m hm, hmq]
  have hpos1 : 1 ≤ ∑ m, x1 m := by
    have : ∑ m, x1 m = ∑ m, x0 m + 1 := by
      simp only [hx1]; rw [Finset.sum_add_distrib]; simp
    omega
  -- for every A, B : F(H+1) x1 + F H x0 ≤ cost A + cost B
  have key : ∀ A, ITraj S r (H + 1) x0 A → ∀ B, ITraj S r H x1 B →
      Fopt T e S r (H + 1) x1 + Fopt T e S r H x0 ≤ tcost T e (H + 1) A + tcost T e H B := by
    intro A hA B hB
    obtain ⟨a', b', ha', hb', hc⟩ := ITraj_exchange T e S r H x0 q A B hA hB
    linarith [Fopt_le T e ha', Fopt_le T e hb']
  have step1 : ∀ B, ITraj S r H x1 B →
      Fopt T e S r (H + 1) x1 + Fopt T e S r H x0 - tcost T e H B ≤ Fopt T e S r (H + 1) x0 := by
    intro B hB
    refine le_Fopt T e _ (ITraj_nonempty S r (H + 1) x0 h0 hS hpos) fun A hA => ?_
    linarith [key A hA B hB]
  have : Fopt T e S r (H + 1) x1 + Fopt T e S r H x0 - Fopt T e S r (H + 1) x0 ≤
      Fopt T e S r H x1 :=
    le_Fopt T e _ (ITraj_nonempty S r H x1 h1 hS1 hpos1) fun B hB => by linarith [step1 B hB]
  linarith

end K17428


/-! D3h (17428d40): attainment of the count-trajectory optimum, end-state optimum `Fend`, and the
unit excess exchange (paper Lemma 30 = Cote et al. Cor. 2, for server counts differing by one).
Needs D3a-D3g, D4. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem le_sum_of_nonneg' (d : M → ℤ) (h0 : ∀ m, 0 ≤ d m) (m : M) : d m ≤ ∑ m', d m' :=
  Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ m)

/-- The cost values of feasible trajectories form a finite set. -/
theorem tcost_image_finite (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) :
    (tcost T e H '' {c | ITraj S r H x0 c}).Finite := by
  classical
  set N := (∑ m, x0 m).toNat
  let rec' : (Fin (H + 1) → M → Fin (N + 1)) → ℕ → M → ℤ :=
    fun f s m => if h : s ≤ H then ((f ⟨s, by omega⟩ m : ℕ) : ℤ) else 0
  refine (Set.finite_range (fun f => tcost T e H (rec' f))).subset ?_
  rintro _ ⟨c, hc, rfl⟩
  have hle : ∀ (s : Fin (H + 1)) m, (c s m).toNat < N + 1 := by
    intro s m
    have h1 := le_sum_of_nonneg' (c s) (hc.2.1 s (by omega)) m
    rw [hc.2.2.2.1 s (by omega)] at h1
    have : (c s m).toNat ≤ N := Int.toNat_le_toNat h1
    omega
  refine ⟨fun s m => ⟨(c s m).toNat, hle s m⟩, ?_⟩
  refine tcost_congr T e H _ _ fun s hs => funext fun m => ?_
  simp only [rec', dif_pos hs]
  exact Int.toNat_of_nonneg (hc.2.1 s hs m)

/-- Minimum attainment on any nonempty set of feasible trajectories. -/
theorem exists_min (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (s : Set (ℕ → M → ℤ))
    (hs : ∀ c ∈ s, ITraj S r H x0 c) (hne : s.Nonempty) :
    ∃ c ∈ s, tcost T e H c = sInf (tcost T e H '' s) := by
  have hfin : (tcost T e H '' s).Finite :=
    (tcost_image_finite T e S r H x0).subset (Set.image_mono fun c hc => hs c hc)
  obtain ⟨c, hc, h⟩ := (hne.image (tcost T e H)).csInf_mem hfin
  exact ⟨c, hc, h⟩

/-- Optimum with prescribed end state. -/
noncomputable def Fend (S : Set M) (r : ℕ → M) (H : ℕ) (x0 y : M → ℤ) : ℝ :=
  sInf (tcost T e H '' {c | ITraj S r H x0 c ∧ c H = y})

theorem Fend_le {S : Set M} {r : ℕ → M} {H : ℕ} {x0 : M → ℤ} {c : ℕ → M → ℤ}
    (h : ITraj S r H x0 c) : Fend T e S r H x0 (c H) ≤ tcost T e H c :=
  csInf_le ⟨0, by rintro _ ⟨d, _, rfl⟩; exact tcost_nonneg T e H d⟩ ⟨c, ⟨h, rfl⟩, rfl⟩

theorem Fopt_attained (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (hne : ∃ c, ITraj S r H x0 c) :
    ∃ c, ITraj S r H x0 c ∧ tcost T e H c = Fopt T e S r H x0 := by
  obtain ⟨c, hc, h⟩ := exists_min T e S r H x0 {c | ITraj S r H x0 c} (fun c hc => hc) hne
  exact ⟨c, hc, h⟩

theorem Fend_attained (S : Set M) (r : ℕ → M) (H : ℕ) (x0 y : M → ℤ)
    (hne : ∃ c, ITraj S r H x0 c ∧ c H = y) :
    ∃ c, ITraj S r H x0 c ∧ c H = y ∧ tcost T e H c = Fend T e S r H x0 y := by
  obtain ⟨c, hc, h⟩ := exists_min T e S r H x0 {c | ITraj S r H x0 c ∧ c H = y}
    (fun c hc => hc.1) hne
  exact ⟨c, hc.1, hc.2, h⟩

theorem Fopt_le_Fend (S : Set M) (r : ℕ → M) (H : ℕ) (x0 y : M → ℤ)
    (hne : ∃ c, ITraj S r H x0 c ∧ c H = y) : Fopt T e S r H x0 ≤ Fend T e S r H x0 y := by
  obtain ⟨c, hc, hy, h⟩ := Fend_attained T e S r H x0 y hne
  rw [← h]; exact Fopt_le T e hc

/-- A nonnegative integer vector with sum one is a unit vector. -/
theorem unit_of_sum_one (d : M → ℤ) (h0 : ∀ m, 0 ≤ d m) (h1 : ∑ m, d m = 1) :
    ∃ q, ∀ m, d m = if m = q then 1 else 0 := by
  classical
  obtain ⟨q, hq⟩ : ∃ q, 0 < d q := by
    by_contra hne; push_neg at hne
    have : ∑ m, d m ≤ 0 := Finset.sum_nonpos fun m _ => hne m
    omega
  have hsplit := Finset.add_sum_erase Finset.univ d (Finset.mem_univ q)
  have hrest : 0 ≤ ∑ m ∈ Finset.univ.erase q, d m := Finset.sum_nonneg fun m _ => h0 m
  have hdq : d q = 1 := by omega
  have hz : ∑ m ∈ Finset.univ.erase q, d m = 0 := by omega
  rw [Finset.sum_eq_zero_iff_of_nonneg fun m _ => h0 m] at hz
  refine ⟨q, fun m => ?_⟩
  by_cases hm : m = q
  · simp [hm, hdq]
  · simp only [hm, if_false]; exact hz m (Finset.mem_erase.2 ⟨hm, Finset.mem_univ m⟩)

/-- Same-horizon exchange on feasible trajectories. -/
theorem ITraj_exchange0 (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (q : M)
    (A B : ℕ → M → ℤ) (hA : ITraj S r H x0 A)
    (hB : ITraj S r H (fun m => x0 m + if m = q then 1 else 0) B) :
    ∃ a' b', ITraj S r H (fun m => x0 m + if m = q then 1 else 0) a' ∧ ITraj S r H x0 b' ∧
      (∀ m, A H m ≤ a' H m) ∧ (∀ m, a' H m + b' H m = A H m + B H m) ∧
      tcost T e H a' + tcost T e H b' ≤ tcost T e H A + tcost T e H B := by
  classical
  set x1 : M → ℤ := fun m => x0 m + if m = q then 1 else 0 with hx1
  have hb0 : ∀ m, B 0 m = A 0 m + if m = q then 1 else 0 := by
    intro m; rw [hB.1 m, hA.1 m]
  have ha : ∀ t ≤ H, ∑ m, A t m = ∑ m, A 0 m := by
    intro t ht; rw [hA.2.2.2.1 t ht]; exact (Finset.sum_congr rfl fun m _ => hA.1 m).symm
  have hb : ∀ t ≤ H, ∑ m, B t m = ∑ m, B 0 m := by
    intro t ht; rw [hB.2.2.2.1 t ht]; exact (Finset.sum_congr rfl fun m _ => hB.1 m).symm
  obtain ⟨a', b', h0a, h0b, hsum, hbet, hlast, hta, htb, hcost⟩ :=
    traj_exchange T e H A B q hb0 ha hb
  have hbet' : ∀ t ≤ H, ∀ m, min (A t m) (B t m) ≤ b' t m ∧ b' t m ≤ max (A t m) (B t m) :=
    fun t ht m => between_of_sum (by linarith [hsum t ht m]) (hbet t ht m).1 (hbet t ht m).2
  have hsumB0 : ∑ m, B 0 m = ∑ m, x1 m := Finset.sum_congr rfl fun m _ => hB.1 m
  have hsumA0 : ∑ m, A 0 m = ∑ m, x0 m := Finset.sum_congr rfl fun m _ => hA.1 m
  refine ⟨a', b', ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
    fun s h1 hs hr => ?_⟩, ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
    fun s h1 hs hr => ?_⟩, hlast, hsum H le_rfl, hcost⟩
  · rw [h0a m, hB.1 m]
  · exact le_trans (le_min (hA.2.1 s hs m) (hB.2.1 s hs m)) (hbet s hs m).1
  · have h1 := (hbet s hs m).1; have h2 := (hbet s hs m).2
    rw [hA.2.2.1 s hs m hm, hB.2.2.1 s hs m hm] at h1 h2; simp at h1 h2; omega
  · rw [hta s hs, hsumB0]
  · exact le_trans (le_min (hA.2.2.2.2 s h1 hs hr) (hB.2.2.2.2 s h1 hs hr)) (hbet s hs (r s)).1
  · rw [h0b m, hA.1 m]
  · exact le_trans (le_min (hA.2.1 s hs m) (hB.2.1 s hs m)) (hbet' s hs m).1
  · have h1 := (hbet' s hs m).1; have h2 := (hbet' s hs m).2
    rw [hA.2.2.1 s hs m hm, hB.2.2.1 s hs m hm] at h1 h2; simp at h1 h2; omega
  · rw [htb s hs, hsumA0]
  · exact le_trans (le_min (hA.2.2.2.2 s h1 hs hr) (hB.2.2.2.2 s h1 hs hr)) (hbet' s hs (r s)).1

/-- Lemma 30, one more server: for any reachable end state `X` of the `x0` problem there is a leaf
`m` such that ending in `X + e_m` costs the `x0 + e_q` problem no more excess. -/
theorem excess_up (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (q : M) (X : M → ℤ)
    (hq : q ∈ S) (h0 : ∀ m, 0 ≤ x0 m) (hS : ∀ m, m ∉ S → x0 m = 0) (hpos : 1 ≤ ∑ m, x0 m)
    (hX : ∃ c, ITraj S r H x0 c ∧ c H = X) :
    ∃ m, (∃ c, ITraj S r H (fun m' => x0 m' + if m' = q then 1 else 0) c ∧
        c H = fun m' => X m' + if m' = m then 1 else 0) ∧
      Fend T e S r H (fun m' => x0 m' + if m' = q then 1 else 0)
          (fun m' => X m' + if m' = m then 1 else 0) + Fopt T e S r H x0 ≤
        Fend T e S r H x0 X + Fopt T e S r H (fun m' => x0 m' + if m' = q then 1 else 0) := by
  classical
  set x1 : M → ℤ := fun m => x0 m + if m = q then 1 else 0 with hx1
  have h1 : ∀ m, 0 ≤ x1 m := fun m => by
    simp only [hx1]; have := h0 m; split_ifs <;> omega
  have hS1 : ∀ m, m ∉ S → x1 m = 0 := fun m hm => by
    have hmq : m ≠ q := fun h => hm (h ▸ hq)
    simp [hx1, hS m hm, hmq]
  have hsum1 : ∑ m, x1 m = ∑ m, x0 m + 1 := by
    simp only [hx1]; rw [Finset.sum_add_distrib]; simp
  obtain ⟨A, hA, hAX, hAc⟩ := Fend_attained T e S r H x0 X hX
  obtain ⟨B, hB, hBc⟩ := Fopt_attained T e S r H x1 (ITraj_nonempty S r H x1 h1 hS1 (by omega))
  obtain ⟨a', b', ha', hb', hlast, -, hcost⟩ := ITraj_exchange0 T e S r H x0 q A B hA hB
  obtain ⟨m, hm⟩ := unit_of_sum_one (fun m => a' H m - X m)
    (fun m => by have := hlast m; rw [hAX] at this; show 0 ≤ a' H m - X m; omega)
    (by
      rw [Finset.sum_sub_distrib, ha'.2.2.2.1 H le_rfl, hsum1, ← hAX, hA.2.2.2.1 H le_rfl]; ring)
  have hend : a' H = fun m' => X m' + if m' = m then 1 else 0 := by
    funext m'; have h := hm m'; beta_reduce at h; split_ifs at h ⊢ <;> omega
  refine ⟨m, ⟨a', ha', hend⟩, ?_⟩
  have e1 := Fend_le T e ha'
  rw [hend] at e1
  have e2 := Fopt_le T e hb'
  linarith

/-- Lemma 30, one fewer server: for any reachable end state `X` of the `x0 + e_q` problem there is a
leaf `m` with `X m ≥ 1` such that ending in `X - e_m` costs the `x0` problem no more excess. -/
theorem excess_down (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (q : M) (X : M → ℤ)
    (h0 : ∀ m, 0 ≤ x0 m) (hS : ∀ m, m ∉ S → x0 m = 0) (hpos : 1 ≤ ∑ m, x0 m)
    (hX : ∃ c, ITraj S r H (fun m' => x0 m' + if m' = q then 1 else 0) c ∧ c H = X) :
    ∃ m, 1 ≤ X m ∧ (∃ c, ITraj S r H x0 c ∧ c H = fun m' => X m' - if m' = m then 1 else 0) ∧
      Fend T e S r H x0 (fun m' => X m' - if m' = m then 1 else 0) +
          Fopt T e S r H (fun m' => x0 m' + if m' = q then 1 else 0) ≤
        Fend T e S r H (fun m' => x0 m' + if m' = q then 1 else 0) X + Fopt T e S r H x0 := by
  classical
  set x1 : M → ℤ := fun m => x0 m + if m = q then 1 else 0 with hx1
  have hsum1 : ∑ m, x1 m = ∑ m, x0 m + 1 := by
    simp only [hx1]; rw [Finset.sum_add_distrib]; simp
  obtain ⟨A, hA, hAX, hAc⟩ := Fend_attained T e S r H x1 X hX
  obtain ⟨B, hB, hBc⟩ := Fopt_attained T e S r H x0 (ITraj_nonempty S r H x0 h0 hS hpos)
  obtain ⟨a', b', ha', hb', hlast, hsum, hcost⟩ := ITraj_exchange0 T e S r H x0 q B A hB hA
  -- X - b' H = a' H - B H ≥ 0 with sum one
  obtain ⟨m, hm⟩ := unit_of_sum_one (fun m => X m - b' H m)
    (fun m => by have := hlast m; have := hsum m; rw [hAX] at this; show 0 ≤ X m - b' H m; omega)
    (by
      rw [Finset.sum_sub_distrib, hb'.2.2.2.1 H le_rfl, ← hAX, hA.2.2.2.1 H le_rfl, hsum1]; ring)
  have hend : b' H = fun m' => X m' - if m' = m then 1 else 0 := by
    funext m'; have h := hm m'; beta_reduce at h; split_ifs at h ⊢ <;> omega
  have hXm : 1 ≤ X m := by
    have h1 := hb'.2.1 H le_rfl m
    have h2 : X m - b' H m = 1 := by simpa using hm m
    omega
  refine ⟨m, hXm, ⟨b', hb', hend⟩, ?_⟩
  have e1 := Fend_le T e hb'
  rw [hend] at e1
  have e2 := Fopt_le T e ha'
  linarith

end K17428


/-! D5a (17428d40): internal step cost `ccost p` of the subtree `T(p)` (edges strictly below `p`),
agreement with the tree EMD for confined states of equal total, triangle inequality and the cost
of one extra unit. Needs D3a-D3h, D4. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem isAnc_total {a b x : V} (ha : T.IsAnc a x) (hb : T.IsAnc b x) :
    T.IsAnc a b ∨ T.IsAnc b a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rcases le_total i j with h | h
  · right; refine ⟨j - i, ?_⟩; rw [← Function.iterate_add_apply]; congr 1; omega
  · left; refine ⟨i - j, ?_⟩; rw [← Function.iterate_add_apply]; congr 1; omega

/-- Leaves of the subtree `T(p)`. -/
def Sp (p : V) : Set M := {m | T.IsAnc p (e m : V)}

open Classical in
/-- Vertices strictly below `p` (their parent edges are the edges of `T(p)`). -/
noncomputable def inner (p : V) : Finset V :=
  univ.filter fun v => v ≠ T.root ∧ T.IsAnc p v ∧ v ≠ p

/-- Internal step cost in `T(p)`. -/
noncomputable def ccost (p : V) (x y : M → ℤ) : ℝ :=
  ∑ v ∈ inner T p, T.W v * |((nsub T e y v - nsub T e x v : ℤ) : ℝ)|

theorem nsub_of_anc (p : V) (x : M → ℤ) (hx : ∀ m, m ∉ Sp T e p → x m = 0) {v : V}
    (hv : T.IsAnc v p) : nsub T e x v = ∑ m, x m := by
  classical
  unfold nsub
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : T.IsAnc p (e m : V)
  · rw [if_pos (isAnc_trans T hv hm)]
  · rw [hx m hm]; simp

theorem nsub_of_disj (p : V) (x : M → ℤ) (hx : ∀ m, m ∉ Sp T e p → x m = 0) {v : V}
    (h1 : ¬ T.IsAnc p v) (h2 : ¬ T.IsAnc v p) : nsub T e x v = 0 := by
  classical
  unfold nsub
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : T.IsAnc v (e m : V)
  · have : m ∉ Sp T e p := fun hp => by
      rcases isAnc_total T hm hp with h | h
      · exact h2 h
      · exact h1 h
    rw [hx m this]; simp
  · simp [hm]

theorem ccost_eq (p : V) (x y : M → ℤ) (hx : ∀ m, m ∉ Sp T e p → x m = 0)
    (hy : ∀ m, m ∉ Sp T e p → y m = 0) (hs : ∑ m, x m = ∑ m, y m) :
    fracMoveCost T e (fun m => (x m : ℝ)) (fun m => (y m : ℝ)) = ccost T e p x y := by
  classical
  unfold fracMoveCost ccost
  simp_rw [subtreeMass_cast]
  push_cast
  symm
  refine Finset.sum_subset (f := fun v => T.W v * |(nsub T e y v : ℝ) - nsub T e x v|) ?_ ?_
  · intro v hv
    simp only [inner, Finset.mem_filter] at hv
    simp [hv.2.1]
  · intro v hv hvn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [inner, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hvn
    have hz : nsub T e y v - nsub T e x v = 0 := by
      by_cases ha : T.IsAnc v p
      · rw [nsub_of_anc T e p x hx ha, nsub_of_anc T e p y hy ha, hs]; ring
      · have h1 : ¬ T.IsAnc p v := fun h => ha (by
          have hvp : v = p := by by_contra hne; exact hvn hv h hne
          rw [hvp]; exact isAnc_refl T p)
        rw [nsub_of_disj T e p x hx h1 ha, nsub_of_disj T e p y hy h1 ha]; ring
    push_cast at hz ⊢
    rw [show ((nsub T e y v : ℝ) - nsub T e x v) = 0 by exact_mod_cast hz]; simp

theorem W_nonneg_inner (p v : V) (hv : v ∈ inner T p) : 0 ≤ T.W v := by
  classical
  simp only [inner, Finset.mem_filter] at hv
  exact (T.W_pos v hv.2.1).le

theorem ccost_nonneg (p : V) (x y : M → ℤ) : 0 ≤ ccost T e p x y :=
  Finset.sum_nonneg fun v hv => mul_nonneg (W_nonneg_inner T p v hv) (abs_nonneg _)

theorem ccost_comm (p : V) (x y : M → ℤ) : ccost T e p x y = ccost T e p y x := by
  unfold ccost
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← abs_neg]; push_cast; ring_nf

theorem ccost_triangle (p : V) (x y z : M → ℤ) :
    ccost T e p x z ≤ ccost T e p x y + ccost T e p y z := by
  unfold ccost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v hv => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (W_nonneg_inner T p v hv)
  push_cast
  calc |(nsub T e z v : ℝ) - nsub T e x v|
      = |((nsub T e y v : ℝ) - nsub T e x v) + ((nsub T e z v : ℝ) - nsub T e y v)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

open Classical in
theorem nsub_add_unit (x : M → ℤ) (m : M) (v : V) :
    nsub T e (fun m' => x m' + if m' = m then 1 else 0) v =
      nsub T e x v + if T.IsAnc v (e m : V) then 1 else 0 := by
  classical
  unfold nsub
  have : ∀ m', (if T.IsAnc v (e m' : V) then x m' + (if m' = m then 1 else 0) else 0) =
      (if T.IsAnc v (e m' : V) then x m' else 0) +
        (if m' = m then (if T.IsAnc v (e m : V) then 1 else 0) else 0) := by
    intro m'
    by_cases h1 : m' = m
    · subst h1; by_cases h2 : T.IsAnc v (e m' : V) <;> simp [h2]
    · by_cases h2 : T.IsAnc v (e m' : V) <;> simp [h1, h2]
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

open Classical in
/-- Weight of the path from `p` down to the leaf `e m` (edges of `T(p)` only). -/
noncomputable def dpath (p : V) (m : M) : ℝ :=
  ∑ v ∈ inner T p, if T.IsAnc v (e m : V) then T.W v else 0

theorem ccost_add_unit (p : V) (x : M → ℤ) (m : M) :
    ccost T e p x (fun m' => x m' + if m' = m then 1 else 0) = dpath T e p m := by
  classical
  unfold ccost dpath
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [nsub_add_unit]
  by_cases h : T.IsAnc v (e m : V) <;> simp [h]

/-- Internal cost of a trajectory up to the horizon. -/
noncomputable def qcost (p : V) (H : ℕ) (c : ℕ → M → ℤ) : ℝ :=
  ∑ s ∈ range H, ccost T e p (c s) (c (s + 1))

theorem tcost_eq_qcost (p : V) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (c : ℕ → M → ℤ)
    (hc : ITraj (Sp T e p) r H x0 c) : tcost T e H c = qcost T e p H c := by
  unfold tcost qcost
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  exact ccost_eq T e p _ _ (hc.2.2.1 s (by omega)) (hc.2.2.1 (s + 1) (by omega))
    (by rw [hc.2.2.2.1 s (by omega), hc.2.2.2.1 (s + 1) (by omega)])

end K17428


/-! D5b (17428d40): nested prefix starts and the multi-unit Lemma 30 (excess chains up and down,
with the internal switching cost bounded by `d * D`). Needs D3a-D3h, D4, D5a. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

/-- Nested prefix starts: `st (j+1) = st j + e_{L j}` inside `S`, `st 0` nonnegative in `S`. -/
def Nested (S : Set M) (st : ℕ → M → ℤ) (L : ℕ → M) : Prop :=
  (∀ j, st (j + 1) = fun m => st j m + if m = L j then 1 else 0) ∧ (∀ j, L j ∈ S) ∧
    (∀ m, 0 ≤ st 0 m) ∧ (∀ m, m ∉ S → st 0 m = 0)

theorem Nested.props {S : Set M} {st : ℕ → M → ℤ} {L : ℕ → M} (h : Nested S st L) (j : ℕ) :
    (∀ m, 0 ≤ st j m) ∧ (∀ m, m ∉ S → st j m = 0) ∧ ∑ m, st j m = ∑ m, st 0 m + j := by
  induction j with
  | zero => exact ⟨h.2.2.1, h.2.2.2, by simp⟩
  | succ j ih =>
    rw [h.1 j]
    refine ⟨fun m => ?_, fun m hm => ?_, ?_⟩
    · have := ih.1 m; show 0 ≤ st j m + (if m = L j then 1 else 0); split_ifs <;> omega
    · have hmq : m ≠ L j := fun hh => hm (hh ▸ h.2.1 j)
      simp [ih.2.1 m hm, hmq]
    · rw [Finset.sum_add_distrib, ih.2.2]; simp; ring

/-- Reachable end states. -/
def Reach (S : Set M) (r : ℕ → M) (H : ℕ) (x0 X : M → ℤ) : Prop :=
  ∃ c, ITraj S r H x0 c ∧ c H = X

/-- Excess cost of ending in `X`. -/
noncomputable def exc (S : Set M) (r : ℕ → M) (H : ℕ) (x0 X : M → ℤ) : ℝ :=
  Fend T e S r H x0 X - Fopt T e S r H x0

theorem Reach.conf {S : Set M} {r : ℕ → M} {H : ℕ} {x0 X : M → ℤ} (h : Reach S r H x0 X) :
    (∀ m, 0 ≤ X m) ∧ ∀ m, m ∉ S → X m = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨hc.2.1 H le_rfl, hc.2.2.1 H le_rfl⟩

theorem ccost_self (p : V) (x : M → ℤ) : ccost T e p x x = 0 := by
  unfold ccost; simp

theorem chain_up (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (D : ℝ) (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D) (d : ℕ) :
    ∀ j, 1 ≤ j → ∀ X, Reach (Sp T e p) r H (st j) X →
      ∃ Y, Reach (Sp T e p) r H (st (j + d)) Y ∧ ccost T e p X Y ≤ d * D ∧
        exc T e (Sp T e p) r H (st (j + d)) Y ≤ exc T e (Sp T e p) r H (st j) X := by
  induction d with
  | zero =>
    intro j _ X hX
    exact ⟨X, hX, by rw [ccost_self]; simp, le_rfl⟩
  | succ d ih =>
    intro j hj X hX
    obtain ⟨Y, hY, hc, hex⟩ := ih j hj X hX
    have hp := hN.props (j + d)
    obtain ⟨m, hR, hle⟩ := excess_up T e (Sp T e p) r H (st (j + d)) (L (j + d)) Y
      (hN.2.1 _) hp.1 hp.2.1 (by
        have h0s : 0 ≤ ∑ m, st 0 m := Finset.sum_nonneg fun m _ => hN.2.2.1 m
        have := hp.2.2; push_cast at this; omega) hY
    rw [← hN.1 (j + d)] at hR hle
    have hmS : m ∈ Sp T e p := by
      by_contra hn
      have h1 := (Reach.conf (hR : Reach _ _ _ _ _)).2 m hn
      have h2 := (Reach.conf hY).1 m
      simp at h1; omega
    refine ⟨_, by rw [show j + (d + 1) = j + d + 1 by omega]; exact hR, ?_, ?_⟩
    · have t1 := ccost_triangle T e p X Y (fun m' => Y m' + if m' = m then 1 else 0)
      rw [ccost_add_unit] at t1
      have := hD m hmS
      push_cast; rw [add_mul, one_mul]; linarith
    · rw [show j + (d + 1) = j + d + 1 by omega]
      unfold exc at hex ⊢
      linarith

theorem chain_down (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (D : ℝ) (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D) (d : ℕ) :
    ∀ j, 1 ≤ j → ∀ X, Reach (Sp T e p) r H (st (j + d)) X →
      ∃ Y, Reach (Sp T e p) r H (st j) Y ∧ ccost T e p X Y ≤ d * D ∧
        exc T e (Sp T e p) r H (st j) Y ≤ exc T e (Sp T e p) r H (st (j + d)) X := by
  induction d with
  | zero =>
    intro j _ X hX
    exact ⟨X, hX, by rw [ccost_self]; simp, le_rfl⟩
  | succ d ih =>
    intro j hj X hX
    have hp := hN.props (j + d)
    rw [show j + (d + 1) = j + d + 1 by omega, hN.1 (j + d)] at hX
    obtain ⟨m, hXm, hR, hle⟩ := excess_down T e (Sp T e p) r H (st (j + d)) (L (j + d)) X
      hp.1 hp.2.1 (by
        have h0s : 0 ≤ ∑ m, st 0 m := Finset.sum_nonneg fun m _ => hN.2.2.1 m
        have := hp.2.2; push_cast at this; omega) hX
    obtain ⟨Y, hY, hc, hex⟩ := ih j hj _ hR
    have hmS : m ∈ Sp T e p := by
      by_contra hn
      have h1 := (Reach.conf (hX : Reach _ _ _ _ _)).2 m hn
      omega
    refine ⟨Y, hY, ?_, ?_⟩
    · have t1 := ccost_triangle T e p X (fun m' => X m' - if m' = m then 1 else 0) Y
      have hXeq : X = fun m' => (X m' - if m' = m then 1 else 0) + if m' = m then 1 else 0 := by
        funext m'; ring
      have t2 : ccost T e p X (fun m' => X m' - if m' = m then 1 else 0) = dpath T e p m := by
        rw [ccost_comm]
        have h := ccost_add_unit T e p (fun m' => X m' - if m' = m then 1 else 0) m
        beta_reduce at h
        rwa [← hXeq] at h
      rw [t2] at t1
      have := hD m hmS
      push_cast; rw [add_mul, one_mul]; linarith
    · rw [show j + (d + 1) = j + d + 1 by omega, hN.1 (j + d)]
      unfold exc at hex ⊢
      linarith

end K17428


/-! D5c (17428d40): quota-pattern trajectories in `T(p)`, their internal optimum `Qopt`, the
`h`-values, `g`, telescoping and the base case (constant quota) of Theorem 31.
Needs D3a-D3h, D4, D5a, D5b. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

/-- Trajectories in `T(p)` following the quota pattern `κ` (total `|st (κ s)|` at time `s`). -/
def QTraj (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ : ℕ → ℕ) (c : ℕ → M → ℤ) : Prop :=
  (∀ m, c 0 m = st (κ 0) m) ∧ (∀ s ≤ H, ∀ m, 0 ≤ c s m) ∧
    (∀ s ≤ H, ∀ m, m ∉ Sp T e p → c s m = 0) ∧ (∀ s ≤ H, ∑ m, c s m = ∑ m, st (κ s) m) ∧
    (∀ s, 1 ≤ s → s ≤ H → r s ∈ Sp T e p → 1 ≤ c s (r s))

/-- Internal optimum for the quota pattern `κ`. -/
noncomputable def Qopt (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ : ℕ → ℕ) : ℝ :=
  sInf (qcost T e p H '' {c | QTraj T e p r H st κ c})

/-- `h^t(κ) = F_t(κ t) - F_{t-1}(κ t)`. -/
noncomputable def hval (p : V) (r : ℕ → M) (st : ℕ → M → ℤ) (κ : ℕ → ℕ) (t : ℕ) : ℝ :=
  Fopt T e (Sp T e p) r t (st (κ t)) - Fopt T e (Sp T e p) r (t - 1) (st (κ t))

/-- `∑_{t=1}^H h^t(κ)`. -/
noncomputable def Hsum (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ : ℕ → ℕ) : ℝ :=
  ∑ t ∈ range H, hval T e p r st κ (t + 1)

/-- `g(κ) = ∑_{s<H} |κ(s+1) - κ(s)|`. -/
noncomputable def gsum (H : ℕ) (κ : ℕ → ℕ) : ℝ := ∑ s ∈ range H, |((κ (s + 1) : ℝ) - κ s)|

theorem qcost_nonneg (p : V) (H : ℕ) (c : ℕ → M → ℤ) : 0 ≤ qcost T e p H c :=
  Finset.sum_nonneg fun _ _ => ccost_nonneg T e p _ _

theorem Qopt_le {p : V} {r : ℕ → M} {H : ℕ} {st : ℕ → M → ℤ} {κ : ℕ → ℕ} {c : ℕ → M → ℤ}
    (h : QTraj T e p r H st κ c) : Qopt T e p r H st κ ≤ qcost T e p H c :=
  csInf_le ⟨0, by rintro _ ⟨d, _, rfl⟩; exact qcost_nonneg T e p H d⟩ ⟨c, h, rfl⟩

theorem le_Qopt {p : V} {r : ℕ → M} {H : ℕ} {st : ℕ → M → ℤ} {κ : ℕ → ℕ} (X : ℝ)
    (hne : ∃ c, QTraj T e p r H st κ c) (h : ∀ c, QTraj T e p r H st κ c → X ≤ qcost T e p H c) :
    X ≤ Qopt T e p r H st κ := by
  obtain ⟨c, hc⟩ := hne
  exact le_csInf ⟨_, c, hc, rfl⟩ (by rintro _ ⟨d, hd, rfl⟩; exact h d hd)

theorem Fopt_zero (S : Set M) (r : ℕ → M) (x0 : M → ℤ) (h0 : ∀ m, 0 ≤ x0 m)
    (hS : ∀ m, m ∉ S → x0 m = 0) (hpos : 1 ≤ ∑ m, x0 m) : Fopt T e S r 0 x0 = 0 := by
  obtain ⟨c, hc⟩ := ITraj_nonempty S r 0 x0 h0 hS hpos
  have h1 := Fopt_le T e hc
  have h2 : tcost T e 0 c = 0 := by simp [tcost]
  linarith [Fopt_nonneg T e S r 0 x0]

/-- Telescoping of the `h`-values over a constant stretch of the quota. -/
theorem Hsum_const (p : V) (r : ℕ → M) (st : ℕ → M → ℤ) (κ : ℕ → ℕ) (k n : ℕ)
    (hk : ∀ t, 1 ≤ t → t ≤ n → κ t = k) :
    Hsum T e p r n st κ = Fopt T e (Sp T e p) r n (st k) - Fopt T e (Sp T e p) r 0 (st k) := by
  unfold Hsum hval
  rw [← Finset.sum_range_sub (fun t => Fopt T e (Sp T e p) r t (st k))]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [hk (t + 1) (by omega) (by omega), Nat.add_sub_cancel]

/-- Constant quota: quota trajectories are the `ITraj` of `st k` and both costs agree. -/
theorem Qopt_const (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ : ℕ → ℕ) (k : ℕ)
    (hk : ∀ t ≤ H, κ t = k) : Qopt T e p r H st κ = Fopt T e (Sp T e p) r H (st k) := by
  unfold Qopt Fopt
  congr 1
  ext v
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hI : ITraj (Sp T e p) r H (st k) c :=
      ⟨fun m => by rw [hc.1 m, hk 0 (Nat.zero_le _)], hc.2.1, hc.2.2.1,
        fun s hs => by rw [hc.2.2.2.1 s hs, hk s hs], hc.2.2.2.2⟩
    exact ⟨c, hI, (tcost_eq_qcost T e p r H (st k) c hI)⟩
  · rintro ⟨c, hc, rfl⟩
    have hQ : QTraj T e p r H st κ c :=
      ⟨fun m => by rw [hc.1 m, hk 0 (Nat.zero_le _)], hc.2.1, hc.2.2.1,
        fun s hs => by rw [hc.2.2.2.1 s hs, hk s hs], hc.2.2.2.2⟩
    exact ⟨c, hQ, (tcost_eq_qcost T e p r H (st k) c hc).symm⟩

theorem gsum_const (H : ℕ) (κ : ℕ → ℕ) (k : ℕ) (hk : ∀ t ≤ H, κ t = k) : gsum H κ = 0 := by
  unfold gsum
  refine Finset.sum_eq_zero fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  rw [hk s (by omega), hk (s + 1) (by omega)]; simp

/-- Base case of Theorem 31 (constant quota, `k ≥ 1`). -/
theorem thm31_const (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (κ : ℕ → ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk : ∀ t ≤ H, κ t = k) :
    Qopt T e p r H st κ = Hsum T e p r H st κ := by
  have hp := hN.props k
  have h0s : 0 ≤ ∑ m, st 0 m := Finset.sum_nonneg fun m _ => hN.2.2.1 m
  rw [Qopt_const T e p r H st κ k hk, Hsum_const T e p r st κ k H (fun t _ ht => hk t ht),
    Fopt_zero T e _ r _ hp.1 hp.2.1 (by have := hp.2.2; push_cast at this; omega)]
  ring

end K17428


/-! D5d (17428d40): Theorem 31 / Lemma 22 of BBMN for count trajectories in `T(p)`:
`|Qopt κ - ∑ h^t(κ)| ≤ D g(κ)` with `D` bounding the path weights below `p`.
Needs D3a-D3h, D4, D5a, D5b, D5c. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem QTraj_restrict {p : V} {r : ℕ → M} {H : ℕ} {st : ℕ → M → ℤ} {κ : ℕ → ℕ}
    {c : ℕ → M → ℤ} (hc : QTraj T e p r H st κ c) (n j : ℕ) (hn : n ≤ H)
    (hκ : ∀ s ≤ n, κ s = j) : ITraj (Sp T e p) r n (st j) c :=
  ⟨fun m => by rw [hc.1 m, hκ 0 (Nat.zero_le _)], fun s hs => hc.2.1 s (by omega),
    fun s hs => hc.2.2.1 s (by omega), fun s hs => by rw [hc.2.2.2.1 s (by omega), hκ s hs],
    fun s h1 hs hr => hc.2.2.2.2 s h1 (by omega) hr⟩

theorem qcost_split (p : V) (n H : ℕ) (hn : n < H) (c : ℕ → M → ℤ) :
    qcost T e p H c = qcost T e p n c + ccost T e p (c n) (c (n + 1)) +
      ∑ s ∈ Ico (n + 1) H, ccost T e p (c s) (c (s + 1)) := by
  unfold qcost
  rw [← Finset.sum_range_add_sum_Ico _ hn.le, Finset.sum_eq_sum_Ico_succ_bot hn]; ring

/-- Follow `B` up to time `n`, then `c`. -/
def splice (n : ℕ) (B c : ℕ → M → ℤ) (s : ℕ) : M → ℤ := if s ≤ n then B s else c s

theorem splice_spec (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ κ' : ℕ → ℕ) (n j : ℕ)
    (hn : n < H) (c B : ℕ → M → ℤ) (hc : QTraj T e p r H st κ c)
    (hB : ITraj (Sp T e p) r n (st j) B) (h1 : ∀ s ≤ n, κ' s = j) (h2 : ∀ s, n < s → κ' s = κ s) :
    QTraj T e p r H st κ' (splice n B c) ∧
      qcost T e p H (splice n B c) ≤
        tcost T e n B + ccost T e p (B n) (c n) + (qcost T e p H c - qcost T e p n c) := by
  constructor
  · refine ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
      fun s h1' hs hr => ?_⟩
    · simp only [splice, if_pos (Nat.zero_le n)]; rw [hB.1 m, h1 0 (Nat.zero_le _)]
    · unfold splice; split_ifs with h
      · exact hB.2.1 s h m
      · exact hc.2.1 s hs m
    · unfold splice; split_ifs with h
      · exact hB.2.2.1 s h m hm
      · exact hc.2.2.1 s hs m hm
    · unfold splice; split_ifs with h
      · rw [hB.2.2.2.1 s h, h1 s h]
      · rw [hc.2.2.2.1 s hs, h2 s (by omega)]
    · unfold splice; split_ifs with h
      · exact hB.2.2.2.2 s h1' h hr
      · exact hc.2.2.2.2 s h1' hs hr
  · rw [qcost_split T e p n H hn (splice n B c), qcost_split T e p n H hn c]
    have e1 : qcost T e p n (splice n B c) = tcost T e n B := by
      rw [tcost_eq_qcost T e p r n (st j) B hB]
      unfold qcost
      refine Finset.sum_congr rfl fun s hs => ?_
      have := Finset.mem_range.1 hs
      simp only [splice, if_pos (show s ≤ n by omega), if_pos (show s + 1 ≤ n by omega)]
    have e2 : ∑ s ∈ Ico (n + 1) H, ccost T e p (splice n B c s) (splice n B c (s + 1)) =
        ∑ s ∈ Ico (n + 1) H, ccost T e p (c s) (c (s + 1)) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have := (Finset.mem_Ico.1 hs).1
      simp only [splice, if_neg (show ¬ s ≤ n by omega), if_neg (show ¬ s + 1 ≤ n by omega)]
    have e3 : splice n B c n = B n := by simp [splice]
    have e4 : splice n B c (n + 1) = c (n + 1) := by simp [splice]
    rw [e1, e2, e3, e4]
    have := ccost_triangle T e p (B n) (c n) (c (n + 1))
    linarith

theorem chain_any (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (D : ℝ) (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D)
    (k1 k2 : ℕ) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) (X : M → ℤ) (hX : Reach (Sp T e p) r H (st k1) X) :
    ∃ Y, Reach (Sp T e p) r H (st k2) Y ∧ ccost T e p X Y ≤ |(k2 : ℝ) - k1| * D ∧
      exc T e (Sp T e p) r H (st k2) Y ≤ exc T e (Sp T e p) r H (st k1) X := by
  rcases le_total k1 k2 with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨Y, hY, hc, hex⟩ := chain_up T e p r H st L hN D hD d k1 h1 X hX
    refine ⟨Y, hY, ?_, hex⟩
    push_cast
    rw [show (k1 : ℝ) + d - k1 = d by ring, abs_of_nonneg (Nat.cast_nonneg _)]; exact hc
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨Y, hY, hc, hex⟩ := chain_down T e p r H st L hN D hD d k2 h2 X hX
    refine ⟨Y, hY, ?_, hex⟩
    push_cast
    rw [show (k2 : ℝ) - (k2 + d) = -d by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; exact hc

theorem QTraj_nonempty (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (κ : ℕ → ℕ) (hκ : ∀ t ≤ H, 1 ≤ κ t) :
    ∃ c, QTraj T e p r H st κ c := by
  classical
  have hq := hN.2.1 0
  let g : ℕ → M := fun s => if r s ∈ Sp T e p then r s else L 0
  have hgS : ∀ s, g s ∈ Sp T e p := by
    intro s; by_cases h : r s ∈ Sp T e p <;> simp [g, h, hq]
  refine ⟨fun s m => if s = 0 then st (κ 0) m else if m = g s then ∑ m', st (κ s) m' else 0,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro m; simp
  · intro s _ m
    by_cases h : s = 0
    · simp [h, (hN.props (κ 0)).1 m]
    · simp only [h, if_false]; split_ifs
      · exact Finset.sum_nonneg fun m' _ => (hN.props (κ s)).1 m'
      · exact le_rfl
  · intro s _ m hm
    by_cases h : s = 0
    · simp [h, (hN.props (κ 0)).2.1 m hm]
    · simp only [h, if_false]
      have : m ≠ g s := fun hh => hm (hh ▸ hgS s)
      simp [this]
  · intro s _
    by_cases h : s = 0
    · subst h; simp
    · simp [h]
  · intro s h1 hs hr
    have hs0 : s ≠ 0 := by omega
    have hg : g s = r s := by simp [g, hr]
    simp [hs0, hg]
    have h3 := (hN.props (κ s)).2.2
    have h0s : 0 ≤ ∑ m, st 0 m := Finset.sum_nonneg fun m _ => hN.2.2.1 m
    have h4 := hκ s hs
    omega

/-- Theorem 31 (BBMN App. B) for count trajectories in `T(p)`. -/
theorem thm31 (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (D : ℝ) (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D)
    (κ : ℕ → ℕ) (hκ : ∀ t ≤ H, 1 ≤ κ t) :
    Hsum T e p r H st κ - D * gsum H κ ≤ Qopt T e p r H st κ ∧
      Qopt T e p r H st κ ≤ Hsum T e p r H st κ + D * gsum H κ := by
  suffices key : ∀ i, i ≤ H → ∀ κ : ℕ → ℕ, (∀ t ≤ H, 1 ≤ κ t) → (∀ s ≤ H - i, κ s = κ 0) →
      Hsum T e p r H st κ - D * gsum H κ ≤ Qopt T e p r H st κ ∧
        Qopt T e p r H st κ ≤ Hsum T e p r H st κ + D * gsum H κ by
    exact key H le_rfl κ hκ (fun s hs => by rw [show s = 0 by omega])
  intro i
  induction i with
  | zero =>
    intro _ κ hκ hc
    have hk : ∀ t ≤ H, κ t = κ 0 := fun t ht => hc t (by omega)
    rw [thm31_const T e p r H st L hN κ (κ 0) (hκ 0 (Nat.zero_le _)) hk, gsum_const H κ (κ 0) hk]
    constructor <;> linarith
  | succ i ih =>
    intro hi κ hκ hc
    set n := H - (i + 1) with hn
    have hnH : n < H := by omega
    by_cases hstep : κ (n + 1) = κ n
    · exact ih (by omega) κ hκ (fun s hs => by
        rcases Nat.lt_or_ge s (n + 1) with h | h
        · exact hc s (by omega)
        · rw [show s = n + 1 by omega, hstep]; exact hc n le_rfl)
    · set k1 := κ 0 with hk1d
      set k2 := κ (n + 1) with hk2d
      have hk1 : ∀ s ≤ n, κ s = k1 := hc
      have k1pos : 1 ≤ k1 := hκ 0 (Nat.zero_le _)
      have k2pos : 1 ≤ k2 := hκ (n + 1) (by omega)
      set κ' : ℕ → ℕ := fun t => if t ≤ n then k2 else κ t with hκ'd
      have hκ'1 : ∀ s ≤ n, κ' s = k2 := fun s hs => if_pos hs
      have hκ'2 : ∀ s, n < s → κ' s = κ s := fun s hs => if_neg (by omega)
      have hκ' : ∀ t ≤ H, 1 ≤ κ' t := fun t ht => by
        rcases Nat.lt_or_ge n t with h | h
        · rw [hκ'2 t h]; exact hκ t ht
        · rw [hκ'1 t h]; exact k2pos
      have hc' : ∀ s ≤ H - i, κ' s = κ' 0 := fun s hs => by
        rw [hκ'1 0 (Nat.zero_le _)]
        rcases Nat.lt_or_ge n s with h | h
        · rw [hκ'2 s h, show s = n + 1 by omega]
        · exact hκ'1 s h
      obtain ⟨IHl, IHu⟩ := ih (by omega) κ' hκ' hc'
      -- the h-sums differ only before n
      have hsplit : ∀ κ0 : ℕ → ℕ, Hsum T e p r H st κ0 = Hsum T e p r n st κ0 +
          ∑ t ∈ Ico n H, hval T e p r st κ0 (t + 1) := fun κ0 => by
        unfold Hsum; rw [Finset.sum_range_add_sum_Ico _ hnH.le]
      have htail : ∑ t ∈ Ico n H, hval T e p r st κ (t + 1) =
          ∑ t ∈ Ico n H, hval T e p r st κ' (t + 1) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have := (Finset.mem_Ico.1 ht).1
        unfold hval; rw [hκ'2 (t + 1) (by omega)]
      have hF1 := Hsum_const T e p r st κ k1 n (fun t _ ht => hk1 t ht)
      have hF2 := Hsum_const T e p r st κ' k2 n (fun t _ ht => hκ'1 t ht)
      have hz1 := Fopt_zero T e _ r _ (hN.props k1).1 (hN.props k1).2.1
        (by have := (hN.props k1).2.2; have := Finset.sum_nonneg fun m (_ : m ∈ univ) =>
              hN.2.2.1 m; omega)
      have hz2 := Fopt_zero T e _ r _ (hN.props k2).1 (hN.props k2).2.1
        (by have := (hN.props k2).2.2; have := Finset.sum_nonneg fun m (_ : m ∈ univ) =>
              hN.2.2.1 m; omega)
      have hH : Hsum T e p r H st κ - Hsum T e p r H st κ' =
          Fopt T e (Sp T e p) r n (st k1) - Fopt T e (Sp T e p) r n (st k2) := by
        rw [hsplit κ, hsplit κ', htail, hF1, hF2, hz1, hz2]; ring
      have hg : gsum H κ = gsum H κ' + |(k2 : ℝ) - k1| := by
        unfold gsum
        have hpt : ∀ s ∈ range H, |((κ (s + 1) : ℝ) - κ s)| =
            |((κ' (s + 1) : ℝ) - κ' s)| + if s = n then |(k2 : ℝ) - k1| else 0 := by
          intro s hs
          rcases lt_trichotomy s n with h | h | h
          · rw [hk1 s h.le, hk1 (s + 1) h, hκ'1 s h.le, hκ'1 (s + 1) h, if_neg h.ne]; simp
          · subst h
            rw [hk1 _ le_rfl, hκ'1 _ le_rfl, hκ'2 _ (Nat.lt_succ_self _), if_pos rfl, ← hk2d]; simp
          · rw [hκ'2 s h, hκ'2 (s + 1) (by omega), if_neg h.ne']; simp
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp [hnH]
      have hg' : D * gsum H κ = D * gsum H κ' + |(k2 : ℝ) - k1| * D := by rw [hg]; ring
      constructor
      · -- lower bound
        refine le_Qopt T e _ (QTraj_nonempty T e p r H st L hN κ hκ) fun c hc0 => ?_
        have hIc : ITraj (Sp T e p) r n (st k1) c := QTraj_restrict T e hc0 n k1 hnH.le hk1
        obtain ⟨Y, hY, hcY, hexY⟩ :=
          chain_any T e p r n st L hN D hD k1 k2 k1pos k2pos (c n) ⟨c, hIc, rfl⟩
        obtain ⟨B, hB, hBY, hBc⟩ := Fend_attained T e (Sp T e p) r n (st k2) Y hY
        obtain ⟨hQ', hcost'⟩ := splice_spec T e p r H st κ κ' n k2 hnH c B hc0 hB hκ'1 hκ'2
        have e1 := Qopt_le T e hQ'
        have e2 := Fend_le T e hIc
        have e3 : tcost T e n c = qcost T e p n c := tcost_eq_qcost T e p r n (st k1) c hIc
        rw [hBY] at hcost'
        have e4 : ccost T e p Y (c n) = ccost T e p (c n) Y := ccost_comm T e p _ _
        unfold exc at hexY
        linarith
      · -- upper bound
        have hQ : Qopt T e p r H st κ - |(k2 : ℝ) - k1| * D -
            (Fopt T e (Sp T e p) r n (st k1) - Fopt T e (Sp T e p) r n (st k2)) ≤
              Qopt T e p r H st κ' := by
          refine le_Qopt T e _ (QTraj_nonempty T e p r H st L hN κ' hκ') fun c' hc0 => ?_
          have hIc : ITraj (Sp T e p) r n (st k2) c' :=
            QTraj_restrict T e hc0 n k2 hnH.le hκ'1
          obtain ⟨Y, hY, hcY, hexY⟩ :=
            chain_any T e p r n st L hN D hD k2 k1 k2pos k1pos (c' n) ⟨c', hIc, rfl⟩
          obtain ⟨B, hB, hBY, hBc⟩ := Fend_attained T e (Sp T e p) r n (st k1) Y hY
          obtain ⟨hQ', hcost'⟩ := splice_spec T e p r H st κ' κ n k1 hnH c' B hc0 hB hk1
            (fun s hs => (hκ'2 s hs).symm)
          have e1 := Qopt_le T e hQ'
          have e2 := Fend_le T e hIc
          have e3 : tcost T e n c' = qcost T e p n c' :=
            tcost_eq_qcost T e p r n (st k2) c' hIc
          rw [hBY] at hcost'
          have e4 : ccost T e p Y (c' n) = ccost T e p (c' n) Y := ccost_comm T e p _ _
          rw [abs_sub_comm] at hcY
          unfold exc at hexY
          linarith
        linarith

end K17428


/-! D2 (17428d40, relay 4): the split direction of the recurrence (BBMN Lemma 21) for the internal
cost of `T(p)`: the internal cost splits over the children `i` of `p` as the edge cost
`W i * |Δ nsub i|` plus the internal cost of `T(i)`; restrictions of quota trajectories are quota
trajectories of the children; `F_t = F_{t-1}` when the request lies outside the subtree; and the
path weight below a non-root node of a weighted `σ`-HST is at most `W i / (σ - 1)`.
Needs D3a-D3h, D4, D5a-D5d. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem not_mem_inner_self (i : V) : i ∉ inner T i := by
  simp [inner]

theorem mem_inner {p v : V} : v ∈ inner T p ↔ v ≠ T.root ∧ T.IsAnc p v ∧ v ≠ p := by
  simp [inner]

theorem inner_split (p : V) :
    inner T p = (children T p).biUnion fun i => insert i (inner T i) := by
  ext v
  simp only [mem_inner, mem_biUnion, mem_insert]
  constructor
  · rintro ⟨hvr, hpv, hvp⟩
    obtain ⟨c, hc, hcv⟩ := exists_child T hpv hvp
    refine ⟨c, hc, ?_⟩
    by_cases h : v = c
    · exact Or.inl h
    · exact Or.inr ⟨hvr, hcv, h⟩
  · rintro ⟨c, hc, h | ⟨hvr, hcv, _⟩⟩
    · subst h
      exact ⟨((mem_children T).1 hc).1, isAnc_of_child T hc (isAnc_refl T v),
        ne_of_child T hc (isAnc_refl T v)⟩
    · exact ⟨hvr, isAnc_of_child T hc hcv, ne_of_child T hc hcv⟩

theorem inner_disj (p : V) :
    ((children T p : Set V)).PairwiseDisjoint fun i => insert i (inner T i) := by
  intro i hi i' hi' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hv hv'
  have a1 : T.IsAnc i v := by
    rcases mem_insert.1 hv with h | h
    · subst h; exact isAnc_refl T v
    · exact ((mem_inner T).1 h).2.1
  have a2 : T.IsAnc i' v := by
    rcases mem_insert.1 hv' with h | h
    · subst h; exact isAnc_refl T v
    · exact ((mem_inner T).1 h).2.1
  exact hne (child_unique T hi hi' a1 a2)

/-- The internal cost of `T(p)` splits over the children of `p`. -/
theorem ccost_split (p : V) (x y : M → ℤ) :
    ccost T e p x y = ∑ i ∈ children T p,
      (T.W i * |((nsub T e y i - nsub T e x i : ℤ) : ℝ)| + ccost T e i x y) := by
  unfold ccost
  rw [inner_split T p, Finset.sum_biUnion (inner_disj T p)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_insert (not_mem_inner_self T i)]

/-- Integer variation of the subtree mass of `i` along `c`. -/
noncomputable def gvar (i : V) (H : ℕ) (c : ℕ → M → ℤ) : ℝ :=
  ∑ s ∈ range H, |((nsub T e (c (s + 1)) i - nsub T e (c s) i : ℤ) : ℝ)|

theorem gvar_nonneg (i : V) (H : ℕ) (c : ℕ → M → ℤ) : 0 ≤ gvar T e i H c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The internal cost of a trajectory in `T(p)` splits over the children of `p`. -/
theorem qcost_children (p : V) (H : ℕ) (c : ℕ → M → ℤ) :
    qcost T e p H c = ∑ i ∈ children T p, (T.W i * gvar T e i H c + qcost T e i H c) := by
  unfold qcost gvar
  simp_rw [ccost_split T e p, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]

open Classical in
/-- Restriction of a state to the leaves of `T(i)`. -/
noncomputable def rst (i : V) (x : M → ℤ) : M → ℤ := fun m => if m ∈ Sp T e i then x m else 0

theorem nsub_rst {i v : V} (x : M → ℤ) (hv : T.IsAnc i v) : nsub T e (rst T e i x) v = nsub T e x v := by
  classical
  unfold nsub rst
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : T.IsAnc v (e m : V)
  · have : m ∈ Sp T e i := isAnc_trans T hv h
    simp [h, this]
  · simp [h]

theorem sum_rst (i : V) (x : M → ℤ) : ∑ m, rst T e i x m = nsub T e x i := by
  classical
  unfold rst nsub
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : T.IsAnc i (e m : V)
  · have : m ∈ Sp T e i := h
    simp [h, this]
  · have : m ∉ Sp T e i := h
    simp [h, this]

theorem ccost_rst (i : V) (x y : M → ℤ) :
    ccost T e i (rst T e i x) (rst T e i y) = ccost T e i x y := by
  unfold ccost
  refine Finset.sum_congr rfl fun v hv => ?_
  have hiv := ((mem_inner T).1 hv).2.1
  rw [nsub_rst T e x hiv, nsub_rst T e y hiv]

theorem qcost_rst (i : V) (H : ℕ) (c : ℕ → M → ℤ) :
    qcost T e i H (fun s => rst T e i (c s)) = qcost T e i H c := by
  unfold qcost
  exact Finset.sum_congr rfl fun s _ => ccost_rst T e i _ _

theorem nsub_nonneg' (x : M → ℤ) (hx : ∀ m, 0 ≤ x m) (v : V) : 0 ≤ nsub T e x v := by
  classical
  unfold nsub
  exact Finset.sum_nonneg fun m _ => by split_ifs <;> simp [hx m]

/-- The restriction of a quota trajectory of `T(p)` to a child subtree `T(i)` is a quota
trajectory of `T(i)` for the child's own pattern `κ'` (any start family `st'` compatible at time
`0` and with the right totals). -/
theorem QTraj_rst (p i : V) (hpi : T.IsAnc p i) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ : ℕ → ℕ)
    (c : ℕ → M → ℤ) (hc : QTraj T e p r H st κ c) (st' : ℕ → M → ℤ) (κ' : ℕ → ℕ)
    (h0 : ∀ m, st' (κ' 0) m = rst T e i (st (κ 0)) m)
    (htot : ∀ s ≤ H, ∑ m, st' (κ' s) m = nsub T e (c s) i) :
    QTraj T e i r H st' κ' (fun s => rst T e i (c s)) := by
  classical
  refine ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_, fun s h1 hs hr => ?_⟩
  · rw [h0 m]; simp only [rst]; rw [hc.1 m]
  · simp only [rst]; split_ifs
    · exact hc.2.1 s hs m
    · exact le_rfl
  · simp [rst, hm]
  · rw [sum_rst, htot s hs]
  · have hrp : r s ∈ Sp T e p := isAnc_trans T hpi hr
    simp only [rst, if_pos hr]
    exact hc.2.2.2.2 s h1 hs hrp

theorem Qopt_le_of {p : V} {r : ℕ → M} {H : ℕ} {st : ℕ → M → ℤ} {κ : ℕ → ℕ} {c : ℕ → M → ℤ}
    (hc : QTraj T e p r H st κ c) : Qopt T e p r H st κ ≤ qcost T e p H c :=
  csInf_le ⟨0, by rintro _ ⟨d, _, rfl⟩; exact qcost_nonneg T e p H d⟩ ⟨c, hc, rfl⟩

/-- **D2 (split direction of Lemma 21).** The internal cost of a quota trajectory of `T(p)` is at
least the sum over the children `i` of the edge cost `W i * g_i` and the children's optima
`Qopt_i(κ_i)`, for any child start families compatible with the trajectory. -/
theorem qcost_ge_split (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (κ : ℕ → ℕ)
    (c : ℕ → M → ℤ) (hc : QTraj T e p r H st κ c) (st' : V → ℕ → M → ℤ) (κ' : V → ℕ → ℕ)
    (h0 : ∀ i ∈ children T p, ∀ m, st' i (κ' i 0) m = rst T e i (st (κ 0)) m)
    (htot : ∀ i ∈ children T p, ∀ s ≤ H, ∑ m, st' i (κ' i s) m = nsub T e (c s) i) :
    ∑ i ∈ children T p, (T.W i * gvar T e i H c + Qopt T e i r H (st' i) (κ' i)) ≤
      qcost T e p H c := by
  rw [qcost_children T e p H c]
  refine Finset.sum_le_sum fun i hi => ?_
  have hpi : T.IsAnc p i := isAnc_of_child T hi (isAnc_refl T i)
  have h := Qopt_le_of T e (QTraj_rst T e p i hpi r H st κ c hc (st' i) (κ' i) (h0 i hi) (htot i hi))
  rw [qcost_rst] at h
  linarith

/-- `gvar` in terms of a natural-number pattern equal to the subtree masses. -/
theorem gvar_eq_gsum (i : V) (H : ℕ) (c : ℕ → M → ℤ) (κ' : ℕ → ℕ)
    (hκ : ∀ s ≤ H, (κ' s : ℤ) = nsub T e (c s) i) : gvar T e i H c = gsum H κ' := by
  unfold gvar gsum
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  rw [← hκ s (by omega), ← hκ (s + 1) (by omega)]
  push_cast; rfl

theorem ITraj_cext {S : Set M} {r : ℕ → M} {H : ℕ} {x0 : M → ℤ} {c : ℕ → M → ℤ}
    (hc : ITraj S r H x0 c) (hr : r (H + 1) ∉ S) : ITraj S r (H + 1) x0 (cext H c) := by
  refine ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_, fun s h1 hs hrs => ?_⟩
  · rw [cext_eq H c 0 (Nat.zero_le _)]; exact hc.1 m
  · unfold cext; split_ifs with h
    · exact hc.2.1 s h m
    · exact hc.2.1 H le_rfl m
  · unfold cext; split_ifs with h
    · exact hc.2.2.1 s h m hm
    · exact hc.2.2.1 H le_rfl m hm
  · unfold cext; split_ifs with h
    · exact hc.2.2.2.1 s h
    · exact hc.2.2.2.1 H le_rfl
  · have hsH : s ≤ H := by
      rcases Nat.lt_or_ge H s with h | h
      · have : s = H + 1 := by omega
        subst this; exact absurd hrs hr
      · exact h
    rw [cext_eq H c s hsH]; exact hc.2.2.2.2 s h1 hsH hrs

/-- `F_{t+1} = F_t` when the request `r (t+1)` lies outside `S`. -/
theorem Fopt_out (S : Set M) (r : ℕ → M) (H : ℕ) (x0 : M → ℤ) (hne : ∃ c, ITraj S r H x0 c)
    (hr : r (H + 1) ∉ S) : Fopt T e S r (H + 1) x0 = Fopt T e S r H x0 := by
  obtain ⟨c0, hc0⟩ := hne
  apply le_antisymm
  · refine le_Fopt T e _ ⟨c0, hc0⟩ fun c hc => ?_
    have := Fopt_le T e (ITraj_cext hc hr)
    rwa [tcost_cext] at this
  · exact Fopt_le_succ T e S r H x0 ⟨_, ITraj_cext hc0 hr⟩

open Classical in
theorem dpath_split (p : V) (m : M) :
    dpath T e p m = ∑ i ∈ children T p,
      ((if T.IsAnc i (e m : V) then T.W i else 0) + dpath T e i m) := by
  unfold dpath
  rw [inner_split T p, Finset.sum_biUnion (inner_disj T p)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_insert (not_mem_inner_self T i)]

open Classical in
theorem dpath_zero_of_not (i : V) (m : M) (h : ¬ T.IsAnc i (e m : V)) : dpath T e i m = 0 := by
  unfold dpath
  refine Finset.sum_eq_zero fun v hv => ?_
  have hiv := ((mem_inner T).1 hv).2.1
  rw [if_neg]
  exact fun hv' => h (isAnc_trans T hiv hv')

theorem card_inner_child_lt {p i : V} (hi : i ∈ children T p) :
    (inner T i).card < (inner T p).card := by
  have hsub : insert i (inner T i) ⊆ inner T p := by
    rw [inner_split T p]
    exact Finset.subset_biUnion_of_mem (fun j => insert j (inner T j)) hi
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (not_mem_inner_self T i)] at this
  omega

/-- In a weighted `σ`-HST (`σ > 1`), the weight of the path from a non-root node `i` down to a
leaf is at most `W i / (σ - 1)`. -/
theorem dpath_le_hst (σ : ℝ) (hσ : 1 < σ) (hT : T.IsWeightedHST σ) (m : M) :
    ∀ i : V, i ≠ T.root → dpath T e i m ≤ T.W i / (σ - 1) := by
  classical
  have hσ1 : 0 < σ - 1 := by linarith
  suffices key : ∀ n, ∀ i : V, (inner T i).card ≤ n → i ≠ T.root → dpath T e i m ≤ T.W i / (σ - 1) by
    exact fun i hi => key _ i le_rfl hi
  intro n
  induction n with
  | zero =>
    intro i hn hi
    have : inner T i = ∅ := Finset.card_eq_zero.1 (by omega)
    unfold dpath; rw [this, Finset.sum_empty]
    exact div_nonneg (T.W_pos i hi).le hσ1.le
  | succ n ih =>
    intro i hn hi
    rw [dpath_split T e i m]
    by_cases hex : ∃ c ∈ children T i, T.IsAnc c (e m : V)
    · obtain ⟨c, hc, hcm⟩ := hex
      rw [Finset.sum_eq_single_of_mem c hc]
      · rw [if_pos hcm]
        have hcr : c ≠ T.root := ((mem_children T).1 hc).1
        have hpc : T.parent c = i := ((mem_children T).1 hc).2
        have h1 := ih c (by have := card_inner_child_lt T hc; omega) hcr
        have h2 : σ * T.W c ≤ T.W i := by
          have := hT c hcr (by rw [hpc]; exact hi); rwa [hpc] at this
        have hWc := T.W_pos c hcr
        rw [le_div_iff₀ hσ1] at h1 ⊢
        nlinarith
      · intro c' hc' hne
        have hn' : ¬ T.IsAnc c' (e m : V) := fun h => hne (child_unique T hc' hc h hcm)
        rw [if_neg hn', dpath_zero_of_not T e c' m hn', add_zero]
    · push Not at hex
      rw [Finset.sum_eq_zero fun c hc => by
        rw [if_neg (hex c hc), dpath_zero_of_not T e c m (hex c hc), add_zero]]
      exact div_nonneg (T.W_pos i hi).le hσ1.le

end K17428


/-! D6a (17428d40, relay 4): first half of the capping projection (design D6', plan file).
Real subtree masses split over children (`smass_split`), leaf facts, and the SOURCE EXTRACTION
lemma: from a subtree `T(v)` with `Y v > Z v` (`Z` superadditive, e.g. expected quotas with unused
quota parked at the node) one can remove any amount `ε ≤ (Y v - Z v)^+` of leaf mass so that every
node `u` of `T(v)` loses at most `(Y u - Z u)^+` (so its mass stays between `Y u` and `Z u`).
Needs D3d (children, exists_child, child_unique, card_children_anc), D2 (card_inner_child_lt). -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

open Classical in
/-- Real amount sitting at the node `v` itself (zero unless `v` is a leaf). -/
noncomputable def rcnt (x : M → ℝ) (v : V) : ℝ := ∑ m, if (e m : V) = v then x m else 0

theorem smass_split (x : M → ℝ) (v : V) :
    subtreeMass T e x v = rcnt T e x v + ∑ c ∈ children T v, subtreeMass T e x c := by
  classical
  unfold subtreeMass rcnt
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : (∑ c ∈ children T v, if T.IsAnc c (e m : V) then x m else 0) =
      ((children T v).filter fun c => T.IsAnc c (e m : V)).card • x m := by
    rw [← Finset.sum_filter, Finset.sum_const]
  rw [hc, card_children_anc]
  by_cases h1 : (e m : V) = v
  · simp [h1, isAnc_refl T v]
  · by_cases h2 : T.IsAnc v (e m : V)
    · simp [h1, h2]
    · simp [h1, h2]

theorem children_leaf (m : M) : children T (e m : V) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
  rw [mem_children] at hc
  exact (e m).2 c hc.1 hc.2

theorem leaf_of_children_empty {v : V} (h : children T v = ∅) : ∃ m, (e m : V) = v := by
  have hl : T.IsLeaf v := fun u hu hp => by
    have : u ∈ children T v := (mem_children T).2 ⟨hu, hp⟩
    rw [h] at this; exact absurd this (Finset.notMem_empty u)
  exact ⟨e.symm ⟨v, hl⟩, by simp⟩

theorem anc_leaf {m : M} {u : V} (h : T.IsAnc (e m : V) u) : u = e m := by
  by_contra hne
  obtain ⟨c, hc, _⟩ := exists_child T h hne
  rw [children_leaf] at hc; exact Finset.notMem_empty c hc

theorem rcnt_inner (x : M → ℝ) {v : V} (h : children T v ≠ ∅) : rcnt T e x v = 0 := by
  classical
  unfold rcnt
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg]
  intro hm; apply h; rw [← hm]; exact children_leaf T e m

theorem smass_inner (x : M → ℝ) {v : V} (h : children T v ≠ ∅) :
    subtreeMass T e x v = ∑ c ∈ children T v, subtreeMass T e x c := by
  rw [smass_split, rcnt_inner T e x h, zero_add]

theorem smass_zero (v : V) : subtreeMass T e (fun _ => (0 : ℝ)) v = 0 := by
  classical
  unfold subtreeMass; simp

open Classical in
theorem smass_single (m0 : M) (ε : ℝ) (u : V) :
    subtreeMass T e (fun m => if m = m0 then ε else 0) u = if T.IsAnc u (e m0 : V) then ε else 0 := by
  classical
  unfold subtreeMass
  rw [Finset.sum_eq_single m0]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem Z_nonneg_leaf (Z : V → ℝ) (hZ : ∀ v, ∑ c ∈ children T v, Z c ≤ Z v) (m : M) : 0 ≤ Z (e m) := by
  have := hZ (e m); rwa [children_leaf, Finset.sum_empty] at this

/-- Mass of a sum of child-supported pieces at a node below one child. -/
theorem smass_pieces (v : V) (D : V → M → ℝ)
    (hD : ∀ c ∈ children T v, ∀ m, ¬ T.IsAnc c (e m : V) → D c m = 0) {c u : V}
    (hc : c ∈ children T v) (hu : T.IsAnc c u) :
    subtreeMass T e (fun m => ∑ c' ∈ children T v, D c' m) u = subtreeMass T e (D c) u := by
  classical
  unfold subtreeMass
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : T.IsAnc u (e m : V)
  · rw [if_pos hm, if_pos hm]
    have hcm : T.IsAnc c (e m : V) := isAnc_trans T hu hm
    show ∑ c' ∈ children T v, D c' m = D c m
    rw [Finset.sum_eq_single c]
    · intro c' hc' hne
      exact hD c' hc' m fun h => hne (child_unique T hc' hc h hcm)
    · intro h; exact absurd hc h
  · rw [if_neg hm, if_neg hm]

/-- **Source extraction.** -/
theorem extract (y : M → ℝ) (Z : V → ℝ) (hZ : ∀ v, ∑ c ∈ children T v, Z c ≤ Z v) :
    ∀ v : V, ∀ ε : ℝ, 0 ≤ ε → ε ≤ max 0 (subtreeMass T e y v - Z v) →
      ∃ d : M → ℝ, (∀ m, 0 ≤ d m) ∧ (∀ m, ¬ T.IsAnc v (e m : V) → d m = 0) ∧
        subtreeMass T e d v = ε ∧
        ∀ u, T.IsAnc v u → 0 ≤ subtreeMass T e d u ∧
          subtreeMass T e d u ≤ max 0 (subtreeMass T e y u - Z u) := by
  classical
  suffices key : ∀ n, ∀ v : V, (inner T v).card ≤ n → ∀ ε : ℝ, 0 ≤ ε →
      ε ≤ max 0 (subtreeMass T e y v - Z v) →
      ∃ d : M → ℝ, (∀ m, 0 ≤ d m) ∧ (∀ m, ¬ T.IsAnc v (e m : V) → d m = 0) ∧
        subtreeMass T e d v = ε ∧
        ∀ u, T.IsAnc v u → 0 ≤ subtreeMass T e d u ∧
          subtreeMass T e d u ≤ max 0 (subtreeMass T e y u - Z u) by
    exact fun v => key _ v le_rfl
  intro n
  induction n with
  | zero =>
    intro v hn ε hε0 hε
    have hin : inner T v = ∅ := Finset.card_eq_zero.1 (by omega)
    have hch : children T v = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
      have := card_inner_child_lt T hc
      rw [hin, Finset.card_empty] at this; omega
    obtain ⟨m0, rfl⟩ := leaf_of_children_empty T e hch
    refine ⟨fun m => if m = m0 then ε else 0, fun m => by dsimp only; split_ifs <;> simp [hε0],
      fun m hm => ?_, ?_, fun u hu => ?_⟩
    · have : m ≠ m0 := by rintro rfl; exact hm (isAnc_refl T _)
      simp [this]
    · rw [smass_single, if_pos (isAnc_refl T _)]
    · rw [anc_leaf T e hu, smass_single, if_pos (isAnc_refl T _)]
      exact ⟨hε0, hε⟩
  | succ n ih =>
    intro v hn ε hε0 hε
    by_cases hch : children T v = ∅
    · obtain ⟨m0, rfl⟩ := leaf_of_children_empty T e hch
      refine ⟨fun m => if m = m0 then ε else 0, fun m => by dsimp only; split_ifs <;> simp [hε0],
        fun m hm => ?_, ?_, fun u hu => ?_⟩
      · have : m ≠ m0 := by rintro rfl; exact hm (isAnc_refl T _)
        simp [this]
      · rw [smass_single, if_pos (isAnc_refl T _)]
      · rw [anc_leaf T e hu, smass_single, if_pos (isAnc_refl T _)]
        exact ⟨hε0, hε⟩
    by_cases hz : ε = 0
    · subst hz
      refine ⟨fun _ => 0, fun _ => le_rfl, fun _ _ => rfl, smass_zero T e v, fun u _ => ?_⟩
      rw [smass_zero]; exact ⟨le_rfl, le_max_left _ _⟩
    have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hz)
    have hεv : ε ≤ subtreeMass T e y v - Z v := by
      rcases le_max_iff.1 hε with h | h
      · linarith
      · exact h
    set a : V → ℝ := fun c => max 0 (subtreeMass T e y c - Z c) with ha
    set A : ℝ := ∑ c ∈ children T v, a c with hA
    have hεA : ε ≤ A := by
      have h1 := smass_inner T e y hch
      have h2 := hZ v
      have h3 : ∑ c ∈ children T v, (subtreeMass T e y c - Z c) ≤ A :=
        Finset.sum_le_sum fun c _ => le_max_right _ _
      rw [Finset.sum_sub_distrib] at h3
      linarith
    have hApos : 0 < A := lt_of_lt_of_le hεpos hεA
    have ha0 : ∀ c, 0 ≤ a c := fun c => le_max_left _ _
    have hrat : ε / A ≤ 1 := (div_le_one hApos).2 hεA
    have hrat0 : 0 ≤ ε / A := div_nonneg hε0 hApos.le
    have hpiece : ∀ c ∈ children T v, ∃ d : M → ℝ, (∀ m, 0 ≤ d m) ∧
        (∀ m, ¬ T.IsAnc c (e m : V) → d m = 0) ∧ subtreeMass T e d c = ε / A * a c ∧
        ∀ u, T.IsAnc c u → 0 ≤ subtreeMass T e d u ∧
          subtreeMass T e d u ≤ max 0 (subtreeMass T e y u - Z u) := by
      intro c hc
      refine ih c (by have := card_inner_child_lt T hc; omega) (ε / A * a c)
        (mul_nonneg hrat0 (ha0 c)) ?_
      have : ε / A * a c ≤ 1 * a c := mul_le_mul_of_nonneg_right hrat (ha0 c)
      rw [one_mul] at this; exact this
    choose! D hD using hpiece
    have hDs : ∀ c ∈ children T v, ∀ m, ¬ T.IsAnc c (e m : V) → D c m = 0 :=
      fun c hc => (hD c hc).2.1
    refine ⟨fun m => ∑ c ∈ children T v, D c m, fun m => Finset.sum_nonneg fun c hc => (hD c hc).1 m,
      fun m hm => Finset.sum_eq_zero fun c hc => (hD c hc).2.1 m fun h => hm (isAnc_of_child T hc h),
      ?_, fun u hu => ?_⟩
    · rw [smass_inner T e _ hch]
      rw [Finset.sum_congr rfl fun c hc => smass_pieces T e v D hDs hc (isAnc_refl T c)]
      rw [Finset.sum_congr rfl fun c hc => (hD c hc).2.2.1, ← Finset.mul_sum, ← hA,
        div_mul_cancel₀ ε hApos.ne']
    · by_cases huv : u = v
      · subst huv
        have hv : subtreeMass T e (fun m => ∑ c ∈ children T u, D c m) u = ε := by
          rw [smass_inner T e _ hch]
          rw [Finset.sum_congr rfl fun c hc => smass_pieces T e u D hDs hc (isAnc_refl T c)]
          rw [Finset.sum_congr rfl fun c hc => (hD c hc).2.2.1, ← Finset.mul_sum, ← hA,
            div_mul_cancel₀ ε hApos.ne']
        rw [hv]; exact ⟨hε0, hε⟩
      · obtain ⟨c, hc, hcu⟩ := exists_child T hu huv
        rw [smass_pieces T e v D hDs hc hcu]
        exact (hD c hc).2.2.2 u hcu

end K17428


/-! D6b (17428d40, relay 4): the CAPPED BETWEEN lemma (design D6', plan file). Given a valid
fractional state `y` (`0 ≤ y ≤ 1`) and a superadditive node-mass target `Z` (expected quotas, unused
quota parked at the node, leaves may exceed one) with `Z root ≤ ∑ y` and `Z (e r) ≥ 1`, there is a
valid state `y'` with the same total, `y' r = 1`, whose subtree masses lie between those of `y` and
`Z` at every node. Proof: greedy chain extraction along the ancestors of `r` (`chain`), using the
source extraction `extract` (D6a) in the sibling subtrees. Needs D3d, D3f (leaf_coe_inj), D2, D6a. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem smass_add (x y : M → ℝ) (u : V) :
    subtreeMass T e (fun m => x m + y m) u = subtreeMass T e x u + subtreeMass T e y u := by
  classical
  unfold subtreeMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem smass_sub (x y : M → ℝ) (u : V) :
    subtreeMass T e (fun m => x m - y m) u = subtreeMass T e x u - subtreeMass T e y u := by
  classical
  unfold subtreeMass
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem smass_supp (x : M → ℝ) (u : V) (h : ∀ m, T.IsAnc u (e m : V) → x m = 0) :
    subtreeMass T e x u = 0 := by
  classical
  unfold subtreeMass
  refine Finset.sum_eq_zero fun m _ => ?_
  split_ifs with hm
  · exact h m hm
  · rfl

theorem smass_leaf (x : M → ℝ) (m : M) : subtreeMass T e x (e m : V) = x m := by
  classical
  unfold subtreeMass
  rw [Finset.sum_eq_single m]
  · rw [if_pos (isAnc_refl T _)]
  · intro b _ hb
    rw [if_neg]
    intro h; exact hb (leaf_coe_inj T e (anc_leaf T e h))
  · intro h; exact absurd (Finset.mem_univ m) h

theorem smass_root (x : M → ℝ) : subtreeMass T e x T.root = ∑ m, x m := by
  classical
  unfold subtreeMass
  exact Finset.sum_congr rfl fun m _ => if_pos (isAnc_root T _)

theorem bet_up {Y Z g : ℝ} (h0 : 0 ≤ g) (h1 : g ≤ max 0 (Z - Y)) :
    |Y + g - Y| + |Y + g - Z| = |Y - Z| := by
  rcases le_or_gt (Z - Y) 0 with h | h
  · rw [max_eq_left h] at h1
    have : g = 0 := le_antisymm h1 h0
    subst this; simp
  · rw [max_eq_right h.le] at h1
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Y + g - Y), abs_of_nonpos (by linarith : Y + g - Z ≤ 0),
      abs_of_neg (by linarith : Y - Z < 0)]
    ring

theorem bet_down {Y Z D : ℝ} (h0 : 0 ≤ D) (h1 : D ≤ max 0 (Y - Z)) :
    |Y - D - Y| + |Y - D - Z| = |Y - Z| := by
  rcases le_or_gt (Y - Z) 0 with h | h
  · rw [max_eq_left h] at h1
    have : D = 0 := le_antisymm h1 h0
    subst this; simp
  · rw [max_eq_right h.le] at h1
    rw [abs_of_nonpos (by linarith : Y - D - Y ≤ 0), abs_of_nonneg (by linarith : (0:ℝ) ≤ Y - D - Z),
      abs_of_pos (by linarith : 0 < Y - Z)]
    ring

omit [Fintype V] in
theorem sum_split_at {s : Finset V} {v : V} (hv : v ∈ s) (f : V → ℝ) :
    ∑ c ∈ s, f c = f v + ∑ c ∈ s, (if c = v then 0 else f c) := by
  rw [← Finset.add_sum_erase s f hv]
  congr 1
  rw [← Finset.add_sum_erase s _ hv, if_pos rfl, zero_add]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [if_neg (Finset.ne_of_mem_erase hc)]

open Classical in
/-- Greedy chain extraction along the ancestors `parent^[j] (e r)` of the requested leaf. -/
theorem chain (y : M → ℝ) (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (Z : V → ℝ)
    (hZ : ∀ v, ∑ c ∈ children T v, Z c ≤ Z v) (r : M) (hr : 1 ≤ Z (e r)) :
    ∀ j, j ≤ T.depth (e r : V) → ∃ d : M → ℝ, (∀ m, 0 ≤ d m) ∧ (∀ m, d m ≤ y m) ∧ d r = 0 ∧
      (∀ m, ¬ T.IsAnc (T.parent^[j] (e r : V)) (e m : V) → d m = 0) ∧
      0 ≤ (1 - y r) - subtreeMass T e d (T.parent^[j] (e r : V)) ∧
      (1 - y r) - subtreeMass T e d (T.parent^[j] (e r : V)) ≤
        max 0 (Z (T.parent^[j] (e r : V)) - subtreeMass T e y (T.parent^[j] (e r : V))) ∧
      ∀ u, T.IsAnc (T.parent^[j] (e r : V)) u →
        |(subtreeMass T e y u + (if T.IsAnc u (e r : V) then 1 - y r else 0) -
            subtreeMass T e d u) - subtreeMass T e y u| +
        |(subtreeMass T e y u + (if T.IsAnc u (e r : V) then 1 - y r else 0) -
            subtreeMass T e d u) - Z u| = |subtreeMass T e y u - Z u| := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => 0, fun _ => le_rfl, hy0, rfl, fun _ _ => rfl, ?_, ?_, fun u hu => ?_⟩
    · simp only [Function.iterate_zero, id_eq]; rw [smass_zero]; linarith [hy1 r]
    · simp only [Function.iterate_zero, id_eq]; rw [smass_zero, smass_leaf]
      exact le_max_of_le_right (by linarith)
    · simp only [Function.iterate_zero, id_eq] at hu
      rw [anc_leaf T e hu, smass_zero, smass_leaf, if_pos (isAnc_refl T _), sub_zero]
      exact bet_up (by linarith [hy1 r]) (le_max_of_le_right (by linarith))
  | succ j ih =>
    intro hj
    obtain ⟨d, hd0, hdy, hdr, hds, hG0, hG1, hB⟩ := ih (by omega)
    have hw : T.parent^[j + 1] (e r : V) = T.parent (T.parent^[j] (e r : V)) :=
      Function.iterate_succ_apply' _ _ _
    rw [hw]
    set v := T.parent^[j] (e r : V) with hvdef
    have hvr : v ≠ T.root := by
      intro h
      have h1 := depth_iter T (e r : V) j
      rw [← hvdef, h, T.depth_root] at h1
      omega
    have hvanc : T.IsAnc v (e r : V) := ⟨j, rfl⟩
    set w := T.parent v with hwdef
    have hvw : v ∈ children T w := (mem_children T).2 ⟨hvr, rfl⟩
    have hwv : T.IsAnc w v := isAnc_parent_self T v
    have hwanc : T.IsAnc w (e r : V) := isAnc_trans T hwv hvanc
    have hwch : children T w ≠ ∅ := by
      intro h; rw [h] at hvw; exact Finset.notMem_empty v hvw
    set δ := 1 - y r with hδ
    set G := δ - subtreeMass T e d v with hG
    set a : V → ℝ := fun c => max 0 (subtreeMass T e y c - Z c) with ha
    set S := ∑ c ∈ children T w, (if c = v then 0 else a c) with hS
    have ha0 : ∀ c, 0 ≤ a c := fun c => le_max_left _ _
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => by split_ifs; exacts [le_rfl, ha0 c]
    set X := min G S with hX
    have hX0 : 0 ≤ X := le_min hG0 hS0
    have hXc : ∀ c ∈ children T w, ∃ D : M → ℝ, (∀ m, 0 ≤ D m) ∧
        (∀ m, ¬ T.IsAnc c (e m : V) → D m = 0) ∧
        subtreeMass T e D c = (if c = v then 0 else X / S * a c) ∧
        ∀ u, T.IsAnc c u → 0 ≤ subtreeMass T e D u ∧
          subtreeMass T e D u ≤ max 0 (subtreeMass T e y u - Z u) := by
      intro c _
      refine extract T e y Z hZ c _ ?_ ?_
      · split_ifs
        · exact le_rfl
        · exact mul_nonneg (div_nonneg hX0 hS0) (ha0 c)
      · split_ifs
        · exact le_max_left _ _
        · have hq : X / S ≤ 1 := by
            rcases eq_or_lt_of_le hS0 with h | h
            · rw [← h, div_zero]; exact zero_le_one
            · exact (div_le_one h).2 (min_le_right _ _)
          have : X / S * a c ≤ 1 * a c := mul_le_mul_of_nonneg_right hq (ha0 c)
          rw [one_mul] at this; exact this
    choose! D' hD' using hXc
    set E : V → M → ℝ := fun c m => if c = v then 0 else D' c m with hE
    have hE0 : ∀ c ∈ children T w, ∀ m, 0 ≤ E c m := fun c hc m => by
      simp only [hE]; split_ifs; exacts [le_rfl, (hD' c hc).1 m]
    have hEs : ∀ c ∈ children T w, ∀ m, ¬ T.IsAnc c (e m : V) → E c m = 0 := fun c hc m hm => by
      simp only [hE]; split_ifs; exacts [rfl, (hD' c hc).2.1 m hm]
    have hEv : ∀ c ∈ children T w, ∀ m, T.IsAnc v (e m : V) → E c m = 0 := fun c hc m hm => by
      by_cases hcv : c = v
      · simp [hE, hcv]
      · exact hEs c hc m fun h => hcv (child_unique T hc hvw h hm)
    set P : M → ℝ := fun m => ∑ c ∈ children T w, E c m with hP
    have hPv : ∀ m, T.IsAnc v (e m : V) → P m = 0 := fun m hm =>
      Finset.sum_eq_zero fun c hc => hEv c hc m hm
    have hPu_v : ∀ u, T.IsAnc v u → subtreeMass T e P u = 0 := fun u hu =>
      smass_supp T e P u fun m hm => hPv m (isAnc_trans T hu hm)
    have hPu_c : ∀ c ∈ children T w, c ≠ v → ∀ u, T.IsAnc c u →
        subtreeMass T e P u = subtreeMass T e (D' c) u := by
      intro c hc hcv u hu
      rw [smass_pieces T e w E hEs hc hu]
      simp only [hE, if_neg hcv]
    have hdu_c : ∀ c ∈ children T w, c ≠ v → ∀ u, T.IsAnc c u → subtreeMass T e d u = 0 := by
      intro c hc hcv u hu
      refine smass_supp T e d u fun m hm => hds m fun h => hcv ?_
      exact child_unique T hc hvw (isAnc_trans T hu hm) h
    set d' : M → ℝ := fun m => d m + P m with hd'
    have hsd' : ∀ u, subtreeMass T e d' u = subtreeMass T e d u + subtreeMass T e P u := fun u =>
      smass_add T e d P u
    -- mass of `d'` at `w`
    have hsum_X : ∑ c ∈ children T w, (if c = v then 0 else X / S * a c) = X := by
      have : ∑ c ∈ children T w, (if c = v then 0 else X / S * a c) = X / S * S := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs <;> simp
      rw [this]
      rcases eq_or_lt_of_le hS0 with h | h
      · rw [← h, mul_zero]
        have : X ≤ 0 := by rw [hX, ← h]; exact min_le_right _ _
        linarith
      · exact div_mul_cancel₀ X h.ne'
    have hdw : subtreeMass T e d w = subtreeMass T e d v := by
      rw [smass_inner T e d hwch, sum_split_at hvw]
      rw [Finset.sum_eq_zero fun c hc => by
        split_ifs with hcv
        · rfl
        · exact hdu_c c hc hcv c (isAnc_refl T c), add_zero]
    have hPw : subtreeMass T e P w = X := by
      rw [smass_inner T e P hwch, ← hsum_X]
      refine Finset.sum_congr rfl fun c hc => ?_
      split_ifs with hcv
      · rw [hcv]; exact hPu_v v (isAnc_refl T v)
      · rw [hPu_c c hc hcv c (isAnc_refl T c), (hD' c hc).2.2.1, if_neg hcv]
    have hd'w : subtreeMass T e d' w = subtreeMass T e d v + X := by
      rw [hsd', hdw, hPw]
    -- `Y w`, `Z w` against the siblings
    have hYw : subtreeMass T e y w = subtreeMass T e y v +
        ∑ c ∈ children T w, (if c = v then 0 else subtreeMass T e y c) := by
      rw [smass_inner T e y hwch, sum_split_at hvw]
    have hZw : Z v + ∑ c ∈ children T w, (if c = v then 0 else Z c) ≤ Z w := by
      have := hZ w; rwa [sum_split_at hvw] at this
    have hSge : ∑ c ∈ children T w, (if c = v then 0 else subtreeMass T e y c) -
        ∑ c ∈ children T w, (if c = v then 0 else Z c) ≤ S := by
      rw [← Finset.sum_sub_distrib, hS]
      refine Finset.sum_le_sum fun c _ => ?_
      split_ifs
      · simp
      · exact le_max_right _ _
    refine ⟨d', fun m => add_nonneg (hd0 m) (Finset.sum_nonneg fun c hc => hE0 c hc m), fun m => ?_,
      ?_, fun m hm => ?_, ?_, ?_, fun u hu => ?_⟩
    · -- `d' ≤ y`
      show d m + P m ≤ y m
      by_cases hmv : T.IsAnc v (e m : V)
      · rw [hPv m hmv, add_zero]; exact hdy m
      · rw [hds m hmv, zero_add]
        by_cases hex : ∃ c ∈ children T w, c ≠ v ∧ T.IsAnc c (e m : V)
        · obtain ⟨c, hc, hcv, hcm⟩ := hex
          have h1 : P m = subtreeMass T e P (e m : V) := (smass_leaf T e P m).symm
          rw [h1, hPu_c c hc hcv _ hcm, smass_leaf]
          have h2 := ((hD' c hc).2.2.2 (e m : V) hcm).2
          rw [smass_leaf, smass_leaf] at h2
          have h3 := Z_nonneg_leaf T e Z hZ m
          refine h2.trans (max_le (hy0 m) ?_)
          linarith
        · have : P m = 0 := Finset.sum_eq_zero fun c hc => by
            by_cases hcv : c = v
            · simp [hE, hcv]
            · exact hEs c hc m fun h => hex ⟨c, hc, hcv, h⟩
          rw [this]; exact hy0 m
    · show d r + P r = 0
      rw [hdr, hPv r hvanc, add_zero]
    · show d m + P m = 0
      have hmv : ¬ T.IsAnc v (e m : V) := fun h => hm (isAnc_trans T hwv h)
      rw [hds m hmv, zero_add]
      exact Finset.sum_eq_zero fun c hc => hEs c hc m fun h => hm (isAnc_of_child T hc h)
    · rw [hd'w]; linarith [min_le_left G S]
    · rw [hd'w]
      by_cases hGS : G ≤ S
      · have : X = G := min_eq_left hGS
        have : δ - (subtreeMass T e d v + X) = 0 := by rw [this, hG]; ring
        rw [this]; exact le_max_left _ _
      · push Not at hGS
        have hXS : X = S := min_eq_right hGS.le
        have hGpos : 0 < G := lt_of_le_of_lt hS0 hGS
        have hGle : G ≤ Z v - subtreeMass T e y v := by
          rcases le_max_iff.1 hG1 with h | h
          · linarith
          · exact h
        refine le_max_of_le_right ?_
        rw [hXS, hYw]
        have : δ - (subtreeMass T e d v + S) = G - S := by rw [hG]; ring
        rw [this]
        linarith
    · -- betweenness in `T(w)`
      by_cases huw : u = w
      · rw [huw, if_pos hwanc, hd'w]
        have : subtreeMass T e y w + δ - (subtreeMass T e d v + X) =
            subtreeMass T e y w + (G - X) := by rw [hG]; ring
        rw [this]
        refine bet_up (by linarith [min_le_left G S]) ?_
        by_cases hGS : G ≤ S
        · have : G - X = 0 := by rw [show X = G from min_eq_left hGS]; ring
          rw [this]; exact le_max_left _ _
        · push Not at hGS
          have hXS : X = S := min_eq_right hGS.le
          have hGpos : 0 < G := lt_of_le_of_lt hS0 hGS
          have hGle : G ≤ Z v - subtreeMass T e y v := by
            rcases le_max_iff.1 hG1 with h | h
            · linarith
            · exact h
          refine le_max_of_le_right ?_
          rw [hXS, hYw]
          linarith
      · obtain ⟨c, hc, hcu⟩ := exists_child T hu huw
        by_cases hcv : c = v
        · subst hcv
          rw [hsd', hPu_v u hcu, add_zero]
          exact hB u hcu
        · have hnr : ¬ T.IsAnc u (e r : V) := fun h =>
            hcv (child_unique T hc hvw (isAnc_trans T hcu h) hvanc)
          rw [if_neg hnr, hsd', hdu_c c hc hcv u hcu, hPu_c c hc hcv u hcu, add_zero, zero_add]
          exact bet_down ((hD' c hc).2.2.2 u hcu).1 ((hD' c hc).2.2.2 u hcu).2

/-- **CAPPED BETWEEN (D6').** -/
theorem capped_between (y : M → ℝ) (hy0 : ∀ m, 0 ≤ y m) (hy1 : ∀ m, y m ≤ 1) (Z : V → ℝ)
    (hZ : ∀ v, ∑ c ∈ children T v, Z c ≤ Z v) (hroot : Z T.root ≤ ∑ m, y m) (r : M)
    (hr : 1 ≤ Z (e r)) :
    ∃ y' : M → ℝ, (∀ m, 0 ≤ y' m ∧ y' m ≤ 1) ∧ ∑ m, y' m = ∑ m, y m ∧ y' r = 1 ∧
      ∀ u, |subtreeMass T e y' u - subtreeMass T e y u| + |subtreeMass T e y' u - Z u| =
        |subtreeMass T e y u - Z u| := by
  classical
  obtain ⟨d, hd0, hdy, hdr, _, hG0, hG1, hB⟩ :=
    chain T e y hy0 hy1 Z hZ r hr (T.depth (e r : V)) le_rfl
  have hrt : T.parent^[T.depth (e r : V)] (e r : V) = T.root := by
    apply eq_root_of_depth; rw [depth_iter]; omega
  rw [hrt] at hG0 hG1 hB
  rw [smass_root, smass_root] at hG1
  rw [smass_root] at hG0
  have hG : ∑ m, d m = 1 - y r := by
    have : max 0 (Z T.root - ∑ m, y m) = 0 := max_eq_left (by linarith)
    rw [this] at hG1; linarith
  refine ⟨fun m => y m + (if m = r then 1 - y r else 0) - d m, fun m => ?_, ?_, ?_, fun u => ?_⟩
  · by_cases hm : m = r
    · subst hm; simp [hdr]
    · simp only [if_neg hm, add_zero]
      exact ⟨by linarith [hdy m], by linarith [hd0 m, hy1 m]⟩
  · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hG, Finset.sum_ite_eq']; simp
  · simp [hdr]
  · have h := hB u (isAnc_root T u)
    have hs : subtreeMass T e (fun m => y m + (if m = r then 1 - y r else 0) - d m) u =
        subtreeMass T e y u + (if T.IsAnc u (e r : V) then 1 - y r else 0) - subtreeMass T e d u := by
      rw [smass_sub T e (fun m => y m + (if m = r then 1 - y r else 0)) d u,
        smass_add T e y (fun m => if m = r then 1 - y r else 0) u, smass_single]
    rw [hs]; exact h

end K17428


/-! D6c (17428d40, relay 5): potential/telescoping for the capping projection (design D6').
`Phi y Z = sum_{v != root} W v |y_v - Z_v|`. If every capped step keeps `y_t` between `y_{t-1}`
and `Z_t` (conclusion of `capped_between`), then the total movement of the `y`'s is at most
`Phi_0 + sum_t zcost Z_{t-1} Z_t`, i.e. the projection never costs more than the quota
trajectory `Z` itself. Needs nothing beyond the Definitions. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

/-- The capping potential: weighted distance of the subtree masses of `y` from the targets `Z`. -/
noncomputable def Phi (y : M → ℝ) (Z : V → ℝ) : ℝ :=
  ∑ v ∈ univ.filter (fun v => v ≠ T.root), T.W v * |subtreeMass T e y v - Z v|

/-- Weighted movement of a target vector (paid by the quota trajectory). -/
noncomputable def zcost (Z Z' : V → ℝ) : ℝ :=
  ∑ v ∈ univ.filter (fun v => v ≠ T.root), T.W v * |Z' v - Z v|

theorem Phi_nonneg (y : M → ℝ) (Z : V → ℝ) : 0 ≤ Phi T e y Z := by
  unfold Phi
  refine Finset.sum_nonneg fun v hv => ?_
  have hv' : v ≠ T.root := (Finset.mem_filter.1 hv).2
  exact mul_nonneg (le_of_lt (T.W_pos v hv')) (abs_nonneg _)

theorem zcost_nonneg (Z Z' : V → ℝ) : 0 ≤ zcost T Z Z' := by
  unfold zcost
  refine Finset.sum_nonneg fun v hv => ?_
  have hv' : v ≠ T.root := (Finset.mem_filter.1 hv).2
  exact mul_nonneg (le_of_lt (T.W_pos v hv')) (abs_nonneg _)

/-- One capped step: movement plus the new potential equals the potential of the old state
against the new targets. -/
theorem Phi_step (y y' : M → ℝ) (Z : V → ℝ)
    (hb : ∀ u, |subtreeMass T e y' u - subtreeMass T e y u| + |subtreeMass T e y' u - Z u| =
        |subtreeMass T e y u - Z u|) :
    fracMoveCost T e y y' + Phi T e y' Z = Phi T e y Z := by
  unfold fracMoveCost Phi
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← mul_add, hb v]

/-- Changing the targets changes the potential by at most `zcost`. -/
theorem Phi_retarget (y : M → ℝ) (Z Z' : V → ℝ) :
    Phi T e y Z' ≤ Phi T e y Z + zcost T Z Z' := by
  unfold Phi zcost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v hv => ?_
  have hv' : v ≠ T.root := (Finset.mem_filter.1 hv).2
  have hW : 0 ≤ T.W v := le_of_lt (T.W_pos v hv')
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hW
  have h := abs_sub_le (subtreeMass T e y v) (Z v) (Z' v)
  have h2 : |Z v - Z' v| = |Z' v - Z v| := abs_sub_comm _ _
  linarith

/-- Telescoping: a capped trajectory `y` costs at most the initial potential plus the target
movement. -/
theorem capped_telescope (y : ℕ → M → ℝ) (Z : ℕ → V → ℝ)
    (hstep : ∀ t, fracMoveCost T e (y t) (y (t + 1)) + Phi T e (y (t + 1)) (Z (t + 1)) =
        Phi T e (y t) (Z (t + 1))) (n : ℕ) :
    ∑ t ∈ range n, fracMoveCost T e (y t) (y (t + 1)) + Phi T e (y n) (Z n) ≤
      Phi T e (y 0) (Z 0) + ∑ t ∈ range n, zcost T (Z t) (Z (t + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 := hstep n
    have h2 := Phi_retarget T e (y n) (Z n) (Z (n + 1))
    linarith

theorem capped_cost_le (y : ℕ → M → ℝ) (Z : ℕ → V → ℝ)
    (hstep : ∀ t, fracMoveCost T e (y t) (y (t + 1)) + Phi T e (y (t + 1)) (Z (t + 1)) =
        Phi T e (y t) (Z (t + 1))) (n : ℕ) :
    ∑ t ∈ range n, fracMoveCost T e (y t) (y (t + 1)) ≤
      Phi T e (y 0) (Z 0) + ∑ t ∈ range n, zcost T (Z t) (Z (t + 1)) := by
  have h := capped_telescope T e y Z hstep n
  have h0 := Phi_nonneg T e (y n) (Z n)
  linarith

theorem Phi_self (y : M → ℝ) : Phi T e y (subtreeMass T e y) = 0 := by
  unfold Phi; simp

end K17428


/-! D5e (17428d40, relay 6): Theorem 31 for quota histories that may DROP TO ZERO at times
whose request lies outside `T(p)` (child histories of the ensemble do; thm31 needs `κ >= 1`).
Part 1 (`Qopt_cut`): `Qopt(κ) <= Qopt(max 1 κ) + D g(κ)` (cut a `max 1 κ` trajectory to `0` on
the zero blocks; each block boundary costs one unit path `<= D`). Needs D3a-D5d. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem unit_state (S : Set M) (x : M → ℤ) (h0 : ∀ m, 0 ≤ x m) (hS : ∀ m, m ∉ S → x m = 0)
    (h1 : ∑ m, x m = 1) : ∃ m ∈ S, x = fun m' => if m' = m then 1 else 0 := by
  obtain ⟨m, hm⟩ : ∃ m, 0 < x m := by
    by_contra hne
    push_neg at hne
    have : ∑ m, x m = 0 := Finset.sum_eq_zero fun m _ => le_antisymm (hne m) (h0 m)
    omega
  have hsplit := Finset.add_sum_erase univ x (Finset.mem_univ m)
  have hrest : 0 ≤ ∑ m' ∈ univ.erase m, x m' := Finset.sum_nonneg fun m' _ => h0 m'
  have hxm : x m = 1 := by omega
  have hz : ∑ m' ∈ univ.erase m, x m' = 0 := by omega
  refine ⟨m, ?_, ?_⟩
  · by_contra hn; have := hS m hn; omega
  · funext m'
    by_cases hm' : m' = m
    · subst hm'; simp [hxm]
    · rw [if_neg hm']
      have := Finset.single_le_sum (f := x) (fun m'' _ => h0 m'')
        (Finset.mem_erase.mpr ⟨hm', Finset.mem_univ m'⟩)
      have := h0 m'
      omega

theorem dpath_nonneg (p : V) (m : M) : 0 ≤ dpath T e p m := by
  unfold dpath
  exact Finset.sum_nonneg fun v hv => by split_ifs; exact W_nonneg_inner T p v hv; exact le_rfl

theorem ccost_unit_zero (p : V) (S : Set M) (x : M → ℤ) (h0 : ∀ m, 0 ≤ x m)
    (hS : ∀ m, m ∉ S → x m = 0) (h1 : ∑ m, x m = 1) (D : ℝ)
    (hD : ∀ m ∈ S, dpath T e p m ≤ D) :
    ccost T e p x (fun _ => 0) ≤ D ∧ 0 ≤ D := by
  obtain ⟨m, hmS, rfl⟩ := unit_state S x h0 hS h1
  have h := ccost_add_unit T e p (fun _ => 0) m
  simp only [zero_add] at h
  rw [ccost_comm, h]
  exact ⟨hD m hmS, (dpath_nonneg T e p m).trans (hD m hmS)⟩

open Classical in
/-- Cut a trajectory to the empty state on the zero blocks of `κ`. -/
noncomputable def cutT (κ : ℕ → ℕ) (c : ℕ → M → ℤ) : ℕ → M → ℤ :=
  fun s => if κ s = 0 then fun _ => 0 else c s

theorem Qopt_cut (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (hst0 : ∀ m, st 0 m = 0) (D : ℝ)
    (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D) (κ : ℕ → ℕ)
    (hfeas : ∀ s, 1 ≤ s → s ≤ H → r s ∈ Sp T e p → 1 ≤ κ s) :
    Qopt T e p r H st κ ≤ Qopt T e p r H st (fun s => max 1 (κ s)) + D * gsum H κ := by
  classical
  have hst1 : ∑ m, st 1 m = 1 := by
    have := ((hN.props 1).2.2); rw [this]; simp [hst0]
  have hst0s : ∑ m, st 0 m = 0 := by simp [hst0]
  have key : Qopt T e p r H st κ - D * gsum H κ ≤ Qopt T e p r H st (fun s => max 1 (κ s)) := by
    refine le_Qopt T e _ (QTraj_nonempty T e p r H st L hN _ fun t _ => le_max_left _ _)
      fun c hc => ?_
    obtain ⟨hc0, hcn, hcS, hcsum, hcr⟩ := hc
    beta_reduce at hc0 hcsum
    -- the cut trajectory is a quota trajectory for κ
    have hq : QTraj T e p r H st κ (cutT κ c) := by
      refine ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
        fun s h1 hs hr => ?_⟩
      · unfold cutT
        by_cases h : κ 0 = 0
        · rw [if_pos h, h, hst0]
        · rw [if_neg h, hc0 m, show max 1 (κ 0) = κ 0 by omega]
      · unfold cutT; split_ifs
        · exact le_rfl
        · exact hcn s hs m
      · unfold cutT; split_ifs
        · rfl
        · exact hcS s hs m hm
      · unfold cutT
        by_cases h : κ s = 0
        · rw [if_pos h, h, hst0s]; simp
        · rw [if_neg h, hcsum s hs, show max 1 (κ s) = κ s by omega]
      · have hk := hfeas s h1 hs hr
        unfold cutT
        rw [if_neg (by omega)]
        exact hcr s h1 hs hr
    -- unit states on the zero blocks
    have hunit : ∀ s ≤ H, κ s = 0 → ccost T e p (c s) (fun _ => 0) ≤ D ∧ 0 ≤ D := by
      intro s hs h
      refine ccost_unit_zero T e p (Sp T e p) (c s) (hcn s hs) (hcS s hs) ?_ D hD
      rw [hcsum s hs, h]; simpa using hst1
    have hstep : ∀ s ∈ range H, ccost T e p (cutT κ c s) (cutT κ c (s + 1)) ≤
        ccost T e p (c s) (c (s + 1)) + D * |((κ (s + 1) : ℝ) - κ s)| := by
      intro s hs
      have hs' := Finset.mem_range.mp hs
      unfold cutT
      by_cases ha : κ s = 0 <;> by_cases hb : κ (s + 1) = 0
      · rw [if_pos ha, if_pos hb]
        have : ccost T e p (fun _ => (0 : ℤ)) (fun _ => 0) = 0 := by
          unfold ccost; simp
        rw [this]
        have := ccost_nonneg T e p (c s) (c (s + 1))
        have := (hunit s hs'.le ha).2
        have : 0 ≤ D * |((κ (s + 1) : ℝ) - κ s)| := mul_nonneg this (abs_nonneg _)
        linarith
      · rw [if_pos ha, if_neg hb]
        obtain ⟨hu, hD0⟩ := hunit s hs'.le ha
        have tr := ccost_triangle T e p (fun _ => 0) (c s) (c (s + 1))
        rw [ccost_comm T e p (fun _ => 0) (c s)] at tr
        have h1 : (1 : ℝ) ≤ |((κ (s + 1) : ℝ) - κ s)| := by
          rw [ha, Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb
        have := mul_le_mul_of_nonneg_left h1 hD0
        linarith
      · rw [if_neg ha, if_pos hb]
        obtain ⟨hu, hD0⟩ := hunit (s + 1) hs' hb
        have tr := ccost_triangle T e p (c s) (c (s + 1)) (fun _ => 0)
        have h1 : (1 : ℝ) ≤ |((κ (s + 1) : ℝ) - κ s)| := by
          rw [hb, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
        have := mul_le_mul_of_nonneg_left h1 hD0
        linarith
      · rw [if_neg ha, if_neg hb]
        have : 0 ≤ D * |((κ (s + 1) : ℝ) - κ s)| ∨ True := Or.inr trivial
        by_cases hD0 : 0 ≤ D
        · have := mul_nonneg hD0 (abs_nonneg ((κ (s + 1) : ℝ) - κ s))
          linarith
        · -- D < 0 is impossible once some leaf lies below p; here it is not needed:
          -- |κ(s+1) - κ s| may be positive, so bound via the general step instead.
          have hle : D * |((κ (s + 1) : ℝ) - κ s)| ≤ 0 ∨ 0 ≤ D * |((κ (s + 1) : ℝ) - κ s)| :=
            le_total _ _
          exact absurd (show 0 ≤ D by
            have := hcsum s hs'.le
            obtain ⟨m, hm⟩ : ∃ m, 0 < c s m := by
              by_contra hne; push_neg at hne
              have hz : ∑ m, c s m = 0 := Finset.sum_eq_zero fun m _ => le_antisymm (hne m) (hcn s hs'.le m)
              have hp := (hN.props (max 1 (κ s))).2.2
              rw [hst0s] at hp
              omega
            have hmS : m ∈ Sp T e p := by
              by_contra hn; have := hcS s hs'.le m hn; omega
            exact (dpath_nonneg T e p m).trans (hD m hmS)) hD0
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hQ := Qopt_le T e hq
    unfold qcost at hQ ⊢
    unfold gsum
    linarith
  linarith

end K17428


/-! D5f (17428d40, relay 7): D5e parts 2-5. Theorem 31 for feasible quota histories that may
drop to zero (`thm31z`): lift a `κ` trajectory to `max 1 κ` (one server parked at `st 1` on the
zero blocks), `Hsum κ = Hsum (max 1 κ)`, `gsum (max 1 κ) ≤ gsum κ`. Needs D3a-D5e. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

theorem zero_of_sum_zero (x : M → ℤ) (h0 : ∀ m, 0 ≤ x m) (hs : ∑ m, x m = 0) :
    x = fun _ => 0 := by
  funext m
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => h0 m)).1 hs m (Finset.mem_univ m)

theorem Fopt_zero_state (S : Set M) (r : ℕ → M) (H : ℕ) :
    Fopt T e S r H (fun _ => 0) = 0 := by
  by_cases hne : ∃ c, ITraj S r H (fun _ => 0) c
  · obtain ⟨c, hc⟩ := hne
    have h1 := Fopt_le T e hc
    have hz : ∀ s ≤ H, c s = fun _ => 0 := fun s hs =>
      zero_of_sum_zero (c s) (hc.2.1 s hs) (by rw [hc.2.2.2.1 s hs]; simp)
    have h2 : tcost T e H c = 0 := by
      unfold tcost
      refine Finset.sum_eq_zero fun t ht => ?_
      have ht' := Finset.mem_range.1 ht
      rw [hz t ht'.le, hz (t + 1) ht']
      exact fracMoveCost_self T e _
    linarith [Fopt_nonneg T e S r H (fun _ => 0)]
  · push_neg at hne
    unfold Fopt
    have : {c | ITraj S r H (fun _ => (0 : ℤ)) c} = ∅ := by
      ext c; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hne c
    rw [this, Set.image_empty, Real.sInf_empty]

theorem gsum_max_le (H : ℕ) (κ : ℕ → ℕ) : gsum H (fun s => max 1 (κ s)) ≤ gsum H κ := by
  unfold gsum
  refine Finset.sum_le_sum fun s _ => ?_
  push_cast
  rw [max_comm (1 : ℝ) (κ (s + 1) : ℝ), max_comm (1 : ℝ) (κ s : ℝ)]
  exact abs_max_sub_max_le_abs _ _ _

theorem Hsum_max (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (hst0 : ∀ m, st 0 m = 0) (κ : ℕ → ℕ)
    (hfeas : ∀ s, 1 ≤ s → s ≤ H → r s ∈ Sp T e p → 1 ≤ κ s) :
    Hsum T e p r H st (fun s => max 1 (κ s)) = Hsum T e p r H st κ := by
  have hst0' : st 0 = fun _ => 0 := funext hst0
  unfold Hsum
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  unfold hval
  by_cases hz : κ (t + 1) = 0
  · have hm : max 1 (κ (t + 1)) = 1 := by omega
    simp only [hm, Nat.add_sub_cancel]
    rw [hz, hst0']
    simp only [Fopt_zero_state]
    have hr : r (t + 1) ∉ Sp T e p := fun hr => by
      have := hfeas (t + 1) (by omega) (by omega) hr; omega
    have hp := hN.props 1
    have hne := ITraj_nonempty (Sp T e p) r t (st 1) hp.1 hp.2.1
      (by rw [hp.2.2]; simp [hst0])
    rw [Fopt_out T e (Sp T e p) r t (st 1) hne hr, sub_self, sub_self]
  · have hm : max 1 (κ (t + 1)) = κ (t + 1) := by omega
    simp only [hm]

open Classical in
/-- Park one server at `st 1` on the zero blocks of `κ`. -/
noncomputable def liftT (st : ℕ → M → ℤ) (κ : ℕ → ℕ) (c : ℕ → M → ℤ) : ℕ → M → ℤ :=
  fun s => if κ s = 0 then st 1 else c s

theorem Qopt_lift (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (hst0 : ∀ m, st 0 m = 0) (D : ℝ)
    (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D) (κ : ℕ → ℕ)
    (hfeas : ∀ s, 1 ≤ s → s ≤ H → r s ∈ Sp T e p → 1 ≤ κ s) :
    Qopt T e p r H st (fun s => max 1 (κ s)) ≤ Qopt T e p r H st κ + D * gsum H κ := by
  classical
  have hst0s : ∑ m, st 0 m = 0 := by simp [hst0]
  have hp1 := hN.props 1
  have hst1 : ∑ m, st 1 m = 1 := by rw [hp1.2.2, hst0s]; simp
  have hD0 : 0 ≤ D := (dpath_nonneg T e p (L 0)).trans (hD _ (hN.2.1 0))
  have hu1 := (ccost_unit_zero T e p (Sp T e p) (st 1) hp1.1 hp1.2.1 hst1 D hD).1
  -- nonemptiness of the κ trajectories (cut a `max 1 κ` trajectory)
  have hne : ∃ c, QTraj T e p r H st κ c := by
    obtain ⟨c, hc0, hcn, hcS, hcsum, hcr⟩ :=
      QTraj_nonempty T e p r H st L hN (fun s => max 1 (κ s)) fun t _ => le_max_left _ _
    beta_reduce at hc0 hcsum
    refine ⟨cutT κ c, fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
      fun s h1 hs hr => ?_⟩
    · unfold cutT
      by_cases h : κ 0 = 0
      · rw [if_pos h, h, hst0]
      · rw [if_neg h, hc0 m, show max 1 (κ 0) = κ 0 by omega]
    · unfold cutT; split_ifs
      · exact le_rfl
      · exact hcn s hs m
    · unfold cutT; split_ifs
      · rfl
      · exact hcS s hs m hm
    · unfold cutT
      by_cases h : κ s = 0
      · rw [if_pos h, h, hst0s]; simp
      · rw [if_neg h, hcsum s hs, show max 1 (κ s) = κ s by omega]
    · have hk := hfeas s h1 hs hr
      unfold cutT
      rw [if_neg (by omega)]
      exact hcr s h1 hs hr
  have key : Qopt T e p r H st (fun s => max 1 (κ s)) - D * gsum H κ ≤ Qopt T e p r H st κ := by
    refine le_Qopt T e _ hne fun c hc => ?_
    obtain ⟨hc0, hcn, hcS, hcsum, hcr⟩ := hc
    have hzero : ∀ s ≤ H, κ s = 0 → c s = fun _ => 0 := fun s hs h =>
      zero_of_sum_zero (c s) (hcn s hs) (by rw [hcsum s hs, h, hst0s])
    have hq : QTraj T e p r H st (fun s => max 1 (κ s)) (liftT st κ c) := by
      refine ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
        fun s h1 hs hr => ?_⟩
      · beta_reduce
        unfold liftT
        by_cases h : κ 0 = 0
        · rw [if_pos h, h, show max 1 0 = 1 from rfl]
        · rw [if_neg h, hc0 m, show max 1 (κ 0) = κ 0 by omega]
      · unfold liftT; split_ifs
        · exact hp1.1 m
        · exact hcn s hs m
      · unfold liftT; split_ifs
        · exact hp1.2.1 m hm
        · exact hcS s hs m hm
      · beta_reduce
        unfold liftT
        by_cases h : κ s = 0
        · rw [if_pos h, h, show max 1 0 = 1 from rfl]
        · rw [if_neg h, hcsum s hs, show max 1 (κ s) = κ s by omega]
      · have hk := hfeas s h1 hs hr
        unfold liftT
        rw [if_neg (by omega)]
        exact hcr s h1 hs hr
    have hstep : ∀ s ∈ range H, ccost T e p (liftT st κ c s) (liftT st κ c (s + 1)) ≤
        ccost T e p (c s) (c (s + 1)) + D * |((κ (s + 1) : ℝ) - κ s)| := by
      intro s hs
      have hs' := Finset.mem_range.mp hs
      have hab := mul_nonneg hD0 (abs_nonneg ((κ (s + 1) : ℝ) - κ s))
      have hcc := ccost_nonneg T e p (c s) (c (s + 1))
      unfold liftT
      by_cases ha : κ s = 0 <;> by_cases hb : κ (s + 1) = 0
      · rw [if_pos ha, if_pos hb, ccost_self]
        linarith
      · rw [if_pos ha, if_neg hb]
        have tr := ccost_triangle T e p (st 1) (c s) (c (s + 1))
        rw [hzero s hs'.le ha] at tr ⊢
        have h1 : (1 : ℝ) ≤ |((κ (s + 1) : ℝ) - κ s)| := by
          rw [ha, Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb
        have := mul_le_mul_of_nonneg_left h1 hD0
        linarith
      · rw [if_neg ha, if_pos hb]
        have tr := ccost_triangle T e p (c s) (c (s + 1)) (st 1)
        rw [hzero (s + 1) hs' hb] at tr ⊢
        rw [ccost_comm T e p (fun _ => 0) (st 1)] at tr
        have h1 : (1 : ℝ) ≤ |((κ (s + 1) : ℝ) - κ s)| := by
          rw [hb, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
        have := mul_le_mul_of_nonneg_left h1 hD0
        linarith
      · rw [if_neg ha, if_neg hb]
        linarith
    have hsum := Finset.sum_le_sum hstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hQ := Qopt_le T e hq
    unfold qcost at hQ ⊢
    unfold gsum
    linarith
  linarith

/-- Theorem 31 for feasible quota histories with zeros (`st 0 = 0`). -/
theorem thm31z (p : V) (r : ℕ → M) (H : ℕ) (st : ℕ → M → ℤ) (L : ℕ → M)
    (hN : Nested (Sp T e p) st L) (hst0 : ∀ m, st 0 m = 0) (D : ℝ)
    (hD : ∀ m ∈ Sp T e p, dpath T e p m ≤ D) (κ : ℕ → ℕ)
    (hfeas : ∀ s, 1 ≤ s → s ≤ H → r s ∈ Sp T e p → 1 ≤ κ s) :
    Hsum T e p r H st κ - 2 * D * gsum H κ ≤ Qopt T e p r H st κ ∧
      Qopt T e p r H st κ ≤ Hsum T e p r H st κ + 2 * D * gsum H κ := by
  have hD0 : 0 ≤ D := (dpath_nonneg T e p (L 0)).trans (hD _ (hN.2.1 0))
  have h31 := thm31 T e p r H st L hN D hD (fun s => max 1 (κ s)) fun t _ => le_max_left _ _
  have hH := Hsum_max T e p r H st L hN hst0 κ hfeas
  have hg := mul_le_mul_of_nonneg_left (gsum_max_le H κ) hD0
  have hcut := Qopt_cut T e p r H st L hN hst0 D hD κ hfeas
  have hlift := Qopt_lift T e p r H st L hN hst0 D hD κ hfeas
  rw [hH] at h31
  constructor
  · have hg0 : 0 ≤ D * gsum H (fun s => max 1 (κ s)) :=
      mul_nonneg hD0 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    linarith [h31.1]
  · linarith [h31.2]

end K17428


/-! D7f (17428d40, relay 6): tree instantiation of the node requests (D7e) at a node `p`:
children indexed by `Fin (children T p).card` (`chv`), the requested child `nloc` (`none`
outside `T(p)`), and the child cost functions `nhf` = D4 differences
`F_t(st_c j) - F_{t-1}(st_c j)` at `max 1 j`, for nested start families `st v` of every vertex.
Results: `nhf_nonneg` (Fopt_le_succ), `nhf_anti` (Fopt_submod), `nhf_out` (Fopt_out): exactly the
hypotheses of `nodeSeq_valid` / `nodeSeq_intCost_split`. Needs D3a-D3h, D4, D5a-D5d, D2. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

variable (T : WTree V) (e : M ≃ T.Leaf)

/-- The `i`-th child of `p`. -/
noncomputable def chv (p : V) (i : Fin (children T p).card) : V :=
  ((children T p).equivFin.symm i : V)

theorem chv_mem (p : V) (i : Fin (children T p).card) : chv T p i ∈ children T p :=
  ((children T p).equivFin.symm i).2

theorem chv_inj (p : V) {i i' : Fin (children T p).card} (h : chv T p i = chv T p i') : i = i' :=
  (children T p).equivFin.symm.injective (Subtype.ext h)

open Classical in
/-- The child of `p` whose subtree contains the request `r t` (`none` if there is none). -/
noncomputable def nloc (p : V) (r : ℕ → M) (t : ℕ) : Option (Fin (children T p).card) :=
  if h : ∃ i : Fin (children T p).card, T.IsAnc (chv T p i) (e (r t) : V) then
    some (Classical.choose h) else none

theorem nloc_some (p : V) (r : ℕ → M) (t : ℕ) (i : Fin (children T p).card)
    (h : nloc T e p r t = some i) : T.IsAnc (chv T p i) (e (r t) : V) := by
  unfold nloc at h
  split_ifs at h with hex
  have h' := Option.some.inj h
  subst h'
  exact Classical.choose_spec hex

theorem nloc_of_anc (p : V) (r : ℕ → M) (t : ℕ) (i : Fin (children T p).card)
    (h : T.IsAnc (chv T p i) (e (r t) : V)) : nloc T e p r t = some i := by
  have hex : ∃ i : Fin (children T p).card, T.IsAnc (chv T p i) (e (r t) : V) := ⟨i, h⟩
  unfold nloc
  rw [dif_pos hex]
  congr 1
  exact chv_inj T p (child_unique T (chv_mem T p _) (chv_mem T p i) (Classical.choose_spec hex) h)

/-- The child cost functions (`h(j)` read at `max 1 j`). -/
noncomputable def nhf (p : V) (r : ℕ → M) (st : V → ℕ → M → ℤ) (i : Fin (children T p).card)
    (t j : ℕ) : ℝ :=
  Fopt T e (Sp T e (chv T p i)) r t (st (chv T p i) (max 1 j)) -
    Fopt T e (Sp T e (chv T p i)) r (t - 1) (st (chv T p i) (max 1 j))

section NodeTree

variable (p : V) (r : ℕ → M) (st : V → ℕ → M → ℤ) (L : V → ℕ → M)

theorem st_ok (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (v : V) (j : ℕ) (hj : 1 ≤ j) :
    (∀ m, 0 ≤ st v j m) ∧ (∀ m, m ∉ Sp T e v → st v j m = 0) ∧ 1 ≤ ∑ m, st v j m := by
  obtain ⟨h0, hS, hsum⟩ := (hN v).props j
  have hz : 0 ≤ ∑ m, st v 0 m := Finset.sum_nonneg fun m _ => ((hN v).props 0).1 m
  refine ⟨h0, hS, ?_⟩
  rw [hsum]
  have : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  linarith

theorem nhf_nonneg (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (i : Fin (children T p).card)
    (t j : ℕ) : 0 ≤ nhf T e p r st i t j := by
  unfold nhf
  cases t with
  | zero => simp
  | succ H =>
    obtain ⟨h0, hS, hpos⟩ := st_ok T e st L hN (chv T p i) (max 1 j) (le_max_left _ _)
    have := Fopt_le_succ T e (Sp T e (chv T p i)) r H (st (chv T p i) (max 1 j))
      (ITraj_nonempty _ r (H + 1) _ h0 hS hpos)
    simp only [Nat.add_sub_cancel]
    linarith

theorem nhf_step (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (i : Fin (children T p).card)
    (t j : ℕ) (hj : 1 ≤ j) : nhf T e p r st i t (j + 1) ≤ nhf T e p r st i t j := by
  unfold nhf
  rw [show max 1 (j + 1) = j + 1 by omega, show max 1 j = j by omega]
  cases t with
  | zero => simp
  | succ H =>
    simp only [Nat.add_sub_cancel]
    obtain ⟨h0, hS, hpos⟩ := st_ok T e st L hN (chv T p i) j hj
    have hq : L (chv T p i) j ∈ Sp T e (chv T p i) := (hN (chv T p i)).2.1 j
    have hsub := Fopt_submod T e (Sp T e (chv T p i)) r H (st (chv T p i) j) (L (chv T p i) j)
      h0 hS hpos hq
    rw [← (hN (chv T p i)).1 j] at hsub
    linarith

theorem nhf_anti (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (i : Fin (children T p).card)
    (t j j' : ℕ) (hj : 1 ≤ j) (hjj : j ≤ j') : nhf T e p r st i t j' ≤ nhf T e p r st i t j := by
  induction j', hjj using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (nhf_step T e p r st L hN i t n (by omega)).trans ih

theorem nhf_out (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (i : Fin (children T p).card)
    (t j : ℕ) (hl : nloc T e p r t ≠ some i) : nhf T e p r st i t j = 0 := by
  unfold nhf
  cases t with
  | zero => simp
  | succ H =>
    simp only [Nat.add_sub_cancel]
    have hr : r (H + 1) ∉ Sp T e (chv T p i) := fun h => hl (nloc_of_anc T e p r _ i h)
    obtain ⟨h0, hS, hpos⟩ := st_ok T e st L hN (chv T p i) (max 1 j) (le_max_left _ _)
    rw [Fopt_out T e _ r H _ (ITraj_nonempty _ r H _ h0 hS hpos) hr]
    ring

end NodeTree

end K17428


/-! D7a (17428d40, relay 5): the QUANTILE COUPLING used by the ensemble (design D7, plan file).
A distribution on `{0, ..., k}` is given by its cumulative vector `c j = P(X < j)` (`cumul`).
The quantile `Q c k u = #{1 <= j <= k : c j < u}` (u uniform on (0,1)) has law `X`;
`int_ind`, `int_Q` (mean), `int_abs_Q_sub` (W1 movement <= sum_j |c j - c' j|), `int_h_Q`
(expected cost of a cost vector). Pure Mathlib. -/

namespace K17428

open Finset MeasureTheory intervalIntegral

/-- Quantile of the distribution with cumulative vector `c` at level `u`. -/
noncomputable def Qf (c : ℕ → ℝ) (k : ℕ) (u : ℝ) : ℕ := ((Icc 1 k).filter (fun j => c j < u)).card

/-- Indicator `1[a < u]` as a real function. -/
noncomputable def ind (a : ℝ) (u : ℝ) : ℝ := if a < u then 1 else 0

theorem Qf_cast (c : ℕ → ℝ) (k : ℕ) (u : ℝ) : (Qf c k u : ℝ) = ∑ j ∈ Icc 1 k, ind (c j) u := by
  unfold Qf ind
  rw [Finset.card_filter]
  push_cast
  rfl

theorem measurable_ind (a : ℝ) : Measurable (ind a) := by
  unfold ind
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

theorem ind_ii (a x y : ℝ) : IntervalIntegrable (ind a) volume x y := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
    (measurable_ind a).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  show ‖ind a u‖ ≤ 1
  unfold ind; split_ifs <;> simp

theorem ii_sum {ι : Type} (s : Finset ι) (f : ι → ℝ → ℝ) (x y : ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume x y) :
    IntervalIntegrable (fun u => ∑ i ∈ s, f i u) volume x y := by
  have e : (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, f i := by
    funext u; simp [Finset.sum_apply]
  rw [e]
  exact IntervalIntegrable.sum s hf

theorem int_ind {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : ∫ u in (0 : ℝ)..1, ind a u = 1 - a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a) (ind_ii a 0 a) (ind_ii a a 1)]
  have e1 : ∫ u in (0 : ℝ)..a, ind a u = ∫ u in (0 : ℝ)..a, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [Set.uIoc_of_le h0] at hu
    unfold ind; rw [if_neg (not_lt.2 hu.2)]
  have e2 : ∫ u in a..(1 : ℝ), ind a u = ∫ u in a..(1 : ℝ), (1 : ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [Set.uIoc_of_le h1] at hu
    unfold ind; rw [if_pos hu.1]
  rw [e1, e2]
  simp

theorem measurable_Qf (c : ℕ → ℝ) (k : ℕ) : Measurable (fun u => (Qf c k u : ℝ)) := by
  have : (fun u => (Qf c k u : ℝ)) = fun u => ∑ j ∈ Icc 1 k, ind (c j) u := by
    funext u; exact Qf_cast c k u
  rw [this]
  exact Finset.measurable_sum _ fun j _ => measurable_ind (c j)

theorem Qf_ii (c : ℕ → ℝ) (k : ℕ) (x y : ℝ) :
    IntervalIntegrable (fun u => (Qf c k u : ℝ)) volume x y := by
  have : (fun u => (Qf c k u : ℝ)) = fun u => ∑ j ∈ Icc 1 k, ind (c j) u := by
    funext u; exact Qf_cast c k u
  rw [this]
  exact ii_sum _ (fun j u => ind (c j) u) x y fun j _ => ind_ii (c j) x y

/-- Mean of the quantile. -/
theorem int_Q (c : ℕ → ℝ) (k : ℕ) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) :
    ∫ u in (0 : ℝ)..1, (Qf c k u : ℝ) = ∑ j ∈ Icc 1 k, (1 - c j) := by
  have : (fun u => (Qf c k u : ℝ)) = fun u => ∑ j ∈ Icc 1 k, ind (c j) u := by
    funext u; exact Qf_cast c k u
  rw [this, intervalIntegral.integral_finsetSum (fun j _ => ind_ii (c j) 0 1)]
  exact Finset.sum_congr rfl fun j _ => int_ind (hc j).1 (hc j).2

theorem abs_ind_sub (a b u : ℝ) : |ind a u - ind b u| = ind (min a b) u - ind (max a b) u := by
  unfold ind
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
    by_cases h1 : a < u <;> by_cases h2 : b < u <;> simp [h1, h2] <;> linarith
  · rw [min_eq_right h, max_eq_left h]
    by_cases h1 : a < u <;> by_cases h2 : b < u <;> simp [h1, h2] <;> linarith

theorem int_abs_ind_sub {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    ∫ u in (0 : ℝ)..1, |ind a u - ind b u| = |a - b| := by
  have e : (fun u => |ind a u - ind b u|) = fun u => ind (min a b) u - ind (max a b) u := by
    funext u; exact abs_ind_sub a b u
  rw [e, intervalIntegral.integral_sub (ind_ii _ 0 1) (ind_ii _ 0 1)]
  rw [int_ind (le_min ha.1 hb.1) (le_trans (min_le_left a b) ha.2),
    int_ind (le_trans ha.1 (le_max_left a b)) (max_le ha.2 hb.2)]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]; ring

/-- W1 bound: the quantile coupling moves at most `sum_j |c j - c' j|` in expectation. -/
theorem int_abs_Q_sub (c c' : ℕ → ℝ) (k : ℕ) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1)
    (hc' : ∀ j, 0 ≤ c' j ∧ c' j ≤ 1) :
    ∫ u in (0 : ℝ)..1, |(Qf c k u : ℝ) - (Qf c' k u : ℝ)| ≤ ∑ j ∈ Icc 1 k, |c j - c' j| := by
  have hle : ∀ u, |(Qf c k u : ℝ) - (Qf c' k u : ℝ)| ≤
      ∑ j ∈ Icc 1 k, |ind (c j) u - ind (c' j) u| := by
    intro u
    rw [Qf_cast, Qf_cast, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hii : ∀ j, IntervalIntegrable (fun u => |ind (c j) u - ind (c' j) u|) volume 0 1 :=
    fun j => ((ind_ii (c j) 0 1).sub (ind_ii (c' j) 0 1)).abs
  calc ∫ u in (0 : ℝ)..1, |(Qf c k u : ℝ) - (Qf c' k u : ℝ)|
      ≤ ∫ u in (0 : ℝ)..1, ∑ j ∈ Icc 1 k, |ind (c j) u - ind (c' j) u| := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (((Qf_ii c k 0 1).sub (Qf_ii c' k 0 1)).abs) (ii_sum _ _ 0 1 fun j _ => hii j)
          fun u _ => hle u
    _ = ∑ j ∈ Icc 1 k, |c j - c' j| := by
        rw [intervalIntegral.integral_finsetSum (fun j _ => hii j)]
        exact Finset.sum_congr rfl fun j _ => int_abs_ind_sub (hc j) (hc' j)

/-- For a monotone cumulative vector, `j <= Q u` iff `c j < u` (for `1 <= j <= k`). -/
theorem le_Qf_iff (c : ℕ → ℝ) (k : ℕ) (hmono : ∀ i j, i ≤ j → c i ≤ c j) (u : ℝ) (j : ℕ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) : j ≤ Qf c k u ↔ c j < u := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hsub : (Icc 1 k).filter (fun i => c i < u) ⊆ Finset.Ico 1 j := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_Icc] at hi
      rw [Finset.mem_Ico]
      refine ⟨hi.1.1, ?_⟩
      by_contra hij
      push_neg at hij
      have := hmono j i hij
      linarith [hi.2]
    have := Finset.card_le_card hsub
    simp at this
    unfold Qf at h
    omega
  · intro h
    have hsub : Finset.Icc 1 j ⊆ (Icc 1 k).filter (fun i => c i < u) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hi.1, le_trans hi.2 hjk⟩, lt_of_le_of_lt (hmono i j hi.2) h⟩
    have := Finset.card_le_card hsub
    simp at this
    unfold Qf
    omega

theorem Qf_le (c : ℕ → ℝ) (k : ℕ) (u : ℝ) : Qf c k u ≤ k := by
  unfold Qf
  calc ((Icc 1 k).filter (fun j => c j < u)).card ≤ (Icc 1 k).card := Finset.card_filter_le _ _
    _ = k := by simp

/-- Layer-cake form of a cost read at the quantile. -/
theorem h_Qf (c : ℕ → ℝ) (k : ℕ) (hmono : ∀ i j, i ≤ j → c i ≤ c j) (h : ℕ → ℝ) (u : ℝ) :
    h (Qf c k u) = h 0 + ∑ j ∈ Icc 1 k, (h j - h (j - 1)) * ind (c j) u := by
  have key : ∀ n, n ≤ k → ∀ q, q ≤ k →
      (∑ j ∈ Icc 1 n, (h j - h (j - 1)) * (if j ≤ q then (1 : ℝ) else 0)) = h (min n q) - h 0 := by
    intro n
    induction n with
    | zero => intro _ q _; simp
    | succ n ih =>
      intro hn q hq
      rw [Finset.sum_Icc_succ_top (by omega), ih (by omega) q hq]
      by_cases hnq : n + 1 ≤ q
      · rw [if_pos hnq, min_eq_left hnq, min_eq_left (by omega : n ≤ q)]
        simp
      · rw [if_neg hnq]
        push_neg at hnq
        rw [min_eq_right (by omega : q ≤ n), min_eq_right (by omega : q ≤ n + 1)]
        ring
  have hk := key k le_rfl (Qf c k u) (Qf_le c k u)
  rw [min_eq_right (Qf_le c k u)] at hk
  have hs : ∑ j ∈ Icc 1 k, (h j - h (j - 1)) * ind (c j) u =
      ∑ j ∈ Icc 1 k, (h j - h (j - 1)) * (if j ≤ Qf c k u then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    unfold ind
    by_cases hcu : c j < u
    · rw [if_pos hcu, if_pos ((le_Qf_iff c k hmono u j hj.1 hj.2).2 hcu)]
    · rw [if_neg hcu, if_neg (fun h' => hcu ((le_Qf_iff c k hmono u j hj.1 hj.2).1 h'))]
  rw [hs, hk]; ring

/-- Expected cost at the quantile. -/
theorem int_h_Q (c : ℕ → ℝ) (k : ℕ) (hmono : ∀ i j, i ≤ j → c i ≤ c j)
    (hc : ∀ j, 0 ≤ c j ∧ c j ≤ 1) (h : ℕ → ℝ) :
    ∫ u in (0 : ℝ)..1, h (Qf c k u) = h 0 + ∑ j ∈ Icc 1 k, (h j - h (j - 1)) * (1 - c j) := by
  have e : (fun u => h (Qf c k u)) =
      fun u => h 0 + ∑ j ∈ Icc 1 k, (h j - h (j - 1)) * ind (c j) u := by
    funext u; exact h_Qf c k hmono h u
  have hii : ∀ j, IntervalIntegrable (fun u => (h j - h (j - 1)) * ind (c j) u) volume 0 1 :=
    fun j => (ind_ii (c j) 0 1).const_mul _
  have hs := ii_sum (Icc 1 k) (fun j u => (h j - h (j - 1)) * ind (c j) u) 0 1 fun j _ => hii j
  rw [e, intervalIntegral.integral_add (intervalIntegrable_const (c := h 0)) hs,
    intervalIntegral.integral_finsetSum (fun j _ => hii j)]
  simp only [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [int_ind (hc j).1 (hc j).2]

end K17428


/-! D7b (17428d40, relay 5): integrability of ANY function of a quantile history.
`qhist c k N u t = Qf (c t) k u` (capped in `Fin (k+1)`): the comonotone quantile coupling of the
marginals with cumulative vectors `c 0, ..., c N` (one uniform `u` for all times). Every real
function `F` of the history is interval integrable in `u` (finitely many values, measurable).
Needs D7a (Qf, measurable_Qf, Qf_le). -/

namespace K17428

open Finset MeasureTheory intervalIntegral

/-- The quantile history (values in `Fin (k+1)`). -/
noncomputable def qhist (c : ℕ → ℕ → ℝ) (k N : ℕ) (u : ℝ) : Fin (N + 1) → Fin (k + 1) :=
  fun t => ⟨Qf (c t) k u, Nat.lt_succ_of_le (Qf_le (c t) k u)⟩

theorem measurable_Qf_nat (c : ℕ → ℝ) (k : ℕ) : Measurable (fun u => Qf c k u) := by
  refine measurable_to_countable' fun n => ?_
  have : (fun u => Qf c k u) ⁻¹' {n} = (fun u => (Qf c k u : ℝ)) ⁻¹' {(n : ℝ)} := by
    ext u; simp
  rw [this]
  exact measurable_Qf c k (measurableSet_singleton _)

theorem measurable_qhist (c : ℕ → ℕ → ℝ) (k N : ℕ) : Measurable (qhist c k N) := by
  refine measurable_pi_lambda _ fun t => ?_
  refine measurable_to_countable' fun n => ?_
  have : (fun u => qhist c k N u t) ⁻¹' {n} = (fun u => Qf (c t) k u) ⁻¹' {(n : ℕ)} := by
    ext u; simp only [Set.mem_preimage, Set.mem_singleton_iff, qhist]
    constructor
    · intro h; rw [← h]
    · intro h; exact Fin.ext h
  rw [this]
  exact measurable_Qf_nat (c t) k (measurableSet_singleton _)

theorem qhist_ii (c : ℕ → ℕ → ℝ) (k N : ℕ) (F : (Fin (N + 1) → Fin (k + 1)) → ℝ) (x y : ℝ) :
    IntervalIntegrable (fun u => F (qhist c k N u)) volume x y := by
  have hm : Measurable (fun u => F (qhist c k N u)) :=
    (measurable_of_countable F).comp (measurable_qhist c k N)
  refine IntervalIntegrable.mono_fun' (g := fun _ => ∑ z, |F z|) intervalIntegrable_const
    hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  show ‖F (qhist c k N u)‖ ≤ ∑ z, |F z|
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun z => |F z|) (fun z _ => abs_nonneg _) (Finset.mem_univ _)

/-- Monotonicity of the expectation over the coupling. -/
theorem qhist_int_mono (c : ℕ → ℕ → ℝ) (k N : ℕ) (F G : (Fin (N + 1) → Fin (k + 1)) → ℝ)
    (hFG : ∀ z, F z ≤ G z) :
    ∫ u in (0 : ℝ)..1, F (qhist c k N u) ≤ ∫ u in (0 : ℝ)..1, G (qhist c k N u) :=
  intervalIntegral.integral_mono_on zero_le_one (qhist_ii c k N F 0 1) (qhist_ii c k N G 0 1)
    fun u _ => hFG _

end K17428



/-! D7e (17428d40, relay 6): the NODE REQUESTS of design D7, abstractly (pure Allocation defs).
A node with `d` children sees at time `t >= 1` the child `loc t` containing the k-server
request (`none` if the request is outside the node's subtree), the child cost functions
`hf i t j` (the D4 differences `h^t_{c_i}(j)`, used for `j >= 1`; `h(0) := h(1)` is ignored by
`Afix` because the quota is positive) and the quota history `κ`. For a child-count schedule
`n` that serves every request, `intCost` splits into the child hit sums plus the edge movement
(`nodeSeq_intCost_split`), and `quotaVariation` is `g(κ)` (`nodeSeq_qv`). -/

namespace K17428

open Finset PolylogKServer.Allocation

variable {d k : ℕ}

noncomputable def nodeReq (hd : 0 < d) (loc : ℕ → Option (Fin d)) (hf : Fin d → ℕ → ℕ → ℝ)
    (κ : ℕ → ℕ) (t : ℕ) : Request d k :=
  ⟨(loc t).getD ⟨0, hd⟩, fun j => match loc t with
    | some i => hf i t (max 1 (j : ℕ)) + if (j : ℕ) = 0 then 1 else 0
    | none => 0, κ t⟩

noncomputable def nodeSeq (hd : 0 < d) (loc : ℕ → Option (Fin d)) (hf : Fin d → ℕ → ℕ → ℝ)
    (κ : ℕ → ℕ) (N : ℕ) : List (Request d k) :=
  (List.range N).map fun s => nodeReq hd loc hf κ (s + 1)

section Node

variable (hd : 0 < d) (loc : ℕ → Option (Fin d)) (hf : Fin d → ℕ → ℕ → ℝ) (κ : ℕ → ℕ)

theorem nodeSeq_length (N : ℕ) : (nodeSeq (k := k) hd loc hf κ N).length = N := by
  simp [nodeSeq]

theorem nodeSeq_get (N s : ℕ) (hs : s < (nodeSeq (k := k) hd loc hf κ N).length) :
    (nodeSeq (k := k) hd loc hf κ N)[s] = nodeReq hd loc hf κ (s + 1) := by
  simp [nodeSeq]

theorem nodeReq_quota (t : ℕ) : (nodeReq (k := k) hd loc hf κ t).quota = κ t := rfl

theorem nodeReq_loc (t : ℕ) (i : Fin d) (hl : loc t = some i) :
    (nodeReq (k := k) hd loc hf κ t).loc = i := by
  simp [nodeReq, hl]

theorem nodeReq_valid (hf0 : ∀ i t j, 0 ≤ hf i t j)
    (hanti : ∀ i t j j', 1 ≤ j → j ≤ j' → hf i t j' ≤ hf i t j) (t : ℕ) (hκ : κ t ≤ k) :
    (nodeReq (k := k) hd loc hf κ t).Valid := by
  refine ⟨hκ, fun j => ?_, fun a b hab => ?_⟩
  · simp only [nodeReq]
    split
    · exact add_nonneg (hf0 _ _ _) (by split_ifs <;> norm_num)
    · exact le_rfl
  · have hab' : (a : ℕ) ≤ b := hab
    simp only [nodeReq]
    split
    · exact add_le_add (hanti _ _ _ _ (le_max_left _ _) (max_le_max le_rfl hab'))
        (by split_ifs <;> norm_num <;> omega)
    · exact le_rfl

theorem nodeSeq_valid (hf0 : ∀ i t j, 0 ≤ hf i t j)
    (hanti : ∀ i t j j', 1 ≤ j → j ≤ j' → hf i t j' ≤ hf i t j) (hκ : ∀ t, κ t ≤ k) (N : ℕ) :
    ValidSeq (nodeSeq (k := k) hd loc hf κ N) := by
  intro r hr
  simp only [nodeSeq, List.mem_map] at hr
  obtain ⟨s, _, rfl⟩ := hr
  exact nodeReq_valid hd loc hf κ hf0 hanti _ (hκ _)

theorem nodeReq_hAt_some (t : ℕ) (i : Fin d) (hl : loc t = some i) (j : ℕ) (h1 : 1 ≤ j)
    (hjk : j ≤ k) : (nodeReq (k := k) hd loc hf κ t).hAt j = hf i t j := by
  have h0 : min j k ≠ 0 := by omega
  simp only [Request.hAt, nodeReq, hl, h0, if_false, add_zero]
  rw [show max 1 (min j k) = j by omega]

theorem nodeReq_h0_pos (hf0 : ∀ i t j, 0 ≤ hf i t j) (t : ℕ) (i : Fin d) (hl : loc t = some i) :
    0 < (nodeReq (k := k) hd loc hf κ t).h 0 := by
  simp only [nodeReq, hl, Fin.val_zero, if_true]
  linarith [hf0 i t (max 1 0)]

theorem nodeReq_h0_none (t : ℕ) (hl : loc t = none) :
    (nodeReq (k := k) hd loc hf κ t).h 0 = 0 := by
  simp only [nodeReq, hl]

theorem nodeReq_hAt_none (t : ℕ) (hl : loc t = none) (j : ℕ) :
    (nodeReq (k := k) hd loc hf κ t).hAt j = 0 := by
  simp only [Request.hAt, nodeReq, hl]

/-- The hit term of a node request, read on a child-count vector. -/
noncomputable def nodeHit (t : ℕ) (n : Fin d → ℕ) : ℝ :=
  match loc t with
  | some i => hf i t (n i)
  | none => 0

theorem nodeSeq_intCost (w : Fin d → ℝ) (N : ℕ) (n : ℕ → Fin d → ℕ)
    (hserve : ∀ t i, loc t = some i → 1 ≤ t → 1 ≤ n t i) (hnk : ∀ t i, n t i ≤ k) :
    intCost w (nodeSeq (k := k) hd loc hf κ N) n =
      ∑ t ∈ range N, (nodeHit loc hf (t + 1) (n (t + 1)) +
        ∑ i, w i * |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)|) := by
  unfold intCost
  rw [nodeSeq_length]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  have htl : t < (nodeSeq (k := k) hd loc hf κ N).length := by rw [nodeSeq_length]; exact ht'
  rw [List.getElem?_eq_getElem htl, nodeSeq_get hd loc hf κ N t htl]
  congr 1
  show (nodeReq (k := k) hd loc hf κ (t + 1)).hAt (n (t + 1) (nodeReq (k := k) hd loc hf κ (t + 1)).loc)
    = nodeHit loc hf (t + 1) (n (t + 1))
  unfold nodeHit
  split
  · rename_i i hl
    rw [nodeReq_loc hd loc hf κ _ i hl]
    exact nodeReq_hAt_some hd loc hf κ _ i hl _ (hserve _ i hl (by omega)) (hnk _ _)
  · rename_i hl
    exact nodeReq_hAt_none hd loc hf κ _ hl _

/-- Off its own child the cost function vanishes, so the hit term is a sum over children. -/
theorem nodeHit_sum (hout : ∀ i t j, loc t ≠ some i → hf i t j = 0) (t : ℕ) (n : Fin d → ℕ) :
    nodeHit loc hf t n = ∑ i, hf i t (n i) := by
  unfold nodeHit
  split
  · rename_i i0 hl
    rw [Finset.sum_eq_single i0]
    · intro b _ hb
      exact hout b t _ (by rw [hl]; intro h; exact hb (Option.some.inj h).symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rename_i hl
    exact (Finset.sum_eq_zero fun i _ => hout i t _ (by rw [hl]; simp)).symm

theorem nodeSeq_intCost_split (w : Fin d → ℝ) (N : ℕ) (n : ℕ → Fin d → ℕ)
    (hserve : ∀ t i, loc t = some i → 1 ≤ t → 1 ≤ n t i) (hnk : ∀ t i, n t i ≤ k)
    (hout : ∀ i t j, loc t ≠ some i → hf i t j = 0) :
    intCost w (nodeSeq (k := k) hd loc hf κ N) n =
      ∑ i, (∑ t ∈ range N, hf i (t + 1) (n (t + 1) i) +
        w i * ∑ t ∈ range N, |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)|) := by
  rw [nodeSeq_intCost hd loc hf κ w N n hserve hnk]
  simp only [nodeHit_sum loc hf hout, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := range N) (t := univ)]
  congr 1
  exact Finset.sum_comm

theorem nodeSeq_qv (κ₀ : ℕ) (hκ0 : κ 0 = κ₀) (N : ℕ) :
    quotaVariation κ₀ (nodeSeq (k := k) hd loc hf κ N) =
      ∑ t ∈ range N, |((κ (t + 1) : ℕ) : ℝ) - ((κ t : ℕ) : ℝ)| := by
  unfold quotaVariation
  rw [nodeSeq_length]
  have hq : ∀ t, t ≤ N → quotaAt κ₀ (nodeSeq (k := k) hd loc hf κ N) t = κ t := by
    intro t ht
    cases t with
    | zero => simp [quotaAt, hκ0]
    | succ s =>
      have hs : s < (nodeSeq (k := k) hd loc hf κ N).length := by rw [nodeSeq_length]; omega
      simp only [quotaAt, List.getElem?_eq_getElem hs, nodeSeq_get hd loc hf κ N s hs]
      rfl
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [hq (t + 1) (by omega), hq t (by omega)]

theorem nodeSeq_feasible (n₀ : Fin d → ℕ) (N : ℕ) (n : ℕ → Fin d → ℕ) (h0 : n 0 = n₀)
    (hnk : ∀ t i, n t i ≤ k) (hsum : ∀ t, t < N → ∑ i, n (t + 1) i ≤ κ (t + 1)) :
    IntFeasible n₀ (nodeSeq (k := k) hd loc hf κ N) n := by
  refine ⟨h0, fun t ht => ⟨fun i => hnk _ _, ?_⟩⟩
  rw [nodeSeq_get hd loc hf κ N t ht, nodeReq_quota]
  exact hsum t (by rwa [nodeSeq_length] at ht)

end Node

end K17428


/-! D8a (17428d40, relay 7): the ENSEMBLE (design D8), abstract in the node algorithms
`B p : FracAlg (children T p).card k` (instantiated later by `Afix` of the black box).
Node `p` with quota history `κ` feeds `B p` the node requests `nodeSeq κ` (D7e/D7f); its state
after `s` requests is `xs p κ i s`; child `i` at level `u ∈ (0,1]` gets the quantile history
`khist p κ i u s = Qf (cumul (xs p κ i s) i) k u` (D7a). Fuel recursion: `Tot` (total movement
of the ensemble below `p` up to time `N`) and `Zf` (expected quota of every vertex at time `N`).
Results: congruence in `κ` up to time `N` and interval integrability of any congruent function
of `khist` (via `qhist_ii`). Needs D7a D7b D7e D7f. -/

namespace K17428

open Finset MeasureTheory intervalIntegral PolylogKServer.HST PolylogKServer.Allocation

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

/-- Child weights of `p`. -/
noncomputable def wch (T : WTree V) (p : V) (i : Fin (children T p).card) : ℝ :=
  T.W (chv T p i)

/-- The state of the node algorithm of `p` after `s` node requests. -/
noncomputable def xs (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
    (B : ∀ p : V, FracAlg (children T p).card k) (p : V) (κ : ℕ → ℕ)
    (i : Fin (children T p).card) (s : ℕ) : FracState (children T p).card k :=
  (B p).state (nodeSeq (k := k) (Fin.pos i) (nloc T e p r) (nhf T e p r st) κ s)

/-- The quantile history of child `i` at level `u`. -/
noncomputable def khist (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
    (B : ∀ p : V, FracAlg (children T p).card k) (p : V) (κ : ℕ → ℕ)
    (i : Fin (children T p).card) (u : ℝ) : ℕ → ℕ :=
  fun s => Qf (fun j => cumul (xs T e k r st B p κ i s) i j) k u

/-- Movement of the node algorithm of `p` up to time `N` (0 at a leaf). -/
noncomputable def nmove (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
    (B : ∀ p : V, FracAlg (children T p).card k) (N : ℕ) (p : V) (κ : ℕ → ℕ) : ℝ :=
  if hd : 0 < (children T p).card then
    (B p).moveTotal (wch T p) (nodeSeq (k := k) hd (nloc T e p r) (nhf T e p r st) κ N)
  else 0

/-- Total ensemble movement below `p` up to time `N` (fuel `f`). -/
noncomputable def Tot (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
    (B : ∀ p : V, FracAlg (children T p).card k) (N : ℕ) : ℕ → V → (ℕ → ℕ) → ℝ
  | 0, _, _ => 0
  | f + 1, p, κ => nmove T e k r st B N p κ +
      ∑ i : Fin (children T p).card,
        ∫ u in (0 : ℝ)..1, Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u)

open Classical in
/-- Expected quota of the vertex `v` at time `N` in the ensemble below `p` (fuel `f`). -/
noncomputable def Zf (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
    (B : ∀ p : V, FracAlg (children T p).card k) (N : ℕ) : ℕ → V → (ℕ → ℕ) → V → ℝ
  | 0, p, κ, v => if v = p then (κ N : ℝ) else 0
  | f + 1, p, κ, v => if v = p then (κ N : ℝ) else
      ∑ i : Fin (children T p).card, if T.IsAnc (chv T p i) v then
        ∫ u in (0 : ℝ)..1, Zf T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) v
      else 0

section Ens

variable (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
  (B : ∀ p : V, FracAlg (children T p).card k)

theorem nodeSeq_congr {d : ℕ} (hd : 0 < d) (loc : ℕ → Option (Fin d)) (hf : Fin d → ℕ → ℕ → ℝ)
    (κ κ' : ℕ → ℕ) (N : ℕ) (h : ∀ s, 1 ≤ s → s ≤ N → κ s = κ' s) :
    nodeSeq (k := k) hd loc hf κ N = nodeSeq (k := k) hd loc hf κ' N := by
  unfold nodeSeq
  refine List.map_congr_left fun s hs => ?_
  have := List.mem_range.1 hs
  unfold nodeReq
  rw [h (s + 1) (by omega) (by omega)]

theorem xs_congr (p : V) (κ κ' : ℕ → ℕ) (i : Fin (children T p).card) (s : ℕ)
    (h : ∀ s' ≤ s, κ s' = κ' s') : xs T e k r st B p κ i s = xs T e k r st B p κ' i s := by
  unfold xs
  rw [nodeSeq_congr k _ _ _ κ κ' s fun s' _ hs' => h s' hs']

theorem khist_congr (p : V) (κ κ' : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ) (N : ℕ)
    (h : ∀ s ≤ N, κ s = κ' s) :
    ∀ s ≤ N, khist T e k r st B p κ i u s = khist T e k r st B p κ' i u s := by
  intro s hs
  unfold khist
  rw [xs_congr T e k r st B p κ κ' i s fun s' hs' => h s' (le_trans hs' hs)]

theorem nmove_congr (N : ℕ) (p : V) (κ κ' : ℕ → ℕ) (h : ∀ s ≤ N, κ s = κ' s) :
    nmove T e k r st B N p κ = nmove T e k r st B N p κ' := by
  unfold nmove
  split_ifs with hd
  · rw [nodeSeq_congr k hd _ _ κ κ' N fun s _ hs => h s hs]
  · rfl

theorem Tot_congr (N : ℕ) : ∀ (f : ℕ) (p : V) (κ κ' : ℕ → ℕ), (∀ s ≤ N, κ s = κ' s) →
    Tot T e k r st B N f p κ = Tot T e k r st B N f p κ' := by
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro p κ κ' h
    simp only [Tot]
    rw [nmove_congr T e k r st B N p κ κ' h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact ih _ _ _ (khist_congr T e k r st B p κ κ' i u N h)

theorem Zf_congr (N : ℕ) : ∀ (f : ℕ) (p : V) (κ κ' : ℕ → ℕ) (v : V), (∀ s ≤ N, κ s = κ' s) →
    Zf T e k r st B N f p κ v = Zf T e k r st B N f p κ' v := by
  intro f
  induction f with
  | zero => intro p κ κ' v h; simp only [Zf, h N le_rfl]
  | succ f ih =>
    intro p κ κ' v h
    simp only [Zf, h N le_rfl]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact ih _ _ _ _ (khist_congr T e k r st B p κ κ' i u N h)

/-- Extend a finite history by zeros. -/
def hext (N k : ℕ) (z : Fin (N + 1) → Fin (k + 1)) : ℕ → ℕ :=
  fun s => if h : s ≤ N then (z ⟨s, Nat.lt_succ_of_le h⟩ : ℕ) else 0

theorem khist_eq_qhist (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ) (N : ℕ) :
    ∀ s ≤ N, khist T e k r st B p κ i u s =
      hext N k (qhist (fun s j => cumul (xs T e k r st B p κ i s) i j) k N u) s := by
  intro s hs
  simp [hext, hs, qhist, khist]

/-- Any function of the history that only reads times `≤ N` is interval integrable along
the quantile family. -/
theorem hist_ii (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (N : ℕ) (G : (ℕ → ℕ) → ℝ)
    (hG : ∀ κ₁ κ₂ : ℕ → ℕ, (∀ s ≤ N, κ₁ s = κ₂ s) → G κ₁ = G κ₂) (x y : ℝ) :
    IntervalIntegrable (fun u => G (khist T e k r st B p κ i u)) volume x y := by
  have h := qhist_ii (fun s j => cumul (xs T e k r st B p κ i s) i j) k N
    (fun z => G (hext N k z)) x y
  have heq : (fun u => G (khist T e k r st B p κ i u)) =
      fun u => G (hext N k (qhist (fun s j => cumul (xs T e k r st B p κ i s) i j) k N u)) :=
    funext fun u => hG _ _ (khist_eq_qhist T e k r st B p κ i u N)
  rw [heq]
  exact h

theorem Tot_ii (N f : ℕ) (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (x y : ℝ) :
    IntervalIntegrable (fun u => Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u))
      volume x y :=
  hist_ii T e k r st B p κ i N _ (fun _ _ h => Tot_congr T e k r st B N f _ _ _ h) x y

theorem Zf_ii (N f : ℕ) (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (v : V) (x y : ℝ) :
    IntervalIntegrable
      (fun u => Zf T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) v) volume x y :=
  hist_ii T e k r st B p κ i N _ (fun _ _ h => Zf_congr T e k r st B N f _ _ _ v h) x y

end Ens

end K17428


/-! D8b (17428d40, relay 7): the expected-quota targets `Zf` move at most the ensemble cost:
`∑_{t<N} ∑_{v ∈ inner p} W v |Zf (t+1) p κ v - Zf t p κ v| ≤ Tot N p κ` (`zc_le_Tot`), by fuel
induction: the edge to child `c_i` moves `W(c_i) |E Q_{t+1} - E Q_t| ≤ w_i ∑_j |Δ cumul|`
(`int_abs_Q_sub`), i.e. the node algorithm's movement; deeper vertices by Jensen
(`|∫ a - ∫ b| ≤ ∫ |a - b|`) and the induction hypothesis inside the integral.
Needs D8a (and its chain). -/

namespace K17428

open Finset MeasureTheory intervalIntegral PolylogKServer.HST PolylogKServer.Allocation

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

theorem sum_children_fin (T : WTree V) (p : V) (F : V → ℝ) :
    ∑ c ∈ children T p, F c = ∑ i : Fin (children T p).card, F (chv T p i) := by
  rw [← Finset.sum_coe_sort]
  exact (Fintype.sum_equiv (children T p).equivFin.symm _ _ (fun _ => rfl)).symm

section Ens2

variable (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
  (B : ∀ p : V, FracAlg (children T p).card k)

theorem Zf_self (N f : ℕ) (p : V) (κ : ℕ → ℕ) : Zf T e k r st B N f p κ p = κ N := by
  cases f <;> simp [Zf]

theorem Zf_child (N f : ℕ) (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (v : V)
    (hv : T.IsAnc (chv T p i) v) :
    Zf T e k r st B N (f + 1) p κ v =
      ∫ u in (0 : ℝ)..1, Zf T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) v := by
  classical
  have hne : v ≠ p := ne_of_child T (chv_mem T p i) hv
  simp only [Zf, if_neg hne]
  rw [Finset.sum_eq_single i]
  · rw [if_pos hv]
  · intro i' _ hi'
    rw [if_neg]
    intro hv'
    exact hi' (chv_inj T p (child_unique T (chv_mem T p i') (chv_mem T p i) hv' hv))
  · intro h; exact absurd (Finset.mem_univ i) h

theorem nodeSeq_take {d : ℕ} (hd : 0 < d) (loc : ℕ → Option (Fin d)) (hf : Fin d → ℕ → ℕ → ℝ)
    (κ : ℕ → ℕ) (N t : ℕ) (h : t ≤ N) :
    (nodeSeq (k := k) hd loc hf κ N).take t = nodeSeq (k := k) hd loc hf κ t := by
  unfold nodeSeq
  rw [show List.range t = (List.range N).take t by rw [List.take_range, Nat.min_eq_left h]]
  first
    | exact (List.map_take ..).symm
    | exact List.map_take ..
    | exact List.take_map ..
    | exact (List.take_map ..).symm

theorem nmove_eq (N : ℕ) (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card) :
    nmove T e k r st B N p κ = ∑ t ∈ range N,
      moveCost (wch T p) (xs T e k r st B p κ i0 t) (xs T e k r st B p κ i0 (t + 1)) := by
  unfold nmove
  rw [dif_pos (Fin.pos i0)]
  unfold FracAlg.moveTotal
  rw [nodeSeq_length]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [nodeSeq_take k _ _ _ κ N t ht'.le, nodeSeq_take k _ _ _ κ N (t + 1) ht']
  rfl

theorem nmove_nonneg_of_empty (N : ℕ) (p : V) (κ : ℕ → ℕ) (h : (children T p).card = 0) :
    nmove T e k r st B N p κ = 0 := by
  unfold nmove
  rw [dif_neg (by omega)]

theorem w_abs_int_sub (W : ℝ) (hW : 0 ≤ W) (a b : ℝ → ℝ)
    (ha : IntervalIntegrable a volume 0 1) (hb : IntervalIntegrable b volume 0 1) :
    W * |(∫ u in (0 : ℝ)..1, a u) - ∫ u in (0 : ℝ)..1, b u| ≤
      ∫ u in (0 : ℝ)..1, W * |a u - b u| := by
  rw [← intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.abs_integral_le_integral_abs zero_le_one) hW

theorem zc_le_Tot
    (hcum : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (s : ℕ) (i' : Fin _) (j : ℕ),
      0 ≤ cumul (xs T e k r st B p κ i s) i' j ∧ cumul (xs T e k r st B p κ i s) i' j ≤ 1)
    (N : ℕ) : ∀ (f : ℕ) (p : V) (κ : ℕ → ℕ),
    ∑ t ∈ range N, ∑ v ∈ inner T p,
        T.W v * |Zf T e k r st B (t + 1) f p κ v - Zf T e k r st B t f p κ v| ≤
      Tot T e k r st B N f p κ := by
  classical
  intro f
  induction f with
  | zero =>
    intro p κ
    have : ∀ t, ∀ v ∈ inner T p, Zf T e k r st B t 0 p κ v = 0 := by
      intro t v hv
      simp only [Zf, if_neg ((mem_inner T).1 hv).2.2]
    simp only [Tot]
    refine le_of_eq (Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun v hv => ?_)
    rw [this t v hv, this (t + 1) v hv]; simp
  | succ f ih =>
    intro p κ
    set F : ℕ → V → ℝ := fun t v =>
      T.W v * |Zf T e k r st B (t + 1) (f + 1) p κ v - Zf T e k r st B t (f + 1) p κ v| with hF
    have hsplit : ∑ t ∈ range N, ∑ v ∈ inner T p, F t v =
        ∑ i : Fin (children T p).card, (∑ t ∈ range N, F t (chv T p i) +
          ∑ v ∈ inner T (chv T p i), ∑ t ∈ range N, F t v) := by
      rw [Finset.sum_comm, inner_split T p, Finset.sum_biUnion (inner_disj T p)]
      rw [sum_children_fin T p (fun c => ∑ v ∈ insert c (inner T c), ∑ t ∈ range N, F t v)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_insert (not_mem_inner_self T _)]
    have hT : Tot T e k r st B N (f + 1) p κ = nmove T e k r st B N p κ +
        ∑ i : Fin (children T p).card, ∫ u in (0 : ℝ)..1,
          Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) := by
      simp only [Tot]
    have hdist := Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin (children T p).card)))
      (f := fun i => ∑ t ∈ range N, F t (chv T p i))
      (g := fun i => ∑ v ∈ inner T (chv T p i), ∑ t ∈ range N, F t v)
    rw [hsplit, hT, hdist]
    have hA : ∑ i : Fin (children T p).card, ∑ t ∈ range N, F t (chv T p i) ≤
        nmove T e k r st B N p κ := by
      by_cases hd : (children T p).card = 0
      · have : IsEmpty (Fin (children T p).card) := by rw [hd]; exact Fin.isEmpty'
        rw [Finset.univ_eq_empty, Finset.sum_empty, nmove_nonneg_of_empty T e k r st B N p κ hd]
      · have i0 : Fin (children T p).card := ⟨0, by omega⟩
        rw [nmove_eq T e k r st B N p κ i0]
        unfold moveCost
        rw [Finset.sum_comm (s := range N)]
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun t _ => ?_
        have hmem : chv T p i ∈ inner T p := by
          rw [inner_split T p, Finset.mem_biUnion]
          exact ⟨_, chv_mem T p i, Finset.mem_insert_self _ _⟩
        have hW : 0 ≤ T.W (chv T p i) := W_nonneg_inner T p _ hmem
        have hZ : ∀ s, Zf T e k r st B s (f + 1) p κ (chv T p i) =
            ∫ u in (0 : ℝ)..1, (Qf (fun j => cumul (xs T e k r st B p κ i s) i j) k u : ℝ) := by
          intro s
          rw [Zf_child T e k r st B s f p κ i _ (isAnc_refl T _)]
          refine intervalIntegral.integral_congr fun u _ => ?_
          rw [Zf_self]; rfl
        simp only [hF, hZ]
        have h1 := w_abs_int_sub (T.W (chv T p i)) hW _ _
          (Qf_ii (fun j => cumul (xs T e k r st B p κ i (t + 1)) i j) k 0 1)
          (Qf_ii (fun j => cumul (xs T e k r st B p κ i t) i j) k 0 1)
        have h2 := int_abs_Q_sub (fun j => cumul (xs T e k r st B p κ i (t + 1)) i j)
          (fun j => cumul (xs T e k r st B p κ i t) i j) k (hcum p κ i (t + 1) i)
          (hcum p κ i t i)
        rw [intervalIntegral.integral_const_mul] at h1
        have h3 := mul_le_mul_of_nonneg_left h2 hW
        unfold wch
        exact h1.trans h3
    have hB : ∀ i : Fin (children T p).card,
        ∑ v ∈ inner T (chv T p i), ∑ t ∈ range N, F t v ≤ ∫ u in (0 : ℝ)..1,
          Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) := by
      intro i
      set c := chv T p i with hc
      have hW : ∀ v ∈ inner T c, 0 ≤ T.W v := fun v hv => W_nonneg_inner T c v hv
      have hZ : ∀ s, ∀ v ∈ inner T c, Zf T e k r st B s (f + 1) p κ v =
          ∫ u in (0 : ℝ)..1, Zf T e k r st B s f c (khist T e k r st B p κ i u) v := by
        intro s v hv
        exact Zf_child T e k r st B s f p κ i v ((mem_inner T).1 hv).2.1
      have hii : ∀ s, s ≤ N → ∀ v, IntervalIntegrable
          (fun u => Zf T e k r st B s f c (khist T e k r st B p κ i u) v) volume 0 1 := by
        intro s hs v
        exact hist_ii T e k r st B p κ i N _ (fun κ₁ κ₂ h =>
          Zf_congr T e k r st B s f _ _ _ v fun s' hs' => h s' (le_trans hs' hs)) 0 1
      set G : ℕ → V → ℝ → ℝ := fun t v u => T.W v *
        |Zf T e k r st B (t + 1) f c (khist T e k r st B p κ i u) v -
          Zf T e k r st B t f c (khist T e k r st B p κ i u) v| with hG
      have hGii : ∀ t ∈ range N, ∀ v, IntervalIntegrable (G t v) volume 0 1 := by
        intro t ht v
        have ht' := Finset.mem_range.1 ht
        exact hist_ii T e k r st B p κ i N (fun κ' => T.W v *
          |Zf T e k r st B (t + 1) f c κ' v - Zf T e k r st B t f c κ' v|) (fun κ₁ κ₂ h => by
          rw [Zf_congr T e k r st B (t + 1) f _ _ _ v fun s' hs' => h s' (by omega),
            Zf_congr T e k r st B t f _ _ _ v fun s' hs' => h s' (by omega)]) 0 1
      have hstep : ∀ v ∈ inner T c, ∀ t ∈ range N, F t v ≤ ∫ u in (0 : ℝ)..1, G t v u := by
        intro v hv t ht
        have ht' := Finset.mem_range.1 ht
        simp only [hF, hG]
        rw [hZ (t + 1) v hv, hZ t v hv]
        exact w_abs_int_sub _ (hW v hv) _ _ (hii (t + 1) ht' v) (hii t ht'.le v)
      refine (Finset.sum_le_sum fun v hv => Finset.sum_le_sum (hstep v hv)).trans ?_
      have hswap : ∑ v ∈ inner T c, ∑ t ∈ range N, ∫ u in (0 : ℝ)..1, G t v u =
          ∫ u in (0 : ℝ)..1, ∑ t ∈ range N, ∑ v ∈ inner T c, G t v u := by
        rw [Finset.sum_comm, intervalIntegral.integral_finset_sum]
        · refine Finset.sum_congr rfl fun t ht => ?_
          rw [intervalIntegral.integral_finset_sum]
          intro v _; exact hGii t ht v
        · intro t ht
          exact ii_sum (inner T c) (fun v => G t v) 0 1 fun v _ => hGii t ht v
      rw [hswap]
      refine intervalIntegral.integral_mono_on zero_le_one ?_ (Tot_ii T e k r st B N f p κ i 0 1)
        fun u _ => ih c (khist T e k r st B p κ i u)
      exact ii_sum (range N) (fun t u => ∑ v ∈ inner T c, G t v u) 0 1 fun t ht =>
        ii_sum (inner T c) (fun v => G t v) 0 1 fun v _ => hGii t ht v
    have hB' := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (children T p).card))) => hB i)
    linarith

end Ens2

end K17428


/-! D7c (17428d40, relay 5): SERVICE FIX of an allocation state (design D7, plan file).
The black-box allocation algorithm may leave a tiny mass `δ = x i0 0` of "no server" at the
requested location `i0` (formal costs are real, so `h(0) = ∞` is not available; we use a huge
`h(0) = H_t` so that `δ <= B_t / H_t`). `fixS x i0 κ` moves that mass to one server and, if the
quota is then exceeded, mixes with the target `1 server at i0, 0 elsewhere`. Results:
feasible (`fixS_feasible`), zero no-server mass at `i0` (`fixS_zero`), movement
`<= 2 wmax δ` (`fixS_move`), hit cost `<= hit + δ h(1)` (`fixS_hit`). Pure Allocation defs. -/

namespace K17428

open Finset PolylogKServer.Allocation

variable {d k : ℕ}

/-- `[j = m]` on `Fin (k+1)`. -/
noncomputable def ej (m : ℕ) (j : Fin (k + 1)) : ℝ := if (j : ℕ) = m then 1 else 0

theorem sum_fin_ite (m : ℕ) (hm : m ≤ k) (g : Fin (k + 1) → ℝ) :
    ∑ j : Fin (k + 1), ej m j * g j = g ⟨m, by omega⟩ := by
  rw [Finset.sum_eq_single ⟨m, by omega⟩]
  · simp [ej]
  · intro b _ hb
    have : (b : ℕ) ≠ m := fun h => hb (Fin.ext h)
    simp [ej, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cumul_ej (m j' : ℕ) (hm : m ≤ k) :
    (∑ j : Fin (k + 1), if (j : ℕ) < j' then ej (k := k) m j else 0) = if m < j' then 1 else 0 := by
  have h := sum_fin_ite (k := k) m hm (fun j => if (j : ℕ) < j' then (1 : ℝ) else 0)
  simp only at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ej; split_ifs <;> simp

/-- Expected number of servers. -/
noncomputable def expect (x : FracState d k) : ℝ := ∑ i, ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * x i j

/-- Move the no-server mass at `i0` to one server. -/
noncomputable def shiftS (x : FracState d k) (i0 : Fin d) : FracState d k := fun i j =>
  x i j + (if i = i0 then x i0 0 else 0) * (ej 1 j - ej 0 j)

/-- One server at `i0`, none elsewhere. -/
noncomputable def targ (i0 : Fin d) : FracState d k := fun i j => if i = i0 then ej 1 j else ej 0 j

noncomputable def mixS (θ : ℝ) (a b : FracState d k) : FracState d k :=
  fun i j => (1 - θ) * a i j + θ * b i j

noncomputable def theta (E κ : ℝ) : ℝ := if E ≤ κ then 0 else (E - κ) / (E - 1)

noncomputable def fixS (x : FracState d k) (i0 : Fin d) (κ : ℕ) : FracState d k :=
  mixS (theta (expect (shiftS x i0)) κ) (shiftS x i0) (targ i0)

theorem theta_props {E κ : ℝ} (hκ : 1 ≤ κ) :
    0 ≤ theta E κ ∧ theta E κ ≤ 1 ∧ (1 - theta E κ) * E + theta E κ ≤ κ ∧
      theta E κ * (E - 1) ≤ max (E - κ) 0 := by
  unfold theta
  split_ifs with h
  · refine ⟨le_rfl, zero_le_one, by linarith, by simp⟩
  · push_neg at h
    have hE : 0 < E - 1 := by linarith
    refine ⟨div_nonneg (by linarith) hE.le, (div_le_one hE).2 (by linarith), ?_, ?_⟩
    · have : (E - κ) / (E - 1) * (E - 1) = E - κ := div_mul_cancel₀ _ hE.ne'
      nlinarith
    · rw [div_mul_cancel₀ _ hE.ne']; exact le_max_left _ _

theorem sum_ej (m : ℕ) (hm : m ≤ k) : ∑ j : Fin (k + 1), ej m j = 1 := by
  have h := sum_fin_ite (k := k) m hm (fun _ => 1)
  simpa using h

theorem sum_mul_ej (m : ℕ) (hm : m ≤ k) : ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * ej m j = m := by
  have h := sum_fin_ite (k := k) m hm (fun j => ((j : ℕ) : ℝ))
  simp only at h
  rw [← h]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem expect_shiftS (hk : 1 ≤ k) (x : FracState d k) (i0 : Fin d) :
    expect (shiftS x i0) = expect x + x i0 0 := by
  unfold expect shiftS
  have hi : ∀ i, (∑ j : Fin (k + 1), ((j : ℕ) : ℝ) *
      (x i j + (if i = i0 then x i0 0 else 0) * (ej 1 j - ej 0 j))) =
      (∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * x i j) + (if i = i0 then x i0 0 else 0) := by
    intro i
    have e : ∀ j : Fin (k + 1), ((j : ℕ) : ℝ) *
        (x i j + (if i = i0 then x i0 0 else 0) * (ej 1 j - ej 0 j)) =
        ((j : ℕ) : ℝ) * x i j + (if i = i0 then x i0 0 else 0) *
          (((j : ℕ) : ℝ) * ej 1 j - ((j : ℕ) : ℝ) * ej 0 j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, sum_mul_ej 1 hk, sum_mul_ej 0 (Nat.zero_le _)]
    simp
  rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_add_distrib]
  simp

theorem expect_targ (hk : 1 ≤ k) (i0 : Fin d) : expect (targ (k := k) i0) = 1 := by
  unfold expect targ
  have hi : ∀ i, (∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * (if i = i0 then ej 1 j else ej 0 j)) =
      if i = i0 then 1 else 0 := by
    intro i
    by_cases h : i = i0
    · simp only [h, if_true]; rw [sum_mul_ej 1 hk]; simp
    · simp only [h, if_false]; rw [sum_mul_ej 0 (Nat.zero_le k)]; simp
  rw [Finset.sum_congr rfl fun i _ => hi i]
  simp

theorem expect_mixS (θ : ℝ) (a b : FracState d k) :
    expect (mixS θ a b) = (1 - θ) * expect a + θ * expect b := by
  unfold expect mixS
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem fixS_zero (x : FracState d k) (i0 : Fin d) (κ : ℕ) : fixS x i0 κ i0 0 = 0 := by
  unfold fixS mixS shiftS targ ej
  simp

theorem shiftS_nonneg (hk : 1 ≤ k) (x : FracState d k) (hx : ∀ i j, 0 ≤ x i j) (i0 : Fin d) :
    ∀ i j, 0 ≤ shiftS x i0 i j := by
  intro i j
  unfold shiftS ej
  by_cases hi : i = i0
  · subst hi
    by_cases h0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext (by simp [h0])
      subst hj; simp
    · by_cases h1 : (j : ℕ) = 1
      · simp [h0, h1]; linarith [hx i j, hx i 0]
      · simp [h0, h1, hx i j]
  · simp [hi, hx i j]

theorem fixS_feasible (hk : 1 ≤ k) (x : FracState d k) (i0 : Fin d) (κ : ℕ) (hκ : 1 ≤ κ)
    (hx : FracFeasible x κ) : FracFeasible (fixS x i0 κ) κ := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  obtain ⟨ht0, ht1, ht2, _⟩ := theta_props (E := expect (shiftS x i0)) hκr
  set θ := theta (expect (shiftS x i0)) κ with hθ
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold fixS mixS
    rw [← hθ]
    have hs := shiftS_nonneg hk x h0 i0 i j
    have ht : 0 ≤ targ (k := k) i0 i j := by unfold targ ej; split_ifs <;> norm_num
    exact add_nonneg (mul_nonneg (by linarith) hs) (mul_nonneg ht0 ht)
  · intro i
    unfold fixS mixS
    rw [← hθ, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs : ∑ j : Fin (k + 1), shiftS x i0 i j = 1 := by
      unfold shiftS
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ej 1 hk,
        sum_ej 0 (Nat.zero_le _), h1 i]
      ring
    have htg : ∑ j : Fin (k + 1), targ (k := k) i0 i j = 1 := by
      unfold targ
      split_ifs
      · exact sum_ej 1 hk
      · exact sum_ej 0 (Nat.zero_le _)
    rw [hs, htg]; ring
  · have he := expect_mixS θ (shiftS x i0) (targ (k := k) i0)
    rw [expect_targ hk] at he
    have : expect (fixS x i0 κ) ≤ κ := by
      unfold fixS; rw [← hθ, he]; linarith
    exact this

/-- `cumul` is linear in the state. -/
theorem cumul_mixS (θ : ℝ) (a b : FracState d k) (i : Fin d) (j : ℕ) :
    cumul (mixS θ a b) i j = (1 - θ) * cumul a i j + θ * cumul b i j := by
  unfold cumul mixS
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  split_ifs <;> ring

theorem cumul_shiftS (hk : 1 ≤ k) (x : FracState d k) (i0 : Fin d) (i : Fin d) (j : ℕ) :
    cumul (shiftS x i0) i j = cumul x i j +
      (if i = i0 then x i0 0 else 0) * ((if 1 < j then 1 else 0) - (if 0 < j then 1 else 0)) := by
  unfold cumul shiftS
  rw [← cumul_ej (k := k) 1 j hk, ← cumul_ej (k := k) 0 j (Nat.zero_le _), ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  split_ifs <;> ring

theorem moveCost_triangle (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (a b c : FracState d k) :
    moveCost w a c ≤ moveCost w a b + moveCost w b c := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (hw i).le
  have := abs_sub_le (cumul c i j) (cumul b i j) (cumul a i j)
  linarith [abs_sub_comm (cumul c i j) (cumul b i j)]

theorem le_wmax (w : Fin d → ℝ) (i : Fin d) : w i ≤ wmax w :=
  le_ciSup (Set.finite_range w).bddAbove i

theorem move_shiftS (hk : 1 ≤ k) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (x : FracState d k)
    (hx : ∀ i j, 0 ≤ x i j) (i0 : Fin d) :
    moveCost w x (shiftS x i0) ≤ wmax w * x i0 0 := by
  unfold moveCost
  have hterm : ∀ i, w i * ∑ j ∈ Icc 1 k, |cumul (shiftS x i0) i j - cumul x i j| =
      if i = i0 then w i0 * x i0 0 else 0 := by
    intro i
    have e : ∀ j ∈ Icc 1 k, |cumul (shiftS x i0) i j - cumul x i j| =
        if j = 1 then (if i = i0 then x i0 0 else 0) else 0 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [cumul_shiftS hk, add_sub_cancel_left, if_pos (by omega : 0 < j)]
      by_cases hj1 : j = 1
      · subst hj1; simp only [lt_irrefl, if_false, if_true]
        split_ifs <;> simp [abs_of_nonneg (hx i0 0)]
      · rw [if_pos (by omega : 1 < j), if_neg hj1]; simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq' (Icc 1 k) 1, if_pos (by simp; omega)]
    split_ifs with h
    · subst h; rfl
    · simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' univ i0, if_pos (mem_univ _)]
  exact mul_le_mul_of_nonneg_right (le_wmax w i0) (hx i0 0)

theorem cumul_le_one (y : FracState d k) (i : Fin d) (hy : ∀ j, 0 ≤ y i j)
    (hs : ∑ j, y i j = 1) (j : ℕ) : cumul y i j ≤ 1 := by
  unfold cumul; rw [← hs]
  exact Finset.sum_le_sum fun j' _ => by split_ifs <;> simp [hy]

theorem cumul_one (y : FracState d k) (i : Fin d) : cumul y i 1 = y i 0 := by
  unfold cumul
  rw [Finset.sum_eq_single (0 : Fin (k + 1))]
  · simp
  · intro j _ hj
    have : ¬ (j : ℕ) < 1 := fun h => hj (Fin.ext (by rw [Fin.val_zero]; omega))
    rw [if_neg this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Layer cake: `sum_{j=1}^k P(X >= j) = E X`. -/
theorem layer_cake (y : FracState d k) (i : Fin d) (hs : ∑ j, y i j = 1) :
    ∑ j ∈ Icc 1 k, (1 - cumul y i j) = ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * y i j := by
  have e1 : ∀ j, 1 - cumul y i j = ∑ j' : Fin (k + 1), if j ≤ (j' : ℕ) then y i j' else 0 := by
    intro j
    unfold cumul
    rw [← hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases h : (j' : ℕ) < j
    · rw [if_pos h, if_neg (by omega)]; ring
    · rw [if_neg h, if_pos (by omega)]; ring
  rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hf : (Icc 1 k).filter (fun j => j ≤ (j' : ℕ)) = Icc 1 (j' : ℕ) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]
    have := j'.isLt; omega
  rw [hf, Nat.card_Icc]; simp

theorem move_mixS (w : Fin d → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (a b : FracState d k) :
    moveCost w a (mixS θ a b) =
      θ * ∑ i, w i * ∑ j ∈ Icc 1 k, |cumul b i j - cumul a i j| := by
  unfold moveCost
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cumul_mixS]
  have : (1 - θ) * cumul a i j + θ * cumul b i j - cumul a i j = θ * (cumul b i j - cumul a i j) := by
    ring
  rw [this, abs_mul, abs_of_nonneg hθ]; ring

theorem targ_dist (hk : 1 ≤ k) (x : FracState d k) (hx : ∀ i j, 0 ≤ x i j) (hs1 : ∀ i, ∑ j, x i j = 1)
    (i0 i : Fin d) :
    ∑ j ∈ Icc 1 k, |cumul (targ (k := k) i0) i j - cumul (shiftS x i0) i j| =
      ∑ j ∈ Icc 1 k, (1 - cumul (shiftS x i0) i j) - (if i = i0 then 1 else 0) := by
  have hsn := shiftS_nonneg hk x hx i0
  have hss : ∀ i, ∑ j, shiftS x i0 i j = 1 := by
    intro i
    unfold shiftS
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ej 1 hk,
      sum_ej 0 (Nat.zero_le _), hs1 i]
    ring
  have hct : ∀ j, cumul (targ (k := k) i0) i j =
      if i = i0 then (if 1 < j then 1 else 0) else (if 0 < j then 1 else 0) := by
    intro j
    unfold cumul targ
    split_ifs with h1 h2 h3 <;> first
      | (rw [← cumul_ej (k := k) 1 j hk]; simp [h1] at *; done)
      | (have := cumul_ej (k := k) 1 j hk; simp only [h1, if_true] at *; rw [this]; simp [*])
      | (have := cumul_ej (k := k) 0 j (Nat.zero_le _); simp only [h1, if_false] at *; rw [this]; simp [*])
  have e : ∀ j ∈ Icc 1 k, |cumul (targ (k := k) i0) i j - cumul (shiftS x i0) i j| =
      (1 - cumul (shiftS x i0) i j) - (if i = i0 ∧ j = 1 then 1 else 0) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hle := cumul_le_one (shiftS x i0) i (hsn i) (hss i) j
    rw [hct j]
    by_cases hi : i = i0
    · by_cases hj1 : j = 1
      · subst hj1
        have h0 : cumul (shiftS x i0) i 1 = 0 := by
          rw [cumul_one]; subst hi; unfold shiftS ej; simp
        rw [if_pos hi, if_neg (lt_irrefl 1), h0, if_pos ⟨hi, rfl⟩]; norm_num
      · rw [if_pos hi, if_pos (by omega : 1 < j), if_neg (by tauto), abs_of_nonneg (by linarith)]
        ring
    · rw [if_neg hi, if_pos (by omega : 0 < j), if_neg (by tauto), abs_of_nonneg (by linarith)]
      ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib]
  congr 1
  by_cases hi : i = i0
  · simp only [hi, true_and, if_true]
    rw [Finset.sum_ite_eq' (Icc 1 k) 1, if_pos (by simp; omega)]
  · simp [hi]

theorem fixS_move (hk : 1 ≤ k) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (x : FracState d k)
    (i0 : Fin d) (κ : ℕ) (hκ : 1 ≤ κ) (hx : FracFeasible x κ) :
    moveCost w x (fixS x i0 κ) ≤ 2 * wmax w * x i0 0 := by
  obtain ⟨h0, h1, h2⟩ := hx
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  set s := shiftS x i0 with hsdef
  obtain ⟨ht0, ht1, ht2, ht3⟩ := theta_props (E := expect s) hκr
  set θ := theta (expect s) κ with hθ
  have hsn := shiftS_nonneg hk x h0 i0
  have hss : ∀ i, ∑ j, s i j = 1 := by
    intro i
    rw [hsdef]; unfold shiftS
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ej 1 hk,
      sum_ej 0 (Nat.zero_le _), h1 i]
    ring
  have hwm : 0 ≤ wmax w := Real.iSup_nonneg fun i => (hw i).le
  have hA : ∑ i, w i * ∑ j ∈ Icc 1 k, |cumul (targ (k := k) i0) i j - cumul s i j| ≤
      wmax w * (expect s - 1) := by
    have hle : ∀ i, w i * ∑ j ∈ Icc 1 k, |cumul (targ (k := k) i0) i j - cumul s i j| ≤
        wmax w * ∑ j ∈ Icc 1 k, |cumul (targ (k := k) i0) i j - cumul s i j| :=
      fun i => mul_le_mul_of_nonneg_right (le_wmax w i)
        (Finset.sum_nonneg fun j _ => abs_nonneg _)
    refine le_trans (Finset.sum_le_sum fun i _ => hle i) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hwm
    rw [Finset.sum_congr rfl fun i _ => targ_dist hk x h0 h1 i0 i, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' univ i0, if_pos (mem_univ _)]
    unfold expect
    rw [Finset.sum_congr rfl fun i _ => layer_cake s i (hss i)]
  have hms := move_shiftS hk w hw x h0 i0
  have hmf : moveCost w s (fixS x i0 κ) ≤ θ * (wmax w * (expect s - 1)) := by
    unfold fixS; rw [← hsdef, ← hθ, move_mixS w θ ht0]
    exact mul_le_mul_of_nonneg_left hA ht0
  have hEs : expect s = expect x + x i0 0 := expect_shiftS hk x i0
  have hEx : expect x ≤ κ := h2
  have hmax : max (expect s - κ) 0 ≤ x i0 0 := max_le (by linarith) (h0 i0 0)
  have htri := moveCost_triangle w hw x s (fixS x i0 κ)
  have h3 : θ * (wmax w * (expect s - 1)) ≤ wmax w * x i0 0 := by
    have : θ * (wmax w * (expect s - 1)) = wmax w * (θ * (expect s - 1)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (le_trans ht3 hmax) hwm
  linarith

theorem hit_mixS (r : Request d k) (θ : ℝ) (a b : FracState d k) :
    hitCost r (mixS θ a b) = (1 - θ) * hitCost r a + θ * hitCost r b := by
  unfold hitCost mixS
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The fix raises the hit cost at the requested location by at most `δ h(1)`. -/
theorem fixS_hit (hk : 1 ≤ k) (x : FracState d k) (κ : ℕ) (hκ : 1 ≤ κ) (hx : FracFeasible x κ)
    (r : Request d k) (hr : r.Valid) :
    hitCost r (fixS x r.loc κ) ≤ hitCost r x + x r.loc 0 * r.h ⟨1, by omega⟩ := by
  obtain ⟨h0, h1, h2⟩ := hx
  obtain ⟨_, hhn, hha⟩ := hr
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  set i0 := r.loc with hi0
  set s := shiftS x i0 with hsdef
  obtain ⟨ht0, ht1, ht2, ht3⟩ := theta_props (E := expect s) hκr
  set θ := theta (expect s) κ with hθ
  set H1 := r.h ⟨1, by omega⟩ with hH1
  have hsn := shiftS_nonneg hk x h0 i0
  have hss : ∑ j, s i0 j = 1 := by
    rw [hsdef]; unfold shiftS
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_ej 1 hk,
      sum_ej 0 (Nat.zero_le _), h1 i0]
    ring
  have hH1n : 0 ≤ H1 := hhn _
  have hH10 : H1 ≤ r.h 0 := hha (Fin.mk_le_mk.2 (Nat.zero_le 1) : (0 : Fin (k + 1)) ≤ ⟨1, by omega⟩)
  have htg : hitCost r (targ (k := k) i0) = H1 := by
    unfold hitCost targ
    simp only [if_pos hi0.symm]
    have h := sum_fin_ite (k := k) 1 hk (fun j => r.h j)
    exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans h
  have hsh : hitCost r s = hitCost r x + x i0 0 * (H1 - r.h 0) := by
    rw [hsdef]; unfold hitCost shiftS
    simp only [if_pos hi0.symm]
    have e : ∀ j : Fin (k + 1), r.h j * (x i0 j + x i0 0 * (ej 1 j - ej 0 j)) =
        r.h j * x i0 j + x i0 0 * (ej 1 j * r.h j - ej 0 j * r.h j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, sum_fin_ite 1 hk, sum_fin_ite 0 (Nat.zero_le _)]
    rfl
  have hkey : H1 - hitCost r s ≤ H1 * (expect s - 1) := by
    have hEi : ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * s i0 j ≤ expect s := by
      unfold expect
      exact Finset.single_le_sum (f := fun i => ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * s i j)
        (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hsn i j))
        (Finset.mem_univ i0)
    have hterm : ∀ j : Fin (k + 1), (H1 - r.h j) * s i0 j ≤ H1 * (((j : ℕ) : ℝ) - 1) * s i0 j := by
      intro j
      by_cases hj0 : (j : ℕ) = 0
      · have : j = 0 := Fin.ext (by rw [Fin.val_zero]; exact hj0)
        have hz : s i0 j = 0 := by rw [this, hsdef]; unfold shiftS ej; simp
        rw [hz]; ring_nf; rfl
      · by_cases hj1 : (j : ℕ) = 1
        · have : j = ⟨1, by omega⟩ := Fin.ext hj1
          rw [this]
          have e1 : r.h ⟨1, by omega⟩ = H1 := rfl
          rw [e1]; simp
        · have hj2 : (2 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ (j : ℕ))
          have hsj := hsn i0 j
          have hhj := hhn j
          have : (H1 - r.h j) ≤ H1 * (((j : ℕ) : ℝ) - 1) := by nlinarith
          exact mul_le_mul_of_nonneg_right this hsj
    have hsum : H1 - hitCost r s = ∑ j : Fin (k + 1), (H1 - r.h j) * s i0 j := by
      unfold hitCost
      rw [← hi0]
      have e : ∀ j : Fin (k + 1), (H1 - r.h j) * s i0 j = H1 * s i0 j - r.h j * s i0 j :=
        fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, ← Finset.mul_sum, hss]
      ring
    have hsum2 : ∑ j : Fin (k + 1), H1 * (((j : ℕ) : ℝ) - 1) * s i0 j =
        H1 * (∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * s i0 j - 1) := by
      have e : ∀ j : Fin (k + 1), H1 * (((j : ℕ) : ℝ) - 1) * s i0 j =
          H1 * (((j : ℕ) : ℝ) * s i0 j) - H1 * s i0 j := fun j => by ring
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hss]
      ring
    rw [hsum]
    refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
    rw [hsum2]
    exact mul_le_mul_of_nonneg_left (by linarith) hH1n
  have hEs : expect s = expect x + x i0 0 := expect_shiftS hk x i0
  have hEx : expect x ≤ κ := h2
  have hmax : max (expect s - κ) 0 ≤ x i0 0 := max_le (by linarith) (h0 i0 0)
  have hfix : hitCost r (fixS x i0 κ) = hitCost r s + θ * (H1 - hitCost r s) := by
    unfold fixS; rw [← hsdef, ← hθ, hit_mixS, htg]; ring
  rw [hfix]
  have hδ := h0 i0 0
  have h4 : θ * (H1 - hitCost r s) ≤ H1 * (θ * (expect s - 1)) := by
    have := mul_le_mul_of_nonneg_left hkey ht0
    linarith
  have h5 : H1 * (θ * (expect s - 1)) ≤ H1 * x i0 0 :=
    mul_le_mul_of_nonneg_left (le_trans ht3 hmax) hH1n
  have h6 : x i0 0 * (H1 - r.h 0) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ (by linarith)
  rw [hsh] at h4 ⊢
  nlinarith

end K17428


/-! D8c (17428d40, relay 8): the ensemble targets `Zf` satisfy the hypotheses of
`capped_between` (D6b): nonnegativity, superadditivity `∑_{c child of v} Z c ≤ Z v` and service
`1 ≤ Z (e (r N))`. Abstract in a class `G p κ` of admissible histories, closed under the child
quantile histories for `u ∈ (0,1)`, on which the node states are feasible (superadditivity) and
have no mass at `(loc, 0)` when the quota is positive (service). Needs D8a D8b D7a D7c. -/

namespace K17428

open Finset MeasureTheory intervalIntegral PolylogKServer.HST PolylogKServer.Allocation

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

theorem depth_child (T : WTree V) {p c : V} (hc : c ∈ children T p) :
    T.depth c = T.depth p + 1 := by
  obtain ⟨hr, hp⟩ := (mem_children T).1 hc
  rw [← hp]; exact (T.depth_parent c hr).symm

theorem exists_chv (T : WTree V) {p v : V} (h : T.IsAnc p v) (hne : v ≠ p) :
    ∃ i : Fin (children T p).card, T.IsAnc (chv T p i) v := by
  obtain ⟨c, hc, hcv⟩ := exists_child T h hne
  refine ⟨(children T p).equivFin ⟨c, hc⟩, ?_⟩
  simpa [chv] using hcv

theorem one_le_Qf (c : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (u : ℝ) (h : c 1 < u) : 1 ≤ Qf c k u := by
  unfold Qf
  exact Finset.card_pos.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, hk⟩, h⟩⟩

theorem cumul_nonneg' {d k : ℕ} (y : FracState d k) (i : Fin d) (hy : ∀ j, 0 ≤ y i j) (j : ℕ) :
    0 ≤ cumul y i j := by
  unfold cumul
  exact Finset.sum_nonneg fun j' _ => by split_ifs <;> simp [hy]

section Ens3

variable (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
  (B : ∀ p : V, FracAlg (children T p).card k)

theorem Zf_nonneg (N : ℕ) : ∀ (f : ℕ) (p : V) (κ : ℕ → ℕ) (v : V),
    0 ≤ Zf T e k r st B N f p κ v := by
  intro f
  induction f with
  | zero => intro p κ v; simp only [Zf]; split_ifs <;> positivity
  | succ f ih =>
    intro p κ v
    simp only [Zf]
    split_ifs
    · positivity
    · refine Finset.sum_nonneg fun i _ => ?_
      split_ifs
      · exact intervalIntegral.integral_nonneg zero_le_one fun u _ => ih _ _ _
      · exact le_refl _

/-- Expected child quotas at the node `p` sum to at most the quota of `p`. -/
theorem sum_int_khist_le (N : ℕ) (p : V) (κ : ℕ → ℕ)
    (hfeas : ∀ i : Fin (children T p).card, FracFeasible (xs T e k r st B p κ i N) (κ N)) :
    ∑ i : Fin (children T p).card,
        ∫ u in (0 : ℝ)..1, ((khist T e k r st B p κ i u N : ℕ) : ℝ) ≤ κ N := by
  rcases Nat.eq_zero_or_pos (children T p).card with h0 | hpos
  · have : IsEmpty (Fin (children T p).card) := by rw [h0]; exact Fin.isEmpty'
    rw [Finset.univ_eq_empty, Finset.sum_empty]; positivity
  · set i0 : Fin (children T p).card := ⟨0, hpos⟩
    set x := xs T e k r st B p κ i0 N
    have hx : ∀ i : Fin (children T p).card, xs T e k r st B p κ i N = x := fun i => rfl
    obtain ⟨hnn, hsum, hle⟩ := hfeas i0
    calc ∑ i : Fin (children T p).card,
          ∫ u in (0 : ℝ)..1, ((khist T e k r st B p κ i u N : ℕ) : ℝ)
        = ∑ i : Fin (children T p).card, ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * x i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold khist
          rw [hx i, int_Q _ k fun j => ⟨cumul_nonneg' x i (hnn i) j,
            cumul_le_one x i (hnn i) (hsum i) j⟩]
          exact layer_cake x i (hsum i)
      _ ≤ κ N := hle

theorem Zf_superadd (N : ℕ) (G : V → (ℕ → ℕ) → Prop)
    (hfeas : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card), G p κ →
      FracFeasible (xs T e k r st B p κ i N) (κ N))
    (hG : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ), G p κ →
      u ∈ Set.Ioo (0 : ℝ) 1 → G (chv T p i) (khist T e k r st B p κ i u)) :
    ∀ (f : ℕ) (p : V) (κ : ℕ → ℕ) (v : V), G p κ → T.IsAnc p v →
      ∑ c ∈ children T v, Zf T e k r st B N f p κ c ≤ Zf T e k r st B N f p κ v := by
  intro f
  induction f with
  | zero =>
    intro p κ v _ hpv
    have h0 : ∀ c ∈ children T v, Zf T e k r st B N 0 p κ c = 0 := by
      intro c hc
      have hne : c ≠ p := by
        rintro rfl
        obtain ⟨hr, hpc⟩ := (mem_children T).1 hc
        exact not_isAnc_parent T hr (hpc ▸ hpv)
      simp [Zf, hne]
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    exact Zf_nonneg T e k r st B N 0 p κ v
  | succ f ih =>
    intro p κ v hG0 hpv
    by_cases hvp : v = p
    · subst hvp
      rw [sum_children_fin T v]
      have hc : ∀ i : Fin (children T v).card,
          Zf T e k r st B N (f + 1) v κ (chv T v i) =
            ∫ u in (0 : ℝ)..1, ((khist T e k r st B v κ i u N : ℕ) : ℝ) := by
        intro i
        rw [Zf_child T e k r st B N f v κ i _ (isAnc_refl T _)]
        refine intervalIntegral.integral_congr fun u _ => ?_
        exact Zf_self T e k r st B N f _ _
      rw [Finset.sum_congr rfl fun i _ => hc i, Zf_self]
      exact sum_int_khist_le T e k r st B N v κ fun i => hfeas v κ i hG0
    · obtain ⟨i, hi⟩ := exists_chv T hpv hvp
      have hcv : ∀ c ∈ children T v, T.IsAnc (chv T p i) c := fun c hc =>
        isAnc_trans T hi (by
          obtain ⟨_, hpc⟩ := (mem_children T).1 hc
          exact ⟨1, hpc⟩)
      rw [Finset.sum_congr rfl fun c hc => Zf_child T e k r st B N f p κ i c (hcv c hc),
        Zf_child T e k r st B N f p κ i v hi,
        ← intervalIntegral.integral_finsetSum fun c _ => Zf_ii T e k r st B N f p κ i c 0 1]
      refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one ?_
        (Zf_ii T e k r st B N f p κ i v 0 1) fun u hu => ?_
      · exact hist_ii T e k r st B p κ i N
          (fun κ' => ∑ c ∈ children T v, Zf T e k r st B N f (chv T p i) κ' c)
          (fun _ _ h => Finset.sum_congr rfl fun c _ => Zf_congr T e k r st B N f _ _ _ c h) 0 1
      · exact ih _ _ _ (hG p κ i u hG0 hu) hi

theorem Zf_service (N : ℕ) (hk : 1 ≤ k) (G : V → (ℕ → ℕ) → Prop)
    (hzero : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card), G p κ → 1 ≤ κ N →
      T.IsAnc (chv T p i) (e (r N) : V) → xs T e k r st B p κ i N i 0 = 0)
    (hG : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ), G p κ →
      u ∈ Set.Ioo (0 : ℝ) 1 → G (chv T p i) (khist T e k r st B p κ i u)) :
    ∀ (f : ℕ) (p : V) (κ : ℕ → ℕ), G p κ → T.IsAnc p (e (r N) : V) → 1 ≤ κ N →
      T.depth (e (r N) : V) ≤ T.depth p + f → 1 ≤ Zf T e k r st B N f p κ (e (r N)) := by
  intro f
  induction f with
  | zero =>
    intro p κ _ hpv hκ hd
    by_cases hvp : (e (r N) : V) = p
    · rw [hvp, Zf_self]; exact_mod_cast hκ
    · obtain ⟨c, hc, hcv⟩ := exists_child T hpv hvp
      have := depth_le_of_isAnc T hcv
      rw [depth_child T hc] at this
      omega
  | succ f ih =>
    intro p κ hG0 hpv hκ hd
    by_cases hvp : (e (r N) : V) = p
    · rw [hvp, Zf_self]; exact_mod_cast hκ
    · obtain ⟨i, hi⟩ := exists_chv T hpv hvp
      rw [Zf_child T e k r st B N f p κ i _ hi]
      refine le_trans (le_of_eq (by simp : (1 : ℝ) = ∫ u in (0 : ℝ)..1, (1 : ℝ))) ?_
      refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one intervalIntegrable_const
        (Zf_ii T e k r st B N f p κ i _ 0 1) fun u hu => ?_
      refine ih _ _ (hG p κ i u hG0 hu) hi ?_ ?_
      · unfold khist
        refine one_le_Qf _ k hk u ?_
        show cumul (xs T e k r st B p κ i N) i 1 < u
        rw [cumul_one, hzero p κ i hG0 hκ hi]
        exact hu.1
      · rw [depth_child T (chv_mem T p i)]; omega

end Ens3

end K17428



/-! D7d (17428d40, relay 6): the allocation-level SERVICE WRAPPER (design D7, plan file).
Stage 1: a competitive black box `A` pays `h(0) * x_{loc,0}` inside its hit cost, which is
bounded by the guarantee against ANY feasible integral schedule of the prefix (`delta_bound`).
Choosing `h(0) = H_t = 2^t (B_t + 1)(h_t(1) + 1)` makes `x_{loc,0} <= 2^-t` (`small_of_big`).
`nfeas` is the one-server-at-the-request schedule (`nfeas_feasible`). Pure Allocation defs. -/

namespace K17428

open Finset PolylogKServer.Allocation

variable {d k : ℕ}

theorem hitCost_nonneg' (r : Request d k) (hr : r.Valid) (x : FracState d k)
    (hx : ∀ i j, 0 ≤ x i j) : 0 ≤ hitCost r x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hr.2.1 j) (hx _ j)

theorem h0_mul_le_hitCost (r : Request d k) (hr : r.Valid) (x : FracState d k)
    (hx : ∀ i j, 0 ≤ x i j) : r.h 0 * x r.loc 0 ≤ hitCost r x := by
  unfold hitCost
  exact Finset.single_le_sum (f := fun j => r.h j * x r.loc j)
    (fun j _ => mul_nonneg (hr.2.1 j) (hx _ j)) (Finset.mem_univ 0)

theorem take_succ_eq' {α : Type*} (l : List α) (s : ℕ) (hs : s < l.length) :
    l.take (s + 1) = l.take s ++ [l[s]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs]; rfl

theorem validSeq_take {ρ : List (Request d k)} (hρ : ValidSeq ρ) (n : ℕ) : ValidSeq (ρ.take n) :=
  fun r hr => hρ r (List.mem_of_mem_take hr)

theorem state_nonneg (A : FracAlg d k) {w : Fin d → ℝ} {n₀ : Fin d → ℕ} {κ₀ : ℕ} {θ γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ) (ρ : List (Request d k)) (hρ : ValidSeq ρ) (s : ℕ)
    (hs : s < ρ.length) : ∀ i j, 0 ≤ A.state (ρ.take (s + 1)) i j := by
  have e := take_succ_eq' ρ s hs
  have hv : ValidSeq (ρ.take s ++ [ρ[s]]) := by rw [← e]; exact validSeq_take hρ _
  have h := (hA.2.1 (ρ.take s) (ρ[s]) hv).1
  rw [e]; exact h

theorem hit_le_hitTotal (A : FracAlg d k) {w : Fin d → ℝ} {n₀ : Fin d → ℕ} {κ₀ : ℕ} {θ γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ) (ρ : List (Request d k)) (hρ : ValidSeq ρ) (t : ℕ)
    (ht : t < ρ.length) : hitCost (ρ[t]) (A.state (ρ.take (t + 1))) ≤ A.hitTotal ρ := by
  unfold FracAlg.hitTotal
  have hterm : ∀ s ∈ range ρ.length,
      0 ≤ (((ρ[s]?).map fun r => hitCost r (A.state (ρ.take (s + 1)))).getD 0) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    rw [List.getElem?_eq_getElem hs']
    exact hitCost_nonneg' _ (hρ _ (List.getElem_mem hs')) _ (state_nonneg A hA ρ hρ s hs')
  have h := Finset.single_le_sum hterm (Finset.mem_range.mpr ht)
  rw [List.getElem?_eq_getElem ht] at h
  exact h

theorem intCost_nonneg (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (ρ : List (Request d k))
    (hρ : ValidSeq ρ) (n : ℕ → Fin d → ℕ) : 0 ≤ intCost w ρ n := by
  unfold intCost
  refine Finset.sum_nonneg fun t ht => add_nonneg ?_
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (abs_nonneg _))
  have ht' := Finset.mem_range.mp ht
  rw [List.getElem?_eq_getElem ht']
  exact (hρ _ (List.getElem_mem ht')).2.1 _

theorem optCost_le_int (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (n₀ : Fin d → ℕ)
    (ρ : List (Request d k)) (hρ : ValidSeq ρ) (n : ℕ → Fin d → ℕ) (hn : IntFeasible n₀ ρ n) :
    optCost w n₀ ρ ≤ intCost w ρ n :=
  csInf_le ⟨0, fun _ ⟨m, _, hc⟩ => hc ▸ intCost_nonneg w hw ρ hρ m⟩ ⟨n, hn, rfl⟩

theorem quotaVariation_nonneg (κ₀ : ℕ) (ρ : List (Request d k)) :
    0 ≤ quotaVariation κ₀ ρ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem wmax_nonneg (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) : 0 ≤ wmax w :=
  Real.iSup_nonneg fun i => (hw i).le

/-- The black box pays `h(0) x_{loc,0}` and is bounded against any feasible schedule
(`a` is the constant of its hit-cost guarantee). -/
theorem delta_bound (A : FracAlg d k) {w : Fin d → ℝ} (hw : ∀ i, 0 < w i) {n₀ : Fin d → ℕ}
    {κ₀ : ℕ} {θ γ : ℝ} (hA : A.IsCompetitive w n₀ κ₀ θ γ) (hθ : 0 ≤ θ) (a : ℝ)
    (ha : ∀ ρ : List (Request d k), ValidSeq ρ →
      A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a)
    (ρ : List (Request d k)) (hρ : ValidSeq ρ) (t : ℕ) (ht : t < ρ.length)
    (n : ℕ → Fin d → ℕ) (hn : IntFeasible n₀ (ρ.take (t + 1)) n) :
    (ρ[t]).h 0 * A.state (ρ.take (t + 1)) (ρ[t]).loc 0 ≤
      θ * (intCost w (ρ.take (t + 1)) n + wmax w * quotaVariation κ₀ (ρ.take (t + 1))) + a := by
  have hv' : ValidSeq (ρ.take (t + 1)) := validSeq_take hρ _
  have hlen : t < (ρ.take (t + 1)).length := by rw [List.length_take]; omega
  have h1 := hit_le_hitTotal A hA (ρ.take (t + 1)) hv' t hlen
  have hget : (ρ.take (t + 1))[t] = ρ[t] := by simp
  have htk : (ρ.take (t + 1)).take (t + 1) = ρ.take (t + 1) := by simp
  rw [hget, htk] at h1
  have h0 := h0_mul_le_hitCost (ρ[t]) (hρ _ (List.getElem_mem ht)) _ (state_nonneg A hA ρ hρ t ht)
  have h2 := ha (ρ.take (t + 1)) hv'
  have h3 := optCost_le_int w hw n₀ (ρ.take (t + 1)) hv' n hn
  have h4 : θ * (optCost w n₀ (ρ.take (t + 1)) + wmax w * quotaVariation κ₀ (ρ.take (t + 1))) ≤
      θ * (intCost w (ρ.take (t + 1)) n + wmax w * quotaVariation κ₀ (ρ.take (t + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith) hθ
  linarith

/-- A huge `h(0)` forces a tiny no-server mass. -/
theorem small_of_big {H B δ h1 : ℝ} (t : ℕ) (hB : 0 ≤ B) (hh1 : 0 ≤ h1) (hδ : 0 ≤ δ)
    (hH : (2 : ℝ) ^ t * (B + 1) * (h1 + 1) ≤ H) (hHδ : H * δ ≤ B) :
    δ ≤ 1 / 2 ^ t ∧ δ * h1 ≤ 1 / 2 ^ t := by
  have hP : (0 : ℝ) < 2 ^ t := by positivity
  have e1 : (2 : ℝ) ^ t * (B + 1) * (h1 + 1) * δ ≤ H * δ := mul_le_mul_of_nonneg_right hH hδ
  have e2 : (B + 1) * (2 ^ t * (h1 + 1) * δ) ≤ (B + 1) * 1 := by
    have : (B + 1) * (2 ^ t * (h1 + 1) * δ) = (2 : ℝ) ^ t * (B + 1) * (h1 + 1) * δ := by ring
    rw [this]; linarith
  have e3 : (2 : ℝ) ^ t * (h1 + 1) * δ ≤ 1 := le_of_mul_le_mul_left e2 (by linarith)
  have e4 : δ * (h1 + 1) * 2 ^ t ≤ 1 := by linarith [show δ * (h1 + 1) * 2 ^ t = (2 : ℝ) ^ t * (h1 + 1) * δ by ring]
  have e5 : δ * (h1 + 1) ≤ 1 / 2 ^ t := (le_div_iff₀ hP).mpr e4
  have e6 : δ * h1 ≤ δ * (h1 + 1) := by nlinarith
  have e7 : δ ≤ δ * (h1 + 1) := by nlinarith
  exact ⟨by linarith, by linarith⟩

/-- The schedule with one server at the requested location whenever the quota allows. -/
noncomputable def nfeas (n₀ : Fin d → ℕ) (ρ : List (Request d k)) : ℕ → Fin d → ℕ
  | 0 => n₀
  | t + 1 => fun i => match ρ[t]? with
    | some r => if r.loc = i ∧ 1 ≤ r.quota then 1 else 0
    | none => 0

theorem nfeas_succ (n₀ : Fin d → ℕ) (ρ : List (Request d k)) (t : ℕ) (ht : t < ρ.length)
    (i : Fin d) : nfeas n₀ ρ (t + 1) i = if (ρ[t]).loc = i ∧ 1 ≤ (ρ[t]).quota then 1 else 0 := by
  simp only [nfeas, List.getElem?_eq_getElem ht]

theorem nfeas_feasible (hk : 1 ≤ k) (n₀ : Fin d → ℕ) (ρ : List (Request d k)) :
    IntFeasible n₀ ρ (nfeas n₀ ρ) := by
  refine ⟨rfl, fun t ht => ⟨fun i => ?_, ?_⟩⟩
  · rw [nfeas_succ n₀ ρ t ht]; split_ifs <;> omega
  · simp only [nfeas_succ n₀ ρ t ht]
    by_cases hq : 1 ≤ (ρ[t]).quota
    · have : (∑ i : Fin d, if (ρ[t]).loc = i ∧ 1 ≤ (ρ[t]).quota then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single (ρ[t]).loc]
        · simp [hq]
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [this]; exact hq
    · have : (∑ i : Fin d, if (ρ[t]).loc = i ∧ 1 ≤ (ρ[t]).quota then 1 else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_; simp [hq]
      rw [this]; exact Nat.zero_le _

/-! Stage 2: congruence lemmas, the modified requests `modReq` and the sequence `mods`. -/

theorem intCost_congr (w : Fin d → ℝ) (ρ ρ' : List (Request d k)) (n : ℕ → Fin d → ℕ)
    (hl : ρ.length = ρ'.length)
    (he : ∀ s (hs : s < ρ.length) (hs' : s < ρ'.length),
      (ρ[s]).hAt (n (s + 1) (ρ[s]).loc) = (ρ'[s]).hAt (n (s + 1) (ρ'[s]).loc)) :
    intCost w ρ n = intCost w ρ' n := by
  unfold intCost
  rw [hl]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.mp hs
  have hs0 : s < ρ.length := hl ▸ hs'
  rw [List.getElem?_eq_getElem hs', List.getElem?_eq_getElem hs0]
  exact congrArg (· + _) (he s hs0 hs')

theorem quotaAt_congr (κ₀ : ℕ) (ρ ρ' : List (Request d k)) (hl : ρ.length = ρ'.length)
    (he : ∀ s (hs : s < ρ.length) (hs' : s < ρ'.length), (ρ[s]).quota = (ρ'[s]).quota) (t : ℕ) :
    quotaAt κ₀ ρ t = quotaAt κ₀ ρ' t := by
  cases t with
  | zero => rfl
  | succ t =>
    simp only [quotaAt]
    by_cases ht : t < ρ.length
    · have ht' : t < ρ'.length := hl ▸ ht
      rw [List.getElem?_eq_getElem ht, List.getElem?_eq_getElem ht']
      simp [he t ht ht']
    · have ht' : ¬ t < ρ'.length := hl ▸ ht
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem quotaVariation_congr (κ₀ : ℕ) (ρ ρ' : List (Request d k)) (hl : ρ.length = ρ'.length)
    (he : ∀ s (hs : s < ρ.length) (hs' : s < ρ'.length), (ρ[s]).quota = (ρ'[s]).quota) :
    quotaVariation κ₀ ρ = quotaVariation κ₀ ρ' := by
  unfold quotaVariation
  rw [hl]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [quotaAt_congr κ₀ ρ ρ' hl he, quotaAt_congr κ₀ ρ ρ' hl he]

theorem nfeas_congr (n₀ : Fin d → ℕ) (ρ ρ' : List (Request d k)) (hl : ρ.length = ρ'.length)
    (he : ∀ s (hs : s < ρ.length) (hs' : s < ρ'.length),
      (ρ[s]).loc = (ρ'[s]).loc ∧ (ρ[s]).quota = (ρ'[s]).quota) :
    nfeas n₀ ρ = nfeas n₀ ρ' := by
  funext t
  cases t with
  | zero => rfl
  | succ t =>
    funext i
    by_cases ht : t < ρ.length
    · have ht' : t < ρ'.length := hl ▸ ht
      rw [nfeas_succ n₀ ρ t ht, nfeas_succ n₀ ρ' t ht']
      obtain ⟨h1, h2⟩ := he t ht ht'
      rw [h1, h2]
    · have ht' : ¬ t < ρ'.length := hl ▸ ht
      simp only [nfeas, List.getElem?_eq_none (show ρ.length ≤ t by omega),
        List.getElem?_eq_none (show ρ'.length ≤ t by omega)]

/-- Replace `h(0)` by `H`. -/
noncomputable def withH (r : Request d k) (H : ℝ) : Request d k :=
  ⟨r.loc, fun j => if (j : ℕ) = 0 then H else r.h j, r.quota⟩

/-- Only requests with a positive quota get the huge `h(0)`. -/
noncomputable def modReq (r : Request d k) (H : ℝ) : Request d k :=
  if 1 ≤ r.quota ∧ 0 < r.h 0 then withH r H else r

theorem modReq_loc (r : Request d k) (H : ℝ) : (modReq r H).loc = r.loc := by
  unfold modReq; split_ifs <;> rfl

theorem modReq_quota (r : Request d k) (H : ℝ) : (modReq r H).quota = r.quota := by
  unfold modReq; split_ifs <;> rfl

theorem modReq_h (r : Request d k) (H : ℝ) (j : Fin (k + 1)) (hj : (j : ℕ) ≠ 0) :
    (modReq r H).h j = r.h j := by
  unfold modReq withH; split_ifs <;> simp [hj]

theorem modReq_h0 (r : Request d k) (H : ℝ) (hq : 1 ≤ r.quota ∧ 0 < r.h 0) : (modReq r H).h 0 = H := by
  unfold modReq withH; rw [if_pos hq]; simp

theorem modReq_of_zero (r : Request d k) (H : ℝ) (hq : ¬ (1 ≤ r.quota ∧ 0 < r.h 0)) : modReq r H = r := by
  unfold modReq; rw [if_neg hq]

theorem modReq_hAt (r : Request d k) (H : ℝ) (j : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (modReq r H).hAt j = r.hAt j := by
  unfold Request.hAt
  exact modReq_h r H _ (show min j k ≠ 0 by omega)

theorem modReq_valid (r : Request d k) (hr : r.Valid) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ j : Fin (k + 1), (j : ℕ) ≠ 0 → r.h j ≤ H) : (modReq r H).Valid := by
  unfold modReq; split_ifs
  · refine ⟨hr.1, fun j => ?_, fun a b hab => ?_⟩
    · show 0 ≤ (if (j : ℕ) = 0 then H else r.h j)
      split_ifs
      · exact hH0
      · exact hr.2.1 j
    · show (if (b : ℕ) = 0 then H else r.h b) ≤ (if (a : ℕ) = 0 then H else r.h a)
      have hab' : (a : ℕ) ≤ b := hab
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (by omega) h2
      · exact hH b h1
      · exact hr.2.2 hab
  · exact hr

section Wrap

variable (θ a : ℝ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ)

/-- The online bound `B_t` (the black box's guarantee against `nfeas` on the prefix). -/
noncomputable def Bval (l : List (Request d k)) : ℝ :=
  θ * (intCost w l (nfeas n₀ l) + wmax w * quotaVariation κ₀ l) + |a| + 1

/-- `H_t = 2^t (B_t + 1)(h_t(1) + 1)`, computed from the earlier requests `l` and `r`. -/
noncomputable def Hval (l : List (Request d k)) (r : Request d k) : ℝ :=
  2 ^ l.length * (Bval θ a w n₀ κ₀ (l ++ [r]) + 1) * (r.hAt 1 + 1)

/-- The sequence fed to the black box. -/
noncomputable def mods (l : List (Request d k)) : List (Request d k) :=
  l.mapIdx fun t r => modReq r (Hval θ a w n₀ κ₀ (l.take t) r)

theorem mods_length (l : List (Request d k)) : (mods θ a w n₀ κ₀ l).length = l.length := by
  simp [mods]

theorem mods_get (l : List (Request d k)) (s : ℕ) (hs : s < (mods θ a w n₀ κ₀ l).length)
    (hs' : s < l.length) :
    (mods θ a w n₀ κ₀ l)[s] = modReq (l[s]) (Hval θ a w n₀ κ₀ (l.take s) (l[s])) := by
  simp [mods]

theorem mods_take (l : List (Request d k)) (n : ℕ) :
    (mods θ a w n₀ κ₀ l).take n = mods θ a w n₀ κ₀ (l.take n) := by
  apply List.ext_getElem
  · simp [mods]
  · intro s h1 h2
    have hs : s < n := by simp [mods] at h1; omega
    simp only [mods, List.getElem_take, List.getElem_mapIdx, List.take_take]
    rw [show min s n = s by omega]

theorem mods_snoc (l : List (Request d k)) (r : Request d k) :
    mods θ a w n₀ κ₀ (l ++ [r]) = mods θ a w n₀ κ₀ l ++ [modReq r (Hval θ a w n₀ κ₀ l r)] := by
  have h1 : (mods θ a w n₀ κ₀ (l ++ [r])).take l.length = mods θ a w n₀ κ₀ l := by
    rw [mods_take]; simp
  have hlt : l.length < (mods θ a w n₀ κ₀ (l ++ [r])).length := by simp [mods]
  have e := take_succ_eq' (mods θ a w n₀ κ₀ (l ++ [r])) l.length hlt
  rw [List.take_of_length_le (by simp [mods])] at e
  rw [e, h1]
  congr 1
  simp [mods]

theorem Bval_nonneg (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (l : List (Request d k)) (hl : ValidSeq l) :
    1 ≤ Bval θ a w n₀ κ₀ l := by
  unfold Bval
  have h1 := intCost_nonneg w hw l hl (nfeas n₀ l)
  have h2 := mul_nonneg (wmax_nonneg w hw) (quotaVariation_nonneg κ₀ l)
  have h3 := mul_nonneg hθ (add_nonneg h1 h2)
  have h4 := abs_nonneg a
  linarith

theorem h_le_hAt1 (hk : 1 ≤ k) (r : Request d k) (hr : r.Valid) (j : Fin (k + 1))
    (hj : (j : ℕ) ≠ 0) : r.h j ≤ r.hAt 1 := by
  unfold Request.hAt
  apply hr.2.2
  show min 1 k ≤ (j : ℕ)
  omega

theorem le_Hval (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (hk : 1 ≤ k) (l : List (Request d k))
    (r : Request d k) (hv : ValidSeq (l ++ [r])) :
    r.hAt 1 + 1 ≤ Hval θ a w n₀ κ₀ l r := by
  unfold Hval
  have hB := Bval_nonneg θ a w n₀ κ₀ hθ hw (l ++ [r]) hv
  have hr : r.Valid := hv r (by simp)
  have hh : 0 ≤ r.hAt 1 := hr.2.1 _
  have hP : (1 : ℝ) ≤ 2 ^ l.length := one_le_pow₀ (by norm_num)
  have e : 1 ≤ (2 : ℝ) ^ l.length * (Bval θ a w n₀ κ₀ (l ++ [r]) + 1) := by nlinarith
  nlinarith

theorem mods_valid (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (hk : 1 ≤ k) (l : List (Request d k))
    (hl : ValidSeq l) : ValidSeq (mods θ a w n₀ κ₀ l) := by
  intro r' hr'
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.mp hr'
  have hs' : s < l.length := by simpa [mods] using hs
  rw [mods_get θ a w n₀ κ₀ l s hs hs']
  have hv : ValidSeq (l.take s ++ [l[s]]) := by
    rw [← take_succ_eq' l s hs']; exact validSeq_take hl _
  have hr : (l[s]).Valid := hl _ (List.getElem_mem hs')
  have hH := le_Hval θ a w n₀ κ₀ hθ hw hk (l.take s) (l[s]) hv
  have hh : 0 ≤ (l[s]).hAt 1 := hr.2.1 _
  refine modReq_valid _ hr _ (by linarith) fun j hj => ?_
  have := h_le_hAt1 hk _ hr j hj
  linarith

/-! Stage 3: the wrapped algorithm `Afix` (black box on `mods`, then `fixS`). -/

theorem mods_nfeas (l : List (Request d k)) :
    nfeas n₀ (mods θ a w n₀ κ₀ l) = nfeas n₀ l :=
  nfeas_congr n₀ _ l (mods_length θ a w n₀ κ₀ l) fun s hs hs' => by
    rw [mods_get θ a w n₀ κ₀ l s hs hs', modReq_loc, modReq_quota]; exact ⟨rfl, rfl⟩

theorem mods_qv (l : List (Request d k)) :
    quotaVariation κ₀ (mods θ a w n₀ κ₀ l) = quotaVariation κ₀ l :=
  quotaVariation_congr κ₀ _ l (mods_length θ a w n₀ κ₀ l) fun s hs hs' => by
    rw [mods_get θ a w n₀ κ₀ l s hs hs', modReq_quota]

/-- Any schedule keeping a server at the request whenever the quota is positive costs the
same on `mods l` as on `l`. -/
theorem mods_intCost (hk : 1 ≤ k) (l : List (Request d k)) (n : ℕ → Fin d → ℕ)
    (hn : ∀ s (hs : s < l.length), 1 ≤ (l[s]).quota ∧ 0 < (l[s]).h 0 → 1 ≤ n (s + 1) (l[s]).loc) :
    intCost w (mods θ a w n₀ κ₀ l) n = intCost w l n :=
  intCost_congr w _ l n (mods_length θ a w n₀ κ₀ l) fun s hs hs' => by
    rw [mods_get θ a w n₀ κ₀ l s hs hs', modReq_loc]
    by_cases hq : 1 ≤ (l[s]).quota ∧ 0 < (l[s]).h 0
    · have h1 := hn s hs' hq
      unfold Request.hAt
      exact modReq_h _ _ _ (show min (n (s + 1) (l[s]).loc) k ≠ 0 by omega)
    · rw [modReq_of_zero _ _ hq]

theorem nfeas_serves (l : List (Request d k)) (s : ℕ) (hs : s < l.length)
    (hq : 1 ≤ (l[s]).quota) : 1 ≤ nfeas n₀ l (s + 1) (l[s]).loc := by
  rw [nfeas_succ n₀ l s hs]; simp [hq]

theorem mods_nfeas_cost (hk : 1 ≤ k) (l : List (Request d k)) :
    intCost w (mods θ a w n₀ κ₀ l) (nfeas n₀ (mods θ a w n₀ κ₀ l)) = intCost w l (nfeas n₀ l) := by
  rw [mods_nfeas]; exact mods_intCost θ a w n₀ κ₀ hk l _ fun s hs hq => nfeas_serves n₀ l s hs hq.1

/-- The wrapped online algorithm. -/
noncomputable def Afix (A : FracAlg d k) : FracAlg d k :=
  ⟨fun l => match l.getLast? with
    | some r => if 1 ≤ r.quota ∧ 0 < r.h 0 then fixS (A.state (mods θ a w n₀ κ₀ l)) r.loc r.quota
        else A.state (mods θ a w n₀ κ₀ l)
    | none => A.state (mods θ a w n₀ κ₀ l)⟩

theorem Afix_nil (A : FracAlg d k) : (Afix θ a w n₀ κ₀ A).state [] = A.state [] := by
  simp [Afix, mods]

theorem Afix_snoc (A : FracAlg d k) (l : List (Request d k)) (r : Request d k) :
    (Afix θ a w n₀ κ₀ A).state (l ++ [r]) =
      if 1 ≤ r.quota ∧ 0 < r.h 0 then fixS (A.state (mods θ a w n₀ κ₀ (l ++ [r]))) r.loc r.quota
      else A.state (mods θ a w n₀ κ₀ (l ++ [r])) := by
  simp only [Afix, List.getLast?_append, List.getLast?_singleton]
  rfl

theorem Afix_feasible (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ) (l : List (Request d k)) (r : Request d k)
    (hv : ValidSeq (l ++ [r])) : FracFeasible ((Afix θ a w n₀ κ₀ A).state (l ++ [r])) r.quota := by
  have hm := mods_valid θ a w n₀ κ₀ hθ hw hk _ hv
  rw [mods_snoc] at hm
  have hF := hA.2.1 _ _ hm
  rw [modReq_quota] at hF
  rw [Afix_snoc, mods_snoc]
  split_ifs with hq
  · exact fixS_feasible hk _ _ _ hq.1 hF
  · exact hF

/-! Stage 4: the service bound and the totals of `Afix`. -/

theorem moveCost_self' (w : Fin d → ℝ) (x : FracState d k) : moveCost w x x = 0 := by
  unfold moveCost; simp

theorem moveCost_comm' (w : Fin d → ℝ) (x y : FracState d k) : moveCost w x y = moveCost w y x := by
  unfold moveCost
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => abs_sub_comm _ _

theorem Afix_zero (A : FracAlg d k) (l : List (Request d k)) (r : Request d k)
    (hq : 1 ≤ r.quota ∧ 0 < r.h 0) : (Afix θ a w n₀ κ₀ A).state (l ++ [r]) r.loc 0 = 0 := by
  rw [Afix_snoc, if_pos hq]; exact fixS_zero _ _ _

theorem Afix_delta (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ)
    (ha : ∀ ρ : List (Request d k), ValidSeq ρ →
      A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a)
    (l : List (Request d k)) (hl : ValidSeq l) (t : ℕ) (ht : t < l.length)
    (hq : 1 ≤ (l[t]).quota ∧ 0 < (l[t]).h 0) :
    A.state (mods θ a w n₀ κ₀ (l.take (t + 1))) (l[t]).loc 0 ≤ 1 / 2 ^ t ∧
    A.state (mods θ a w n₀ κ₀ (l.take (t + 1))) (l[t]).loc 0 * (l[t]).hAt 1 ≤ 1 / 2 ^ t := by
  have hm := mods_valid θ a w n₀ κ₀ hθ hw hk l hl
  have htm : t < (mods θ a w n₀ κ₀ l).length := by rw [mods_length]; exact ht
  have hb := delta_bound A hw hA hθ a ha _ hm t htm
    (nfeas n₀ ((mods θ a w n₀ κ₀ l).take (t + 1))) (nfeas_feasible hk _ _)
  have hδ0 := state_nonneg A hA _ hm t htm
  rw [mods_take] at hb hδ0
  rw [mods_get θ a w n₀ κ₀ l t htm ht, modReq_h0 _ _ hq, modReq_loc,
    mods_nfeas_cost θ a w n₀ κ₀ hk, mods_qv] at hb
  have hδ : 0 ≤ A.state (mods θ a w n₀ κ₀ (l.take (t + 1))) (l[t]).loc 0 := hδ0 _ _
  have hBdef : Bval θ a w n₀ κ₀ (l.take (t + 1)) = θ * (intCost w (l.take (t + 1))
      (nfeas n₀ (l.take (t + 1))) + wmax w * quotaVariation κ₀ (l.take (t + 1))) + |a| + 1 := rfl
  have hB := Bval_nonneg θ a w n₀ κ₀ hθ hw (l.take (t + 1)) (validSeq_take hl _)
  have hHdef : Hval θ a w n₀ κ₀ (l.take t) (l[t]) =
      2 ^ t * (Bval θ a w n₀ κ₀ (l.take (t + 1)) + 1) * ((l[t]).hAt 1 + 1) := by
    unfold Hval; rw [← take_succ_eq' l t ht, List.length_take, min_eq_left ht.le]
  have hh1 : 0 ≤ (l[t]).hAt 1 := (hl _ (List.getElem_mem ht)).2.1 _
  have haa := le_abs_self a
  refine small_of_big (H := Hval θ a w n₀ κ₀ (l.take t) (l[t]))
    (B := Bval θ a w n₀ κ₀ (l.take (t + 1))) t (by linarith) hh1 hδ hHdef.ge ?_
  rw [hBdef]; linarith

theorem modReq_valid_at (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (l : List (Request d k))
    (hl : ValidSeq l) (t : ℕ) (ht : t < l.length) :
    (modReq (l[t]) (Hval θ a w n₀ κ₀ (l.take t) (l[t]))).Valid := by
  have hm := mods_valid θ a w n₀ κ₀ hθ hw hk l hl
  have htm : t < (mods θ a w n₀ κ₀ l).length := by rw [mods_length]; exact ht
  have := hm _ (List.getElem_mem htm)
  rwa [mods_get θ a w n₀ κ₀ l t htm ht] at this

theorem inner_feasible (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ) (l : List (Request d k)) (hl : ValidSeq l) (t : ℕ)
    (ht : t < l.length) :
    FracFeasible (A.state (mods θ a w n₀ κ₀ (l.take (t + 1)))) (l[t]).quota := by
  have hv : ValidSeq (l.take t ++ [l[t]]) := by rw [← take_succ_eq' l t ht]; exact validSeq_take hl _
  have hm := mods_valid θ a w n₀ κ₀ hθ hw hk _ hv
  rw [mods_snoc] at hm
  have hF := hA.2.1 _ _ hm
  rw [modReq_quota, ← mods_snoc, ← take_succ_eq' l t ht] at hF
  exact hF

theorem Afix_hit (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ)
    (ha : ∀ ρ : List (Request d k), ValidSeq ρ →
      A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a)
    (l : List (Request d k)) (hl : ValidSeq l) :
    (Afix θ a w n₀ κ₀ A).hitTotal l ≤ A.hitTotal (mods θ a w n₀ κ₀ l) + 2 := by
  unfold FracAlg.hitTotal
  rw [mods_length]
  have hterm : ∀ t ∈ range l.length,
      (((l[t]?).map fun r => hitCost r ((Afix θ a w n₀ κ₀ A).state (l.take (t + 1)))).getD 0) ≤
      ((((mods θ a w n₀ κ₀ l)[t]?).map fun r =>
        hitCost r (A.state ((mods θ a w n₀ κ₀ l).take (t + 1)))).getD 0) + (1 / 2 : ℝ) ^ t := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have htm : t < (mods θ a w n₀ κ₀ l).length := by rw [mods_length]; exact ht'
    rw [List.getElem?_eq_getElem ht', List.getElem?_eq_getElem htm]
    show hitCost (l[t]) ((Afix θ a w n₀ κ₀ A).state (l.take (t + 1))) ≤
      hitCost ((mods θ a w n₀ κ₀ l)[t]) (A.state ((mods θ a w n₀ κ₀ l).take (t + 1))) +
        (1 / 2 : ℝ) ^ t
    have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ t := by positivity
    have hX := inner_feasible θ a w n₀ κ₀ hk hθ hw A hA l hl t ht'
    rw [mods_take, mods_get θ a w n₀ κ₀ l t htm ht', take_succ_eq' l t ht', Afix_snoc,
      ← take_succ_eq' l t ht']
    split_ifs with hq
    · have hr' := modReq_valid_at θ a w n₀ κ₀ hk hθ hw l hl t ht'
      have hX' : FracFeasible (A.state (mods θ a w n₀ κ₀ (l.take (t + 1))))
          (modReq (l[t]) (Hval θ a w n₀ κ₀ (l.take t) (l[t]))).quota := by
        rw [modReq_quota]; exact hX
      have h1 := fixS_hit hk _ _ hq.1 hX _ hr'
      rw [modReq_loc] at h1
      have heq : hitCost (l[t]) (fixS (A.state (mods θ a w n₀ κ₀ (l.take (t + 1)))) (l[t]).loc
            (l[t]).quota) =
          hitCost (modReq (l[t]) (Hval θ a w n₀ κ₀ (l.take t) (l[t])))
            (fixS (A.state (mods θ a w n₀ κ₀ (l.take (t + 1)))) (l[t]).loc (l[t]).quota) := by
        unfold hitCost
        rw [modReq_loc]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : (j : ℕ) = 0
        · have : j = 0 := Fin.ext hj
          rw [this, fixS_zero]; simp
        · rw [modReq_h _ _ _ hj]
      have h1' : (modReq (l[t]) (Hval θ a w n₀ κ₀ (l.take t) (l[t]))).h ⟨1, by omega⟩ =
          (l[t]).hAt 1 := by
        rw [modReq_h _ _ _ (by simp)]
        unfold Request.hAt
        congr 1; ext; simp; omega
      rw [h1'] at h1
      have hd := (Afix_delta θ a w n₀ κ₀ hk hθ hw A hA ha l hl t ht' hq).2
      rw [one_div_pow]
      linarith
    · rw [modReq_of_zero _ _ hq]; linarith
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hs
  have hg := sum_geometric_two_le l.length
  linarith

theorem Afix_e (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ)
    (ha : ∀ ρ : List (Request d k), ValidSeq ρ →
      A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a)
    (l : List (Request d k)) (hl : ValidSeq l) (t : ℕ) (ht : t ≤ l.length) :
    moveCost w (A.state (mods θ a w n₀ κ₀ (l.take t))) ((Afix θ a w n₀ κ₀ A).state (l.take t)) ≤
      4 * wmax w * (1 / 2 : ℝ) ^ t := by
  have hwm := wmax_nonneg w hw
  cases t with
  | zero =>
    simp only [List.take_zero, Afix_nil, mods, List.mapIdx_nil, moveCost_self']
    positivity
  | succ s =>
    have hs : s < l.length := by omega
    have hX := inner_feasible θ a w n₀ κ₀ hk hθ hw A hA l hl s hs
    rw [take_succ_eq' l s hs, Afix_snoc, ← take_succ_eq' l s hs]
    split_ifs with hq
    · have h1 := fixS_move hk w hw _ (l[s]).loc _ hq.1 hX
      have hd := (Afix_delta θ a w n₀ κ₀ hk hθ hw A hA ha l hl s hs hq).1
      rw [← one_div_pow] at hd
      have e : 4 * wmax w * (1 / 2 : ℝ) ^ (s + 1) = 2 * wmax w * (1 / 2 : ℝ) ^ s := by
        rw [pow_succ]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ 2 * wmax w)
      linarith
    · rw [moveCost_self']; positivity

theorem Afix_move (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ)
    (ha : ∀ ρ : List (Request d k), ValidSeq ρ →
      A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a)
    (l : List (Request d k)) (hl : ValidSeq l) :
    (Afix θ a w n₀ κ₀ A).moveTotal w l ≤ A.moveTotal w (mods θ a w n₀ κ₀ l) + 16 * wmax w := by
  unfold FracAlg.moveTotal
  rw [mods_length]
  have hwm := wmax_nonneg w hw
  have hterm : ∀ t ∈ range l.length,
      moveCost w ((Afix θ a w n₀ κ₀ A).state (l.take t)) ((Afix θ a w n₀ κ₀ A).state (l.take (t + 1))) ≤
      moveCost w (A.state ((mods θ a w n₀ κ₀ l).take t)) (A.state ((mods θ a w n₀ κ₀ l).take (t + 1)))
        + 8 * wmax w * (1 / 2 : ℝ) ^ t := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [mods_take, mods_take]
    have e0 := Afix_e θ a w n₀ κ₀ hk hθ hw A hA ha l hl t ht'.le
    have e1 := Afix_e θ a w n₀ κ₀ hk hθ hw A hA ha l hl (t + 1) ht'
    have tr1 := moveCost_triangle w hw ((Afix θ a w n₀ κ₀ A).state (l.take t))
      (A.state (mods θ a w n₀ κ₀ (l.take t))) ((Afix θ a w n₀ κ₀ A).state (l.take (t + 1)))
    have tr2 := moveCost_triangle w hw (A.state (mods θ a w n₀ κ₀ (l.take t)))
      (A.state (mods θ a w n₀ κ₀ (l.take (t + 1)))) ((Afix θ a w n₀ κ₀ A).state (l.take (t + 1)))
    rw [moveCost_comm' w ((Afix θ a w n₀ κ₀ A).state (l.take t)) (A.state (mods θ a w n₀ κ₀ (l.take t)))] at tr1
    have hp : (1 / 2 : ℝ) ^ (t + 1) ≤ (1 / 2 : ℝ) ^ t :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ t)
    have hp2 := mul_le_mul_of_nonneg_left hp (by linarith : (0 : ℝ) ≤ 4 * wmax w)
    linarith
  have hs := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hg := sum_geometric_two_le l.length
  have := mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ 8 * wmax w)
  linarith

/-- **D7d-alloc**: the wrapped black box against any schedule that keeps a server at every
request with a positive quota. -/
theorem Afix_bounds (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ) (hγ : 0 ≤ γ)
    (ha : ∀ ρ : List (Request d k), ValidSeq ρ →
      A.hitTotal ρ ≤ θ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a ∧
      A.moveTotal w ρ ≤ γ * (optCost w n₀ ρ + wmax w * quotaVariation κ₀ ρ) + a)
    (l : List (Request d k)) (hl : ValidSeq l) (n : ℕ → Fin d → ℕ) (hn : IntFeasible n₀ l n)
    (hserve : ∀ s (hs : s < l.length), 1 ≤ (l[s]).quota ∧ 0 < (l[s]).h 0 → 1 ≤ n (s + 1) (l[s]).loc) :
    (Afix θ a w n₀ κ₀ A).hitTotal l ≤
        θ * (intCost w l n + wmax w * quotaVariation κ₀ l) + a + 2 ∧
      (Afix θ a w n₀ κ₀ A).moveTotal w l ≤
        γ * (intCost w l n + wmax w * quotaVariation κ₀ l) + a + 16 * wmax w := by
  have hm := mods_valid θ a w n₀ κ₀ hθ hw hk l hl
  have hn' : IntFeasible n₀ (mods θ a w n₀ κ₀ l) n := by
    refine ⟨hn.1, fun t ht => ?_⟩
    have ht' : t < l.length := by rwa [mods_length] at ht
    rw [mods_get θ a w n₀ κ₀ l t ht ht', modReq_quota]
    exact hn.2 t ht'
  have ho := optCost_le_int w hw n₀ _ hm n hn'
  rw [mods_intCost θ a w n₀ κ₀ hk l n hserve] at ho
  have hq := mods_qv θ a w n₀ κ₀ l
  obtain ⟨h1, h2⟩ := ha _ hm
  rw [hq] at h1 h2
  have hh := Afix_hit θ a w n₀ κ₀ hk hθ hw A hA (fun ρ hρ => (ha ρ hρ).1) l hl
  have hmv := Afix_move θ a w n₀ κ₀ hk hθ hw A hA (fun ρ hρ => (ha ρ hρ).1) l hl
  have e1 : θ * (optCost w n₀ (mods θ a w n₀ κ₀ l) + wmax w * quotaVariation κ₀ l) ≤
      θ * (intCost w l n + wmax w * quotaVariation κ₀ l) :=
    mul_le_mul_of_nonneg_left (by linarith) hθ
  have e2 : γ * (optCost w n₀ (mods θ a w n₀ κ₀ l) + wmax w * quotaVariation κ₀ l) ≤
      γ * (intCost w l n + wmax w * quotaVariation κ₀ l) :=
    mul_le_mul_of_nonneg_left (by linarith) hγ
  exact ⟨by linarith, by linarith⟩

end Wrap

end K17428


/-! D8d1 (17428d40, relay 8): the two ensemble-to-node comparisons used in the induction D8d.
(1) `int_Hsum_le_hit`: the expected child service costs `∑_i ∫ Hsum_{c_i}(κ_i^u)` are at most
the hit cost of the node algorithm on the node requests (Abel summation `abel_cake` + `int_h_Q`).
(2) `int_gsum_le_nmove`: `∑_i W(c_i) ∫ g(κ_i^u) ≤` the node algorithm's movement
(`int_abs_Q_sub`). Needs D8a D8b D8c D7a D7c D7e D7f D5c D5f D2. -/

namespace K17428

open Finset MeasureTheory intervalIntegral PolylogKServer.HST PolylogKServer.Allocation

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

theorem sum_Icc_telesc (h : ℕ → ℝ) (n : ℕ) : ∑ j ∈ Icc 1 n, (h j - h (j - 1)) = h n - h 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

theorem abel_cake {d k : ℕ} (y : FracState d k) (i : Fin d) (hs : ∑ j, y i j = 1) (h : ℕ → ℝ) :
    ∑ j : Fin (k + 1), h j * y i j =
      h 0 + ∑ j ∈ Icc 1 k, (h j - h (j - 1)) * (1 - cumul y i j) := by
  have e1 : ∀ j, 1 - cumul y i j = ∑ j' : Fin (k + 1), if j ≤ (j' : ℕ) then y i j' else 0 := by
    intro j
    unfold cumul
    rw [← hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hlt : (j' : ℕ) < j
    · rw [if_pos hlt, if_neg (by omega)]; ring
    · rw [if_neg hlt, if_pos (by omega)]; ring
  simp_rw [e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e2 : ∀ j' : Fin (k + 1), ∑ j ∈ Icc 1 k, (h j - h (j - 1)) *
      (if j ≤ (j' : ℕ) then y i j' else 0) = (h j' - h 0) * y i j' := by
    intro j'
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hf : (Icc 1 k).filter (fun j => j ≤ (j' : ℕ)) = Icc 1 (j' : ℕ) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have := j'.isLt
      omega
    rw [hf, ← Finset.sum_mul, sum_Icc_telesc]
  rw [Finset.sum_congr rfl fun j' _ => e2 j']
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hs]
  ring

theorem cumul_mono' {d k : ℕ} (y : FracState d k) (i : Fin d) (hy : ∀ j, 0 ≤ y i j) :
    ∀ a b : ℕ, a ≤ b → cumul y i a ≤ cumul y i b := by
  intro a b hab
  unfold cumul
  exact Finset.sum_le_sum fun j _ => by
    split_ifs with h1 h2 <;> first | exact le_rfl | exact hy j | (exfalso; omega)

theorem int_hit {d k : ℕ} (y : FracState d k) (i : Fin d) (hy : ∀ j, 0 ≤ y i j)
    (hs : ∑ j, y i j = 1) (h : ℕ → ℝ) :
    ∫ u in (0 : ℝ)..1, h (Qf (fun j => cumul y i j) k u) = ∑ j : Fin (k + 1), h j * y i j := by
  rw [abel_cake y i hs h, int_h_Q _ k (cumul_mono' y i hy)
    (fun j => ⟨cumul_nonneg' y i hy j, cumul_le_one y i hy hs j⟩) h]

theorem Qf_le_k (c : ℕ → ℝ) (k : ℕ) (u : ℝ) : Qf c k u ≤ k := by
  unfold Qf
  exact (Finset.card_filter_le _ _).trans (by simp)

section HV

variable (T : WTree V) (e : M ≃ T.Leaf) (r : ℕ → M) (st : V → ℕ → M → ℤ) (L : V → ℕ → M)

theorem hval_zero (hst0 : ∀ v m, st v 0 m = 0) (c : V) (κ' : ℕ → ℕ) (t : ℕ) (h0 : κ' t = 0) :
    hval T e c r (st c) κ' t = 0 := by
  unfold hval
  have : st c (κ' t) = fun _ => 0 := by rw [h0]; funext m; exact hst0 c m
  rw [this, Fopt_zero_state, Fopt_zero_state]; ring

theorem hval_out (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (hst0 : ∀ v m, st v 0 m = 0)
    (c : V) (κ' : ℕ → ℕ) (t : ℕ) (hr : r t ∉ Sp T e c) : hval T e c r (st c) κ' t = 0 := by
  rcases Nat.eq_zero_or_pos (κ' t) with h0 | hpos
  · exact hval_zero T e r st hst0 c κ' t h0
  cases t with
  | zero => simp [hval]
  | succ H =>
    unfold hval
    simp only [Nat.add_sub_cancel]
    obtain ⟨h0, hS, hp⟩ := st_ok T e st L hN c (κ' (H + 1)) hpos
    rw [Fopt_out T e _ r H _ (ITraj_nonempty _ r H _ h0 hS hp) hr]; ring

theorem hval_le_req (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (hst0 : ∀ v m, st v 0 m = 0)
    (p : V) (hd : 0 < (children T p).card) (k : ℕ) (κ κ' : ℕ → ℕ) (t : ℕ)
    (i : Fin (children T p).card) (hl : nloc T e p r t = some i) (hk : κ' t ≤ k) :
    hval T e (chv T p i) r (st (chv T p i)) κ' t ≤
      (nodeReq (k := k) hd (nloc T e p r) (nhf T e p r st) κ t).hAt (κ' t) := by
  rcases Nat.eq_zero_or_pos (κ' t) with h0 | hpos
  · rw [hval_zero T e r st hst0 _ κ' t h0, h0]
    have h1 := nodeReq_h0_pos (k := k) hd (nloc T e p r) (nhf T e p r st) κ
      (nhf_nonneg T e p r st L hN) t i hl
    have h2 : (nodeReq (k := k) hd (nloc T e p r) (nhf T e p r st) κ t).hAt 0 =
        (nodeReq (k := k) hd (nloc T e p r) (nhf T e p r st) κ t).h 0 := by
      unfold Request.hAt; congr 1
    rw [h2]; exact h1.le
  · rw [nodeReq_hAt_some hd (nloc T e p r) (nhf T e p r st) κ t i hl _ hpos hk]
    unfold hval nhf
    rw [max_eq_right hpos]

end HV

section Ens4

variable (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
  (B : ∀ p : V, FracAlg (children T p).card k) (L : V → ℕ → M)

theorem hitTotal_node (N : ℕ) (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card) :
    (B p).hitTotal (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) =
      ∑ t ∈ range N, hitCost (nodeReq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ
        (t + 1)) (xs T e k r st B p κ i0 (t + 1)) := by
  unfold FracAlg.hitTotal
  rw [nodeSeq_length]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have htl : t < (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N).length := by
    rw [nodeSeq_length]; exact ht'
  rw [List.getElem?_eq_getElem htl, nodeSeq_get _ _ _ κ N t htl, nodeSeq_take k _ _ _ κ N (t + 1) ht']
  rfl

theorem int_Hsum_le_hit (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (hst0 : ∀ v m, st v 0 m = 0)
    (N : ℕ) (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card)
    (hprob : ∀ s (i' : Fin (children T p).card),
      (∀ j, 0 ≤ xs T e k r st B p κ i0 s i' j) ∧ ∑ j, xs T e k r st B p κ i0 s i' j = 1) :
    ∑ i : Fin (children T p).card, ∫ u in (0 : ℝ)..1,
        Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u) ≤
      (B p).hitTotal (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) := by
  rw [hitTotal_node T e k r st B N p κ i0]
  have hx : ∀ i : Fin (children T p).card, ∀ s,
      xs T e k r st B p κ i s = xs T e k r st B p κ i0 s := fun _ _ => rfl
  -- swap the integral with the time sum
  have hswap : ∀ i : Fin (children T p).card, ∫ u in (0 : ℝ)..1,
      Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u) =
      ∑ t ∈ range N, ∫ u in (0 : ℝ)..1,
        hval T e (chv T p i) r (st (chv T p i)) (khist T e k r st B p κ i u) (t + 1) := by
    intro i
    unfold Hsum
    rw [intervalIntegral.integral_finsetSum]
    intro t ht
    have ht' := Finset.mem_range.1 ht
    exact hist_ii T e k r st B p κ i N (fun κ' => hval T e (chv T p i) r (st (chv T p i)) κ' (t + 1))
      (fun κ₁ κ₂ h => by unfold hval; rw [h (t + 1) (by omega)]) 0 1
  rw [Finset.sum_congr rfl fun i _ => hswap i, Finset.sum_comm]
  refine Finset.sum_le_sum fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  set req := nodeReq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ (t + 1) with hreq
  rcases hl : nloc T e p r (t + 1) with _ | i1
  · -- the request is outside `T(p)`: no child pays anything
    have h0 : ∀ i : Fin (children T p).card, ∫ u in (0 : ℝ)..1,
        hval T e (chv T p i) r (st (chv T p i)) (khist T e k r st B p κ i u) (t + 1) = 0 := by
      intro i
      have hr : r (t + 1) ∉ Sp T e (chv T p i) := fun h => by
        have := nloc_of_anc T e p r (t + 1) i h
        rw [hl] at this; simp at this
      simp [hval_out T e r st L hN hst0 _ _ _ hr]
    rw [Finset.sum_congr rfl fun i _ => h0 i, Finset.sum_const_zero]
    unfold hitCost
    refine Finset.sum_nonneg fun j _ => ?_
    have hh : req.h j = 0 := by rw [hreq]; simp [nodeReq, hl]
    rw [hh, zero_mul]
  · -- the request is in the subtree of child `i1`
    have hoth : ∀ i ∈ (Finset.univ : Finset (Fin (children T p).card)), i ≠ i1 →
        ∫ u in (0 : ℝ)..1,
          hval T e (chv T p i) r (st (chv T p i)) (khist T e k r st B p κ i u) (t + 1) = 0 := by
      intro i _ hne
      have hr : r (t + 1) ∉ Sp T e (chv T p i) := fun h => by
        have := nloc_of_anc T e p r (t + 1) i h
        rw [hl] at this; exact hne (Option.some.inj this).symm
      simp [hval_out T e r st L hN hst0 _ _ _ hr]
    rw [Finset.sum_eq_single i1 hoth (fun h => absurd (Finset.mem_univ _) h)]
    have hloc : req.loc = i1 := by
      rw [hreq]; exact nodeReq_loc _ _ _ κ _ i1 hl
    obtain ⟨hy, hs⟩ := hprob (t + 1) i1
    have hint := int_hit (xs T e k r st B p κ i0 (t + 1)) i1 hy hs (fun j => req.hAt j)
    have hcost : hitCost req (xs T e k r st B p κ i0 (t + 1)) =
        ∑ j : Fin (k + 1), req.hAt j * xs T e k r st B p κ i0 (t + 1) i1 j := by
      unfold hitCost
      rw [hloc]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold Request.hAt
      congr 2
      exact Fin.ext (by simp [Nat.min_eq_left (Nat.lt_succ_iff.1 j.isLt)])
    rw [hcost, ← hint]
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun u _ => ?_
    · exact hist_ii T e k r st B p κ i1 N
        (fun κ' => hval T e (chv T p i1) r (st (chv T p i1)) κ' (t + 1))
        (fun κ₁ κ₂ h => by unfold hval; rw [h (t + 1) (by omega)]) 0 1
    · exact hist_ii T e k r st B p κ i1 N (fun κ' => req.hAt (κ' (t + 1)))
        (fun κ₁ κ₂ h => by rw [h (t + 1) (by omega)]) 0 1
    · exact hval_le_req T e r st L hN hst0 p (Fin.pos i0) k κ _ (t + 1) i1 hl (Qf_le_k _ k u)

theorem int_gsum_le_nmove (N : ℕ) (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card)
    (hprob : ∀ s (i' : Fin (children T p).card),
      (∀ j, 0 ≤ xs T e k r st B p κ i0 s i' j) ∧ ∑ j, xs T e k r st B p κ i0 s i' j = 1) :
    ∑ i : Fin (children T p).card, T.W (chv T p i) *
        ∫ u in (0 : ℝ)..1, gsum N (khist T e k r st B p κ i u) ≤
      nmove T e k r st B N p κ := by
  rw [nmove_eq T e k r st B N p κ i0]
  unfold moveCost
  rw [Finset.sum_comm (s := range N)]
  refine Finset.sum_le_sum fun i _ => ?_
  have hmem : chv T p i ∈ inner T p := by
    rw [inner_split T p, Finset.mem_biUnion]
    exact ⟨_, chv_mem T p i, Finset.mem_insert_self _ _⟩
  have hW : 0 ≤ T.W (chv T p i) := W_nonneg_inner T p _ hmem
  have hc : ∀ s j, 0 ≤ cumul (xs T e k r st B p κ i0 s) i j ∧
      cumul (xs T e k r st B p κ i0 s) i j ≤ 1 := fun s j =>
    ⟨cumul_nonneg' _ i (hprob s i).1 j, cumul_le_one _ i (hprob s i).1 (hprob s i).2 j⟩
  unfold gsum
  rw [intervalIntegral.integral_finsetSum fun t _ =>
    hist_ii T e k r st B p κ i N
      (fun κ' => |((κ' (t + 1) : ℕ) : ℝ) - ((κ' t : ℕ) : ℝ)|)
      (fun κ₁ κ₂ h => by
        have ht := Finset.mem_range.1 ‹t ∈ range N›
        rw [h (t + 1) (by omega), h t (by omega)]) 0 1]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  unfold wch
  refine mul_le_mul_of_nonneg_left ?_ hW
  exact int_abs_Q_sub (fun j => cumul (xs T e k r st B p κ i0 (t + 1)) i j)
    (fun j => cumul (xs T e k r st B p κ i0 t) i j) k (hc (t + 1)) (hc t)

end Ens4

end K17428


/-! D8d2 (17428d40, relay 8): the comparison schedule at a node `p`. From any quota trajectory
`c` of `T(p)` for the history `κ` (cut to a serving configuration after time `N`), the child
counts `n s i = nsub (c s) (c_i)` form an integral schedule of the node requests that is
feasible, serves every marked request, and costs at most `(1 + 2/(σ-1)) · qcost c`
(`nodeSeq_intCost_split`, `thm31z` lower bound per child, `qcost_ge_split`). -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Allocation PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

theorem sum_children_fin' {β : Type} [AddCommMonoid β] (T : WTree V) (p : V) (F : V → β) :
    ∑ c ∈ children T p, F c = ∑ i : Fin (children T p).card, F (chv T p i) := by
  rw [← Finset.sum_coe_sort]
  exact (Fintype.sum_equiv (children T p).equivFin.symm _ _ (fun _ => rfl)).symm

section Cmp

variable (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
  (L : V → ℕ → M)

theorem nsub_le_sum (x : M → ℤ) (hx : ∀ m, 0 ≤ x m) (v : V) : nsub T e x v ≤ ∑ m, x m := by
  classical
  unfold nsub
  exact Finset.sum_le_sum fun m _ => by split_ifs <;> simp [hx m]

theorem le_nsub (x : M → ℤ) (hx : ∀ m, 0 ≤ x m) (v : V) (m : M) (hm : T.IsAnc v (e m : V)) :
    x m ≤ nsub T e x v := by
  classical
  unfold nsub
  have h := Finset.single_le_sum (f := fun m' => if T.IsAnc v (e m' : V) then x m' else 0)
    (fun m' _ => by split_ifs <;> simp [hx m']) (Finset.mem_univ m)
  simp only [if_pos hm] at h
  convert h using 1

theorem nsub_children (x : M → ℤ) (p : V) (hp : (children T p).Nonempty) :
    nsub T e x p = ∑ c ∈ children T p, nsub T e x c := by
  classical
  rw [nsub_split T e x p]
  have : cnt T e x p = 0 := by
    unfold cnt
    refine Finset.sum_eq_zero fun m _ => ?_
    split_ifs with h
    · exfalso
      obtain ⟨c, hc⟩ := hp
      obtain ⟨hr, hpc⟩ := (mem_children T).1 hc
      exact (e m).2 c hr (hpc.trans h.symm)
    · rfl
  rw [this, zero_add]

theorem sum_st (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (hst0 : ∀ v m, st v 0 m = 0)
    (v : V) (j : ℕ) : ∑ m, st v j m = j := by
  rw [((hN v).props j).2.2]; simp [hst0]

theorem Qopt_nonneg' (p : V) (H : ℕ) (st1 : ℕ → M → ℤ) (κ : ℕ → ℕ) :
    0 ≤ Qopt T e p r H st1 κ := by
  unfold Qopt
  exact Real.sInf_nonneg (by rintro _ ⟨c, _, rfl⟩; exact qcost_nonneg T e p H c)

/-- A trajectory cut after time `N` to the unit configuration at the request. -/
def cutc (N : ℕ) (c : ℕ → M → ℤ) : ℕ → M → ℤ :=
  fun s m => if s ≤ N then c s m else if m = r s then 1 else 0

theorem QTraj_cutc (p : V) (N : ℕ) (st1 : ℕ → M → ℤ) (κ : ℕ → ℕ) (c : ℕ → M → ℤ)
    (hc : QTraj T e p r N st1 κ c) : QTraj T e p r N st1 κ (cutc r N c) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  refine ⟨fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
    fun s hs1 hs hr => ?_⟩
  · simp only [cutc, if_pos (Nat.zero_le N)]; exact h1 m
  · simp only [cutc, if_pos hs]; exact h2 s hs m
  · simp only [cutc, if_pos hs]; exact h3 s hs m hm
  · simp only [cutc, if_pos hs]; exact h4 s hs
  · simp only [cutc, if_pos hs]; exact h5 s hs1 hs hr

theorem qcost_cutc (p : V) (N : ℕ) (c : ℕ → M → ℤ) :
    qcost T e p N (cutc r N c) = qcost T e p N c := by
  unfold qcost
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  have e1 : cutc r N c s = c s := funext fun m => by simp [cutc, show s ≤ N by omega]
  have e2 : cutc r N c (s + 1) = c (s + 1) :=
    funext fun m => by simp [cutc, show s + 1 ≤ N by omega]
  rw [e1, e2]

theorem cmp_bound (hk : 1 ≤ k) (σ : ℝ) (hσ : 1 < σ) (hT : T.IsWeightedHST σ)
    (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (hst0 : ∀ v m, st v 0 m = 0)
    (N : ℕ) (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card) (hκk : ∀ s, κ s ≤ k)
    (hinit : ∀ c ∈ children T p, ∀ m,
      st c (nsub T e (st p (κ 0)) c).toNat m = rst T e c (st p (κ 0)) m)
    (c0 : ℕ → M → ℤ) (hc0 : QTraj T e p r N (st p) κ c0) :
    ∃ n : ℕ → Fin (children T p).card → ℕ,
      IntFeasible (fun i => (nsub T e (st p (κ 0)) (chv T p i)).toNat)
        (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) n ∧
      (∀ s (hs : s < (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N).length),
        1 ≤ ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N)[s]).quota ∧
        0 < ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N)[s]).h 0 →
        1 ≤ n (s + 1) ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N)[s]).loc) ∧
      intCost (wch T p) (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) n ≤
        (1 + 2 / (σ - 1)) * qcost T e p N c0 := by
  classical
  have hd : 0 < (children T p).card := Fin.pos i0
  set cc := cutc r N c0 with hccdef
  have hc : QTraj T e p r N (st p) κ cc := QTraj_cutc T e r p N (st p) κ c0 hc0
  obtain ⟨h1, h2, h3, h4, h5⟩ := hc
  have hnn : ∀ s m, 0 ≤ cc s m := by
    intro s m
    by_cases hs : s ≤ N
    · exact h2 s hs m
    · simp only [hccdef, cutc, if_neg hs]; split_ifs <;> norm_num
  have htot : ∀ s, ∑ m, cc s m ≤ k := by
    intro s
    by_cases hs : s ≤ N
    · rw [h4 s hs, sum_st T e st L hN hst0]; exact_mod_cast hκk s
    · simp only [hccdef, cutc, if_neg hs]
      rw [Finset.sum_ite_eq' Finset.univ (r s) (fun _ => (1 : ℤ))]
      simp; exact_mod_cast hk
  have hserv : ∀ s, 1 ≤ s → ∀ v, T.IsAnc p v → T.IsAnc v (e (r s) : V) →
      1 ≤ nsub T e (cc s) v := by
    intro s hs1 v hpv hv
    refine le_trans ?_ (le_nsub T e (cc s) (hnn s) v (r s) hv)
    by_cases hs : s ≤ N
    · exact h5 s hs1 hs (isAnc_trans T hpv hv)
    · simp [hccdef, cutc, hs]
  set κ' : V → ℕ → ℕ := fun c s => (nsub T e (cc s) c).toNat with hκ'
  have hκ'z : ∀ c s, ((κ' c s : ℕ) : ℤ) = nsub T e (cc s) c := fun c s =>
    Int.toNat_of_nonneg (nsub_nonneg' T e (cc s) (hnn s) c)
  set n : ℕ → Fin (children T p).card → ℕ := fun s i => κ' (chv T p i) s with hn
  have hserve' : ∀ t i, nloc T e p r t = some i → 1 ≤ t → 1 ≤ n t i := by
    intro t i hl ht
    have h := hserv t ht (chv T p i) (isAnc_of_child T (chv_mem T p i) (isAnc_refl T _))
      (nloc_some T e p r t i hl)
    have := hκ'z (chv T p i) t
    simp only [hn]; omega
  have hnk : ∀ t i, n t i ≤ k := by
    intro t i
    have h := (nsub_le_sum T e (cc t) (hnn t) (chv T p i)).trans (htot t)
    have := hκ'z (chv T p i) t
    simp only [hn]; omega
  have hcc0 : cc 0 = st p (κ 0) := funext h1
  refine ⟨n, ⟨?_, fun t ht => ⟨fun i => hnk _ i, ?_⟩⟩, fun s hs hq => ?_, ?_⟩
  · funext i; simp only [hn, hκ', hcc0]
  · -- the child counts use exactly the quota
    rw [nodeSeq_get _ _ _ κ N t ht, nodeReq_quota]
    have hs : t + 1 ≤ N := by rw [nodeSeq_length] at ht; omega
    have hsum : ((∑ i, n (t + 1) i : ℕ) : ℤ) = ∑ m, cc (t + 1) m := by
      push_cast
      simp only [hn, hκ'z]
      rw [← sum_children_fin' T p (fun c => nsub T e (cc (t + 1)) c),
        ← nsub_children T e _ p (Finset.card_pos.1 hd)]
      exact nsub_of_anc T e p _ (h3 (t + 1) hs) (isAnc_refl T p)
    rw [h4 (t + 1) hs, sum_st T e st L hN hst0] at hsum
    exact_mod_cast hsum.le
  · -- marked requests are served
    have hs' : s < N := by rw [nodeSeq_length] at hs; exact hs
    rw [nodeSeq_get _ _ _ κ N s hs] at hq ⊢
    rcases hl : nloc T e p r (s + 1) with _ | i
    · rw [nodeReq_h0_none _ _ _ κ _ hl] at hq; exact absurd hq.2 (lt_irrefl 0)
    · rw [nodeReq_loc _ _ _ κ _ i hl]; exact hserve' (s + 1) i hl (by omega)
  · -- the cost
    rw [nodeSeq_intCost_split _ _ _ κ (wch T p) N n hserve' hnk (nhf_out T e p r st L hN)]
    have hσ1 : 0 < σ - 1 := by linarith
    have hq0 : 0 ≤ 2 / (σ - 1) := by positivity
    have hper : ∀ i : Fin (children T p).card,
        ∑ t ∈ range N, nhf T e p r st i (t + 1) (n (t + 1) i) +
          wch T p i * ∑ t ∈ range N, |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)| ≤
        (1 + 2 / (σ - 1)) * (T.W (chv T p i) * gvar T e (chv T p i) N cc +
          Qopt T e (chv T p i) r N (st (chv T p i)) (κ' (chv T p i))) := by
      intro i
      set c := chv T p i with hcdef
      have hcr : c ≠ T.root := ((mem_children T).1 (chv_mem T p i)).1
      have hW : 0 < T.W c := T.W_pos c hcr
      have hfeas : ∀ s, 1 ≤ s → s ≤ N → r s ∈ Sp T e c → 1 ≤ κ' c s := by
        intro s hs1 _ hr
        have h := hserv s hs1 c (isAnc_of_child T (chv_mem T p i) (isAnc_refl T _)) hr
        have := hκ'z c s
        omega
      have hD : ∀ m ∈ Sp T e c, dpath T e c m ≤ T.W c / (σ - 1) := fun m _ =>
        dpath_le_hst T e σ hσ hT m c hcr
      have h31 := (thm31z T e c r N (st c) (L c) (hN c) (hst0 c) _ hD (κ' c) hfeas).1
      have hHs : ∑ t ∈ range N, nhf T e p r st i (t + 1) (n (t + 1) i) =
          Hsum T e c r N (st c) (κ' c) := by
        unfold Hsum
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hz : 1 ≤ κ' c (t + 1)
        · rw [hcdef] at hz
          simp only [hn, hval, nhf, hcdef, Nat.add_sub_cancel]
          rw [max_eq_right hz]
        · have hz0 : κ' c (t + 1) = 0 := by omega
          have hl : nloc T e p r (t + 1) ≠ some i := fun hl => by
            have := hserve' (t + 1) i hl (by omega); simp only [hn, ← hcdef] at this; omega
          have hr : r (t + 1) ∉ Sp T e c := fun h => hl (nloc_of_anc T e p r _ i h)
          rw [nhf_out T e p r st L hN i _ _ hl, hval_out T e r st L hN hst0 c _ _ hr]
      have hg : wch T p i * ∑ t ∈ range N, |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)| =
          T.W c * gsum N (κ' c) := by
        unfold wch gsum; rfl
      have hgv : gvar T e c N cc = gsum N (κ' c) :=
        gvar_eq_gsum T e c N cc (κ' c) fun s _ => hκ'z c s
      have hQ := Qopt_nonneg' T e r c N (st c) (κ' c)
      have hg0 : 0 ≤ gsum N (κ' c) := Finset.sum_nonneg fun _ _ => abs_nonneg _
      rw [hHs, hg, hgv]
      have e2 : 2 * (T.W c / (σ - 1)) * gsum N (κ' c) = 2 / (σ - 1) * (T.W c * gsum N (κ' c)) := by
        ring
      have hm := mul_nonneg hq0 hQ
      nlinarith
    calc ∑ i : Fin (children T p).card, (∑ t ∈ range N, nhf T e p r st i (t + 1) (n (t + 1) i) +
          wch T p i * ∑ t ∈ range N, |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)|)
        ≤ ∑ i : Fin (children T p).card, (1 + 2 / (σ - 1)) *
            (T.W (chv T p i) * gvar T e (chv T p i) N cc +
              Qopt T e (chv T p i) r N (st (chv T p i)) (κ' (chv T p i))) :=
          Finset.sum_le_sum fun i _ => hper i
      _ = (1 + 2 / (σ - 1)) * ∑ c ∈ children T p,
            (T.W c * gvar T e c N cc + Qopt T e c r N (st c) (κ' c)) := by
          rw [← Finset.mul_sum, sum_children_fin' T p]
      _ ≤ (1 + 2 / (σ - 1)) * qcost T e p N cc := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine qcost_ge_split T e p r N (st p) κ cc ⟨h1, h2, h3, h4, h5⟩ st κ' ?_ ?_
          · intro c hc m
            simp only [hκ', hcc0]
            exact hinit c hc m
          · intro c _ s _
            rw [sum_st T e st L hN hst0]
            exact hκ'z c s
      _ = (1 + 2 / (σ - 1)) * qcost T e p N c0 := by rw [hccdef, qcost_cutc]

end Cmp

end K17428


/-! D8d3 (17428d40, relay 9): the INDUCTION BOUND of the ensemble (BBMN Lemma 18/19 shape).
Abstract node algorithms `B p` satisfying the Afix_bounds shape `hB` on every serving integral
schedule; a class `G` of histories closed under the quantile children (`hGc`).
`Tot N f p κ ≤ β f (Qopt_p κ + wmax(wch p) gsum N κ) + A f` with
`β (f+1) = (θ β f + (1 + μ β f) γ)(1 + q)`, `A (f+1) = (β f + 1 + μ β f) a + |V| A f`,
`μ = 3/(σ-1)`, `q = 2/(σ-1)`. -/

namespace K17428

open Finset MeasureTheory intervalIntegral PolylogKServer.HST PolylogKServer.Allocation
  PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]

theorem chv_ne_root (T : WTree V) (p : V) (i : Fin (children T p).card) :
    chv T p i ≠ T.root :=
  ((mem_children T).1 (chv_mem T p i)).1

theorem wmax_wch_le (T : WTree V) (σ : ℝ) (hσ : 1 < σ) (hT : T.IsWeightedHST σ) (c : V)
    (hc : c ≠ T.root) : wmax (wch T c) ≤ T.W c / (σ - 1) := by
  have hσ1 : 0 < σ - 1 := by linarith
  have hWc : 0 < T.W c := T.W_pos c hc
  unfold wmax
  refine Real.iSup_le (fun i => ?_) (div_nonneg hWc.le hσ1.le)
  obtain ⟨hne, hpar⟩ := (mem_children T).1 (chv_mem T c i)
  have h1 : σ * T.W (chv T c i) ≤ T.W (T.parent (chv T c i)) :=
    hT _ hne (by rw [hpar]; exact hc)
  rw [hpar] at h1
  have h2 : 0 < T.W (chv T c i) := T.W_pos _ hne
  show T.W (chv T c i) ≤ T.W c / (σ - 1)
  rw [le_div_iff₀ hσ1]
  nlinarith

theorem QTraj_nonempty_feas (T : WTree V) (e : M ≃ T.Leaf) (p : V) (r : ℕ → M) (H : ℕ)
    (st : ℕ → M → ℤ) (L : ℕ → M) (hN : Nested (Sp T e p) st L) (hst0 : ∀ m, st 0 m = 0)
    (κ : ℕ → ℕ) (hfeas : ∀ s, 1 ≤ s → s ≤ H → r s ∈ Sp T e p → 1 ≤ κ s) :
    ∃ c, QTraj T e p r H st κ c := by
  classical
  have hst0s : ∑ m, st 0 m = 0 := by simp [hst0]
  obtain ⟨c, hc0, hcn, hcS, hcsum, hcr⟩ :=
    QTraj_nonempty T e p r H st L hN (fun s => max 1 (κ s)) fun t _ => le_max_left _ _
  beta_reduce at hc0 hcsum
  refine ⟨cutT κ c, fun m => ?_, fun s hs m => ?_, fun s hs m hm => ?_, fun s hs => ?_,
    fun s h1 hs hr => ?_⟩
  · unfold cutT
    by_cases h : κ 0 = 0
    · rw [if_pos h, h, hst0]
    · rw [if_neg h, hc0 m, show max 1 (κ 0) = κ 0 by omega]
  · unfold cutT; split_ifs
    · exact le_rfl
    · exact hcn s hs m
  · unfold cutT; split_ifs
    · rfl
    · exact hcS s hs m hm
  · unfold cutT
    by_cases h : κ s = 0
    · rw [if_pos h, h, hst0s]; simp
    · rw [if_neg h, hcsum s hs, show max 1 (κ s) = κ s by omega]
  · have hk := hfeas s h1 hs hr
    unfold cutT
    rw [if_neg (by omega)]
    exact hcr s h1 hs hr

theorem le_of_forall_pos_mul (x R C : ℝ) (hC : 0 ≤ C)
    (h : ∀ η : ℝ, 0 < η → x ≤ R + C * η) : x ≤ R := by
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < (x - R) / (2 * (C + 1)) := div_pos (by linarith) (by linarith)
  have h1 := h _ hpos
  have h2 : C * ((x - R) / (2 * (C + 1))) ≤ (C + 1) * ((x - R) / (2 * (C + 1))) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  have hC1 : C + 1 ≠ 0 := by linarith
  have h3 : (C + 1) * ((x - R) / (2 * (C + 1))) = (x - R) / 2 := by
    field_simp <;> ring
  linarith

theorem gsum_nonneg (N : ℕ) (κ : ℕ → ℕ) : 0 ≤ gsum N κ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem gsum_congr' (N : ℕ) (κ₁ κ₂ : ℕ → ℕ) (h : ∀ s ≤ N, κ₁ s = κ₂ s) :
    gsum N κ₁ = gsum N κ₂ := by
  unfold gsum
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < N := Finset.mem_range.1 hs
  rw [h s (by omega), h (s + 1) (by omega)]

theorem Hsum_congr' (T : WTree V) (e : M ≃ T.Leaf) (p : V) (r : ℕ → M) (N : ℕ)
    (st : ℕ → M → ℤ) (κ₁ κ₂ : ℕ → ℕ) (h : ∀ s ≤ N, κ₁ s = κ₂ s) :
    Hsum T e p r N st κ₁ = Hsum T e p r N st κ₂ := by
  unfold Hsum hval
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s < N := Finset.mem_range.1 hs
  rw [h (s + 1) (by omega)]

/-- The growth constants of the induction. -/
noncomputable def betaF (θ γ μ q : ℝ) : ℕ → ℝ
  | 0 => 0
  | f + 1 => (θ * betaF θ γ μ q f + (1 + μ * betaF θ γ μ q f) * γ) * (1 + q)

noncomputable def AF (a θ γ μ q nV : ℝ) : ℕ → ℝ
  | 0 => 0
  | f + 1 => (betaF θ γ μ q f + 1 + μ * betaF θ γ μ q f) * a + nV * AF a θ γ μ q nV f

theorem betaF_nonneg (θ γ μ q : ℝ) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hq : 0 ≤ q) :
    ∀ f, 0 ≤ betaF θ γ μ q f := by
  intro f
  induction f with
  | zero => exact le_rfl
  | succ f ih =>
    show 0 ≤ (θ * betaF θ γ μ q f + (1 + μ * betaF θ γ μ q f) * γ) * (1 + q)
    have h1 : 0 ≤ 1 + μ * betaF θ γ μ q f := by linarith [mul_nonneg hμ ih]
    exact mul_nonneg (add_nonneg (mul_nonneg hθ ih) (mul_nonneg h1 hγ)) (by linarith)

theorem AF_nonneg (a θ γ μ q nV : ℝ) (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hq : 0 ≤ q) (hnV : 0 ≤ nV) : ∀ f, 0 ≤ AF a θ γ μ q nV f := by
  intro f
  induction f with
  | zero => exact le_rfl
  | succ f ih =>
    show 0 ≤ (betaF θ γ μ q f + 1 + μ * betaF θ γ μ q f) * a + nV * AF a θ γ μ q nV f
    have hb := betaF_nonneg θ γ μ q hθ hγ hμ hq f
    have h1 : 0 ≤ betaF θ γ μ q f + 1 + μ * betaF θ γ μ q f := by
      linarith [mul_nonneg hμ hb]
    exact add_nonneg (mul_nonneg h1 ha) (mul_nonneg hnV ih)

section Ind

variable (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (r : ℕ → M) (st : V → ℕ → M → ℤ)
  (B : ∀ p : V, FracAlg (children T p).card k) (L : V → ℕ → M)

/-- D8d3: the induction bound on the total ensemble movement below `p`. -/
theorem tot_bound (hk : 1 ≤ k) (σ : ℝ) (hσ : 1 < σ) (hT : T.IsWeightedHST σ)
    (hN : ∀ v, Nested (Sp T e v) (st v) (L v)) (hst0 : ∀ v m, st v 0 m = 0)
    (N : ℕ) (θ γ a μ q : ℝ) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (hμe : μ = 3 / (σ - 1)) (hqe : q = 2 / (σ - 1))
    (G : V → (ℕ → ℕ) → Prop)
    (hGf : ∀ p κ, G p κ → ∀ s, 1 ≤ s → s ≤ N → r s ∈ Sp T e p → 1 ≤ κ s)
    (hGk : ∀ p κ, G p κ → ∀ s, κ s ≤ k)
    (hGi : ∀ p κ, G p κ → ∀ c ∈ children T p, ∀ m,
      st c (nsub T e (st p (κ 0)) c).toNat m = rst T e c (st p (κ 0)) m)
    (hGc : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ), G p κ →
      u ∈ Set.Ioo (0 : ℝ) 1 → G (chv T p i) (khist T e k r st B p κ i u))
    (hprob : ∀ p κ, G p κ → ∀ (i0 : Fin (children T p).card) s (i' : Fin (children T p).card),
      (∀ j, 0 ≤ xs T e k r st B p κ i0 s i' j) ∧ ∑ j, xs T e k r st B p κ i0 s i' j = 1)
    (hB : ∀ p κ, G p κ → ∀ (i0 : Fin (children T p).card)
      (n : ℕ → Fin (children T p).card → ℕ),
      IntFeasible (fun i => (nsub T e (st p (κ 0)) (chv T p i)).toNat)
        (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) n →
      (∀ s (hs : s < (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N).length),
        1 ≤ ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N)[s]).quota ∧
        0 < ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N)[s]).h 0 →
        1 ≤ n (s + 1) ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N)[s]).loc) →
      (B p).hitTotal (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) ≤
          θ * (intCost (wch T p) (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) n
            + wmax (wch T p) * gsum N κ) + a ∧
        nmove T e k r st B N p κ ≤
          γ * (intCost (wch T p) (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r st) κ N) n
            + wmax (wch T p) * gsum N κ) + a) :
    ∀ (f : ℕ) (p : V) (κ : ℕ → ℕ), G p κ →
      Tot T e k r st B N f p κ ≤
        betaF θ γ μ q f * (Qopt T e p r N (st p) κ + wmax (wch T p) * gsum N κ) +
          AF a θ γ μ q (Fintype.card V) f := by
  have hσ1 : 0 < σ - 1 := by linarith
  have hμ0 : 0 ≤ μ := by rw [hμe]; exact div_nonneg (by norm_num) hσ1.le
  have hq0 : 0 ≤ q := by rw [hqe]; exact div_nonneg (by norm_num) hσ1.le
  have hnV : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hβ := betaF_nonneg θ γ μ q hθ hγ hμ0 hq0
  have hA := AF_nonneg a θ γ μ q (Fintype.card V) ha hθ hγ hμ0 hq0 hnV
  have hwm0 : ∀ p, 0 ≤ wmax (wch T p) := fun p =>
    wmax_nonneg _ fun i => T.W_pos _ (chv_ne_root T p i)
  have hR0 : ∀ f p κ, 0 ≤ betaF θ γ μ q f * (Qopt T e p r N (st p) κ +
      wmax (wch T p) * gsum N κ) + AF a θ γ μ q (Fintype.card V) f := fun f p κ =>
    add_nonneg (mul_nonneg (hβ f) (add_nonneg (Qopt_nonneg' T e r p N (st p) κ)
      (mul_nonneg (hwm0 p) (gsum_nonneg N κ)))) (hA f)
  intro f
  induction f with
  | zero =>
    intro p κ _
    exact hR0 0 p κ
  | succ f ih =>
    intro p κ hG
    by_cases hd : (children T p).card = 0
    · have h0 : Tot T e k r st B N (f + 1) p κ = 0 := by
        rw [Tot, nmove_nonneg_of_empty T e k r st B N p κ hd, zero_add]
        refine Finset.sum_eq_zero fun i _ => ?_
        exact absurd i.2 (by omega)
      rw [h0]; exact hR0 _ p κ
    have hpos : 0 < (children T p).card := Nat.pos_of_ne_zero hd
    have hp := hprob p κ hG ⟨0, hpos⟩
    have hβf := hβ f
    have hAf := hA f
    -- per-child bound
    have hchild : ∀ i : Fin (children T p).card,
        ∫ u in (0 : ℝ)..1, Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) ≤
          betaF θ γ μ q f * (∫ u in (0 : ℝ)..1,
            Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u)) +
          betaF θ γ μ q f * μ * (T.W (chv T p i) *
            ∫ u in (0 : ℝ)..1, gsum N (khist T e k r st B p κ i u)) +
          AF a θ γ μ q (Fintype.card V) f := by
      intro i
      have hHi : IntervalIntegrable (fun u =>
          Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u)) volume 0 1 :=
        hist_ii T e k r st B p κ i N (fun κ' => Hsum T e (chv T p i) r N (st (chv T p i)) κ')
          (fun κ₁ κ₂ h => Hsum_congr' T e (chv T p i) r N (st (chv T p i)) κ₁ κ₂ h) 0 1
      have hgi : IntervalIntegrable (fun u => gsum N (khist T e k r st B p κ i u)) volume 0 1 :=
        hist_ii T e k r st B p κ i N (fun κ' => gsum N κ') (fun κ₁ κ₂ h => gsum_congr' N κ₁ κ₂ h) 0 1
      have hI1 : IntervalIntegrable (fun u => betaF θ γ μ q f *
          Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u)) volume 0 1 :=
        hHi.const_mul _
      have hI2 : IntervalIntegrable (fun u => betaF θ γ μ q f * μ *
          (T.W (chv T p i) * gsum N (khist T e k r st B p κ i u))) volume 0 1 :=
        (hgi.const_mul _).const_mul _
      have hpt : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
          Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) ≤
            betaF θ γ μ q f *
                Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u) +
              betaF θ γ μ q f * μ * (T.W (chv T p i) * gsum N (khist T e k r st B p κ i u)) +
              AF a θ γ μ q (Fintype.card V) f := by
        intro u hu
        have hGu := hGc p κ i u hG hu
        have hcr := chv_ne_root T p i
        generalize khist T e k r st B p κ i u = κu at hGu ⊢
        generalize chv T p i = c at hGu hcr ⊢
        have h1 := ih c κu hGu
        have hD : ∀ m ∈ Sp T e c, dpath T e c m ≤ T.W c / (σ - 1) :=
          fun m _ => dpath_le_hst T e σ hσ hT m c hcr
        have h2 := (thm31z T e c r N (st c) (L c) (hN c) (hst0 c) _ hD κu (hGf c κu hGu)).2
        have h3 := mul_le_mul_of_nonneg_right (wmax_wch_le T σ hσ hT c hcr) (gsum_nonneg N κu)
        have h5 : Qopt T e c r N (st c) κu + wmax (wch T c) * gsum N κu ≤
            Hsum T e c r N (st c) κu + μ * (T.W c * gsum N κu) := by
          have e5 : μ * (T.W c * gsum N κu) =
              2 * (T.W c / (σ - 1)) * gsum N κu + T.W c / (σ - 1) * gsum N κu := by
            rw [hμe]; ring
          rw [e5]; linarith
        have h6 := mul_le_mul_of_nonneg_left h5 hβf
        linarith
      calc ∫ u in (0 : ℝ)..1, Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u)
          ≤ ∫ u in (0 : ℝ)..1, (betaF θ γ μ q f *
                Hsum T e (chv T p i) r N (st (chv T p i)) (khist T e k r st B p κ i u) +
              betaF θ γ μ q f * μ * (T.W (chv T p i) * gsum N (khist T e k r st B p κ i u)) +
              AF a θ γ μ q (Fintype.card V) f) :=
            intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
              (Tot_ii T e k r st B N f p κ i 0 1) ((hI1.add hI2).add intervalIntegrable_const) hpt
        _ = _ := by
            rw [intervalIntegral.integral_add (hI1.add hI2) intervalIntegrable_const,
              intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const]
            simp
    -- sum over the children
    have hsum : ∑ i : Fin (children T p).card,
        ∫ u in (0 : ℝ)..1, Tot T e k r st B N f (chv T p i) (khist T e k r st B p κ i u) ≤
          betaF θ γ μ q f *
              (B p).hitTotal (nodeSeq (k := k) (Fin.pos (⟨0, hpos⟩ : Fin (children T p).card))
                (nloc T e p r) (nhf T e p r st) κ N) +
            betaF θ γ μ q f * μ * nmove T e k r st B N p κ +
            (Fintype.card V : ℝ) * AF a θ γ μ q (Fintype.card V) f := by
      refine (Finset.sum_le_sum fun i _ => hchild i).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h1 := int_Hsum_le_hit T e k r st B L hN hst0 N p κ ⟨0, hpos⟩ hp
      have h2 := int_gsum_le_nmove T e k r st B N p κ ⟨0, hpos⟩ hp
      have h3 : ((children T p).card : ℝ) ≤ Fintype.card V := by
        exact_mod_cast Finset.card_le_univ _
      have h4 := mul_le_mul_of_nonneg_left h1 hβf
      have h5 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hβf hμ0)
      have h6 := mul_le_mul_of_nonneg_right h3 hAf
      linarith
    -- near-optimal comparison schedules
    have hne := QTraj_nonempty_feas T e p r N (st p) (L p) (hN p) (hst0 p) κ (hGf p κ hG)
    have hC : 0 ≤ (θ * betaF θ γ μ q f + (1 + μ * betaF θ γ μ q f) * γ) * (1 + q) := by
      have h1 : 0 ≤ 1 + μ * betaF θ γ μ q f := by linarith [mul_nonneg hμ0 hβf]
      exact mul_nonneg (add_nonneg (mul_nonneg hθ hβf) (mul_nonneg h1 hγ)) (by linarith)
    simp only [betaF, AF]
    refine le_of_forall_pos_mul _ _ _ hC fun η hη => ?_
    obtain ⟨c0, hc0⟩ := hne
    have hlt : Qopt T e p r N (st p) κ < Qopt T e p r N (st p) κ + η := by linarith
    obtain ⟨_, ⟨c, hc, rfl⟩, hcl⟩ := exists_lt_of_csInf_lt
      (⟨_, c0, hc0, rfl⟩ : (qcost T e p N '' {c | QTraj T e p r N (st p) κ c}).Nonempty) hlt
    obtain ⟨n, hnf, hns, hnc⟩ := cmp_bound T e k r st L hk σ hσ hT hN hst0 N p κ ⟨0, hpos⟩
      (hGk p κ hG) (hGi p κ hG) c hc
    obtain ⟨hh, hm⟩ := hB p κ hG ⟨0, hpos⟩ n hnf hns
    rw [← hqe] at hnc
    have hwg := mul_nonneg (hwm0 p) (gsum_nonneg N κ)
    have hX : intCost (wch T p) (nodeSeq (k := k) (Fin.pos (⟨0, hpos⟩ : Fin (children T p).card))
          (nloc T e p r) (nhf T e p r st) κ N) n + wmax (wch T p) * gsum N κ ≤
        (1 + q) * (Qopt T e p r N (st p) κ + wmax (wch T p) * gsum N κ) + (1 + q) * η := by
      have h1 := mul_le_mul_of_nonneg_left hcl.le (show (0 : ℝ) ≤ 1 + q by linarith)
      have h2 := mul_nonneg hq0 hwg
      linarith
    have hX' := mul_le_mul_of_nonneg_left hX
      (add_nonneg (mul_nonneg hθ hβf) (mul_nonneg (show 0 ≤ 1 + μ * betaF θ γ μ q f by
        linarith [mul_nonneg hμ0 hβf]) hγ))
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1 + μ * betaF θ γ μ q f by
        linarith [mul_nonneg hμ0 hβf])
    have hh' := mul_le_mul_of_nonneg_left hh hβf
    rw [Tot]
    linarith

end Ind

end K17428


/-! D9f (17428d40, relay 9): the constants. With `ε = 1/ℓ`, `θ = 1 + ε`, `γ = c₀ log(kℓ)`,
`μ = 3/(σ-1)`, `q = 2/(σ-1)` and `σ ≥ (108 c₀ + 8) ℓ log(kℓ)`, the growth constant of
`tot_bound` after `ℓ` levels is at most `(108 c₀ + 8) ℓ log(kℓ)`. Needs `betaF` (D8d3). -/

namespace K17428

theorem one_add_inv_pow_le (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (1 + 1 / (ℓ : ℝ)) ^ ℓ ≤ 3 := by
  have hℓ0 : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : 1 + 1 / (ℓ : ℝ) ≤ Real.exp (1 / ℓ) := by
    have := Real.add_one_le_exp (1 / (ℓ : ℝ)); linarith
  have h0 : 0 ≤ 1 + 1 / (ℓ : ℝ) := by positivity
  calc (1 + 1 / (ℓ : ℝ)) ^ ℓ ≤ Real.exp (1 / ℓ) ^ ℓ := pow_le_pow_left₀ h0 h1 ℓ
    _ = Real.exp ((ℓ : ℝ) * (1 / ℓ)) := (Real.exp_nat_mul _ ℓ).symm
    _ = Real.exp 1 := by rw [mul_one_div_cancel hℓ0]
    _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith

theorem betaF_le (γ q ε μ : ℝ) (ℓ : ℕ) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hε : 0 ≤ ε) (hμ : 0 ≤ μ)
    (hsmall : ∀ x, 0 ≤ x → x ≤ 2 * γ * (1 + q) * ℓ * ((1 + ε) * (1 + q)) ^ ℓ → μ * x ≤ 1) :
    ∀ f, f ≤ ℓ → betaF (1 + ε) γ μ q f ≤ 2 * γ * (1 + q) * f * ((1 + ε) * (1 + q)) ^ f := by
  have hlam : 1 ≤ (1 + ε) * (1 + q) := by nlinarith
  have hl0 : 0 ≤ (1 + ε) * (1 + q) := by linarith
  have hc0 : 0 ≤ 2 * γ * (1 + q) := by nlinarith
  intro f
  induction f with
  | zero => intro _; simp [betaF]
  | succ f ih =>
    intro hf
    have hx0 := betaF_nonneg (1 + ε) γ μ q (by linarith) hγ hμ hq f
    have hx := ih (by omega)
    have hpow : ((1 + ε) * (1 + q)) ^ f ≤ ((1 + ε) * (1 + q)) ^ ℓ :=
      pow_le_pow_right₀ hlam (by omega)
    have hfl : (f : ℝ) ≤ ℓ := by exact_mod_cast (show f ≤ ℓ by omega)
    have hm1 : 2 * γ * (1 + q) * f * ((1 + ε) * (1 + q)) ^ f ≤
        2 * γ * (1 + q) * ℓ * ((1 + ε) * (1 + q)) ^ ℓ := by
      have a1 := mul_le_mul_of_nonneg_left hfl hc0
      have a2 := mul_le_mul a1 hpow (pow_nonneg hl0 _)
        (mul_nonneg hc0 (Nat.cast_nonneg _))
      exact a2
    have hμx := hsmall _ hx0 (hx.trans hm1)
    show ((1 + ε) * betaF (1 + ε) γ μ q f + (1 + μ * betaF (1 + ε) γ μ q f) * γ) * (1 + q) ≤ _
    have e1 : ((1 + ε) * betaF (1 + ε) γ μ q f + (1 + μ * betaF (1 + ε) γ μ q f) * γ) * (1 + q) =
        ((1 + ε) * (1 + q)) * betaF (1 + ε) γ μ q f +
          (1 + μ * betaF (1 + ε) γ μ q f) * (γ * (1 + q)) := by ring
    have h1 := mul_le_mul_of_nonneg_left hx hl0
    have h2 := mul_le_mul_of_nonneg_right (show 1 + μ * betaF (1 + ε) γ μ q f ≤ 2 by linarith)
      (show 0 ≤ γ * (1 + q) by nlinarith)
    have h3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hlam : 1 ≤ ((1 + ε) * (1 + q)) ^ (f + 1)) hc0
    rw [e1]
    push_cast
    have e2 : ((1 + ε) * (1 + q)) * (2 * γ * (1 + q) * f * ((1 + ε) * (1 + q)) ^ f) =
        2 * γ * (1 + q) * f * ((1 + ε) * (1 + q)) ^ (f + 1) := by ring
    linarith

theorem betaF_final (c₀ : ℝ) (hc₀ : 0 < c₀) (k ℓ : ℕ) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (σ : ℝ)
    (hσ : (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) ≤ σ) :
    1 < σ ∧ betaF (1 + 1 / (ℓ : ℝ)) (c₀ * Real.log (k * ℓ)) (3 / (σ - 1)) (2 / (σ - 1)) ℓ ≤
      (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) := by
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkl : (2 : ℝ) ≤ k * ℓ := by nlinarith
  have hL : 1 / 2 ≤ Real.log (k * ℓ) := by
    have h2 := Real.log_two_gt_d9
    have h3 := Real.log_le_log (by norm_num) hkl
    linarith
  have hγ : 0 ≤ c₀ * Real.log (k * ℓ) := mul_nonneg hc₀.le (by linarith)
  have hσ' : 108 * (c₀ * Real.log (k * ℓ)) * ℓ + 4 * ℓ ≤ σ := by
    have a1 := mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 8 * ℓ by linarith)
    have e : (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) =
        108 * (c₀ * Real.log (k * ℓ)) * ℓ + 8 * ℓ * Real.log (k * ℓ) := by ring
    linarith
  have hγl : 0 ≤ 108 * (c₀ * Real.log (k * ℓ)) * ℓ := by
    have := mul_nonneg hγ (show (0 : ℝ) ≤ ℓ by linarith); linarith
  have hσ1 : 0 < σ - 1 := by linarith
  refine ⟨by linarith, ?_⟩
  have hq0 : 0 ≤ 2 / (σ - 1) := div_nonneg (by norm_num) hσ1.le
  have hμ0 : 0 ≤ 3 / (σ - 1) := div_nonneg (by norm_num) hσ1.le
  have hε0 : 0 ≤ 1 / (ℓ : ℝ) := by positivity
  have hqℓ : 2 / (σ - 1) ≤ 1 / (ℓ : ℝ) := by
    rw [div_le_div_iff₀ hσ1 (by linarith)]; linarith
  have hε1 : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hℓ1
  have hlam : (1 + 1 / (ℓ : ℝ)) * (1 + 2 / (σ - 1)) ≤ (1 + 1 / (ℓ : ℝ)) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hlam0 : 0 ≤ (1 + 1 / (ℓ : ℝ)) * (1 + 2 / (σ - 1)) := by positivity
  have hpw : ((1 + 1 / (ℓ : ℝ)) * (1 + 2 / (σ - 1))) ^ ℓ ≤ 9 := by
    calc ((1 + 1 / (ℓ : ℝ)) * (1 + 2 / (σ - 1))) ^ ℓ ≤ ((1 + 1 / (ℓ : ℝ)) ^ 2) ^ ℓ :=
          pow_le_pow_left₀ hlam0 hlam ℓ
      _ = ((1 + 1 / (ℓ : ℝ)) ^ ℓ) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ 3 ^ 2 := pow_le_pow_left₀ (by positivity) (one_add_inv_pow_le ℓ hℓ) 2
      _ = 9 := by norm_num
  -- the a-priori bound 36 γ ℓ
  have hB0 : 2 * (c₀ * Real.log (k * ℓ)) * (1 + 2 / (σ - 1)) * ℓ *
      ((1 + 1 / (ℓ : ℝ)) * (1 + 2 / (σ - 1))) ^ ℓ ≤ 36 * (c₀ * Real.log (k * ℓ)) * ℓ := by
    have a0 : 0 ≤ 2 * (c₀ * Real.log (k * ℓ)) * ℓ := by
      have := mul_nonneg hγ (show (0 : ℝ) ≤ ℓ by linarith); linarith
    have a1 : 2 * (c₀ * Real.log (k * ℓ)) * (1 + 2 / (σ - 1)) * ℓ ≤
        2 * (c₀ * Real.log (k * ℓ)) * 2 * ℓ := by
      have := mul_le_mul_of_nonneg_left (show 1 + 2 / (σ - 1) ≤ 2 by linarith) a0
      nlinarith
    have a2 := mul_le_mul a1 hpw (pow_nonneg hlam0 _) (by nlinarith)
    nlinarith
  have hsmall : ∀ x, 0 ≤ x → x ≤ 2 * (c₀ * Real.log (k * ℓ)) * (1 + 2 / (σ - 1)) * ℓ *
      ((1 + 1 / (ℓ : ℝ)) * (1 + 2 / (σ - 1))) ^ ℓ → 3 / (σ - 1) * x ≤ 1 := by
    intro x hx0 hx
    have hx' := hx.trans hB0
    rw [div_mul_eq_mul_div, div_le_one hσ1]
    linarith
  have hb := betaF_le (c₀ * Real.log (k * ℓ)) (2 / (σ - 1)) (1 / (ℓ : ℝ)) (3 / (σ - 1)) ℓ
    hγ hq0 hε0 hμ0 hsmall ℓ le_rfl
  have e : (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) =
      36 * (c₀ * Real.log (k * ℓ)) * ℓ + (72 * c₀ * ℓ * Real.log (k * ℓ) + 8 * ℓ * Real.log (k * ℓ)) := by
    ring
  have hrest : 0 ≤ 72 * c₀ * ℓ * Real.log (k * ℓ) + 8 * ℓ * Real.log (k * ℓ) := by
    have h1 : 0 ≤ ℓ * Real.log (k * ℓ) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ c₀ * (ℓ * Real.log (k * ℓ)) := mul_nonneg hc₀.le h1
    nlinarith
  linarith

end K17428


/-! D9a (17428d40, relay 9, part 1): every vertex has a leaf below it (needed to build the
nested prefix families `L v`, which must stay inside `Sp v`). Standalone. -/

namespace K17428

open PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type}

theorem exists_leaf_below (T : WTree V) (e : M ≃ T.Leaf) (v : V) : ∃ m : M, T.IsAnc v (e m : V) := by
  classical
  have key : ∀ n : ℕ, ∀ v : V, Finset.univ.sup T.depth - T.depth v ≤ n →
      ∃ m : M, T.IsAnc v (e m : V) := by
    intro n
    induction n with
    | zero =>
      intro v hv
      by_cases hl : T.IsLeaf v
      · exact ⟨e.symm ⟨v, hl⟩, ⟨0, by simp⟩⟩
      · exfalso
        simp only [WTree.IsLeaf, not_forall, not_not] at hl
        obtain ⟨u, hu, hpar⟩ := hl
        have hd := T.depth_parent u hu
        rw [hpar] at hd
        have hle : T.depth u ≤ Finset.univ.sup T.depth := Finset.le_sup (Finset.mem_univ u)
        omega
    | succ n ih =>
      intro v hv
      by_cases hl : T.IsLeaf v
      · exact ⟨e.symm ⟨v, hl⟩, ⟨0, by simp⟩⟩
      · simp only [WTree.IsLeaf, not_forall, not_not] at hl
        obtain ⟨u, hu, hpar⟩ := hl
        have hd := T.depth_parent u hu
        rw [hpar] at hd
        obtain ⟨m, i, hi⟩ := ih u (by omega)
        refine ⟨m, i + 1, ?_⟩
        rw [Function.iterate_succ_apply', hi, hpar]
  exact key _ v le_rfl


section Init

variable [Fintype M] [DecidableEq M] (T : WTree V) (e : M ≃ T.Leaf) {k : ℕ} (C₀ : Fin k → M)

open Classical in
/-- Indices of the initial servers inside `T(v)`. -/
noncomputable def iS (v : V) : Finset (Fin k) := Finset.univ.filter (fun i => C₀ i ∈ Sp T e v)

/-- Initial number of servers inside `T(v)`. -/
noncomputable def iN (v : V) : ℕ := (iS T e C₀ v).card

/-- A fixed leaf below `v`. -/
noncomputable def iLeaf (v : V) : M := Classical.choose (exists_leaf_below T e v)

/-- The nested prefix order at `v`: initial servers of `T(v)` first, then a parking leaf. -/
noncomputable def iL (v : V) (j : ℕ) : M :=
  if h : j < iN T e C₀ v then C₀ ((iS T e C₀ v).orderIsoOfFin rfl ⟨j, h⟩) else iLeaf T e v

/-- Nested prefix starts at `v`. -/
noncomputable def iSt (v : V) (j : ℕ) (m : M) : ℤ :=
  ∑ j' ∈ Finset.range j, if iL T e C₀ v j' = m then 1 else 0

open Classical in
/-- Indicator of the initial configuration. -/
noncomputable def iInd (m : M) : ℤ := if ∃ i, C₀ i = m then 1 else 0

theorem iL_mem (v : V) (j : ℕ) : iL T e C₀ v j ∈ Sp T e v := by
  classical
  unfold iL
  split_ifs with h
  · have := ((iS T e C₀ v).orderIsoOfFin rfl ⟨j, h⟩).2
    unfold iS at this
    exact (Finset.mem_filter.1 this).2
  · exact Classical.choose_spec (exists_leaf_below T e v)

theorem iSt_zero (v : V) (m : M) : iSt T e C₀ v 0 m = 0 := by simp [iSt]

theorem iSt_nested (v : V) : Nested (Sp T e v) (iSt T e C₀ v) (iL T e C₀ v) := by
  refine ⟨fun j => ?_, fun j => iL_mem T e C₀ v j, fun m => by simp [iSt],
    fun m _ => by simp [iSt]⟩
  funext m
  simp only [iSt, Finset.sum_range_succ]
  congr 1
  by_cases h : iL T e C₀ v j = m
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem iSt_full (hinj : Function.Injective C₀) (v : V) :
    iSt T e C₀ v (iN T e C₀ v) = rst T e v (iInd C₀) := by
  classical
  funext m
  set s := iS T e C₀ v with hs
  have h1 : iSt T e C₀ v (iN T e C₀ v) m =
      ∑ j : Fin s.card, (if C₀ ((s.orderIsoOfFin rfl) j : Fin k) = m then (1 : ℤ) else 0) := by
    unfold iSt
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) < iN T e C₀ v := j.2
    simp only [iL, dif_pos hj]
    rfl
  have h2 : ∑ j : Fin s.card, (if C₀ ((s.orderIsoOfFin rfl) j : Fin k) = m then (1 : ℤ) else 0) =
      ∑ x : {x // x ∈ s}, (if C₀ (x : Fin k) = m then (1 : ℤ) else 0) :=
    Equiv.sum_comp (s.orderIsoOfFin rfl).toEquiv (fun x => if C₀ (x : Fin k) = m then (1 : ℤ) else 0)
  rw [h1, h2, Finset.sum_coe_sort s (fun i => if C₀ i = m then (1 : ℤ) else 0)]
  unfold rst iInd
  by_cases hm : m ∈ Sp T e v
  · rw [if_pos hm]
    by_cases hex : ∃ i, C₀ i = m
    · obtain ⟨i0, hi0⟩ := hex
      rw [if_pos ⟨i0, hi0⟩]
      have hi0s : i0 ∈ s := by
        rw [hs]; unfold iS; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0 ▸ hm⟩
      rw [Finset.sum_eq_single i0 (fun b _ hb => if_neg fun h => hb (hinj (h.trans hi0.symm)))
        (fun h => absurd hi0s h), if_pos hi0]
    · rw [if_neg hex]
      exact Finset.sum_eq_zero fun i _ => if_neg fun h => hex ⟨i, h⟩
  · rw [if_neg hm]
    refine Finset.sum_eq_zero fun i hi => if_neg fun h => hm ?_
    rw [hs] at hi; unfold iS at hi
    exact h ▸ (Finset.mem_filter.1 hi).2

theorem iN_eq (hinj : Function.Injective C₀) (v : V) :
    nsub T e (iInd C₀) v = (iN T e C₀ v : ℤ) := by
  have h := ((iSt_nested T e C₀ v).props (iN T e C₀ v)).2.2
  rw [iSt_full T e C₀ hinj v, sum_rst] at h
  rw [h]; simp [iSt]

theorem iN_root : iN T e C₀ T.root = k := by
  classical
  have h : iS T e C₀ T.root = Finset.univ := Finset.eq_univ_of_forall fun i => by
    unfold iS; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, isAnc_root T _⟩
  unfold iN; rw [h]; simp

theorem iN_le (v : V) : iN T e C₀ v ≤ k := by
  unfold iN
  exact (Finset.card_le_univ _).trans (by simp)

theorem rst_rst {p c : V} (hpc : T.IsAnc p c) (x : M → ℤ) :
    rst T e c (rst T e p x) = rst T e c x := by
  classical
  funext m
  unfold rst
  by_cases h : m ∈ Sp T e c
  · have : m ∈ Sp T e p := isAnc_trans T hpc h
    simp [h, this]
  · simp [h]

theorem iSt_hGi (hinj : Function.Injective C₀) (p c : V) (hc : c ∈ children T p) (m : M) :
    iSt T e C₀ c (nsub T e (iSt T e C₀ p (iN T e C₀ p)) c).toNat m =
      rst T e c (iSt T e C₀ p (iN T e C₀ p)) m := by
  have hpc : T.IsAnc p c := isAnc_of_child T hc ⟨0, rfl⟩
  rw [iSt_full T e C₀ hinj p, nsub_rst T e _ hpc, iN_eq T e C₀ hinj c, Int.toNat_natCast,
    iSt_full T e C₀ hinj c, rst_rst T e hpc]

theorem iN_child (hinj : Function.Injective C₀) (p c : V) (hc : c ∈ children T p) :
    nsub T e (iSt T e C₀ p (iN T e C₀ p)) c = (iN T e C₀ c : ℤ) := by
  have hpc : T.IsAnc p c := isAnc_of_child T hc ⟨0, rfl⟩
  rw [iSt_full T e C₀ hinj p, nsub_rst T e _ hpc, iN_eq T e C₀ hinj c]

end Init

end K17428


/-! D9b (17428d40, relay 10): ROOT LINK. The root quota optimum with constant quota `k` from the
nested start `iSt root` is at most the count-trajectory optimum `treeOPT` (D1), hence at most the
offline optimum. Needs D1 D5a D5c D9a. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]
  (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (C₀ : Fin k → M)

theorem mem_Sp_root (m : M) : m ∈ Sp T e T.root := isAnc_root T _

theorem iSt_root_k (hinj : Function.Injective C₀) : iSt T e C₀ T.root k = iInd C₀ := by
  have h := iSt_full T e C₀ hinj T.root
  rw [iN_root] at h
  rw [h]; funext m; unfold rst; rw [if_pos (mem_Sp_root T e m)]

theorem iInd_cast (m : M) : ((iInd C₀ m : ℤ) : ℝ) = indicatorState C₀ m := by
  classical
  unfold iInd indicatorState
  by_cases h : ∃ i, C₀ i = m
  · rw [if_pos h, if_pos (Set.mem_range.2 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (Set.mem_range.1 h'))]; simp

theorem sum_iSt_root_k : ∑ m, iSt T e C₀ T.root k m = k := by
  have h := ((iSt_nested T e C₀ T.root).props k).2.2
  rw [h]; simp [iSt]

include T e in
theorem sum_indicatorState (hinj : Function.Injective C₀) : ∑ m, indicatorState C₀ m = k := by
  have h := iN_eq T e C₀ hinj T.root
  rw [nsub_root, iN_root] at h
  have h' := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at h'
  rw [← h']
  exact Finset.sum_congr rfl fun m _ => (iInd_cast k C₀ m).symm

theorem Qopt_root_le (hinj : Function.Injective C₀) (ρ : List M) (r : ℕ → M)
    (hr : ∀ j : Fin ρ.length, r (j + 1) = ρ.get j) (c : ℕ → M → ℝ) (hc : CountTraj k C₀ ρ c) :
    Qopt T e T.root r ρ.length (iSt T e C₀ T.root) (fun _ => k) ≤ trajCost T e ρ c := by
  classical
  choose n hn using hc.2.1
  set c' : ℕ → M → ℤ := fun t m => (n t m : ℤ) with hc'
  have hcast : ∀ t, (fun m => ((c' t m : ℤ) : ℝ)) = c t := fun t => by
    funext m; simp [hc', hn]
  have hsum : ∀ t, ∑ m, c' t m = k := fun t => by
    have h := hc.2.2.1 t
    have : ((∑ m, c' t m : ℤ) : ℝ) = (k : ℝ) := by
      push_cast; rw [← h]; exact Finset.sum_congr rfl fun m _ => by simp [hc', hn]
    exact_mod_cast this
  have hQ : QTraj T e T.root r ρ.length (iSt T e C₀ T.root) (fun _ => k) c' := by
    refine ⟨fun m => ?_, fun s _ m => by simp [hc'], fun s _ m hm => absurd (mem_Sp_root T e m) hm,
      fun s _ => by rw [hsum, sum_iSt_root_k], fun s hs1 hsN _ => ?_⟩
    · show (n 0 m : ℤ) = iSt T e C₀ T.root k m
      rw [iSt_root_k T e k C₀ hinj]
      have h0 := congrFun hc.1 m
      rw [hn, ← iInd_cast] at h0
      exact_mod_cast h0
    · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
      have hj : j < ρ.length := by omega
      have h1 := hc.2.2.2 ⟨j, hj⟩
      rw [hr ⟨j, hj⟩]
      rw [hn] at h1
      show (1 : ℤ) ≤ (n (j + 1) (ρ.get ⟨j, hj⟩) : ℤ)
      have h1' : (1 : ℝ) ≤ (n (j + 1) (ρ.get ⟨j, hj⟩) : ℝ) := by simpa using h1
      exact_mod_cast h1'
  refine (Qopt_le T e hQ).trans (le_of_eq ?_)
  unfold qcost trajCost
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← ccost_eq T e T.root _ _ (fun m hm => absurd (mem_Sp_root T e m) hm)
    (fun m hm => absurd (mem_Sp_root T e m) hm) (by rw [hsum, hsum]), hcast, hcast]

include T e in
theorem countTraj_nonempty (hk : 1 ≤ k) (hinj : Function.Injective C₀) (ρ : List M) :
    ∃ c, CountTraj k C₀ ρ c := by
  classical
  let c : ℕ → M → ℝ := fun t m =>
    if t = 0 then indicatorState C₀ m else if m = ρ.getD (t - 1) (C₀ ⟨0, hk⟩) then (k : ℝ) else 0
  refine ⟨c, ?_, fun t m => ?_, fun t => ?_, fun j => ?_⟩
  · funext m; simp [c]
  · by_cases ht : t = 0
    · simp only [c, if_pos ht]
      unfold indicatorState
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    · simp only [c, if_neg ht]
      split_ifs
      · exact ⟨k, rfl⟩
      · exact ⟨0, by simp⟩
  · by_cases ht : t = 0
    · simp only [c, if_pos ht]
      exact sum_indicatorState T e k C₀ hinj
    · simp only [c, if_neg ht]
      rw [Finset.sum_ite_eq']; simp
  · simp only [c, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    rw [if_pos (by rw [List.getD_eq_getElem _ _ j.2]; rfl)]
    exact_mod_cast hk

theorem Qopt_root_le_treeOPT (hk : 1 ≤ k) (hinj : Function.Injective C₀) (ρ : List M) (r : ℕ → M)
    (hr : ∀ j : Fin ρ.length, r (j + 1) = ρ.get j) :
    Qopt T e T.root r ρ.length (iSt T e C₀ T.root) (fun _ => k) ≤ treeOPT T e C₀ ρ := by
  obtain ⟨c, hc⟩ := countTraj_nonempty T e k C₀ hk hinj ρ
  refine le_csInf ⟨_, c, hc, rfl⟩ ?_
  rintro x ⟨c', hc', rfl⟩
  exact Qopt_root_le T e k C₀ hinj ρ r hr c' hc'

end K17428


/-! D9c (17428d40, relay 10): the node algorithms. `clampAlg` clamps every quota at `k` (so every
node request sequence is admissible, for ALL histories); `Bn p` = clamped `Afix` of the black box
at node `p`. Results: rows of every node state are probability vectors (`hcum`/`hprob` of D8),
and the D8d3 hypothesis `hB` with one uniform constant `aU`. Needs D7d D7e D7f D8a D9a. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Allocation

/-- Clamp the quota of a request at `k`. -/
def clampReq {d k : ℕ} (q : Request d k) : Request d k := ⟨q.loc, q.h, min q.quota k⟩

theorem clampReq_eq {d k : ℕ} (q : Request d k) (h : q.quota ≤ k) : clampReq q = q := by
  cases q with
  | mk loc h' quota =>
    simp only [clampReq, Request.mk.injEq, true_and]
    exact min_eq_left h

/-- The clamped algorithm. -/
def clampAlg {d k : ℕ} (A : FracAlg d k) : FracAlg d k := ⟨fun l => A.state (l.map clampReq)⟩

theorem clampAlg_totals {d k : ℕ} (A : FracAlg d k) (w : Fin d → ℝ) (ρ : List (Request d k))
    (h : ∀ q ∈ ρ, q.quota ≤ k) :
    (clampAlg A).hitTotal ρ = A.hitTotal ρ ∧ (clampAlg A).moveTotal w ρ = A.moveTotal w ρ := by
  have ht : ∀ t, (ρ.take t).map clampReq = ρ.take t := fun t => by
    conv_rhs => rw [← List.map_id (ρ.take t)]
    exact List.map_congr_left fun q hq => clampReq_eq q (h q (List.mem_of_mem_take hq))
  constructor
  · simp only [FracAlg.hitTotal, clampAlg, ht]
  · simp only [FracAlg.moveTotal, clampAlg, ht]

section NodeGen

variable {d k : ℕ} (hd : 0 < d) (loc : ℕ → Option (Fin d)) (hf : Fin d → ℕ → ℕ → ℝ)

theorem nodeSeq_clamp (κ : ℕ → ℕ) (N : ℕ) :
    (nodeSeq (k := k) hd loc hf κ N).map clampReq = nodeSeq (k := k) hd loc hf (fun t => min (κ t) k) N := by
  unfold nodeSeq
  rw [List.map_map]
  rfl

theorem nodeSeq_quota_le (κ : ℕ → ℕ) (hκ : ∀ t, κ t ≤ k) (N : ℕ) :
    ∀ q ∈ nodeSeq (k := k) hd loc hf κ N, q.quota ≤ k := by
  intro q hq
  simp only [nodeSeq, List.mem_map] at hq
  obtain ⟨s, _, rfl⟩ := hq
  exact hκ _

theorem nodeSeq_succ' (κ : ℕ → ℕ) (N : ℕ) :
    nodeSeq (k := k) hd loc hf κ (N + 1) =
      nodeSeq (k := k) hd loc hf κ N ++ [nodeReq hd loc hf κ (N + 1)] := by
  simp [nodeSeq, List.range_succ]

theorem pointMass_prob (n₀ : Fin d → ℕ) (hn : ∀ i, n₀ i ≤ k) (i : Fin d) :
    (∀ j, 0 ≤ (pointMass n₀ : FracState d k) i j) ∧ ∑ j, (pointMass n₀ : FracState d k) i j = 1 := by
  refine ⟨fun j => by unfold pointMass; split_ifs <;> norm_num, ?_⟩
  unfold pointMass
  rw [Finset.sum_eq_single (⟨n₀ i, Nat.lt_succ_of_le (hn i)⟩ : Fin (k + 1))]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro hh; exact hb (Fin.ext hh)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem afix_prob (θ a : ℝ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ) (hk : 1 ≤ k)
    (hθ : 0 ≤ θ) (hw : ∀ i, 0 < w i) (hn : ∀ i, n₀ i ≤ k) (A : FracAlg d k) {γ : ℝ}
    (hA : A.IsCompetitive w n₀ κ₀ θ γ) (hf0 : ∀ i t j, 0 ≤ hf i t j)
    (hanti : ∀ i t j j', 1 ≤ j → j ≤ j' → hf i t j' ≤ hf i t j) (κ : ℕ → ℕ) (s : ℕ) (i : Fin d) :
    (∀ j, 0 ≤ (clampAlg (Afix θ a w n₀ κ₀ A)).state (nodeSeq (k := k) hd loc hf κ s) i j) ∧
      ∑ j, (clampAlg (Afix θ a w n₀ κ₀ A)).state (nodeSeq (k := k) hd loc hf κ s) i j = 1 := by
  show (∀ j, 0 ≤ (Afix θ a w n₀ κ₀ A).state ((nodeSeq (k := k) hd loc hf κ s).map clampReq) i j) ∧
      ∑ j, (Afix θ a w n₀ κ₀ A).state ((nodeSeq (k := k) hd loc hf κ s).map clampReq) i j = 1
  rw [nodeSeq_clamp]
  cases s with
  | zero =>
    have h0 : nodeSeq (k := k) hd loc hf (fun t => min (κ t) k) 0 = [] := by simp [nodeSeq]
    rw [h0, Afix_nil, hA.1]
    exact pointMass_prob n₀ hn i
  | succ t =>
    have hv := nodeSeq_valid hd loc hf (fun t => min (κ t) k) hf0 hanti (fun t => min_le_right _ _) (t + 1)
    rw [nodeSeq_succ'] at hv ⊢
    have hF := Afix_feasible θ a w n₀ κ₀ hk hθ hw A hA _ _ hv
    exact ⟨fun j => hF.1 i j, hF.2.1 i⟩

end NodeGen

section NodeTree

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]
  (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (C₀ : Fin k → M) (r : ℕ → M)

/-- Initial child counts at `p`. -/
noncomputable def n0 (p : V) (i : Fin (children T p).card) : ℕ := iN T e C₀ (chv T p i)

variable (θ γ : ℝ) (A : ∀ p : V, FracAlg (children T p).card k) (aa : V → ℝ)

/-- The node algorithms. -/
noncomputable def Bn (p : V) : FracAlg (children T p).card k :=
  clampAlg (Afix θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (A p))

/-- The uniform additive constant. -/
noncomputable def aU : ℝ := ∑ p : V, (|aa p| + 2 + 16 * wmax (wch T p))

theorem wch_pos (p : V) (i : Fin (children T p).card) : 0 < wch T p i :=
  T.W_pos _ (chv_ne_root T p i)

theorem le_aU (p : V) : aa p + 2 ≤ aU T aa ∧ aa p + 16 * wmax (wch T p) ≤ aU T aa := by
  have hn : ∀ q : V, 0 ≤ |aa q| + 2 + 16 * wmax (wch T q) := fun q => by
    have := wmax_nonneg _ (wch_pos T q); positivity
  have hs := Finset.single_le_sum (fun q _ => hn q) (Finset.mem_univ p)
  have h1 : aa p ≤ |aa p| := le_abs_self _
  have h2 := wmax_nonneg _ (wch_pos T p)
  unfold aU
  constructor <;> linarith

theorem aU_nonneg : 0 ≤ aU T aa := by
  unfold aU
  refine Finset.sum_nonneg fun q _ => ?_
  have := wmax_nonneg _ (wch_pos T q); positivity

variable (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ)
  (hA : ∀ p, (A p).IsCompetitive (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) θ γ)
  (ha : ∀ p (ρ : List (Request (children T p).card k)), ValidSeq ρ →
      (A p).hitTotal ρ ≤ θ * (optCost (wch T p) (n0 T e k C₀ p) ρ +
        wmax (wch T p) * quotaVariation (iN T e C₀ p) ρ) + aa p ∧
      (A p).moveTotal (wch T p) ρ ≤ γ * (optCost (wch T p) (n0 T e k C₀ p) ρ +
        wmax (wch T p) * quotaVariation (iN T e C₀ p) ρ) + aa p)

include hk hθ hA in
theorem Bn_prob (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card) (s : ℕ)
    (i' : Fin (children T p).card) :
    (∀ j, 0 ≤ xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i0 s i' j) ∧
      ∑ j, xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i0 s i' j = 1 :=
  afix_prob (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) θ (aa p) (wch T p)
    (n0 T e k C₀ p) (iN T e C₀ p) hk hθ (wch_pos T p) (fun i => iN_le T e C₀ _) (A p) (hA p)
    (nhf_nonneg T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀))
    (nhf_anti T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀)) κ s i'

include hk hθ hA in
theorem Bn_cum (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card) (s : ℕ)
    (i' : Fin (children T p).card) (j : ℕ) :
    0 ≤ cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i0 s) i' j ∧
      cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i0 s) i' j ≤ 1 := by
  obtain ⟨h1, h2⟩ := Bn_prob T e k C₀ r θ γ A aa hk hθ hA p κ i0 s i'
  exact ⟨cumul_nonneg' _ _ h1 j, cumul_le_one _ _ h1 h2 j⟩

include hk hθ hγ hA ha in
theorem Bn_hB (hinj : Function.Injective C₀) (N : ℕ) (p : V) (κ : ℕ → ℕ)
    (hκ0 : κ 0 = iN T e C₀ p) (hκ : ∀ s, κ s ≤ k) (i0 : Fin (children T p).card)
    (n : ℕ → Fin (children T p).card → ℕ)
    (hn : IntFeasible (fun i => (nsub T e (iSt T e C₀ p (κ 0)) (chv T p i)).toNat)
        (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N) n)
    (hserve : ∀ s (hs : s < (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N).length),
        1 ≤ ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N)[s]).quota ∧
        0 < ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N)[s]).h 0 →
        1 ≤ n (s + 1) ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N)[s]).loc) :
    (Bn T e k C₀ θ A aa p).hitTotal
        (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N) ≤
      θ * (intCost (wch T p) (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N) n
          + wmax (wch T p) * gsum N κ) + aU T aa ∧
    nmove T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) N p κ ≤
      γ * (intCost (wch T p) (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N) n
          + wmax (wch T p) * gsum N κ) + aU T aa := by
  set l := nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ N with hl
  have hn0 : (fun i => (nsub T e (iSt T e C₀ p (κ 0)) (chv T p i)).toNat) = n0 T e k C₀ p := by
    funext i
    rw [hκ0, iN_child T e C₀ hinj p _ (chv_mem T p i), Int.toNat_natCast]
    rfl
  rw [hn0] at hn
  have hv : ValidSeq l := nodeSeq_valid _ _ _ κ
    (nhf_nonneg T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀))
    (nhf_anti T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀)) hκ N
  have hb := Afix_bounds θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) hk hθ (wch_pos T p)
    (A p) (hA p) hγ (ha p) l hv n hn hserve
  have hq : quotaVariation (iN T e C₀ p) l = gsum N κ := by
    rw [hl, nodeSeq_qv _ _ _ κ _ hκ0]; rfl
  rw [hq] at hb
  obtain ⟨ht, hm⟩ := clampAlg_totals (Afix θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (A p))
    (wch T p) l (nodeSeq_quota_le _ _ _ κ hκ N)
  obtain ⟨c1, c2⟩ := le_aU T aa p
  constructor
  · show (clampAlg _).hitTotal l ≤ _
    rw [ht]; linarith [hb.1]
  · unfold nmove
    rw [dif_pos (Fin.pos i0)]
    show (clampAlg _).moveTotal (wch T p) l ≤ _
    rw [hm]; linarith [hb.2]

end NodeTree

end K17428


/-! D9d (17428d40, relay 10): the admissible-history class `Gc` for the D8 induction with the
concrete node algorithms `Bn` (D9c) and starts `iSt` (D9a): closure under `khist` (`Gc_hGc`), the
start consistency `hGi`, feasibility of node states (`Gc_feas`, for `Zf_superadd`) and service
(`Bn_zero`, for `Zf_service`). Needs D9a D9c. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Allocation

theorem cumul_one_eq {d k : ℕ} (y : FracState d k) (i : Fin d) : cumul y i 1 = y i 0 := by
  unfold cumul
  rw [Fin.sum_univ_succ]
  simp

theorem cumul_pointMass {d k : ℕ} (n₀ : Fin d → ℕ) (hn : ∀ i, n₀ i ≤ k) (i : Fin d) (j : ℕ) :
    cumul (pointMass n₀ : FracState d k) i j = if n₀ i < j then 1 else 0 := by
  unfold cumul pointMass
  rw [Finset.sum_eq_single (⟨n₀ i, Nat.lt_succ_of_le (hn i)⟩ : Fin (k + 1))]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ n₀ i := fun h => hb (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Qf_pointMass {d k : ℕ} (n₀ : Fin d → ℕ) (hn : ∀ i, n₀ i ≤ k) (i : Fin d) (u : ℝ)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    Qf (fun j => cumul (pointMass n₀ : FracState d k) i j) k u = n₀ i := by
  unfold Qf
  have : (Icc 1 k).filter (fun j => cumul (pointMass n₀ : FracState d k) i j < u) = Icc 1 (n₀ i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, cumul_pointMass n₀ hn i j]
    have h1 := hu.1
    have h2 := hu.2
    have hk := hn i
    by_cases hj : n₀ i < j
    · simp only [hj, if_true]
      constructor
      · intro h; linarith [h.2]
      · intro h; omega
    · simp only [hj, if_false]
      constructor
      · intro h; omega
      · intro h; exact ⟨⟨h.1, by omega⟩, h1⟩
  rw [this]; simp

theorem pointMass_mass {d k : ℕ} (n₀ : Fin d → ℕ) (hn : ∀ i, n₀ i ≤ k) (i : Fin d) :
    ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * (pointMass n₀ : FracState d k) i j = n₀ i := by
  unfold pointMass
  rw [Finset.sum_eq_single (⟨n₀ i, Nat.lt_succ_of_le (hn i)⟩ : Fin (k + 1))]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ n₀ i := fun h => hb (Fin.ext h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

section Gclass

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]
  (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (C₀ : Fin k → M) (r : ℕ → M)

theorem n0_sum_le (hinj : Function.Injective C₀) (p : V) :
    ∑ i, (n0 T e k C₀ p i : ℝ) ≤ iN T e C₀ p := by
  classical
  have hs := nsub_split T e (iInd C₀) p
  rw [iN_eq T e C₀ hinj p] at hs
  have hc : ∀ c ∈ children T p, nsub T e (iInd C₀) c = (iN T e C₀ c : ℤ) :=
    fun c _ => iN_eq T e C₀ hinj c
  rw [Finset.sum_congr rfl hc] at hs
  have hcnt : 0 ≤ cnt T e (iInd C₀) p := by
    unfold cnt
    exact Finset.sum_nonneg fun m _ => by unfold iInd; split_ifs <;> norm_num
  have hR := congrArg (Int.cast : ℤ → ℝ) hs
  push_cast at hR
  rw [sum_children_fin T p (fun c => (iN T e C₀ c : ℝ))] at hR
  have : (0 : ℝ) ≤ (cnt T e (iInd C₀) p : ℝ) := by exact_mod_cast hcnt
  unfold n0
  linarith

/-- The admissible histories at `p` (up to time `N`). -/
def Gc (N : ℕ) (p : V) (κ : ℕ → ℕ) : Prop :=
  κ 0 = iN T e C₀ p ∧ (∀ s, κ s ≤ k) ∧ (∀ s, 1 ≤ s → s ≤ N → r s ∈ Sp T e p → 1 ≤ κ s)

variable (θ γ : ℝ) (A : ∀ p : V, FracAlg (children T p).card k) (aa : V → ℝ)
  (hk : 1 ≤ k) (hθ : 0 ≤ θ)
  (hA : ∀ p, (A p).IsCompetitive (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) θ γ)

include hA in
theorem xs_zero (p : V) (κ : ℕ → ℕ) (i0 : Fin (children T p).card) :
    xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i0 0 = pointMass (n0 T e k C₀ p) := by
  show (Afix θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (A p)).state
    ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ 0).map clampReq) = _
  have h0 : nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ 0 = [] := by
    simp [nodeSeq]
  rw [h0, List.map_nil, Afix_nil, (hA p).1]

include hk in
theorem Bn_zero (p : V) (κ : ℕ → ℕ) (i0 i : Fin (children T p).card) (t : ℕ)
    (hκ : 1 ≤ κ (t + 1)) (h : T.IsAnc (chv T p i) (e (r (t + 1)) : V)) :
    xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i0 (t + 1) i 0 = 0 := by
  show (Afix θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (A p)).state
    ((nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ (t + 1)).map clampReq) i 0 = 0
  rw [nodeSeq_clamp, nodeSeq_succ']
  have hl : nloc T e p r (t + 1) = some i := nloc_of_anc T e p r (t + 1) i h
  have hf0 := nhf_nonneg T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀)
  have hz := Afix_zero θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (A p)
    (nodeSeq (k := k) (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) (fun t => min (κ t) k) t)
    (nodeReq (Fin.pos i0) (nloc T e p r) (nhf T e p r (iSt T e C₀)) (fun t => min (κ t) k) (t + 1))
    ⟨le_min hκ hk, nodeReq_h0_pos _ _ _ _ hf0 (t + 1) i hl⟩
  rwa [nodeReq_loc _ _ _ _ (t + 1) i hl] at hz

include hk hA in
theorem Gc_hGc (N : ℕ) (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ)
    (hG : Gc T e k C₀ r N p κ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    Gc T e k C₀ r N (chv T p i) (khist T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i u) := by
  refine ⟨?_, fun s => Qf_le_k _ _ _, fun s hs1 hsN hsp => ?_⟩
  · show Qf (fun j => cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i 0) i j) k u = _
    rw [xs_zero T e k C₀ r θ γ A aa hA]
    exact Qf_pointMass _ (fun i => iN_le T e C₀ _) i u hu
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hspp : r (t + 1) ∈ Sp T e p := isAnc_of_child T (chv_mem T p i) hsp
    have hκ := hG.2.2 (t + 1) hs1 hsN hspp
    show 1 ≤ Qf (fun j => cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i (t + 1)) i j) k u
    refine one_le_Qf _ k hk u ?_
    show cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i (t + 1)) i 1 < u
    rw [cumul_one_eq, Bn_zero T e k C₀ r θ A aa hk p κ i i t hκ hsp]
    exact hu.1

theorem Gc_hGi (hinj : Function.Injective C₀) (N : ℕ) (p : V) (κ : ℕ → ℕ)
    (hG : Gc T e k C₀ r N p κ) (c : V) (hc : c ∈ children T p) (m : M) :
    iSt T e C₀ c (nsub T e (iSt T e C₀ p (κ 0)) c).toNat m = rst T e c (iSt T e C₀ p (κ 0)) m := by
  rw [hG.1]; exact iSt_hGi T e C₀ hinj p c hc m

include hk hθ hA in
theorem Gc_feas (hinj : Function.Injective C₀) (N : ℕ) (p : V) (κ : ℕ → ℕ)
    (i : Fin (children T p).card) (hG : Gc T e k C₀ r N p κ) :
    FracFeasible (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i N) (κ N) := by
  cases N with
  | zero =>
    rw [xs_zero T e k C₀ r θ γ A aa hA]
    have hn : ∀ i, n0 T e k C₀ p i ≤ k := fun i => iN_le T e C₀ _
    refine ⟨fun i j => (pointMass_prob _ hn i).1 j, fun i => (pointMass_prob _ hn i).2, ?_⟩
    rw [Finset.sum_congr rfl fun i _ => pointMass_mass _ hn i, hG.1]
    exact n0_sum_le T e k C₀ hinj p
  | succ t =>
    show FracFeasible ((Afix θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (A p)).state
      ((nodeSeq (k := k) (Fin.pos i) (nloc T e p r) (nhf T e p r (iSt T e C₀)) κ (t + 1)).map clampReq)) _
    rw [nodeSeq_clamp]
    have hv := nodeSeq_valid (Fin.pos i) (nloc T e p r) (nhf T e p r (iSt T e C₀)) (fun t => min (κ t) k)
      (nhf_nonneg T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀))
      (nhf_anti T e p r (iSt T e C₀) (iL T e C₀) (iSt_nested T e C₀)) (fun t => min_le_right _ _) (t + 1)
    rw [nodeSeq_succ'] at hv ⊢
    have hF := Afix_feasible θ (aa p) (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) hk hθ (wch_pos T p) (A p)
      (hA p) _ _ hv
    rw [nodeReq_quota, min_eq_left (hG.2.1 (t + 1))] at hF
    exact hF

end Gclass

end K17428


/-! D9e (17428d40, relay 10): ONLINE CONGRUENCE in the request function `r` (everything at time
`t` reads `r` only on `[1, t]`: `Fopt`, `nloc`, `nhf`, `nodeSeq`, `xs`, `khist`, `Zf`), and the
capped k-server run `Yrun` (one `capped_between` step per request, identity fallback) with its
step identity (the `hstep` of `capped_cost_le`) and congruence. Needs D4 D6b D6c D7e D7f D8a. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Allocation PolylogKServer.Fractional

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]
  (T : WTree V) (e : M ≃ T.Leaf)

theorem ITraj_rcongr (S : Set M) (r r' : ℕ → M) (H : ℕ) (x0 : M → ℤ) (c : ℕ → M → ℤ)
    (h : ∀ s, 1 ≤ s → s ≤ H → r s = r' s) : ITraj S r H x0 c ↔ ITraj S r' H x0 c := by
  unfold ITraj
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, fun s hs1 hsH hS => ?_⟩
    rw [← h s hs1 hsH] at hS ⊢; exact h5 s hs1 hsH hS
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, fun s hs1 hsH hS => ?_⟩
    rw [h s hs1 hsH] at hS ⊢; exact h5 s hs1 hsH hS

theorem Fopt_rcongr (S : Set M) (r r' : ℕ → M) (H : ℕ) (x0 : M → ℤ)
    (h : ∀ s, 1 ≤ s → s ≤ H → r s = r' s) : Fopt T e S r H x0 = Fopt T e S r' H x0 := by
  unfold Fopt
  have : {c | ITraj S r H x0 c} = {c | ITraj S r' H x0 c} :=
    Set.ext fun c => ITraj_rcongr S r r' H x0 c h
  rw [this]

theorem nloc_rcongr (p : V) (r r' : ℕ → M) (t : ℕ) (h : r t = r' t) :
    nloc T e p r t = nloc T e p r' t := by
  unfold nloc
  generalize r t = a at h ⊢
  subst h
  rfl

theorem nhf_rcongr (p : V) (r r' : ℕ → M) (st : V → ℕ → M → ℤ) (i : Fin (children T p).card)
    (t j : ℕ) (h : ∀ s, 1 ≤ s → s ≤ t → r s = r' s) :
    nhf T e p r st i t j = nhf T e p r' st i t j := by
  unfold nhf
  rw [Fopt_rcongr T e _ r r' t _ h, Fopt_rcongr T e _ r r' (t - 1) _ fun s h1 h2 => h s h1 (by omega)]

theorem nodeReq_congr' {d k : ℕ} (hd : 0 < d) (loc loc' : ℕ → Option (Fin d))
    (hf hf' : Fin d → ℕ → ℕ → ℝ) (κ : ℕ → ℕ) (t : ℕ) (hl : loc t = loc' t)
    (hh : ∀ i j, hf i t j = hf' i t j) :
    nodeReq (k := k) hd loc hf κ t = nodeReq (k := k) hd loc' hf' κ t := by
  unfold nodeReq
  rw [hl]
  simp only [hh]

theorem nodeSeq_rcongr {k : ℕ} (p : V) (hd : 0 < (children T p).card) (r r' : ℕ → M)
    (st : V → ℕ → M → ℤ) (κ : ℕ → ℕ) (N : ℕ) (h : ∀ s, 1 ≤ s → s ≤ N → r s = r' s) :
    nodeSeq (k := k) hd (nloc T e p r) (nhf T e p r st) κ N =
      nodeSeq (k := k) hd (nloc T e p r') (nhf T e p r' st) κ N := by
  unfold nodeSeq
  refine List.map_congr_left fun s hs => ?_
  have hs' : s < N := List.mem_range.1 hs
  exact nodeReq_congr' hd _ _ _ _ κ (s + 1)
    (nloc_rcongr T e p r r' (s + 1) (h (s + 1) (by omega) (by omega)))
    (fun i j => nhf_rcongr T e p r r' st i (s + 1) j fun s' h1 h2 => h s' h1 (by omega))

section Ens

variable (k : ℕ) (st : V → ℕ → M → ℤ) (B : ∀ p : V, FracAlg (children T p).card k)

theorem xs_rcongr (r r' : ℕ → M) (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (s : ℕ)
    (h : ∀ s', 1 ≤ s' → s' ≤ s → r s' = r' s') :
    xs T e k r st B p κ i s = xs T e k r' st B p κ i s := by
  unfold xs
  rw [nodeSeq_rcongr T e p _ r r' st κ s h]

theorem khist_rcongr (r r' : ℕ → M) (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ)
    (N : ℕ) (h : ∀ s, 1 ≤ s → s ≤ N → r s = r' s) :
    ∀ s ≤ N, khist T e k r st B p κ i u s = khist T e k r' st B p κ i u s := by
  intro s hs
  unfold khist
  rw [xs_rcongr T e k st B r r' p κ i s fun s' h1 h2 => h s' h1 (le_trans h2 hs)]

theorem Zf_rcongr (r r' : ℕ → M) (N : ℕ) (h : ∀ s, 1 ≤ s → s ≤ N → r s = r' s) :
    ∀ (f : ℕ) (p : V) (κ : ℕ → ℕ) (v : V),
      Zf T e k r st B N f p κ v = Zf T e k r' st B N f p κ v := by
  intro f
  induction f with
  | zero => intro p κ v; simp only [Zf]
  | succ f ih =>
    intro p κ v
    simp only [Zf]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [ih]
    exact Zf_congr T e k r' st B N f _ _ _ v (khist_rcongr T e k st B r r' p κ i u N h)

end Ens

/-! The capped run. -/

open Classical in
/-- One capped step towards the target `Z` serving `x` (identity if the hypotheses fail). -/
noncomputable def Ystep (y : M → ℝ) (Z : V → ℝ) (x : M) : M → ℝ :=
  if h : (∀ m, 0 ≤ y m) ∧ (∀ m, y m ≤ 1) ∧ (∀ v, ∑ c ∈ children T v, Z c ≤ Z v) ∧
      Z T.root ≤ ∑ m, y m ∧ 1 ≤ Z (e x) then
    Classical.choose (capped_between T e y h.1 h.2.1 Z h.2.2.1 h.2.2.2.1 x h.2.2.2.2)
  else y

theorem Ystep_step (y : M → ℝ) (Z : V → ℝ) (x : M) :
    fracMoveCost T e y (Ystep T e y Z x) + Phi T e (Ystep T e y Z x) Z = Phi T e y Z := by
  classical
  unfold Ystep
  split_ifs with h
  · have hs := Classical.choose_spec (capped_between T e y h.1 h.2.1 Z h.2.2.1 h.2.2.2.1 x h.2.2.2.2)
    unfold fracMoveCost Phi
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← mul_add, hs.2.2.2 v]
  · unfold fracMoveCost
    simp

theorem Ystep_spec (y : M → ℝ) (Z : V → ℝ) (x : M) (h0 : ∀ m, 0 ≤ y m) (h1 : ∀ m, y m ≤ 1)
    (hZ : ∀ v, ∑ c ∈ children T v, Z c ≤ Z v) (hroot : Z T.root ≤ ∑ m, y m) (hx : 1 ≤ Z (e x)) :
    (∀ m, 0 ≤ Ystep T e y Z x m ∧ Ystep T e y Z x m ≤ 1) ∧
      ∑ m, Ystep T e y Z x m = ∑ m, y m ∧ Ystep T e y Z x x = 1 := by
  classical
  have h : (∀ m, 0 ≤ y m) ∧ (∀ m, y m ≤ 1) ∧ (∀ v, ∑ c ∈ children T v, Z c ≤ Z v) ∧
      Z T.root ≤ ∑ m, y m ∧ 1 ≤ Z (e x) := ⟨h0, h1, hZ, hroot, hx⟩
  have hs := Classical.choose_spec (capped_between T e y h.1 h.2.1 Z h.2.2.1 h.2.2.2.1 x h.2.2.2.2)
  unfold Ystep
  rw [dif_pos h]
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-- The capped run from `y0` towards the targets `Zr t`, serving `r t` at time `t ≥ 1`. -/
noncomputable def Yrun (y0 : M → ℝ) (Zr : ℕ → V → ℝ) (r : ℕ → M) : ℕ → M → ℝ
  | 0 => y0
  | t + 1 => Ystep T e (Yrun y0 Zr r t) (Zr (t + 1)) (r (t + 1))

theorem Yrun_congr (y0 : M → ℝ) (Zr Zr' : ℕ → V → ℝ) (r r' : ℕ → M) (t : ℕ)
    (hZ : ∀ s, s ≤ t → Zr s = Zr' s) (hr : ∀ s, 1 ≤ s → s ≤ t → r s = r' s) :
    Yrun T e y0 Zr r t = Yrun T e y0 Zr' r' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Yrun]
    rw [ih (fun s hs => hZ s (by omega)) (fun s h1 h2 => hr s h1 (by omega)), hZ (t + 1) le_rfl,
      hr (t + 1) (by omega) le_rfl]

end K17428


/-! D9g (17428d40, relay 10): ASSEMBLY. For a fixed request function `r`, the capped run
`Yr r` towards the ensemble quotas `Zr r t = Zf r t ℓ root (const k)` stays a fractional k-server
state, serves `r t`, and costs at most `Phi_0 + Tot ≤ Phi_0 + β Qopt_root + AF`. Needs all of D1-D9e. -/

namespace K17428

open Finset PolylogKServer.HST PolylogKServer.Allocation PolylogKServer.Fractional

section Run

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]
  (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (C₀ : Fin k → M) (ℓ : ℕ)
  (θ γ : ℝ) (A : ∀ p : V, FracAlg (children T p).card k) (aa : V → ℝ)

/-- The ensemble quota targets. -/
noncomputable def Zr (r : ℕ → M) (t : ℕ) : V → ℝ := fun v =>
  Zf T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) t ℓ T.root (fun _ => k) v

/-- The capped k-server run. -/
noncomputable def Yr (r : ℕ → M) : ℕ → M → ℝ :=
  Yrun T e (indicatorState C₀) (Zr T e k C₀ ℓ θ A aa r) r

theorem inner_root_eq : inner T T.root = univ.filter (fun v => v ≠ T.root) := by
  ext v
  rw [mem_inner, Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, h.1⟩, fun h => ⟨h.2, isAnc_root T v, h.2⟩⟩

theorem depth_leaf_le (hht : T.height = ℓ) (m : M) : T.depth (e m : V) ≤ T.depth T.root + ℓ := by
  rw [T.depth_root, zero_add, ← hht]
  unfold WTree.height
  exact Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, (e m).2⟩)

theorem Groot (r : ℕ → M) (hk : 1 ≤ k) (N : ℕ) : Gc T e k C₀ r N T.root (fun _ => k) :=
  ⟨(iN_root T e C₀).symm, fun _ => le_rfl, fun _ _ _ _ => hk⟩

variable (hk : 1 ≤ k) (hθ : 0 ≤ θ)
  (hA : ∀ p, (A p).IsCompetitive (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) θ γ)

include hk hθ hA in
theorem Yr_inv (hinj : Function.Injective C₀) (hht : T.height = ℓ) (r : ℕ → M) :
    ∀ t, (∀ m, 0 ≤ Yr T e k C₀ ℓ θ A aa r t m ∧ Yr T e k C₀ ℓ θ A aa r t m ≤ 1) ∧
      ∑ m, Yr T e k C₀ ℓ θ A aa r t m = k ∧
      (1 ≤ t → Yr T e k C₀ ℓ θ A aa r t (r t) = 1) := by
  classical
  intro t
  induction t with
  | zero =>
    refine ⟨fun m => ?_, sum_indicatorState T e k C₀ hinj, fun h => absurd h (by omega)⟩
    show 0 ≤ indicatorState C₀ m ∧ indicatorState C₀ m ≤ 1
    unfold indicatorState
    split_ifs <;> norm_num
  | succ t ih =>
    obtain ⟨h01, hsum, _⟩ := ih
    set G := Gc T e k C₀ r (t + 1) with hGdef
    have hGc : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (u : ℝ), G p κ →
        u ∈ Set.Ioo (0 : ℝ) 1 →
        G (chv T p i) (khist T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i u) :=
      fun p κ i u hG hu => Gc_hGc T e k C₀ r θ γ A aa hk hA (t + 1) p κ i u hG hu
    have hZ : ∀ v, ∑ c ∈ children T v, Zr T e k C₀ ℓ θ A aa r (t + 1) c ≤
        Zr T e k C₀ ℓ θ A aa r (t + 1) v := fun v =>
      Zf_superadd T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) (t + 1) G
        (fun p κ i hG => Gc_feas T e k C₀ r θ γ A aa hk hθ hA hinj (t + 1) p κ i hG) hGc ℓ T.root
        (fun _ => k) v (Groot T e k C₀ r hk (t + 1)) (isAnc_root T v)
    have hroot : Zr T e k C₀ ℓ θ A aa r (t + 1) T.root ≤ ∑ m, Yr T e k C₀ ℓ θ A aa r t m := by
      rw [hsum]
      show Zf T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) (t + 1) ℓ T.root (fun _ => k) T.root ≤ _
      rw [Zf_self]
    have hx : 1 ≤ Zr T e k C₀ ℓ θ A aa r (t + 1) (e (r (t + 1))) :=
      Zf_service T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) (t + 1) hk G
        (fun p κ i _ hκ hanc => Bn_zero T e k C₀ r θ A aa hk p κ i i t hκ hanc) hGc ℓ T.root
        (fun _ => k) (Groot T e k C₀ r hk (t + 1)) (isAnc_root T _) hk
        (depth_leaf_le T e ℓ hht _)
    have hs := Ystep_spec T e (Yr T e k C₀ ℓ θ A aa r t) (Zr T e k C₀ ℓ θ A aa r (t + 1)) (r (t + 1))
      (fun m => (h01 m).1) (fun m => (h01 m).2) hZ hroot hx
    refine ⟨hs.1, ?_, fun _ => hs.2.2⟩
    rw [← hsum]; exact hs.2.1

theorem Yr_cost (r : ℕ → M) (N : ℕ)
    (hcum : ∀ (p : V) (κ : ℕ → ℕ) (i : Fin (children T p).card) (s : ℕ) (i' : Fin _) (j : ℕ),
      0 ≤ cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i s) i' j ∧
        cumul (xs T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) p κ i s) i' j ≤ 1) :
    ∑ t ∈ range N, fracMoveCost T e (Yr T e k C₀ ℓ θ A aa r t) (Yr T e k C₀ ℓ θ A aa r (t + 1)) ≤
      Phi T e (indicatorState C₀) (Zr T e k C₀ ℓ θ A aa r 0) +
        Tot T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) N ℓ T.root (fun _ => k) := by
  have h1 := capped_cost_le T e (Yr T e k C₀ ℓ θ A aa r) (Zr T e k C₀ ℓ θ A aa r)
    (fun t => Ystep_step T e _ _ _) N
  have h2 := zc_le_Tot T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) hcum N ℓ T.root (fun _ => k)
  rw [inner_root_eq] at h2
  have h3 : ∑ t ∈ range N, zcost T (Zr T e k C₀ ℓ θ A aa r t) (Zr T e k C₀ ℓ θ A aa r (t + 1)) ≤
      Tot T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) N ℓ T.root (fun _ => k) := h2
  have h1' : ∑ t ∈ range N, fracMoveCost T e (Yr T e k C₀ ℓ θ A aa r t) (Yr T e k C₀ ℓ θ A aa r (t + 1)) ≤
      Phi T e (indicatorState C₀) (Zr T e k C₀ ℓ θ A aa r 0) +
        ∑ t ∈ range N, zcost T (Zr T e k C₀ ℓ θ A aa r t) (Zr T e k C₀ ℓ θ A aa r (t + 1)) := h1
  linarith

end Run

section Tot

variable {V : Type} [Fintype V] [DecidableEq V] {M : Type} [Fintype M] [DecidableEq M]
  (T : WTree V) (e : M ≃ T.Leaf) (k : ℕ) (C₀ : Fin k → M) (ℓ : ℕ)
  (θ γ : ℝ) (A : ∀ p : V, FracAlg (children T p).card k) (aa : V → ℝ)

theorem Tot_root_le (hk : 1 ≤ k) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ)
    (hA : ∀ p, (A p).IsCompetitive (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) θ γ)
    (ha : ∀ p (ρ : List (Request (children T p).card k)), ValidSeq ρ →
      (A p).hitTotal ρ ≤ θ * (optCost (wch T p) (n0 T e k C₀ p) ρ +
        wmax (wch T p) * quotaVariation (iN T e C₀ p) ρ) + aa p ∧
      (A p).moveTotal (wch T p) ρ ≤ γ * (optCost (wch T p) (n0 T e k C₀ p) ρ +
        wmax (wch T p) * quotaVariation (iN T e C₀ p) ρ) + aa p)
    (hinj : Function.Injective C₀) (σ : ℝ) (hσ : 1 < σ) (hT : T.IsWeightedHST σ)
    (r : ℕ → M) (N : ℕ) :
    Tot T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) N ℓ T.root (fun _ => k) ≤
      betaF θ γ (3 / (σ - 1)) (2 / (σ - 1)) ℓ * Qopt T e T.root r N (iSt T e C₀ T.root) (fun _ => k) +
        AF (aU T aa) θ γ (3 / (σ - 1)) (2 / (σ - 1)) (Fintype.card V) ℓ := by
  have h := tot_bound T e k r (iSt T e C₀) (Bn T e k C₀ θ A aa) (iL T e C₀) hk σ hσ hT
    (iSt_nested T e C₀) (iSt_zero T e C₀) N θ γ (aU T aa) (3 / (σ - 1)) (2 / (σ - 1)) hθ hγ
    (aU_nonneg T aa) rfl rfl (Gc T e k C₀ r N)
    (fun p κ hG => hG.2.2) (fun p κ hG => hG.2.1)
    (fun p κ hG c hc m => Gc_hGi T e k C₀ r hinj N p κ hG c hc m)
    (fun p κ i u hG hu => Gc_hGc T e k C₀ r θ γ A aa hk hA N p κ i u hG hu)
    (fun p κ _ i0 s i' => Bn_prob T e k C₀ r θ γ A aa hk hθ hA p κ i0 s i')
    (fun p κ hG i0 n hn hserve =>
      Bn_hB T e k C₀ r θ γ A aa hk hθ hγ hA ha hinj N p κ hG.1 hG.2.1 i0 n hn hserve)
    ℓ T.root (fun _ => k) (Groot T e k C₀ r hk N)
  have hg : gsum N (fun _ => k) = 0 := by simp [gsum]
  rw [hg, mul_zero, add_zero] at h
  exact h

end Tot

/-- The request function of a request list (`r s` = the `s`-th request, `s ≥ 1`). -/
def rOf {M : Type} (d : M) (l : List M) (s : ℕ) : M := l.getD (s - 1) d

theorem final (c₀ : ℝ) (hc₀ : 0 < c₀) (k : ℕ) (hk : 2 ≤ k)
    (hyp : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (d : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ),
          (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
          ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (c₀ * Real.log (k / ε)))
    {V : Type} [Fintype V] [DecidableEq V] (T : WTree V) (σ : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hht : T.height = ℓ) (hT : T.IsWeightedHST σ)
    (hσ : (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) ≤ σ)
    {M : Type} [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf) (hM : T.IsLeafMetric M e)
    (C₀ : KServer.Config k M) (hinj : Function.Injective C₀) :
    ∃ F : FracKServerAlg k M, F.IsCompetitiveFrom T e C₀ ((108 * c₀ + 8) * ℓ * Real.log (k * ℓ)) := by
  classical
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hσ1, hβ⟩ := betaF_final c₀ hc₀ k ℓ hk hℓ σ hσ
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkl : (1 : ℝ) ≤ k * ℓ := by nlinarith
  have hlog : 0 ≤ Real.log (k * ℓ) := Real.log_nonneg hkl
  have hε0 : (0 : ℝ) < 1 / (ℓ : ℝ) := by positivity
  have hε1 : 1 / (ℓ : ℝ) ≤ 1 := (div_le_one (by linarith)).2 hℓR
  have hkε : (k : ℝ) / (1 / (ℓ : ℝ)) = k * ℓ := by rw [div_div_eq_mul_div, div_one]
  have hθ : (0 : ℝ) ≤ 1 + 1 / (ℓ : ℝ) := by positivity
  have hγ : 0 ≤ c₀ * Real.log (k * ℓ) := mul_nonneg hc₀.le hlog
  have hex : ∀ p : V, ∃ A : FracAlg (children T p).card k,
      A.IsCompetitive (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (1 + 1 / (ℓ : ℝ))
        (c₀ * Real.log (k * ℓ)) := by
    intro p
    have hs : ∑ i, n0 T e k C₀ p i ≤ iN T e C₀ p := by
      have := n0_sum_le T e k C₀ hinj p
      exact_mod_cast this
    have h := hyp (1 / (ℓ : ℝ)) hε0 hε1 _ (wch T p) (n0 T e k C₀ p) (iN T e C₀ p) (wch_pos T p)
      (fun i => iN_le T e C₀ _) hs (iN_le T e C₀ p)
    rw [hkε] at h
    exact h
  choose A hA using hex
  choose aa ha using fun p => (hA p).2.2
  have hd : (0 : ℕ) < k := by omega
  let d0 : M := C₀ ⟨0, hd⟩
  have hinv := fun r => Yr_inv T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) (c₀ * Real.log (k * ℓ)) A aa hk1 hθ hA
    hinj hht r
  refine ⟨⟨fun l => Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 l) l.length⟩, rfl, fun l => ?_,
    fun l x => ?_, ?_⟩
  · obtain ⟨h01, hsum, _⟩ := hinv (rOf d0 l) l.length
    exact ⟨h01, hsum⟩
  · obtain ⟨_, _, hserve⟩ := hinv (rOf d0 (l ++ [x])) (l ++ [x]).length
    have hlen : (l ++ [x]).length = l.length + 1 := by simp
    have hr : rOf d0 (l ++ [x]) (l ++ [x]).length = x := by
      unfold rOf
      rw [hlen, Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by simp)]
      simp
    have := hserve (by rw [hlen]; omega)
    rw [hr] at this
    exact this
  · refine ⟨Phi T e (indicatorState C₀)
        (Zr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (fun _ => d0) 0) +
      AF (aU T aa) (1 + 1 / (ℓ : ℝ)) (c₀ * Real.log (k * ℓ)) (3 / (σ - 1)) (2 / (σ - 1))
        (Fintype.card V) ℓ, fun ρ => ?_⟩
    have hagree : ∀ t, t ≤ ρ.length → ∀ s, 1 ≤ s → s ≤ t →
        rOf d0 (ρ.take t) s = rOf d0 ρ s := by
      intro t _ s h1 h2
      unfold rOf
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
      rw [if_pos (by omega)]
    have hstate : ∀ t, t ≤ ρ.length →
        Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 (ρ.take t)) (ρ.take t).length =
          Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 ρ) t := by
      intro t ht
      rw [List.length_take, min_eq_left ht]
      unfold Yr
      refine Yrun_congr T e _ _ _ _ _ t (fun s hs => ?_) (fun s h1 h2 => hagree t ht s h1 h2)
      funext v
      unfold Zr
      exact Zf_rcongr T e k (iSt T e C₀) (Bn T e k C₀ (1 + 1 / (ℓ : ℝ)) A aa) _ _ s
        (fun s' h1' h2' => hagree t ht s' h1' (le_trans h2' hs)) ℓ T.root _ v
    have hcost : FracKServerAlg.cost
        (⟨fun l => Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 l) l.length⟩ : FracKServerAlg k M)
        T e ρ = ∑ t ∈ range ρ.length,
          fracMoveCost T e (Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 ρ) t)
            (Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 ρ) (t + 1)) := by
      unfold FracKServerAlg.cost
      refine Finset.sum_congr rfl fun t ht => ?_
      have := Finset.mem_range.1 ht
      show fracMoveCost T e (Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 (ρ.take t)) (ρ.take t).length)
        (Yr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 (ρ.take (t + 1))) (ρ.take (t + 1)).length) = _
      rw [hstate t (by omega), hstate (t + 1) (by omega)]
    rw [hcost]
    have h1 := Yr_cost T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 ρ) ρ.length
      (fun p κ i s i' j => Bn_cum T e k C₀ (rOf d0 ρ) (1 + 1 / (ℓ : ℝ)) (c₀ * Real.log (k * ℓ)) A aa
        hk1 hθ hA p κ i s i' j)
    have h2 := Tot_root_le T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) (c₀ * Real.log (k * ℓ)) A aa hk1 hθ hγ hA ha
      hinj σ hσ1 hT (rOf d0 ρ) ρ.length
    have hr : ∀ j : Fin ρ.length, rOf d0 ρ (j + 1) = ρ.get j := by
      intro j
      unfold rOf
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ _ j.2]
      rfl
    have h3 := Qopt_root_le_treeOPT T e k C₀ hk1 hinj ρ (rOf d0 ρ) hr
    have h4 := treeOPT_le_offlineCost T hk1 e hM C₀ hinj ρ
    have hPhi : Phi T e (indicatorState C₀) (Zr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (rOf d0 ρ) 0) =
        Phi T e (indicatorState C₀) (Zr T e k C₀ ℓ (1 + 1 / (ℓ : ℝ)) A aa (fun _ => d0) 0) := by
      congr 1
      funext v
      unfold Zr
      exact Zf_rcongr T e k (iSt T e C₀) (Bn T e k C₀ (1 + 1 / (ℓ : ℝ)) A aa) _ _ 0
        (fun s h1 h2 => by omega) ℓ T.root _ v
    have hQ0 := Qopt_nonneg' T e (rOf d0 ρ) T.root ρ.length (iSt T e C₀ T.root) (fun _ => k)
    have hC0 : 0 ≤ (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) := by positivity
    have h5 : betaF (1 + 1 / (ℓ : ℝ)) (c₀ * Real.log (k * ℓ)) (3 / (σ - 1)) (2 / (σ - 1)) ℓ *
          Qopt T e T.root (rOf d0 ρ) ρ.length (iSt T e C₀ T.root) (fun _ => k) ≤
        (108 * c₀ + 8) * ℓ * Real.log (k * ℓ) * KServer.offlineCost C₀ ρ :=
      mul_le_mul hβ (h3.trans h4) hQ0 hC0
    rw [hPhi] at h1
    linarith

end K17428

open PolylogKServer.HST PolylogKServer.Allocation PolylogKServer.Fractional in
theorem solution :
    ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (d : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ),
          (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
          ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (c₀ * Real.log (k / ε))) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (T : WTree V) (σ : ℝ) (ℓ : ℕ),
        1 ≤ ℓ → T.height = ℓ → T.IsWeightedHST σ →
        C * ℓ * Real.log (k * ℓ) ≤ σ →
        ∀ (M : Type) [MetricSpace M] [Fintype M] (e : M ≃ T.Leaf),
          T.IsLeafMetric M e →
          ∀ C₀ : KServer.Config k M, Function.Injective C₀ →
          ∃ F : FracKServerAlg k M,
            F.IsCompetitiveFrom T e C₀ (C * ℓ * Real.log (k * ℓ)) := by
  intro c₀ hc₀
  refine ⟨108 * c₀ + 8, by positivity, ?_⟩
  intro k hk hyp V _ _ T σ ℓ hℓ hht hT hσ M _ _ e hM C₀ hinj
  exact K17428.final c₀ hc₀ k hk hyp T σ ℓ hℓ hht hT hσ e hM C₀ hinj
