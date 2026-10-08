-- Prove2me | solution 1 for ServiceParts.UnitDecomp.lemma2_release_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T10:26:51.257271+00:00
-- url     : https://prove2.me/submissions/c22b0e84-f81d-47c2-bcfd-1b5870c88114

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem



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

open ServiceParts.UnitDecomp


theorem solution {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (s : σ) (y : ℕ) (hy : 1 ≤ y)
    (hrel : M.optDecisions N n s (y + 1) = {Decision.release}) :
    Decision.release ∈ M.optDecisions N n s y := by
  exact SPD.lemma2_core M N n s y hy hrel
