-- Prove2me | solution 1 for VanderbeiLP.Networks.max_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:23:50.95359+00:00
-- url     : https://prove2.me/submissions/142b0d79-6abc-4767-82f0-3c6a647b3c3f

/-
Theorem 15.1 (Max-Flow Min-Cut), Vanderbei's Linear Programming, proved from scratch.

1. The set of feasible flows (with flow off the arc set normalized to zero) is a closed subset of a
   compact box, so the flow value `x_ts` attains a maximum at some flow `x`.
2. Let `C` be the set of nodes reachable from `s` along residual steps (forward along an arc with
   `x < u`, backward along an arc with `x > 0`). If `t` were reachable, pushing a small amount `ε`
   along the residual walk (with `ε` at most the smallest positive slack divided by the walk
   length, which keeps every arc within its bounds even if the walk repeats arcs) would give a
   feasible flow of larger value, contradicting maximality (lemmas `aug`, `improve`).
3. Hence `C` is a cut. Every arc leaving `C` is saturated and every arc entering `C` carries zero
   flow, so the net flow across the cut, which equals the flow value (`cut_identity`), equals the
   capacity of `C`. Weak duality (`flow_le_cap`) shows no cut is smaller.
-/
import Mathlib
import Definitions.Def_VanderbeiLP_Networks_MaxFlow

set_option autoImplicit false

namespace VanderbeiLP.Networks
open Finset

section FlowLib
variable {N : Type*} [DecidableEq N]

/-- Inflow minus outflow of `f` at `k`, through the incidence matrix. -/
noncomputable def netOf (A : Finset (N × N)) (f : N × N → ℝ) (k : N) : ℝ :=
  ∑ a ∈ A, incidence k a * f a

theorem netOf_eq (A : Finset (N × N)) (hA : IsNetwork A) (f : N × N → ℝ) (k : N) :
    netOf A f k = (∑ a ∈ A.filter (fun a => a.2 = k), f a) - ∑ a ∈ A.filter (fun a => a.1 = k), f a := by
  unfold netOf
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have h := hA a ha
  obtain ⟨i, j⟩ := a
  simp only at h
  unfold incidence
  by_cases h2 : k = j
  · have h1 : i ≠ k := fun e => h (e.trans h2)
    simp [h2, h1, h]
  · by_cases h1 : k = i
    · simp [h1, h2, h, Ne.symm h]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]


theorem sum_incidence (A : Finset (N × N)) (hA : IsNetwork A) (C : Finset N) (a : N × N) (ha : a ∈ A) :
    ∑ k ∈ C, incidence k a = (if a.2 ∈ C then 1 else 0) - (if a.1 ∈ C then 1 else 0) := by
  have h := hA a ha
  obtain ⟨i, j⟩ := a
  simp only at h ⊢
  have : ∀ k : N, incidence k (i, j) = (if j = k then 1 else 0) - (if i = k then 1 else 0) := by
    intro k
    unfold incidence
    by_cases h2 : k = j
    · subst h2; simp [h]
    · by_cases h1 : k = i
      · subst h1; simp [Ne.symm h2, h2]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq]

theorem cut_identity (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) (hx : IsMaxFlowFeasible A u s t x xts) (C : Finset N)
    (hC : IsCut s t C) :
    (∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a) -
      (∑ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a) = xts := by
  obtain ⟨hs, ht⟩ := hC
  have hcons : ∀ k, netOf A x k + (if k = s then xts else 0) - (if k = t then xts else 0) = 0 := by
    intro k
    have := hx.2.2 k
    rw [netOf_eq A hA]
    linarith
  have h1 : ∑ k ∈ C, (netOf A x k + (if k = s then xts else 0) - (if k = t then xts else 0)) = 0 :=
    Finset.sum_eq_zero (fun k _ => hcons k)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos hs, if_neg ht] at h1
  have h2 : ∑ k ∈ C, netOf A x k =
      (∑ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a) -
        ∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a := by
    unfold netOf
    rw [Finset.sum_comm, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [← Finset.sum_mul, sum_incidence A hA C a ha]
    by_cases h1 : a.1 ∈ C <;> by_cases h2 : a.2 ∈ C <;> simp [h1, h2]
  linarith


theorem flow_le_cap (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N)
    (x : N × N → ℝ) (xts : ℝ) (hx : IsMaxFlowFeasible A u s t x xts) (C : Finset N)
    (hC : IsCut s t C) : xts ≤ cutCapacity A u C := by
  have h := cut_identity A hA u s t x xts hx C hC
  have hin : 0 ≤ ∑ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a :=
    Finset.sum_nonneg (fun a ha => (hx.1 a (Finset.mem_filter.1 ha).1).1)
  have hout : ∑ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a ≤ cutCapacity A u C :=
    Finset.sum_le_sum (fun a ha => (hx.1 a (Finset.mem_filter.1 ha).1).2)
  linarith


theorem incidence_eq {i j : N} (h : i ≠ j) (k : N) :
    incidence k (i, j) = (if k = j then 1 else 0) - (if k = i then 1 else 0) := by
  unfold incidence
  by_cases h2 : k = j
  · subst h2; simp [Ne.symm h]
  · by_cases h1 : k = i
    · subst h1; simp [h2]
    · simp [h1, h2]

theorem netOf_add (A : Finset (N × N)) (f g : N × N → ℝ) (k : N) :
    netOf A (fun a => f a + g a) k = netOf A f k + netOf A g k := by
  unfold netOf; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem netOf_sub (A : Finset (N × N)) (f g : N × N → ℝ) (k : N) :
    netOf A (fun a => f a - g a) k = netOf A f k - netOf A g k := by
  unfold netOf; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun a _ => by ring)

theorem netOf_single (A : Finset (N × N)) (a : N × N) (ha : a ∈ A) (c : ℝ) (k : N) :
    netOf A (fun b => if b = a then c else 0) k = incidence k a * c := by
  unfold netOf
  simp [mul_ite, ha]

theorem exists_pos_le (T : Finset ℝ) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ T, 0 < y → ρ ≤ y := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert y T hy ih =>
    obtain ⟨ρ, hρ, h⟩ := ih
    by_cases hpos : 0 < y
    · refine ⟨min ρ y, lt_min hρ hpos, ?_⟩
      intro z hz hz0
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h z hz hz0)
    · refine ⟨ρ, hρ, ?_⟩
      intro z hz hz0
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact absurd hz0 hpos
      · exact h z hz hz0

theorem exists_slack (A : Finset (N × N)) (u x : N × N → ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ A, (x a < u a → ρ ≤ u a - x a) ∧ (0 < x a → ρ ≤ x a) := by
  obtain ⟨ρ, hρ, h⟩ := exists_pos_le (A.image (fun a => u a - x a) ∪ A.image x)
  refine ⟨ρ, hρ, fun a ha => ⟨fun hlt => ?_, fun hpos => ?_⟩⟩
  · exact h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)) (by linarith)
  · exact h _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)) hpos

/-- One step of the residual graph of the flow `x`. -/
def Res (A : Finset (N × N)) (u x : N × N → ℝ) (i j : N) : Prop :=
  ((i, j) ∈ A ∧ x (i, j) < u (i, j)) ∨ ((j, i) ∈ A ∧ 0 < x (j, i))

/-- `Reach A u x s v n`: `v` is reached from `s` by a residual walk of length `n`. -/
inductive Reach (A : Finset (N × N)) (u x : N × N → ℝ) (s : N) : N → ℕ → Prop
  | start : Reach A u x s s 0
  | step {i j : N} {n : ℕ} : Reach A u x s i n → Res A u x i j → Reach A u x s j (n + 1)


theorem aug (A : Finset (N × N)) (hA : IsNetwork A) (u x : N × N → ℝ) (s : N) (ρ : ℝ)
    (hslack : ∀ a ∈ A, (x a < u a → ρ ≤ u a - x a) ∧ (0 < x a → ρ ≤ x a))
    {v : N} {n : ℕ} (h : Reach A u x s v n) :
    ∀ ε : ℝ, 0 ≤ ε → (n : ℝ) * ε ≤ ρ → ∃ d : N × N → ℝ,
      (∀ k, netOf A d k = ε * ((if k = v then 1 else 0) - (if k = s then 1 else 0))) ∧
      ∀ a ∈ A, |d a| ≤ n * ε ∧ (0 < d a → ρ ≤ u a - x a) ∧ (d a < 0 → ρ ≤ x a) := by
  induction h with
  | start =>
    intro ε hε _
    refine ⟨fun _ => 0, fun k => ?_, fun a _ => by simp⟩
    unfold netOf; simp
  | @step i j n hr hres ih =>
    intro ε hε hnε
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnε' : (n : ℝ) * ε ≤ ρ := by
      push_cast at hnε; nlinarith
    obtain ⟨d, hd1, hd2⟩ := ih ε hε hnε'
    rcases hres with ⟨hij, hlt⟩ | ⟨hji, hpos⟩
    · have hne : i ≠ j := by
        intro e; subst e; exact hA _ hij rfl
      refine ⟨fun b => d b + (if b = (i, j) then ε else 0), fun k => ?_, fun a ha => ?_⟩
      · rw [netOf_add, netOf_single A _ hij, hd1 k, incidence_eq hne]
        ring
      · obtain ⟨h1, h2, h3⟩ := hd2 a ha
        by_cases hab : a = (i, j)
        · subst hab
          simp only [if_true]
          refine ⟨?_, fun _ => (hslack _ ha).1 hlt, fun hneg => h3 (by linarith)⟩
          calc |d (i, j) + ε| ≤ |d (i, j)| + |ε| := abs_add_le _ _
            _ ≤ ((n + 1 : ℕ) : ℝ) * ε := by rw [abs_of_nonneg hε]; push_cast; linarith
        · simp only [hab, if_false, add_zero]
          refine ⟨?_, h2, h3⟩
          calc |d a| ≤ n * ε := h1
            _ ≤ ((n + 1 : ℕ) : ℝ) * ε := by push_cast; nlinarith
    · have hne : j ≠ i := by
        intro e; subst e; exact hA _ hji rfl
      refine ⟨fun b => d b - (if b = (j, i) then ε else 0), fun k => ?_, fun a ha => ?_⟩
      · rw [netOf_sub, netOf_single A _ hji, hd1 k, incidence_eq hne]
        ring
      · obtain ⟨h1, h2, h3⟩ := hd2 a ha
        by_cases hab : a = (j, i)
        · subst hab
          simp only [if_true]
          refine ⟨?_, fun hp => h2 (by linarith), fun _ => (hslack _ ha).2 hpos⟩
          calc |d (j, i) - ε| ≤ |d (j, i)| + |ε| := abs_sub _ _
            _ ≤ ((n + 1 : ℕ) : ℝ) * ε := by rw [abs_of_nonneg hε]; push_cast; linarith
        · simp only [hab, if_false, sub_zero]
          refine ⟨?_, h2, h3⟩
          calc |d a| ≤ n * ε := h1
            _ ≤ ((n + 1 : ℕ) : ℝ) * ε := by push_cast; nlinarith


theorem improve (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (s t : N) (hst : s ≠ t)
    (x : N × N → ℝ) (w : ℝ) (hx : IsMaxFlowFeasible A u s t x w) {n : ℕ}
    (h : Reach A u x s t n) : ∃ x' w', IsMaxFlowFeasible A u s t x' w' ∧ w < w' := by
  obtain ⟨ρ, hρ, hslack⟩ := exists_slack A u x
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hεpos : 0 < ρ / ((n : ℝ) + 1) := div_pos hρ hn1
  have hnε : (n : ℝ) * (ρ / ((n : ℝ) + 1)) ≤ ρ := by
    rw [← mul_div_assoc, div_le_iff₀ hn1]
    nlinarith
  obtain ⟨d, hd1, hd2⟩ := aug A hA u x s ρ hslack h _ hεpos.le hnε
  refine ⟨fun a => x a + d a, w + ρ / ((n : ℝ) + 1), ⟨?_, ?_, ?_⟩, by linarith⟩
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := hd2 a ha
    obtain ⟨hx0, hxu⟩ := hx.1 a ha
    have hb := abs_le.1 (h1.trans hnε)
    constructor
    · by_cases hneg : d a < 0
      · have := h3 hneg; linarith [hb.1]
      · linarith [not_lt.1 hneg]
    · by_cases hp : 0 < d a
      · have := h2 hp; linarith [hb.2]
      · linarith [not_lt.1 hp]
  · linarith [hx.2.1]
  · intro k
    have e1 := netOf_eq A hA (fun a => x a + d a) k
    have e2 := netOf_eq A hA x k
    rw [netOf_add] at e1
    have e3 := hd1 k
    have e4 := hx.2.2 k
    by_cases hks : k = s
    · have hkt : k ≠ t := fun e => hst (hks.symm.trans e)
      simp only [if_pos hks, if_neg hkt] at e3 e4 ⊢
      linarith
    · by_cases hkt : k = t
      · simp only [if_neg hks, if_pos hkt] at e3 e4 ⊢
        linarith
      · simp only [if_neg hks, if_neg hkt] at e3 e4 ⊢
        linarith

theorem feasible_trunc (A : Finset (N × N)) (u : N × N → ℝ) (s t : N) (x : N × N → ℝ) (w : ℝ)
    (hx : IsMaxFlowFeasible A u s t x w) :
    IsMaxFlowFeasible A u s t (fun a => if a ∈ A then x a else 0) w := by
  have hsum : ∀ (P : N × N → Prop) [DecidablePred P],
      ∑ a ∈ A.filter P, (if a ∈ A then x a else 0) = ∑ a ∈ A.filter P, x a :=
    fun P _ => Finset.sum_congr rfl (fun a ha => if_pos (Finset.mem_filter.1 ha).1)
  refine ⟨fun a ha => by simpa [ha] using hx.1 a ha, hx.2.1, fun k => ?_⟩
  have := hx.2.2 k
  rw [hsum, hsum]
  exact this

end FlowLib

section Existence
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem exists_max_flow (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ)
    (hu : ∀ a ∈ A, 0 ≤ u a) (s t : N) (hst : s ≠ t) :
    ∃ (x : N × N → ℝ) (w : ℝ), IsMaxFlowFeasible A u s t x w ∧
      ∀ (x' : N × N → ℝ) (w' : ℝ), IsMaxFlowFeasible A u s t x' w' → w' ≤ w := by
  set K : Set ((N × N → ℝ) × ℝ) :=
    {p | IsMaxFlowFeasible A u s t p.1 p.2 ∧ ∀ a, a ∉ A → p.1 a = 0} with hK
  have hKclosed : IsClosed K := by
    have c1 : IsClosed {p : (N × N → ℝ) × ℝ | ∀ a ∈ A, 0 ≤ p.1 a ∧ p.1 a ≤ u a} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter (fun a => isClosed_iInter (fun _ => ?_))
      have hc : Continuous fun p : (N × N → ℝ) × ℝ => p.1 a := (continuous_apply a).comp continuous_fst
      exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
    have c2 : IsClosed {p : (N × N → ℝ) × ℝ | 0 ≤ p.2} :=
      isClosed_le continuous_const continuous_snd
    have c3 : IsClosed {p : (N × N → ℝ) × ℝ | ∀ k : N,
        (∑ a ∈ A.filter (fun a => a.2 = k), p.1 a) + (if k = s then p.2 else 0) -
          ((∑ a ∈ A.filter (fun a => a.1 = k), p.1 a) + (if k = t then p.2 else 0)) = 0} := by
      simp only [Set.ofPred_forall]
      refine isClosed_iInter (fun k => isClosed_eq ?_ continuous_const)
      refine Continuous.sub (Continuous.add ?_ ?_) (Continuous.add ?_ ?_)
      · exact continuous_finsetSum _ (fun a _ => by fun_prop)
      · split_ifs <;> fun_prop
      · exact continuous_finsetSum _ (fun a _ => by fun_prop)
      · split_ifs <;> fun_prop
    have c4 : IsClosed {p : (N × N → ℝ) × ℝ | ∀ a, a ∉ A → p.1 a = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun a => isClosed_iInter (fun _ => isClosed_eq (by fun_prop) continuous_const))
    have : K = {p : (N × N → ℝ) × ℝ | ∀ a ∈ A, 0 ≤ p.1 a ∧ p.1 a ≤ u a} ∩
        ({p | 0 ≤ p.2} ∩ ({p | ∀ k : N,
        (∑ a ∈ A.filter (fun a => a.2 = k), p.1 a) + (if k = s then p.2 else 0) -
          ((∑ a ∈ A.filter (fun a => a.1 = k), p.1 a) + (if k = t then p.2 else 0)) = 0} ∩
          {p | ∀ a, a ∉ A → p.1 a = 0})) := by
      ext p
      simp only [hK, IsMaxFlowFeasible, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
    rw [this]
    exact c1.inter (c2.inter (c3.inter c4))
  have hcut : IsCut s t ({s} : Finset N) := by
    refine ⟨Finset.mem_singleton_self s, ?_⟩
    simpa using Ne.symm hst
  have hKcompact : IsCompact K := by
    have hB : IsCompact ((Set.pi Set.univ (fun a : N × N => Set.Icc (0 : ℝ) (if a ∈ A then u a else 0))) ×ˢ
        Set.Icc (0 : ℝ) (cutCapacity A u {s})) :=
      (isCompact_univ_pi (fun a => isCompact_Icc)).prod isCompact_Icc
    refine hB.of_isClosed_subset hKclosed ?_
    intro p hp
    refine ⟨fun a _ => ?_, hp.1.2.1, flow_le_cap A hA u s t p.1 p.2 hp.1 {s} hcut⟩
    by_cases ha : a ∈ A
    · simpa [ha] using hp.1.1 a ha
    · simp [ha, hp.2 a ha]
  have hne : (Prod.snd '' K).Nonempty := by
    refine ⟨0, (0, 0), ⟨⟨fun a ha => ⟨le_refl _, hu a ha⟩, le_refl _, fun k => by simp⟩, fun a _ => rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := (hKcompact.image continuous_snd).exists_isGreatest hne
  obtain ⟨p, hpK, rfl⟩ := hw.1
  refine ⟨p.1, p.2, hpK.1, fun x' w' h' => ?_⟩
  exact hw.2 ⟨(fun a => if a ∈ A then x' a else 0, w'),
    ⟨feasible_trunc A u s t x' w' h', fun a ha => by simp [ha]⟩, rfl⟩

theorem max_flow_min_cut_core (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ)
    (hu : ∀ a ∈ A, 0 ≤ u a) (s t : N) (hst : s ≠ t) :
    ∃ v : ℝ,
      IsGreatest {w : ℝ | ∃ x : N × N → ℝ, IsMaxFlowFeasible A u s t x w} v ∧
      IsLeast {κ : ℝ | ∃ C : Finset N, IsCut s t C ∧ cutCapacity A u C = κ} v := by
  classical
  obtain ⟨x, w, hxw, hmax⟩ := exists_max_flow A hA u hu s t hst
  set C : Finset N := Finset.univ.filter (fun v => ∃ n, Reach A u x s v n) with hCdef
  have hmem : ∀ v, v ∈ C ↔ ∃ n, Reach A u x s v n := fun v => by simp [hCdef]
  have hsC : s ∈ C := (hmem s).2 ⟨0, Reach.start⟩
  have htC : t ∉ C := by
    intro ht
    obtain ⟨n, hn⟩ := (hmem t).1 ht
    obtain ⟨x', w', h', hlt⟩ := improve A hA u s t hst x w hxw hn
    exact absurd (hmax x' w' h') (not_le.2 hlt)
  have hcut : IsCut s t C := ⟨hsC, htC⟩
  have hout : ∀ a ∈ A.filter (fun a => a.1 ∈ C ∧ a.2 ∉ C), x a = u a := by
    intro a ha
    obtain ⟨haA, h1, h2⟩ := Finset.mem_filter.1 ha
    by_contra hne
    have hlt : x a < u a := lt_of_le_of_ne (hxw.1 a haA).2 hne
    obtain ⟨n, hn⟩ := (hmem _).1 h1
    exact h2 ((hmem _).2 ⟨n + 1, Reach.step hn (Or.inl ⟨by simpa using haA, by simpa using hlt⟩)⟩)
  have hin : ∀ a ∈ A.filter (fun a => a.1 ∉ C ∧ a.2 ∈ C), x a = 0 := by
    intro a ha
    obtain ⟨haA, h1, h2⟩ := Finset.mem_filter.1 ha
    by_contra hne
    have hpos : 0 < x a := lt_of_le_of_ne (hxw.1 a haA).1 (Ne.symm hne)
    obtain ⟨n, hn⟩ := (hmem _).1 h2
    exact h1 ((hmem _).2 ⟨n + 1, Reach.step hn (Or.inr ⟨by simpa using haA, by simpa using hpos⟩)⟩)
  have hid := cut_identity A hA u s t x w hxw C hcut
  have hcap : cutCapacity A u C = w := by
    rw [Finset.sum_congr rfl hout, Finset.sum_eq_zero hin, sub_zero] at hid
    unfold cutCapacity
    rw [← hid]
  refine ⟨w, ⟨⟨x, hxw⟩, ?_⟩, ⟨⟨C, hcut, hcap⟩, ?_⟩⟩
  · rintro w' ⟨x', hx'⟩
    exact hmax x' w' hx'
  · rintro κ ⟨C', hC', rfl⟩
    exact flow_le_cap A hA u s t x w hxw C' hC'

end Existence

end VanderbeiLP.Networks

open VanderbeiLP.Networks in
theorem solution {N : Type*} [Fintype N] [DecidableEq N]
    (A : Finset (N × N)) (hA : IsNetwork A) (u : N × N → ℝ) (hu : ∀ a ∈ A, 0 ≤ u a)
    (s t : N) (hst : s ≠ t) :
    ∃ v : ℝ,
      IsGreatest {w : ℝ | ∃ x : N × N → ℝ, IsMaxFlowFeasible A u s t x w} v ∧
      IsLeast {κ : ℝ | ∃ C : Finset N, IsCut s t C ∧ cutCapacity A u C = κ} v :=
  max_flow_min_cut_core A hA u hu s t hst
