-- Prove2me | solution 1 for RandomGreedyMIS.total_calls_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:31:58.64462+00:00
-- url     : https://prove2.me/submissions/bfc59b59-e44d-4ce1-b05e-c3eafea88520

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Definitions.Def_RandomGreedyMIS_basic

namespace MTSPRG
open Finset RandomGreedyMIS
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### Characterisations -/

lemma inMIS_eq_true (π : Equiv.Perm (Fin n)) (v : Fin n) :
    inMIS G π v = true ↔ ∀ w, G.Adj v w → π w < π v → inMIS G π w = false := by
  rw [inMIS]
  simp only [List.all_eq_true, List.mem_finRange, true_implies]
  constructor
  · intro h w hw hlt
    have := h w
    rw [dif_pos ⟨hw, hlt⟩] at this
    simpa using this
  · intro h w
    split_ifs with hw
    · simpa using h w hw.1 hw.2
    · rfl

/-- `y` queries `x` (directly invokes `RGMIS(x)`) in the computation of `RGMIS(y)`. -/
def Qry (π : Equiv.Perm (Fin n)) (y x : Fin n) : Prop :=
  G.Adj y x ∧ π x < π y ∧ ∀ u, G.Adj y u → π u < π x → inMIS G π u = false

instance (π : Equiv.Perm (Fin n)) (y : Fin n) : DecidablePred (Qry G π y) := fun x => by
  unfold Qry; infer_instance

lemma loopCost_eq {α : Type*} [DecidableEq α] (ρ : α → ℕ) (mis : α → Bool) (f : α → ℕ) :
    ∀ L : List α, L.Pairwise (fun a b => ρ a < ρ b) →
      loopCost (L.map fun w => (mis w, f w)) =
        ∑ w ∈ L.toFinset.filter (fun w => ∀ u ∈ L, ρ u < ρ w → mis u = false), f w
  | [], _ => by simp [loopCost]
  | a :: rest, hp => by
    rw [List.pairwise_cons] at hp
    obtain ⟨ha, hp⟩ := hp
    have ih := loopCost_eq ρ mis f rest hp
    have hnot : a ∉ rest.toFinset := by
      intro h; have := ha a (List.mem_toFinset.1 h); omega
    simp only [List.map_cons, loopCost, List.toFinset_cons]
    have hpa : ∀ u ∈ a :: rest, ρ u < ρ a → mis u = false := by
      intro u hu hlt
      rcases List.mem_cons.1 hu with rfl | hu
      · omega
      · have := ha u hu; omega
    rw [Finset.filter_insert, if_pos hpa]
    rw [Finset.sum_insert (fun h => hnot (Finset.mem_filter.1 h).1)]
    congr 1
    cases hm : mis a
    · simp only [Bool.false_eq_true, if_false]
      rw [ih]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      apply Finset.filter_congr
      intro w _
      constructor
      · intro h u hu hlt
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hm
        · exact h u hu hlt
      · intro h u hu hlt; exact h u (List.mem_cons_of_mem _ hu) hlt
    · simp only [if_true]
      symm
      apply Finset.sum_eq_zero
      intro w hw
      exfalso
      rw [Finset.mem_filter] at hw
      have := hw.2 a List.mem_cons_self (ha w (List.mem_toFinset.1 hw.1))
      rw [hm] at this
      exact Bool.noConfusion this

lemma lowerNbrs_pairwise (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (lowerNbrs G π v).Pairwise (fun a b => ((π a : Fin n) : ℕ) < π b) := by
  unfold lowerNbrs
  apply List.Pairwise.filter
  rw [List.pairwise_map]
  refine (List.pairwise_lt_finRange n).imp ?_
  intro a b h
  simpa using h

lemma calls_eq (π : Equiv.Perm (Fin n)) (v : Fin n) :
    calls G π v = ∑ x ∈ univ.filter (Qry G π v), (1 + calls G π x) := by
  rw [calls]
  rw [List.attach_map_val (f := fun w => (inMIS G π w, 1 + calls G π w))]
  rw [loopCost_eq (fun w => ((π w : Fin n) : ℕ)) (inMIS G π) (fun w => 1 + calls G π w) _
    (lowerNbrs_pairwise G π v)]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset, mem_lowerNbrs, Finset.mem_univ, true_and, Qry]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun u hu hlt => h3 u ⟨hu, lt_trans hlt h2⟩ hlt⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun u hu hlt => h3 u hu.1 hlt⟩

end MTSPRG


namespace MTSPRG
open RandomGreedyMIS

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-! ### Locality: `inMIS` and `calls` at a vertex only depend on the ranks below it -/

section Locality

variable (π π' : Equiv.Perm (Fin n)) (k : ℕ)
  (h1 : ∀ x, (π x : ℕ) < k → π' x = π x)
  (h2 : ∀ x, (π' x : ℕ) < k → (π x : ℕ) < k)
include h1 h2

lemma lt_local {a : Fin n} (ha : (π a : ℕ) < k) (w : Fin n) : π' w < π' a ↔ π w < π a := by
  rw [h1 a ha]
  constructor
  · intro hw
    have : (π' w : ℕ) < k := lt_trans (Fin.lt_def.1 hw) ha
    rw [← h1 w (h2 w this)]; exact hw
  · intro hw
    have : (π w : ℕ) < k := lt_trans (Fin.lt_def.1 hw) ha
    rw [h1 w this]; exact hw

lemma inMIS_local : ∀ v, (π v : ℕ) < k → inMIS G π' v = inMIS G π v := by
  suffices H : ∀ m, ∀ v, (π v : ℕ) = m → (π v : ℕ) < k → inMIS G π' v = inMIS G π v from
    fun v => H _ v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hm hv
    have key : ∀ w, π w < π v → inMIS G π' w = inMIS G π w := by
      intro w hw
      have := Fin.lt_def.1 hw
      exact ih _ (by omega) w rfl (by omega)
    apply Bool.eq_iff_iff.2
    rw [inMIS_eq_true, inMIS_eq_true]
    constructor
    · intro h w hw hlt
      rw [← key w hlt]
      exact h w hw ((lt_local π π' k h1 h2 hv w).2 hlt)
    · intro h w hw hlt
      have hlt' := (lt_local π π' k h1 h2 hv w).1 hlt
      rw [key w hlt']
      exact h w hw hlt'

lemma cond_local (y : Fin n) {x : Fin n} (hx : (π x : ℕ) < k) :
    (∀ u, G.Adj y u → π' u < π' x → inMIS G π' u = false) ↔
      (∀ u, G.Adj y u → π u < π x → inMIS G π u = false) := by
  have key : ∀ u, π u < π x → inMIS G π' u = inMIS G π u := by
    intro u hu
    exact inMIS_local G π π' k h1 h2 u (lt_trans (Fin.lt_def.1 hu) hx)
  constructor
  · intro h u hu hlt
    rw [← key u hlt]
    exact h u hu ((lt_local π π' k h1 h2 hx u).2 hlt)
  · intro h u hu hlt
    have hlt' := (lt_local π π' k h1 h2 hx u).1 hlt
    rw [key u hlt']
    exact h u hu hlt'

lemma qry_local {y : Fin n} (hy : (π y : ℕ) < k) (x : Fin n) :
    Qry G π' y x ↔ Qry G π y x := by
  unfold Qry
  constructor
  · rintro ⟨ha, hlt, hc⟩
    have hlt' := (lt_local π π' k h1 h2 hy x).1 hlt
    have hx : (π x : ℕ) < k := lt_trans (Fin.lt_def.1 hlt') hy
    exact ⟨ha, hlt', (cond_local G π π' k h1 h2 y hx).1 hc⟩
  · rintro ⟨ha, hlt, hc⟩
    have hx : (π x : ℕ) < k := lt_trans (Fin.lt_def.1 hlt) hy
    exact ⟨ha, (lt_local π π' k h1 h2 hy x).2 hlt, (cond_local G π π' k h1 h2 y hx).2 hc⟩

lemma calls_local : ∀ v, (π v : ℕ) < k → calls G π' v = calls G π v := by
  suffices H : ∀ m, ∀ v, (π v : ℕ) = m → (π v : ℕ) < k → calls G π' v = calls G π v from
    fun v => H _ v rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hm hv
    rw [calls_eq, calls_eq]
    have hs : univ.filter (Qry G π' v) = univ.filter (Qry G π v) :=
      Finset.filter_congr (fun x _ => qry_local G π π' k h1 h2 hv x)
    rw [hs]
    apply Finset.sum_congr rfl
    intro x hx
    have hq := (Finset.mem_filter.1 hx).2.2.1
    have := Fin.lt_def.1 hq
    rw [ih _ (by omega) x rfl (by omega)]

end Locality

/-! ### The potential -/

/-- `z` is dominated by the greedy MIS among the vertices of rank `< t`. -/
def dom (π : Equiv.Perm (Fin n)) (t : ℕ) (z : Fin n) : Prop :=
  ∃ w, G.Adj z w ∧ (π w : ℕ) < t ∧ inMIS G π w = true

instance (π : Equiv.Perm (Fin n)) (t : ℕ) : DecidablePred (dom G π t) := fun z => by
  unfold dom; infer_instance

/-- Partial cost of the computation started at `y`: calls to neighbours of rank `< t`. -/
def Sp (π : Equiv.Perm (Fin n)) (t : ℕ) (y : Fin n) : ℕ :=
  ∑ x ∈ univ.filter (fun x => Qry G π y x ∧ (π x : ℕ) < t), (1 + calls G π x)

/-- Unrevealed, undominated neighbours of `y`. -/
def Fr (π : Equiv.Perm (Fin n)) (t : ℕ) (y : Fin n) : Finset (Fin n) :=
  univ.filter (fun z => G.Adj y z ∧ t ≤ (π z : ℕ) ∧ ¬ dom G π t z)

/-- Unrevealed vertices. -/
def Un (π : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  univ.filter (fun v => t ≤ (π v : ℕ))

/-- Twice the potential `Φ_t = |Q_t| + |D_t|/2`. -/
def Psi (π : Equiv.Perm (Fin n)) (t : ℕ) : ℕ :=
  2 * ∑ y, Sp G π t y + ∑ y ∈ Un π t, (1 + Sp G π t y) * (Fr G π t y).card

lemma mem_Fr (π : Equiv.Perm (Fin n)) (t : ℕ) (y z : Fin n) :
    z ∈ Fr G π t y ↔ G.Adj y z ∧ t ≤ (π z : ℕ) ∧ ¬ dom G π t z := by
  simp [Fr]

lemma mem_Un (π : Equiv.Perm (Fin n)) (t : ℕ) (y : Fin n) :
    y ∈ Un π t ↔ t ≤ (π y : ℕ) := by
  simp [Un]

lemma Sp_eq_calls (π : Equiv.Perm (Fin n)) (t : ℕ) (y : Fin n) (hy : (π y : ℕ) ≤ t) :
    Sp G π t y = calls G π y := by
  rw [Sp, calls_eq]
  congr 1
  apply Finset.filter_congr
  intro x _
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, lt_of_lt_of_le (Fin.lt_def.1 h.2.1) hy⟩

lemma Psi_zero (π : Equiv.Perm (Fin n)) : Psi G π 0 = 2 * G.edgeFinset.card := by
  have hS : ∀ y, Sp G π 0 y = 0 := by
    intro y; simp [Sp]
  have hU : Un π 0 = univ := by ext; simp [Un]
  have hF : ∀ y, Fr G π 0 y = G.neighborFinset y := by
    intro y; ext z; simp [Fr, dom]
  simp only [Psi, hS, hU, hF, Finset.sum_const_zero, mul_zero, zero_add, add_zero, one_mul,
    SimpleGraph.card_neighborFinset_eq_degree]
  exact G.sum_degrees_eq_twice_card_edges

lemma Psi_n (π : Equiv.Perm (Fin n)) : Psi G π n = 2 * ∑ y, calls G π y := by
  have hU : Un π n = ∅ := by
    ext y; simp [Un, (π y).isLt]
  simp only [Psi, hU, Finset.sum_empty, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact Sp_eq_calls G π n y (le_of_lt (π y).isLt)

/-! ### One step: revealing the vertex `v` at time `t` -/

section Step

variable (π π' : Equiv.Perm (Fin n)) (t : ℕ) (v : Fin n)
  (hA : ∀ x, (π x : ℕ) < t → π' x = π x)
  (hC : (π' v : ℕ) = t)
  (hD : ∀ x, x ≠ v → t ≤ (π x : ℕ) → t < (π' x : ℕ))
  (hv : t ≤ (π v : ℕ))
include hA hC hD

omit hA in
lemma hB : ∀ x, (π' x : ℕ) < t → (π x : ℕ) < t := by
  intro x hx
  by_contra hcon
  push Not at hcon
  by_cases hxv : x = v
  · subst hxv; omega
  · have := hD x hxv hcon; omega

lemma lt_succ_iff' (x : Fin n) : (π' x : ℕ) < t + 1 ↔ (π x : ℕ) < t ∨ x = v := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := hD x hcon.2 hcon.1
    omega
  · rintro (h | rfl)
    · rw [hA x h]; omega
    · omega

lemma condv (y : Fin n) :
    (∀ u, G.Adj y u → π' u < π' v → inMIS G π' u = false) ↔ ¬ dom G π t y := by
  have hB' := hB π π' t v hC hD
  unfold dom
  push Not
  constructor
  · intro h w hw hlt
    have h' := h w hw (by rw [Fin.lt_def, hC, hA w hlt]; exact hlt)
    rw [inMIS_local G π π' t hA hB' w hlt] at h'
    simp [h']
  · intro h u hu hlt
    rw [Fin.lt_def, hC] at hlt
    have hu' := hB' u hlt
    rw [inMIS_local G π π' t hA hB' u hu']
    simpa using h u hu hu'

lemma misv : inMIS G π' v = true ↔ ¬ dom G π t v :=
  (inMIS_eq_true G π' v).trans (condv G π π' t v hA hC hD v)

lemma dom_step (z : Fin n) :
    dom G π' (t + 1) z ↔ dom G π t z ∨ (G.Adj z v ∧ ¬ dom G π t v) := by
  have hB' := hB π π' t v hC hD
  constructor
  · rintro ⟨w, hw, hlt, hm⟩
    rcases (lt_succ_iff' π π' t v hA hC hD w).1 hlt with h | rfl
    · left
      refine ⟨w, hw, h, ?_⟩
      rwa [inMIS_local G π π' t hA hB' w h] at hm
    · right
      exact ⟨hw, (misv G π π' t w hA hC hD).1 hm⟩
  · rintro (⟨w, hw, hlt, hm⟩ | ⟨hw, hd⟩)
    · refine ⟨w, hw, by rw [hA w hlt]; omega, ?_⟩
      rwa [inMIS_local G π π' t hA hB' w hlt]
    · exact ⟨v, hw, by omega, (misv G π π' t v hA hC hD).2 hd⟩

lemma le_succ_iff' (x : Fin n) : t + 1 ≤ (π' x : ℕ) ↔ x ≠ v ∧ t ≤ (π x : ℕ) := by
  have := lt_succ_iff' π π' t v hA hC hD x
  constructor
  · intro h
    by_contra hcon
    have : (π' x : ℕ) < t + 1 := by
      apply this.2
      by_cases hxv : x = v
      · exact Or.inr hxv
      · left; push Not at hcon; exact hcon hxv
    omega
  · rintro ⟨h1, h2⟩
    exact hD x h1 h2

lemma Un_step : Un π' (t + 1) = (Un π t).erase v := by
  ext x
  rw [mem_Un, Finset.mem_erase, mem_Un, le_succ_iff' π π' t v hA hC hD]

lemma Fr_step (y : Fin n) :
    Fr G π' (t + 1) y =
      (Fr G π t y).filter (fun z => z ≠ v ∧ ¬ (G.Adj z v ∧ ¬ dom G π t v)) := by
  ext z
  rw [Finset.mem_filter, mem_Fr, mem_Fr, le_succ_iff' π π' t v hA hC hD,
    dom_step G π π' t v hA hC hD]
  tauto

lemma calls_v (hv : t ≤ (π v : ℕ)) : calls G π' v = Sp G π t v := by
  have hB' := hB π π' t v hC hD
  rw [calls_eq, Sp, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (π x : ℕ) < t
  · have hq : Qry G π' v x ↔ Qry G π v x := by
      unfold Qry
      have e1 : π' x < π' v := by rw [Fin.lt_def, hC, hA x hx]; exact hx
      have e2 : π x < π v := by rw [Fin.lt_def]; omega
      rw [cond_local G π π' t hA hB' v hx]
      tauto
    rw [calls_local G π π' t hA hB' x hx]
    by_cases hqx : Qry G π v x
    · rw [if_pos (hq.2 hqx), if_pos ⟨hqx, hx⟩]
    · rw [if_neg (fun h => hqx (hq.1 h)), if_neg (fun h => hqx h.1)]
  · have hq : ¬ Qry G π' v x := by
      intro h
      have := Fin.lt_def.1 h.2.1
      rw [hC] at this
      exact hx (hB' x this)
    rw [if_neg hq, if_neg (fun h => hx h.2)]

lemma Sp_step (hv : t ≤ (π v : ℕ)) (y : Fin n) :
    Sp G π' (t + 1) y = Sp G π t y + if y ∈ Fr G π t v then 1 + Sp G π t v else 0 := by
  have hB' := hB π π' t v hC hD
  by_cases hy : (π y : ℕ) < t
  · have hnot : y ∉ Fr G π t v := by
      rw [mem_Fr]; omega
    rw [if_neg hnot, add_zero, Sp_eq_calls G π' (t+1) y (by rw [hA y hy]; omega),
      Sp_eq_calls G π t y hy.le, calls_local G π π' t hA hB' y hy]
  by_cases hyv : y = v
  · subst hyv
    have hnot : y ∉ Fr G π t y := by
      rw [mem_Fr]; exact fun h => G.irrefl h.1
    rw [if_neg hnot, add_zero, Sp_eq_calls G π' (t+1) y (by omega),
      calls_v G π π' t y hA hC hD hv]
  push Not at hy
  have hty := hD y hyv hy
  have hsum : (if y ∈ Fr G π t v then 1 + Sp G π t v else 0) =
      ∑ x, if x = v then (if y ∈ Fr G π t v then 1 + Sp G π t v else 0) else 0 := by
    rw [Finset.sum_ite_eq']; simp
  rw [hsum, Sp, Sp, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxv : x = v
  · subst hxv
    have hn : ¬ (Qry G π y x ∧ (π x : ℕ) < t) := fun h => by omega
    rw [if_neg hn, zero_add, if_pos rfl, calls_v G π π' t x hA hC hD hv]
    have hiff : (Qry G π' y x ∧ (π' x : ℕ) < t + 1) ↔ y ∈ Fr G π t x := by
      rw [mem_Fr]
      unfold Qry
      rw [condv G π π' t x hA hC hD y, G.adj_comm]
      have e1 : π' x < π' y := by rw [Fin.lt_def]; omega
      have e2 : (π' x : ℕ) < t + 1 := by omega
      tauto
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · rw [if_neg hxv, add_zero]
    by_cases hx : (π x : ℕ) < t
    · have hq : Qry G π' y x ↔ Qry G π y x := by
        unfold Qry
        have e1 : π' x < π' y := by rw [Fin.lt_def, hA x hx]; omega
        have e2 : π x < π y := by rw [Fin.lt_def]; omega
        rw [cond_local G π π' t hA hB' y hx]
        tauto
      have e3 : (π' x : ℕ) < t + 1 := by rw [hA x hx]; omega
      rw [calls_local G π π' t hA hB' x hx]
      by_cases hqx : Qry G π y x
      · rw [if_pos ⟨hq.2 hqx, e3⟩, if_pos ⟨hqx, hx⟩]
      · rw [if_neg (fun h => hqx (hq.1 h.1)), if_neg (fun h => hqx h.1)]
    · have e3 := hD x hxv (by omega)
      rw [if_neg (fun h => by omega), if_neg (fun h => hx h.2)]

lemma Psi_step_le (hv : t ≤ (π v : ℕ)) :
    Psi G π' (t + 1) ≤ 2 * ∑ y, Sp G π t y + 2 * ((Fr G π t v).card * (1 + Sp G π t v)) +
      ∑ y ∈ (Un π t).erase v, (1 + Sp G π t y) *
        ((Fr G π t y).filter (fun z => z ≠ v ∧ ¬ (G.Adj z v ∧ ¬ dom G π t v))).card +
      (1 + Sp G π t v) * ∑ y ∈ Fr G π t v, ((Fr G π t y).erase v).card := by
  have hS := Sp_step G π π' t v hA hC hD hv
  have hF := Fr_step G π π' t v hA hC hD
  unfold Psi
  rw [Un_step π π' t v hA hC hD]
  simp only [hS, hF]
  have h1 : ∑ y, (Sp G π t y + if y ∈ Fr G π t v then 1 + Sp G π t v else 0) =
      ∑ y, Sp G π t y + (Fr G π t v).card * (1 + Sp G π t v) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      smul_eq_mul]
  rw [h1]
  set c := 1 + Sp G π t v with hc
  have h2 : ∀ y, (1 + (Sp G π t y + if y ∈ Fr G π t v then c else 0)) *
      ((Fr G π t y).filter (fun z => z ≠ v ∧ ¬ (G.Adj z v ∧ ¬ dom G π t v))).card =
      (1 + Sp G π t y) *
      ((Fr G π t y).filter (fun z => z ≠ v ∧ ¬ (G.Adj z v ∧ ¬ dom G π t v))).card +
      (if y ∈ Fr G π t v then c else 0) *
      ((Fr G π t y).filter (fun z => z ≠ v ∧ ¬ (G.Adj z v ∧ ¬ dom G π t v))).card := by
    intro y; ring
  simp only [h2]
  rw [Finset.sum_add_distrib]
  have h3 : ∑ y ∈ (Un π t).erase v, (if y ∈ Fr G π t v then c else 0) *
      ((Fr G π t y).filter (fun z => z ≠ v ∧ ¬ (G.Adj z v ∧ ¬ dom G π t v))).card ≤
      c * ∑ y ∈ Fr G π t v, ((Fr G π t y).erase v).card := by
    rw [Finset.mul_sum]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    calc _ ≤ ∑ y ∈ ((Un π t).erase v).filter (fun y => y ∈ Fr G π t v),
          c * ((Fr G π t y).erase v).card := by
          apply Finset.sum_le_sum
          intro y _
          apply Nat.mul_le_mul_left
          apply Finset.card_le_card
          intro z hz
          rw [Finset.mem_filter] at hz
          exact Finset.mem_erase.2 ⟨hz.2.1, hz.1⟩
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset
          intro y hy
          exact (Finset.mem_filter.1 hy).2
  omega

end Step

/-- The counting identity behind `E[Δ|D|] ≤ -2|D|/(n-t)`. -/
lemma count_eq (π : Equiv.Perm (Fin n)) (t : ℕ) (y z : Fin n) (hy : y ∈ Un π t)
    (hz : z ∈ Fr G π t y) :
    2 + ((Fr G π t z).erase y).card +
      ((Un π t).erase y |>.filter (fun w => z ≠ w ∧ ¬ (G.Adj z w ∧ ¬ dom G π t w))).card =
      (Un π t).card := by
  rw [mem_Fr] at hz
  have hzU : z ∈ (Un π t).erase y :=
    Finset.mem_erase.2 ⟨(G.ne_of_adj hz.1).symm, (mem_Un π t z).2 hz.2.1⟩
  set W := ((Un π t).erase y).erase z with hW
  have e1 : (Fr G π t z).erase y = W.filter (fun w => G.Adj z w ∧ ¬ dom G π t w) := by
    ext w
    simp only [Finset.mem_erase, Finset.mem_filter, mem_Fr, hW, mem_Un]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨(G.ne_of_adj h2).symm, h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨_, h1, h3⟩, h2, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  have e2 : ((Un π t).erase y).filter (fun w => z ≠ w ∧ ¬ (G.Adj z w ∧ ¬ dom G π t w)) =
      W.filter (fun w => ¬ (G.Adj z w ∧ ¬ dom G π t w)) := by
    ext w
    simp only [Finset.mem_erase, Finset.mem_filter, hW]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun h => h2 h.symm, h1⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, fun h => h1 h.symm, h3⟩
  rw [e1, e2, add_assoc, Finset.card_filter_add_card_filter_not]
  have h1 := Finset.card_erase_add_one hzU
  have h2 := Finset.card_erase_add_one hy
  rw [← hW] at h1
  omega

/-- The supermartingale inequality, for one prefix (given by `π` and `t`), averaged over the
`|U|` choices of the next revealed vertex. -/
lemma step_ineq (π : Equiv.Perm (Fin n)) (t : ℕ) (P : Fin n → Equiv.Perm (Fin n))
    (hP : ∀ v ∈ Un π t, (∀ x, (π x : ℕ) < t → P v x = π x) ∧ ((P v v : Fin n) : ℕ) = t ∧
      (∀ x, x ≠ v → t ≤ (π x : ℕ) → t < (P v x : ℕ))) :
    ∑ v ∈ Un π t, Psi G (P v) (t + 1) ≤ (Un π t).card * Psi G π t := by
  set U := Un π t with hU
  set S := ∑ y, Sp G π t y with hSdef
  let c : Fin n → ℕ := fun y => 1 + Sp G π t y
  let F : Fin n → Finset (Fin n) := fun y => Fr G π t y
  let Pr : Fin n → Fin n → Prop := fun z w => z ≠ w ∧ ¬ (G.Adj z w ∧ ¬ dom G π t w)
  have hbound : ∑ v ∈ U, Psi G (P v) (t + 1) ≤
      ∑ v ∈ U, (2 * S + (2 * ((F v).card * c v) + c v * ∑ y ∈ F v, ((F y).erase v).card) +
        ∑ y ∈ U.erase v, c y * ((F y).filter (fun z => Pr z v)).card) := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨hA, hC, hD⟩ := hP v hv
    have := Psi_step_le G π (P v) t v hA hC hD ((mem_Un π t v).1 hv)
    rw [← hU] at this
    simp only [c, F, Pr]
    omega
  refine hbound.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  -- the `X` part
  have hX : ∑ v ∈ U, (2 * ((F v).card * c v) + c v * ∑ y ∈ F v, ((F y).erase v).card) =
      ∑ y ∈ U, c y * ∑ z ∈ F y, (2 + ((F z).erase y).card) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    ring
  -- the `Y` part
  have hY : ∑ v ∈ U, ∑ y ∈ U.erase v, c y * ((F y).filter (fun z => Pr z v)).card =
      ∑ y ∈ U, c y * ∑ z ∈ F y, ((U.erase y).filter (fun w => Pr z w)).card := by
    rw [Finset.sum_comm' (t' := U) (s' := fun y => U.erase y)]
    · apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum]
      congr 1
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    · intro v y
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨fun h => h2 h.symm, h1⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, fun h => h1 h.symm, h3⟩
  rw [hX, hY, add_assoc, ← Finset.sum_add_distrib]
  have hcount : ∀ y ∈ U, c y * ∑ z ∈ F y, (2 + ((F z).erase y).card) +
      c y * ∑ z ∈ F y, ((U.erase y).filter (fun w => Pr z w)).card =
      U.card * (c y * (F y).card) := by
    intro y hy
    rw [← mul_add, ← Finset.sum_add_distrib]
    have : ∀ z ∈ F y, 2 + ((F z).erase y).card +
        ((U.erase y).filter (fun w => Pr z w)).card = U.card :=
      fun z hz => count_eq G π t y z hy hz
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hcount, ← Finset.mul_sum]
  simp only [Psi, c, F, hSdef, hU]
  ring

/-! ### Averaging over permutations -/

lemma swap_props (π : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) (v : Fin n)
    (hv : t ≤ (π v : ℕ)) :
    (∀ x, (π x : ℕ) < t → (π.trans (Equiv.swap ⟨t, ht⟩ (π v))) x = π x) ∧
    (((π.trans (Equiv.swap ⟨t, ht⟩ (π v))) v : Fin n) : ℕ) = t ∧
    (∀ x, x ≠ v → t ≤ (π x : ℕ) → t < ((π.trans (Equiv.swap ⟨t, ht⟩ (π v))) x : ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Equiv.trans_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; rw [h] at hx; simp at hx
    · intro h; rw [h] at hx; omega
  · rw [Equiv.trans_apply, Equiv.swap_apply_right]
  · intro x hxv hx
    have hne : π x ≠ π v := fun h => hxv (π.injective h)
    rw [Equiv.trans_apply]
    by_cases hT : π x = ⟨t, ht⟩
    · rw [hT, Equiv.swap_apply_left]
      have : π v ≠ ⟨t, ht⟩ := fun h => hne (hT.trans h.symm)
      have : (π v : ℕ) ≠ t := fun h => this (Fin.ext h)
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hT hne]
      have : (π x : ℕ) ≠ t := fun h => hT (Fin.ext h)
      omega

lemma sum_step (t : ℕ) (ht : t < n) :
    ∑ π : Equiv.Perm (Fin n), Psi G π (t + 1) ≤ ∑ π, Psi G π t := by
  let T : Fin n := ⟨t, ht⟩
  let W := (univ : Finset (Fin n)).filter (fun s : Fin n => t ≤ (s : ℕ))
  have hW : 0 < W.card := Finset.card_pos.2 ⟨T, by simp [W, T]⟩
  have hcard : ∀ π : Equiv.Perm (Fin n), (Un π t).card = W.card := by
    intro π
    apply Finset.card_nbij' (fun v => π v) (fun s => π.symm s) <;> intro x hx <;> simp_all [Un, W]
  have hre : ∀ π : Equiv.Perm (Fin n),
      ∑ v ∈ Un π t, Psi G (π.trans (Equiv.swap T (π v))) (t + 1) =
        ∑ s ∈ W, Psi G (π.trans (Equiv.swap T s)) (t + 1) := by
    intro π
    apply Finset.sum_nbij' (fun v => π v) (fun s => π.symm s) <;> simp [Un, W]
  have hinv : ∀ s : Fin n, ∑ π : Equiv.Perm (Fin n), Psi G (π.trans (Equiv.swap T s)) (t + 1) =
      ∑ π, Psi G π (t + 1) := by
    intro s
    exact Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap T s)) _ _
      (fun π => by
        show Psi G (π.trans _) _ = Psi G (Equiv.swap T s * π) _
        rw [Equiv.Perm.mul_def])
  have key : W.card * ∑ π, Psi G π (t + 1) ≤ W.card * ∑ π, Psi G π t := by
    calc W.card * ∑ π, Psi G π (t + 1)
        = ∑ s ∈ W, ∑ π : Equiv.Perm (Fin n), Psi G (π.trans (Equiv.swap T s)) (t + 1) := by
          rw [Finset.sum_congr rfl (fun s _ => hinv s), Finset.sum_const, smul_eq_mul]
      _ = ∑ π : Equiv.Perm (Fin n), ∑ s ∈ W, Psi G (π.trans (Equiv.swap T s)) (t + 1) :=
          Finset.sum_comm
      _ = ∑ π : Equiv.Perm (Fin n), ∑ v ∈ Un π t, Psi G (π.trans (Equiv.swap T (π v))) (t + 1) :=
          Finset.sum_congr rfl (fun π _ => (hre π).symm)
      _ ≤ ∑ π : Equiv.Perm (Fin n), (Un π t).card * Psi G π t := by
          apply Finset.sum_le_sum
          intro π _
          exact step_ineq G π t _ (fun v hv => swap_props π t ht v ((mem_Un π t v).1 hv))
      _ = W.card * ∑ π, Psi G π t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun π _ => by rw [hcard π])
  exact Nat.le_of_mul_le_mul_left key hW

lemma sum_Psi_le : ∀ t, t ≤ n → ∑ π : Equiv.Perm (Fin n), Psi G π t ≤ ∑ π, Psi G π 0
  | 0, _ => le_rfl
  | t + 1, ht => (sum_step G t ht).trans (sum_Psi_le t (by omega))

/-- Per-permutation-sum version in `ℕ`: `∑_π ∑_v calls ≤ m · n!`. -/
theorem total_calls_le_nat :
    ∑ π : Equiv.Perm (Fin n), ∑ v, calls G π v ≤ G.edgeFinset.card * Nat.factorial n := by
  have h := sum_Psi_le G n le_rfl
  simp only [Psi_n, Psi_zero, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at h
  have h2 : 2 * ∑ π : Equiv.Perm (Fin n), ∑ v, calls G π v ≤
      2 * (G.edgeFinset.card * Nat.factorial n) := h.trans (le_of_eq (by ring))
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

/-- **Main theorem** (Yoshida–Yamamoto–Ito; Dalirrooyfard–Makarychev–Mitrović, Cor. 1.2):
the expected total number of recursive calls of the randomized greedy MIS oracle, summed over
all start vertices, is at most the number of edges. -/
theorem total_calls_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ π : Equiv.Perm (Fin n), ∑ v, (calls G π v : ℝ)) ≤
      (G.edgeFinset.card : ℝ) * (Nat.factorial n) := by
  have h := total_calls_le_nat G
  exact_mod_cast h

end MTSPRG

open RandomGreedyMIS in
theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ π : Equiv.Perm (Fin n), ∑ v, (calls G π v : ℝ)) ≤ (G.edgeFinset.card : ℝ) * (Nat.factorial n) :=
  MTSPRG.total_calls_le n G
