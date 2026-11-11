-- Prove2me | solution 1 for OnlineMatchFrameworks.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:02:48.40136+00:00
-- url     : https://prove2.me/submissions/15c3394e-8622-4214-be7d-0fb9244dc5e9

import Definitions.Def_OnlineMatchFrameworks_BlackBox
import Mathlib.Tactic.Ring
import Definitions.Def_OnlineMatchFrameworks_Offline
import Mathlib.Tactic
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped BigOperators
open OnlineMatchFrameworks
namespace S01.P097
variable {U V : Type*}

/-- The remaining fractional offline reward on the available items and customers. -/
def potential (G : Instance U V) (q : U → V → ℝ) (A : Finset U) (R : Finset V) : ℝ :=
  ∑ u ∈ A, (∑ v ∈ R, q u v) * G.w u

lemma potential_empty (G : Instance U V) (q : U → V → ℝ) (A : Finset U) :
    potential G q A ∅ = 0 := by
  simp [potential]

lemma potential_insert [DecidableEq V]
    (G : Instance U V) (q : U → V → ℝ) (A : Finset U) (R : Finset V)
    (v : V) (hv : v ∉ R) :
    potential G q A (insert v R) = (∑ u ∈ A, q u v * G.w u) + potential G q A R := by
  simp [potential, Finset.sum_insert hv, add_mul, Finset.sum_add_distrib]

lemma potential_erase_le [DecidableEq U] [Fintype V]
    (G : Instance U V) (q : U → V → ℝ)
    (hq : ∀ u v, 0 ≤ q u v) (hrow : ∀ u, ∑ v : V, q u v ≤ 1)
    (A : Finset U) (R : Finset V) (u : U) :
    potential G q A R ≤ G.w u + potential G q (A.erase u) R := by
  classical
  have hR : ∑ v ∈ R, q u v ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun v _ _ => hq u v)).trans (hrow u)
  have hu_bound : (∑ v ∈ R, q u v) * G.w u ≤ G.w u := by
    simpa using mul_le_mul_of_nonneg_right hR (G.w_nonneg u)
  by_cases hu : u ∈ A
  · have he : potential G q A R = potential G q (A.erase u) R + (∑ v ∈ R, q u v) * G.w u := by
      exact (Finset.sum_erase_add _ _ hu).symm
    rw [he, add_comm (G.w u)]
    exact add_le_add le_rfl hu_bound
  · rw [Finset.erase_eq_of_notMem hu]
    exact le_add_of_nonneg_left (G.w_nonneg u)

lemma potential_univ_eq [Fintype U] [Fintype V]
    (G : Instance U V) (q : U → V → ℝ) :
    potential G q Finset.univ Finset.univ = ∑ u : U, ∑ v : V, q u v * G.w u := by
  simp only [potential, Finset.sum_mul]

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks
namespace S01.P097
variable {U V : Type*} (G : Instance U V)

noncomputable def failureProd (v : V) (l : List U) : ℝ :=
  (l.map fun u => 1 - G.p u v).prod

lemma failureProd_nonneg (v : V) (l : List U) : 0 ≤ failureProd G v l := by
  induction l with
  | nil => simp [failureProd]
  | cons u l ih =>
    change 0 ≤ (1 - G.p u v) * failureProd G v l
    exact mul_nonneg (sub_nonneg.mpr (G.p_le_one u v)) ih

lemma failureProd_sublist (v : V) {a b : List U} (h : a.Sublist b) :
    failureProd G v b ≤ failureProd G v a := by
  induction h with
  | slnil => simp [failureProd]
  | @cons a b u h ih =>
    change (1 - G.p u v) * failureProd G v b ≤ failureProd G v a
    exact (mul_le_of_le_one_left (failureProd_nonneg G v b)
      (sub_le_self 1 (G.p_nonneg u v))).trans ih
  | @cons_cons a b u h ih =>
    change (1 - G.p u v) * failureProd G v b ≤
      (1 - G.p u v) * failureProd G v a
    exact mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (G.p_le_one u v))

noncomputable def prefixMass (v : V) (pre : List U) : ℝ :=
  G.surv v pre * failureProd G v pre

lemma prefixMass_nonneg (v : V) (pre : List U) : 0 ≤ prefixMass G v pre :=
  mul_nonneg (G.surv_nonneg v pre) (failureProd_nonneg G v pre)

lemma prefixMass_sublist (v : V) {a b : List U} (h : a.Sublist b) :
    prefixMass G v b ≤ prefixMass G v a := by
  exact mul_le_mul (G.surv_mono v b a h) (failureProd_sublist G v h)
    (failureProd_nonneg G v b) (G.surv_nonneg v a)

noncomputable def weightedFrom (v : V) (r : U → ℝ) : List U → List U → ℝ
  | _, [] => 0
  | pre, u :: l => prefixMass G v pre * G.p u v * r u +
      weightedFrom v r (pre ++ [u]) l

lemma weightedFrom_eq_sum (v : V) (r : U → ℝ) (pre l : List U) :
    weightedFrom G v r pre l =
      ∑ i : Fin l.length, prefixMass G v (pre ++ l.take i) *
        G.p (l.get i) v * r (l.get i) := by
  induction l generalizing pre with
  | nil => simp [weightedFrom]
  | cons u l ih =>
    simp only [List.length_cons]
    rw [weightedFrom, Fin.sum_univ_succ, ih]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro i hi
      simp [List.take_succ_cons, List.append_assoc]

lemma weightedFrom_eq_starValue (v : V) (l : List U) :
    weightedFrom G v G.w [] l = G.starValue v l := by
  rw [weightedFrom_eq_sum]
  simp [Instance.starValue, Instance.matchProb, Instance.reach, prefixMass, failureProd]

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks
namespace S01.P097
variable {U V : Type*} (G : Instance U V)

lemma matchProb_nonneg (v : V) (l : List U) (i : Fin l.length) :
    0 ≤ G.matchProb v l i := by
  change 0 ≤ prefixMass G v (l.take i) * G.p (l.get i) v
  exact mul_nonneg (prefixMass_nonneg G v _) (G.p_nonneg _ _)

lemma starValue_nonneg (v : V) (l : List U) : 0 ≤ G.starValue v l := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (matchProb_nonneg G v l i) (G.w_nonneg _)

lemma failureProd_append (v : V) (a b : List U) :
    failureProd G v (a ++ b) = failureProd G v a * failureProd G v b := by
  simp [failureProd, List.map_append, List.prod_append]

lemma prefixMass_le_failureProd (v : V) (pre : List U) :
    prefixMass G v pre ≤ failureProd G v pre := by
  exact mul_le_of_le_one_left (failureProd_nonneg G v pre) (G.surv_le_one v pre)

lemma weightedFrom_mass_bound (v : V) (pre l : List U) :
    weightedFrom G v (fun _ => 1) pre l ≤
      failureProd G v pre * (1 - failureProd G v l) := by
  induction l generalizing pre with
  | nil => simp [weightedFrom, failureProd]
  | cons u l ih =>
    calc
      weightedFrom G v (fun _ => 1) pre (u :: l) =
          prefixMass G v pre * G.p u v + weightedFrom G v (fun _ => 1) (pre ++ [u]) l := by
        simp [weightedFrom]
      _ ≤ failureProd G v pre * G.p u v +
          failureProd G v (pre ++ [u]) * (1 - failureProd G v l) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (prefixMass_le_failureProd G v pre) (G.p_nonneg u v))
          (ih _)
      _ = failureProd G v pre * (1 - failureProd G v (u :: l)) := by
        rw [failureProd_append]
        simp only [failureProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one]
        ring

lemma sum_matchProb_le_one (v : V) (l : List U) :
    (∑ i : Fin l.length, G.matchProb v l i) ≤ 1 := by
  have h := weightedFrom_mass_bound G v [] l
  rw [weightedFrom_eq_sum] at h
  have h' : (∑ i : Fin l.length, G.matchProb v l i) ≤ 1 - failureProd G v l := by
    simpa [Instance.matchProb, Instance.reach, prefixMass, failureProd] using h
  exact h'.trans (sub_le_self 1 (failureProd_nonneg G v l))

/-- Removing unavailable entries increases every retained weighted contribution. -/
lemma weightedFrom_filter_le [DecidableEq U] (v : V) (r : U → ℝ)
    (hr : ∀ u, 0 ≤ r u) (A : Finset U) (pre pre' l : List U)
    (hpre : pre'.Sublist pre) :
    weightedFrom G v (fun u => if u ∈ A then r u else 0) pre l ≤
      weightedFrom G v r pre' (l.filter fun u => decide (u ∈ A)) := by
  induction l generalizing pre pre' with
  | nil => simp [weightedFrom]
  | cons u l ih =>
    by_cases hu : u ∈ A
    · have hterm : prefixMass G v pre * G.p u v * r u ≤
          prefixMass G v pre' * G.p u v * r u :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (prefixMass_sublist G v hpre) (G.p_nonneg u v)) (hr u)
      have htail := ih (pre ++ [u]) (pre' ++ [u]) (hpre.append_right [u])
      simpa [List.filter_cons, weightedFrom, hu] using add_le_add hterm htail
    · have htail := ih (pre ++ [u]) pre'
        (hpre.trans (List.sublist_append_left pre [u]))
      simpa [List.filter_cons, weightedFrom, hu] using htail

lemma restricted_star_le_filter [DecidableEq U] (v : V) (A : Finset U) (l : List U) :
    (∑ i : Fin l.length, G.matchProb v l i *
      (if l.get i ∈ A then G.w (l.get i) else 0)) ≤
      G.starValue v (l.filter fun u => decide (u ∈ A)) := by
  have h := weightedFrom_filter_le G v G.w G.w_nonneg A [] [] l (List.Sublist.refl [])
  rw [weightedFrom_eq_sum, weightedFrom_eq_starValue] at h
  simpa [Instance.matchProb, Instance.reach, prefixMass, failureProd] using h

lemma starValue_le_starOpt [DecidableEq U] [Fintype U] (v : V) (A : Finset U)
    (l : List U) (hl : l.Nodup) (hA : ∀ u ∈ l, u ∈ A) :
    G.starValue v l ≤ G.starOpt A v := by
  classical
  unfold Instance.starOpt
  exact le_ciSup
    (Finite.bddAbove_range (fun z : {l : Policy U // ∀ u ∈ l.1, u ∈ A} =>
      G.starValue v z.1.1))
    (⟨⟨l, hl⟩, hA⟩ : {l : Policy U // ∀ u ∈ l.1, u ∈ A})

lemma starOpt_nonneg [DecidableEq U] [Fintype U] (A : Finset U) (v : V) :
    0 ≤ G.starOpt A v := by
  simpa [Instance.starValue] using
    starValue_le_starOpt G v A [] List.nodup_nil (by simp)

lemma restricted_star_le_starOpt [DecidableEq U] [Fintype U]
    (v : V) (A : Finset U) (l : List U) (hl : l.Nodup) :
    (∑ i : Fin l.length, G.matchProb v l i *
      (if l.get i ∈ A then G.w (l.get i) else 0)) ≤ G.starOpt A v := by
  refine (restricted_star_le_filter G v A l).trans
    (starValue_le_starOpt G v A _ (hl.filter _) ?_)
  intro u hu
  exact of_decide_eq_true (List.mem_filter.mp hu).2

lemma pmf_sum_toReal {X : Type*} [Fintype X] (p : PMF X) :
    (∑ x : X, (p x).toReal) = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)] at h'
  simpa using h'

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks

namespace S01.P097

lemma pmf_weight_nonneg {X : Type*} (p : PMF X) (x : X) : 0 ≤ (p x).toReal :=
  ENNReal.toReal_nonneg

lemma pmf_average_const {X : Type*} [Fintype X] (p : PMF X) (c : ℝ) :
    (∑ x : X, (p x).toReal * c) = c := by
  rw [← Finset.sum_mul, pmf_sum_toReal, one_mul]

lemma pmf_average_nonneg {X : Type*} [Fintype X] (p : PMF X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∑ x : X, (p x).toReal * f x := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (pmf_weight_nonneg p x) (hf x)

/-- A per-policy bound is needed only where the black box assigns positive mass. -/
lemma pmf_average_le_of_support {X : Type*} [Fintype X] (p : PMF X)
    (f : X → ℝ) (c : ℝ) (hf : ∀ x, p x ≠ 0 → f x ≤ c) :
    (∑ x : X, (p x).toReal * f x) ≤ c := by
  rw [← pmf_average_const p c]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (hf x hx) (pmf_weight_nonneg p x)

lemma le_pmf_average_of_support {X : Type*} [Fintype X] (p : PMF X)
    (f : X → ℝ) (c : ℝ) (hf : ∀ x, p x ≠ 0 → c ≤ f x) :
    c ≤ ∑ x : X, (p x).toReal * f x := by
  rw [← pmf_average_const p c]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (hf x hx) (pmf_weight_nonneg p x)

variable {U V : Type*} [DecidableEq U] (G : Instance U V)

lemma step_nonneg (v : V) (l : List U) (f : Finset U → ℝ) (A : Finset U)
    (hf : ∀ B, 0 ≤ f B) : 0 ≤ G.step v l f A := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (matchProb_nonneg G v l i) (add_nonneg (G.w_nonneg _) (hf _))
  · exact mul_nonneg (sub_nonneg.mpr (sum_matchProb_le_one G v l)) (hf A)

lemma step_mono (v : V) (l : List U) (f g : Finset U → ℝ) (A : Finset U)
    (hfg : ∀ B, f B ≤ g B) : G.step v l f A ≤ G.step v l g A := by
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hfg _))
      (matchProb_nonneg G v l i)
  · exact mul_le_mul_of_nonneg_left (hfg A)
      (sub_nonneg.mpr (sum_matchProb_le_one G v l))

lemma step_const (v : V) (l : List U) (A : Finset U) (c : ℝ) :
    G.step v l (fun _ => c) A = G.starValue v l + c := by
  simp only [Instance.step, Instance.starValue, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  ring

lemma algFrom_nonneg [Fintype U] (BB : Finset U → V → PMF (Policy U))
    (vs : List V) (A : Finset U) : 0 ≤ G.algFrom BB vs A := by
  induction vs generalizing A with
  | nil => simp [Instance.algFrom]
  | cons v vs ih =>
    exact pmf_average_nonneg (BB A v) _ fun l =>
      step_nonneg G v l.1 (G.algFrom BB vs) A ih

lemma ALG_nonneg [Fintype U] (BB : Finset U → V → PMF (Policy U))
    (order : List V) : 0 ≤ G.ALG BB order :=
  algFrom_nonneg G BB order Finset.univ

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks

namespace S01.P097

variable {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V)

/-- One online step pays for the possible loss of the remaining-customer potential. -/
theorem potential_step_bound (q : U → V → ℝ)
    (hq : ∀ u v, 0 ≤ q u v) (hrow : ∀ u, (∑ v : V, q u v) ≤ 1)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (A : Finset U) (R : Finset V) (v : V) (l : List U) (f : Finset U → ℝ)
    (hnext : ∀ B, κ * potential G q B R ≤ 2 * f B) :
    κ * potential G q A R + G.starValue v l ≤ 2 * G.step v l f A := by
  have hbasic (u : U) : κ * potential G q A R ≤ G.w u + 2 * f (A.erase u) := by
    calc
      κ * potential G q A R ≤ κ * (G.w u + potential G q (A.erase u) R) :=
        mul_le_mul_of_nonneg_left (potential_erase_le G q hq hrow A R u) hκ0
      _ = κ * G.w u + κ * potential G q (A.erase u) R := mul_add _ _ _
      _ ≤ κ * G.w u + 2 * f (A.erase u) := by linarith [hnext (A.erase u)]
      _ ≤ G.w u + 2 * f (A.erase u) :=
        by linarith [mul_le_of_le_one_left (G.w_nonneg u) hκ1]
  have hterm (i : Fin l.length) :
      G.matchProb v l i * (κ * potential G q A R + G.w (l.get i)) ≤
        2 * (G.matchProb v l i * (G.w (l.get i) + f (A.erase (l.get i)))) := by
    have hi : κ * potential G q A R + G.w (l.get i) ≤
        2 * (G.w (l.get i) + f (A.erase (l.get i))) := by
      linarith [hbasic (l.get i)]
    calc
      _ ≤ G.matchProb v l i * (2 * (G.w (l.get i) + f (A.erase (l.get i)))) :=
        mul_le_mul_of_nonneg_left hi (matchProb_nonneg G v l i)
      _ = _ := by ring
  have hfail := mul_le_mul_of_nonneg_left (hnext A)
    (sub_nonneg.mpr (sum_matchProb_le_one G v l))
  calc
    κ * potential G q A R + G.starValue v l =
        (∑ i : Fin l.length, G.matchProb v l i *
          (κ * potential G q A R + G.w (l.get i))) +
        (1 - ∑ i : Fin l.length, G.matchProb v l i) * (κ * potential G q A R) := by
      simp only [Instance.starValue, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    _ ≤ (∑ i : Fin l.length, 2 *
          (G.matchProb v l i * (G.w (l.get i) + f (A.erase (l.get i))))) +
        (1 - ∑ i : Fin l.length, G.matchProb v l i) * (2 * f A) :=
      add_le_add (Finset.sum_le_sum (fun i _ => hterm i)) hfail
    _ = 2 * G.step v l f A := by
      rw [← Finset.mul_sum]
      unfold Instance.step
      ring

/-- The online recursion dominates every feasible match-contribution matrix. -/
theorem potential_algFrom_bound (q : U → V → ℝ)
    (hq : ∀ u v, 0 ≤ q u v) (hrow : ∀ u, (∑ v : V, q u v) ≤ 1)
    (hcol : ∀ (A : Finset U) (v : V), (∑ u ∈ A, q u v * G.w u) ≤ G.starOpt A v)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (BB : Finset U → V → PMF (Policy U)) (hBB : G.IsKappaApprox κ BB)
    (order : List V) (hnd : order.Nodup) (A : Finset U) :
    κ * potential G q A order.toFinset ≤ 2 * G.algFrom BB order A := by
  induction order generalizing A with
  | nil => simp [potential, Instance.algFrom]
  | cons v vs ih =>
    have hndvs : vs.Nodup := (List.nodup_cons.mp hnd).2
    have hv : v ∉ vs.toFinset := by
      simpa only [List.mem_toFinset] using (List.nodup_cons.mp hnd).1
    have hstep (l : Policy U) :
        κ * potential G q A vs.toFinset + G.starValue v l.1 ≤
          2 * G.step v l.1 (G.algFrom BB vs) A :=
      potential_step_bound G q hq hrow κ hκ0 hκ1 A vs.toFinset v l.1 _
        (fun B => ih hndvs B)
    have hmix : κ * potential G q A vs.toFinset +
        (∑ l : Policy U, (BB A v l).toReal * G.starValue v l.1) ≤
          2 * G.algFrom BB (v :: vs) A := by
      calc
        _ = ∑ l : Policy U, (BB A v l).toReal *
            (κ * potential G q A vs.toFinset + G.starValue v l.1) := by
          simp only [mul_add, Finset.sum_add_distrib, pmf_average_const]
        _ ≤ ∑ l : Policy U, (BB A v l).toReal *
            (2 * G.step v l.1 (G.algFrom BB vs) A) :=
          Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hstep l) ENNReal.toReal_nonneg
        _ = 2 * G.algFrom BB (v :: vs) A := by
          simp only [Instance.algFrom, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
    have hcurrent : κ * (∑ u ∈ A, q u v * G.w u) ≤
        ∑ l : Policy U, (BB A v l).toReal * G.starValue v l.1 :=
      (mul_le_mul_of_nonneg_left (hcol A v) hκ0).trans (hBB.2 A v)
    rw [List.toFinset_cons, potential_insert G q A vs.toFinset v hv]
    nlinarith [hmix, hcurrent]

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks
namespace S01.P097

variable {U V : Type*}

/-- The exact adaptive strategy recurrence with a reward attached to each match. -/
def taggedValue (G : Instance U V) (r : U → V → ℝ) : Strategy U V → ℝ
  | .done => 0
  | .visit v l g h =>
      ∑ i : Fin l.length, G.matchProb v l i * (r (l.get i) v + taggedValue G r (g (l.get i))) +
        (1 - ∑ i : Fin l.length, G.matchProb v l i) * taggedValue G r h

lemma taggedValue_zero (G : Instance U V) (T : Strategy U V) :
    taggedValue G (fun _ _ => 0) T = 0 := by
  induction T with
  | done => rfl
  | visit v l g h ihg ihh => simp [taggedValue, ihg, ihh]

lemma taggedValue_add (G : Instance U V) (r s : U → V → ℝ) (T : Strategy U V) :
    taggedValue G (fun u v => r u v + s u v) T =
      taggedValue G r T + taggedValue G s T := by
  induction T with
  | done => simp [taggedValue]
  | visit v l g h ihg ihh =>
    simp only [taggedValue, ihg, ihh]
    rw [mul_add, ← add_add_add_comm]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

lemma taggedValue_mul (G : Instance U V) (c : ℝ) (r : U → V → ℝ) (T : Strategy U V) :
    taggedValue G (fun u v => c * r u v) T = c * taggedValue G r T := by
  induction T with
  | done => simp [taggedValue]
  | visit v l g h ihg ihh =>
    simp only [taggedValue, ihg, ihh]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      ring
    · ring

lemma taggedValue_sum {I : Type*} (G : Instance U V) (s : Finset I)
    (r : I → U → V → ℝ) (T : Strategy U V) :
    taggedValue G (fun u v => ∑ a ∈ s, r a u v) T = ∑ a ∈ s, taggedValue G (r a) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [taggedValue_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [taggedValue_add, ih]

lemma taggedValue_weight (G : Instance U V) (T : Strategy U V) :
    taggedValue G (fun u _ => G.w u) T = G.value T := by
  induction T with
  | done => rfl
  | visit v l g h ihg ihh => simp only [taggedValue, Instance.value, ihg, ihh]

lemma taggedValue_eq_zero_of_valid [DecidableEq U] [DecidableEq V]
    (G : Instance U V) (r : U → V → ℝ) (T : Strategy U V)
    (A : Finset U) (R : Finset V) (hT : T.ValidFrom A R)
    (hr : ∀ u ∈ A, ∀ v ∈ R, r u v = 0) : taggedValue G r T = 0 := by
  induction T generalizing A R with
  | done => rfl
  | visit v l g h ihg ihh =>
    rcases hT with ⟨hv, hnd, hl, hg, hh⟩
    have hg0 (i : Fin l.length) : taggedValue G r (g (l.get i)) = 0 := by
      apply ihg (l.get i) (A.erase (l.get i)) (R.erase v) (hg _ (List.get_mem _ _))
      intro u hu v' hv'
      exact hr u (Finset.mem_of_mem_erase hu) v' (Finset.mem_of_mem_erase hv')
    have hh0 : taggedValue G r h = 0 := by
      apply ihh A (R.erase v) hh
      intro u hu v' hv'
      exact hr u hu v' (Finset.mem_of_mem_erase hv')
    simp only [taggedValue, hg0, hh0, mul_zero, add_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hr (l.get i) (hl _ (List.get_mem _ _)) v hv, mul_zero]

/-- Successful matching mass on one particular edge in the adaptive tree. -/
noncomputable def matchMass [DecidableEq U] [DecidableEq V]
    (G : Instance U V) (T : Strategy U V) (u : U) (v : V) : ℝ :=
  taggedValue G (fun u' v' => if u' = u ∧ v' = v then 1 else 0) T

lemma taggedValue_decomposition [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (r : U → V → ℝ) (T : Strategy U V) :
    taggedValue G r T = ∑ u : U, ∑ v : V, r u v * matchMass G T u v := by
  classical
  have he : r = fun u' v' => ∑ u : U, ∑ v : V,
      r u v * (if u' = u ∧ v' = v then 1 else 0) := by
    funext u' v'
    simp [ite_and, eq_comm]
  conv_lhs => rw [he]
  rw [taggedValue_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [taggedValue_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact taggedValue_mul G (r u v) _ T

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks
namespace S01.P097
variable {U V : Type*}

lemma weighted_step_le {I : Type*} [Fintype I] (q b : I → ℝ) (c d : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i ≤ 1)
    (hb : ∀ i, b i ≤ c) (hd : d ≤ c) :
    (∑ i, q i * b i) + (1 - ∑ i, q i) * d ≤ c := by
  calc
    _ ≤ (∑ i, q i * c) + (1 - ∑ i, q i) * c :=
      add_le_add (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hq i))
        (mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hm))
    _ = c := by rw [← Finset.sum_mul]; ring

section Probabilities
variable (G : Instance U V)
variable (hprob : ∀ (v : V) (l : List U) (i : Fin l.length), 0 ≤ G.matchProb v l i)
variable (hmass : ∀ (v : V) (l : List U), ∑ i : Fin l.length, G.matchProb v l i ≤ 1)
include hprob hmass

lemma taggedValue_nonneg_of (r : U → V → ℝ) (hr : ∀ u v, 0 ≤ r u v)
    (T : Strategy U V) : 0 ≤ taggedValue G r T := by
  induction T with
  | done => rfl
  | visit v l g h ihg ihh =>
    exact add_nonneg
      (Finset.sum_nonneg fun i _ => mul_nonneg (hprob v l i) (add_nonneg (hr _ _) (ihg _)))
      (mul_nonneg (sub_nonneg.mpr (hmass v l)) ihh)

lemma taggedValue_one_item_le [DecidableEq U] [DecidableEq V]
    (T : Strategy U V) (A : Finset U) (R : Finset V) (hT : T.ValidFrom A R) (u : U) :
    taggedValue G (fun u' _ => if u' = u then 1 else 0) T ≤ 1 := by
  induction T generalizing A R with
  | done => norm_num [taggedValue]
  | visit v l g h ihg ihh =>
    rcases hT with ⟨hv, hnd, hl, hg, hh⟩
    apply weighted_step_le (fun i : Fin l.length => G.matchProb v l i)
      (fun i => (if l.get i = u then 1 else 0) +
        taggedValue G (fun u' _ => if u' = u then 1 else 0) (g (l.get i))) 1
      (taggedValue G (fun u' _ => if u' = u then 1 else 0) h)
      (hprob v l) (hmass v l)
    · intro i
      by_cases he : l.get i = u
      · have hz : taggedValue G (fun u' _ => if u' = u then 1 else 0) (g (l.get i)) = 0 := by
          apply taggedValue_eq_zero_of_valid G _ _ (A.erase (l.get i)) (R.erase v)
            (hg _ (List.get_mem _ _))
          intro u' hu v' hv'
          have hne : u' ≠ u := fun heu => (Finset.mem_erase.mp hu).1 (heu.trans he.symm)
          simp [hne]
        rw [if_pos he, hz]
        norm_num
      · simp only [he, ite_false, zero_add]
        exact ihg _ (A.erase (l.get i)) (R.erase v) (hg _ (List.get_mem _ _))
    · exact ihh A (R.erase v) hh

lemma taggedValue_customer_subset_le [DecidableEq U] [DecidableEq V]
    (C : Finset U → V → ℝ) (hC : ∀ A v, 0 ≤ C A v)
    (hlocal : ∀ (v : V) (l : List U) (A : Finset U), l.Nodup →
      (∑ i : Fin l.length, G.matchProb v l i *
        (if l.get i ∈ A then G.w (l.get i) else 0)) ≤ C A v)
    (T : Strategy U V) (A₀ : Finset U) (R : Finset V) (hT : T.ValidFrom A₀ R)
    (A : Finset U) (v : V) :
    taggedValue G (fun u' v' => if v' = v ∧ u' ∈ A then G.w u' else 0) T ≤ C A v := by
  induction T generalizing A₀ R with
  | done => exact hC A v
  | visit v' l g h ihg ihh =>
    rcases hT with ⟨hv', hnd, hl, hg, hh⟩
    by_cases he : v' = v
    · have hg0 (i : Fin l.length) :
          taggedValue G (fun u' v' => if v' = v ∧ u' ∈ A then G.w u' else 0) (g (l.get i)) = 0 := by
        apply taggedValue_eq_zero_of_valid G _ _ (A₀.erase (l.get i)) (R.erase v')
          (hg _ (List.get_mem _ _))
        intro u' hu v'' hv''
        have hne : v'' ≠ v := by simpa [he] using (Finset.mem_erase.mp hv'').1
        simp [hne]
      have hh0 : taggedValue G (fun u' v' => if v' = v ∧ u' ∈ A then G.w u' else 0) h = 0 := by
        apply taggedValue_eq_zero_of_valid G _ _ A₀ (R.erase v') hh
        intro u' hu v'' hv''
        have hne : v'' ≠ v := by simpa [he] using (Finset.mem_erase.mp hv'').1
        simp [hne]
      simp only [taggedValue, hg0, hh0, add_zero, mul_zero]
      simpa [he] using hlocal v' l A hnd
    · simp only [taggedValue, he, false_and, ite_false, zero_add]
      apply weighted_step_le _ _ _ _ (hprob v' l) (hmass v' l)
      · intro i
        exact ihg _ (A₀.erase (l.get i)) (R.erase v') (hg _ (List.get_mem _ _))
      · exact ihh A₀ (R.erase v') hh

end Probabilities
end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks
namespace S01.P097
variable {U V : Type*}

lemma matchMass_nonneg [DecidableEq U] [DecidableEq V]
    (G : Instance U V) (T : Strategy U V) (u : U) (v : V) :
    0 ≤ matchMass G T u v := by
  apply taggedValue_nonneg_of G (matchProb_nonneg G) (sum_matchProb_le_one G)
  intro u' v'
  split_ifs <;> norm_num

lemma matchMass_item_capacity [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (T : Strategy U V) (A : Finset U) (R : Finset V)
    (hT : T.ValidFrom A R) (u : U) :
    ∑ v : V, matchMass G T u v ≤ 1 := by
  have hb := taggedValue_one_item_le G (matchProb_nonneg G) (sum_matchProb_le_one G) T A R hT u
  rw [taggedValue_decomposition] at hb
  simpa [ite_mul] using hb

lemma matchMass_customer_bound [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (T : Strategy U V) (A₀ : Finset U) (R : Finset V)
    (hT : T.ValidFrom A₀ R) (A : Finset U) (v : V) :
    ∑ u ∈ A, matchMass G T u v * G.w u ≤ G.starOpt A v := by
  have hb := taggedValue_customer_subset_le G (matchProb_nonneg G) (sum_matchProb_le_one G)
    G.starOpt (starOpt_nonneg G)
    (fun v l A hl => restricted_star_le_starOpt G v A l hl) T A₀ R hT A v
  rw [taggedValue_decomposition] at hb
  simpa [ite_and, ite_mul, Finset.sum_ite_irrel, mul_comm] using hb

lemma value_eq_matchMass [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (T : Strategy U V) :
    G.value T = ∑ u : U, ∑ v : V, matchMass G T u v * G.w u := by
  rw [← taggedValue_weight, taggedValue_decomposition]
  simp only [mul_comm]


end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks

namespace S01.P097

/-- Pass the charging inequality for every valid adaptive strategy to the exact
offline supremum. The zero-approximation boundary needs no division. -/
theorem competitive_of_tree_bound {U V : Type*}
    [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (κ : ℝ) (hκ0 : 0 ≤ κ)
    (BB : Finset U → V → PMF (Policy U)) (order : List V)
    (hbound : ∀ T : Strategy U V, T.ValidFrom Finset.univ Finset.univ →
      κ * G.value T ≤ 2 * G.ALG BB order) :
    0.5 * κ * G.OPT ≤ G.ALG BB order := by
  by_cases hk : κ = 0
  · simpa only [hk, mul_zero, zero_mul] using ALG_nonneg G BB order
  · have hpos : 0 < κ := lt_of_le_of_ne hκ0 (Ne.symm hk)
    letI : Nonempty {T : Strategy U V // T.ValidFrom Finset.univ Finset.univ} :=
      ⟨⟨.done, trivial⟩⟩
    have hopt : G.OPT ≤ (2 * G.ALG BB order) / κ := by
      apply ciSup_le
      intro T
      apply (le_div_iff₀ hpos).mpr
      simpa only [mul_comm] using hbound T.1 T.2
    have h := (le_div_iff₀ hpos).mp hopt
    nlinarith

end S01.P097

open scoped BigOperators
open OnlineMatchFrameworks

/-- The original competitive guarantee against every adaptive sequential
offline strategy, followed by the exact supremum benchmark. -/
theorem solution {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (BB : Finset U → V → PMF (Policy U)) (hBB : G.IsKappaApprox κ BB)
    (order : List V) (hnd : order.Nodup) (hall : ∀ v, v ∈ order) :
    0.5 * κ * G.OPT ≤ G.ALG BB order := by
  apply S01.P097.competitive_of_tree_bound G κ hκ0 BB order
  intro T hT
  have horder : order.toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hall v
  have hcharge := S01.P097.potential_algFrom_bound G (S01.P097.matchMass G T)
    (S01.P097.matchMass_nonneg G T)
    (fun u => S01.P097.matchMass_item_capacity G T Finset.univ Finset.univ hT u)
    (fun A v => S01.P097.matchMass_customer_bound G T Finset.univ Finset.univ hT A v)
    κ hκ0 hκ1 BB hBB order hnd Finset.univ
  rw [horder, S01.P097.potential_univ_eq, ← S01.P097.value_eq_matchMass G T] at hcharge
  simpa only [Instance.ALG] using hcharge

#print axioms solution
