-- Prove2me | solution 1 for TimeSpaceMA.polylogConstantLossExtractor
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T20:36:06.075406+00:00
-- url     : https://prove2.me/submissions/da7faf2f-2ade-469f-9f73-84e03a2592bf

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_TimeSpaceMA_RRVNearFull
import Definitions.Def_TimeSpaceMA_TUZExtractorComponents
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_TimeSpaceMA_RRV_nearFullStrongExtractor
import Theorems.Thm_TimeSpaceMA_shortLosslessCondenser

open scoped BigOperators

namespace TimeSpaceMA.RRV

/-- Probability carried by a finite event. -/
def eventMass {X : Type} (p : X → ℝ) (U : Finset X) : ℝ := ∑ x ∈ U, p x

/-- One-sided event bound. With normalized masses the reverse bound follows by complement. -/
def EventClose {X : Type} (p q : X → ℝ) (ε : ℝ) : Prop :=
  ∀ U : Finset X, eventMass p U - eventMass q U ≤ ε

private theorem EventClose.reverse {X : Type} [Fintype X] (p q : X → ℝ) {ε : ℝ}
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (h : EventClose p q ε) :
    EventClose q p ε := by
  classical
  intro U
  have hU := h (Finset.univ \ U)
  have hs (r : X → ℝ) : eventMass r (Finset.univ \ U) + eventMass r U = ∑ x, r x := by
    exact Finset.sum_sdiff (Finset.subset_univ U)
  have hsp := hs p
  have hsq := hs q
  linarith

/-- If `p` is event-close to `q`, then the mass of outcomes under `p` that fall below
half their reference mass is at most the error. This is the `s=1` case of RRV Claim 31. -/
theorem lightMass_le {X : Type} [Fintype X] (p q : X → ℝ) {ε : ℝ}
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (h : EventClose p q ε) :
    eventMass p (Finset.univ.filter fun x => 2*p x < q x) ≤ ε := by
  classical
  let L := Finset.univ.filter fun x => 2*p x < q x
  have hm : 2 * eventMass p L ≤ eventMass q L := by
    rw [eventMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun x hx => ((Finset.mem_filter.mp hx).2 : 2*p x < q x).le
  have hU := h.reverse p q hp hq L
  linarith

/-- Event-level conditional composition. On good outer outcomes the conditional kernel
is event-close to a common reference distribution. On the exceptional outcomes its
entire mass is charged. -/
theorem conditionalClose {X Y : Type} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (k : X → Y → ℝ) (r : Y → ℝ) (bad : Finset X)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x y, 0 ≤ k x y) (hK : ∀ x, ∑ y, k x y = 1)
    (hr : ∀ y, 0 ≤ r y) (hR : ∑ y, r y = 1)
    {ε δ η : ℝ} (hε : EventClose p q ε) (hP : ∑ x, p x = 1)
    (hbad : eventMass p bad ≤ η) (hδ : 0 ≤ δ)
    (hgood : ∀ x, x ∉ bad → EventClose (k x) r δ) :
    EventClose (fun z : X × Y => p z.1 * k z.1 z.2)
      (fun z : X × Y => q z.1 * r z.2) (ε+δ+η) := by
  classical
  intro U
  let fiber (x : X) := Finset.univ.filter fun y => (x,y) ∈ U
  have hf {f : X → ℝ} {g : X → Y → ℝ} :
      eventMass (fun z : X × Y => f z.1 * g z.1 z.2) U =
        ∑ x, f x * eventMass (g x) (fiber x) := by
    have hU : U = (Finset.univ : Finset (X × Y)).filter (· ∈ U) := by ext; simp
    unfold eventMass
    conv_lhs => rw [hU, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp_rw [fiber, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split <;> simp
  rw [hf (f := p) (g := k), hf (f := q) (g := fun _ => r)]
  have hhyb : (∑ x, p x * eventMass (k x) (fiber x)) -
      (∑ x, p x * eventMass r (fiber x)) ≤ δ+η := by
    rw [← Finset.sum_sub_distrib]
    have hterm (x : X) : p x * eventMass (k x) (fiber x) - p x * eventMass r (fiber x) ≤
        p x * δ + if x ∈ bad then p x else 0 := by
      by_cases hx : x ∈ bad
      · have hkx : eventMass (k x) (fiber x) ≤ 1 := by
          rw [← hK x]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hk x y)
        have hrx : 0 ≤ eventMass r (fiber x) := Finset.sum_nonneg (fun y _ => hr y)
        rw [if_pos hx, ← mul_sub]
        have hle : eventMass (k x) (fiber x) - eventMass r (fiber x) ≤ 1 := by linarith
        exact (mul_le_mul_of_nonneg_left hle (hp x)).trans (by nlinarith [mul_nonneg (hp x) hδ])
      · rw [if_neg hx, add_zero, ← mul_sub]
        exact mul_le_mul_of_nonneg_left (hgood x hx _ ) (hp x)
    calc
      _ ≤ ∑ x, (p x * δ + if x ∈ bad then p x else 0) := Finset.sum_le_sum (fun x _ => hterm x)
      _ = δ + eventMass p bad := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hP, one_mul, eventMass, ← Finset.sum_filter]
        simp
      _ ≤ _ := by linarith
  have hmarg : (∑ x, p x * eventMass r (fiber x)) -
      (∑ x, q x * eventMass r (fiber x)) ≤ ε := by
    rw [← Finset.sum_sub_distrib]
    have hs : ∀ (y : Y), eventMass p (Finset.univ.filter fun x => (x,y) ∈ U) -
        eventMass q (Finset.univ.filter fun x => (x,y) ∈ U) ≤ ε := fun y => hε _
    simp_rw [← sub_mul, eventMass, fiber, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hh (y : Y) : (∑ x, (p x - q x) * (if (x,y) ∈ U then r y else 0)) ≤ ε * r y := by
      simp only [eventMass, Finset.sum_filter, ← Finset.sum_sub_distrib] at hs
      have hu := mul_le_mul_of_nonneg_right (hs y) (hr y)
      rw [Finset.sum_mul] at hu
      apply le_trans _ hu
      refine le_of_eq (Finset.sum_congr rfl fun x _ => ?_)
      split <;> simp
    calc
      _ ≤ ∑ y, ε * r y := Finset.sum_le_sum (fun y _ => hh y)
      _ = ε := by rw [← Finset.mul_sum, hR, mul_one]
  linarith


section Weighted

variable {X S1 S2 O1 O2 : Type}
variable [Fintype X] [Fintype S1] [Fintype S2] [Fintype O1] [Fintype O2]
variable [DecidableEq S1] [DecidableEq S2] [DecidableEq O1] [DecidableEq O2]

/-- Distribution of the seed and output of a seeded map when its input has mass p. -/
noncomputable def strongMass (ext : X → S1 → O1) (p : X → ℝ) (a : S1 × O1) : ℝ :=
  (∑ x, if ext x a.1 = a.2 then p x else 0) / (Fintype.card S1 : ℝ)

omit [Fintype O1] [DecidableEq S1] in
theorem strongMass_nonnegative (ext : X → S1 → O1) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) :
    ∀ a, 0 ≤ strongMass ext p a := by
  intro a
  exact div_nonneg
    (Finset.sum_nonneg (fun x _ => by split; exact hp x; rfl))
    (Nat.cast_nonneg _)

omit [DecidableEq S1] in
theorem strongMass_total (ext : X → S1 → O1) {p : X → ℝ} (hp : ∑ x, p x = 1)
    (hs : 0 < Fintype.card S1) : ∑ a, strongMass ext p a = 1 := by
  classical
  unfold strongMass
  rw [← Finset.sum_div, ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset O1)), Finset.sum_ite_eq, Finset.mem_univ,
    if_true, hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs))

omit [Fintype O1] in
theorem strongMass_event (ext : X → S1 → O1) (p : X → ℝ) (event : Finset (S1 × O1)) :
    eventMass (strongMass ext p) event =
      weightedExtractionProbability (fun x s => (s, ext x s)) p event := by
  classical
  unfold eventMass strongMass weightedExtractionProbability
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  let T := (Finset.univ : Finset S1).filter (fun s => (s,ext x s) ∈ event)
  have hT : event.filter (fun a => ext x a.1 = a.2) =
      T.map (⟨fun s => (s,ext x s), fun _ _ h => congrArg Prod.fst h⟩ : S1 ↪ S1 × O1) := by
    ext a
    rcases a with ⟨s,o⟩ 
    simp only [Finset.mem_filter, Finset.mem_map, T, Finset.mem_univ, true_and]
    change (s,o) ∈ event ∧ ext x s = o ↔
      ∃ t, (t,ext x t) ∈ event ∧ (t,ext x t) = (s,o)
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨ha, he⟩
      exact ⟨s, by simpa [he] using ha, rfl, he⟩
    · rintro ⟨t, ht, rfl, he⟩
      exact ⟨by simpa [he] using ht, he⟩
  rw [← Finset.sum_filter, Finset.sum_const, hT, Finset.card_map, nsmul_eq_mul, mul_comm]

private theorem uniform_event {A : Type} [Fintype A] (U : Finset A) :
    eventMass (fun _ : A => 1 / (Fintype.card A : ℝ)) U = (U.card : ℝ) / Fintype.card A := by
  simp [eventMass, nsmul_eq_mul, div_eq_mul_inv]

private theorem uniform_total {A : Type} [Fintype A] (hA : 0 < Fintype.card A) :
    ∑ _ : A, 1 / (Fintype.card A : ℝ) = 1 := by
  change eventMass (fun _ : A => 1/(Fintype.card A : ℝ)) Finset.univ = 1
  rw [uniform_event, Finset.card_univ]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA))

theorem weightedStrong_iff (ext : X → S1 → O1) (p : X → ℝ) (ε : ℝ) :
    WeightedExtractorEvents (fun x s => (s, ext x s)) p ε ↔
      EventClose (strongMass ext p) (fun _ => 1/(Fintype.card (S1 × O1) : ℝ)) ε := by
  change (∀ U, weightedExtractionProbability _ _ U - _ ≤ ε) ↔
    (∀ U, eventMass (strongMass ext p) U - eventMass _ U ≤ ε)
  simp only [strongMass_event, uniform_event]

/-- The input posterior given a particular seed and first output. At zero-mass outer events
the posterior is defined by the original distribution. -/
noncomputable def posterior (ext : X → S1 → O1) (p : X → ℝ) (a : S1 × O1) (x : X) : ℝ :=
  let z := ∑ x, if ext x a.1 = a.2 then p x else 0
  if z = 0 then p x else if ext x a.1 = a.2 then p x / z else 0

omit [Fintype S1] [Fintype O1] [DecidableEq S1] in
theorem posterior_nonnegative (ext : X → S1 → O1) (a : S1 × O1) {p : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) : ∀ x, 0 ≤ posterior ext p a x := by
  intro x
  rw [posterior]
  split
  · exact hp x
  split
  · exact div_nonneg (hp x) (Finset.sum_nonneg (fun y _ => by split; exact hp y; rfl))
  · exact le_rfl

omit [Fintype S1] [Fintype O1] [DecidableEq S1] in
theorem posterior_total (ext : X → S1 → O1) (a : S1 × O1) {p : X → ℝ}
    (hp : ∑ x, p x = 1) : ∑ x, posterior ext p a x = 1 := by
  let z := ∑ x, if ext x a.1 = a.2 then p x else 0
  by_cases hz : z = 0
  · simpa [posterior, z, hz] using hp
  · change (∑ x, if z = 0 then p x else if ext x a.1 = a.2 then p x / z else 0) = 1
    simp only [if_neg hz]
    have he (x : X) : (if ext x a.1 = a.2 then p x / z else 0) =
        (if ext x a.1 = a.2 then p x else 0) / z := by split <;> simp
    simp_rw [he]
    rw [← Finset.sum_div]
    exact div_self hz

omit [DecidableEq S1] in
/-- RRV's entropy recovery step on an outer outcome whose mass is at least half uniform.
Each posterior point is at most 2 * |O1| times the original point bound. -/
theorem posterior_le (ext : X → S1 → O1) (a : S1 × O1) {p : X → ℝ}
    {u : ℝ} (hu : 0 ≤ u) (hpu : ∀ x, p x ≤ u)
    (hs : 0 < Fintype.card S1) (ho : 0 < Fintype.card O1)
    (ha : 1/(Fintype.card (S1 × O1) : ℝ) ≤ 2 * strongMass ext p a) :
    ∀ x, posterior ext p a x ≤ u * (2 * Fintype.card O1) := by
  intro x
  let z := ∑ x, if ext x a.1 = a.2 then p x else 0
  let d : ℝ := Fintype.card S1
  let o : ℝ := Fintype.card O1
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hs
  have ho' : 0 < o := by dsimp [o]; exact_mod_cast ho
  rw [Fintype.card_prod, Nat.cast_mul] at ha
  change 1/(d*o) ≤ 2 * (z/d) at ha
  have hlow : 1 ≤ z * (2*o) := by
    rw [← mul_div_assoc] at ha
    have hb : 1 / (o*d) ≤ (2*z)/d := by simpa [mul_comm d o] using ha
    rw [← div_div] at hb
    have hc := (div_le_div_iff_of_pos_right hd).mp hb
    have hc' := (div_le_iff₀ ho').mp hc
    linarith
  have hz : 0 < z := by
    by_contra! h
    have : z * (2*o) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  unfold posterior
  change (if z = 0 then p x else if ext x a.1 = a.2 then p x/z else 0) ≤ u*(2*o)
  rw [if_neg hz.ne']
  split
  · apply (div_le_iff₀ hz).mpr
    calc
      p x ≤ u := hpu x
      _ ≤ u * (z*(2*o)) := le_mul_of_one_le_right hu hlow
      _ = u*(2*o)*z := by ring
  · exact mul_nonneg hu (by positivity)

omit [Fintype O1] [DecidableEq S1] in
private theorem strongMass_mul_posterior (ext : X → S1 → O1) (a : S1 × O1) {p : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hs : 0 < Fintype.card S1) (x : X) :
    strongMass ext p a * posterior ext p a x =
      (if ext x a.1 = a.2 then p x else 0) / (Fintype.card S1 : ℝ) := by
  let z := ∑ x, if ext x a.1 = a.2 then p x else 0
  let d : ℝ := Fintype.card S1
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  change z/d * (if z = 0 then p x else if ext x a.1 = a.2 then p x/z else 0) =
    (if ext x a.1 = a.2 then p x else 0)/d
  by_cases hz : z = 0
  · have hterm : (if ext x a.1 = a.2 then p x else 0) = 0 := by
      have hle : (if ext x a.1 = a.2 then p x else 0) ≤ z :=
        Finset.single_le_sum (f := fun y => if ext y a.1 = a.2 then p y else 0)
          (fun y _ => by split; exact hp y; rfl) (Finset.mem_univ x)
      have hlo : 0 ≤ (if ext x a.1 = a.2 then p x else 0) := by split; exact hp x; rfl
      linarith
    simp [hz, hterm]
  · rw [if_neg hz]
    split <;> (field_simp <;> ring)

omit [Fintype O1] [Fintype O2] [DecidableEq S1] [DecidableEq S2] in
private theorem tuple_mass (f1 : X → S1 → O1) (f2 : X → S2 → O2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs1 : 0 < Fintype.card S1)
    (a : S1 × O1) (b : S2 × O2) :
    strongMass f1 p a * strongMass f2 (posterior f1 p a) b =
      (∑ x, if f1 x a.1 = a.2 ∧ f2 x b.1 = b.2 then p x else 0) /
        ((Fintype.card S1 : ℝ) * Fintype.card S2) := by
  change strongMass f1 p a *
      ((∑ x, if f2 x b.1 = b.2 then posterior f1 p a x else 0) / (Fintype.card S2 : ℝ)) = _
  rw [← mul_div_assoc, Finset.mul_sum, ← div_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f2 x b.1 = b.2
  · simpa [hx] using strongMass_mul_posterior f1 a hp hs1 x
  · simp [hx]

omit [Fintype O1] [Fintype O2] in
private theorem tuple_event (f1 : X → S1 → O1) (f2 : X → S2 → O2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs1 : 0 < Fintype.card S1)
    (U : Finset ((S1 × O1) × (S2 × O2))) :
    eventMass (fun ab : (S1 × O1) × (S2 × O2) =>
        strongMass f1 p ab.1 * strongMass f2 (posterior f1 p ab.1) ab.2) U =
      weightedExtractionProbability
        (fun (x : X) (s : S1 × S2) => ((s.1, f1 x s.1), (s.2, f2 x s.2))) p U := by
  classical
  unfold eventMass weightedExtractionProbability
  simp_rw [tuple_mass f1 f2 p hp hs1]
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm, Fintype.card_prod, Nat.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  let T := (Finset.univ : Finset (S1 × S2)).filter
    (fun s => ((s.1,f1 x s.1),(s.2,f2 x s.2)) ∈ U)
  have hT : U.filter (fun ab : (S1 × O1) × (S2 × O2) =>
        f1 x ab.1.1 = ab.1.2 ∧ f2 x ab.2.1 = ab.2.2) =
      T.map (⟨fun s => ((s.1,f1 x s.1), (s.2,f2 x s.2)),
        fun _ _ h => congrArg (fun ab : (S1 × O1) × (S2 × O2) => (ab.1.1,ab.2.1)) h⟩ :
        (S1 × S2) ↪ (S1 × O1) × (S2 × O2)) := by
    ext ab
    rcases ab with ⟨⟨s1,o1⟩,⟨s2,o2⟩⟩
    simp only [Finset.mem_filter, Finset.mem_map, T, Finset.mem_univ, true_and]
    change ((s1,o1),(s2,o2)) ∈ U ∧ (f1 x s1 = o1 ∧ f2 x s2 = o2) ↔
      ∃ t : S1 × S2, ((t.1,f1 x t.1),(t.2,f2 x t.2)) ∈ U ∧
        ((t.1,f1 x t.1),(t.2,f2 x t.2)) = ((s1,o1),(s2,o2))
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hm, h1, h2⟩
      exact ⟨(s1,s2), by simpa [h1,h2] using hm, ⟨rfl,h1⟩, ⟨rfl,h2⟩⟩
    · rintro ⟨⟨t1,t2⟩, ht, ⟨rfl,h1⟩, ⟨rfl,h2⟩⟩
      exact ⟨by simpa [h1,h2] using ht, h1, h2⟩
  rw [← Finset.sum_filter, Finset.sum_const, hT, Finset.card_map, nsmul_eq_mul, mul_comm]

/-- The entropy-recovery composition from RRV Lemma 27, in finite weighted event form.
A fresh seed is used for the second map. The returned value retains both seeds, so this
is the strong-extractor guarantee for the pair of output blocks. -/
theorem compose_strong_event (f1 : X → S1 → O1) (f2 : X → S2 → O2)
    {p : X → ℝ} {u ε δ : ℝ} (hp : ∀ x, 0 ≤ p x) (hP : ∑ x, p x = 1)
    (hu : 0 ≤ u) (hpu : ∀ x, p x ≤ u) (hδ : 0 ≤ δ)
    (hs1 : 0 < Fintype.card S1) (hs2 : 0 < Fintype.card S2)
    (ho1 : 0 < Fintype.card O1) (ho2 : 0 < Fintype.card O2)
    (hf1 : WeightedExtractorEvents (fun x s => (s, f1 x s)) p ε)
    (hf2 : ∀ q : X → ℝ, (∑ x, q x = 1) →
      (∀ x, 0 ≤ q x ∧ q x ≤ u * (2 * Fintype.card O1)) →
      WeightedExtractorEvents (fun x s => (s, f2 x s)) q δ) :
    WeightedExtractorEvents
      (fun (x : X) (s : S1 × S2) => ((s.1, f1 x s.1), (s.2, f2 x s.2))) p (2*ε+δ) := by
  classical
  let q1 : S1 × O1 → ℝ := fun _ => 1/(Fintype.card (S1 × O1) : ℝ)
  let q2 : S2 × O2 → ℝ := fun _ => 1/(Fintype.card (S2 × O2) : ℝ)
  let p1 := strongMass f1 p
  let kernel a := strongMass f2 (posterior f1 p a)
  let bad := Finset.univ.filter fun a => 2 * p1 a < q1 a
  have hQ1 : ∑ a, q1 a = 1 := uniform_total (by rw [Fintype.card_prod]; exact Nat.mul_pos hs1 ho1)
  have hQ2 : ∑ b, q2 b = 1 := uniform_total (by rw [Fintype.card_prod]; exact Nat.mul_pos hs2 ho2)
  have hP1 : ∑ a, p1 a = 1 := strongMass_total f1 hP hs1
  have hε : EventClose p1 q1 ε := (weightedStrong_iff f1 p ε).mp hf1
  have hbad : eventMass p1 bad ≤ ε := lightMass_le p1 q1 hP1 hQ1 hε
  have hk a b : 0 ≤ kernel a b := strongMass_nonnegative f2 (posterior_nonnegative f1 a hp) b
  have hK a : ∑ b, kernel a b = 1 := strongMass_total f2 (posterior_total f1 a hP) hs2
  have hgood (a : S1 × O1) (ha : a ∉ bad) : EventClose (kernel a) q2 δ := by
    have hb : q1 a ≤ 2 * p1 a := le_of_not_gt (by simpa [bad] using ha)
    apply (weightedStrong_iff f2 (posterior f1 p a) δ).mp
    apply hf2 _ (posterior_total f1 a hP)
    exact fun x => ⟨posterior_nonnegative f1 a hp x, posterior_le f1 a hu hpu hs1 ho1 hb x⟩
  have hstat := conditionalClose p1 q1 kernel q2 bad (strongMass_nonnegative f1 hp)
    hk hK (fun _ => by dsimp [q2]; positivity) hQ2 hε hP1 hbad hδ hgood
  intro U
  have hproduct : (fun ab : (S1 × O1) × (S2 × O2) => q1 ab.1 * q2 ab.2) =
      fun _ => 1/(Fintype.card ((S1 × O1) × (S2 × O2)) : ℝ) := by
    funext ab
    unfold q1 q2
    rw [Fintype.card_prod (α := S1 × O1) (β := S2 × O2), Nat.cast_mul,
      div_mul_div_comm, one_mul]
  have hU := hstat U
  rw [hproduct, uniform_event, tuple_event f1 f2 p hp hs1] at hU
  exact hU.trans (by ring_nf; rfl)

end Weighted

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

/-- Decode a padded seed into the original seed and independently appended seed. -/
def paddedSeedEquiv (t extra : ℕ) : Fin (2^(t+extra)) ≃ Fin (2^t) × Fin (2^extra) :=
  (finCongr (pow_add 2 t extra)).trans finProdFinEquiv.symm

/-- Encode the original output and the independently appended seed back into one label. -/
def paddedOutputEquiv (m extra : ℕ) : Fin (2^m) × Fin (2^extra) ≃ Fin (2^(m+extra)) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 m extra).symm)

end TimeSpaceMA.RRV


open scoped BigOperators

namespace TimeSpaceMA.RRV

/-- Relabel an extractor's source of uniform randomness and its output without changing
any weighted event bound. -/
theorem equiv_weighted_event {X S S' O O' : Type}
    [Fintype X] [Fintype S] [Fintype S'] [Fintype O] [Fintype O']
    [DecidableEq O] [DecidableEq O']
    (f : X → S → O) (p : X → ℝ) (ε : ℝ) (es : S' ≃ S) (eo : O ≃ O')
    (h : WeightedExtractorEvents f p ε) :
    WeightedExtractorEvents (fun x s => eo (f x (es s))) p ε := by
  classical
  intro U
  let V := U.map eo.symm.toEmbedding
  have hV y : y ∈ V ↔ eo y ∈ U := by
    constructor
    · intro hy
      obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hy
      change eo.symm z = y at he
      simpa [← he] using hz
    · intro hy
      exact Finset.mem_map.mpr ⟨_,hy,eo.symm_apply_apply y⟩
  have heq : weightedExtractionProbability (fun x s => eo (f x (es s))) p U =
      weightedExtractionProbability f p V := by
    unfold weightedExtractionProbability
    rw [Fintype.card_congr es]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hfilter : ((Finset.univ : Finset S').filter (fun s => eo (f x (es s)) ∈ U)).map
          es.toEmbedding = (Finset.univ : Finset S).filter (fun s => f x s ∈ V) := by
      ext s
      constructor
      · intro hs
        obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hs
        change es t = s at he
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, (hV _).mpr (by simpa [← he] using (Finset.mem_filter.mp ht).2)⟩
      · intro hs
        have hs' := (hV _).mp (Finset.mem_filter.mp hs).2
        exact Finset.mem_map.mpr ⟨es.symm s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa using hs'⟩, es.apply_symm_apply _⟩
    rw [← hfilter, Finset.card_map]
  have hU := h V
  change weightedExtractionProbability f p V - (V.card : ℝ) / Fintype.card O ≤ ε at hU
  rw [Fintype.card_congr eo] at hU
  change weightedExtractionProbability _ p U - (U.card : ℝ) / Fintype.card O' ≤ ε
  rw [heq]
  simpa only [V, Finset.card_map] using hU

/-- The RRV posterior cap at initial entropy K and first output width m is exactly the
point cap for residual entropy K−m−1, whenever the first stage leaves that many bits. -/
theorem posteriorCap_eq (m K : ℕ) (hm : m+1 ≤ K) :
    (1 / (2:ℝ)^K) * (2 * Fintype.card (Fin (2^m))) =
      1 / (2:ℝ)^(K-m-1) := by
  have hK : K = K-m-1+(m+1) := by omega
  have hpow : (2:ℝ)^K = (2:ℝ)^(K-m-1) * ((2:ℝ)^m*2) := by
    conv_lhs => rw [hK, pow_add, pow_succ]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [hpow]
  field_simp

/-- The exact weighted strong-extractor theorem at the two residual entropy thresholds,
with outputs and seeds independently combined and returned as part of the output. -/
theorem compose_binary_strong {X : Type} [Fintype X]
    {s1 s2 m1 m2 K : ℕ}
    (f1 : X → Fin (2^s1) → Fin (2^m1)) (f2 : X → Fin (2^s2) → Fin (2^m2))
    {p : X → ℝ} {ε δ : ℝ} (hP : ∑ x, p x = 1) (hδ : 0 ≤ δ)
    (hpm : ∀ x, 0 ≤ p x ∧ p x ≤ 1 / (2:ℝ)^K) (hm : m1 + 1 ≤ K)
    (hf1 : WeightedExtractorEvents (fun x s => (s, f1 x s)) p ε)
    (hf2 : ∀ q : X → ℝ, (∑ x, q x = 1) →
      (∀ x, 0 ≤ q x ∧ q x ≤ 1 / (2:ℝ)^(K-m1-1)) →
      WeightedExtractorEvents (fun x s => (s, f2 x s)) q δ) :
    WeightedExtractorEvents
      (fun (x : X) (s : Fin (2^(s1+s2))) =>
        let t := paddedSeedEquiv s1 s2 s
        (s, paddedOutputEquiv m1 m2 (f1 x t.1, f2 x t.2))) p (2*ε+δ) := by
  let eS := paddedSeedEquiv s1 s2
  let eO : ((Fin (2^s1) × Fin (2^m1)) × (Fin (2^s2) × Fin (2^m2))) ≃
      (Fin (2^(s1+s2)) × Fin (2^(m1+m2))) :=
    { toFun := fun a => (eS.symm (a.1.1,a.2.1), paddedOutputEquiv m1 m2 (a.1.2,a.2.2))
      invFun := fun a =>
        let t := eS a.1
        let y := (paddedOutputEquiv m1 m2).symm a.2
        ((t.1,y.1),(t.2,y.2))
      left_inv := by intro a; simp
      right_inv := by intro a; simp }
  have hq : ∀ q : X → ℝ, (∑ x, q x = 1) →
      (∀ x, 0 ≤ q x ∧ q x ≤ (1 / (2:ℝ)^K) * (2 * Fintype.card (Fin (2^m1)))) →
      WeightedExtractorEvents (fun x s => (s, f2 x s)) q δ := by
    simpa only [posteriorCap_eq m1 K hm] using hf2
  have h := compose_strong_event f1 f2 (fun x => (hpm x).1) hP (by positivity)
    (fun x => (hpm x).2) hδ (by simp) (by simp) (by simp) (by simp) hf1 hq
  simpa [eO] using equiv_weighted_event _ p _ eS eO h

end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

section IndependentSeed

variable {X S O B : Type}
variable [Fintype X] [Fintype S] [Fintype O] [Fintype B] [DecidableEq O] [DecidableEq B]

private theorem weighted_fibers (f : X → S → O) (p : X → ℝ) (U : Finset (O × B)) :
    let F := fun b : B => Finset.univ.filter (fun y : O => (y,b) ∈ U)
    weightedExtractionProbability (fun x (s : S × B) => (f x s.1,s.2)) p U =
      (∑ b, weightedExtractionProbability f p (F b)) / Fintype.card B := by
  classical
  dsimp only
  unfold weightedExtractionProbability
  rw [Fintype.card_prod, Nat.cast_mul, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← div_div, ← Finset.sum_div, ← Finset.mul_sum]
  congr 3
  simp only [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_sum]
  rw [Finset.sum_comm]

/-- The output of an extractor stays uniform when it includes extra independent seed bits. -/
theorem weighted_independent_seed (f : X → S → O) (p : X → ℝ) {ε : ℝ}
    (hB : 0 < Fintype.card B) (h : WeightedExtractorEvents f p ε) :
    WeightedExtractorEvents (fun x (s : S × B) => (f x s.1,s.2)) p ε := by
  classical
  intro U
  let F := fun b : B => Finset.univ.filter (fun y : O => (y,b) ∈ U)
  have hcount : U.card = ∑ b, (F b).card := by
    have hU : U = (Finset.univ : Finset (O × B)).filter (· ∈ U) := by ext; simp
    conv_lhs => rw [hU, Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp_rw [F, Finset.card_filter]
    rw [Finset.sum_comm]
  have hr : (U.card : ℝ) = ∑ b, ((F b).card : ℝ) := by exact_mod_cast hcount
  have hb : 0 < (Fintype.card B : ℝ) := by exact_mod_cast hB
  have hsum : ∑ b, (weightedExtractionProbability f p (F b) -
      ((F b).card : ℝ) / Fintype.card O) ≤ (Fintype.card B : ℝ) * ε := by
    calc
      _ ≤ ∑ _b : B, ε := Finset.sum_le_sum (fun b _ => h (F b))
      _ = _ := by simp [nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hr] at hsum
  change weightedExtractionProbability _ p U - (U.card : ℝ) / Fintype.card (O × B) ≤ ε
  rw [weighted_fibers, Fintype.card_prod, Nat.cast_mul, ← div_div, ← sub_div]
  exact (div_le_iff₀ hb).mpr (by simpa [mul_comm] using hsum)

end IndependentSeed

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

theorem weighted_drop_initial_seed_bits {X : Type} [Fintype X]
    {d m : ℕ} (hm : m ≤ d) (p : X → ℝ) {ε : ℝ} (hP : ∑ x, p x = 1) (hε : 0 ≤ ε) :
    WeightedExtractorEvents (fun (_ : X) (y : Fin (2^d)) =>
      ⟨y.val % 2^m, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩ : X → Fin (2^d) → Fin (2^m)) p ε := by
  classical
  have hsplit : d-m+m = d := Nat.sub_add_cancel hm
  let es : Fin (2^d) ≃ Fin (2^(d-m)) × Fin (2^m) :=
    (finCongr (congrArg (fun n : ℕ => 2^n) hsplit.symm)).trans (paddedSeedEquiv (d-m) m)
  apply equiv_weighted_event (fun _ (b : Fin (2^(d-m)) × Fin (2^m)) => b.2) p ε es (Equiv.refl _)
  intro U
  unfold weightedExtractionProbability
  have hfilter : (Finset.univ.filter (fun z : Fin (2^(d-m)) × Fin (2^m) => z.2 ∈ U)) =
      (Finset.univ : Finset (Fin (2^(d-m)))) ×ˢ U := by ext z; simp
  change (∑ x, p x * (((Finset.univ.filter (fun z : Fin (2^(d-m)) × Fin (2^m) => z.2 ∈ U)).card : ℕ) : ℝ) /
        Fintype.card (Fin (2^(d-m)) × Fin (2^m))) -
      (U.card : ℝ) / Fintype.card (Fin (2^m)) ≤ ε
  rw [hfilter, Finset.card_product, Finset.card_univ, Nat.cast_mul, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, ← Finset.sum_mul, hP, one_mul]
  have hp : 0 < (Fintype.card (Fin (2^(d-m))) : ℝ) := by simp
  rw [mul_div_mul_left _ _ hp.ne', sub_self]
  exact hε


end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV
section
variable {X S1 S2 O1 O2 : Type}
variable [Fintype X] [Fintype S1] [Fintype S2] [Fintype O1] [Fintype O2]
variable [DecidableEq S1] [DecidableEq S2] [DecidableEq O1] [DecidableEq O2]

private theorem uniform_event_weak {A : Type} [Fintype A] (U : Finset A) :
    eventMass (fun _ : A => 1 / (Fintype.card A : ℝ)) U = (U.card : ℝ) / Fintype.card A := by
  simp [eventMass, nsmul_eq_mul, div_eq_mul_inv]

private theorem uniform_total_weak {A : Type} [Fintype A] (hA : 0 < Fintype.card A) :
    ∑ _ : A, 1 / (Fintype.card A : ℝ) = 1 := by
  change eventMass (fun _ : A => 1/(Fintype.card A : ℝ)) Finset.univ = 1
  rw [uniform_event_weak, Finset.card_univ]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hA))

omit [Fintype O1] [DecidableEq S1] in
private theorem strongMass_mul_posterior_weak (ext : X → S1 → O1) (a : S1 × O1) {p : X → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hs : 0 < Fintype.card S1) (x : X) :
    strongMass ext p a * posterior ext p a x =
      (if ext x a.1 = a.2 then p x else 0) / (Fintype.card S1 : ℝ) := by
  let z := ∑ x, if ext x a.1 = a.2 then p x else 0
  let d : ℝ := Fintype.card S1
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  change z/d * (if z = 0 then p x else if ext x a.1 = a.2 then p x/z else 0) =
    (if ext x a.1 = a.2 then p x else 0)/d
  by_cases hz : z = 0
  · have hterm : (if ext x a.1 = a.2 then p x else 0) = 0 := by
      have hle : (if ext x a.1 = a.2 then p x else 0) ≤ z :=
        Finset.single_le_sum (f := fun y => if ext y a.1 = a.2 then p y else 0)
          (fun y _ => by split; exact hp y; rfl) (Finset.mem_univ x)
      have hlo : 0 ≤ (if ext x a.1 = a.2 then p x else 0) := by split; exact hp x; rfl
      linarith
    simp [hz, hterm]
  · rw [if_neg hz]
    split <;> (field_simp <;> ring)

omit [Fintype O1] [Fintype O2] [DecidableEq S1] [DecidableEq S2] in
private theorem tuple_mass_weak (f1 : X → S1 → O1) (f2 : X → S2 → O2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs1 : 0 < Fintype.card S1)
    (a : S1 × O1) (b : S2 × O2) :
    strongMass f1 p a * strongMass f2 (posterior f1 p a) b =
      (∑ x, if f1 x a.1 = a.2 ∧ f2 x b.1 = b.2 then p x else 0) /
        ((Fintype.card S1 : ℝ) * Fintype.card S2) := by
  change strongMass f1 p a *
      ((∑ x, if f2 x b.1 = b.2 then posterior f1 p a x else 0) / (Fintype.card S2 : ℝ)) = _
  rw [← mul_div_assoc, Finset.mul_sum, ← div_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : f2 x b.1 = b.2
  · simpa [hx] using strongMass_mul_posterior_weak f1 a hp hs1 x
  · simp [hx]

omit [Fintype O1] [Fintype O2] in
private theorem tuple_event_weak (f1 : X → S1 → O1) (f2 : X → S2 → O2)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hs1 : 0 < Fintype.card S1)
    (U : Finset ((S1 × O1) × (S2 × O2))) :
    eventMass (fun ab : (S1 × O1) × (S2 × O2) =>
        strongMass f1 p ab.1 * strongMass f2 (posterior f1 p ab.1) ab.2) U =
      weightedExtractionProbability
        (fun (x : X) (s : S1 × S2) => ((s.1, f1 x s.1), (s.2, f2 x s.2))) p U := by
  classical
  unfold eventMass weightedExtractionProbability
  simp_rw [tuple_mass_weak f1 f2 p hp hs1]
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm, Fintype.card_prod, Nat.cast_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  let T := (Finset.univ : Finset (S1 × S2)).filter
    (fun s => ((s.1,f1 x s.1),(s.2,f2 x s.2)) ∈ U)
  have hT : U.filter (fun ab : (S1 × O1) × (S2 × O2) =>
        f1 x ab.1.1 = ab.1.2 ∧ f2 x ab.2.1 = ab.2.2) =
      T.map (⟨fun s => ((s.1,f1 x s.1), (s.2,f2 x s.2)),
        fun _ _ h => congrArg (fun ab : (S1 × O1) × (S2 × O2) => (ab.1.1,ab.2.1)) h⟩ :
        (S1 × S2) ↪ (S1 × O1) × (S2 × O2)) := by
    ext ab
    rcases ab with ⟨⟨s1,o1⟩,⟨s2,o2⟩⟩
    simp only [Finset.mem_filter, Finset.mem_map, T, Finset.mem_univ, true_and]
    change ((s1,o1),(s2,o2)) ∈ U ∧ (f1 x s1 = o1 ∧ f2 x s2 = o2) ↔
      ∃ t : S1 × S2, ((t.1,f1 x t.1),(t.2,f2 x t.2)) ∈ U ∧
        ((t.1,f1 x t.1),(t.2,f2 x t.2)) = ((s1,o1),(s2,o2))
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hm, h1, h2⟩
      exact ⟨(s1,s2), by simpa [h1,h2] using hm, ⟨rfl,h1⟩, ⟨rfl,h2⟩⟩
    · rintro ⟨⟨t1,t2⟩, ht, ⟨rfl,h1⟩, ⟨rfl,h2⟩⟩
      exact ⟨by simpa [h1,h2] using ht, h1, h2⟩
  rw [← Finset.sum_filter, Finset.sum_const, hT, Finset.card_map, nsmul_eq_mul, mul_comm]

set_option maxHeartbeats 700000 in
/-- Retaining the first seed but only the weak output of the second extractor gives
the same entropy recovery guarantee. -/
theorem compose_weak_event (f1 : X → S1 → O1) (f2 : X → S2 → O2)
    {p : X → ℝ} {u ε δ : ℝ} (hp : ∀ x, 0 ≤ p x) (hP : ∑ x, p x = 1)
    (hu : 0 ≤ u) (hpu : ∀ x, p x ≤ u) (hδ : 0 ≤ δ)
    (hs1 : 0 < Fintype.card S1) (hs2 : 0 < Fintype.card S2)
    (ho1 : 0 < Fintype.card O1) (ho2 : 0 < Fintype.card O2)
    (hf1 : WeightedExtractorEvents (fun x s => (s, f1 x s)) p ε)
    (hf2 : ∀ q : X → ℝ, (∑ x, q x = 1) →
      (∀ x, 0 ≤ q x ∧ q x ≤ u * (2 * Fintype.card O1)) →
      WeightedExtractorEvents f2 q δ) :
    WeightedExtractorEvents
      (fun (x : X) (s : S1 × S2) => ((s.1, f1 x s.1), f2 x s.2)) p (2*ε+δ) := by
  classical
  let q1 : S1 × O1 → ℝ := fun _ => 1/(Fintype.card (S1 × O1) : ℝ)
  let q2 : O2 → ℝ := fun _ => 1/(Fintype.card O2 : ℝ)
  let p1 := strongMass f1 p
  let kernel a (b : O2) := ∑ s : S2, strongMass f2 (posterior f1 p a) (s,b)
  let bad := Finset.univ.filter fun a => 2 * p1 a < q1 a
  have hQ1 : ∑ a, q1 a = 1 := uniform_total_weak (by rw [Fintype.card_prod]; exact Nat.mul_pos hs1 ho1)
  have hQ2 : ∑ b, q2 b = 1 := uniform_total_weak ho2
  have hP1 : ∑ a, p1 a = 1 := strongMass_total f1 hP hs1
  have hε : EventClose p1 q1 ε := (weightedStrong_iff f1 p ε).mp hf1
  have hbad : eventMass p1 bad ≤ ε := lightMass_le p1 q1 hP1 hQ1 hε
  have hk a b : 0 ≤ kernel a b := Finset.sum_nonneg fun s _ =>
    strongMass_nonnegative f2 (posterior_nonnegative f1 a hp) (s,b)
  have hK a : ∑ b, kernel a b = 1 := by
    dsimp only [kernel]
    rw [Finset.sum_comm,← Finset.sum_product,Finset.univ_product_univ]
    exact strongMass_total f2 (posterior_total f1 a hP) hs2
  have hkernel (a : S1 × O1) (U : Finset O2) :
      eventMass (kernel a) U = weightedExtractionProbability f2 (posterior f1 p a) U := by
    unfold eventMass
    dsimp only [kernel]
    rw [Finset.sum_comm,← Finset.sum_product]
    change eventMass (strongMass f2 (posterior f1 p a)) _ = _
    rw [strongMass_event]
    apply Finset.sum_congr rfl
    intro x _
    have he : ((Finset.univ : Finset S2).filter fun s => (s,f2 x s) ∈ Finset.univ ×ˢ U) =
        (Finset.univ.filter fun s : S2 => f2 x s ∈ U) := by ext s; simp
    rw [he]
  have hgood (a : S1 × O1) (ha : a ∉ bad) : EventClose (kernel a) q2 δ := by
    have hb : q1 a ≤ 2 * p1 a := le_of_not_gt (by simpa [bad] using ha)
    have hf := hf2 _ (posterior_total f1 a hP)
      (fun x => ⟨posterior_nonnegative f1 a hp x, posterior_le f1 a hu hpu hs1 ho1 hb x⟩)
    intro U
    rw [hkernel,show eventMass q2 U = (U.card:ℝ)/Fintype.card O2 from uniform_event_weak _]
    exact hf U
  have hstat := conditionalClose p1 q1 kernel q2 bad (strongMass_nonnegative f1 hp)
    hk hK (fun _ => by dsimp [q2]; positivity) hQ2 hε hP1 hbad hδ hgood
  intro U
  have hproduct : (fun ab : (S1 × O1) × O2 => q1 ab.1 * q2 ab.2) =
      fun _ => 1/(Fintype.card ((S1 × O1) × O2) : ℝ) := by
    funext ab
    unfold q1 q2
    rw [Fintype.card_prod (α := S1 × O1) (β := O2), Nat.cast_mul, div_mul_div_comm, one_mul]
  let π (z : (S1 × O1) × (S2 × O2)) := (z.1,z.2.2)
  let lift (z : ((S1 × O1) × O2) × S2) : (S1 × O1) × (S2 × O2) :=
    (z.1.1,z.2,z.1.2)
  let V := (U ×ˢ (Finset.univ : Finset S2)).map
    (show (((S1 × O1) × O2) × S2) ↪ ((S1 × O1) × (S2 × O2)) from
      ⟨lift,fun x y h => Prod.ext (congrArg π h) (congrArg (fun z : (S1 × O1) × (S2 × O2) => z.2.1) h)⟩)
  have hV (z : (S1 × O1) × (S2 × O2)) : z ∈ V ↔ π z ∈ U := by
    constructor
    · intro h
      obtain ⟨v,hv,he⟩ := Finset.mem_map.mp h
      change lift v = z at he
      rw [← he]
      exact (Finset.mem_product.mp hv).1
    · intro hz
      exact Finset.mem_map.mpr ⟨(π z,z.2.1),
        Finset.mem_product.mpr ⟨hz,Finset.mem_univ _⟩,rfl⟩
  have hSource : eventMass (fun ab : (S1 × O1) × O2 => p1 ab.1 * kernel ab.1 ab.2) U =
      eventMass (fun ab : (S1 × O1) × (S2 × O2) =>
        strongMass f1 p ab.1 * strongMass f2 (posterior f1 p ab.1) ab.2) V := by
    dsimp only [eventMass, V, kernel, p1]
    rw [Finset.sum_map, Finset.sum_product]
    simp_rw [Finset.mul_sum,lift]
    rfl
  have hJoin : eventMass (fun ab : (S1 × O1) × O2 => p1 ab.1 * kernel ab.1 ab.2) U =
      weightedExtractionProbability (fun (x : X) (s : S1 × S2) =>
        ((s.1,f1 x s.1), f2 x s.2)) p U := by
    rw [hSource,tuple_event_weak f1 f2 p hp hs1]
    simp only [weightedExtractionProbability,hV,π]
  have hU := hstat U
  rw [hproduct,uniform_event_weak,hJoin] at hU
  exact hU.trans (by ring_nf; rfl)


end
end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA

/-- A finite sublevel set caps every event once the average mass of the points
above the level is bounded. -/
theorem capped_reference {Y : Type} [Fintype Y] [DecidableEq Y]
    (p : Y → ℝ) (cap δ : ℝ) (hp : ∑ y, p y = 1) (hp0 : ∀ y, 0 ≤ p y)
    (hc : 0 ≤ cap) (hcard : 1 ≤ (Fintype.card Y : ℝ)*cap)
    (he : ∀ U : Finset Y, (∑ y ∈ U,p y) ≤ (U.card : ℝ)*cap+δ) :
    ∃ q : Y → ℝ, (∑ y, q y) = 1 ∧ (∀ y, 0 ≤ q y ∧ q y ≤ cap) ∧
      ∀ U : Finset Y, (∑ y ∈ U, (p y-q y)) ≤ δ := by
  let a (y : Y) := min (p y) cap
  let A := ∑ y, a y
  let C := (Fintype.card Y : ℝ)*cap
  have ha y : 0 ≤ a y := le_min (hp0 y) hc
  have hac y : a y ≤ cap := min_le_right _ _
  have hap y : a y ≤ p y := min_le_left _ _
  have hA : A ≤ 1 := (Finset.sum_le_sum fun y _ => hap y).trans_eq hp
  have hCap : ∑ y : Y, (cap-a y) = C-A := by
    simp [C,A,Finset.sum_sub_distrib,nsmul_eq_mul]
  let D := Finset.univ.filter (fun y : Y => cap < p y)
  have hδ : ∑ y, (p y-a y) ≤ δ := by
    have he' := he D
    have hs : (∑ y, (p y-a y)) = ∑ y ∈ D, (p y-cap) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : cap < p y
      · simp [a,hy,min_eq_right hy.le]
      · simp [a,hy,min_eq_left (le_of_not_gt hy)]
    rw [hs,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    linarith
  have error_bound (q : Y → ℝ) (hq : ∀ y, a y ≤ q y) (U : Finset Y) :
      (∑ y ∈ U, (p y-q y)) ≤ δ := by
    calc
      _ ≤ ∑ y ∈ U, (p y-a y) := Finset.sum_le_sum fun y _ => sub_le_sub_left (hq y) _
      _ ≤ ∑ y : Y, (p y-a y) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ => sub_nonneg.mpr (hap y))
      _ ≤ _ := hδ
  by_cases hAone : A = 1
  · exact ⟨a,hAone,fun y => ⟨ha y,hac y⟩,error_bound a (fun _ => le_rfl)⟩
  have hCA : 0 < C-A := sub_pos.mpr ((lt_of_le_of_ne hA hAone).trans_le hcard)
  let η := (1-A)/(C-A)
  have hη0 : 0 ≤ η := div_nonneg (by linarith) hCA.le
  have hη1 : η ≤ 1 := (div_le_iff₀ hCA).2 (by linarith)
  let q (y : Y) := a y+η*(cap-a y)
  have hq y : a y ≤ q y := le_add_of_nonneg_right (mul_nonneg hη0 (sub_nonneg.mpr (hac y)))
  refine ⟨q,?_,fun y => ⟨(ha y).trans (hq y),?_⟩,error_bound q hq⟩
  · simp_rw [q,Finset.sum_add_distrib,← Finset.mul_sum]
    rw [hCap]
    change A+((1-A)/(C-A))*(C-A) = 1
    rw [div_mul_cancel₀ _ hCA.ne']
    ring
  · have hh := mul_le_mul_of_nonneg_right hη1 (sub_nonneg.mpr (hac y))
    simp only [one_mul] at hh
    dsimp [q]
    linarith

/-- Compare a capped source to a flat source on the points of greatest score. -/
theorem capped_average_le_some_flat {X : Type} [Fintype X] [DecidableEq X]
    (p f : X → ℝ) {K : ℕ} (hK : 0 < K) (hcard : K ≤ Fintype.card X)
    (hp : ∑ x, p x = 1) (hcap : ∀ x, 0 ≤ p x ∧ p x ≤ 1/(K:ℝ)) :
    ∃ S : Finset X, S.card = K ∧ (∑ x, p x*f x) ≤ (∑ x ∈ S, f x)/(K:ℝ) := by
  classical
  let scores : Finset (Finset X) := Finset.univ.powersetCard K
  have hex : scores.Nonempty := by
    obtain ⟨S,hSub,hS⟩ := Finset.exists_subset_card_eq hcard
    exact ⟨S,Finset.mem_powersetCard.mpr ⟨hSub,hS⟩⟩
  obtain ⟨T,hT,hMax⟩ := scores.exists_max_image (fun S => ∑ x ∈ S, f x) hex
  have hKT := (Finset.mem_powersetCard.mp hT).2
  have hNoSwap (x y : X) (hx : x ∈ T) (hy : y ∉ T) : f y ≤ f x := by
    have hNew : insert y (T.erase x) ∈ scores := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _,?_⟩
      rw [Finset.card_insert_of_notMem (fun h => hy (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hx,hKT]
      omega
    have hh := hMax _ hNew
    rw [Finset.sum_insert (fun h => hy (Finset.mem_of_mem_erase h))] at hh
    have he := Finset.sum_erase_add _ hx (f := f)
    linarith
  have hn : T.Nonempty := Finset.card_pos.mp (hKT.symm ▸ hK)
  obtain ⟨x,hx,hMin⟩ := T.exists_min_image f hn
  let b := f x
  let r (y : X) : ℝ := if y ∈ T then 1/(K:ℝ) else 0
  have hnK : (K:ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hr : ∑ y, r y = 1 := by
    unfold r
    rw [← Finset.sum_filter]
    simp [Finset.sum_const,nsmul_eq_mul,hKT,hnK]
  have hterm y : (p y-r y)*(f y-b) ≤ 0 := by
    by_cases hy : y ∈ T
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by simpa [r,hy] using (hcap y).2))
        (sub_nonneg.mpr (hMin _ hy))
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (by simpa [r,hy] using (hcap y).1))
        (sub_nonpos.mpr (hNoSwap x y hx hy))
  have hMass : ∑ y : X, (p y-r y)*(f y-b) = ∑ y, p y*f y - ∑ y, r y*f y := by
    simp_rw [sub_mul,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hp,hr]
    ring
  have hab : (∑ y : X, (p y-r y)*(f y-b)) ≤ 0 :=
    Finset.sum_nonpos fun y _ => hterm y
  rw [hMass] at hab
  refine ⟨T,hKT,?_⟩
  have hFlat : ∑ y : X, r y * f y = (∑ y ∈ T, f y)/(K:ℝ) := by
    simp_rw [r,ite_mul,zero_mul,← Finset.sum_filter,← Finset.mul_sum]
    simp [div_eq_mul_inv,mul_comm]
  linarith

end TimeSpaceMA

namespace TimeSpaceMA

open scoped BigOperators

variable {X Seed Y : Type} [Fintype X] [Fintype Seed] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]

/-- Weighted analogue of the flat condenser event condition. -/
def WeightedCondenses (cond : X → Seed → Y) (p : X → ℝ) (q : Y → ℝ) (δ : ℝ) : Prop :=
  ∀ U : Finset Y, weightedExtractionProbability cond p U - ∑ y ∈ U, q y ≤ δ

/-- A lossless condenser that works for every flat set of size K also works for
every weighted source capped at 1/K. -/
theorem WeightedCondenses.ofFlat (cond : X → Seed → Y) {K : ℕ} (hK : 0 < K)
    (hKX : K ≤ Fintype.card X) (hs : 0 < Fintype.card Seed) (p : X → ℝ)
    (hp : ∑ x, p x = 1) (hcap : ∀ x, 0 ≤ p x ∧ p x ≤ 1/(K:ℝ))
    (cap δ : ℝ) (hcap0 : 0 ≤ cap) (hRoom : 1 ≤ (Fintype.card Y : ℝ)*cap)
    (hflat : ∀ S : Finset X, S.card = K →
      ∃ q : Y → ℝ, (∀ y, q y ≤ cap) ∧ CondensesFlatEvents cond S q δ) :
    ∃ q : Y → ℝ, (∑ y, q y) = 1 ∧ (∀ y, 0 ≤ q y ∧ q y ≤ cap) ∧
      WeightedCondenses cond p q δ := by
  classical
  let f (y : Y) : ℝ := weightedExtractionProbability cond p {y}
  have hf (U : Finset Y) :
      weightedExtractionProbability cond p U = ∑ y ∈ U, f y := by
    dsimp only [f,weightedExtractionProbability]
    rw [Finset.sum_comm (s := U)]
    apply Finset.sum_congr rfl
    intro x _
    have hh : (((Finset.univ : Finset Seed).filter fun r => cond x r ∈ U).card : ℝ) =
        ∑ y ∈ U, (((Finset.univ : Finset Seed).filter fun r => cond x r ∈ ({y}:Finset Y)).card : ℝ) := by
      simp_rw [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hh : cond x s ∈ U
      · rw [if_pos hh]
        simp [hh]
      · simp [hh]
    rw [hh, Finset.mul_sum, Finset.sum_div]
  have hf0 (y : Y) : 0 ≤ f y := Finset.sum_nonneg (fun x _ =>
    div_nonneg (mul_nonneg (hcap x).1 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  have hfNorm : ∑ y, f y = 1 := by
    rw [← hf]
    unfold weightedExtractionProbability
    have hs' : (Fintype.card Seed : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    simpa [hs',mul_div_cancel_right₀] using hp
  have hTest (U : Finset Y) : (∑ y ∈ U, f y) ≤ (U.card : ℝ) * cap + δ := by
    rw [← hf]
    let score (x : X) : ℝ :=
      (((Finset.univ : Finset Seed).filter fun r => cond x r ∈ U).card : ℝ) / Fintype.card Seed
    obtain ⟨S,hS,hSc⟩ := capped_average_le_some_flat p score hK hKX hp hcap
    obtain ⟨q,hq,hqcond⟩ := hflat S hS
    have hcnt : (∑ x ∈ S, (((Finset.univ : Finset Seed).filter fun r => cond x r ∈ U).card : ℝ)) =
        (((S ×ˢ Finset.univ).filter fun p : X × Seed => cond p.1 p.2 ∈ U).card : ℝ) := by
      simp_rw [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_product]
    have hSc' : weightedExtractionProbability cond p U ≤
        (((S ×ˢ Finset.univ).filter fun p : X × Seed => cond p.1 p.2 ∈ U).card : ℝ) /
          ((S.card : ℝ)*Fintype.card Seed) := by
      simpa [weightedExtractionProbability,score,mul_div_assoc,← Finset.sum_div,hcnt,hS,
        div_div, mul_comm] using hSc
    have hqU := hqcond U
    have hqCap : (∑ y ∈ U, q y) ≤ (U.card : ℝ)*cap := by
      calc
        _ ≤ ∑ _ ∈ U, cap := Finset.sum_le_sum (fun y _ => hq y)
        _ = _ := by simp [nsmul_eq_mul]
    linarith
  obtain ⟨q,hq,hqc,he⟩ := capped_reference f cap δ hfNorm hf0 hcap0 hRoom hTest
  refine ⟨q,hq,hqc,?_⟩
  intro U
  rw [hf, ← Finset.sum_sub_distrib]
  exact he U

/-- The exact weighted form of the selected GUV condenser schedule. -/
theorem HasShortLosslessCondenser.weighted {δ : ℝ} (h : HasShortLosslessCondenser δ) :
    ∃ (a : ℕ) (cond : ExtractorInput → ℕ), 0 < a ∧
      Turing.MultiTapeTM.ComputableInPolyTime cond encExtractorInput
        Turing.MultiTapeTM.encNat ∧
      ∀ n k : ℕ, 1 ≤ n → k ≤ n →
        let s := a*n.size
        let m := 2*(k+s)
        ∀ p : Fin (2^n) → ℝ, (∑ x, p x) = 1 →
          (∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^k) →
          ∃ q : Fin (2^m) → ℝ, (∑ y, q y) = 1 ∧
            (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^(k+s)) ∧
            WeightedCondenses (fixedOutput cond n k s m) p q δ := by
  obtain ⟨a,cond,ha,hc,h⟩ := h
  refine ⟨a,cond,ha,hc,?_⟩
  intro n k hn hk s m p hp hcap
  have hpos : (0:ℝ) < (2:ℝ)^(k+s) := by positivity
  have hKX : 2^k ≤ Fintype.card (Fin (2^n)) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hRoom : 1 ≤ (Fintype.card (Fin (2^m)) : ℝ)*(1/(2:ℝ)^(k+s)) := by
    rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat, ← div_eq_mul_one_div]
    apply (le_div_iff₀ hpos).2
    simp only [one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by dsimp [m]; omega)
  apply WeightedCondenses.ofFlat _ (K:=2^k) (by positivity) hKX (by simp) p hp
    (by exact_mod_cast hcap) _ _ (by positivity) hRoom
  intro S hS
  obtain ⟨q,_,hcap,hq⟩ := h n k hn hk S hS.ge
  exact ⟨q,fun y => (hcap y).2,hq⟩

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

section
variable {X Seed Out : Type} [Fintype X] [Fintype Seed] [Fintype Out] [DecidableEq Out] [DecidableEq Seed]

noncomputable def hashMass (f : X → Seed → Out) (p : X → ℝ) (s : Seed) (z : Out) : ℝ :=
  ∑ x, if f x s = z then p x else 0

omit [Fintype Seed] [DecidableEq Seed] in
private theorem sum_hashMass (f : X → Seed → Out) (p : X → ℝ) (s : Seed) :
    ∑ z, hashMass f p s z = ∑ x, p x := by
  unfold hashMass
  rw [Finset.sum_comm]
  simp

omit [Fintype Seed] [DecidableEq Seed] in
private theorem sum_hashMass_sq (f : X → Seed → Out) (p : X → ℝ) (s : Seed) :
    ∑ z, hashMass f p s z ^ 2 =
      ∑ x, ∑ y, if f x s = f y s then p x * p y else 0 := by
  classical
  unfold hashMass
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hh : f x s = f y s
  · simp_rw [hh]
    simp [mul_ite, mul_comm]
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hx : f x s = z
    · have hy : f y s ≠ z := fun e => hh (hx.trans e.symm)
      simp [hx,hy]
    · simp [hx]

/-- A collision-universal hash family yields a strong extractor for every finite
source with a point-mass cap. The error bound is given without square roots. -/
theorem weighted_leftover_hash
    (f : X → Seed → Out) (p : X → ℝ) (u ε : ℝ)
    (hS : 0 < Fintype.card Seed) (hO : 0 < Fintype.card Out)
    (hp : ∑ x, p x = 1) (hpu : ∀ x, 0 ≤ p x ∧ p x ≤ u)
    (hε : 0 ≤ ε) (herr : (Fintype.card Out : ℝ)*u ≤ ε^2)
    (huniv : ∀ x y, x ≠ y →
      ((Finset.univ.filter (fun s => f x s = f y s)).card : ℝ) *
        Fintype.card Out ≤ Fintype.card Seed) :
    WeightedExtractorEvents (fun x s => (s,f x s)) p ε := by
  classical
  let S : ℝ := Fintype.card Seed
  let O : ℝ := Fintype.card Out
  have hS' : 0 < S := by dsimp [S]; exact_mod_cast hS
  have hO' : 0 < O := by dsimp [O]; exact_mod_cast hO
  let m := hashMass f p
  let v (s : Seed) (z : Out) := m s z - 1/O
  have diag (x : X) : (∑ s : Seed, if f x s = f x s then p x * p x else 0) =
      S*(p x*p x) := by simp [S,nsmul_eq_mul]
  have off (x y : X) (h : x ≠ y) :
      (∑ s : Seed, if f x s = f y s then p x*p y else 0) ≤ S/O*(p x*p y) := by
    have c := (le_div_iff₀ hO').2 (huniv x y h)
    rw [← Finset.sum_filter]
    simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_right c (mul_nonneg (hpu x).1 (hpu y).1)
  have energy : ∑ s : Seed, ∑ z : Out, m s z ^ 2 ≤ S*u+S/O := by
    simp_rw [m,sum_hashMass_sq]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Seed)) (t := (Finset.univ : Finset X))]
    have hterm (x y : X) : (∑ s : Seed, if f x s = f y s then p x*p y else 0) ≤
        (if x=y then S*(p x*p x) else 0) + S/O*(p x*p y) := by
      by_cases h : x=y
      · subst y
        rw [diag]
        simp only [if_true]
        exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hS'.le hO'.le) (mul_nonneg (hpu x).1 (hpu x).1))
      · simpa [h] using off x y h
    calc
      _ ≤ ∑ x, ∑ y, ((if x=y then S*(p x*p x) else 0) + S/O*(p x*p y)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
      _ = S*(∑ x, p x*p x)+S/O := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum, ← mul_assoc, ← Finset.mul_sum]
        simp [hp, mul_assoc]
        rw [← Finset.mul_sum,hp,mul_one]
      _ ≤ _ := by
        have hd : ∑ x, p x*p x ≤ u := by
          calc
            _ ≤ ∑ x, p x*u := Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_left (hpu x).2 (hpu x).1
            _ = u := by rw [← Finset.sum_mul,hp,one_mul]
        exact add_le_add_left (mul_le_mul_of_nonneg_left hd hS'.le) _
  have center (s : Seed) : ∑ z : Out, (v s z)^2 = (∑ z : Out, (m s z)^2)-1/O := by
    have hm : ∑ z : Out, m s z = 1 := (sum_hashMass f p s).trans hp
    calc
      _ = ∑ z : Out, ((m s z)^2-(2/O)*m s z+(1/O)^2) := by
        apply Finset.sum_congr rfl
        intro z _
        dsimp only [v]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hm,
          mul_one, Finset.sum_const, nsmul_eq_mul]
        change _ - 2 / O + O * (1/O)^2 = _
        field_simp; ring
  have centered : (∑ z : Seed × Out, (v z.1 z.2)^2) ≤ S*u := by
    rw [Fintype.sum_prod_type]
    simp_rw [center,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    change (∑ s : Seed, ∑ z : Out, m s z^2)-S*(1/O) ≤ S*u
    rw [← div_eq_mul_one_div]
    linarith
  intro U
  have hpU : weightedExtractionProbability (fun x s => (s,f x s)) p U =
      (∑ z ∈ U, m z.1 z.2)/S := by
    have hf (x : X) : (((Finset.univ : Finset Seed).filter fun s => (s,f x s) ∈ U).card : ℝ) =
        ∑ z ∈ U, if f x z.1 = z.2 then 1 else 0 := by
      rw [Finset.card_filter,Nat.cast_sum]
      simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      rw [← Finset.sum_filter,← Finset.sum_filter]
      have hmap : ((Finset.univ : Finset Seed).filter fun s => (s,f x s) ∈ U).map
          (show Seed ↪ Seed × Out from ⟨fun s => (s,f x s),fun s t h => congrArg Prod.fst h⟩) =
          U.filter (fun z => f x z.1 = z.2) := by
        ext z
        constructor
        · intro h
          obtain ⟨s,hs,he⟩ := Finset.mem_map.mp h
          change (s,f x s) = z at he
          subst z
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).2,rfl⟩
        · intro hz
          obtain ⟨hz,hc⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_map.mpr ⟨z.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
            rcases z with ⟨s,o⟩
            simpa only [hc] using hz⟩,Prod.ext rfl hc⟩
      rw [← hmap]
      simp
    unfold weightedExtractionProbability
    rw [← Finset.sum_div]
    simp_rw [hf, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine congrArg (fun y : ℝ => y / S) (Finset.sum_congr rfl fun z _ => ?_)
    unfold m hashMass
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp
  have excess : weightedExtractionProbability (fun x s => (s,f x s)) p U -
      (U.card : ℝ)/Fintype.card (Seed × Out) = (∑ z ∈ U, v z.1 z.2)/S := by
    rw [hpU, Fintype.card_prod, Nat.cast_mul, mul_comm (↑(Fintype.card Seed) : ℝ), ← div_div, ← sub_div]
    simp_rw [v,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    rw [← div_eq_mul_one_div]
  have hu : ∑ z ∈ U, (v z.1 z.2)^2 ≤ S*u :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (by intros; positivity)).trans centered
  have hCard : (U.card : ℝ) ≤ S*O := by
    have h := Finset.card_le_univ U
    rw [Fintype.card_prod] at h
    dsimp [S,O]
    exact_mod_cast h
  have hsq : (∑ z ∈ U, v z.1 z.2)^2 ≤ (S*ε)^2 := by
    have hb := Finset.sum_mul_sq_le_sq_mul_sq U (fun z : Seed × Out => (1:ℝ)) (fun z => v z.1 z.2)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
    calc
      _ ≤ (U.card : ℝ) * ∑ z ∈ U, (v z.1 z.2)^2 := hb
      _ ≤ S*O*(S*u) := mul_le_mul hCard hu (Finset.sum_nonneg (by intros; positivity)) (by positivity)
      _ = S^2*(O*u) := by ring
      _ ≤ S^2*ε^2 := mul_le_mul_of_nonneg_left herr (by positivity)
      _ = _ := by ring
  rw [excess,div_le_iff₀ hS']
  have hNon : 0 ≤ S*ε := mul_nonneg hS'.le hε
  have ha : |∑ z ∈ U, v z.1 z.2| ≤ S*ε := (sq_le_sq₀ (abs_nonneg _) hNon).mp (by rwa [sq_abs])
  rw [mul_comm ε S]
  exact (le_abs_self _).trans ha

end

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

/-- A binary Toeplitz matrix uses a single seed bit on each skew diagonal.
The last seed bit is unused, yielding the convenient exact width n+m. -/
def toeplitzHash {n m : ℕ} (x : Fin n → ZMod 2) (s : Fin (n+m) → ZMod 2) :
    Fin m → ZMod 2 :=
  fun i => ∑ j : Fin n, x j * s ⟨i.val+j.val, by omega⟩

private theorem collisionCount_toeplitz {n m : ℕ}
    (x y : Fin n → ZMod 2) (hxy : x ≠ y) :
    (Finset.univ.filter (fun s : Fin (n+m) → ZMod 2 => toeplitzHash x s = toeplitzHash y s)).card
      ≤ 2^n := by
  classical
  let Δ := Finset.univ.filter (fun j : Fin n => x j ≠ y j)
  have hΔ : Δ.Nonempty := by
    by_contra! h
    apply hxy
    ext j
    by_contra hj
    have hm : j ∈ Δ := by simpa [Δ] using hj
    rw [h] at hm
    exact Finset.notMem_empty _ hm
  let p : Fin n := Δ.max' hΔ
  have hp : x p ≠ y p := by
    have h := Finset.max'_mem Δ hΔ
    simpa [Δ,p] using h
  have hzero (j : Fin n) (hj : p.val < j.val) : x j - y j = 0 := by
    by_contra hd
    have hmem : j ∈ Δ := by simpa [Δ, sub_ne_zero] using hd
    have hle : j ≤ p := Finset.le_max' Δ _ hmem
    exact (not_le_of_gt hj) hle
  let free (j : Fin n) : Fin (n+m) := ⟨if j.val < p.val then j.val else j.val + m, by
    split <;> omega⟩
  let forget (s : Fin (n+m) → ZMod 2) (j : Fin n) := s (free j)
  let C := Finset.univ.filter (fun s : Fin (n+m) → ZMod 2 => toeplitzHash x s = toeplitzHash y s)
  have hinj (s t : Fin (n+m) → ZMod 2) (hs : s ∈ C) (ht : t ∈ C)
      (hforget : forget s = forget t) : s = t := by
    have hcollS : toeplitzHash x s = toeplitzHash y s := (Finset.mem_filter.mp hs).2
    have hcollT : toeplitzHash x t = toeplitzHash y t := (Finset.mem_filter.mp ht).2
    have hsum (u : Fin (n+m) → ZMod 2) (hu : toeplitzHash x u = toeplitzHash y u) (i : Fin m) :
        ∑ j : Fin n, (x j-y j) * u ⟨i.val+j.val, by omega⟩ = 0 := by
      have hz := congrFun hu i
      change ∑ j : Fin n, x j * u ⟨i.val+j.val, by omega⟩ =
        ∑ j : Fin n, y j * u ⟨i.val+j.val, by omega⟩ at hz
      simp_rw [sub_mul, Finset.sum_sub_distrib, hz, sub_self]
    have hN (q : ℕ) : ∀ hq : q < n+m, s ⟨q,hq⟩ = t ⟨q,hq⟩ := by
      induction q using Nat.strong_induction_on with
      | h q ih =>
        intro hq
        by_cases hlo : q < p.val
        · have h := congrFun hforget (⟨q, by omega⟩ : Fin n)
          change s ⟨if q < p.val then q else q+m, _⟩ =
            t ⟨if q < p.val then q else q+m, _⟩ at h
          simpa only [if_pos hlo] using h
        by_cases hhi : p.val+m ≤ q
        · have hqp : ¬q-m < p.val := by omega
          have h := congrFun hforget (⟨q-m, by omega⟩ : Fin n)
          have hqv : q-m+m = q := by omega
          change s ⟨if q-m < p.val then q-m else q-m+m, _⟩ =
            t ⟨if q-m < p.val then q-m else q-m+m, _⟩ at h
          simpa only [if_neg hqp, hqv] using h
        let i : Fin m := ⟨q-p.val, by omega⟩
        have hAt : i.val + p.val = q := by dsimp [i]; omega
        let g (u : Fin (n+m) → ZMod 2) (j : Fin n) :=
          (x j-y j) * u ⟨i.val+j.val, by omega⟩
        have hsc : ∑ j : Fin n, g s j = 0 := hsum s hcollS i
        have htc : ∑ j : Fin n, g t j = 0 := hsum t hcollT i
        have hErase : (∑ j ∈ (Finset.univ : Finset (Fin n)).erase p, g s j) =
            ∑ j ∈ (Finset.univ : Finset (Fin n)).erase p, g t j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjp := (Finset.mem_erase.mp hj).1
          by_cases hless : j.val < p.val
          · unfold g
            rw [ih _ (by omega)]
          · have hmore : p.val < j.val := by
              have : j.val ≠ p.val := fun h => hjp (Fin.ext h)
              omega
            simp [g, hzero j hmore]
        have hfs := Finset.sum_erase_add Finset.univ (g s) (Finset.mem_univ p)
        have hft := Finset.sum_erase_add Finset.univ (g t) (Finset.mem_univ p)
        rw [hsc] at hfs
        rw [htc, ← hErase] at hft
        have heq : g s p = g t p := add_left_cancel (hfs.trans hft.symm)
        have hcan := mul_left_cancel₀ (sub_ne_zero.mpr hp) heq
        simpa [hAt] using hcan
    funext j
    exact hN j.val j.isLt
  calc
    C.card ≤ (Finset.univ : Finset (Fin n → ZMod 2)).card := by
      apply Finset.card_le_card_of_injOn forget
      · exact fun _ _ => Finset.mem_univ _
      · exact fun s hs t ht h => hinj s t hs ht h
    _ = 2^n := by simp

/-- Every distinct pair collides under at most a (2^{-m}) fraction
of Toeplitz seeds, as an integer counting inequality. -/
theorem toeplitzHash_universal {n m : ℕ}
    (x y : Fin n → ZMod 2) (hxy : x ≠ y) :
    (Finset.univ.filter (fun s : Fin (n+m) → ZMod 2 =>
      toeplitzHash (m := m) x s = toeplitzHash (m := m) y s)).card *
        Fintype.card (Fin m → ZMod 2) ≤ Fintype.card (Fin (n+m) → ZMod 2) := by
  have hcount (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2^k := by simp
  rw [hcount, hcount, pow_add]
  exact Nat.mul_le_mul_right _ (collisionCount_toeplitz x y hxy)

end TimeSpaceMA

namespace TimeSpaceMA

/-- Natural output label, with coordinate zero assigned the least significant bit. -/
def packBits {m : ℕ} (bits : Fin m → ZMod 2) : ℕ :=
  ∑ i, (bits i).val * 2^i.val

/-- Unpack a natural label into its little-endian bit vector. -/
def unpackBits {m : ℕ} (x : Fin (2^m)) : Fin m → ZMod 2 :=
  fun i => (x.val / 2^i.val : ℕ)

theorem pack_unpackBits {m : ℕ} (x : Fin (2^m)) : packBits (unpackBits x) = x.val := by
  have h : ∀ (m z : ℕ), z < 2^m →
      (∑ i : Fin m, (z / 2^i.val % 2) * 2^i.val) = z := by
    intro m
    induction m with
    | zero => intro z hz; simp at hz; simp [hz]
    | succ m ih =>
      intro z hz
      have hz' : z / 2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hz)
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one, Fin.val_succ]
      have hs (i : Fin m) : (z / 2^(i.val+1) % 2) * 2^(i.val+1) =
          2 * ((z/2 / 2^i.val % 2) * 2^i.val) := by
        rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm 2 (2^i.val)]
        ac_rfl
      simp_rw [hs]
      rw [← Finset.mul_sum, ih _ hz']
      exact Nat.mod_add_div z 2
  simpa only [packBits, unpackBits, ZMod.val_natCast] using h m x.val x.isLt

/-- The canonical equivalence between numerical labels and bit vectors. -/
noncomputable def bitsEquiv (m : ℕ) : Fin (2^m) ≃ (Fin m → ZMod 2) := by
  let e : Fin (2^m) ≃ (Fin m → ZMod 2) := Fintype.equivOfCardEq (by simp)
  have hi : Function.Injective (unpackBits (m := m)) :=
    fun x y he => Fin.ext (by simpa only [pack_unpackBits] using congrArg packBits he)
  exact Equiv.ofBijective unpackBits ⟨hi, (Finite.injective_iff_surjective_of_equiv e).mp hi⟩

theorem bitsEquiv_apply {m : ℕ} (v : Fin (2^m)) : bitsEquiv m v = unpackBits v :=
  rfl

theorem bitsEquiv_symm_val {m : ℕ} (v : Fin m → ZMod 2) :
    ((bitsEquiv m).symm v).val = packBits v := by
  calc
    _ = packBits (unpackBits ((bitsEquiv m).symm v)) := (pack_unpackBits _).symm
    _ = packBits v := congrArg packBits ((bitsEquiv m).apply_symm_apply v)

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

private theorem sum_range_map {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [← List.sum_toFinset f List.nodup_range, List.toFinset_range, Finset.sum_range]

/-- One output coordinate of a binary diagonal hash, evaluated with arithmetic on labels. -/
def Toeplitz.bit (p : (ℕ × ℕ × ℕ) × ℕ) : ℕ :=
  (((List.range p.1.1).map fun j =>
    (p.1.2.1 / 2^j % 2) * (p.1.2.2 / 2^(p.2+j) % 2)).sum) % 2

/-- The encoded widths control the two loops, even for values with leading zero bits. -/
def Toeplitz.eval (p : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  ((List.range p.2.1).map fun i =>
    Toeplitz.bit ((p.1,p.2.2.1,p.2.2.2),i) * 2^i).sum

abbrev Toeplitz.encInput : (ℕ × ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat encNat))

private abbrev Toeplitz.encBitInput : ((ℕ × ℕ × ℕ) × ℕ) ↪ List Bool :=
  encPair (encPair encUnary (encPair encNat encNat)) encUnary

private theorem Toeplitz.bit_polytime :
    ComputableTidilyInPolyTime Toeplitz.bit Toeplitz.encBitInput encNat := by
  let input := Toeplitz.encBitInput
  have hn : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ × ℕ) × ℕ => p.1.1) input encUnary :=
    (fst _ _).fst'
  have hl := range.comp hn
  have hf : ComputableTidilyInPolyTime (fun p : ((ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      (p.1.1.2.1 / 2^p.2 % 2) * (p.1.1.2.2 / 2^(p.1.2+p.2) % 2))
      (encPair input encUnary) encNat := by
    have houter := fst input encUnary
    have hj := snd input encUnary
    have hi := houter.snd'
    have hx := houter.fst'.snd'.fst'
    have hs := houter.fst'.snd'.snd'
    have hp := binary_two_pow.comp hj
    have hq := binary_two_pow.comp (unary_add.comp (hi.prod hj))
    exact binary_mul'
      (binary_mod' (binary_div' hx hp) (const 2))
      (binary_mod' (binary_div' hs hq) (const 2))
  exact binary_mod' (binary_sum.comp (mapWithInput hl hf)) (const 2)

theorem Toeplitz.eval_polytime :
    ComputableInPolyTime Toeplitz.eval Toeplitz.encInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let input := Toeplitz.encInput
  have hm : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) input encUnary :=
    (snd _ _).fst'
  have hl := range.comp hm
  have hf : ComputableTidilyInPolyTime (fun p : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
      Toeplitz.bit ((p.1.1,p.1.2.2.1,p.1.2.2.2),p.2) * 2^p.2)
      (encPair input encUnary) encNat := by
    have houter := fst input encUnary
    have hi := snd input encUnary
    have hn := houter.fst'
    have hx := houter.snd'.snd'.fst'
    have hs := houter.snd'.snd'.snd'
    exact binary_mul' (Toeplitz.bit_polytime.comp ((hn.prod (hx.prod hs)).prod hi))
      (binary_two_pow.comp hi)
  exact binary_sum.comp (mapWithInput hl hf)

theorem Toeplitz.eval_eq_pack {n m : ℕ}
    (x : Fin (2^n)) (s : Fin (2^(n+m))) :
    Toeplitz.eval (n,m,x.val,s.val) = packBits (toeplitzHash (bitsEquiv n x) (bitsEquiv (n+m) s)) := by
  unfold Toeplitz.eval packBits
  rw [sum_range_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold Toeplitz.bit
  rw [sum_range_map]
  simp only [toeplitzHash, bitsEquiv_apply, unpackBits]
  rw [← ZMod.val_natCast 2]
  congr 1
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have hm (z : ℕ) : ((z % 2 : ℕ) : ZMod 2) = (z : ZMod 2) := by
    apply ZMod.val_injective 2
    simp [ZMod.val_natCast]
  simp only [hm]

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

/-- Universal hashing as a map of the binary labels used by the TUZ encoding. -/
def Toeplitz.edge {w m : ℕ} (x : Fin (2^w)) (s : Fin (2^(w+m))) : Fin (2^m) :=
  ⟨Toeplitz.eval (w,m,x.val,s.val) % 2^m, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

theorem Toeplitz.edge_eq {w m : ℕ} (x : Fin (2^w)) (s : Fin (2^(w+m))) :
    Toeplitz.edge (m := m) x s =
      (bitsEquiv m).symm (toeplitzHash (bitsEquiv w x) (bitsEquiv (w+m) s)) := by
  apply Fin.ext
  change Toeplitz.eval (w,m,x.val,s.val) % 2^m = _
  rw [Toeplitz.eval_eq_pack, ← bitsEquiv_symm_val, Nat.mod_eq_of_lt (Fin.isLt _)]

theorem Toeplitz.edge_universal {w m : ℕ} (x y : Fin (2^w)) (hxy : x ≠ y) :
    ((Finset.univ.filter (fun s : Fin (2^(w+m)) => Toeplitz.edge x s = Toeplitz.edge y s)).card : ℝ)
      * Fintype.card (Fin (2^m)) ≤ Fintype.card (Fin (2^(w+m))) := by
  classical
  let e := bitsEquiv (w+m)
  let h := fun s : Fin (w+m) → ZMod 2 => toeplitzHash (m := m) (bitsEquiv w x) s =
    toeplitzHash (m := m) (bitsEquiv w y) s
  have he (s : Fin (2^(w+m))) :
      Toeplitz.edge x s = Toeplitz.edge y s ↔ h (e s) := by
    rw [Toeplitz.edge_eq, Toeplitz.edge_eq]
    exact (bitsEquiv m).symm.injective.eq_iff
  have hc : ((Finset.univ : Finset (Fin (2^(w+m)))).filter
      (fun s => Toeplitz.edge x s = Toeplitz.edge y s)).map e.toEmbedding =
      (Finset.univ : Finset (Fin (w+m) → ZMod 2)).filter h := by
    ext s
    constructor
    · intro hs
      obtain ⟨t,ht,ht'⟩ := Finset.mem_map.mp hs
      change e t = s at ht'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht' ▸ (he t).mp (Finset.mem_filter.mp ht).2⟩
    · intro hs
      have ht := (Finset.mem_filter.mp hs).2
      refine Finset.mem_map.mpr ⟨e.symm s,Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        e.apply_symm_apply _⟩
      exact (he _).mpr (by simpa using ht)
  have hu := toeplitzHash_universal (m := m) (bitsEquiv w x) (bitsEquiv w y)
    (fun hx => hxy ((bitsEquiv w).injective hx))
  change (Finset.univ.filter h).card * _ ≤ _ at hu
  rw [← hc, Finset.card_map, ← Fintype.card_congr (bitsEquiv m), ← Fintype.card_congr e] at hu
  exact_mod_cast hu

/-- The arithmetic Toeplitz hash is a strong extractor from w bits with
seed width w+m and payload width m, at the leftover hash error bound. -/
theorem Toeplitz.edge_extracts {w m : ℕ} (p : Fin (2^w) → ℝ) {u ε : ℝ}
    (hp : ∑ x, p x = 1) (hpu : ∀ x, 0 ≤ p x ∧ p x ≤ u)
    (hε : 0 ≤ ε) (herr : (2:ℝ)^m*u ≤ ε^2) :
    WeightedExtractorEvents (fun x s => (s, Toeplitz.edge (m := m) x s)) p ε := by
  apply weighted_leftover_hash _ p u ε (by simp) (by simp) hp hpu hε
  · simpa using herr
  · exact fun x y => Toeplitz.edge_universal x y

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Push a weighted condenser output through an extractor. The seed of the second
extraction is fresh, so the statistical errors add. -/
theorem weighted_condense_then_extract {X Y S T O : Type}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype T] [Fintype O] [DecidableEq Y] [DecidableEq O]
    (c : X → S → Y) (f : Y → T → O) (p : X → ℝ) (q : Y → ℝ) {γ ε : ℝ}
    (ht : 0 < Fintype.card T) (hc : WeightedCondenses c p q γ)
    (hf : WeightedExtractorEvents f q ε) :
    WeightedExtractorEvents (fun x (s : S × T) => f (c x s.1) s.2) p (γ+ε) := by
  classical
  intro U
  let A := fun t : T => Finset.univ.filter (fun y : Y => f y t ∈ U)
  have hc' (t : T) := hc (A t)
  have hsum : ∑ t, (weightedExtractionProbability c p (A t) - ∑ y ∈ A t, q y) ≤
      (Fintype.card T : ℝ)*γ := by
    calc
      _ ≤ ∑ _t : T, γ := Finset.sum_le_sum (fun t _ => hc' t)
      _ = _ := by simp [nsmul_eq_mul]
  rw [Finset.sum_sub_distrib] at hsum
  have h1 : weightedExtractionProbability (fun x (s : S × T) => f (c x s.1) s.2) p U =
      (∑ t, weightedExtractionProbability c p (A t)) / Fintype.card T := by
    unfold weightedExtractionProbability
    rw [Finset.sum_comm, Finset.sum_div, Fintype.card_prod, Nat.cast_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← div_div, ← Finset.sum_div, ← Finset.mul_sum]
    congr 3
    simp only [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product,
      A, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_sum]
    rw [Finset.sum_comm]
  have h2 : weightedExtractionProbability f q U =
      (∑ t, ∑ y ∈ A t, q y) / Fintype.card T := by
    unfold weightedExtractionProbability
    rw [← Finset.sum_div]
    congr 1
    simp_rw [A, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split <;> simp
  have ht' : 0 < (Fintype.card T : ℝ) := by exact_mod_cast ht
  have hb : weightedExtractionProbability (fun x (s : S × T) => f (c x s.1) s.2) p U -
      weightedExtractionProbability f q U ≤ γ := by
    rw [h1,h2,← sub_div]
    exact (div_le_iff₀ ht').mpr (by simpa [mul_comm] using hsum)
  have he := hf U
  linarith

/-- The low-entropy stage spends a short condenser seed and a Toeplitz seed of
length compressed width plus extracted payload width. -/
def lowSeed (a loss w K : ℕ) : ℕ :=
  a*w.size + (2*(K+a*w.size)+(K+a*w.size-loss))

theorem lowSeed_le {a loss w K B : ℕ} (hw : 1 ≤ w) (hK : K ≤ B*w.size^3) :
    lowSeed a loss w K ≤ (3*B+4*a)*w.size^3 := by
  have hs : 1 ≤ w.size := Nat.size_pos.mpr hw
  have hp : w.size ≤ w.size^3 := by
    calc
      _ = w.size*1 := (Nat.mul_one _).symm
      _ ≤ w.size*(w.size*w.size) := Nat.mul_le_mul_left _ (by
        exact Nat.mul_pos hs hs)
      _ = _ := by ring
  have ha := Nat.mul_le_mul_left (4*a) hp
  unfold lowSeed
  rw [Nat.add_mul]
  nlinarith [Nat.sub_le (K+a*w.size) loss]

/-- The evaluator first condenses, then outputs the second seed and its hashed payload.
Below the constant loss, it outputs the required bits of the original uniform seed. -/
def lowEvaluator (a loss : ℕ) (cond : ExtractorInput → ℕ) : ExtractorInput → ℕ :=
  fun (w,K,d,x,y) =>
    let K := min K w
    let s := a*w.size
    let W := 2*(K+s)
    let M := K+s-loss
    if K+s < loss then y else
      let z := y % 2^(d-s)
      let v := cond (w,K,s,x,y/2^(d-s)) % 2^W
      z*2^M + Toeplitz.eval (W,M,v,z) % 2^M

private theorem size_u {α : Type} {input : α ↪ List Bool} {v : α → ℕ}
    (h : ComputableTidilyInPolyTime v input encUnary) :
    ComputableTidilyInPolyTime (fun x => (v x).size) input encUnary :=
  ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp h)

theorem lowEvaluator_polytime (a loss : ℕ) (cond : ExtractorInput → ℕ)
    (hc : ComputableInPolyTime cond encExtractorInput encNat) :
    ComputableInPolyTime (lowEvaluator a loss cond) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let w := fun p : ExtractorInput => p.1
  let K := fun p : ExtractorInput => min p.2.1 p.1
  let d := fun p : ExtractorInput => p.2.2.1
  let x := fun p : ExtractorInput => p.2.2.2.1
  let y := fun p : ExtractorInput => p.2.2.2.2
  let s := fun p => a*(w p).size
  let W := fun p => 2*(K p+s p)
  let M := fun p => K p+s p-loss
  let base := fun p => (2:ℕ)^(d p-s p)
  let z := fun p => y p % base p
  let v := fun p => cond (w p,K p,s p,x p,y p/base p) % 2^(W p)
  have hw : ComputableTidilyInPolyTime w encExtractorInput encUnary := fst _ _
  have hKRaw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1)
      encExtractorInput encNat := (snd _ _).fst'
  have hK : ComputableTidilyInPolyTime K encExtractorInput encUnary := by
    simpa only [K, min_comm] using
      (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime hKRaw.computableInPolyTime).tidy
  have hd : ComputableTidilyInPolyTime d encExtractorInput encUnary := (snd _ _).snd'.fst'
  have hx : ComputableTidilyInPolyTime x encExtractorInput encNat := (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime y encExtractorInput encNat := (snd _ _).snd'.snd'.snd'
  have hs : ComputableTidilyInPolyTime s encExtractorInput encUnary :=
    unary_mul.comp ((const a).prod (size_u hw))
  have hsum := unary_add.comp (hK.prod hs)
  have hW : ComputableTidilyInPolyTime W encExtractorInput encUnary :=
    unary_mul.comp ((const 2).prod hsum)
  have hM : ComputableTidilyInPolyTime M encExtractorInput encUnary :=
    unary_sub.comp (hsum.prod (const loss))
  have hp := binary_two_pow.comp hM
  have hbase : ComputableTidilyInPolyTime base encExtractorInput encNat :=
    binary_two_pow.comp (unary_sub.comp (hd.prod hs))
  have hz : ComputableTidilyInPolyTime z encExtractorInput encNat := binary_mod' hy hbase
  have hv : ComputableTidilyInPolyTime v encExtractorInput encNat :=
    binary_mod' (hc.tidy.comp (hw.prod ((unary_to_binary.comp hK).prod
      (hs.prod (hx.prod (binary_div' hy hbase)))))) (binary_two_pow.comp hW)
  have hvalue := binary_add' (binary_mul' hz hp)
    (binary_mod' (Toeplitz.eval_polytime.tidy.comp (hW.prod (hM.prod (hv.prod hz)))) hp)
  have htest := unary_lt' hsum (const loss)
  convert htest.ite' hy hvalue using 1
  funext zz
  rcases zz with ⟨w₀,K₀,d₀,x₀,y₀⟩
  simp [lowEvaluator, K, d, w, x, y, s, W, M, base, z, v]


theorem lowSeed_polytime (a loss : ℕ) :
    ComputableInPolyTime (fun z : ℕ × ℕ => lowSeed a loss z.1 (min z.2 z.1))
      (encPair encUnary encNat) encUnary := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let input := encPair encUnary encNat
  have hw := fst encUnary encNat
  have hK : ComputableTidilyInPolyTime (fun z : ℕ × ℕ => min z.2 z.1) input encUnary := by
    simpa only [min_comm] using (ComputableInPolyTime.binary_min_unary'
      hw.computableInPolyTime (snd encUnary encNat).computableInPolyTime).tidy
  have hs := unary_mul.comp ((const a).prod (size_u hw))
  have hsum := unary_add.comp (hK.prod hs)
  have hW := unary_mul.comp ((const 2).prod hsum)
  have hM := unary_sub.comp (hsum.prod (const loss))
  exact unary_add.comp (hs.prod (unary_add.comp (hW.prod hM)))

/-- At the exact seed schedule the compressed output retains its hash seed.
For inputs too small for the target loss, a uniform seed projection suffices. -/
theorem lowEvaluator_extracts (a loss : ℕ) (cond : ExtractorInput → ℕ) {γ ε : ℝ}
    (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hLoss : 1/(2:ℝ)^loss ≤ ε^2)
    {w K : ℕ} (hKw : K ≤ w) (p : Fin (2^w) → ℝ) (hp : ∑ x, p x = 1)
    (hcond : ∃ q : Fin (2^(2*(K+a*w.size))) → ℝ, (∑ y, q y) = 1 ∧
      (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^(K+a*w.size)) ∧
      WeightedCondenses (fixedOutput cond w K (a*w.size) (2*(K+a*w.size))) p q γ) :
    WeightedExtractorEvents (extractorEdge (lowEvaluator a loss cond) loss w K (lowSeed a loss w K))
      p (γ+ε) := by
  classical
  let s := a*w.size
  let W := 2*(K+s)
  let M := K+s-loss
  let h := W+M
  let d := s+h
  by_cases hsm : K+s < loss
  · have hs : K+d-loss ≤ d := by omega
    have he : extractorEdge (lowEvaluator a loss cond) loss w K d =
        (fun (_ : Fin (2^w)) (y : Fin (2^d)) =>
          ⟨y.val % 2^(K+d-loss), Nat.mod_lt _ (Nat.pow_pos (by decide))⟩) := by
      funext x y
      apply Fin.ext
      simp [extractorEdge, lowEvaluator, min_eq_left hKw, hsm, s]
    change WeightedExtractorEvents (extractorEdge (lowEvaluator a loss cond) loss w K d) p (γ+ε)
    rw [he]
    exact weighted_drop_initial_seed_bits hs p hp (add_nonneg hγ hε)
  · have hbig : loss ≤ K+s := by omega
    have hout : h+M = K+d-loss := by omega
    obtain ⟨q,hq,hcap,hcond⟩ := hcond
    let c := fixedOutput cond w K s W
    let f := fun (v : Fin (2^W)) (z : Fin (2^h)) => (z, Toeplitz.edge (m := M) v z)
    have herr : (2:ℝ)^M*(1/(2:ℝ)^(K+s)) ≤ ε^2 := by
      have hwidth : K+s = M+loss := by omega
      have hpow : (2:ℝ)^(K+s) = (2:ℝ)^M * (2:ℝ)^loss := by rw [hwidth,pow_add]
      rw [hpow, mul_one_div]
      have hEq : (2:ℝ)^M / ((2:ℝ)^M * (2:ℝ)^loss) = 1/(2:ℝ)^loss := by
        field_simp
      rwa [hEq]
    have hf : WeightedExtractorEvents f q ε := Toeplitz.edge_extracts q hq hcap hε herr
    have hh := weighted_condense_then_extract c f p q (by simp) hcond hf
    let e := paddedSeedEquiv s h
    let eo : ((Fin (2^h) × Fin (2^M))) ≃ Fin (2^(K+d-loss)) :=
      (paddedOutputEquiv h M).trans (finCongr (congrArg (fun n : ℕ => 2^n) hout))
    have he := equiv_weighted_event _ p (γ+ε) e eo hh
    change WeightedExtractorEvents (extractorEdge (lowEvaluator a loss cond) loss w K d) p (γ+ε)
    convert he using 2
    rename_i x
    funext y
    apply Fin.ext
    let t := e y
    have ht0 : t.1.val = y.val / 2^h := rfl
    have ht1 : t.2.val = y.val % 2^h := rfl
    let z := f (c x t.1) t.2
    have hz : z.1.val*2^M+z.2.val < 2^(K+d-loss) := by
      conv_rhs => rw [← hout,pow_add]
      calc
        _ < z.1.val*2^M+2^M := Nat.add_lt_add_left z.2.isLt _
        _ = (z.1.val+1)*2^M := by rw [Nat.add_mul,Nat.one_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt z.1.isLt)
    have hEval : lowEvaluator a loss cond (w,K,d,x.val,y.val) = z.1.val*2^M+z.2.val := by
      have hds : d - s = h := by omega
      unfold z f c
      unfold lowEvaluator
      simp only [min_eq_left hKw]
      change (if K+s<loss then y.val else
          let zz := y.val % 2^(d-s)
          let v := cond (w,K,s,x.val,y.val/2^(d-s)) % 2^W
          zz*2^M + Toeplitz.eval (W,M,v,zz) % 2^M) = _
      simp only [if_neg hsm,hds,Toeplitz.edge,fixedOutput,ht0,ht1]
    change lowEvaluator a loss cond (w,K,d,x.val,y.val) % 2^(K+d-loss) =
      z.2.val + 2^M*z.1.val
    rw [hEval,Nat.mod_eq_of_lt hz]
    ac_rfl

/-- A condenser followed by binary diagonal hashing gives a weak near-full extractor,
with a seed linear in input entropy and logarithmic in the original width. -/
theorem lowExtractor_of_guv {γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (loss : ℕ) (hLoss : 1/(2:ℝ)^loss ≤ ε^2) (hGUV : HasShortLosslessCondenser γ) :
    ∃ (a : ℕ) (ext : ExtractorInput → ℕ), 0 < a ∧ ComputableInPolyTime ext encExtractorInput encNat ∧
      ∀ w K : ℕ, 1 ≤ w → K ≤ w → ∀ p : Fin (2^w) → ℝ, (∑ x, p x = 1) →
        (∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K) →
        WeightedExtractorEvents (extractorEdge ext loss w K (lowSeed a loss w K)) p (γ+ε) := by
  obtain ⟨a,cond,ha,hc,hcond⟩ := hGUV.weighted
  refine ⟨a,lowEvaluator a loss cond,ha,lowEvaluator_polytime a loss cond hc,?_⟩
  intro w K hw hK p hp hcap
  exact lowEvaluator_extracts a loss cond hγ hε hLoss hK p hp (hcond w K hw hK p hp hcap)


/-- Add a constant reserve of fresh bits so the output-width subtraction never
truncates on the actual schedule. -/
def lowPaddedSeed (a loss w K : ℕ) : ℕ :=
  lowSeed a loss w K + loss

theorem le_lowPaddedSeed {a loss w K : ℕ} : loss ≤ lowPaddedSeed a loss w K := by
  unfold lowPaddedSeed
  omega

theorem lowPaddedSeed_le {a loss w K B : ℕ} (hw : 1 ≤ w) (hK : K ≤ B*w.size^3) :
    lowPaddedSeed a loss w K ≤ (3*B+4*a+loss)*w.size^3 := by
  unfold lowPaddedSeed
  rw [Nat.add_mul]
  apply Nat.add_le_add (lowSeed_le hw hK)
  have hs : 1 ≤ w.size^3 := Nat.pow_pos (Nat.size_pos.mpr hw)
  exact Nat.le_mul_of_pos_right loss hs

theorem lowPaddedSeed_polytime (a loss : ℕ) :
    ComputableInPolyTime (fun z : ℕ × ℕ => lowPaddedSeed a loss z.1 (min z.2 z.1))
      (encPair encUnary encNat) encUnary :=
  (unary_add.comp ((lowSeed_polytime a loss).tidy.prod (const loss))).computableInPolyTime

/-- The low-entropy evaluator can pad its seed by fresh low bits. The exceptional
branch is uniform by direct projection whenever the original seed was too short. -/
def lowPaddedEvaluator (_a loss : ℕ) (ext : ExtractorInput → ℕ) : ExtractorInput → ℕ :=
  fun (w,K,d,x,y) =>
    let K := min K w
    let d₀ := d-loss
    if K+d₀ < loss then y else
      let r := 2^loss
      let z := ext (w,K,d₀,x,y/r) % 2^(K+d₀-loss)
      z*r+y%r

theorem lowPaddedEvaluator_polytime (a loss : ℕ) (ext : ExtractorInput → ℕ)
    (hExt : ComputableInPolyTime ext encExtractorInput encNat) :
    ComputableInPolyTime (lowPaddedEvaluator a loss ext) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let w := fun p : ExtractorInput => p.1
  let K := fun p : ExtractorInput => min p.2.1 p.1
  let d₀ := fun p : ExtractorInput => p.2.2.1-loss
  let x := fun p : ExtractorInput => p.2.2.2.1
  let y := fun p : ExtractorInput => p.2.2.2.2
  have hw : ComputableTidilyInPolyTime w encExtractorInput encUnary := fst _ _
  have hKRaw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1)
      encExtractorInput encNat := (snd _ _).fst'
  have hK : ComputableTidilyInPolyTime K encExtractorInput encUnary := by
    simpa only [K,min_comm] using (ComputableInPolyTime.binary_min_unary'
      hw.computableInPolyTime hKRaw.computableInPolyTime).tidy
  have hd : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.1)
      encExtractorInput encUnary := (snd _ _).snd'.fst'
  have hd₀ : ComputableTidilyInPolyTime d₀ encExtractorInput encUnary :=
    unary_sub.comp (hd.prod (const loss))
  have hx : ComputableTidilyInPolyTime x encExtractorInput encNat := (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime y encExtractorInput encNat := (snd _ _).snd'.snd'.snd'
  have hsum := unary_add.comp (hK.prod hd₀)
  have hr : ComputableTidilyInPolyTime (fun _ : ExtractorInput => (2:ℕ)^loss)
      encExtractorInput encNat := const _
  have h0 := binary_two_pow.comp (unary_sub.comp (hsum.prod (const loss)))
  have hz := binary_mod' (hExt.tidy.comp (hw.prod ((unary_to_binary.comp hK).prod
    (hd₀.prod (hx.prod (binary_div' hy hr)))))) h0
  have hvalue := binary_add' (binary_mul' hz hr) (binary_mod' hy hr)
  have htest := unary_lt' hsum (const loss)
  convert htest.ite' hy hvalue using 1
  funext zz
  rcases zz with ⟨w₀,K₀,d₁,x₀,y₀⟩
  simp [lowPaddedEvaluator,w,K,d₀,x,y]

theorem lowPadded_extracts (a loss : ℕ) (ext : ExtractorInput → ℕ) {ε : ℝ}
    {w K : ℕ} (hKw : K ≤ w) (p : Fin (2^w) → ℝ) (hp : ∑ x, p x = 1) (hε : 0 ≤ ε)
    (hBase : WeightedExtractorEvents (extractorEdge ext loss w K (lowSeed a loss w K)) p ε) :
    WeightedExtractorEvents
      (extractorEdge (lowPaddedEvaluator a loss ext) loss w K (lowPaddedSeed a loss w K)) p ε := by
  classical
  let d₀ := lowSeed a loss w K
  let d := d₀+loss
  have hd : d-loss = d₀ := Nat.add_sub_cancel d₀ loss
  change WeightedExtractorEvents (extractorEdge (lowPaddedEvaluator a loss ext) loss w K d) p ε
  by_cases hsm : K+d₀ < loss
  · have hs : K+d-loss ≤ d := by omega
    have he : extractorEdge (lowPaddedEvaluator a loss ext) loss w K d =
        (fun (_ : Fin (2^w)) (y : Fin (2^d)) =>
          ⟨y.val % 2^(K+d-loss), Nat.mod_lt _ (Nat.pow_pos (by decide))⟩) := by
      funext x y
      apply Fin.ext
      simp [extractorEdge, lowPaddedEvaluator, min_eq_left hKw, hsm, hd]
    rw [he]
    exact weighted_drop_initial_seed_bits hs p hp hε
  · let m := K+d₀-loss
    have hOut : m+loss = K+d-loss := by omega
    let e := paddedSeedEquiv d₀ loss
    let eo : ((Fin (2^m) × Fin (2^loss))) ≃ Fin (2^(K+d-loss)) :=
      (paddedOutputEquiv m loss).trans (finCongr (congrArg (fun n : ℕ => 2^n) hOut))
    let f := extractorEdge ext loss w K d₀
    have hh := weighted_independent_seed (B := Fin (2^loss)) f p (by simp) hBase
    have he := equiv_weighted_event _ p ε e eo hh
    convert he using 2
    rename_i x
    funext y
    apply Fin.ext
    let t := e y
    have ht0 : t.1.val = y.val / 2^loss := rfl
    have ht1 : t.2.val = y.val % 2^loss := rfl
    let z := f x t.1
    have hz : z.val*2^loss+t.2.val < 2^(K+d-loss) := by
      conv_rhs => rw [← hOut,pow_add]
      calc
        _ < z.val*2^loss+2^loss := Nat.add_lt_add_left t.2.isLt _
        _ = (z.val+1)*2^loss := by rw [Nat.add_mul,Nat.one_mul]
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt z.isLt)
    have hEval : lowPaddedEvaluator a loss ext (w,K,d,x.val,y.val) = z.val*2^loss+t.2.val := by
      unfold z f
      simp [lowPaddedEvaluator,min_eq_left hKw,if_neg hsm,hd,extractorEdge,ht0,ht1]
    change lowPaddedEvaluator a loss ext (w,K,d,x.val,y.val) % 2^(K+d-loss) =
      t.2.val + 2^loss*z.val
    rw [hEval,Nat.mod_eq_of_lt hz]
    ac_rfl

theorem lowPaddedExtractor_of_guv {γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (loss : ℕ) (hLoss : 1/(2:ℝ)^loss ≤ ε^2) (hGUV : HasShortLosslessCondenser γ) :
    ∃ (a : ℕ) (ext : ExtractorInput → ℕ), 0 < a ∧ ComputableInPolyTime ext encExtractorInput encNat ∧
      ∀ w K : ℕ, 1 ≤ w → K ≤ w → ∀ p : Fin (2^w) → ℝ, (∑ x, p x = 1) →
        (∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K) →
        WeightedExtractorEvents (extractorEdge ext loss w K (lowPaddedSeed a loss w K)) p (γ+ε) := by
  obtain ⟨a,ext,ha,hExt,hstat⟩ := lowExtractor_of_guv hγ hε loss hLoss hGUV
  refine ⟨a,lowPaddedEvaluator a loss ext,ha,lowPaddedEvaluator_polytime a loss ext hExt,?_⟩
  intro w K hw hKw p hp hcap
  exact lowPadded_extracts a loss ext hKw p hp (add_nonneg hγ hε) (hstat w K hw hKw p hp hcap)

end TimeSpaceMA.RRV

open scoped BigOperators

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The seed bound is linear in the remaining entropy plus the binary input width. -/
def HasLinearResidualExtractor (ε : ℝ) : Prop :=
  ∃ (a L : ℕ) (low : ExtractorInput → ℕ), 0 < a ∧
    ComputableInPolyTime low encExtractorInput encNat ∧
    ∀ w r : ℕ, 1 ≤ w → r ≤ w →
      ∀ p : Fin (2^w) → ℝ, (∑ x, p x = 1) →
        (∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^r) →
        let s := a*w.size
        let M := r+s-L
        let d := s+(2*(r+s)+M)+L
        WeightedExtractorEvents (extractorEdge low L w r d) p ε

def recoverySeed (B a L w K : ℕ) : ℕ :=
  let d := B*w.size^3
  let r := K-(K-d)-1
  let s := a*w.size
  d + (s+(2*(r+s)+(r+s-L))+L)

def recoverNative (B a L : ℕ) (first low : ExtractorInput → ℕ) : ExtractorInput → ℕ :=
  fun (w,K,_,x,y) =>
    let K := min K w
    let d₁ := B*w.size^3
    let m := K-d₁
    let r := K-m-1
    let s := a*w.size
    let d₂ := s+(2*(r+s)+(r+s-L))+L
    let o := r+d₂-L
    let y₁ := y/2^d₂
    let y₂ := y%2^d₂
    let v₁ := first (w,K,d₁,x,y₁) % 2^m
    let v₂ := low (w,r,d₂,x,y₂) % 2^o
    (y₁*2^m+v₁)*2^o+v₂

private theorem recoveryWidths {α : Type} {input : α ↪ List Bool} {w K : α → ℕ}
    (B a L : ℕ)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hK : ComputableTidilyInPolyTime K input encUnary) :
    let d₁ (z : α) := B*(w z).size^3
    let m (z : α) := K z-d₁ z
    let r (z : α) := K z-m z-1
    let s (z : α) := a*(w z).size
    let d₂ (z : α) := s z+(2*(r z+s z)+(r z+s z-L))+L
    ComputableTidilyInPolyTime d₁ input encUnary ∧
    ComputableTidilyInPolyTime m input encUnary ∧
    ComputableTidilyInPolyTime r input encUnary ∧
    ComputableTidilyInPolyTime d₂ input encUnary := by
  have hb := ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hw)
  have hd := unary_mul.comp ((const B).prod ((unary_pow 3).comp hb))
  have hm := unary_sub.comp (hK.prod hd)
  have hr := unary_sub.comp ((unary_sub.comp (hK.prod hm)).prod (const 1))
  have hs := unary_mul.comp ((const a).prod hb)
  have hT := unary_add.comp (hr.prod hs)
  have hM := unary_sub.comp (hT.prod (const L))
  exact ⟨hd,hm,hr,unary_add.comp ((unary_add.comp (hs.prod (unary_add.comp
    ((unary_mul.comp ((const 2).prod hT)).prod hM)))).prod (const L))⟩

private theorem recoverySeed_polytime (B a L : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ℕ => recoverySeed B a L p.1 (min p.2 p.1))
      (encPair encUnary encNat) encUnary := by
  have hw := fst encUnary encNat
  have hk := (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime
    (snd encUnary encNat).computableInPolyTime).tidy
  obtain ⟨h₁,_,_,h₂⟩ := recoveryWidths B a L hw hk
  have hh := (unary_add.comp (h₁.prod h₂)).computableInPolyTime
  convert hh using 1
  funext p
  simp [recoverySeed,min_comm]

private theorem recoverNative_polytime (B a L : ℕ) (first low : ExtractorInput → ℕ)
    (hFirst : ComputableInPolyTime first encExtractorInput encNat)
    (hLow : ComputableInPolyTime low encExtractorInput encNat) :
    ComputableInPolyTime (recoverNative B a L first low) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let E := encExtractorInput
  have hw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.1) E encUnary := fst _ _
  have hk0 : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1) E encNat := (snd _ _).fst'
  have hk := (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime hk0.computableInPolyTime).tidy
  have hx : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.1) E encNat :=
    (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.2) E encNat :=
    (snd _ _).snd'.snd'.snd'
  obtain ⟨h₁,hm,hr,h₂⟩ := recoveryWidths B a L hw hk
  have hpow₂ := binary_two_pow.comp h₂
  have hy₁ := binary_div' hy hpow₂
  have hy₂ := binary_mod' hy hpow₂
  have hpowM := binary_two_pow.comp hm
  have hpowO := binary_two_pow.comp (unary_sub.comp ((unary_add.comp (hr.prod h₂)).prod (const L)))
  have hv₁ := binary_mod' (hFirst.tidy.comp (hw.prod ((unary_to_binary.comp hk).prod
    (h₁.prod (hx.prod hy₁))))) hpowM
  have hv₂ := binary_mod' (hLow.tidy.comp (hw.prod ((unary_to_binary.comp hr).prod
    (h₂.prod (hx.prod hy₂))))) hpowO
  have ho := binary_add' (binary_mul' (binary_add' (binary_mul' hy₁ hpowM) hv₁) hpowO) hv₂
  convert ho using 1
  funext p
  rcases p with ⟨w,K,d,x,y⟩
  simp [recoverNative,min_comm]

private theorem residual_cap {K m : ℕ} (h : m+1 ≤ K) :
    (1/(2:ℝ)^K)*(2*(Fintype.card (Fin (2^m)) : ℝ)) = 1/2^(K-m-1) := by
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have he : K = (K-m-1)+(m+1) := by omega
  conv_lhs => rw [he, pow_add, pow_succ]
  field_simp
  <;> ring

set_option maxHeartbeats 800000 in
theorem recoverNative_events {ε δ : ℝ} {B a L : ℕ} (first low : ExtractorInput → ℕ)
    {w K : ℕ} (hKw : K ≤ w) (hKL : L+1 ≤ K)
    (ha : 0 < a) (hB : 0 < B) (hw : 1 ≤ w) (hδ : 0 ≤ δ)
    (p : Fin (2^w) → ℝ) (hP : ∑ x, p x = 1)
    (hcap : ∀ x, 0 ≤ p x ∧ p x ≤ 1/(2:ℝ)^K)
    (hf : WeightedExtractorEvents (fun x s =>
      (s,fixedOutput first w K (B*w.size^3) (K-B*w.size^3) x s)) p ε)
    (hl : let d₁ := B*w.size^3
      let r := K-(K-d₁)-1
      let s := a*w.size
      let d₂ := s+(2*(r+s)+(r+s-L))+L
      ∀ q : Fin (2^w) → ℝ, (∑ x, q x = 1) →
        (∀ x, 0 ≤ q x ∧ q x ≤ 1/(2:ℝ)^r) →
        WeightedExtractorEvents (extractorEdge low L w r d₂) q δ) :
    WeightedExtractorEvents
      (extractorEdge (recoverNative B a L first low) (L+1) w K (recoverySeed B a L w K))
      p (2*ε+δ) := by
  let d₁ := B*w.size^3
  let m := K-d₁
  let r := K-m-1
  let s := a*w.size
  let d₂ := s+(2*(r+s)+(r+s-L))+L
  let o := r+d₂-L
  have hd₁ : 0 < d₁ := Nat.mul_pos hB (Nat.pow_pos (Nat.size_pos.mpr hw))
  have hmr : m+1 ≤ K := by unfold m; omega
  have hod : L ≤ r+d₂ := by unfold d₂; omega
  let eIn := paddedSeedEquiv d₁ d₂
  have hwidth : (d₁+m)+o = K+(d₁+d₂)-(L+1) := by
    dsimp only [o,r] at *
    omega
  let eOut : ((Fin (2^d₁) × Fin (2^m)) × Fin (2^o)) ≃ Fin (2^(K+(d₁+d₂)-(L+1))) :=
    ((Equiv.prodCongr (paddedOutputEquiv d₁ m) (Equiv.refl (Fin (2^o)))).trans
      (paddedOutputEquiv (d₁+m) o)).trans (finCongr (congrArg (2^·) hwidth))
  let f := fixedOutput first w K d₁ m
  let g := extractorEdge low L w r d₂
  have hj := compose_weak_event f g (fun x => (hcap x).1) hP (by positivity)
    (fun x => (hcap x).2) hδ (by simp) (by simp) (by simp) (by simp) hf (by
      intro q hq hc
      apply hl q hq
      have hR : (1/(2:ℝ)^K)*(2*(Fintype.card (Fin (2^m)) : ℝ)) = 1/2^r := residual_cap hmr
      rw [hR] at hc
      exact hc)
  have hs := equiv_weighted_event _ p (2*ε+δ) eIn eOut hj
  change WeightedExtractorEvents
    (extractorEdge (recoverNative B a L first low) (L+1) w K (d₁+d₂)) p (2*ε+δ)
  convert hs using 2
  rename_i x
  funext y
  apply Fin.ext
  let s₁ := (eIn y).1
  let s₂ := (eIn y).2
  have H := (eOut ((s₁,f x s₁),g x s₂)).isLt
  change (g x s₂).val + 2^o*((f x s₁).val + 2^m*s₁.val) < _ at H
  let out := (s₁.val*2^m+(f x s₁).val)*2^o+(g x s₂).val
  have hgo : out < 2^(K+(d₁+d₂)-(L+1)) := by
    have hEq : out = (g x s₂).val + 2^o*((f x s₁).val + 2^m*s₁.val) := by
      unfold out
      ac_rfl
    exact hEq.symm ▸ H
  have h1 : s₁.val = y.val / 2^d₂ := rfl
  have h2 : s₂.val = y.val % 2^d₂ := rfl
  change recoverNative B a L first low (w,K,d₁+d₂,x.val,y.val) % _ =
    (g x s₂).val + 2^o*((f x s₁).val + 2^m*s₁.val)
  have he : recoverNative B a L first low (w,K,d₁+d₂,x.val,y.val) = out := by
    unfold out f g fixedOutput extractorEdge recoverNative
    simp only [min_eq_left hKw,h1,h2,d₁,m,r,s,d₂,o]
  rw [he,Nat.mod_eq_of_lt hgo]
  unfold out
  ac_rfl

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Extend a weak extractor from its native computable schedule, with independent spare bits.
The entropy thresholds smaller than the fixed loss can be served by projecting the seed. -/
def padWeak (L : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ) : ExtractorInput → ℕ :=
  fun (w,k,d,x,y) =>
    let k := min k w
    if k < L then y else
      let r := schedule (w,k)
      let b := 2^(d-r)
      let o := k+r-L
      let u := base (w,k,r,x,y/b) % 2^o
      u*b+y%b

private theorem padWeak_polytime (L : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ)
    (hSchedule : ComputableInPolyTime schedule (encPair encUnary encNat) encUnary)
    (hBase : ComputableInPolyTime base encExtractorInput encNat) :
    ComputableInPolyTime (padWeak L schedule base) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let input := encExtractorInput
  have hw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.1) input encUnary := fst _ _
  have hKRaw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1) input encNat := (snd _ _).fst'
  have hK := (ComputableInPolyTime.binary_min_unary' hw.computableInPolyTime
    hKRaw.computableInPolyTime).tidy
  have hd : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.1) input encUnary :=
    (snd _ _).snd'.fst'
  have hx : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.1) input encNat :=
    (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.2) input encNat :=
    (snd _ _).snd'.snd'.snd'
  have hr := hSchedule.tidy.comp (hw.prod (unary_to_binary.comp hK))
  have hb := binary_two_pow.comp (unary_sub.comp (hd.prod hr))
  have ho := binary_two_pow.comp (unary_sub.comp ((unary_add.comp (hK.prod hr)).prod (const L)))
  have hu := binary_mod' (hBase.tidy.comp (hw.prod ((unary_to_binary.comp hK).prod
    (hr.prod (hx.prod (binary_div' hy hb)))))) ho
  have h := (unary_lt' hK (const L)).ite' hy (binary_add' (binary_mul' hu hb) (binary_mod' hy hb))
  convert h using 1
  funext z
  rcases z with ⟨w,k,d,x,y⟩
  simp [padWeak,min_comm]

set_option maxHeartbeats 800000 in
private theorem padWeak_events {ε : ℝ} (L : ℕ) (schedule : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ)
    {w k d : ℕ} (hKw : k ≤ w) (hD : L ≤ d) (hr : schedule (w,k) ≤ d)
    (p : Fin (2^w) → ℝ) (hP : ∑ x, p x = 1) (hε : 0 ≤ ε)
    (h : L ≤ k →
      WeightedExtractorEvents (extractorEdge base L w k (schedule (w,k))) p ε) :
    WeightedExtractorEvents (extractorEdge (padWeak L schedule base) L w k d) p ε := by
  by_cases hs : k < L
  · have he : extractorEdge (padWeak L schedule base) L w k d =
        (fun (_ : Fin (2^w)) (y : Fin (2^d)) =>
          ⟨y.val % 2^(k+d-L), Nat.mod_lt _ (Nat.pow_pos (by decide))⟩) := by
      funext x y
      apply Fin.ext
      simp [padWeak,extractorEdge,min_eq_left hKw,hs]
    rw [he]
    exact weighted_drop_initial_seed_bits (by omega) p hP hε
  · have hKL := Nat.le_of_not_gt hs
    let r := schedule (w,k)
    let b := d-r
    let o := k+r-L
    have hIn : r+b = d := Nat.add_sub_of_le hr
    have hOut : o+b = k+d-L := by unfold o b; omega
    let e : Fin (2^d) ≃ Fin (2^r) × Fin (2^b) :=
      (finCongr (congrArg (fun n : ℕ => 2^n) hIn.symm)).trans (paddedSeedEquiv r b)
    let eo : Fin (2^o) × Fin (2^b) ≃ Fin (2^(k+d-L)) :=
      (paddedOutputEquiv o b).trans (finCongr (congrArg (fun n : ℕ => 2^n) hOut))
    let f := extractorEdge base L w k r
    have hpad := weighted_independent_seed (B := Fin (2^b)) f p (by simp) (h hKL)
    have hh := equiv_weighted_event _ p ε e eo hpad
    convert hh using 2
    rename_i x
    funext y
    apply Fin.ext
    let t := e y
    have H := (eo (f x t.1,t.2)).isLt
    change t.2.val+2^b*(f x t.1).val < _ at H
    have h1 : t.1.val = y.val / 2^b := rfl
    have h2 : t.2.val = y.val % 2^b := rfl
    change padWeak L schedule base (w,k,d,x.val,y.val) % 2^(k+d-L) =
      t.2.val+2^b*(f x t.1).val
    have he : padWeak L schedule base (w,k,d,x.val,y.val) = t.2.val+2^b*(f x t.1).val := by
      simp only [padWeak,min_eq_left hKw,if_neg hs,h1,h2,f,extractorEdge,b,r,o]
      ac_rfl
    rw [he,Nat.mod_eq_of_lt H]

theorem hasPolylogConstantLossExtractor_of_recovery
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hFirst : HasNearFullStrongExtractor ε) (hLow : HasLinearResidualExtractor δ) :
    HasPolylogConstantLossExtractor (2*ε+δ) := by
  obtain ⟨B,first,hB,hFirst,hStrong⟩ := hFirst
  obtain ⟨a,L,low,ha,hLow,hWeak⟩ := hLow
  let schedule (p : ℕ × ℕ) := recoverySeed B a L p.1 (min p.2 p.1)
  let eval := recoverNative B a L first low
  let C := B+(3*B+4*a+L)
  let loss := L+1
  refine ⟨C,loss,padWeak loss schedule eval,by unfold C; omega,
    padWeak_polytime loss schedule eval (recoverySeed_polytime B a L)
      (recoverNative_polytime B a L first low hFirst hLow),?_⟩
  intro w K hw hKw d p hP hcap
  have hSize : 1 ≤ w.size^3 := Nat.pow_pos (Nat.size_pos.mpr hw)
  have hLog : w.size ≤ w.size^3 := by
    simpa using Nat.pow_le_pow_right (Nat.size_pos.mpr hw) (by decide : 1 ≤ 3)
  let d₁ := B*w.size^3
  let m := K-d₁
  let r := K-m-1
  let s := a*w.size
  let d₂ := s+(2*(r+s)+(r+s-L))+L
  have hrd : r ≤ d₁ := by unfold r m; omega
  have hs : s ≤ a*w.size^3 := Nat.mul_le_mul_left _ hLog
  have hL : L ≤ L*w.size^3 := by simpa using Nat.mul_le_mul_left L hSize
  have bound : schedule (w,K) ≤ C*w.size^3 := by
    change recoverySeed B a L w (min K w) ≤ _
    rw [min_eq_left hKw]
    change d₁+d₂ ≤ _
    unfold C d₂
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,Nat.mul_assoc,Nat.mul_assoc]
    unfold d₁ at hrd ⊢
    omega
  apply padWeak_events loss schedule eval hKw (by omega)
    (bound.trans (Nat.le_add_right _ _)) p hP (by linarith)
  intro hK
  have hRun := recoverNative_events first low hKw hK ha hB hw hδ p hP hcap
    (hStrong w K hw hKw p hP hcap) (hWeak w r hw (by unfold r; omega))
  have hD : schedule (w,K) = recoverySeed B a L w K := by simp [schedule,min_eq_left hKw]
  rw [hD]
  exact hRun

end TimeSpaceMA.RRV

namespace TimeSpaceMA.RRV

open Turing.MultiTapeTM

private theorem loss_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 1/(2:ℝ)^L ≤ ε^2 := by
  obtain ⟨L,hL⟩ := exists_nat_ge (1/(ε^2))
  have hP : 0 < ε^2 := sq_pos_of_pos hε
  refine ⟨L,(div_le_iff₀ (by positivity)).2 ?_⟩
  have h := (div_le_iff₀ hP).mp hL
  have hPow : (L : ℝ) ≤ (2:ℝ)^L := by
    exact_mod_cast (Nat.lt_two_pow_self (n := L)).le
  simpa only [mul_comm (ε^2)] using h.trans (mul_le_mul_of_nonneg_right hPow hP.le)

theorem constantLoss_of_nearFull_and_guv (δ : ℝ) (hδ : 0 < δ)
    (hFirst : HasNearFullStrongExtractor (δ/4))
    (hGUV : HasShortLosslessCondenser (δ/4)) :
    HasPolylogConstantLossExtractor δ := by
  have hp : 0 < δ/4 := by linarith
  obtain ⟨L,hL⟩ := loss_exists (δ/4) hp
  obtain ⟨a,low,ha,hP,hstat⟩ := lowPaddedExtractor_of_guv hp.le hp.le L hL hGUV
  have hLow : HasLinearResidualExtractor (δ/4+δ/4) :=
    ⟨a,L,low,ha,hP,hstat⟩
  rw [show δ = 2*(δ/4)+(δ/4+δ/4) by ring]
  exact hasPolylogConstantLossExtractor_of_recovery hp.le (add_nonneg hp.le hp.le) hFirst hLow

end TimeSpaceMA.RRV

open TimeSpaceMA TimeSpaceMA.RRV

theorem solution (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1/8) :
    HasPolylogConstantLossExtractor δ := by
  have h0 : 0 < δ/4 := by linarith
  have h1 : δ/4 ≤ (1:ℝ)/32 := by linarith
  have h2 : δ/4 ≤ (1:ℝ)/8 := by linarith
  exact constantLoss_of_nearFull_and_guv δ hδ (nearFullStrongExtractor _ h0 h1)
    (shortLosslessCondenser _ h0 h2)
