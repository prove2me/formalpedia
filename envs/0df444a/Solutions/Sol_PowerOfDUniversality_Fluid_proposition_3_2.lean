-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:03:39.408314+00:00
-- url     : https://prove2.me/submissions/efd088d3-79b8-4b67-bc7a-a0a6f258425e

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace
import Theorems.Thm_PowerOfDUniversality_Fluid_proposition_3_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Prop32Aux

open PowerOfDUniversality.Fluid

lemma le_level_iff (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) (i : ℕ) :
    i ≤ level N Q c ↔ N + 1 ≤ Q i + c := by
  obtain ⟨h0, hanti, _⟩ := hQ
  constructor
  · intro hi
    have hne : (Q.support.filter (fun i => N + 1 ≤ Q i + c)).Nonempty := by
      refine ⟨0, ?_⟩
      rw [Finset.mem_filter, Finsupp.mem_support_iff, h0]
      omega
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [Finset.mem_filter] at hj
    have hl : level N Q c = j := hjeq
    have := hanti (show i ≤ j by omega)
    omega
  · intro hi
    apply Finset.le_sup (f := id)
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    exact ⟨by omega, hi⟩

lemma level_le_b (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (Q : ℕ →₀ ℕ) (hQ : IsOccupancy N b Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : ((level N Q c : ℕ) : ℕ∞) ≤ b := by
  by_contra h
  push Not at h
  have h1 := (le_level_iff N hN b Q hQ c hc1 hcN (level N Q c)).mp le_rfl
  have h2 := hQ.2.2 _ h
  omega

lemma add_apply (N : ℕ) (b : ℕ∞) (c : ℕ) (x : Ensemble) (i : ℕ) :
    (addItem N b c x).Q i = x.Q i +
      (if ((level N x.Q c : ℕ) : ℕ∞) < b ∧ i = level N x.Q c + 1 then 1 else 0) := by
  unfold addItem
  by_cases h : ((level N x.Q c : ℕ) : ℕ∞) < b
  · rw [if_pos h]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    by_cases hi : i = level N x.Q c + 1
    · rw [if_pos hi.symm, if_pos ⟨h, hi⟩]
    · rw [if_neg (fun e => hi e.symm), if_neg (fun e => hi e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]
    simp

lemma remove_apply (N : ℕ) (k : ℕ) (x : Ensemble) (i : ℕ) :
    (removeItem N k x).Q i = x.Q i -
      (if 1 ≤ level N x.Q k ∧ i = level N x.Q k then 1 else 0) := by
  unfold removeItem
  by_cases h : 1 ≤ level N x.Q k
  · rw [if_pos h]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
    by_cases hi : i = level N x.Q k
    · rw [if_pos hi.symm, if_pos ⟨h, hi⟩]
    · rw [if_neg (fun e => hi e.symm), if_neg (fun e => hi e.2)]
  · rw [if_neg h, if_neg (fun e => h e.1)]
    simp

lemma occ_add (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x : Ensemble) (hx : IsOccupancy N b x.Q)
    (c : ℕ) (hc1 : 1 ≤ c) (hcN : c ≤ N) : IsOccupancy N b (addItem N b c x).Q := by
  obtain ⟨I, hI⟩ : ∃ I, level N x.Q c = I := ⟨_, rfl⟩
  have hl := le_level_iff N hN b x.Q hx c hc1 hcN
  have f1 := (hl I).mp (le_of_eq hI.symm)
  have f2 : ¬ N + 1 ≤ x.Q (I + 1) + c := fun h => by have := (hl (I + 1)).mpr h; omega
  obtain ⟨h0, hanti, hzero⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [add_apply, hI, h0]; simp
  · intro i j hij
    show (addItem N b c x).Q j ≤ (addItem N b c x).Q i
    rw [add_apply, add_apply, hI]
    have := hanti hij
    by_cases hj : j = I + 1
    · subst hj
      by_cases hi : i = I + 1
      · subst hi; exact le_rfl
      · have : x.Q I ≤ x.Q i := hanti (by omega)
        split_ifs <;> omega
    · by_cases hi : i = I + 1
      · split_ifs <;> omega
      · split_ifs <;> omega
  · intro i hi
    rw [add_apply, hI, hzero i hi]
    rw [if_neg]
    rintro ⟨h1, rfl⟩
    have : ((I : ℕ∞) + 1) ≤ b := Order.add_one_le_of_lt h1
    push_cast at hi
    exact absurd (lt_of_le_of_lt this hi) (lt_irrefl _)

lemma occ_remove (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (x : Ensemble) (hx : IsOccupancy N b x.Q)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) : IsOccupancy N b (removeItem N k x).Q := by
  obtain ⟨I, hI⟩ : ∃ I, level N x.Q k = I := ⟨_, rfl⟩
  have hl := le_level_iff N hN b x.Q hx k hk1 hkN
  have f1 := (hl I).mp (le_of_eq hI.symm)
  have f2 : ¬ N + 1 ≤ x.Q (I + 1) + k := fun h => by have := (hl (I + 1)).mpr h; omega
  obtain ⟨h0, hanti, hzero⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [remove_apply, hI, h0]; split_ifs <;> omega
  · intro i j hij
    show (removeItem N k x).Q j ≤ (removeItem N k x).Q i
    rw [remove_apply, remove_apply, hI]
    have := hanti hij
    by_cases hi : i = I
    · subst hi
      by_cases hj : j = i
      · subst hj; exact le_rfl
      · have : x.Q j ≤ x.Q (i + 1) := hanti (by omega)
        split_ifs <;> omega
    · split_ifs <;> omega
  · intro i hi
    rw [remove_apply, hzero i hi]
    simp

lemma uniformPos_bounds (N : ℕ) (hN : 1 ≤ N) (x : ℝ) : 1 ≤ uniformPos N x ∧ uniformPos N x ≤ N := by
  unfold uniformPos
  exact ⟨le_min (by omega) hN, min_le_right _ _⟩

open Classical in
/-- Under the S-coupling, two systems whose dispatch choices are ordered (`pol₁ ≤ pol₂`
positionwise) and whose initial states are ordered stay ordered as in (3.1) after every event
(iterating Proposition 3.1). -/
lemma ordered_seq (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (pol₁ pol₂ : Scheme)
    (hp₁ : ∀ j Q u, 1 ≤ pol₁ j Q u) (hp₂ : ∀ j Q u, pol₂ j Q u ≤ N)
    (hle : ∀ j Q Q' u, pol₁ j Q u ≤ pol₂ j Q' u)
    (Q₁ Q₂ : ℕ →₀ ℕ) (hQ₁ : IsOccupancy N b Q₁) (hQ₂ : IsOccupancy N b Q₂)
    (h0 : ∀ m : ℕ, 1 ≤ m → tailSum Q₁ m ≤ tailSum Q₂ m) (ξ : ℕ → ℕ → ℝ) (n : ℕ) :
    IsOccupancy N b (eventState N b lam pol₁ Q₁ ξ n).Q ∧
    IsOccupancy N b (eventState N b lam pol₂ Q₂ ξ n).Q ∧
    StackOrdered (eventState N b lam pol₁ Q₁ ξ n) (eventState N b lam pol₂ Q₂ ξ n) := by
  induction n with
  | zero =>
    refine ⟨hQ₁, hQ₂, ?_⟩
    intro m hm
    simp only [eventState]
    have := h0 m hm
    omega
  | succ n ih =>
    obtain ⟨o1, o2, hd⟩ := ih
    set x := eventState N b lam pol₁ Q₁ ξ n with hx
    set y := eventState N b lam pol₂ Q₂ ξ n with hy
    have e1 : eventState N b lam pol₁ Q₁ ξ (n + 1) =
        if IsArrival N lam (ξ (n + 1)) then addItem N b (pol₁ (n + 1) x.Q (ξ (n + 1))) x
        else removeItem N (uniformPos N (ξ (n + 1) 2)) x := by
      simp only [eventState, step, hx]
    have e2 : eventState N b lam pol₂ Q₂ ξ (n + 1) =
        if IsArrival N lam (ξ (n + 1)) then addItem N b (pol₂ (n + 1) y.Q (ξ (n + 1))) y
        else removeItem N (uniformPos N (ξ (n + 1) 2)) y := by
      simp only [eventState, step, hy]
    rw [e1, e2]
    have P31 := proposition_3_1 N hN b hb x y o1 o2 hd
    obtain ⟨u1, u2⟩ := uniformPos_bounds N hN (ξ (n + 1) 2)
    by_cases harr : IsArrival N lam (ξ (n + 1))
    · simp only [harr, if_true]
      have a1 := hp₁ (n + 1) x.Q (ξ (n + 1))
      have a2 := hp₂ (n + 1) y.Q (ξ (n + 1))
      have a3 := hle (n + 1) x.Q y.Q (ξ (n + 1))
      have a4 := hp₁ (n + 1) y.Q (ξ (n + 1))
      have a5 := hp₂ (n + 1) x.Q (ξ (n + 1))
      exact ⟨occ_add N hN b x o1 _ a1 (le_trans a3 a2), occ_add N hN b y o2 _ (le_trans a4 (hle (n + 1) y.Q y.Q (ξ (n + 1)))) a2,
        P31.2 _ _ a1 a3 a2⟩
    · simp only [harr, if_false]
      exact ⟨occ_remove N hN b x o1 _ u1 u2, occ_remove N hN b y o2 _ u1 u2, P31.1 _ u1 u2⟩

/-! ### Measurability of the event recursion -/

instance ensMS : MeasurableSpace Ensemble := ⊤

instance : MeasurableSingletonClass Ensemble := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable Ensemble := by
  have hinj : Function.Injective (fun e : Ensemble => (e.Q, e.L)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  exact hinj.countable

/-- marks as a function of the uncurried array `w : ℕ × ℕ → ℝ`. -/
def mk (w : ℕ × ℕ → ℝ) : ℕ → ℕ → ℝ := fun j r => w (j, r)

lemma measurable_mark (j : ℕ) : Measurable (fun w : ℕ × ℕ → ℝ => mk w j) :=
  measurable_pi_lambda _ (fun r => measurable_pi_apply (j, r))

lemma measurable_step (N : ℕ) (b : ℕ∞) (lam : ℝ) (pol : Scheme)
    (hpol : ∀ j Q, Measurable (pol j Q)) (j : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × Ensemble => step N b lam pol j p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro e
  simp only [step]
  apply Measurable.ite
  · exact measurableSet_lt (measurable_const.mul (measurable_pi_apply 1)) measurable_const
  · exact (measurable_from_top (f := fun c : ℕ => addItem N b c e)).comp (hpol j e.Q)
  · have hu : Measurable (fun u : ℕ → ℝ => uniformPos N (u 2)) := by
      unfold uniformPos
      exact (measurable_from_top (f := fun c : ℕ => min (c + 1) N)).comp
        ((measurable_const.mul (measurable_pi_apply 2)).nat_floor)
    exact (measurable_from_top (f := fun c : ℕ => removeItem N c e)).comp hu

lemma measurable_eventState (N : ℕ) (b : ℕ∞) (lam : ℝ) (pol : Scheme)
    (hpol : ∀ j Q, Measurable (pol j Q)) (Q0 : ℕ →₀ ℕ) (n : ℕ) :
    Measurable (fun w : ℕ × ℕ → ℝ => eventState N b lam pol Q0 (mk w) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_step N b lam pol hpol (n + 1)).comp ((measurable_mark (n + 1)).prodMk ih)

lemma renewal_eq_iff (X : ℕ → ℝ) (t : ℝ) (hX0 : X 0 = 0) (n : ℕ) :
    BellWilliams2001.ThresholdPolicy.renewalCount X t = (n : ℕ∞) ↔
      (n = 0 ∨ X n ≤ t) ∧ ∀ m : ℕ, n < m → t < X m := by
  unfold BellWilliams2001.ThresholdPolicy.renewalCount
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      push Not at hc
      have : (⨆ (k : ℕ) (_ : X k ≤ t), (k : ℕ∞)) ≤ ((n - 1 : ℕ) : ℕ∞) := by
        apply iSup₂_le
        intro k hk
        have : k ≠ n := fun e => by subst e; linarith [hc.2]
        have hkn : (k : ℕ∞) ≤ n := h ▸ le_iSup₂ (f := fun (k : ℕ) (_ : X k ≤ t) => (k : ℕ∞)) k hk
        have : k ≤ n := by exact_mod_cast hkn
        exact_mod_cast (by omega : k ≤ n - 1)
      rw [h] at this
      have : n ≤ n - 1 := by exact_mod_cast this
      omega
    · intro m hm
      by_contra hc
      push Not at hc
      have := le_iSup₂ (f := fun (k : ℕ) (_ : X k ≤ t) => (k : ℕ∞)) m hc
      rw [h] at this
      have : m ≤ n := by exact_mod_cast this
      omega
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · apply iSup₂_le
      intro k hk
      by_contra hc
      push Not at hc
      have : n < k := by exact_mod_cast hc
      linarith [h2 k this]
    · rcases h1 with h1 | h1
      · subst h1; simp
      · exact le_iSup₂ (f := fun (k : ℕ) (_ : X k ≤ t) => (k : ℕ∞)) n h1

lemma measurable_eventCount (t : ℝ) :
    Measurable (fun w : ℕ × ℕ → ℝ => eventCount (mk w) t) := by
  unfold eventCount
  refine (measurable_from_top (f := ENat.toNat)).comp ?_
  rw [ENat.measurable_iff]
  intro n
  have hX : ∀ k, Measurable (fun w : ℕ × ℕ → ℝ =>
      BellWilliams2001.ThresholdPolicy.partialSum (fun j => mk w j 0) k) := by
    intro k
    unfold BellWilliams2001.ThresholdPolicy.partialSum
    exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply (i, 0))
  have hset : (fun w : ℕ × ℕ → ℝ => BellWilliams2001.ThresholdPolicy.renewalCount
      (BellWilliams2001.ThresholdPolicy.partialSum (fun j => mk w j 0)) t) ⁻¹' {(n : ℕ∞)} =
      ({w | n = 0} ∪ {w | BellWilliams2001.ThresholdPolicy.partialSum (fun j => mk w j 0) n ≤ t}) ∩
      ⋂ m : ℕ, {w | n < m → t < BellWilliams2001.ThresholdPolicy.partialSum
        (fun j => mk w j 0) m} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_union,
      Set.mem_setOf_eq, Set.mem_iInter]
    exact renewal_eq_iff _ t (by simp [BellWilliams2001.ThresholdPolicy.partialSum]) n
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.union ?_ ?_) (MeasurableSet.iInter (fun m => ?_))
  · by_cases h : n = 0 <;> simp [h]
  · exact measurableSet_le (hX n) measurable_const
  · by_cases h : n < m
    · simp only [h, true_implies]
      exact measurableSet_lt measurable_const (hX m)
    · simp [h]

/-- The scalar process `∑_{i ≥ m} Q_i(t) + L(t)` as a function of the marks. -/
noncomputable def F (N : ℕ) (b : ℕ∞) (lam : ℝ) (pol : Scheme) (Q0 : ℕ →₀ ℕ) (m : ℕ)
    (w : ℕ × ℕ → ℝ) (t : ℝ) : ℝ :=
  ((tailSum (eventState N b lam pol Q0 (mk w) (eventCount (mk w) t)).Q m +
    (eventState N b lam pol Q0 (mk w) (eventCount (mk w) t)).L : ℕ) : ℝ)

lemma measurable_F (N : ℕ) (b : ℕ∞) (lam : ℝ) (pol : Scheme)
    (hpol : ∀ j Q, Measurable (pol j Q)) (Q0 : ℕ →₀ ℕ) (m : ℕ) :
    Measurable (fun w (t : ℝ≥0) => F N b lam pol Q0 m w t) := by
  apply measurable_pi_lambda
  intro t
  have h2 : Measurable (fun p : (ℕ × ℕ → ℝ) × ℕ => eventState N b lam pol Q0 (mk p.1) p.2) :=
    measurable_from_prod_countable_left (fun k => measurable_eventState N b lam pol hpol Q0 k)
  have h3 : Measurable (fun w : ℕ × ℕ → ℝ =>
      eventState N b lam pol Q0 (mk w) (eventCount (mk w) t)) :=
    h2.comp (measurable_id.prodMk (measurable_eventCount t))
  exact (measurable_from_top (f := fun e : Ensemble => ((tailSum e.Q m + e.L : ℕ) : ℝ))).comp h3

/-- The uncurried array of clock and marks of a system. -/
def U {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {b : ℕ∞} {lam : ℝ}
    (sys : System P N b lam) (ω : Ω) : ℕ × ℕ → ℝ := fun p => sys.ξ p.1 p.2 ω

lemma measurable_U {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {b : ℕ∞}
    {lam : ℝ} (sys : System P N b lam) : Measurable (U sys) :=
  measurable_pi_lambda _ (fun p => sys.measurable_ξ p.1 p.2)

lemma law_U {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {N : ℕ} {b : ℕ∞}
    {lam : ℝ} (s₁ : System P₁ N b lam) (s₂ : System P₂ N b lam) :
    P₁.map (U s₁) = P₂.map (U s₂) := by
  have h1 := s₁.iIndep_ξ.map_fun_eq_infinitePi_map (fun (p : ℕ × ℕ) => s₁.measurable_ξ p.1 p.2)
  have h2 := s₂.iIndep_ξ.map_fun_eq_infinitePi_map (fun (p : ℕ × ℕ) => s₂.measurable_ξ p.1 p.2)
  have hm : (fun (p : ℕ × ℕ) => P₁.map (s₁.ξ p.1 p.2)) =
      (fun (p : ℕ × ℕ) => P₂.map (s₂.ξ p.1 p.2)) := by
    funext p
    obtain ⟨k, r⟩ := p
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; rw [s₁.law_clock k, s₂.law_clock k]
    · rw [s₁.law_mark k r hr, s₂.law_mark k r hr]
  show P₁.map (fun ω (p : ℕ × ℕ) => s₁.ξ p.1 p.2 ω) = P₂.map (fun ω (p : ℕ × ℕ) => s₂.ξ p.1 p.2 ω)
  rw [h1, h2]
  congr 1

lemma identDistrib_comp {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {β : Type*}
    [MeasurableSpace β] (P : Measure Ω) (Φ : Ω → Ω₀) (hΦ : Measurable Φ) (f : Ω₀ → β)
    (hf : Measurable f) : IdentDistrib f (f ∘ Φ) (P.map Φ) P :=
  ⟨hf.aemeasurable, (hf.comp hΦ).aemeasurable, Measure.map_map hf hΦ⟩

lemma procLeSt_of {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {N : ℕ} {b : ℕ∞}
    {lam : ℝ} (s₁ : System P₁ N b lam) (s₂ : System P₂ N b lam)
    (pol₁ pol₂ : Scheme) (hm₁ : ∀ j Q, Measurable (pol₁ j Q)) (hm₂ : ∀ j Q, Measurable (pol₂ j Q))
    (Q₁ Q₂ : ℕ →₀ ℕ) (h₁ : ∀ ω, s₁.Q0 ω = Q₁) (h₂ : ∀ ω, s₂.Q0 ω = Q₂) (m : ℕ)
    (hle : ∀ w t, F N b lam pol₁ Q₁ m w t ≤ F N b lam pol₂ Q₂ m w t) :
    ProcLeSt P₁ P₂
      (fun ω t => ((tailSum (s₁.occ pol₁ ω t) m + s₁.overflow pol₁ ω t : ℕ) : ℝ))
      (fun ω t => ((tailSum (s₂.occ pol₂ ω t) m + s₂.overflow pol₂ ω t : ℕ) : ℝ)) := by
  haveI : IsProbabilityMeasure (P₁.map (U s₁)) :=
    Measure.isProbabilityMeasure_map (measurable_U s₁).aemeasurable
  refine ⟨ℕ × ℕ → ℝ, inferInstance, P₁.map (U s₁), F N b lam pol₁ Q₁ m,
    F N b lam pol₂ Q₂ m, inferInstance, ?_, ?_, ?_⟩
  · have := identDistrib_comp P₁ (U s₁) (measurable_U s₁) _ (measurable_F N b lam pol₁ hm₁ Q₁ m)
    convert this using 1
    funext ω t
    simp only [Function.comp, System.occ, System.overflow, System.stateSeq, System.count,
      F, h₁]
    rfl
  · rw [law_U s₁ s₂]
    have := identDistrib_comp P₂ (U s₂) (measurable_U s₂) _ (measurable_F N b lam pol₂ hm₂ Q₂ m)
    convert this using 1
    funext ω t
    simp only [Function.comp, System.occ, System.overflow, System.stateSeq, System.count,
      F, h₂]
    rfl
  · exact Filter.Eventually.of_forall (fun w t _ => hle w t)

lemma F_le (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (pol₁ pol₂ : Scheme)
    (hp₁ : ∀ j Q u, 1 ≤ pol₁ j Q u) (hp₂ : ∀ j Q u, pol₂ j Q u ≤ N)
    (hle : ∀ j Q Q' u, pol₁ j Q u ≤ pol₂ j Q' u)
    (Q₁ Q₂ : ℕ →₀ ℕ) (hQ₁ : IsOccupancy N b Q₁) (hQ₂ : IsOccupancy N b Q₂)
    (h0 : ∀ m : ℕ, 1 ≤ m → tailSum Q₁ m ≤ tailSum Q₂ m) (m : ℕ) (hm : 1 ≤ m)
    (w : ℕ × ℕ → ℝ) (t : ℝ) : F N b lam pol₁ Q₁ m w t ≤ F N b lam pol₂ Q₂ m w t := by
  have := (ordered_seq N hN b hb lam pol₁ pol₂ hp₁ hp₂ hle Q₁ Q₂ hQ₁ hQ₂ h0 (mk w)
    (eventCount (mk w) t)).2.2 m hm
  unfold F
  exact_mod_cast this

end PowerOfDUniversality.Fluid.Prop32Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Prop32Aux

theorem solution (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (n : ℕ) (hn : n + 1 ≤ N) (pol : Scheme) (hpol : IsCJSQ n pol)
    {Ω₁ Ω₂ Ω₃ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (P₃ : Measure Ω₃)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure P₃]
    (sysJ : System P₁ N b lam) (sysC : System P₂ N b lam) (sysM : System P₃ N b lam)
    (QJ QC QM : ℕ →₀ ℕ) (hJ : ∀ ω, sysJ.Q0 ω = QJ) (hC : ∀ ω, sysC.Q0 ω = QC)
    (hM : ∀ ω, sysM.Q0 ω = QM) (m : ℕ) (hm : 1 ≤ m) :
    ((∀ m' : ℕ, 1 ≤ m' → tailSum QJ m' ≤ tailSum QC m') →
      ProcLeSt P₁ P₂
        (fun ω t => ((tailSum (sysJ.occ jsq ω t) m + sysJ.overflow jsq ω t : ℕ) : ℝ))
        (fun ω t => ((tailSum (sysC.occ pol ω t) m + sysC.overflow pol ω t : ℕ) : ℝ))) ∧
    ((∀ m' : ℕ, 1 ≤ m' → tailSum QC m' ≤ tailSum QM m') →
      ProcLeSt P₂ P₃
        (fun ω t => ((tailSum (sysC.occ pol ω t) m + sysC.overflow pol ω t : ℕ) : ℝ))
        (fun ω t => ((tailSum (sysM.occ (mjsq n) ω t) m + sysM.overflow (mjsq n) ω t : ℕ) : ℝ))) := by
  obtain ⟨ω₁⟩ := nonempty_of_isProbabilityMeasure P₁
  obtain ⟨ω₂⟩ := nonempty_of_isProbabilityMeasure P₂
  obtain ⟨ω₃⟩ := nonempty_of_isProbabilityMeasure P₃
  have oJ : IsOccupancy N b QJ := hJ ω₁ ▸ sysJ.isOccupancy_Q0 ω₁
  have oC : IsOccupancy N b QC := hC ω₂ ▸ sysC.isOccupancy_Q0 ω₂
  have oM : IsOccupancy N b QM := hM ω₃ ▸ sysM.isOccupancy_Q0 ω₃
  have mJ : ∀ j Q, Measurable (jsq j Q) := fun _ _ => measurable_const
  have mM : ∀ j Q, Measurable (mjsq n j Q) := fun _ _ => measurable_const
  constructor
  · intro h0
    exact procLeSt_of sysJ sysC jsq pol mJ hpol.2 QJ QC hJ hC m
      (F_le N hN b hb lam jsq pol (fun _ _ _ => le_rfl)
        (fun j Q u => le_trans (hpol.1 j Q u).2 hn) (fun j Q Q' u => (hpol.1 j Q' u).1)
        QJ QC oJ oC h0 m hm)
  · intro h0
    exact procLeSt_of sysC sysM pol (mjsq n) hpol.2 mM QC QM hC hM m
      (F_le N hN b hb lam pol (mjsq n) (fun j Q u => (hpol.1 j Q u).1)
        (fun _ _ _ => hn) (fun j Q Q' u => (hpol.1 j Q u).2)
        QC QM oC oM h0 m hm)
