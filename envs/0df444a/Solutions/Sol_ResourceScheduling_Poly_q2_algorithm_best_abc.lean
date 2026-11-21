-- Prove2me | solution 1 for ResourceScheduling.Poly.q2_algorithm_best_abc
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:47:11.961038+00:00
-- url     : https://prove2.me/submissions/efc1f70d-bdb1-4328-867f-2abebd41dac5

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_Q2Properties
import Definitions.Def_ResourceScheduling_Poly_Q2Algorithm

set_option autoImplicit false

namespace Aux_Q2ABC
open ResourceScheduling.Poly

/-! ### Generic facts about schedules -/

theorem transGen_false {α : Type*} {R : α → α → Prop} (h : ∀ a b, ¬ R a b) {a b : α}
    (hab : Relation.TransGen R a b) : False := by
  induction hab with
  | single h' => exact h _ _ h'
  | tail _ h' _ => exact h _ _ h'

theorem proc_pos (I : Instance) (i : Fin I.m) : 0 < I.procTime i := by
  unfold Instance.procTime
  exact one_div_pos.mpr (I.q_pos i)

theorem start_lt_completion {I : Instance} (σ : Schedule I) (j : Fin I.n) :
    σ.start j < σ.completion j := by
  unfold Schedule.completion
  linarith [proc_pos I (σ.machine j)]

theorem mem_filter_any {α : Type*} [Fintype α] (p : α → Prop) (d : DecidablePred p) (a : α) :
    a ∈ @Finset.filter α p d Finset.univ ↔ p a := by
  simp

theorem mem_active {I : Instance} (σ : Schedule I) (t : ℝ) (j : Fin I.n) :
    j ∈ σ.activeSet t ↔ σ.start j ≤ t ∧ t < σ.completion j := by
  unfold Schedule.activeSet
  exact mem_filter_any _ _ j

theorem le_makespan {I : Instance} (σ : Schedule I) (j : Fin I.n) :
    σ.completion j ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with hne
  · exact Finset.le_sup' σ.completion (Finset.mem_univ j)
  · exact (hne ⟨j, Finset.mem_univ j⟩).elim

theorem makespan_le {I : Instance} (σ : Schedule I) (M : ℝ) (h : ∀ j, σ.completion j ≤ M)
    (h0 : 0 ≤ M) : σ.makespan ≤ M := by
  unfold Schedule.makespan
  split_ifs with hne
  · exact Finset.sup'_le hne _ (fun j _ => h j)
  · exact h0

theorem makespan_nonneg {I : Instance} (σ : Schedule I) (hσ : ∀ j, 0 ≤ σ.start j) :
    0 ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with hne
  · obtain ⟨j, -⟩ := id hne
    exact le_trans (le_trans (hσ j) (start_lt_completion σ j).le)
      (Finset.le_sup' σ.completion (Finset.mem_univ j))
  · exact le_rfl

theorem sum_le_of_pairs {ι : Type*} [DecidableEq ι] (A : Finset ι) (r : ι → ℕ) (s : ℕ)
    (h1 : ∀ a ∈ A, r a ≤ s) (h2 : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → r a + r b ≤ s)
    (h3 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → False) :
    ∑ a ∈ A, r a ≤ s := by
  rcases A.eq_empty_or_nonempty with hA | ⟨a, ha⟩
  · rw [hA, Finset.sum_empty]; exact Nat.zero_le _
  · by_cases hb : ∃ b ∈ A, b ≠ a
    · obtain ⟨b, hb, hba⟩ := hb
      have hsub : A ⊆ {a, b} := by
        intro c hc
        by_contra hc'
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
        exact h3 a ha b hb c hc (Ne.symm hba) (Ne.symm hc'.1) (Ne.symm hc'.2)
      calc ∑ x ∈ A, r x ≤ ∑ x ∈ ({a, b} : Finset ι), r x := Finset.sum_le_sum_of_subset hsub
        _ = r a + r b := Finset.sum_pair (Ne.symm hba)
        _ ≤ s := h2 a ha b hb (Ne.symm hba)
    · push_neg at hb
      have hsub : A ⊆ {a} := by
        intro c hc
        rw [Finset.mem_singleton]
        exact hb c hc
      calc ∑ x ∈ A, r x ≤ ∑ x ∈ ({a} : Finset ι), r x := Finset.sum_le_sum_of_subset hsub
        _ = r a := Finset.sum_singleton _ _
        _ ≤ s := h1 a ha

theorem fin2_eq {m : ℕ} (hm : m = 2) (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) : y = z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have h1 : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have h2 : x.val ≠ z.val := fun h => hxz (Fin.ext h)
  exact Fin.ext (by omega)

theorem active_sum_le {I : Instance} (hm : I.m = 2) (σ : Schedule I)
    (hdisj : ∀ j k, j ≠ k → σ.machine j = σ.machine k →
      σ.completion j ≤ σ.start k ∨ σ.completion k ≤ σ.start j)
    (r : Fin I.n → ℕ) (s : ℕ) (t : ℝ) (h1 : ∀ a, r a ≤ s)
    (h2 : ∀ a b, a ∈ σ.activeSet t → b ∈ σ.activeSet t → σ.machine a ≠ σ.machine b →
      r a + r b ≤ s) :
    ∑ a ∈ σ.activeSet t, r a ≤ s := by
  have hnb : ∀ a b, a ∈ σ.activeSet t → b ∈ σ.activeSet t → a ≠ b →
      σ.machine a ≠ σ.machine b := by
    intro a b ha hb hab hmab
    rw [mem_active] at ha hb
    rcases hdisj a b hab hmab with h | h
    · linarith [ha.2, hb.1]
    · linarith [ha.1, hb.2]
  apply sum_le_of_pairs
  · intro a _
    exact h1 a
  · intro a ha b hb hab
    exact h2 a b ha hb (hnb a b ha hb hab)
  · intro a ha b hb c hc hab hac hbc
    exact hnb b c hb hc hbc (fin2_eq hm _ _ _ (hnb a b ha hb hab) (hnb a c ha hc hac))

theorem no_overlap {I : Instance} (σ : Schedule I)
    (hres : ∀ t : ℝ, I.ResourceFeasibleSet (σ.activeSet t))
    (h : Fin I.l) (a b : Fin I.n) (hab : a ≠ b) (hc : I.s h < I.r h a + I.r h b) :
    σ.completion a ≤ σ.start b ∨ σ.completion b ≤ σ.start a := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have ha : a ∈ σ.activeSet (max (σ.start a) (σ.start b)) := by
    rw [mem_active]
    exact ⟨le_max_left _ _, max_lt (start_lt_completion σ a) h1⟩
  have hb : b ∈ σ.activeSet (max (σ.start a) (σ.start b)) := by
    rw [mem_active]
    exact ⟨le_max_right _ _, max_lt h2 (start_lt_completion σ b)⟩
  have hsub : ({a, b} : Finset (Fin I.n)) ⊆ σ.activeSet (max (σ.start a) (σ.start b)) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx]; exact ha
    · rw [hx]; exact hb
  have h3 := Finset.sum_le_sum_of_subset (f := I.r h) hsub
  rw [Finset.sum_pair hab] at h3
  have h4 : I.r h a + I.r h b ≤ I.s h := le_trans h3 (hres _ h)
  exact absurd h4 (not_le.mpr hc)

/-- Pairwise disjoint executions inside `[t0, L]` have total length at most `L - t0`. -/
theorem disj_sum {I : Instance} (σ : Schedule I) :
    ∀ (N : ℕ) (X : Finset (Fin I.n)), X.card ≤ N → ∀ (t0 L : ℝ),
    (∀ x ∈ X, t0 ≤ σ.start x) → (∀ x ∈ X, σ.completion x ≤ L) →
    (∀ x ∈ X, ∀ y ∈ X, x ≠ y → σ.completion x ≤ σ.start y ∨ σ.completion y ≤ σ.start x) →
    t0 ≤ L → t0 + ∑ x ∈ X, I.procTime (σ.machine x) ≤ L := by
  intro N
  induction N with
  | zero =>
    intro X hX t0 L _ _ _ hL
    have hX0 : X = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hX0, Finset.sum_empty, add_zero]
    exact hL
  | succ N ih =>
    intro X hX t0 L hst hco hdj hL
    rcases X.eq_empty_or_nonempty with hE | hne
    · rw [hE, Finset.sum_empty, add_zero]
      exact hL
    obtain ⟨x, hx, hmin⟩ := X.exists_min_image σ.start hne
    have hrest := ih (X.erase x) (by rw [Finset.card_erase_of_mem hx]; omega) (σ.completion x) L
      (fun y hy => by
        have hyx := Finset.ne_of_mem_erase hy
        have hyX := Finset.mem_of_mem_erase hy
        rcases hdj x hx y hyX (Ne.symm hyx) with h | h
        · exact h
        · exfalso
          have h5 := hmin y hyX
          have h6 := start_lt_completion σ y
          linarith)
      (fun y hy => hco y (Finset.mem_of_mem_erase hy))
      (fun y hy z hz hyz => hdj y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hyz)
      (hco x hx)
    rw [← Finset.add_sum_erase X _ hx]
    have h1 := hst x hx
    have h2 : σ.completion x = σ.start x + I.procTime (σ.machine x) := rfl
    linarith

/-! ### Facts specific to the two-machine, one-resource setting -/

theorem M1_ne_M2 (I : Instance) (hm : I.m = 2) : I.M₁ hm ≠ I.M₂ hm := by
  intro h
  have h' : (0 : ℕ) = 1 := congrArg Fin.val h
  omega

theorem mach_cases (I : Instance) (hm : I.m = 2) (x : Fin I.m) : x = I.M₁ hm ∨ x = I.M₂ hm := by
  have hx := x.isLt
  rcases Nat.lt_or_ge x.val 1 with h | h
  · left
    exact Fin.ext (by show x.val = 0; omega)
  · right
    exact Fin.ext (by show x.val = 1; omega)

theorem R1_eq (I : Instance) (hl : I.l = 1) (h : Fin I.l) : h = I.R₁ hl := by
  have := h.isLt
  exact Fin.ext (by show h.val = 0; omega)

/-- The positions (among the first `c`) whose job conflicts with job `j`. -/
def Dset (I : Instance) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n) (c : ℕ) (j : Fin I.n) :
    Finset (Fin I.n) :=
  Finset.univ.filter (fun p : Fin I.n =>
    p.val < c ∧ I.s (I.R₁ hl) < I.r (I.R₁ hl) j + I.r (I.R₁ hl) (ord p))

theorem mem_Dset (I : Instance) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n) (c : ℕ)
    (j p : Fin I.n) :
    p ∈ Dset I hl ord c j ↔ p.val < c ∧ I.s (I.R₁ hl) < I.r (I.R₁ hl) j + I.r (I.R₁ hl) (ord p) := by
  unfold Dset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem Dset_down (I : Instance) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) (c : ℕ) (j : Fin I.n)
    {p q : Fin I.n} (hq : q ∈ Dset I hl ord c j) (hpq : p ≤ q) : p ∈ Dset I hl ord c j := by
  rw [mem_Dset] at hq ⊢
  have h1 : p.val ≤ q.val := hpq
  have h2 : I.r (I.R₁ hl) (ord q) ≤ I.r (I.R₁ hl) (ord p) := hord hpq
  exact ⟨by omega, by omega⟩

theorem Dset_i (I : Instance) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) (c : ℕ) (j : Fin I.n)
    {p : Fin I.n} (hp : p ∈ Dset I hl ord c j) : p.val + 1 ≤ (Dset I hl ord c j).card := by
  have hsub : Finset.Iic p ⊆ Dset I hl ord c j := by
    intro q hq
    exact Dset_down I hl ord hord c j hp (Finset.mem_Iic.mp hq)
  have := Finset.card_le_card hsub
  rwa [Fin.card_Iic] at this

theorem Dset_ii (I : Instance) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) (c : ℕ) (j : Fin I.n)
    {p : Fin I.n} (hp : p.val < (Dset I hl ord c j).card) : p ∈ Dset I hl ord c j := by
  by_contra hnot
  have hsub : Dset I hl ord c j ⊆ Finset.Iio p := by
    intro q hq
    rw [Finset.mem_Iio]
    by_contra hqp
    push_neg at hqp
    exact hnot (Dset_down I hl ord hord c j hq hqp)
  have := Finset.card_le_card hsub
  rw [Fin.card_Iio] at this
  omega

theorem slot_lt {a b : ℕ} {u q : ℝ} (hq : 0 < q) (h1 : (a : ℝ) / q ≤ u)
    (h2 : u < ((b : ℝ) + 1) / q) : a < b + 1 := by
  have h3 : (a : ℝ) / q < ((b : ℝ) + 1) / q := lt_of_le_of_lt h1 h2
  rw [div_lt_div_iff_of_pos_right hq] at h3
  exact_mod_cast h3

theorem sum_le_single {ι : Type*} (F : Finset ι) (R : ι → ℕ) (rj s : ℕ) (h0 : rj ≤ s)
    (h1 : ∀ p ∈ F, rj + R p ≤ s) (h2 : ∀ p ∈ F, ∀ p' ∈ F, p = p') :
    rj + ∑ p ∈ F, R p ≤ s := by
  rcases F.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE, Finset.sum_empty, add_zero]
    exact h0
  · have hF : F = {p0} := by
      ext p
      rw [Finset.mem_singleton]
      constructor
      · intro hp
        exact h2 p hp p0 hp0
      · intro hp
        rw [hp]
        exact hp0
    rw [hF, Finset.sum_singleton]
    exact h1 p0 hp0

/-- Closed form of the "as early as possible" start time. -/
theorem moveStart_eq (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (e : ℝ) (he : 0 ≤ e) (c : ℕ)
    (j : Fin I.n) :
    Q2Algorithm.moveStart I hm hl ord e c j
      = max e (((Dset I hl ord c j).card : ℝ) / I.q (I.M₁ hm)) := by
  have hq1 : 0 < I.q (I.M₁ hm) := I.q_pos _
  have hq2 : 0 < 1 / I.q (I.M₂ hm) := one_div_pos.mpr (I.q_pos _)
  have hset : {t : ℝ | e ≤ t ∧ Q2Algorithm.FitsOnM₂ I hm hl ord c j t}
      = Set.Ici (max e (((Dset I hl ord c j).card : ℝ) / I.q (I.M₁ hm))) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Ici, max_le_iff]
    constructor
    · rintro ⟨het, hfits⟩
      refine ⟨het, ?_⟩
      by_contra hlt
      push_neg at hlt
      have ht0 : 0 ≤ t := le_trans he het
      have hp1 : ((⌊t * I.q (I.M₁ hm)⌋₊ : ℕ) : ℝ) ≤ t * I.q (I.M₁ hm) :=
        Nat.floor_le (mul_nonneg ht0 hq1.le)
      have hp2 : t * I.q (I.M₁ hm) < ((⌊t * I.q (I.M₁ hm)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hlt' : t * I.q (I.M₁ hm) < ((Dset I hl ord c j).card : ℝ) := by
        rwa [lt_div_iff₀ hq1] at hlt
      have hpN : ⌊t * I.q (I.M₁ hm)⌋₊ < (Dset I hl ord c j).card := by
        exact_mod_cast lt_of_le_of_lt hp1 hlt'
      have hNn : (Dset I hl ord c j).card ≤ I.n := by
        have := Finset.card_le_univ (Dset I hl ord c j)
        simpa using this
      have hpn : ⌊t * I.q (I.M₁ hm)⌋₊ < I.n := lt_of_lt_of_le hpN hNn
      have hmem := Dset_ii I hl ord hord c j (p := ⟨_, hpn⟩) hpN
      rw [mem_Dset] at hmem
      unfold Q2Algorithm.FitsOnM₂ at hfits
      have key := hfits t le_rfl (by linarith)
      have hin : (⟨_, hpn⟩ : Fin I.n) ∈ Finset.univ.filter (fun p : Fin I.n =>
          p.val < c ∧ (p.val : ℝ) / I.q (I.M₁ hm) ≤ t ∧
            t < ((p.val : ℝ) + 1) / I.q (I.M₁ hm)) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hmem.1, ?_, ?_⟩
        · show ((⌊t * I.q (I.M₁ hm)⌋₊ : ℕ) : ℝ) / I.q (I.M₁ hm) ≤ t
          rw [div_le_iff₀ hq1]
          exact hp1
        · show t < (((⌊t * I.q (I.M₁ hm)⌋₊ : ℕ) : ℝ) + 1) / I.q (I.M₁ hm)
          rw [lt_div_iff₀ hq1]
          exact hp2
      have hle := Finset.single_le_sum (f := fun p => I.r (I.R₁ hl) (ord p))
        (fun _ _ => Nat.zero_le _) hin
      have h5 : I.r (I.R₁ hl) j + I.r (I.R₁ hl) (ord ⟨_, hpn⟩) ≤ I.s (I.R₁ hl) :=
        le_trans (Nat.add_le_add_left hle _) key
      exact absurd h5 (not_le.mpr hmem.2)
    · rintro ⟨het, hNt⟩
      refine ⟨het, ?_⟩
      unfold Q2Algorithm.FitsOnM₂
      intro u htu _
      apply sum_le_single _ _ _ _ (hfit j)
      · intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨_, hpc, _, hpu⟩ := hp
        by_contra hcon
        push_neg at hcon
        have hD : p ∈ Dset I hl ord c j := (mem_Dset I hl ord c j p).mpr ⟨hpc, hcon⟩
        have h1 := Dset_i I hl ord hord c j hD
        have h2 : ((p.val : ℝ) + 1) / I.q (I.M₁ hm)
            ≤ ((Dset I hl ord c j).card : ℝ) / I.q (I.M₁ hm) :=
          div_le_div_of_nonneg_right (by exact_mod_cast h1) hq1.le
        linarith
      · intro p hp p' hp'
        rw [Finset.mem_filter] at hp hp'
        have a1 := slot_lt hq1 hp.2.2.1 hp'.2.2.2
        have a2 := slot_lt hq1 hp'.2.2.1 hp.2.2.2
        exact Fin.ext (by omega)
  unfold Q2Algorithm.moveStart
  rw [hset, csInf_Ici]

/-! ### The completion times on `M₂` -/

theorem m2End_zero (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n) :
    Q2Algorithm.m2End I hm hl ord 0 = 0 := rfl

theorem m2End_succ (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (i : ℕ) (h : i < I.n) :
    Q2Algorithm.m2End I hm hl ord (i + 1)
      = Q2Algorithm.movedStart I hm hl ord i h + 1 / I.q (I.M₂ hm) := by
  first
  | (simp only [Q2Algorithm.m2End, dif_pos h, Q2Algorithm.movedStart]; done)
  | (rw [Q2Algorithm.m2End, dif_pos h]; rfl)
  | rfl

theorem m2End_succ_ge (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (i : ℕ) (h : ¬ i < I.n) :
    Q2Algorithm.m2End I hm hl ord (i + 1) = Q2Algorithm.m2End I hm hl ord i := by
  first
  | (simp only [Q2Algorithm.m2End, dif_neg h]; done)
  | (rw [Q2Algorithm.m2End, dif_neg h])

theorem m2End_nonneg (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) :
    ∀ i, 0 ≤ Q2Algorithm.m2End I hm hl ord i := by
  intro i
  induction i with
  | zero => exact le_of_eq (m2End_zero I hm hl ord).symm
  | succ i ih =>
    by_cases h : i < I.n
    · rw [m2End_succ I hm hl ord i h]
      unfold Q2Algorithm.movedStart
      rw [moveStart_eq I hm hl ord hord hfit _ ih]
      have h1 : 0 < 1 / I.q (I.M₂ hm) := one_div_pos.mpr (I.q_pos _)
      have h2 := le_max_left (Q2Algorithm.m2End I hm hl ord i)
        (((Dset I hl ord (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)).card : ℝ)
          / I.q (I.M₁ hm))
      linarith
    · rw [m2End_succ_ge I hm hl ord i h]
      exact ih

theorem movedStart_eq (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (i : ℕ) (h : i < I.n) :
    Q2Algorithm.movedStart I hm hl ord i h = max (Q2Algorithm.m2End I hm hl ord i)
      (((Dset I hl ord (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)).card : ℝ)
        / I.q (I.M₁ hm)) := by
  unfold Q2Algorithm.movedStart
  exact moveStart_eq I hm hl ord hord hfit _ (m2End_nonneg I hm hl ord hord hfit i) _ _

theorem movedStart_ge (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (i : ℕ) (h : i < I.n) :
    Q2Algorithm.m2End I hm hl ord i ≤ Q2Algorithm.movedStart I hm hl ord i h := by
  rw [movedStart_eq I hm hl ord hord hfit i h]
  exact le_max_left _ _

theorem movedStart_nonneg (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (ord : Fin I.n ≃ Fin I.n) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (i : ℕ) (h : i < I.n) :
    0 ≤ Q2Algorithm.movedStart I hm hl ord i h :=
  le_trans (m2End_nonneg I hm hl ord hord hfit i) (movedStart_ge I hm hl ord hord hfit i h)

theorem m2End_mono (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) :
    Monotone (Q2Algorithm.m2End I hm hl ord) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases h : i < I.n
  · rw [m2End_succ I hm hl ord i h]
    have h1 : 0 < 1 / I.q (I.M₂ hm) := one_div_pos.mpr (I.q_pos _)
    have h2 := movedStart_ge I hm hl ord hord hfit i h
    linarith
  · rw [m2End_succ_ge I hm hl ord i h]

theorem movedStart_mono (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (ord : Fin I.n ≃ Fin I.n) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (i i' : ℕ) (h : i < I.n) (h' : i' < I.n)
    (hii : i ≤ i') :
    Q2Algorithm.movedStart I hm hl ord i h ≤ Q2Algorithm.movedStart I hm hl ord i' h' := by
  rcases Nat.eq_or_lt_of_le hii with heq | hlt
  · subst heq
    exact le_rfl
  · have h1 : 0 < 1 / I.q (I.M₂ hm) := one_div_pos.mpr (I.q_pos _)
    have h2 := m2End_succ I hm hl ord i h
    have h3 := m2End_mono I hm hl ord hord hfit (show i + 1 ≤ i' by omega)
    have h4 := movedStart_ge I hm hl ord hord hfit i' h'
    linarith

theorem moved_noconf (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (i : ℕ) (h : i < I.n) (p : Fin I.n)
    (hp : p.val < I.n - 1 - i)
    (hlt : Q2Algorithm.movedStart I hm hl ord i h < ((p.val : ℝ) + 1) / I.q (I.M₁ hm)) :
    I.r (I.R₁ hl) (ord ⟨I.n - 1 - i, by omega⟩) + I.r (I.R₁ hl) (ord p) ≤ I.s (I.R₁ hl) := by
  by_contra hcon
  push_neg at hcon
  have hD : p ∈ Dset I hl ord (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩) :=
    (mem_Dset I hl ord _ _ p).mpr ⟨hp, hcon⟩
  have h1 := Dset_i I hl ord hord _ _ hD
  rw [movedStart_eq I hm hl ord hord hfit i h] at hlt
  have hq1 : 0 < I.q (I.M₁ hm) := I.q_pos _
  have h2 : ((p.val : ℝ) + 1) / I.q (I.M₁ hm) ≤
      ((Dset I hl ord (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)).card : ℝ)
        / I.q (I.M₁ hm) :=
    div_le_div_of_nonneg_right (by exact_mod_cast h1) hq1.le
  have h3 := le_max_right (Q2Algorithm.m2End I hm hl ord i)
    (((Dset I hl ord (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)).card : ℝ) / I.q (I.M₁ hm))
  linarith

/-! ### The schedules `afterMoves k` -/

theorem am_mach1 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (j : Fin I.n) (h : (ord.symm j).val + k < I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).machine j = I.M₁ hm := by
  show (if (ord.symm j).val + k < I.n then I.M₁ hm else I.M₂ hm) = I.M₁ hm
  rw [if_pos h]

theorem am_mach2 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (j : Fin I.n) (h : ¬ (ord.symm j).val + k < I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).machine j = I.M₂ hm := by
  show (if (ord.symm j).val + k < I.n then I.M₁ hm else I.M₂ hm) = I.M₂ hm
  rw [if_neg h]

theorem am_start1 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (j : Fin I.n) (h : (ord.symm j).val + k < I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).start j = ((ord.symm j).val : ℝ) / I.q (I.M₁ hm) := by
  show (if (ord.symm j).val + k < I.n then ((ord.symm j).val : ℝ) / I.q (I.M₁ hm) else _) = _
  rw [if_pos h]

theorem am_start2 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (j : Fin I.n) (h : ¬ (ord.symm j).val + k < I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).start j
      = Q2Algorithm.movedStart I hm hl ord (I.n - 1 - (ord.symm j).val)
          (by have := (ord.symm j).isLt; omega) := by
  show (if (ord.symm j).val + k < I.n then _ else _) = _
  rw [if_neg h]

theorem am_compl1 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (j : Fin I.n) (h : (ord.symm j).val + k < I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).completion j
      = (((ord.symm j).val : ℝ) + 1) / I.q (I.M₁ hm) := by
  unfold Schedule.completion
  rw [am_start1 I hm hl ord k j h, am_mach1 I hm hl ord k j h]
  unfold Instance.procTime
  ring

theorem am_compl2 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (j : Fin I.n) (h : ¬ (ord.symm j).val + k < I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).completion j
      = Q2Algorithm.m2End I hm hl ord (I.n - (ord.symm j).val) := by
  have hlt := (ord.symm j).isLt
  unfold Schedule.completion
  rw [am_start2 I hm hl ord k j h, am_mach2 I hm hl ord k j h]
  have h2 := m2End_succ I hm hl ord (I.n - 1 - (ord.symm j).val) (by omega)
  rw [show I.n - 1 - (ord.symm j).val + 1 = I.n - (ord.symm j).val by omega] at h2
  rw [h2]
  unfold Instance.procTime
  rfl

theorem am_disj (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (k : ℕ) :
    ∀ j j', j ≠ j' →
      (Q2Algorithm.afterMoves I hm hl ord k).machine j
        = (Q2Algorithm.afterMoves I hm hl ord k).machine j' →
      (Q2Algorithm.afterMoves I hm hl ord k).completion j
          ≤ (Q2Algorithm.afterMoves I hm hl ord k).start j' ∨
        (Q2Algorithm.afterMoves I hm hl ord k).completion j'
          ≤ (Q2Algorithm.afterMoves I hm hl ord k).start j := by
  intro j j' hjj' hmach
  have hρ : (ord.symm j).val ≠ (ord.symm j').val := by
    intro heq
    exact hjj' (ord.symm.injective (Fin.ext heq))
  have hq1 := I.q_pos (I.M₁ hm)
  have hj1 := (ord.symm j).isLt
  have hj2 := (ord.symm j').isLt
  by_cases h1 : (ord.symm j).val + k < I.n <;> by_cases h2 : (ord.symm j').val + k < I.n
  · rw [am_compl1 I hm hl ord k j h1, am_compl1 I hm hl ord k j' h2,
      am_start1 I hm hl ord k j h1, am_start1 I hm hl ord k j' h2]
    rcases Nat.lt_or_gt_of_ne hρ with hlt | hlt
    · left
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hq1.le
    · right
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hq1.le
  · exfalso
    rw [am_mach1 I hm hl ord k j h1, am_mach2 I hm hl ord k j' h2] at hmach
    exact M1_ne_M2 I hm hmach
  · exfalso
    rw [am_mach2 I hm hl ord k j h1, am_mach1 I hm hl ord k j' h2] at hmach
    exact M1_ne_M2 I hm hmach.symm
  · rw [am_compl2 I hm hl ord k j h1, am_compl2 I hm hl ord k j' h2,
      am_start2 I hm hl ord k j h1, am_start2 I hm hl ord k j' h2]
    rcases Nat.lt_or_gt_of_ne hρ with hlt | hlt
    · right
      calc Q2Algorithm.m2End I hm hl ord (I.n - (ord.symm j').val)
          ≤ Q2Algorithm.m2End I hm hl ord (I.n - 1 - (ord.symm j).val) :=
            m2End_mono I hm hl ord hord hfit (by omega)
        _ ≤ _ := movedStart_ge I hm hl ord hord hfit _ _
    · left
      calc Q2Algorithm.m2End I hm hl ord (I.n - (ord.symm j).val)
          ≤ Q2Algorithm.m2End I hm hl ord (I.n - 1 - (ord.symm j').val) :=
            m2End_mono I hm hl ord hord hfit (by omega)
        _ ≤ _ := movedStart_ge I hm hl ord hord hfit _ _

theorem am_cross (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (k : ℕ) (a b : Fin I.n)
    (ha : (ord.symm a).val + k < I.n) (hb : ¬ (ord.symm b).val + k < I.n) (t : ℝ)
    (hat : (Q2Algorithm.afterMoves I hm hl ord k).start a ≤ t ∧
      t < (Q2Algorithm.afterMoves I hm hl ord k).completion a)
    (hbt : (Q2Algorithm.afterMoves I hm hl ord k).start b ≤ t ∧
      t < (Q2Algorithm.afterMoves I hm hl ord k).completion b) :
    I.r (I.R₁ hl) a + I.r (I.R₁ hl) b ≤ I.s (I.R₁ hl) := by
  rw [am_compl1 I hm hl ord k a ha] at hat
  rw [am_start2 I hm hl ord k b hb] at hbt
  have hlt := (ord.symm b).isLt
  have key := moved_noconf I hm hl ord hord hfit (I.n - 1 - (ord.symm b).val) (by omega)
    (ord.symm a) (by omega) (lt_of_le_of_lt hbt.1 hat.2)
  have e : (⟨I.n - 1 - (I.n - 1 - (ord.symm b).val), by omega⟩ : Fin I.n) = ord.symm b :=
    Fin.ext (by show I.n - 1 - (I.n - 1 - (ord.symm b).val) = (ord.symm b).val; omega)
  rw [e] at key
  simp only [Equiv.apply_symm_apply] at key
  omega

theorem am_feasible (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hprec : I.NoPrecedence) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (k : ℕ) :
    (Q2Algorithm.afterMoves I hm hl ord k).Feasible := by
  refine ⟨?_, am_disj I hm hl ord hord hfit k, ?_, ?_⟩
  · intro j
    by_cases h : (ord.symm j).val + k < I.n
    · rw [am_start1 I hm hl ord k j h]
      exact div_nonneg (Nat.cast_nonneg _) (I.q_pos _).le
    · rw [am_start2 I hm hl ord k j h]
      exact movedStart_nonneg I hm hl ord hord hfit _ _
  · intro j j' hjj'
    exact (transGen_false hprec hjj').elim
  · intro t h
    rw [R1_eq I hl h]
    apply active_sum_le hm _ (am_disj I hm hl ord hord hfit k) _ _ t (fun a => hfit a)
    intro a b ha hb hab
    rw [mem_active] at ha hb
    by_cases h1 : (ord.symm a).val + k < I.n <;> by_cases h2 : (ord.symm b).val + k < I.n
    · exfalso
      rw [am_mach1 I hm hl ord k a h1, am_mach1 I hm hl ord k b h2] at hab
      exact hab rfl
    · exact am_cross I hm hl ord hord hfit k a b h1 h2 t ha hb
    · rw [add_comm]
      exact am_cross I hm hl ord hord hfit k b a h2 h1 t hb ha
    · exfalso
      rw [am_mach2 I hm hl ord k a h1, am_mach2 I hm hl ord k b h2] at hab
      exact hab rfl

theorem am_abc (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (k : ℕ) :
    (Q2Algorithm.afterMoves I hm hl ord k).SatisfiesABC hm hl := by
  have hq1 := I.q_pos (I.M₁ hm)
  have m1 : ∀ j, (Q2Algorithm.afterMoves I hm hl ord k).machine j = I.M₁ hm →
      (ord.symm j).val + k < I.n := by
    intro j hj
    by_contra h
    rw [am_mach2 I hm hl ord k j h] at hj
    exact M1_ne_M2 I hm hj.symm
  have m2 : ∀ j, (Q2Algorithm.afterMoves I hm hl ord k).machine j = I.M₂ hm →
      ¬ (ord.symm j).val + k < I.n := by
    intro j hj h
    rw [am_mach1 I hm hl ord k j h] at hj
    exact M1_ne_M2 I hm hj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j hj
    have h := m1 j hj
    have hsub : (Finset.Iic (ord.symm j)).image ord ⊆ Finset.univ.filter
        (fun k' => (Q2Algorithm.afterMoves I hm hl ord k).machine k' = I.M₁ hm) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, am_mach1 I hm hl ord k _ ?_⟩
      rw [Equiv.symm_apply_apply]
      have hp' : p ≤ ord.symm j := Finset.mem_Iic.mp hp
      have : p.val ≤ (ord.symm j).val := hp'
      omega
    refine ⟨(ord.symm j).val, lt_of_lt_of_le ?_ (Finset.card_le_card hsub),
      am_start1 I hm hl ord k j h⟩
    rw [Finset.card_image_of_injective _ ord.injective, Fin.card_Iic]
    omega
  · intro j j' hj hj' hne heq
    rw [am_start1 I hm hl ord k j (m1 j hj), am_start1 I hm hl ord k j' (m1 j' hj'),
      div_left_inj' hq1.ne'] at heq
    have h2 : (ord.symm j).val = (ord.symm j').val := by exact_mod_cast heq
    exact hne (ord.symm.injective (Fin.ext h2))
  · intro j j' hj hj' hlt
    rw [am_start1 I hm hl ord k j (m1 j hj), am_start1 I hm hl ord k j' (m1 j' hj'),
      div_lt_div_iff_of_pos_right hq1] at hlt
    have hle : ord.symm j ≤ ord.symm j' := by
      have h3 : (ord.symm j).val < (ord.symm j').val := by exact_mod_cast hlt
      exact le_of_lt h3
    have h4 : I.r (I.R₁ hl) (ord (ord.symm j')) ≤ I.r (I.R₁ hl) (ord (ord.symm j)) := hord hle
    simpa using h4
  · intro j j' hj hj' hlt
    have h1 := m2 j hj
    have h2 := m2 j' hj'
    have hj1 := (ord.symm j).isLt
    have hj2 := (ord.symm j').isLt
    rw [am_start2 I hm hl ord k j h1, am_start2 I hm hl ord k j' h2] at hlt
    have hi : I.n - 1 - (ord.symm j).val < I.n - 1 - (ord.symm j').val := by
      by_contra hc
      push_neg at hc
      exact absurd hlt (not_lt.mpr (movedStart_mono I hm hl ord hord hfit _ _ _ _ hc))
    have hle : ord.symm j' ≤ ord.symm j := by
      show (ord.symm j').val ≤ (ord.symm j).val
      omega
    have h4 : I.r (I.R₁ hl) (ord (ord.symm j)) ≤ I.r (I.R₁ hl) (ord (ord.symm j')) := hord hle
    simpa using h4
  · intro j j' hj hj'
    have h1 := m1 j hj
    have h2 := m2 j' hj'
    have hle : ord.symm j ≤ ord.symm j' := by
      show (ord.symm j).val ≤ (ord.symm j').val
      omega
    have h4 : I.r (I.R₁ hl) (ord (ord.symm j')) ≤ I.r (I.R₁ hl) (ord (ord.symm j)) := hord hle
    simpa using h4

/-! ### Makespan of `afterMoves k` -/

theorem am_ms_le (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (k : ℕ) :
    (Q2Algorithm.afterMoves I hm hl ord k).makespan
      ≤ max (((I.n - k : ℕ) : ℝ) / I.q (I.M₁ hm)) (Q2Algorithm.m2End I hm hl ord k) := by
  have hq1 := I.q_pos (I.M₁ hm)
  apply makespan_le
  · intro j
    by_cases h : (ord.symm j).val + k < I.n
    · rw [am_compl1 I hm hl ord k j h]
      apply le_max_of_le_left
      apply div_le_div_of_nonneg_right _ hq1.le
      have h2 : (ord.symm j).val + 1 ≤ I.n - k := by omega
      exact_mod_cast h2
    · rw [am_compl2 I hm hl ord k j h]
      apply le_max_of_le_right
      apply m2End_mono I hm hl ord hord hfit
      have := (ord.symm j).isLt
      omega
  · exact le_max_of_le_right (m2End_nonneg I hm hl ord hord hfit k)

theorem am_ms_ge1 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (hk : k < I.n) :
    ((I.n - k : ℕ) : ℝ) / I.q (I.M₁ hm) ≤ (Q2Algorithm.afterMoves I hm hl ord k).makespan := by
  have hj : I.n - k - 1 < I.n := by omega
  have h : (ord.symm (ord ⟨I.n - k - 1, hj⟩)).val + k < I.n := by
    rw [Equiv.symm_apply_apply]
    show I.n - k - 1 + k < I.n
    omega
  have h1 := le_makespan (Q2Algorithm.afterMoves I hm hl ord k) (ord ⟨I.n - k - 1, hj⟩)
  rw [am_compl1 I hm hl ord k _ h, Equiv.symm_apply_apply] at h1
  have e : (((⟨I.n - k - 1, hj⟩ : Fin I.n).val : ℕ) : ℝ) + 1 = ((I.n - k : ℕ) : ℝ) := by
    show ((I.n - k - 1 : ℕ) : ℝ) + 1 = ((I.n - k : ℕ) : ℝ)
    rw [← Nat.cast_add_one, show I.n - k - 1 + 1 = I.n - k by omega]
  rw [e] at h1
  exact h1

theorem am_ms_ge2 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ I.n) :
    Q2Algorithm.m2End I hm hl ord k ≤ (Q2Algorithm.afterMoves I hm hl ord k).makespan := by
  have hj : I.n - k < I.n := by omega
  have h : ¬ (ord.symm (ord ⟨I.n - k, hj⟩)).val + k < I.n := by
    rw [Equiv.symm_apply_apply]
    show ¬ (I.n - k + k < I.n)
    omega
  have h1 := le_makespan (Q2Algorithm.afterMoves I hm hl ord k) (ord ⟨I.n - k, hj⟩)
  rw [am_compl2 I hm hl ord k _ h, Equiv.symm_apply_apply] at h1
  have e : I.n - (⟨I.n - k, hj⟩ : Fin I.n).val = k := by
    show I.n - (I.n - k) = k
    omega
  rw [e] at h1
  exact h1

theorem am_ms_eq (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (hn : 1 ≤ I.n) (k : ℕ) (hk : k ≤ I.n) :
    (Q2Algorithm.afterMoves I hm hl ord k).makespan
      = max (((I.n - k : ℕ) : ℝ) / I.q (I.M₁ hm)) (Q2Algorithm.m2End I hm hl ord k) := by
  apply le_antisymm (am_ms_le I hm hl ord hord hfit k)
  apply max_le
  · rcases Nat.lt_or_ge k I.n with h | h
    · exact am_ms_ge1 I hm hl ord k h
    · have h0 : I.n - k = 0 := by omega
      rw [h0, Nat.cast_zero, zero_div]
      exact le_trans (m2End_nonneg I hm hl ord hord hfit k)
        (am_ms_ge2 I hm hl ord k (by omega) hk)
  · rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [m2End_zero]
      exact le_trans (div_nonneg (Nat.cast_nonneg _) (I.q_pos _).le)
        (am_ms_ge1 I hm hl ord 0 (by omega))
    · exact am_ms_ge2 I hm hl ord k h hk

/-! ### The stopping rule picks a best `k` -/

theorem find_props {p : ℕ → Prop} (d : DecidablePred p) (H : ∃ n, p n) :
    p (@Nat.find p d H) ∧ ∀ m < @Nat.find p d H, ¬ p m :=
  ⟨@Nat.find_spec p d H, fun m hm => @Nat.find_min p d H m hm⟩

theorem stop_spec (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n) :
    (I.n ≤ Q2Algorithm.stopIndex I hm hl ord ∨
      ¬ ((Q2Algorithm.afterMoves I hm hl ord (Q2Algorithm.stopIndex I hm hl ord + 1)).makespan
        < (Q2Algorithm.afterMoves I hm hl ord (Q2Algorithm.stopIndex I hm hl ord)).makespan)) ∧
    ∀ m < Q2Algorithm.stopIndex I hm hl ord,
      ¬ (I.n ≤ m ∨ ¬ ((Q2Algorithm.afterMoves I hm hl ord (m + 1)).makespan
        < (Q2Algorithm.afterMoves I hm hl ord m).makespan)) := by
  unfold Q2Algorithm.stopIndex
  exact find_props (p := fun k => I.n ≤ k ∨ ¬ ((Q2Algorithm.afterMoves I hm hl ord (k + 1)).makespan
    < (Q2Algorithm.afterMoves I hm hl ord k).makespan)) _ _

theorem stop_opt (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl)) (hn : 1 ≤ I.n) (k : ℕ) (hk : k ≤ I.n) :
    (Q2Algorithm.afterMoves I hm hl ord (Q2Algorithm.stopIndex I hm hl ord)).makespan
      ≤ (Q2Algorithm.afterMoves I hm hl ord k).makespan := by
  obtain ⟨hspec, hmin⟩ := stop_spec I hm hl ord
  obtain ⟨K, hK⟩ : ∃ K, K = Q2Algorithm.stopIndex I hm hl ord := ⟨_, rfl⟩
  rw [← hK] at hspec hmin ⊢
  have hKn : K ≤ I.n := by
    by_contra h
    push_neg at h
    exact hmin I.n h (Or.inl le_rfl)
  rcases le_or_gt k K with hkK | hkK
  · have chain : ∀ d, d ≤ K → (Q2Algorithm.afterMoves I hm hl ord K).makespan
        ≤ (Q2Algorithm.afterMoves I hm hl ord (K - d)).makespan := by
      intro d
      induction d with
      | zero =>
        intro _
        simp only [Nat.sub_zero, le_refl]
      | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have h2 := hmin (K - (d + 1)) (by omega)
        push_neg at h2
        have e : K - (d + 1) + 1 = K - d := by omega
        rw [e] at h2
        linarith [h2.2]
    have h3 := chain (K - k) (by omega)
    rwa [show K - (K - k) = k by omega] at h3
  · have hKlt : K < I.n := by omega
    have hnot : ¬ ((Q2Algorithm.afterMoves I hm hl ord (K + 1)).makespan
        < (Q2Algorithm.afterMoves I hm hl ord K).makespan) := by
      rcases hspec with h | h
      · exact absurd h (not_le.mpr hKlt)
      · exact h
    push_neg at hnot
    rw [am_ms_eq I hm hl ord hord hfit hn (K + 1) (by omega)] at hnot
    have hK1 := am_ms_eq I hm hl ord hord hfit hn K hKn
    have hq1 := I.q_pos (I.M₁ hm)
    by_cases hc : ((I.n - (K + 1) : ℕ) : ℝ) / I.q (I.M₁ hm)
        ≤ Q2Algorithm.m2End I hm hl ord (K + 1)
    · rw [max_eq_right hc] at hnot
      calc (Q2Algorithm.afterMoves I hm hl ord K).makespan
          ≤ Q2Algorithm.m2End I hm hl ord (K + 1) := hnot
        _ ≤ Q2Algorithm.m2End I hm hl ord k := m2End_mono I hm hl ord hord hfit (by omega)
        _ ≤ (Q2Algorithm.afterMoves I hm hl ord k).makespan :=
            am_ms_ge2 I hm hl ord k (by omega) hk
    · push_neg at hc
      rw [max_eq_left hc.le] at hnot
      exfalso
      have h1 : ((I.n - (K + 1) : ℕ) : ℝ) / I.q (I.M₁ hm)
          < ((I.n - K : ℕ) : ℝ) / I.q (I.M₁ hm) := by
        apply div_lt_div_of_pos_right _ hq1
        have h5 : I.n - (K + 1) < I.n - K := by omega
        exact_mod_cast h5
      have h2 := le_max_left (((I.n - K : ℕ) : ℝ) / I.q (I.M₁ hm))
        (Q2Algorithm.m2End I hm hl ord K)
      rw [← hK1] at h2
      linarith

/-! ### Lower bound for an arbitrary feasible schedule -/

theorem key2 (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm)) (σ : Schedule I) (hσ : σ.Feasible)
    (L : ℝ) (hLc : ∀ j, σ.completion j ≤ L) (hL0 : 0 ≤ L)
    (F : ℕ) (hF : F = ⌊L * I.q (I.M₁ hm)⌋₊) (j : ℕ) (hj : j + F < I.n) :
    ((Dset I hl ord (I.n - 1 - j) (ord ⟨I.n - 1 - j, by omega⟩)).card : ℝ) / I.q (I.M₁ hm)
      + ((I.n - F - j : ℕ) : ℝ) / I.q (I.M₂ hm) ≤ L := by
  obtain ⟨hst, hdisj, _, hres⟩ := hσ
  have hq1 := I.q_pos (I.M₁ hm)
  have hq2 := I.q_pos (I.M₂ hm)
  have hjn : j < I.n := by omega
  obtain ⟨x, hx⟩ : ∃ x, x = ord ⟨I.n - 1 - j, by omega⟩ := ⟨_, rfl⟩
  rw [← hx]
  obtain ⟨D, hD⟩ : ∃ D, D = Dset I hl ord (I.n - 1 - j) x := ⟨_, rfl⟩
  rw [← hD]
  have hHcard : (D.image ord).card = D.card := Finset.card_image_of_injective _ ord.injective
  have hWcard : ((Finset.Iic (⟨I.n - 1 - j, by omega⟩ : Fin I.n)).image ord).card = I.n - j := by
    rw [Finset.card_image_of_injective _ ord.injective, Fin.card_Iic]
    show I.n - 1 - j + 1 = I.n - j
    omega
  obtain ⟨H, hH⟩ : ∃ H, H = D.image ord := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = (Finset.Iic (⟨I.n - 1 - j, by omega⟩ : Fin I.n)).image ord :=
    ⟨_, rfl⟩
  rw [← hH] at hHcard
  rw [← hW] at hWcard
  have hHW : H ⊆ W := by
    intro y hy
    rw [hH, Finset.mem_image] at hy
    rw [hW, Finset.mem_image]
    obtain ⟨p, hp, rfl⟩ := hy
    refine ⟨p, ?_, rfl⟩
    rw [Finset.mem_Iic]
    rw [hD, mem_Dset] at hp
    show p.val ≤ I.n - 1 - j
    omega
  have hconf : ∀ h ∈ H, ∀ w ∈ W, I.s (I.R₁ hl) < I.r (I.R₁ hl) h + I.r (I.R₁ hl) w := by
    intro h hh w hw
    rw [hH, Finset.mem_image] at hh
    rw [hW, Finset.mem_image] at hw
    obtain ⟨p, hp, rfl⟩ := hh
    obtain ⟨p', hp', rfl⟩ := hw
    rw [hD, mem_Dset] at hp
    have h2 : I.r (I.R₁ hl) x ≤ I.r (I.R₁ hl) (ord p') := by
      rw [hx]
      exact hord (Finset.mem_Iic.mp hp')
    omega
  have hno : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → (a ∈ H ∨ b ∈ H) →
      σ.completion a ≤ σ.start b ∨ σ.completion b ≤ σ.start a := by
    intro a ha b hb hab hor
    apply no_overlap σ hres (I.R₁ hl) a b hab
    rcases hor with h | h
    · exact hconf a h b hb
    · have := hconf b h a ha
      omega
  obtain ⟨W1, hW1⟩ : ∃ W1, W1 = (W \ H).filter (fun w => σ.machine w = I.M₁ hm) := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2, W2 = (W \ H).filter (fun w => ¬ σ.machine w = I.M₁ hm) :=
    ⟨_, rfl⟩
  have hW12 : W1.card + W2.card = W.card - H.card := by
    rw [hW1, hW2, Finset.card_filter_add_card_filter_not, Finset.card_sdiff_of_subset hHW]
  have hHle : H.card ≤ W.card := Finset.card_le_card hHW
  have hW1W : W1 ⊆ W := by
    intro a ha
    rw [hW1, Finset.mem_filter, Finset.mem_sdiff] at ha
    exact ha.1.1
  have hW2W : W2 ⊆ W := by
    intro a ha
    rw [hW2, Finset.mem_filter, Finset.mem_sdiff] at ha
    exact ha.1.1
  have hdisjH1 : Disjoint H W1 := by
    rw [Finset.disjoint_left]
    intro a ha ha1
    rw [hW1, Finset.mem_filter, Finset.mem_sdiff] at ha1
    exact ha1.1.2 ha
  have hdisjH2 : Disjoint H W2 := by
    rw [Finset.disjoint_left]
    intro a ha ha2
    rw [hW2, Finset.mem_filter, Finset.mem_sdiff] at ha2
    exact ha2.1.2 ha
  have hlen : ∀ y, 1 / I.q (I.M₁ hm) ≤ I.procTime (σ.machine y) := by
    intro y
    unfold Instance.procTime
    rcases mach_cases I hm (σ.machine y) with h | h
    · exact le_of_eq (by rw [h])
    · rw [h]
      exact one_div_le_one_div_of_le hq2 hq
  -- the family `H ∪ W1`
  have pairA : ∀ a ∈ H ∪ W1, ∀ b ∈ H ∪ W1, a ≠ b →
      σ.completion a ≤ σ.start b ∨ σ.completion b ≤ σ.start a := by
    intro a ha b hb hab
    rw [Finset.mem_union] at ha hb
    have haW : a ∈ W := ha.elim (fun h => hHW h) (fun h => hW1W h)
    have hbW : b ∈ W := hb.elim (fun h => hHW h) (fun h => hW1W h)
    by_cases hor : a ∈ H ∨ b ∈ H
    · exact hno a haW b hbW hab hor
    · push_neg at hor
      have ha1 : a ∈ W1 := ha.resolve_left hor.1
      have hb1 : b ∈ W1 := hb.resolve_left hor.2
      rw [hW1, Finset.mem_filter] at ha1 hb1
      exact hdisj a b hab (ha1.2.trans hb1.2.symm)
  have hA := disj_sum σ (H ∪ W1).card (H ∪ W1) le_rfl 0 L
    (fun y _ => hst y) (fun y _ => hLc y) pairA hL0
  have hsumA : ((H ∪ W1).card : ℝ) * (1 / I.q (I.M₁ hm))
      ≤ ∑ y ∈ H ∪ W1, I.procTime (σ.machine y) := by
    have h1 := Finset.card_nsmul_le_sum (H ∪ W1) (fun y => I.procTime (σ.machine y))
      (1 / I.q (I.M₁ hm)) (fun y _ => hlen y)
    rwa [nsmul_eq_mul] at h1
  have hcardA : (H ∪ W1).card ≤ F := by
    rw [hF]
    apply Nat.le_floor
    have h1 : ((H ∪ W1).card : ℝ) * (1 / I.q (I.M₁ hm)) ≤ L := by linarith
    rw [mul_one_div, div_le_iff₀ hq1] at h1
    exact h1
  rw [Finset.card_union_of_disjoint hdisjH1] at hcardA
  -- the family `H ∪ W2`
  have pairB : ∀ a ∈ H ∪ W2, ∀ b ∈ H ∪ W2, a ≠ b →
      σ.completion a ≤ σ.start b ∨ σ.completion b ≤ σ.start a := by
    intro a ha b hb hab
    rw [Finset.mem_union] at ha hb
    have haW : a ∈ W := ha.elim (fun h => hHW h) (fun h => hW2W h)
    have hbW : b ∈ W := hb.elim (fun h => hHW h) (fun h => hW2W h)
    by_cases hor : a ∈ H ∨ b ∈ H
    · exact hno a haW b hbW hab hor
    · push_neg at hor
      have ha2 : a ∈ W2 := ha.resolve_left hor.1
      have hb2 : b ∈ W2 := hb.resolve_left hor.2
      rw [hW2, Finset.mem_filter] at ha2 hb2
      have e1 := (mach_cases I hm (σ.machine a)).resolve_left ha2.2
      have e2 := (mach_cases I hm (σ.machine b)).resolve_left hb2.2
      exact hdisj a b hab (e1.trans e2.symm)
  have hB := disj_sum σ (H ∪ W2).card (H ∪ W2) le_rfl 0 L
    (fun y _ => hst y) (fun y _ => hLc y) pairB hL0
  rw [Finset.sum_union hdisjH2] at hB
  have hsH : (H.card : ℝ) * (1 / I.q (I.M₁ hm)) ≤ ∑ y ∈ H, I.procTime (σ.machine y) := by
    have h1 := Finset.card_nsmul_le_sum H (fun y => I.procTime (σ.machine y))
      (1 / I.q (I.M₁ hm)) (fun y _ => hlen y)
    rwa [nsmul_eq_mul] at h1
  have hW2len : ∀ y ∈ W2, 1 / I.q (I.M₂ hm) ≤ I.procTime (σ.machine y) := by
    intro y hy
    rw [hW2, Finset.mem_filter] at hy
    have e1 := (mach_cases I hm (σ.machine y)).resolve_left hy.2
    unfold Instance.procTime
    exact le_of_eq (by rw [e1])
  have hsW2 : (W2.card : ℝ) * (1 / I.q (I.M₂ hm)) ≤ ∑ y ∈ W2, I.procTime (σ.machine y) := by
    have h1 := Finset.card_nsmul_le_sum W2 (fun y => I.procTime (σ.machine y))
      (1 / I.q (I.M₂ hm)) hW2len
    rwa [nsmul_eq_mul] at h1
  have hnum : I.n - F - j ≤ W2.card := by omega
  have c1 : (D.card : ℝ) / I.q (I.M₁ hm) = (H.card : ℝ) * (1 / I.q (I.M₁ hm)) := by
    rw [hHcard, mul_one_div]
  have c2 : ((I.n - F - j : ℕ) : ℝ) / I.q (I.M₂ hm) ≤ (W2.card : ℝ) * (1 / I.q (I.M₂ hm)) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) hq2.le
  linarith

theorem main_bound (I : Instance) (hm : I.m = 2) (hl : I.l = 1) (ord : Fin I.n ≃ Fin I.n)
    (hord : Antitone fun p => I.r (I.R₁ hl) (ord p))
    (hfit : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl))
    (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm)) (σ : Schedule I) (hσ : σ.Feasible) :
    (Q2Algorithm.afterMoves I hm hl ord (Q2Algorithm.stopIndex I hm hl ord)).makespan
      ≤ σ.makespan := by
  have hL0 : 0 ≤ σ.makespan := makespan_nonneg σ hσ.1
  rcases Nat.eq_zero_or_pos I.n with hn | hn
  · exact makespan_le _ _ (fun j => absurd j.isLt (by omega)) hL0
  have hq1 := I.q_pos (I.M₁ hm)
  have hq2 := I.q_pos (I.M₂ hm)
  obtain ⟨L, hL⟩ : ∃ L, L = σ.makespan := ⟨_, rfl⟩
  rw [← hL] at hL0 ⊢
  have hLc : ∀ j, σ.completion j ≤ L := fun j => by rw [hL]; exact le_makespan σ j
  obtain ⟨F, hF⟩ : ∃ F, F = ⌊L * I.q (I.M₁ hm)⌋₊ := ⟨_, rfl⟩
  have hFle : (F : ℝ) / I.q (I.M₁ hm) ≤ L := by
    rw [div_le_iff₀ hq1, hF]
    exact Nat.floor_le (mul_nonneg hL0 hq1.le)
  have hKopt := stop_opt I hm hl ord hord hfit hn
  rcases le_or_gt I.n F with hnF | hnF
  · refine le_trans (hKopt 0 (Nat.zero_le _)) ?_
    rw [am_ms_eq I hm hl ord hord hfit hn 0 (Nat.zero_le _), m2End_zero, Nat.sub_zero]
    apply max_le
    · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hnF) hq1.le) hFle
    · exact hL0
  · obtain ⟨k, hk⟩ : ∃ k, k = I.n - F := ⟨_, rfl⟩
    refine le_trans (hKopt k (by omega)) ?_
    rw [am_ms_eq I hm hl ord hord hfit hn k (by omega)]
    apply max_le
    · rw [show I.n - k = F by omega]
      exact hFle
    · have ind : ∀ i, i ≤ k →
          Q2Algorithm.m2End I hm hl ord i + ((k - i : ℕ) : ℝ) / I.q (I.M₂ hm) ≤ L := by
        intro i
        induction i with
        | zero =>
          intro _
          rw [m2End_zero, zero_add, Nat.sub_zero]
          have h1 := key2 I hm hl ord hord hq σ hσ L hLc hL0 F hF 0 (by omega)
          rw [show I.n - F - 0 = k by omega] at h1
          exact le_trans (le_add_of_nonneg_left (div_nonneg (Nat.cast_nonneg _) hq1.le)) h1
        | succ i ih =>
          intro hi
          have h1 := ih (by omega)
          have h2 := key2 I hm hl ord hord hq σ hσ L hLc hL0 F hF i (by omega)
          rw [show I.n - F - i = k - i by omega] at h2
          rw [m2End_succ I hm hl ord i (by omega), movedStart_eq I hm hl ord hord hfit i (by omega)]
          have e1 : ((k - i : ℕ) : ℝ) = ((k - (i + 1) : ℕ) : ℝ) + 1 := by
            rw [← Nat.cast_add_one, show k - (i + 1) + 1 = k - i by omega]
          rw [e1, add_div] at h1 h2
          rcases le_total (Q2Algorithm.m2End I hm hl ord i)
              (((Dset I hl ord (I.n - 1 - i) (ord ⟨I.n - 1 - i, by omega⟩)).card : ℝ)
                / I.q (I.M₁ hm)) with hc | hc
          · rw [max_eq_right hc]
            linarith
          · rw [max_eq_left hc]
            linarith
      have h3 := ind k le_rfl
      rw [Nat.sub_self, Nat.cast_zero, zero_div, add_zero] at h3
      exact h3

end Aux_Q2ABC

open ResourceScheduling.Poly in
theorem solution (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (hprec : I.NoPrecedence) (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm)) (hfit : I.EveryJobFits)
    (ord : Fin I.n ≃ Fin I.n) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) :
    (q2Algorithm I hm hl ord).Feasible ∧ (q2Algorithm I hm hl ord).SatisfiesABC hm hl ∧
      ∀ σ : Schedule I, σ.Feasible → σ.SatisfiesABC hm hl →
        (q2Algorithm I hm hl ord).makespan ≤ σ.makespan := by
  have hfit' : ∀ j, I.r (I.R₁ hl) j ≤ I.s (I.R₁ hl) := fun j => hfit _ j
  refine ⟨Aux_Q2ABC.am_feasible I hm hl ord hprec hord hfit' (Q2Algorithm.stopIndex I hm hl ord),
    Aux_Q2ABC.am_abc I hm hl ord hord hfit' (Q2Algorithm.stopIndex I hm hl ord), ?_⟩
  intro σ hσ _
  exact Aux_Q2ABC.main_bound I hm hl ord hord hfit' hq σ hσ
