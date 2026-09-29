-- Prove2me | solution 1 for ResourceScheduling.Graph.paths_iff_q2Schedule
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:24:36.786086+00:00
-- url     : https://prove2.me/submissions/d1083293-8bb8-4c25-9772-25c9c918625c

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Construction



namespace ResourceScheduling.Graph

theorem rs_mem_nonEdge {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (p : Fin N × Fin N) :
    p ∈ nonEdgeList G ↔ p.1 < p.2 ∧ ¬ G.Adj p.1 p.2 := by
  obtain ⟨a, b⟩ := p
  simp [nonEdgeList]

theorem rs_feas_adj {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (y m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) (S : Finset (Fin N))
    (hS : ((construct G y).toInstance m q hq).ResourceFeasibleSet S)
    (j k : Fin N) (hj : j ∈ S) (hk : k ∈ S) (hjk : j ≠ k) : G.Adj j k := by
  have hS' : ∀ h : Fin (nonEdgeList G).length, ∑ i ∈ S,
      (if i = ((nonEdgeList G).get h).1 ∨ i = ((nonEdgeList G).get h).2 then 1 else 0) ≤ 1 := hS
  by_contra hadj
  have key : ∀ a b : Fin N, a ∈ S → b ∈ S → a < b → ¬ G.Adj a b → False := by
    intro a b ha hb hab hn
    have hm : (a, b) ∈ nonEdgeList G := (rs_mem_nonEdge G _).2 ⟨hab, hn⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hm
    have := hS' i
    rw [hi] at this
    have hsub : ({a, b} : Finset (Fin N)) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have h2 := Finset.sum_le_sum_of_subset (f := fun i : Fin N => if i = a ∨ i = b then 1 else 0) hsub
    rw [Finset.sum_pair (ne_of_lt hab)] at h2
    have hba : b ≠ a := (ne_of_lt hab).symm
    have e2 : ((if a = a ∨ a = b then 1 else 0) + (if b = a ∨ b = b then 1 else 0) : ℕ) = 2 := by
      simp
    simp only at this
    simp only [true_or, or_true, if_true] at h2
    omega
  rcases lt_or_gt_of_ne hjk with hlt | hlt
  · exact key j k hj hk hlt hadj
  · exact key k j hk hj hlt (fun h' => hadj h'.symm)

theorem rs_clique_feas {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (y m : ℕ) (q : Fin m → ℝ) (hq : ∀ i, 0 < q i) (S : Finset (Fin N))
    (hc : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → G.Adj j k) :
    ((construct G y).toInstance m q hq).ResourceFeasibleSet S := by
  show ∀ h : Fin (nonEdgeList G).length, ∑ i ∈ S,
      (if i = ((nonEdgeList G).get h).1 ∨ i = ((nonEdgeList G).get h).2 then 1 else 0) ≤ 1
  intro h
  have hm := (rs_mem_nonEdge G _).1 (List.get_mem (nonEdgeList G) h)
  obtain ⟨hlt, hn⟩ := hm
  set a := ((nonEdgeList G).get h).1
  set b := ((nonEdgeList G).get h).2
  rw [Finset.sum_boole]
  simp only [Nat.cast_id]
  apply Finset.card_le_one.2
  intro x hx z hz
  simp only [Finset.mem_filter] at hx hz
  by_contra hxz
  rcases hx with ⟨hxS, hx | hx⟩ <;> rcases hz with ⟨hzS, hz | hz⟩
  · exact hxz (hx.trans hz.symm)
  · subst hx hz; exact hn (hc _ hxS _ hzS hxz)
  · subst hx hz; exact hn (hc _ hzS _ hxS (Ne.symm hxz))
  · exact hxz (hx.trans hz.symm)

theorem rs_transgen_false {α : Type*} (j k : α) :
    ¬ Relation.TransGen (fun _ _ : α => False) j k := by
  intro h
  induction h with
  | single h => exact h
  | tail _ h _ => exact h

/-! Generic packing lemmas. -/

section Pack
variable {α : Type*} [Fintype α]

def RsPack (S : α → ℝ) (n : ℕ) : Prop :=
  (∀ j, 0 ≤ S j) ∧ (∀ j, S j + 1 ≤ n) ∧ (∀ j k, j ≠ k → S j + 1 ≤ S k ∨ S k + 1 ≤ S j)

theorem rs_ceil_lt (a : ℝ) (ha : -1 < a) : (⌈a⌉₊ : ℝ) < a + 1 := by
  rcases le_or_gt a 0 with h | h
  · simp [Nat.ceil_eq_zero.mpr h]; linarith
  · exact Nat.ceil_lt_add_one h.le

theorem rs_pack_index {S : α → ℝ} {n : ℕ} (hP : RsPack S n) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ g : α → Fin n, Function.Injective g ∧
      ∀ j, S j ≤ ((g j : ℕ) : ℝ) + δ ∧ ((g j : ℕ) : ℝ) + δ < S j + 1 := by
  obtain ⟨h0, h1, h2⟩ := hP
  have hlt : ∀ j, ⌈S j - δ⌉₊ < n := by
    intro j
    have := rs_ceil_lt (S j - δ) (by linarith [h0 j])
    have h' : (⌈S j - δ⌉₊ : ℝ) < n := by linarith [h1 j]
    exact_mod_cast h'
  have hcov : ∀ j, S j ≤ ((⌈S j - δ⌉₊ : ℕ) : ℝ) + δ ∧ ((⌈S j - δ⌉₊ : ℕ) : ℝ) + δ < S j + 1 := by
    intro j
    have a1 := Nat.le_ceil (S j - δ)
    have a2 := rs_ceil_lt (S j - δ) (by linarith [h0 j])
    constructor <;> linarith
  refine ⟨fun j => ⟨⌈S j - δ⌉₊, hlt j⟩, ?_, fun j => hcov j⟩
  intro j k hjk
  by_contra hne
  have e : ((⌈S j - δ⌉₊ : ℕ) : ℝ) = ((⌈S k - δ⌉₊ : ℕ) : ℝ) := by
    have := congrArg (fun x : Fin n => (x : ℕ)) hjk
    simp only at this
    rw [this]
  have cj := hcov j
  have ck := hcov k
  rcases h2 j k hne with h | h <;> linarith [cj.1, cj.2, ck.1, ck.2]

theorem rs_pack_card_le {S : α → ℝ} {n : ℕ} (hP : RsPack S n) : Fintype.card α ≤ n := by
  obtain ⟨g, hg, -⟩ := rs_pack_index hP 0 le_rfl one_pos
  simpa using Fintype.card_le_of_injective g hg

theorem rs_pack_cover {S : α → ℝ} {n : ℕ} (hP : RsPack S n) (hc : Fintype.card α = n)
    (p : ℝ) (hp0 : 0 ≤ p) (hpn : p < n) : ∃ j, S j ≤ p ∧ p < S j + 1 := by
  have hf1 := Nat.floor_le hp0
  have hf2 := Nat.lt_floor_add_one p
  obtain ⟨g, hg, hcov⟩ := rs_pack_index hP (p - ⌊p⌋₊) (by linarith) (by linarith)
  have hb : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by simp [hc]⟩
  have hm : ⌊p⌋₊ < n := (Nat.floor_lt hp0).2 hpn
  obtain ⟨j, hj⟩ := hb.2 ⟨⌊p⌋₊, hm⟩
  refine ⟨j, ?_⟩
  have := hcov j
  rw [hj] at this
  simp only at this
  constructor <;> linarith [this.1, this.2]

theorem rs_pack_int {S : α → ℝ} {n : ℕ} (hP : RsPack S n) (hc : Fintype.card α = n) :
    ∀ j, ∃ m : ℕ, S j = m := by
  classical
  by_contra hne
  push_neg at hne
  set T := Finset.univ.filter (fun j => ∀ m : ℕ, S j ≠ m) with hT
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨j, by simp [hT, hj]⟩
  obtain ⟨j, hjT, hmin⟩ := Finset.exists_min_image T S hTne
  have hjm : ∀ m : ℕ, S j ≠ m := by simpa [hT] using hjT
  obtain ⟨h0, h1, h2⟩ := hP
  have hF1 := Nat.floor_le (h0 j)
  have hF2 := Nat.lt_floor_add_one (S j)
  have hfpos : (⌊S j⌋₊ : ℝ) < S j := lt_of_le_of_ne hF1 (fun h => hjm _ h.symm)
  have hF0 : (0:ℝ) ≤ (⌊S j⌋₊ : ℝ) := Nat.cast_nonneg _
  obtain ⟨j', hj'1, hj'2⟩ := rs_pack_cover ⟨h0, h1, h2⟩ hc (S j - (S j - ⌊S j⌋₊) / 2)
    (by linarith) (by linarith [h1 j])
  have hne' : j' ≠ j := by
    rintro rfl; linarith
  have hlt : S j' + 1 ≤ S j := by
    rcases h2 j' j hne' with h | h
    · exact h
    · linarith
  have hj'T : j' ∈ T := by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    intro m hm
    rw [hm] at hlt hj'2
    have a : (m : ℝ) < (⌊S j⌋₊ : ℝ) := by linarith
    have a' : m < ⌊S j⌋₊ := by exact_mod_cast a
    have a'' : ((m + 1 : ℕ) : ℝ) ≤ (⌊S j⌋₊ : ℝ) := by exact_mod_cast a'
    push_cast at a''
    linarith
  have := hmin j' hj'T
  linarith

theorem rs_pack_equiv {S : α → ℝ} {n : ℕ} (hP : RsPack S n) (hc : Fintype.card α = n) :
    ∃ e : α ≃ Fin n, ∀ j, S j = ((e j : ℕ) : ℝ) := by
  choose m hm using rs_pack_int hP hc
  obtain ⟨h0, h1, h2⟩ := hP
  have hlt : ∀ j, m j < n := by
    intro j
    have := h1 j
    rw [hm j] at this
    have : ((m j + 1 : ℕ) : ℝ) ≤ n := by push_cast; exact this
    have : m j + 1 ≤ n := by exact_mod_cast this
    omega
  let g : α → Fin n := fun j => ⟨m j, hlt j⟩
  have hg : Function.Injective g := by
    intro j k hjk
    by_contra hne
    have e : m j = m k := congrArg (fun x : Fin n => (x : ℕ)) hjk
    have := h2 j k hne
    rw [hm j, hm k, e] at this
    rcases this with h | h <;> linarith
  have hb : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by simp [hc]⟩
  exact ⟨Equiv.ofBijective g hb, fun j => hm j⟩

end Pack

theorem rs_p3_compl (d : GraphData)
    (σ : Schedule ((reduce d).toInstance 3 (fun _ => 1) (fun _ => one_pos)))
    (j : Fin ((reduce d).toInstance 3 (fun _ => 1) (fun _ => one_pos)).n) :
    σ.completion j = σ.start j + 1 := by
  simp [Schedule.completion, Instance.procTime, ResDot11Data.toInstance]

theorem rs_mem_active {I : Instance} (σ : Schedule I) (τ : ℝ) (j : Fin I.n) :
    j ∈ σ.activeSet τ ↔ σ.start j ≤ τ ∧ τ < σ.completion j := by
  classical
  unfold Schedule.activeSet
  rw [Finset.mem_filter]
  simp [Schedule.IsExecutingAt]

theorem rs_makespan_le {I : Instance} (σ : Schedule I) (y : ℝ) (hy : 0 ≤ y)
    (h : ∀ j, σ.completion j ≤ y) : σ.makespan ≤ y := by
  unfold Schedule.makespan
  split_ifs with hn
  · exact Finset.sup'_le _ _ (fun j _ => h j)
  · exact hy

theorem rs_le_makespan {I : Instance} (σ : Schedule I) (j : Fin I.n) :
    σ.completion j ≤ σ.makespan := by
  unfold Schedule.makespan
  rw [dif_pos ⟨j, Finset.mem_univ _⟩]
  exact Finset.le_sup' _ (Finset.mem_univ j)

theorem rs_nat_eq_of_close (i i' : ℕ) (τ : ℝ) (h1 : (i : ℝ) ≤ τ) (h2 : τ < (i : ℝ) + 1)
    (h3 : (i' : ℝ) ≤ τ) (h4 : τ < (i' : ℝ) + 1) : i = i' := by
  have h1 : (i : ℝ) < i' + 1 := by linarith
  have h2 : (i' : ℝ) < i + 1 := by linarith
  have h1' : i < i' + 1 := by exact_mod_cast h1
  have h2' : i' < i + 1 := by exact_mod_cast h2
  omega

theorem rs_nat_sep (i i' : ℕ) (h : i ≠ i') : (i : ℝ) + 1 ≤ i' ∨ (i' : ℝ) + 1 ≤ i := by
  rcases lt_or_gt_of_ne h with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

theorem triangles_core (d : GraphData) :
    PartitionIntoTriangles d.G ↔
      ((reduce d).toInstance 3 (fun _ => 1) (fun _ => one_pos)).HasScheduleWithin d.t := by
  constructor
  · rintro ⟨place, hadj⟩
    let σ : Schedule ((reduce d).toInstance 3 (fun _ => 1) (fun _ => one_pos)) :=
      ⟨fun j => (place.symm j).2, fun j => (((place.symm j).1 : ℕ) : ℝ)⟩
    have hcomp := rs_p3_compl d σ
    have hst : ∀ i a, σ.start (place (i, a)) = ((i : ℕ) : ℝ) := by intro i a; simp [σ]
    have hmach : ∀ i a, σ.machine (place (i, a)) = a := by
      intro i a; show (place.symm (place (i, a))).2 = a; simp
    refine ⟨σ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro j; exact Nat.cast_nonneg _
    · intro j k hjk hm
      obtain ⟨⟨i, a⟩, rfl⟩ := place.surjective j
      obtain ⟨⟨i', b⟩, rfl⟩ := place.surjective k
      have e1 := hcomp (place (i, a))
      have e2 := hcomp (place (i', b))
      have s1 := hst i a
      have s2 := hst i' b
      rw [hmach, hmach] at hm
      subst hm
      have hii : (i : ℕ) ≠ i' := by
        intro h; exact hjk (by rw [Fin.ext h])
      rcases rs_nat_sep _ _ hii with h | h
      · left; linarith
      · right; linarith
    · intro j k h; exact absurd h (rs_transgen_false _ _)
    · intro τ
      apply rs_clique_feas
      intro j hj k hk hjk
      obtain ⟨⟨i, a⟩, rfl⟩ := place.surjective j
      obtain ⟨⟨i', b⟩, rfl⟩ := place.surjective k
      have hj' := (rs_mem_active σ τ _).1 hj
      have hk' := (rs_mem_active σ τ _).1 hk
      have e1 := hcomp (place (i, a))
      have e2 := hcomp (place (i', b))
      have s1 := hst i a
      have s2 := hst i' b
      have hii : i = i' := Fin.ext (rs_nat_eq_of_close _ _ τ (by linarith [hj'.1]) (by linarith [hj'.2])
        (by linarith [hk'.1]) (by linarith [hk'.2]))
      subst hii
      have hab : a ≠ b := by rintro rfl; exact hjk rfl
      exact hadj i a b hab
    · apply rs_makespan_le _ _ (Nat.cast_nonneg _)
      intro j
      obtain ⟨⟨i, a⟩, rfl⟩ := place.surjective j
      have e1 := hcomp (place (i, a))
      have s1 := hst i a
      have : (i : ℕ) + 1 ≤ d.t := i.isLt
      have : ((i : ℕ) : ℝ) + 1 ≤ d.t := by exact_mod_cast this
      linarith
  · rintro ⟨σ, ⟨h0, hov, -, hres⟩, hmk⟩
    have hcomp := rs_p3_compl d σ
    have hC : ∀ j, σ.start j + 1 ≤ d.t := by
      intro j
      have := (rs_le_makespan σ j).trans hmk
      linarith [hcomp j]
    have hlt : ∀ j, ⌈σ.start j⌉₊ < d.t := by
      intro j
      have := rs_ceil_lt (σ.start j) (by linarith [h0 j])
      have h' : (⌈σ.start j⌉₊ : ℝ) < d.t := by linarith [hC j]
      exact_mod_cast h'
    have hcov : ∀ j, σ.start j ≤ ((⌈σ.start j⌉₊ : ℕ) : ℝ) ∧
        ((⌈σ.start j⌉₊ : ℕ) : ℝ) < σ.completion j := by
      intro j
      rw [hcomp]
      exact ⟨Nat.le_ceil _, rs_ceil_lt _ (by linarith [h0 j])⟩
    let φ : Fin (3 * d.t) → Fin d.t × Fin 3 := fun j => (⟨⌈σ.start j⌉₊, hlt j⟩, σ.machine j)
    have hφ : Function.Injective φ := by
      intro j k hjk
      by_contra hne
      have hc1 : ⌈σ.start j⌉₊ = ⌈σ.start k⌉₊ :=
        congrArg (fun p : Fin d.t × Fin 3 => (p.1 : ℕ)) hjk
      have hc2 : σ.machine j = σ.machine k := congrArg (fun p : Fin d.t × Fin 3 => p.2) hjk
      have cj := hcov j
      have ck := hcov k
      rw [hc1] at cj
      rcases hov j k hne hc2 with h | h <;> linarith [cj.1, cj.2, ck.1, ck.2]
    have hb : Function.Bijective φ :=
      (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, by simp [mul_comm]⟩
    refine ⟨(Equiv.ofBijective φ hb).symm, ?_⟩
    intro i a b hab
    set j := (Equiv.ofBijective φ hb).symm (i, a) with hjdef
    set k := (Equiv.ofBijective φ hb).symm (i, b) with hkdef
    have hj : φ j = (i, a) := by rw [hjdef]; exact (Equiv.ofBijective φ hb).apply_symm_apply _
    have hk : φ k = (i, b) := by rw [hkdef]; exact (Equiv.ofBijective φ hb).apply_symm_apply _
    have hjk : j ≠ k := by
      intro h; rw [h, hk] at hj; exact hab (Prod.mk.inj hj).2.symm
    have hji : ⌈σ.start j⌉₊ = i := congrArg (fun p : Fin d.t × Fin 3 => (p.1 : ℕ)) hj
    have hki : ⌈σ.start k⌉₊ = i := congrArg (fun p : Fin d.t × Fin 3 => (p.1 : ℕ)) hk
    have cj := hcov j
    have ck := hcov k
    rw [hji] at cj
    rw [hki] at ck
    exact rs_feas_adj d.G d.t 3 (fun _ => 1) (fun _ => one_pos) (σ.activeSet (i : ℕ)) (hres _) j k
      ((rs_mem_active _ _ _).2 cj) ((rs_mem_active _ _ _).2 ck) hjk

abbrev RsI2 (d : GraphData) : Instance :=
  (reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)

def rsM {d : GraphData} (σ : Schedule (RsI2 d)) (j : Fin (RsI2 d).n) : Fin 2 := σ.machine j

theorem rs_q2_compl (d : GraphData)
    (σ : Schedule ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)))
    (j : Fin ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)).n) :
    σ.completion j = σ.start j + if rsM σ j = 0 then 1 / 2 else 1 := by
  have hm : rsM σ j = 0 ∨ rsM σ j = 1 := by
    generalize rsM σ j = x
    fin_cases x <;> simp
  unfold rsM at hm ⊢
  rcases hm with h | h
  · simp [Schedule.completion, Instance.procTime, ResDot11Data.toInstance, h]
  · simp [Schedule.completion, Instance.procTime, ResDot11Data.toInstance, h]

theorem rs_nat_le_or (i i' : ℕ) : (i : ℝ) ≤ i' ∨ (i' : ℝ) + 1 ≤ i := by
  rcases le_or_gt i i' with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

theorem paths_core (d : GraphData) :
    PartitionIntoPathsOfLength2 d.G ↔
      ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)).HasScheduleWithin
        d.t := by
  constructor
  · rintro ⟨F⟩
    have hcard : F.blockCount = d.t := by
      have := Fintype.card_congr F.place
      simp at this
      omega
    let σ : Schedule ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)) :=
      ⟨fun j => if (F.place.symm j).2 = 1 then (1 : Fin 2) else (0 : Fin 2),
       fun j => (((F.place.symm j).1 : ℕ) : ℝ) + if (F.place.symm j).2 = 2 then 1 / 2 else 0⟩
    have hcomp := rs_q2_compl d σ
    have hst : ∀ i a, σ.start (F.place (i, a)) = ((i : ℕ) : ℝ) + if a = 2 then 1 / 2 else 0 := by
      intro i a; show (((F.place.symm (F.place (i, a))).1 : ℕ) : ℝ) + _ = _; simp
    have hmach : ∀ i a, rsM σ (F.place (i, a)) = if a = 1 then 1 else 0 := by
      intro i a; show (if (F.place.symm (F.place (i, a))).2 = 1 then (1 : Fin 2) else (0 : Fin 2)) = _; simp
    have key : ∀ (i : Fin F.blockCount) (a : Fin 3), ((i : ℕ) : ℝ) ≤ σ.start (F.place (i, a)) ∧
        σ.completion (F.place (i, a)) ≤ ((i : ℕ) : ℝ) + 1 ∧
        (a = 0 → σ.completion (F.place (i, a)) = ((i : ℕ) : ℝ) + 1 / 2) ∧
        (a = 2 → σ.start (F.place (i, a)) = ((i : ℕ) : ℝ) + 1 / 2) := by
      intro i a
      have e1 := hcomp (F.place (i, a))
      rw [hst, hmach] at e1
      rw [hst]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> fin_cases a <;> simp at e1 ⊢ <;> linarith
    refine ⟨σ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro j
      obtain ⟨⟨i, a⟩, rfl⟩ := F.place.surjective j
      linarith [(key i a).1, show (0:ℝ) ≤ ((i : ℕ) : ℝ) from Nat.cast_nonneg _]
    · intro j k hjk hm
      obtain ⟨⟨i, a⟩, rfl⟩ := F.place.surjective j
      obtain ⟨⟨i', b⟩, rfl⟩ := F.place.surjective k
      have e1 := hcomp (F.place (i, a))
      have e2 := hcomp (F.place (i', b))
      have s1 := hst i a
      have s2 := hst i' b
      change rsM σ _ = rsM σ _ at hm
      rw [hmach, hmach] at hm
      rw [hmach] at e1 e2
      have hne : (i, a) ≠ (i', b) := fun h => hjk (by rw [h])
      rcases rs_nat_le_or i i' with h | h <;> rcases rs_nat_le_or i' i with h' | h' <;>
        fin_cases a <;> fin_cases b <;> simp at hm e1 e2 s1 s2 hne ⊢ <;>
        first
        | (left; linarith)
        | (right; linarith)
        | (exfalso; exact hne (Fin.ext (by
              have : ((i : ℕ) : ℝ) = (i' : ℕ) := le_antisymm h h'
              exact_mod_cast this)))
        | skip
    · intro j k h; exact absurd h (rs_transgen_false _ _)
    · intro τ
      apply rs_clique_feas
      intro j hj k hk hjk
      obtain ⟨⟨i, a⟩, rfl⟩ := F.place.surjective j
      obtain ⟨⟨i', b⟩, rfl⟩ := F.place.surjective k
      have hj' := (rs_mem_active σ τ _).1 hj
      have hk' := (rs_mem_active σ τ _).1 hk
      have ka := key i a
      have kb := key i' b
      have hii : i = i' := Fin.ext (rs_nat_eq_of_close _ _ τ (by linarith) (by linarith)
        (by linarith) (by linarith))
      subst hii
      have hab : a ≠ b := by rintro rfl; exact hjk rfl
      fin_cases a <;> fin_cases b <;> simp at hab ka kb hj' hk' ⊢
      · exact F.edge01 i
      · exfalso; linarith
      · exact (F.edge01 i).symm
      · exact F.edge12 i
      · exfalso; linarith
      · exact (F.edge12 i).symm
    · apply rs_makespan_le _ _ (Nat.cast_nonneg _)
      intro j
      obtain ⟨⟨i, a⟩, rfl⟩ := F.place.surjective j
      have := (key i a).2.1
      have h1 : (i : ℕ) + 1 ≤ d.t := by have := i.isLt; omega
      have h2 : ((i : ℕ) : ℝ) + 1 ≤ d.t := by exact_mod_cast h1
      linarith
  · rintro ⟨σ, ⟨h0, hov, -, hres⟩, hmk⟩
    have hcomp := rs_q2_compl d σ
    have hC : ∀ j, σ.completion j ≤ d.t := fun j => (rs_le_makespan σ j).trans hmk
    let α0 := {j : Fin (RsI2 d).n // rsM σ j = 0}
    let α1 := {j : Fin (RsI2 d).n // ¬ rsM σ j = 0}
    have hm1 : ∀ j, ¬ rsM σ j = 0 → rsM σ j = 1 := by
      intro j h
      generalize rsM σ j = x at h ⊢
      fin_cases x <;> simp_all
    have hP0 : RsPack (fun j : α0 => 2 * σ.start j.1) (2 * d.t) := by
      refine ⟨fun j => by linarith [h0 j.1], fun j => ?_, fun j k hjk => ?_⟩
      · have := hC j.1
        rw [hcomp, if_pos j.2] at this
        push_cast; linarith
      · have hne : j.1 ≠ k.1 := fun h => hjk (Subtype.ext h)
        have hm : σ.machine j.1 = σ.machine k.1 := by
          have := j.2.trans k.2.symm
          exact this
        have e1 := hcomp j.1
        have e2 := hcomp k.1
        rw [if_pos j.2] at e1
        rw [if_pos k.2] at e2
        rcases hov _ _ hne hm with h | h
        · left; linarith
        · right; linarith
    have hP1 : RsPack (fun j : α1 => σ.start j.1) d.t := by
      refine ⟨fun j => h0 j.1, fun j => ?_, fun j k hjk => ?_⟩
      · have := hC j.1
        rw [hcomp, if_neg j.2] at this
        linarith
      · have hne : j.1 ≠ k.1 := fun h => hjk (Subtype.ext h)
        have hm : σ.machine j.1 = σ.machine k.1 := by
          have := (hm1 _ j.2).trans (hm1 _ k.2).symm
          exact this
        have e1 := hcomp j.1
        have e2 := hcomp k.1
        rw [if_neg j.2] at e1
        rw [if_neg k.2] at e2
        rcases hov _ _ hne hm with h | h
        · left; linarith
        · right; linarith
    have c0 := rs_pack_card_le hP0
    have c1 := rs_pack_card_le hP1
    have c01 : Fintype.card α1 = 3 * d.t - Fintype.card α0 := by
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_fin]
      rfl
    have hc0 : Fintype.card α0 = 2 * d.t := by omega
    have hc1 : Fintype.card α1 = d.t := by omega
    obtain ⟨e0, he0⟩ := rs_pack_equiv hP0 hc0
    obtain ⟨e1, he1⟩ := rs_pack_equiv hP1 hc1
    let ψ : Fin d.t × Fin 3 → Fin (2 * d.t) ⊕ Fin d.t := fun p =>
      if p.2 = 0 then Sum.inl ⟨2 * p.1, by have := p.1.isLt; omega⟩
      else if p.2 = 1 then Sum.inr p.1
      else Sum.inl ⟨2 * p.1 + 1, by have := p.1.isLt; omega⟩
    have hψ : Function.Injective ψ := by
      rintro ⟨i, a⟩ ⟨i', b⟩ h
      fin_cases a <;> fin_cases b <;> simp [ψ] at h ⊢ <;> omega
    let E : Fin (2 * d.t) ⊕ Fin d.t ≃ Fin (RsI2 d).n :=
      (e0.sumCongr e1).symm.trans (Equiv.sumCompl (fun j => rsM σ j = 0))
    let φ : Fin d.t × Fin 3 → Fin (3 * d.t) := fun p => E (ψ p)
    have hφ : Function.Injective φ := E.injective.comp hψ
    have hb : Function.Bijective φ :=
      (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, by simp [mul_comm]⟩
    have hE0 : ∀ x, E (Sum.inl x) = (e0.symm x).1 := fun x => rfl
    have hE1 : ∀ x, E (Sum.inr x) = (e1.symm x).1 := fun x => rfl
    have hfeas := fun (τ : ℝ) (j k : Fin (3 * d.t)) (hj : σ.start j ≤ τ ∧ τ < σ.completion j)
        (hk : σ.start k ≤ τ ∧ τ < σ.completion k) (hjk : j ≠ k) =>
      rs_feas_adj d.G d.t 2 ![2, 1] (by intro i; fin_cases i <;> norm_num) (σ.activeSet τ) (hres _) j k
        ((rs_mem_active _ _ _).2 hj) ((rs_mem_active _ _ _).2 hk) hjk
    -- facts about the three kinds of jobs
    have fL : ∀ i : Fin d.t, ∀ x : Fin (2 * d.t), (x : ℕ) = 2 * i →
        σ.start (e0.symm x).1 = (i : ℕ) ∧ σ.completion (e0.symm x).1 = (i : ℕ) + 1 / 2 := by
      intro i x hx
      have h1 := he0 (e0.symm x)
      rw [Equiv.apply_symm_apply, hx] at h1
      push_cast at h1
      have h2 := hcomp (e0.symm x).1
      rw [if_pos (e0.symm x).2] at h2
      constructor <;> linarith
    have fR : ∀ i : Fin d.t, ∀ x : Fin (2 * d.t), (x : ℕ) = 2 * i + 1 →
        σ.start (e0.symm x).1 = (i : ℕ) + 1 / 2 ∧ σ.completion (e0.symm x).1 = (i : ℕ) + 1 := by
      intro i x hx
      have h1 := he0 (e0.symm x)
      rw [Equiv.apply_symm_apply, hx] at h1
      push_cast at h1
      have h2 := hcomp (e0.symm x).1
      rw [if_pos (e0.symm x).2] at h2
      constructor <;> linarith
    have fC : ∀ i : Fin d.t,
        σ.start (e1.symm i).1 = (i : ℕ) ∧ σ.completion (e1.symm i).1 = (i : ℕ) + 1 := by
      intro i
      have h1 := he1 (e1.symm i)
      rw [Equiv.apply_symm_apply] at h1
      have h2 := hcomp (e1.symm i).1
      rw [if_neg (e1.symm i).2] at h2
      constructor <;> linarith
    refine ⟨⟨d.t, Equiv.ofBijective φ hb, ?_, ?_⟩⟩
    · intro i
      show d.G.Adj (E (ψ (i, 0))) (E (ψ (i, 1)))
      have p0 : ψ (i, 0) = Sum.inl ⟨2 * i, by have := i.isLt; omega⟩ := by simp [ψ]
      have p1 : ψ (i, 1) = Sum.inr i := by simp [ψ]
      rw [p0, p1, hE0, hE1]
      obtain ⟨a1, a2⟩ := fL i ⟨2 * i, by have := i.isLt; omega⟩ rfl
      obtain ⟨b1, b2⟩ := fC i
      refine hfeas (i : ℕ) _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_
      intro h
      have := (e0.symm ⟨2 * i, by have := i.isLt; omega⟩).2
      rw [h] at this
      exact (e1.symm i).2 this
    · intro i
      show d.G.Adj (E (ψ (i, 1))) (E (ψ (i, 2)))
      have p2 : ψ (i, 2) = Sum.inl ⟨2 * i + 1, by have := i.isLt; omega⟩ := by simp [ψ]
      have p1 : ψ (i, 1) = Sum.inr i := by simp [ψ]
      rw [p2, p1, hE0, hE1]
      obtain ⟨a1, a2⟩ := fR i ⟨2 * i + 1, by have := i.isLt; omega⟩ rfl
      obtain ⟨b1, b2⟩ := fC i
      refine hfeas ((i : ℕ) + 1 / 2) _ _ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ ?_
      intro h
      have := (e0.symm ⟨2 * i + 1, by have := i.isLt; omega⟩).2
      rw [← h] at this
      exact (e1.symm i).2 this

end ResourceScheduling.Graph

open ResourceScheduling.Graph


theorem solution (d : GraphData) :
    PartitionIntoPathsOfLength2 d.G ↔
      ((reduce d).toInstance 2 ![2, 1] (by intro i; fin_cases i <;> norm_num)).HasScheduleWithin
        d.t := by
  exact paths_core d
