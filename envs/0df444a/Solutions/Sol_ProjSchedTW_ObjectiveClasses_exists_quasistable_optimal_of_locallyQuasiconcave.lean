-- Prove2me | solution 1 for ProjSchedTW.ObjectiveClasses.exists_quasistable_optimal_of_locallyQuasiconcave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T20:04:29.672028+00:00
-- url     : https://prove2.me/submissions/916c95cc-df1b-4bfd-9ade-c6a73b52c7ae

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

set_option autoImplicit false

namespace P5884ced4

open ProjSchedTW.ObjectiveClasses

theorem mem_active {n : ℕ} {K : Type} (P : Project n K) (S : Fin (n + 2) → ℝ) (t : ℝ)
    (i : Fin (n + 2)) : i ∈ activeSet P S t ↔ S i ≤ t ∧ t < S i + (P.p i : ℝ) := by
  simp [activeSet]

/-! ### Q2: the schedule polytope of a feasible schedule is feasible -/

theorem usage_le {n : ℕ} {K : Type} (P : Project n K) (S1 S2 : Fin (n + 2) → ℝ)
    (h : ∀ i j, i ≠ j → S2 i + (P.p i : ℝ) ≤ S2 j → S1 i + (P.p i : ℝ) ≤ S1 j)
    (h2 : ∀ i, 0 ≤ S2 i) (hR : S2 ∈ resourceFeasibleSet P) (k : K) (t : ℝ) :
    usage P S1 k t ≤ P.R k := by
  by_cases hA : (activeSet P S1 t).Nonempty
  · obtain ⟨j, hjA, hj⟩ := Finset.exists_max_image (activeSet P S1 t) S2 hA
    have hsub : activeSet P S1 t ⊆ activeSet P S2 (S2 j) := by
      intro i hi
      have hi' := (mem_active P S1 t i).1 hi
      have hjA' := (mem_active P S1 t j).1 hjA
      rw [mem_active]
      refine ⟨hj i hi, ?_⟩
      by_contra hc0
      have hc := not_lt.mp hc0
      by_cases hij : i = j
      · subst hij
        linarith [hi'.1, hi'.2]
      · have := h i j hij hc
        linarith [hjA'.1, hi'.2]
    calc usage P S1 k t ≤ usage P S2 k (S2 j) := Finset.sum_le_sum_of_subset hsub
      _ ≤ P.R k := hR.2.2 k (S2 j) (h2 j)
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    simp [usage, hA]

theorem orderPolytope_subset {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    orderPolytope P (scheduleOrder P S) ⊆ feasibleSet P := by
  intro X hX
  refine ⟨hX.1, hX.1.1, hX.1.2.1, fun k t _ => ?_⟩
  exact usage_le P X S (fun i j hij hle => hX.2 (i, j) ⟨hij, hle⟩) hS.1.2.1 hS.2 k t

theorem self_mem_orderPolytope {n : ℕ} {K : Type} (P : Project n K)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ timeFeasibleSet P) :
    S ∈ orderPolytope P (scheduleOrder P S) :=
  ⟨hS, fun e he => he.2⟩

/-! ### boundedness and compactness -/

theorem walk_le {n : ℕ} {K : Type} (P : Project n K) (X : Fin (n + 2) → ℝ)
    (hX : X ∈ timeFeasibleSet P) {i j : Fin (n + 2)} {w : ℤ}
    (hw : NetworkWalk P.E P.δ i j w) : (w : ℝ) ≤ X j - X i := by
  induction hw with
  | refl => simp
  | step _ hE ih =>
    have := hX.2.2 _ hE
    push_cast
    simp only at this
    linarith

theorem le_dbar {n : ℕ} {K : Type} (P : Project n K) (X : Fin (n + 2) → ℝ)
    (hX : X ∈ timeFeasibleSet P) (i : Fin (n + 2)) : X i ≤ P.dbar := by
  obtain ⟨w, hpw, hw⟩ := P.path_to_last i
  have h1 := walk_le P X hX hw
  have h2 := hX.2.2 _ P.back_arc
  simp only [P.back_weight] at h2
  have h3 : (0 : ℝ) ≤ w := by exact_mod_cast le_trans (by positivity) hpw
  have h0 := hX.1
  push_cast at h2
  linarith

theorem orderPolytope_isCompact {n : ℕ} {K : Type} (P : Project n K)
    (O : Set (Fin (n + 2) × Fin (n + 2))) : IsCompact (orderPolytope P O) := by
  have hsub : orderPolytope P O ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) P.dbar) := by
    intro X hX i _
    exact ⟨hX.1.2.1 i, le_dbar P X hX.1 i⟩
  have hcl : IsClosed (orderPolytope P O) := by
    have : orderPolytope P O = {X : Fin (n + 2) → ℝ | X 0 = 0} ∩ (⋂ i, {X | 0 ≤ X i}) ∩
        (⋂ e ∈ P.E, {X | (P.δ e.1 e.2 : ℝ) ≤ X e.2 - X e.1}) ∩
        (⋂ e ∈ O, {X | X e.1 + (P.p e.1 : ℝ) ≤ X e.2}) := by
      ext X
      simp [orderPolytope, timeFeasibleSet, and_assoc]
    rw [this]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · exact isClosed_eq (continuous_apply 0) continuous_const
    · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_biInter fun e _ => isClosed_le continuous_const
        ((continuous_apply e.2).sub (continuous_apply e.1))
    · exact isClosed_biInter fun e _ => isClosed_le
        ((continuous_apply e.1).add continuous_const) (continuous_apply e.2)
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

theorem feasibleSet_isCompact {n : ℕ} {K : Type} (P : Project n K) :
    IsCompact (feasibleSet P) := by
  have hcov : feasibleSet P =
      ⋃ O ∈ (scheduleOrder P '' feasibleSet P), orderPolytope P O := by
    ext X
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · intro hX
      exact ⟨scheduleOrder P X, ⟨X, hX, rfl⟩, self_mem_orderPolytope P X hX.1⟩
    · rintro ⟨O, ⟨S, hS, rfl⟩, hX⟩
      exact orderPolytope_subset P S hS hX
  rw [hcov]
  exact (Set.toFinite _).isCompact_biUnion fun O _ => orderPolytope_isCompact P O

/-! ### constraints -/

abbrev Cn (n : ℕ) := (Fin (n + 2) × Fin (n + 2)) ⊕ Fin (n + 2) ⊕ (Fin (n + 2) × Fin (n + 2))

def ca {n : ℕ} : Cn n → Fin (n + 2)
  | Sum.inl e => e.1
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr e) => e.1

def cb {n : ℕ} : Cn n → Fin (n + 2)
  | Sum.inl e => e.2
  | Sum.inr (Sum.inl i) => i
  | Sum.inr (Sum.inr e) => e.2

def cw {n : ℕ} {K : Type} (P : Project n K) : Cn n → ℝ
  | Sum.inl e => (P.δ e.1 e.2 : ℝ)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr e) => (P.p e.1 : ℝ)

def cvalid {n : ℕ} {K : Type} (P : Project n K) : Cn n → Prop
  | Sum.inl e => e ∈ P.E
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr e) => e.1 ≠ e.2

def cv {n : ℕ} {K : Type} (P : Project n K) (c : Cn n) (X : Fin (n + 2) → ℝ) : ℝ :=
  X (cb c) - X (ca c) - cw P c

open Classical in
noncomputable def tight {n : ℕ} {K : Type} (P : Project n K) (X : Fin (n + 2) → ℝ) :
    Finset (Cn n) :=
  Finset.univ.filter (fun c => cvalid P c ∧ cv P c X = 0)

theorem mem_tight {n : ℕ} {K : Type} (P : Project n K) (X : Fin (n + 2) → ℝ) (c : Cn n) :
    c ∈ tight P X ↔ cvalid P c ∧ cv P c X = 0 := by
  simp [tight]

theorem cv_line {n : ℕ} {K : Type} (P : Project n K) (c : Cn n) (S d : Fin (n + 2) → ℝ)
    (t : ℝ) : cv P c (S + t • d) = cv P c S + t * (d (cb c) - d (ca c)) := by
  simp only [cv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- sign facts of a constraint along the line. -/
theorem sign_fact {n : ℕ} {K : Type} (P : Project n K) (S Y : Fin (n + 2) → ℝ)
    (hS : S ∈ timeFeasibleSet P) (hY : Y ∈ orderPolytope P (scheduleOrder P S))
    (c : Cn n) (hc : cvalid P c) :
    (0 ≤ cv P c S ∧ 0 ≤ cv P c Y) ∨ cv P c S < 0 := by
  rcases c with e | i | e
  · left
    have h1 := hS.2.2 e hc
    have h2 := hY.1.2.2 e hc
    simp only [cv, ca, cb, cw]
    constructor <;> linarith
  · left
    simp only [cv, ca, cb, cw, hS.1, hY.1.1]
    constructor <;> linarith [hS.2.1 i, hY.1.2.1 i]
  · by_cases h : S e.1 + (P.p e.1 : ℝ) ≤ S e.2
    · left
      have h2 := hY.2 e ⟨hc, h⟩
      simp only [cv, ca, cb, cw]
      constructor <;> linarith
    · right
      simp only [cv, ca, cb, cw]
      linarith [not_le.mp h]

/-! ### abstract root lemma -/

theorem prod_nonneg_of {a b t r : ℝ} (hab : a * b < 0) (hr : r = -a / b) (ht : t ≤ r) :
    0 ≤ a * (a + t * b) := by
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  rcases lt_or_gt_of_ne hb with hb | hb
  · have ha : 0 < a := by nlinarith
    rw [hr, le_div_iff_of_neg hb] at ht
    nlinarith
  · have ha : a < 0 := by nlinarith
    rw [hr, le_div_iff₀ hb] at ht
    nlinarith

theorem prod_pos_of {a b t r : ℝ} (hab : a * b < 0) (hr : r = -a / b) (ht : t < r) :
    0 < a * (a + t * b) := by
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  rcases lt_or_gt_of_ne hb with hb | hb
  · have ha : 0 < a := by nlinarith
    rw [hr, lt_div_iff_of_neg hb] at ht
    nlinarith
  · have ha : a < 0 := by nlinarith
    rw [hr, lt_div_iff₀ hb] at ht
    nlinarith

theorem root_pos {a b : ℝ} (hab : a * b < 0) : 0 < -a / b := by
  have hb : b ≠ 0 := by rintro rfl; simp at hab
  rcases lt_or_gt_of_ne hb with hb | hb
  · have ha : 0 < a := by nlinarith
    exact div_pos_of_neg_of_neg (by linarith) hb
  · have ha : a < 0 := by nlinarith
    exact div_pos (by linarith) hb

/-! ### half line step -/

open Classical in
theorem half_step {n : ℕ} {K : Type} (P : Project n K) (S d : Fin (n + 2) → ℝ)
    (hS : S ∈ timeFeasibleSet P) (hd : d ≠ 0) (μ₁ μ₂ : ℝ) (h₁ : 0 < μ₁) (h₂ : μ₂ < 0)
    (hY₁ : S + μ₁ • d ∈ orderPolytope P (scheduleOrder P S))
    (hY₂ : S + μ₂ • d ∈ orderPolytope P (scheduleOrder P S)) :
    ∃ tu : ℝ, 0 < tu ∧ (∀ t, 0 ≤ t → t < tu → S + t • d ∈ equalOrderSet P S) ∧
      S + tu • d ∈ orderPolytope P (scheduleOrder P S) ∧ tight P S ⊂ tight P (S + tu • d) := by
  set α : Cn n → ℝ := fun c => cv P c S with hα
  set β : Cn n → ℝ := fun c => d (cb c) - d (ca c) with hβ
  have hline : ∀ c t, cv P c (S + t • d) = α c + t * β c := fun c t => cv_line P c S d t
  have hd0 : d 0 = 0 := by
    have h1 := hY₁.1.1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hS.1] at h1
    rcases mul_eq_zero.mp (by linarith : μ₁ * d 0 = 0) with h | h
    · linarith
    · exact h
  -- (A) sign facts
  have hA : ∀ c, cvalid P c →
      (0 ≤ α c ∧ 0 ≤ α c + μ₁ * β c ∧ 0 ≤ α c + μ₂ * β c) ∨ α c < 0 := by
    intro c hc
    rcases sign_fact P S _ hS hY₁ c hc with h | h
    · rcases sign_fact P S _ hS hY₂ c hc with h' | h'
      · left
        rw [hline] at h h'
        exact ⟨h.1, h.2, h'.2⟩
      · right; exact h'
    · right; exact h
  have hB : ∀ c, cvalid P c → α c = 0 → β c = 0 := by
    intro c hc h0
    rcases hA c hc with h | h
    · rw [h0] at h
      have e1 : 0 ≤ μ₁ * β c := by linarith [h.2.1]
      have e2 : 0 ≤ μ₂ * β c := by linarith [h.2.2]
      rcases lt_trichotomy (β c) 0 with hb | hb | hb
      · nlinarith
      · exact hb
      · nlinarith
    · linarith
  -- (J) a positive root exists
  have hJ : ∃ c, cvalid P c ∧ α c * β c < 0 := by
    by_contra hno
    push_neg at hno
    -- every point S + t • d, t ≥ 0, is time-feasible
    have hT : ∀ t : ℝ, 0 ≤ t → S + t • d ∈ timeFeasibleSet P := by
      intro t ht
      have key : ∀ c, cvalid P c → 0 ≤ α c → 0 ≤ cv P c (S + t • d) := by
        intro c hc hα0
        rw [hline]
        rcases eq_or_lt_of_le hα0 with h | h
        · rw [← h, hB c hc h.symm]; simp
        · have := hno c hc
          have : 0 ≤ β c := by
            by_contra hneg; push_neg at hneg; nlinarith
          positivity
      refine ⟨?_, ?_, ?_⟩
      · simp [hS.1, hd0]
      · intro i
        have := key (Sum.inr (Sum.inl i)) trivial (by
          simp only [hα, cv, ca, cb, cw, hS.1]; linarith [hS.2.1 i])
        simp only [cv, ca, cb, cw] at this
        have h0 : (S + t • d) 0 = 0 := by simp [hS.1, hd0]
        rw [h0] at this
        linarith
      · intro e he
        have := key (Sum.inl e) he (by
          simp only [hα, cv, ca, cb, cw]; linarith [hS.2.2 e he])
        simp only [cv, ca, cb, cw] at this
        linarith
    apply hd
    funext i
    have hup : ∀ t : ℝ, 0 ≤ t → S i + t * d i ≤ P.dbar := by
      intro t ht
      have := le_dbar P _ (hT t ht) i
      simpa using this
    have hlo : ∀ t : ℝ, 0 ≤ t → 0 ≤ S i + t * d i := by
      intro t ht
      have := (hT t ht).2.1 i
      simpa using this
    rcases lt_trichotomy (d i) 0 with h | h | h
    · exfalso
      have := hlo ((S i + 1) / (-d i)) (div_nonneg (by linarith [hS.2.1 i]) (by linarith))
      have hne : d i ≠ 0 := h.ne
      have e : (S i + 1) / (-d i) * d i = -(S i + 1) := by field_simp
      linarith
    · simpa using h
    · exfalso
      have := hup (((P.dbar : ℝ) + 1) / d i) (div_nonneg (by positivity) h.le)
      have hne : d i ≠ 0 := h.ne'
      have e : ((P.dbar : ℝ) + 1) / d i * d i = P.dbar + 1 := by field_simp
      have := hS.2.1 i
      linarith
  -- the first root
  set J := Finset.univ.filter (fun c => cvalid P c ∧ α c * β c < 0) with hJdef
  have hJne : J.Nonempty := by
    obtain ⟨c, hc⟩ := hJ
    exact ⟨c, by simp [hJdef, hc]⟩
  set tu := J.inf' hJne (fun c => -α c / β c) with htu
  have hJmem : ∀ c, c ∈ J ↔ cvalid P c ∧ α c * β c < 0 := by
    intro c; simp [hJdef]
  have htu_le : ∀ c, cvalid P c → α c * β c < 0 → tu ≤ -α c / β c := by
    intro c hc h
    exact Finset.inf'_le _ ((hJmem c).2 ⟨hc, h⟩)
  obtain ⟨c₀, hc₀J, hc₀⟩ := Finset.exists_mem_eq_inf' hJne (fun c => -α c / β c)
  have hc₀' := (hJmem c₀).1 hc₀J
  have htu_pos : 0 < tu := by
    rw [htu, hc₀]; exact root_pos hc₀'.2
  -- monotone facts
  have M0 : ∀ c, cvalid P c → ∀ t, 0 ≤ t → t ≤ tu → 0 ≤ α c * (α c + t * β c) := by
    intro c hc t ht htu'
    by_cases h : α c * β c < 0
    · exact prod_nonneg_of h rfl (le_trans htu' (htu_le c hc h))
    · push_neg at h
      nlinarith [sq_nonneg (α c)]
  have M0' : ∀ c, cvalid P c → α c ≠ 0 → ∀ t, 0 ≤ t → t < tu →
      0 < α c * (α c + t * β c) := by
    intro c hc hne t ht htu'
    by_cases h : α c * β c < 0
    · exact prod_pos_of h rfl (lt_of_lt_of_le htu' (htu_le c hc h))
    · push_neg at h
      have : 0 < α c * α c := mul_self_pos.mpr hne
      nlinarith
  have M1 : ∀ c, cvalid P c → 0 ≤ α c → ∀ t, 0 ≤ t → t ≤ tu → 0 ≤ cv P c (S + t • d) := by
    intro c hc hα0 t ht htu'
    rw [hline]
    rcases eq_or_lt_of_le hα0 with h | h
    · rw [← h, hB c hc h.symm]; simp
    · have := M0 c hc t ht htu'
      by_contra hh; push_neg at hh; nlinarith
  have M2 : ∀ c, cvalid P c → α c < 0 → ∀ t, 0 ≤ t → t < tu → cv P c (S + t • d) < 0 := by
    intro c hc hα0 t ht htu'
    rw [hline]
    have := M0' c hc hα0.ne t ht htu'
    by_contra hh; push_neg at hh; nlinarith
  -- membership in the order polytope on [0, tu]
  have hpoly : ∀ t, 0 ≤ t → t ≤ tu → S + t • d ∈ orderPolytope P (scheduleOrder P S) := by
    intro t ht htu'
    have h0 : (S + t • d) 0 = 0 := by simp [hS.1, hd0]
    refine ⟨⟨h0, ?_, ?_⟩, ?_⟩
    · intro i
      have := M1 (Sum.inr (Sum.inl i)) trivial (by
        simp only [hα, cv, ca, cb, cw, hS.1]; linarith [hS.2.1 i]) t ht htu'
      simp only [cv, ca, cb, cw] at this
      rw [h0] at this
      linarith
    · intro e he
      have := M1 (Sum.inl e) he (by
        simp only [hα, cv, ca, cb, cw]; linarith [hS.2.2 e he]) t ht htu'
      simp only [cv, ca, cb, cw] at this
      linarith
    · intro e he
      have := M1 (Sum.inr (Sum.inr e)) he.1 (by
        simp only [hα, cv, ca, cb, cw]; linarith [he.2]) t ht htu'
      simp only [cv, ca, cb, cw] at this
      linarith
  refine ⟨tu, htu_pos, ?_, hpoly tu htu_pos.le le_rfl, ?_⟩
  · intro t ht htu'
    refine ⟨hpoly t ht htu'.le, ?_⟩
    ext e
    constructor
    · intro he
      by_contra hn
      have hlt : α (Sum.inr (Sum.inr e)) < 0 := by
        simp only [hα, cv, ca, cb, cw]
        have : ¬ (S e.1 + (P.p e.1 : ℝ) ≤ S e.2) := fun h => hn ⟨he.1, h⟩
        linarith [not_le.mp this]
      have := M2 (Sum.inr (Sum.inr e)) he.1 hlt t ht htu'
      simp only [cv, ca, cb, cw] at this
      linarith [he.2]
    · intro he
      exact ⟨he.1, (hpoly t ht htu'.le).2 e he⟩
  · rw [Finset.ssubset_iff_of_subset]
    · refine ⟨c₀, ?_, ?_⟩
      · rw [mem_tight, hline]
        refine ⟨hc₀'.1, ?_⟩
        rw [htu, hc₀]
        have hb : β c₀ ≠ 0 := by rintro h; rw [h] at hc₀'; simp at hc₀'
        field_simp
        ring
      · rw [mem_tight]
        rintro ⟨-, h⟩
        have : α c₀ = 0 := h
        rw [this] at hc₀'
        simp at hc₀'
    · intro c hc
      rw [mem_tight] at hc ⊢
      refine ⟨hc.1, ?_⟩
      rw [hline, hB c hc.1 hc.2]
      simpa using hc.2

/-! ### Q4: lsc + quasiconcavity on a segment -/

open Filter Topology in
theorem seg {n : ℕ} {K : Type} (P : Project n K) (f : (Fin (n + 2) → ℝ) → ℝ)
    (S d : Fin (n + 2) → ℝ) (tl tu : ℝ) (hl : tl < 0) (hu : 0 < tu)
    (hE : ∀ t ∈ Set.Ioo tl tu, S + t • d ∈ equalOrderSet P S)
    (hqc : IsQuasiconcaveOn (equalOrderSet P S) f)
    (hlsc : LowerSemicontinuousOn f (orthant n))
    (hl' : S + tl • d ∈ orthant n) (hu' : S + tu • d ∈ orthant n) :
    min (f (S + tl • d)) (f (S + tu • d)) ≤ f S := by
  by_contra h
  push_neg at h
  have hlt1 : f S < f (S + tu • d) := lt_of_lt_of_le h (min_le_right _ _)
  have hlt2 : f S < f (S + tl • d) := lt_of_lt_of_le h (min_le_left _ _)
  set X : ℝ → (Fin (n + 2) → ℝ) := fun t => S + t • d with hX
  have hcont : Continuous X := continuous_const.add (continuous_id.smul continuous_const)
  have hmemO : ∀ t ∈ Set.Ioo tl tu, X t ∈ orthant n := fun t ht => (hE t ht).1.1.2.1
  have ev1 : ∀ᶠ t in 𝓝[<] tu, f S < f (X t) := by
    have h1 := hlsc _ hu' (f S) hlt1
    have ht : Tendsto X (𝓝[<] tu) (𝓝[orthant n] (X tu)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hcont.tendsto tu).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT (show tl < tu by linarith)] with t ht using hmemO t ht
    exact ht.eventually h1
  have ev2 : ∀ᶠ t in 𝓝[>] tl, f S < f (X t) := by
    have h1 := hlsc _ hl' (f S) hlt2
    have ht : Tendsto X (𝓝[>] tl) (𝓝[orthant n] (X tl)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hcont.tendsto tl).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show tl < tu by linarith)] with t ht using hmemO t ht
    exact ht.eventually h1
  obtain ⟨t₁, h1f, h1m⟩ := (ev1.and (Ioo_mem_nhdsLT hu)).exists
  obtain ⟨t₂, h2f, h2m⟩ := (ev2.and (Ioo_mem_nhdsGT hl)).exists
  obtain ⟨h1a, h1b⟩ := h1m
  obtain ⟨h2a, h2b⟩ := h2m
  have hq := hqc (X t₁) (hE t₁ ⟨by linarith, h1b⟩) (X t₂) (hE t₂ ⟨h2a, by linarith⟩)
    (-t₂ / (t₁ - t₂)) (div_nonneg (by linarith) (by linarith))
    ((div_le_one (by linarith)).mpr (by linarith))
  have hcomb : (-t₂ / (t₁ - t₂)) • X t₁ + (1 - (-t₂ / (t₁ - t₂))) • X t₂ = S := by
    have hne : t₁ - t₂ ≠ 0 := by linarith
    funext i
    simp only [hX, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hcomb] at hq
  rcases min_le_iff.mp hq with h' | h'
  · linarith
  · linarith

end P5884ced4

open ProjSchedTW.ObjectiveClasses in
theorem solution {n : ℕ} {K : Type} (P : Project n K)
    (f : (Fin (n + 2) → ℝ) → ℝ) (hf : IsLocallyQuasiconcave P f)
    (hS : (feasibleSet P).Nonempty) :
    ∃ S : Fin (n + 2) → ℝ, IsQuasistable P S ∧ IsOptimal P f S := by
  obtain ⟨S₀, hS₀, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hS (P5884ced4.feasibleSet_isCompact P)
    (hf.1.mono (fun X hX => hX.1.2.1))
  have hopt₀ : IsOptimal P f S₀ := ⟨hS₀, fun S' hS' => isMinOn_iff.mp hmin S' hS'⟩
  have key : ∀ m : ℕ, ∀ S, IsOptimal P f S → Fintype.card (P5884ced4.Cn n) - (P5884ced4.tight P S).card = m →
      ∃ S : Fin (n + 2) → ℝ, IsQuasistable P S ∧ IsOptimal P f S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro S hopt hm
    by_cases hq : IsQuasistable P S
    · exact ⟨S, hq, hopt⟩
    have hex : ∃ S' S'', IsOrderPreservingShift P S S' ∧ IsOrderPreservingShift P S S'' ∧
        ProjSchedTW.StableSchedules.AreOpposite S S' S'' := by
      by_contra h
      exact hq ⟨hopt.1, h⟩
    obtain ⟨S', S'', ⟨⟨-, hS'F, hne'⟩, hO'⟩, ⟨⟨-, hS''F, -⟩, hO''⟩, ⟨-, -, lam, hlam, hEq⟩⟩ := hex
    set d := S' - S with hd_def
    have hd : d ≠ 0 := sub_ne_zero.mpr hne'
    have hY1 : S + (1 : ℝ) • d = S' := by simp [hd_def]
    have hY2 : S + lam • d = S'' := by rw [← hEq]; abel
    have hP' : S' ∈ orderPolytope P (scheduleOrder P S) := ⟨hS'F.1, fun e he => (hO' he).2⟩
    have hP'' : S'' ∈ orderPolytope P (scheduleOrder P S) := ⟨hS''F.1, fun e he => (hO'' he).2⟩
    obtain ⟨tu, htu, hEu, hPu, hTu⟩ := P5884ced4.half_step P S d hopt.1.1 hd 1 lam one_pos hlam
      (by rw [hY1]; exact hP') (by rw [hY2]; exact hP'')
    obtain ⟨tl, htl, hEl, hPl, hTl⟩ := P5884ced4.half_step P S (-d) hopt.1.1 (neg_ne_zero.mpr hd)
      (-lam) (-1) (by linarith) (by norm_num)
      (by rw [neg_smul_neg, hY2]; exact hP'') (by rw [neg_smul_neg, hY1]; exact hP')
    have hseg : ∀ t ∈ Set.Ioo (-tl) tu, S + t • d ∈ equalOrderSet P S := by
      intro t ht
      rcases le_or_gt 0 t with h0 | h0
      · exact hEu t h0 ht.2
      · have := hEl (-t) (by linarith) (by linarith [ht.1])
        rwa [neg_smul_neg] at this
    have hl_eq : S + (-tl) • d = S + tl • (-d) := by rw [smul_neg, neg_smul]
    have hmin2 := P5884ced4.seg P f S d (-tl) tu (by linarith) htu hseg (hf.2 S hopt.1) hf.1
      (by rw [hl_eq]; exact hPl.1.2.1) hPu.1.2.1
    have hcard : ∀ Z, Z ∈ orderPolytope P (scheduleOrder P S) → f Z ≤ f S →
        P5884ced4.tight P S ⊂ P5884ced4.tight P Z → ∃ S : Fin (n + 2) → ℝ, IsQuasistable P S ∧ IsOptimal P f S := by
      intro Z hZ hfZ hT
      have hZopt : IsOptimal P f Z :=
        ⟨P5884ced4.orderPolytope_subset P S hopt.1 hZ, fun S' h => le_trans hfZ (hopt.2 S' h)⟩
      have hlt := Finset.card_lt_card hT
      have hle : (P5884ced4.tight P Z).card ≤ Fintype.card (P5884ced4.Cn n) := Finset.card_le_univ _
      exact ih (Fintype.card (P5884ced4.Cn n) - (P5884ced4.tight P Z).card) (by omega) Z hZopt rfl
    rcases min_le_iff.mp hmin2 with h | h
    · rw [hl_eq] at h
      exact hcard _ hPl h hTl
    · exact hcard _ hPu h hTu
  exact key _ S₀ hopt₀ rfl
