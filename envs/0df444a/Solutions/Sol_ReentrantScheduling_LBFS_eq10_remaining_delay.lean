-- Prove2me | solution 1 for ReentrantScheduling.LBFS.eq10_remaining_delay
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T17:42:44.448476+00:00
-- url     : https://prove2.me/submissions/273a1e47-7012-4e8d-a3f3-7ea2cff09c1f

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model
import Definitions.Def_ReentrantScheduling_LBFS_Constants

set_option autoImplicit false

namespace LBFSEq10Aux

open ReentrantScheduling.LBFS

lemma wt_cases (x : WithTop ℝ) : x = ⊤ ∨ ∃ s : ℝ, x = (s : WithTop ℝ) := by
  induction x using WithTop.recTopCoe <;> simp

open MeasureTheory Classical in
/-- Busy-time counting: if at every instant of `[a, b)` at least `m` of the sets `G x` (`x ∈ P`) contain
the instant, then `m (b - a) ≤ Σ_x d x` whenever `vol (G x) ≤ d x`. -/
lemma count_integral {X : Type*} (P : Finset X) (G : X → Set ℝ) (hG : ∀ x, MeasurableSet (G x))
    (d : X → ℝ) (hd : ∀ x ∈ P, volume (G x) ≤ ENNReal.ofReal (d x)) (hd0 : ∀ x ∈ P, 0 ≤ d x)
    (m : ℕ) (a b : ℝ) (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ico a b, m ≤ (P.filter (fun x => t ∈ G x)).card) :
    (m : ℝ) * (b - a) ≤ ∑ x ∈ P, d x := by
  classical
  have h1 : ∫⁻ t in Set.Ico a b, (m : ENNReal) ≤
      ∫⁻ t in Set.Ico a b, ∑ x ∈ P, (G x).indicator (1 : ℝ → ENNReal) t := by
    apply setLIntegral_mono' measurableSet_Ico
    intro t ht
    have : ∑ x ∈ P, (G x).indicator (1 : ℝ → ENNReal) t =
        ((P.filter (fun x => t ∈ G x)).card : ENNReal) := by
      rw [← Finset.sum_boole]; apply Finset.sum_congr rfl; intro x _
      simp [Set.indicator_apply]
    rw [this]; exact_mod_cast h t ht
  rw [setLIntegral_const, Real.volume_Ico,
    lintegral_finsetSum _ (fun x _ => (measurable_one.indicator (hG x)))] at h1
  have h2 : ∀ x ∈ P, ∫⁻ t in Set.Ico a b, (G x).indicator (1 : ℝ → ENNReal) t ≤
      ENNReal.ofReal (d x) := by
    intro x hx
    rw [lintegral_indicator_one (hG x)]
    exact le_trans (Measure.restrict_apply_le _ _) (hd x hx)
  have h3 := le_trans h1 (Finset.sum_le_sum h2)
  rw [← ENNReal.ofReal_sum_of_nonneg hd0, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg hd0)).mp h3

section basic
variable {L : Line} (R : Run L)

lemma arrive_entry (p : R.Part) : R.arrive p (R.entry p) = ((R.α p : ℝ) : WithTop ℝ) := by
  simp [Run.arrive]

lemma arrive_succ (p : R.Part) (j : Fin L.l) (hj : j.val + 1 < L.l) (hpj : R.entry p ≤ j) :
    R.arrive p ⟨j.val + 1, hj⟩ = R.start p j + ((L.τ j : ℝ) : WithTop ℝ) := by
  have h1 : (⟨j.val + 1, hj⟩ : Fin L.l) ≠ R.entry p := by
    intro h; have := congrArg Fin.val h; simp at this
    have := Fin.le_def.mp hpj; omega
  have h2 : R.entry p < (⟨j.val + 1, hj⟩ : Fin L.l) := by
    rw [Fin.lt_def]; have := Fin.le_def.mp hpj; simp; omega
  unfold Run.arrive
  rw [if_neg h1, dif_pos h2]
  have : (⟨j.val + 1 - 1, by omega⟩ : Fin L.l) = j := by ext; simp
  simp only [this]

lemma arrive_of_lt (p : R.Part) (i : Fin L.l) (h : R.entry p < i) :
    ∃ j : Fin L.l, ∃ hj : j.val + 1 < L.l, i = ⟨j.val + 1, hj⟩ ∧ R.entry p ≤ j ∧
      R.arrive p i = R.start p j + ((L.τ j : ℝ) : WithTop ℝ) := by
  have hi : 0 < i.val := by have := Fin.lt_def.mp h; omega
  refine ⟨⟨i.val - 1, by omega⟩, by simp; omega, by ext; simp; omega, ?_, ?_⟩
  · rw [Fin.le_def]; have := Fin.lt_def.mp h; simp; omega
  · have e : i = ⟨(⟨i.val - 1, by omega⟩ : Fin L.l).val + 1, by simp; omega⟩ := by ext; simp; omega
    conv_lhs => rw [e]
    exact arrive_succ R p _ _ (by rw [Fin.le_def]; have := Fin.lt_def.mp h; simp; omega)

end basic

section gs
variable {L : Line} (R : Run L)

/-- The instants at which `x.1` is in service at buffer `x.2`. -/
def Gs (x : R.Part × Fin L.l) : Set ℝ :=
  {t | R.start x.1 x.2 ≤ ((t : ℝ) : WithTop ℝ) ∧
    ((t : ℝ) : WithTop ℝ) < R.start x.1 x.2 + ((L.τ x.2 : ℝ) : WithTop ℝ)}

lemma Gs_cases (x : R.Part × Fin L.l) :
    Gs R x = ∅ ∨ ∃ s : ℝ, Gs R x = Set.Ico s (s + L.τ x.2) := by
  rcases wt_cases (R.start x.1 x.2) with h | ⟨s, h⟩
  · left; ext t; simp [Gs, h]
  · right; refine ⟨s, ?_⟩; ext t
    simp only [Gs, h, Set.mem_ofPred_eq, Set.mem_Ico, ← WithTop.coe_add, WithTop.coe_le_coe,
      WithTop.coe_lt_coe]

lemma Gs_meas (x : R.Part × Fin L.l) : MeasurableSet (Gs R x) := by
  rcases Gs_cases R x with h | ⟨s, h⟩
  · rw [h]; exact MeasurableSet.empty
  · rw [h]; exact measurableSet_Ico

lemma Gs_vol (x : R.Part × Fin L.l) :
    MeasureTheory.volume (Gs R x) ≤ ENNReal.ofReal (L.τ x.2) := by
  rcases Gs_cases R x with h | ⟨s, h⟩
  · rw [h]; simp
  · rw [h, Real.volume_Ico]; ring_nf; exact le_refl _

/-- The buffers `i ≥ k` at the center of `b_k`. -/
def Ik (k : Fin L.l) : Finset (Fin L.l) :=
  Finset.univ.filter (fun i => k ≤ i ∧ L.center i = L.center k)

end gs

section consts
variable (L : Line)

lemma wk_congr {i j : Fin L.l} (h : i.val = j.val) : L.wk i = L.wk j := by rw [Fin.ext h]

lemma Wk_le_wk (k : Fin L.l) : (∑ i ∈ Ik k, L.τ i) / (L.m (L.center k) : ℝ) ≤ L.wk k := by
  unfold Line.wk
  refine le_trans ?_ (Finset.le_sup' _ (b := k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl k⟩))
  rw [Finset.sum_div]
  exact le_of_eq rfl

lemma wk_nonneg (k : Fin L.l) : 0 ≤ L.wk k := by
  refine le_trans ?_ (Wk_le_wk L k)
  exact div_nonneg (Finset.sum_nonneg (fun i _ => (L.τ_pos i).le)) (Nat.cast_nonneg _)

lemma wk_anti (k : Fin L.l) (hk : k.val + 1 < L.l) : L.wk ⟨k.val + 1, hk⟩ ≤ L.wk k := by
  unfold Line.wk
  apply Finset.sup'_le
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hj
  have hjm : j ∈ Finset.univ.filter (fun j : Fin L.l => k ≤ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Fin.le_def]; simp at hj; omega⟩
  refine le_trans ?_ (Finset.le_sup' _ hjm)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hi ⊢
    exact ⟨by omega, hi.2⟩
  · intro i _ _
    exact div_nonneg (L.τ_pos i).le (Nat.cast_nonneg _)

lemma taubar_nonneg' : 0 ≤ L.τbar :=
  le_trans (L.τ_pos L.first).le (Finset.le_sup' L.τ (Finset.mem_univ _))

lemma cAux_pos : ∀ (d : ℕ) (ε : ℝ), 0 < L.cAux d ε
  | 0, ε => by
      rw [Line.cAux]
      exact add_pos_of_nonneg_of_pos (taubar_nonneg' L) (L.τ_pos _)
  | d + 1, ε => by
      rw [Line.cAux]
      have h1 := cAux_pos d ε
      have h2 : 0 ≤ 2 * (L.l : ℝ) * L.τbar := by
        have := taubar_nonneg' L; positivity
      exact add_pos_of_pos_of_nonneg h1 (le_trans h2 (le_max_left _ _))

lemma c_last (ε : ℝ) : L.c L.last ε = L.τbar + L.τ L.last := by
  unfold Line.c
  have : L.l - 1 - L.last.val = 0 := by simp [Line.last]
  rw [this, Line.cAux]

lemma c_step (k : Fin L.l) (hk : k.val + 1 < L.l) (ε : ℝ) :
    L.c ⟨k.val + 1, hk⟩ ε ≤ L.c k ε ∧
    L.c ⟨k.val + 1, hk⟩ ε + (L.wk ⟨k.val + 1, hk⟩ + ε) *
      (⌈2 * L.c ⟨k.val + 1, hk⟩ (ε / 2) / ε⌉₊ : ℝ) + 2 * L.τbar ≤ L.c k ε := by
  have hd : L.l - 1 - k.val = (L.l - 1 - (k.val + 1)) + 1 := by omega
  have e : L.c k ε = L.cAux (L.l - 1 - (k.val + 1) + 1) ε := by unfold Line.c; rw [hd]
  have e' : ∀ ε', L.c ⟨k.val + 1, hk⟩ ε' = L.cAux (L.l - 1 - (k.val + 1)) ε' := fun _ => rfl
  rw [e, e', e', Line.cAux]
  rw [wk_congr L (j := ⟨k.val + 1, hk⟩)]
  · have h2 : 0 ≤ 2 * (L.l : ℝ) * L.τbar := by
      have := taubar_nonneg' L; positivity
    constructor
    · exact le_add_of_nonneg_right (le_trans h2 (le_max_left _ _))
    · rw [add_assoc]
      gcongr
      exact le_trans (le_max_left _ _) (le_max_right _ _)
  · simp; omega

end consts

lemma exists_kth (T : Finset ℕ) : ∀ j < T.card, ∃ v ∈ T, (T.filter (fun u => v < u)).card = j := by
  induction T using Finset.induction_on_max with
  | empty => intro j hj; simp at hj
  | insert M T hlt ih =>
    intro j hj
    have hM : M ∉ T := fun h => lt_irrefl _ (hlt M h)
    rw [Finset.card_insert_of_notMem hM] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · refine ⟨M, Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact lt_irrefl _
      · exact not_lt.mpr (hlt u hu).le
    · obtain ⟨v, hv, hc⟩ := ih (j - 1) (by omega)
      refine ⟨v, Finset.mem_insert_of_mem hv, ?_⟩
      rw [Finset.filter_insert, if_pos (hlt v hv), Finset.card_insert_of_notMem (by simp [hM])]
      omega

section adm
variable {L : Line} {R : Run L} (hR : R.Admissible L.lbfsPrio)
include hR

omit hR in
lemma alpha_nonneg (p : R.Part) : 0 ≤ R.α p := by
  by_cases h : R.initial p
  · rw [R.initial_zero p h]
  · exact R.released_nonneg p h

lemma arrive_nonneg_aux : ∀ (n : ℕ) (p : R.Part) (i : Fin L.l), i.val = n → R.entry p ≤ i →
    (0 : WithTop ℝ) ≤ R.arrive p i := by
  intro n
  induction n with
  | zero =>
    intro p i hi hpi
    have : i = R.entry p := by
      ext; have := Fin.le_def.mp hpi; omega
    subst this
    rw [arrive_entry]; exact_mod_cast alpha_nonneg p
  | succ n ih =>
    intro p i hi hpi
    by_cases he : i = R.entry p
    · subst he; rw [arrive_entry]; exact_mod_cast alpha_nonneg p
    · have hlt : R.entry p < i := lt_of_le_of_ne hpi (Ne.symm he)
      obtain ⟨j, hj, rfl, hpj, harr⟩ := arrive_of_lt R p i hlt
      rw [harr]
      rcases hR.precedence p j hpj with h | ⟨_, _, hneg, _⟩
      · have h0 := ih p j (by simp at hi; omega) hpj
        have := le_trans h0 h
        exact le_trans this (le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos j).le))
      · rcases wt_cases (R.start p j) with h' | ⟨s, h'⟩
        · rw [h']; simp
        · rw [h'] at hneg ⊢
          have : -L.τ j < s := by exact_mod_cast hneg
          rw [← WithTop.coe_add]; exact_mod_cast (by linarith : (0:ℝ) ≤ s + L.τ j)

lemma arrive_nonneg (p : R.Part) (i : Fin L.l) (hpi : R.entry p ≤ i) :
    (0 : WithTop ℝ) ≤ R.arrive p i := arrive_nonneg_aux hR _ p i rfl hpi

/-- FIFO at every buffer: line order is service-start order. -/
lemma fifo_aux : ∀ (n : ℕ) (i : Fin L.l), i.val = n → ∀ a b : R.Part, R.ord a < R.ord b →
    R.entry a ≤ i → R.entry b ≤ i → R.start a i ≤ R.start b i := by
  intro n
  induction n with
  | zero => ?base
  | succ n ih => ?step
  all_goals
    intro i hi a b hab hai hbi
    rcases wt_cases (R.start b i) with ht | ⟨s, ht⟩
    · rw [ht]; exact le_top
    · rw [ht]
      by_cases hs : s < 0
      · -- b is an initial part already in service at time 0
        rcases hR.precedence b i hbi with h | ⟨hib, hbin, _, _⟩
        · have := le_trans (arrive_nonneg hR b i hbi) (ht ▸ h)
          have : (0:ℝ) ≤ s := by exact_mod_cast this
          linarith
        · have hain : R.initial a := by
            by_contra ha
            have := hR.ord_initial b a hbin ha; omega
          have heq : R.entry a = R.entry b := by
            rcases lt_or_eq_of_le (hib ▸ hai) with hlt | heq
            · have := hR.ord_deeper b a hbin hain hlt; omega
            · exact heq
          have hnl : ¬ R.start b (R.entry b) < R.start a (R.entry a) := by
            intro hlt; have := hR.ord_start b a hbin hain heq.symm hlt; omega
          rw [heq, ← hib] at hnl
          rw [← ht]; exact not_lt.mp hnl
      · replace hs : 0 ≤ s := not_lt.mp hs
        have hhead := hR.head b i s hs hbi ht a hab
        suffices harr : R.arrive a i ≤ ((s : ℝ) : WithTop ℝ) by
          by_contra hlt
          exact hhead ⟨hai, harr, not_le.mp hlt⟩
        -- facts about b's arrival
        have hb_arr : R.initial b → False ∨ True := fun _ => Or.inr trivial
        clear hb_arr
        by_cases hia : i = R.entry a
        · subst hia
          rw [arrive_entry]
          by_cases hain : R.initial a
          · rw [R.initial_zero a hain]; exact_mod_cast hs
          · have hbin : ¬ R.initial b := by
              intro hbin; have := hR.ord_initial b a hbin hain; omega
            have hbe : R.entry a = R.entry b := by
              rw [R.released_entry a hain, R.released_entry b hbin]
            have hαb : ((R.α b : ℝ) : WithTop ℝ) ≤ (s : WithTop ℝ) := by
              rcases hR.precedence b (R.entry a) hbi with h | ⟨_, hbin', _, _⟩
              · rw [hbe, arrive_entry] at h
                have ht' := ht; rw [hbe] at ht'; rw [← ht']; exact h
              · exact absurd hbin' hbin
            have hαab : R.α a ≤ R.α b := by
              by_contra hlt
              have := hR.ord_release b a hbin hain (not_le.mp hlt); omega
            exact le_trans (by exact_mod_cast hαab) hαb
        · have hlta : R.entry a < i := lt_of_le_of_ne hai (Ne.symm hia)
          by_cases hib : i = R.entry b
          · exfalso
            by_cases hbin : R.initial b
            · have hain : R.initial a := by
                by_contra ha; have := hR.ord_initial b a hbin ha; omega
              have := hR.ord_deeper b a hbin hain (hib ▸ hlta); omega
            · have := R.released_entry b hbin
              have h0 : i.val = 0 := by rw [hib, this]; rfl
              have := Fin.lt_def.mp hlta; omega
          · have hltb : R.entry b < i := lt_of_le_of_ne hbi (Ne.symm hib)
            obtain ⟨j, hj, hij, haj, harra⟩ := arrive_of_lt R a i hlta
            obtain ⟨j', hj', hij', hbj, harrb⟩ := arrive_of_lt R b i hltb
            have hjj : j' = j := by
              ext; have h1 := congrArg Fin.val hij; have h2 := congrArg Fin.val hij'; simp at h1 h2; omega
            subst hjj
            have hstart : R.start a j' ≤ R.start b j' := by
              first
              | (have h1 := congrArg Fin.val hij; simp at h1; omega)
              | exact ih j' (by have h1 := congrArg Fin.val hij; simp at h1; omega) a b hab haj hbj
            have hb : R.arrive b i ≤ ((s : ℝ) : WithTop ℝ) := by
              rcases hR.precedence b i hbi with h | ⟨hib', _, _, _⟩
              · rw [← ht]; exact h
              · exact absurd hib' hib
            rw [harra]; rw [harrb] at hb
            exact le_trans (by gcongr) hb

lemma fifo (i : Fin L.l) (a b : R.Part) (hab : R.ord a < R.ord b)
    (hai : R.entry a ≤ i) (hbi : R.entry b ≤ i) : R.start a i ≤ R.start b i :=
  fifo_aux hR _ i rfl a b hab hai hbi

omit hR in
lemma entry_le_last (p : R.Part) : R.entry p ≤ L.last := by
  rw [Fin.le_def]; simp [Line.last]; have := (R.entry p).isLt; omega

lemma exit_mono (a b : R.Part) (hab : R.ord a < R.ord b) : R.exit a ≤ R.exit b := by
  unfold Run.exit
  have := fifo hR _ a b hab (entry_le_last a) (entry_le_last b)
  gcongr


lemma alpha_le_arrive_aux : ∀ (n : ℕ) (p : R.Part) (i : Fin L.l), i.val = n → R.entry p ≤ i →
    ((R.α p : ℝ) : WithTop ℝ) ≤ R.arrive p i := by
  intro n
  induction n with
  | zero =>
    intro p i hi hpi
    have : i = R.entry p := by
      ext; have := Fin.le_def.mp hpi; omega
    subst this
    rw [arrive_entry]
  | succ n ih =>
    intro p i hi hpi
    by_cases he : i = R.entry p
    · subst he; rw [arrive_entry]
    · have hlt : R.entry p < i := lt_of_le_of_ne hpi (Ne.symm he)
      obtain ⟨j, hj, rfl, hpj, harr⟩ := arrive_of_lt R p i hlt
      rw [harr]
      rcases hR.precedence p j hpj with h | ⟨_, hin, hneg, _⟩
      · have h0 := ih p j (by simp at hi; omega) hpj
        have := le_trans h0 h
        exact le_trans this (le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos j).le))
      · rw [R.initial_zero p hin]
        rcases wt_cases (R.start p j) with h' | ⟨s, h'⟩
        · rw [h']; simp
        · rw [h'] at hneg ⊢
          have : -L.τ j < s := by exact_mod_cast hneg
          rw [← WithTop.coe_add]; exact_mod_cast (by linarith : (0:ℝ) ≤ s + L.τ j)

lemma alpha_le_arrive (p : R.Part) (i : Fin L.l) (hpi : R.entry p ≤ i) :
    ((R.α p : ℝ) : WithTop ℝ) ≤ R.arrive p i := alpha_le_arrive_aux hR _ p i rfl hpi

lemma alpha_le_of_ord (q p : R.Part) (h : R.ord q < R.ord p) : R.α q ≤ R.α p := by
  by_cases hq : R.initial q
  · rw [R.initial_zero q hq]; exact alpha_nonneg p
  · have hp : ¬ R.initial p := by
      intro hp; have := hR.ord_initial p q hp hq; omega
    by_contra hlt
    have := hR.ord_release p q hp hq (not_le.mp hlt); omega

lemma arrive_le_of_ord (q p : R.Part) (i : Fin L.l) (h : R.ord q < R.ord p)
    (hq : R.entry q ≤ i) (hp : R.entry p ≤ i) : R.arrive q i ≤ R.arrive p i := by
  by_cases hpe : i = R.entry p
  · by_cases hpin : R.initial p
    · have hqin : R.initial q := by
        by_contra hq'; have := hR.ord_initial p q hpin hq'; omega
      have hqe : i = R.entry q := by
        rcases lt_or_eq_of_le (hpe ▸ hq) with hlt | heq
        · have := hR.ord_deeper p q hpin hqin hlt; omega
        · rw [hpe, heq]
      rw [hpe, arrive_entry, R.initial_zero p hpin]
      rw [hpe] at hqe; rw [hqe, arrive_entry, R.initial_zero q hqin]
    · have h0 : i.val = 0 := by rw [hpe, R.released_entry p hpin]; rfl
      have hqe : i = R.entry q := by ext; have := Fin.le_def.mp hq; omega
      have hpe' := hpe
      rw [hpe, arrive_entry]; rw [hpe] at hqe; rw [hqe, arrive_entry]
      exact_mod_cast alpha_le_of_ord hR q p h
  · have hltp : R.entry p < i := lt_of_le_of_ne hp (Ne.symm hpe)
    by_cases hqe : i = R.entry q
    · rw [hqe, arrive_entry]; rw [hqe] at hp
      exact le_trans (by exact_mod_cast alpha_le_of_ord hR q p h) (alpha_le_arrive hR p _ hp)
    · have hltq : R.entry q < i := lt_of_le_of_ne hq (Ne.symm hqe)
      obtain ⟨j, hj, hij, hqj, harrq⟩ := arrive_of_lt R q i hltq
      obtain ⟨j', hj', hij', hpj, harrp⟩ := arrive_of_lt R p i hltp
      have hjj : j' = j := by
        ext; have h1 := congrArg Fin.val hij; have h2 := congrArg Fin.val hij'; simp at h1 h2; omega
      subst hjj
      rw [harrq, harrp]
      have := fifo hR j' q p h hqj hpj
      gcongr

omit hR in
/-- A part that has reached buffer `j ≥ k` by time `t` and has not exited is in `B^(k)`. -/
lemma inBlock_of_arrive (q : R.Part) (k j : Fin L.l) (t : ℝ) (hkj : k ≤ j) (hqj : R.entry q ≤ j)
    (harr : R.arrive q j ≤ ((t : ℝ) : WithTop ℝ)) (hex : ((t : ℝ) : WithTop ℝ) < R.exit q) :
    R.inBlock q k t := by
  classical
  let S : Finset (Fin L.l) := Finset.univ.filter (fun i => j ≤ i ∧ R.arrive q i ≤ ((t : ℝ) : WithTop ℝ))
  have hne : S.Nonempty := ⟨j, by simp [S, harr]⟩
  set i := S.max' hne with hi
  have hiS : i ∈ S := S.max'_mem hne
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
  refine ⟨i, le_trans hkj hiS.1, le_trans hqj hiS.1, hiS.2, ?_⟩
  by_cases hlast : i.val + 1 < L.l
  · have hqi : R.entry q ≤ i := le_trans hqj hiS.1
    have hnot : ⟨i.val + 1, hlast⟩ ∉ S := by
      intro hmem
      have := S.le_max' _ hmem
      rw [← hi, Fin.le_def] at this; simp at this
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hnot
    have := hnot (by rw [Fin.le_def]; have := Fin.le_def.mp hiS.1; simp; omega)
    rw [arrive_succ R q i hlast hqi] at this
    exact not_le.mp this
  · have : i = L.last := by ext; simp [Line.last]; have := i.isLt; omega
    rw [this]; exact hex

lemma start_le_succ (p : R.Part) (j : Fin L.l) (hj : j.val + 1 < L.l) (hpj : R.entry p ≤ j) :
    R.start p j + ((L.τ j : ℝ) : WithTop ℝ) ≤ R.start p ⟨j.val + 1, hj⟩ := by
  have hle : R.entry p ≤ ⟨j.val + 1, hj⟩ := by
    rw [Fin.le_def]; have := Fin.le_def.mp hpj; simp; omega
  rcases hR.precedence p _ hle with h | ⟨he, _, _, _⟩
  · rw [arrive_succ R p j hj hpj] at h; exact h
  · exfalso; have := congrArg Fin.val he; have := Fin.le_def.mp hpj; simp at *; omega

lemma start_le_start_aux (p : R.Part) : ∀ (d : ℕ) (j i : Fin L.l), i.val = j.val + d →
    R.entry p ≤ j → R.start p j ≤ R.start p i := by
  intro d
  induction d with
  | zero => intro j i h _; have : i = j := Fin.ext (by omega); rw [this]
  | succ d ih =>
    intro j i h hpj
    have hlt : j.val + d + 1 < L.l := by have := i.isLt; omega
    have h1 := ih j ⟨j.val + d, by omega⟩ rfl hpj
    have hpj' : R.entry p ≤ ⟨j.val + d, by omega⟩ := le_trans hpj (by rw [Fin.le_def]; simp)
    have h2 := start_le_succ hR p ⟨j.val + d, by omega⟩ hlt hpj'
    have hi : i = ⟨(⟨j.val + d, by omega⟩ : Fin L.l).val + 1, hlt⟩ := Fin.ext (by simp; omega)
    rw [hi]
    exact le_trans h1 (le_trans (le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos _).le)) h2)

lemma start_le_start (p : R.Part) (j i : Fin L.l) (hji : j ≤ i) (hpj : R.entry p ≤ j) :
    R.start p j ≤ R.start p i :=
  start_le_start_aux hR p (i.val - j.val) j i (by have := Fin.le_def.mp hji; omega) hpj

lemma end_le_exit (p : R.Part) (i : Fin L.l) (hpi : R.entry p ≤ i) :
    R.start p i + ((L.τ i : ℝ) : WithTop ℝ) ≤ R.exit p := by
  unfold Run.exit
  by_cases hlast : i.val + 1 < L.l
  · have h1 := start_le_succ hR p i hlast hpi
    have h2 := start_le_start hR p ⟨i.val + 1, hlast⟩ L.last
      (by rw [Fin.le_def]; simp [Line.last]; omega) (le_trans hpi (by rw [Fin.le_def]; simp))
    exact le_trans h1 (le_trans h2 (le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos _).le)))
  · have : i = L.last := by ext; simp [Line.last]; have := i.isLt; omega
    rw [this]

omit hR in
lemma tau_le_taubar (i : Fin L.l) : L.τ i ≤ L.τbar :=
  Finset.le_sup' L.τ (Finset.mem_univ i)

omit hR in
lemma taubar_nonneg : 0 ≤ L.τbar := le_trans (L.τ_pos L.first).le (tau_le_taubar L.first)

/-- WORK lemma: a part in `b_k` at `t₀ ≥ 0` starts service there by `t₀ + τ̄ + |A| W_k`, where `A`
contains every part ahead of it and `W_k = Σ_{i ≥ k, σ_i = σ_k} τ_i / m_{σ_k}`. -/
lemma work (π : R.Part) (k : Fin L.l) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (hπ : R.inBuffer π k t₀)
    (A : Finset R.Part) (hA : ∀ q, R.inSystem q t₀ → R.ord q < R.ord π → q ∈ A) :
    R.start π k ≤ (((t₀ + L.τbar + (A.card : ℝ) *
      ((∑ i ∈ Ik k, L.τ i) / (L.m (L.center k) : ℝ))) : ℝ) : WithTop ℝ) := by
  classical
  set W := (∑ i ∈ Ik k, L.τ i) / (L.m (L.center k) : ℝ) with hW
  have hm : (0:ℝ) < L.m (L.center k) := by exact_mod_cast L.m_pos _
  have hW0 : 0 ≤ W := div_nonneg (Finset.sum_nonneg (fun i _ => (L.τ_pos i).le)) hm.le
  have htb := taubar_nonneg (L := L)
  set T₁ := t₀ + L.τbar + (A.card : ℝ) * W with hT₁
  by_contra hcon
  have hlt : ((T₁ : ℝ) : WithTop ℝ) < R.start π k := not_le.mp hcon
  obtain ⟨T₂, hT12, hT₂⟩ : ∃ T₂ : ℝ, T₁ < T₂ ∧
      ∀ t : ℝ, t < T₂ → ((t : ℝ) : WithTop ℝ) < R.start π k := by
    rcases wt_cases (R.start π k) with h | ⟨S, h⟩
    · exact ⟨T₁ + 1, by linarith, fun t _ => by rw [h]; exact WithTop.coe_lt_top t⟩
    · rw [h] at hlt
      exact ⟨S, by exact_mod_cast hlt, fun t ht => by rw [h]; exact_mod_cast ht⟩
  have hαπ : R.α π ≤ t₀ := by
    have := le_trans (alpha_le_arrive hR π k hπ.1) hπ.2.1
    exact_mod_cast this
  have hwait : ∀ t : ℝ, t₀ ≤ t → t < T₂ → R.waiting π k t := fun t h1 h2 =>
    ⟨hπ.1, le_trans hπ.2.1 (by exact_mod_cast h1), hT₂ t h2⟩
  have key : ∀ t ∈ Set.Ico (t₀ + L.τbar) T₂,
      L.m (L.center k) ≤ ((A ×ˢ Ik k).filter (fun x => t ∈ Gs R x)).card := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hbusy := hR.nonidling (L.center k) t ht0 ⟨π, k, rfl, hwait t (by linarith [ht.1]) ht.2⟩
    have hsub : {pi : R.Part × Fin L.l | L.center pi.2 = L.center k ∧ R.inService pi.1 pi.2 t} ⊆
        ↑((A ×ˢ Ik k).filter (fun x => t ∈ Gs R x)) := by
      rintro ⟨p, i⟩ ⟨hc, hpi, hs1, hs2⟩
      rcases wt_cases (R.start p i) with hst | ⟨s, hst⟩
      · exfalso; rw [hst] at hs1; simp at hs1
      have hs1' : s ≤ t := by rw [hst] at hs1; exact_mod_cast hs1
      have hs2' : t < s + L.τ i := by
        rw [hst, ← WithTop.coe_add] at hs2; exact_mod_cast hs2
      have hτi := tau_le_taubar (L := L) i
      have hs0 : t₀ ≤ s := by linarith [ht.1]
      have hsw := hwait s hs0 (lt_of_le_of_lt hs1' ht.2)
      have hki : k ≤ i := by
        by_contra hik
        exact hR.priority p i s (by linarith) hpi hst π k hc.symm (not_le.mp hik) hsw
      have hord : R.ord p < R.ord π := by
        rcases lt_trichotomy (R.ord p) (R.ord π) with h | h | h
        · exact h
        · exfalso
          have hp : p = π := R.ord_inj h
          rw [hp] at hst
          have := start_le_start hR π k i hki hπ.1
          rw [hst] at this; exact absurd this (not_le.mpr hsw.2.2)
        · exfalso
          have h1 := fifo hR i π p h (le_trans hπ.1 hki) hpi
          rw [hst] at h1
          have := le_trans (start_le_start hR π k i hki hπ.1) h1
          exact absurd this (not_le.mpr hsw.2.2)
      have hpA : p ∈ A := by
        refine hA p ⟨le_trans (alpha_le_of_ord hR p π hord) hαπ, ?_⟩ hord
        exact lt_of_le_of_lt (by exact_mod_cast (by linarith [ht.1] : t₀ ≤ t))
          (lt_of_lt_of_le hs2 (end_le_exit hR p i hpi))
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq]
      refine ⟨⟨hpA, ?_⟩, hs1, hs2⟩
      simp [Ik, hki, hc]
    have := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at this
    unfold Run.busyCount at hbusy
    rw [hbusy] at this
    exact_mod_cast this
  have hab : t₀ + L.τbar ≤ T₂ := by
    have : 0 ≤ (A.card : ℝ) * W := mul_nonneg (Nat.cast_nonneg _) hW0
    linarith
  have hcount := count_integral (A ×ˢ Ik k) (Gs R) (Gs_meas R) (fun x => L.τ x.2)
    (fun x _ => Gs_vol R x) (fun x _ => (L.τ_pos _).le) _ (t₀ + L.τbar) T₂ hab (by convert key)
  rw [Finset.sum_product] at hcount
  simp only [Finset.sum_const, nsmul_eq_mul] at hcount
  have h3 : T₂ - (t₀ + L.τbar) ≤ (A.card : ℝ) * W := by
    rw [hW, ← mul_div_assoc, le_div_iff₀ hm]; linarith [hcount]
  linarith

lemma ahead_finite (π : R.Part) (t : ℝ) : (R.ahead π t).Finite :=
  (R.released_finite t).subset (fun _ hq => hq.1.1)

lemma alpha_le_of_inBlock (π : R.Part) (k : Fin L.l) (t : ℝ) (h : R.inBlock π k t) : R.α π ≤ t := by
  obtain ⟨i, _, hb⟩ := h
  have := le_trans (alpha_le_arrive hR π i hb.1) hb.2.1
  exact_mod_cast this

lemma ahead_mono (π : R.Part) (t₀ t : ℝ) (h : t₀ ≤ t) (hα : R.α π ≤ t₀) :
    R.ahead π t ⊆ R.ahead π t₀ := by
  rintro q ⟨⟨_, hex⟩, hord⟩
  exact ⟨⟨le_trans (alpha_le_of_ord hR q π hord) hα,
    lt_of_le_of_lt (by exact_mod_cast h) hex⟩, hord⟩

lemma ahead_inBlock (π q : R.Part) (k : Fin L.l) (t₀ : ℝ) (hπ : R.inBlock π k t₀)
    (hq : q ∈ R.ahead π t₀) : R.inBlock q k t₀ := by
  obtain ⟨i, hki, hπi⟩ := hπ
  obtain ⟨⟨hαq, hexq⟩, hord⟩ := hq
  by_cases hqi : R.entry q ≤ i
  · exact inBlock_of_arrive q k i t₀ hki hqi
      (le_trans (arrive_le_of_ord hR q π i hord hqi hπi.1) hπi.2.1) hexq
  · have hlt : i < R.entry q := not_le.mp hqi
    exact inBlock_of_arrive q k (R.entry q) t₀ (le_trans hki hlt.le) le_rfl
      (by rw [arrive_entry]; exact_mod_cast hαq) hexq

omit hR in
lemma select (B : Finset R.Part) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ B.card) :
    ∃ q ∈ B, (B.filter (fun p => R.ord q < R.ord p)).card = n - 1 := by
  classical
  have hinj : Set.InjOn R.ord B := fun a _ b _ h => R.ord_inj h
  obtain ⟨v, hv, hc⟩ := exists_kth (B.image R.ord) (n - 1)
    (by rw [Finset.card_image_of_injOn hinj]; omega)
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨q, hq, ?_⟩
  have e : (B.image R.ord).filter (fun u => R.ord q < u) =
      (B.filter (fun p => R.ord q < R.ord p)).image R.ord := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, h⟩; exact ⟨a, ⟨ha, h⟩, rfl⟩
    · rintro ⟨a, ⟨ha, h⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, h⟩
  rw [← hc, e, Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]

omit hR in
lemma card_of_encard {α : Type*} {s : Set α} (hs : s.Finite) {x : ℕ} (h : s.encard = x) :
    hs.toFinset.card = x := by
  rw [hs.encard_eq_coe_toFinset_card] at h; exact_mod_cast h

end adm

/-- The induction claim (10) at level `k`, for every `ε`. -/
def H (L : Line) (R : Run L) (k : Fin L.l) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ (π : R.Part) (t₀ : ℝ), 0 ≤ t₀ → R.inBlock π k t₀ → ∀ x : ℕ,
    (R.ahead π t₀).encard = x → R.exit π ≤ ((t₀ + L.c k ε + (L.wk k + ε) * x : ℝ) : WithTop ℝ)

section main
variable {L : Line} {R : Run L} (hR : R.Admissible L.lbfsPrio)
include hR

lemma base : H L R L.last := by
  classical
  intro ε hε π t₀ ht₀ hπ x hx
  obtain ⟨i, hi, hb⟩ := hπ
  have hil : i = L.last :=
    le_antisymm (by rw [Fin.le_def]; simp [Line.last]; have := i.isLt; omega) hi
  rw [hil] at hb
  set A := (ahead_finite hR π t₀).toFinset with hAdef
  have hA : ∀ q, R.inSystem q t₀ → R.ord q < R.ord π → q ∈ A := fun q h1 h2 => by
    rw [hAdef, Set.Finite.mem_toFinset]; exact ⟨h1, h2⟩
  have hcard : A.card = x := card_of_encard _ hx
  have hw := work hR π L.last t₀ ht₀ hb A hA
  rw [hcard] at hw
  have hW := Wk_le_wk L L.last
  have hx0 : (0:ℝ) ≤ x := Nat.cast_nonneg x
  have hxW : (x:ℝ) * ((∑ i ∈ Ik L.last, L.τ i) / (L.m (L.center L.last) : ℝ)) ≤
      x * (L.wk L.last + ε) := mul_le_mul_of_nonneg_left (by linarith) hx0
  unfold Run.exit
  calc R.start π L.last + ((L.τ L.last : ℝ) : WithTop ℝ)
      ≤ ((t₀ + L.τbar + (x : ℝ) * ((∑ i ∈ Ik L.last, L.τ i) / (L.m (L.center L.last) : ℝ)) : ℝ)
          : WithTop ℝ) + ((L.τ L.last : ℝ) : WithTop ℝ) := by gcongr
    _ ≤ _ := by
      rw [← WithTop.coe_add, WithTop.coe_le_coe, c_last]
      linarith

lemma step (k : Fin L.l) (hk : k.val + 1 < L.l) (hH : H L R ⟨k.val + 1, hk⟩) : H L R k := by
  classical
  intro ε hε
  obtain ⟨hc1, hc2⟩ := c_step L k hk ε
  have hwk' := wk_anti L k hk
  have hwk'0 := wk_nonneg L ⟨k.val + 1, hk⟩
  have hcpos : 0 < L.c ⟨k.val + 1, hk⟩ (ε / 2) := cAux_pos L _ _
  have hc0 : 0 ≤ L.c ⟨k.val + 1, hk⟩ ε := (cAux_pos L _ _).le
  set k' : Fin L.l := ⟨k.val + 1, hk⟩ with hk'
  have hceil := Nat.le_ceil (2 * L.c k' (ε / 2) / ε)
  generalize hn : ⌈2 * L.c k' (ε / 2) / ε⌉₊ = n at hc2 hceil
  have hcn : L.c k' (ε / 2) ≤ ε / 2 * n := by
    rw [div_le_iff₀ hε] at hceil; linarith
  have hn1 : 1 ≤ n := by
    have : (0:ℝ) < n := lt_of_lt_of_le (div_pos (by linarith) hε) hceil
    have : 0 < n := by exact_mod_cast this
    omega
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hwk0 := wk_nonneg L k
  have htb := taubar_nonneg' L
  have hkk' : k ≤ k' := by rw [Fin.le_def, hk']; simp
  have hwn : 0 ≤ (L.wk k' + ε) * n := mul_nonneg (by linarith) hn0
  intro π t₀ ht₀ hπ x hx
  induction x using Nat.strong_induction_on generalizing π t₀ with
  | _ x ih =>
  have hx0 : (0:ℝ) ≤ x := Nat.cast_nonneg x
  have hεx : 0 ≤ ε * x := mul_nonneg hε.le hx0
  obtain ⟨i, hki, hb⟩ := hπ
  by_cases hik : i = k
  swap
  · have hblk : R.inBlock π k' t₀ := by
      refine ⟨i, ?_, hb⟩
      have := Fin.lt_def.mp (lt_of_le_of_ne hki (Ne.symm hik))
      rw [Fin.le_def, hk']; simp; omega
    refine le_trans (hH ε hε π t₀ ht₀ hblk x hx) ?_
    rw [WithTop.coe_le_coe]
    have := mul_le_mul_of_nonneg_right hwk' hx0
    linarith
  rw [hik] at hb
  have hαπ : R.α π ≤ t₀ := alpha_le_of_inBlock hR π k t₀ ⟨k, le_rfl, hb⟩
  set A := (ahead_finite hR π t₀).toFinset with hAdef
  have hA : ∀ q, R.inSystem q t₀ → R.ord q < R.ord π → q ∈ A := fun q h1 h2 => by
    rw [hAdef, Set.Finite.mem_toFinset]; exact ⟨h1, h2⟩
  have hcard : A.card = x := card_of_encard _ hx
  have hw := work hR π k t₀ ht₀ hb A hA
  rw [hcard] at hw
  have hW := Wk_le_wk L k
  set W := (∑ i ∈ Ik k, L.τ i) / (L.m (L.center k) : ℝ) with hWdef
  have hxW : (x:ℝ) * W ≤ x * L.wk k := mul_le_mul_of_nonneg_left hW hx0
  have hτk := tau_le_taubar (L := L) k
  obtain ⟨s, hs⟩ : ∃ s : ℝ, R.start π k = (s : WithTop ℝ) := by
    rcases wt_cases (R.start π k) with h | h
    · rw [h] at hw; exact absurd hw (not_le.mpr (WithTop.coe_lt_top _))
    · exact h
  rw [hs] at hw
  have hsle : s ≤ t₀ + L.τbar + x * W := by exact_mod_cast hw
  have ht0U : t₀ < s + L.τ k := by
    have := hb.2.2; rw [hs, ← WithTop.coe_add] at this; exact_mod_cast this
  have harr' : R.arrive π k' = ((s + L.τ k : ℝ) : WithTop ℝ) := by
    rw [hk', arrive_succ R π k hk hb.1, hs, ← WithTop.coe_add]
  have hπk' : R.entry π ≤ k' := le_trans hb.1 hkk'
  have hblk : ∀ T : ℝ, s + L.τ k ≤ T → ((T : ℝ) : WithTop ℝ) < R.exit π → R.inBlock π k' T :=
    fun T h1 h2 => inBlock_of_arrive π k' k' T le_rfl hπk' (by rw [harr']; exact_mod_cast h1) h2
  have hfin : ∀ T : ℝ, T ≤ t₀ + L.c k ε + (L.wk k + ε) * x → R.exit π ≤ (T : WithTop ℝ) →
      R.exit π ≤ ((t₀ + L.c k ε + (L.wk k + ε) * x : ℝ) : WithTop ℝ) :=
    fun T h1 h2 => le_trans h2 (by exact_mod_cast h1)
  set B := (ahead_finite hR π (s + L.τ k)).toFinset with hBdef
  have hBA : ∀ p, p ∈ R.ahead π (s + L.τ k) → p ∈ R.ahead π t₀ :=
    fun p hp => ahead_mono hR π t₀ (s + L.τ k) ht0U.le hαπ hp
  by_cases hBn : B.card < n
  · by_cases hex : R.exit π ≤ (((s + L.τ k) : ℝ) : WithTop ℝ)
    · apply hfin (s + L.τ k) _ hex
      linarith
    · have h := hH ε hε π (s + L.τ k) (by linarith) (hblk _ le_rfl (not_le.mp hex)) B.card
        (by rw [hBdef]; exact (ahead_finite hR π _).encard_eq_coe_toFinset_card)
      refine le_trans h ?_
      rw [WithTop.coe_le_coe]
      have hBn' : (B.card : ℝ) ≤ n := by exact_mod_cast hBn.le
      have : (L.wk k' + ε) * B.card ≤ (L.wk k' + ε) * n :=
        mul_le_mul_of_nonneg_left hBn' (by linarith)
      linarith
  · obtain ⟨q, hqB, hqc⟩ := select B n hn1 (not_lt.mp hBn)
    have hqU : q ∈ R.ahead π (s + L.τ k) := by
      rw [hBdef, Set.Finite.mem_toFinset] at hqB; exact hqB
    have hqA : q ∈ R.ahead π t₀ := hBA q hqU
    have hqord : R.ord q < R.ord π := hqA.2
    have hqblk := ahead_inBlock hR π q k t₀ ⟨k, le_rfl, hb⟩ hqA
    set Aq := (ahead_finite hR q t₀).toFinset with hAqdef
    have hAq_sub : Aq ⊆ A.filter (fun p => R.ord p < R.ord q) := by
      intro p hp
      rw [hAqdef, Set.Finite.mem_toFinset] at hp
      rw [Finset.mem_filter]
      exact ⟨hA p hp.1 (lt_trans hp.2 hqord), hp.2⟩
    have hsupB : insert q (B.filter (fun p => R.ord q < R.ord p)) ⊆
        A.filter (fun p => ¬ (R.ord p < R.ord q)) := by
      intro p hp
      rw [Finset.mem_insert] at hp
      rw [Finset.mem_filter]
      rcases hp with rfl | hp
      · exact ⟨by rw [hAdef, Set.Finite.mem_toFinset]; exact hqA, lt_irrefl _⟩
      · rw [Finset.mem_filter] at hp
        have hpU : p ∈ R.ahead π (s + L.τ k) := by
          have := hp.1; rw [hBdef, Set.Finite.mem_toFinset] at this; exact this
        exact ⟨by rw [hAdef, Set.Finite.mem_toFinset]; exact hBA p hpU, not_lt.mpr hp.2.le⟩
    have hnot : q ∉ B.filter (fun p => R.ord q < R.ord p) := by simp
    have h1 := Finset.card_le_card hsupB
    rw [Finset.card_insert_of_notMem hnot, hqc] at h1
    have h2 : (A.filter (fun p => R.ord p < R.ord q)).card +
        (A.filter (fun p => ¬ (R.ord p < R.ord q))).card = A.card :=
      Finset.card_filter_add_card_filter_not _
    have h3 := Finset.card_le_card hAq_sub
    have hyx : Aq.card + n ≤ x := by omega
    have hqb := ih Aq.card (by omega) q t₀ ht₀ hqblk
      (by rw [hAqdef]; exact (ahead_finite hR q t₀).encard_eq_coe_toFinset_card)
    obtain ⟨T, hT⟩ : ∃ T : ℝ, R.exit q = (T : WithTop ℝ) := by
      rcases wt_cases (R.exit q) with h | h
      · rw [h] at hqb; exact absurd hqb (not_le.mpr (WithTop.coe_lt_top _))
      · exact h
    rw [hT] at hqb
    have hTle : T ≤ t₀ + L.c k ε + (L.wk k + ε) * Aq.card := by exact_mod_cast hqb
    have hUT : s + L.τ k < T := by
      have := hqU.1.2; rw [hT] at this; exact_mod_cast this
    have hy0 : (Aq.card : ℝ) + n ≤ x := by exact_mod_cast hyx
    have hwy := mul_le_mul_of_nonneg_left hy0 (by linarith : 0 ≤ L.wk k + ε)
    have hwkn : 0 ≤ (L.wk k + ε) * n := mul_nonneg (by linarith) hn0
    by_cases hex : R.exit π ≤ ((T : ℝ) : WithTop ℝ)
    · apply hfin T _ hex
      linarith
    · have hblkT := hblk T hUT.le (not_le.mp hex)
      set C := (ahead_finite hR π T).toFinset with hCdef
      have hCsub : C ⊆ B.filter (fun p => R.ord q < R.ord p) := by
        intro p hp
        rw [hCdef, Set.Finite.mem_toFinset] at hp
        obtain ⟨⟨hαp, hTp⟩, hordp⟩ := hp
        have hpU : p ∈ R.ahead π (s + L.τ k) :=
          ahead_mono hR π (s + L.τ k) T hUT.le (by linarith) ⟨⟨hαp, hTp⟩, hordp⟩
        rw [Finset.mem_filter, hBdef, Set.Finite.mem_toFinset]
        refine ⟨hpU, ?_⟩
        by_contra hle
        rcases lt_or_eq_of_le (not_lt.mp hle) with hlt | heq
        · have := exit_mono hR p q hlt
          rw [hT] at this
          exact absurd hTp (not_lt.mpr this)
        · have : p = q := R.ord_inj heq
          rw [this, hT] at hTp
          exact lt_irrefl _ hTp
      have hz := Finset.card_le_card hCsub
      rw [hqc] at hz
      have h := hH (ε / 2) (half_pos hε) π T (by linarith) hblkT C.card
        (by rw [hCdef]; exact (ahead_finite hR π T).encard_eq_coe_toFinset_card)
      refine le_trans h ?_
      rw [WithTop.coe_le_coe]
      have hz' : (C.card : ℝ) ≤ n := by
        have : C.card ≤ n := by omega
        exact_mod_cast this
      have h5 : (L.wk k' + ε / 2) * C.card ≤ (L.wk k' + ε / 2) * n :=
        mul_le_mul_of_nonneg_left hz' (by linarith)
      have h6 : L.wk k' * n ≤ L.wk k * n := mul_le_mul_of_nonneg_right hwk' hn0
      linarith

lemma allH : ∀ d : ℕ, ∀ k : Fin L.l, k.val + d = L.l - 1 → H L R k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have : k = L.last := Fin.ext (by simp [Line.last]; omega)
    rw [this]; exact base hR
  | succ d ih =>
    intro k hk
    exact step hR k (by omega) (ih ⟨k.val + 1, by omega⟩ (by simp; omega))

end main

end LBFSEq10Aux

open ReentrantScheduling.LBFS in
theorem solution (L : Line) (R : Run L) (hR : R.Admissible L.lbfsPrio)
    (k : Fin L.l) (ε : ℝ) (hε : 0 < ε) (π : R.Part) (t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hπ : R.inBlock π k t₀) (x : ℕ) (hx : (R.ahead π t₀).encard = x) :
    R.exit π ≤ ((t₀ + L.c k ε + (L.wk k + ε) * x : ℝ) : WithTop ℝ) := by
  have := k.isLt
  exact LBFSEq10Aux.allH hR (L.l - 1 - k.val) k (by omega) ε hε π t₀ ht₀ hπ x hx
