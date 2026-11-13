-- Prove2me | solution 1 for PinwheelDensity.ExactRange.theorem_E_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:01:12.624479+00:00
-- url     : https://prove2.me/submissions/909d97ff-1b99-452e-94df-5764b2049241
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_A_1
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_B_1
import Theorems.Thm_PinwheelDensity_ExactRange_lemma_B_2
import Theorems.Thm_PinwheelDensity_ExactRange_prop_B_5
import Theorems.Thm_PinwheelDensity_ExactRange_prop_C_3
import Theorems.Thm_PinwheelDensity_ExactRange_prop_D_3

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LE1Aux

open PinwheelDensity.ExactRange

/-! ### Schedulability is invariant under permutation -/

def Sch (A : List ℕ) : Prop :=
  ∃ s : ℕ → Option ℕ, ∀ (i : ℕ) (hi : i < A.length) (t : ℕ),
    ∃ d : ℕ, t ≤ d ∧ d < t + A[i] ∧ s d = some i

theorem sch_iff (A : List ℕ) : Schedulable A ↔ Sch A := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun d => (s d).map Fin.val, fun i hi t => ?_⟩
    obtain ⟨d, h1, h2, h3⟩ := hs ⟨i, hi⟩ t
    exact ⟨d, h1, h2, by simp [h3]⟩
  · rintro ⟨s, hs⟩
    refine ⟨fun d => match s d with
      | some j => if h : j < A.length then some ⟨j, h⟩ else none
      | none => none, fun i t => ?_⟩
    obtain ⟨d, h1, h2, h3⟩ := hs i.1 i.2 t
    exact ⟨d, h1, h2, by simp [h3]⟩

theorem sch_reindex (L L' : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ (i : ℕ) (hi : i < L'.length),
      ∃ hf : f i < L.length, g (f i) = i ∧ L[f i] = L'[i]) : Sch L → Sch L' := by
  rintro ⟨s, hs⟩
  refine ⟨fun d => (s d).map g, fun i hi t => ?_⟩
  obtain ⟨hf, hg, hv⟩ := h i hi
  obtain ⟨d, h1, h2, h3⟩ := hs (f i) hf t
  exact ⟨d, h1, by rw [← hv]; exact h2, by simp [h3, hg]⟩

theorem swap_sch (pre : List ℕ) (x y : ℕ) (l : List ℕ) :
    Sch (pre ++ x :: y :: l) → Sch (pre ++ y :: x :: l) := by
  intro hs
  refine sch_reindex _ _ (Equiv.swap pre.length (pre.length + 1))
    (Equiv.swap pre.length (pre.length + 1)) ?_ hs
  intro i hi
  have hlen : i < pre.length + l.length + 2 := by simp at hi; omega
  have hlen2 : (pre ++ x :: y :: l).length = pre.length + l.length + 2 := by simp; omega
  have hn : pre.length ≠ pre.length + 1 := by omega
  rcases Nat.lt_or_ge i pre.length with h1 | h1
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    refine ⟨by simp; omega, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), ?_⟩
    simp [List.getElem_append_left h1]
  · rcases Nat.lt_or_ge i (pre.length + 2) with h2 | h2
    · rcases (by omega : i = pre.length ∨ i = pre.length + 1) with rfl | rfl
      · rw [Equiv.swap_apply_left]
        refine ⟨by simp, Equiv.swap_apply_right _ _, ?_⟩
        simp [List.getElem_append_right]
      · rw [Equiv.swap_apply_right]
        refine ⟨by simp, Equiv.swap_apply_left _ _, ?_⟩
        simp [List.getElem_append_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      refine ⟨by simp; omega, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), ?_⟩
      rcases (⟨i - (pre.length + 2), by omega⟩ : ∃ k, i = pre.length + 2 + k) with ⟨k, hk⟩
      subst hk
      have e : pre.length + 2 + k - pre.length = k + 2 := by omega
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp [e]

theorem perm_sch {l l' : List ℕ} (h : l.Perm l') : ∀ pre : List ℕ, Sch (pre ++ l) → Sch (pre ++ l') := by
  induction h with
  | nil => intro pre hs; exact hs
  | cons x _ ih =>
    intro pre hs
    have := ih (pre ++ [x]) (by simpa using hs)
    simpa using this
  | swap x y l => intro pre hs; exact swap_sch pre y x l hs
  | trans _ _ ih1 ih2 => intro pre hs; exact ih2 pre (ih1 pre hs)

theorem schedulable_perm {A A' : List ℕ} (h : A.Perm A') (hA : Schedulable A) : Schedulable A' := by
  rw [sch_iff] at hA ⊢
  simpa using perm_sch h [] (by simpa using hA)

theorem schedulable_nil : Schedulable ([] : List ℕ) :=
  ⟨fun _ => none, fun i => i.elim0⟩

/-! ### Density -/

theorem density_eq (s : List ℕ) : density s = (s.map fun a : ℕ => (1 : ℚ) / (a : ℚ)).sum := by
  induction s <;> simp_all [density]

theorem density_nonneg (s : List ℕ) : 0 ≤ density s := by
  rw [density_eq]
  apply List.sum_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem density_append (a b : List ℕ) : density (a ++ b) = density a + density b := by
  simp [density]

theorem density_perm {a b : List ℕ} (h : a.Perm b) : density a = density b := by
  rw [density_eq, density_eq]
  exact List.Perm.sum_eq (h.map _)

theorem density_take_le (s : List ℕ) (k : ℕ) : density (s.take k) ≤ density s := by
  conv_rhs => rw [← List.take_append_drop k s]
  rw [density_append]
  linarith [density_nonneg (s.drop k)]

theorem length_le_density (a₀ : ℕ) :
    ∀ s : List ℕ, (∀ x ∈ s, 1 ≤ x ∧ x ≤ a₀) → (s.length : ℚ) ≤ a₀ * density s := by
  intro s
  induction s with
  | nil => intro _; simp [density]
  | cons x t ih =>
    intro h
    have h1 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    obtain ⟨hx1, hx2⟩ := h x (by simp)
    have hxq : (0 : ℚ) < x := by exact_mod_cast hx1
    have h2 : (1 : ℚ) ≤ a₀ * (1 / (x : ℚ)) := by
      rw [mul_one_div, le_div_iff₀ hxq]; simpa using (by exact_mod_cast hx2 : (x : ℚ) ≤ a₀)
    have : density (x :: t) = 1 / (x : ℚ) + density t := by simp [density]
    rw [this, List.length_cons]; push_cast
    nlinarith

/-! ### Completeness of the generic enumerator (copied from LB2) -/

theorem enum_complete (ok : List ℕ → Bool) (lo hi : ℕ) :
    ∀ (c pref : List ℕ) (fuel : ℕ), c ≠ [] → c.length ≤ fuel → (pref ++ c).Pairwise (· ≤ ·) →
      (∀ x ∈ c, lo ≤ x ∧ x < hi) →
      (∀ k, pref.length < k → k ≤ (pref ++ c).length → ok ((pref ++ c).take k) = true) →
      pref ++ c ∈ enumSorted ok lo hi fuel pref := by
  intro c
  induction c with
  | nil => intro _ _ hne; exact absurd rfl hne
  | cons v c' ih =>
    intro pref fuel _ hlen hsort hrange hok
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
    have hv := hrange v (by simp)
    have hstart : max lo (pref.getLast?.getD lo) ≤ v := by
      refine max_le hv.1 ?_
      cases hl : pref.getLast? with
      | none => simpa using hv.1
      | some w =>
        simp only [Option.getD_some]
        have hw : w ∈ pref := List.mem_of_getLast? hl
        exact (List.pairwise_append.mp hsort).2.2 w hw v (by simp)
    have e : (pref ++ [v]) ++ c' = pref ++ v :: c' := by simp
    have hokp : ok (pref ++ [v]) = true := by
      have := hok (pref.length + 1) (by omega) (by simp)
      rw [← e, List.take_left' (by simp)] at this
      exact this
    simp only [enumSorted]
    rw [List.mem_flatMap]
    refine ⟨v, ?_, ?_⟩
    · rw [List.mem_range'_1]; omega
    · rw [if_pos hokp]
      by_cases hc' : c' = []
      · subst hc'; simp
      · apply List.mem_cons_of_mem
        have := ih (pref ++ [v]) f hc' (by simp at hlen; omega) (by rw [e]; exact hsort)
          (fun x hx => hrange x (List.mem_cons_of_mem _ hx))
          (by rw [e]; intro k hk1 hk2; exact hok k (by simp at hk1; omega) (by simpa using hk2))
        rwa [e] at this
    
end PinwheelDensity.ExactRange.Dev.LE1Aux
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.LE1

open PinwheelDensity.ExactRange PinwheelDensity.ExactRange.Dev.LE1Aux

theorem foldOf_sorted (θ : ℕ) (A : List ℕ) : (foldOf θ A).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ _

/-- A valid absorption record certifies every target whose small part is `rec.S`. -/
theorem abs_sound (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (rec : AbsRecord) (hrec : checkAbsRecord B rec = true) (h : ℕ) (A : List ℕ)
    (hA : IsTarget m B A) (hl : rec.l ≤ h)
    (hS : rec.S.Perm (A.filter (fun x => x < h))) : Schedulable A := by
  unfold checkAbsRecord at hrec
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrec
  obtain ⟨⟨hSpos, hδ⟩, hall⟩ := hrec
  set δ : ℚ := B - density rec.S with hδdef
  set lStar : ℕ := max rec.l ⌈1 / δ⌉₊ with hlStar
  have hδ1 : δ ≤ 1 := by
    have := density_nonneg rec.S
    linarith
  have hl1 : 1 ≤ lStar := by
    refine le_trans ?_ (le_max_right _ _)
    exact Nat.ceil_pos.mpr (by positivity)
  have hcases : ∀ s : List ℕ, s.Pairwise (· ≤ ·) → (∀ x ∈ s, lStar ≤ x ∧ x < rec.a₀) →
      density s ≤ δ → ∃ w : List ℕ, absorbCaseOK δ rec.S s w rec.a₀ = true := by
    intro s hs hrange hd
    have hmem : s ∈ absEnum δ lStar rec.a₀ := by
      by_cases hne : s = []
      · subst hne; simp [absEnum]
      · unfold absEnum
        apply List.mem_cons_of_mem
        have hlen : s.length ≤ rec.a₀ + 1 := by
          have h1 := length_le_density rec.a₀ s (fun x hx =>
            ⟨le_trans hl1 (hrange x hx).1, (hrange x hx).2.le⟩)
          have h2 : (s.length : ℚ) ≤ rec.a₀ := by
            have h3 : (0 : ℚ) ≤ rec.a₀ := by positivity
            have : (rec.a₀ : ℚ) * density s ≤ rec.a₀ * 1 :=
              mul_le_mul_of_nonneg_left (hd.trans hδ1) h3
            linarith
          have : s.length ≤ rec.a₀ := by exact_mod_cast h2
          omega
        have := enum_complete (fun p => decide (density p ≤ δ)) lStar rec.a₀ s [] (rec.a₀ + 1)
          hne hlen (by simpa using hs) hrange
          (by
            intro k _ _
            simp only [List.nil_append, decide_eq_true_eq]
            exact (density_take_le s k).trans hd)
        simpa using this
    have := hall s hmem
    cases hl : rec.cases.lookup s with
    | none => simp [hl] at this
    | some w => exact ⟨w, by simpa [hl] using this⟩
  set T : List ℕ := A.filter (fun x => !decide (x < h)) with hT
  have hperm : (rec.S ++ T).Perm A :=
    (hS.append_right T).trans (List.filter_append_perm _ _)
  have hSpos' : ∀ a ∈ rec.S, 1 ≤ a := fun a ha => by have := hSpos a ha; omega
  have hTpos : ∀ a ∈ T, 1 ≤ a ∧ rec.l ≤ a := by
    intro a ha
    rw [hT, List.mem_filter] at ha
    have h1 : h ≤ a := by simpa using ha.2
    exact ⟨le_trans hm (hA.1 a ha.1), le_trans hl h1⟩
  have hdens : density (rec.S ++ T) ≤ B := by
    rw [density_perm hperm]; exact hA.2
  have := prop_D_3 B hB0 hB1 rec.S hSpos' δ hδdef (by simpa using hδ) rec.l rec.a₀ lStar hlStar
    hcases T hTpos hdens
  exact schedulable_perm hperm this

theorem cert_sound (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (recs : List AbsRecord) (θ : ℕ) (hθ : Even θ) (hθ4 : 4 ≤ θ) (A : List ℕ)
    (hA : IsTarget m B A) (cert : CellCert)
    (hv : certValid B recs θ (cellOf θ A) cert = true) : Schedulable A := by
  have hB1' := lemma_B_1 m hm B hB0 hB1 θ hθ hθ4 A hA
  cases cert with
  | tree sm T =>
    simp only [certValid] at hv
    have h1 := prop_C_3 sm (beta B θ) T _ _ hv (foldOf θ A) (foldOf_sorted θ A) hB1'.1
    have h2 := hB1'.2.2.2 h1
    have h3 := (lemma_A_1.2.1 A (fun a ha => le_trans hm (hA.1 a ha))).mp h2
    exact h3
  | absorb i =>
    simp only [certValid] at hv
    cases hr : recs[i]? with
    | none => simp [hr] at hv
    | some rec =>
      simp only [hr, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
      obtain ⟨⟨hS, hl⟩, hrec⟩ := hv
      refine abs_sound m hm B hB0 hB1 rec hrec (θ / 2) A hA hl ?_
      rw [hS]; exact hB1'.2.2.1

theorem stages_sound (m : ℕ) (hm : 1 ≤ m) (B : ℚ) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (recs : List AbsRecord) :
    ∀ (stages : List Stage) (θ : ℕ) (K : List (List ℕ)), Even θ → 4 ≤ θ →
      checkStages B recs θ K stages = true →
      ∀ A : List ℕ, IsTarget m B A → cellOf θ A ∈ K → Schedulable A := by
  intro stages
  induction stages with
  | nil => intro θ K _ _ h; simp [checkStages] at h
  | cons st rest ih =>
    intro θ K hθ hθ4 hchk A hA hmem
    cases rest with
    | nil =>
      rw [checkStages, Bool.and_eq_true] at hchk
      obtain ⟨hall0, hres⟩ := hchk
      have hall := List.all_eq_true.mp hall0
      have h1 := hall _ hmem
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.contains_iff_mem] at h1
      rcases h1 with ⟨e, he, heq, hv⟩ | hr
      · exact cert_sound m hm B hB0 hB1 recs θ hθ hθ4 A hA e.2 hv
      · have : st.residual = [] := by simpa using hres
        rw [this] at hr; simp at hr
    | cons r rs =>
      rw [checkStages, Bool.and_eq_true] at hchk
      obtain ⟨hall0, hnext0⟩ := hchk
      have hall := List.all_eq_true.mp hall0
      have hnext : checkStages B recs (θ + 2) (st.residual.flatMap (unfoldCell B θ)) (r :: rs)
          = true := hnext0
      have h1 := hall _ hmem
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        List.contains_iff_mem] at h1
      rcases h1 with ⟨e, he, heq, hv⟩ | hr
      · exact cert_sound m hm B hB0 hB1 recs θ hθ hθ4 A hA e.2 hv
      · refine ih (θ + 2) _ (by obtain ⟨k, hk⟩ := hθ; exact ⟨k + 1, by omega⟩) (by omega)
          hnext A hA ?_
        rw [List.mem_flatMap]
        exact ⟨cellOf θ A, hr, ((prop_B_5 B θ hθ hθ4).1 m A hm hB0 hB1 hA).2.2⟩

theorem main (P : Params) (d : Run) (h : checkRun P d = true) : Guarantee P.m P.B := by
  unfold checkRun at h
  simp only [Bool.and_eq_true, paramsOK, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hm, hθ4⟩, hθ2⟩, hB0⟩, hB1⟩, hst⟩ := h
  have hθ : Even P.θ₀ := Nat.even_iff.mpr hθ2
  intro A hA hd
  by_cases hne : A = []
  · subst hne; exact schedulable_nil
  have hT : IsTarget P.m P.B A := ⟨fun a ha => (hA a ha).2, hd⟩
  exact stages_sound P.m hm P.B hB0 hB1 d.records d.stages P.θ₀ _ hθ hθ4 hst A hT
    (lemma_B_2 P.m hm P.B hB0 hB1 P.θ₀ hθ hθ4 A hne hT).2

end PinwheelDensity.ExactRange.Dev.LE1

namespace PinwheelDensity.ExactRange

theorem chk_theorem_E_1 (P : Params) (d : Run) (h : checkRun P d = true) :
    Guarantee P.m P.B := PinwheelDensity.ExactRange.Dev.LE1.main P d h

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_theorem_E_1 := @PinwheelDensity.ExactRange.chk_theorem_E_1
