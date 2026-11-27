-- Prove2me | solution 1 for SPFacilityGraph.lemma_Q_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:58:17.634438+00:00
-- url     : https://prove2.me/submissions/9460b0de-ed5c-4bc0-b5dc-265ace0c7003

import Mathlib
import Theorems.Thm_SPFacilityGraph_lemma_I_1
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
import Theorems.Thm_SPFacilityGraph_attribution_of_lipschitz
import Theorems.Thm_SPFacilityGraph_lemma_Q_3_median_representation
import Definitions.Def_SPFacilityGraph_IsSP

set_option autoImplicit false


namespace SPFGSeg

variable {n : ℕ}

/-- profiles in `[a,b]ⁿ` -/
def InA (a b : ℝ) (u : Fin n → ℝ) : Prop := ∀ j, u j ∈ Set.Icc a b

/-- hypotheses: SP, values in `[a,b]`, onto `[a,b]` -/
structure Hyp (a b : ℝ) (F : (Fin n → ℝ) → ℝ) : Prop where
  hab : a ≤ b
  sp : ∀ u, InA a b u → ∀ i, ∀ v ∈ Set.Icc a b, |F u - u i| ≤ |F (Function.update u i v) - u i|
  range : ∀ u, InA a b u → F u ∈ Set.Icc a b
  onto : ∀ s ∈ Set.Icc a b, ∃ u, InA a b u ∧ F u = s

variable {a b : ℝ} {F : (Fin n → ℝ) → ℝ}

lemma InA.update {u : Fin n → ℝ} (hu : InA a b u) (i : Fin n) {v : ℝ} (hv : v ∈ Set.Icc a b) :
    InA a b (Function.update u i v) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hv
  · rw [Function.update_of_ne h]; exact hu j

/-- coalition `C` reports `v`, others as in `u` -/
def setC (C : Finset (Fin n)) (u : Fin n → ℝ) (v : ℝ) : Fin n → ℝ :=
  fun j => if j ∈ C then v else u j

lemma InA.setC {u : Fin n → ℝ} (hu : InA a b u) (C : Finset (Fin n)) {v : ℝ}
    (hv : v ∈ Set.Icc a b) : InA a b (setC C u v) := by
  intro j; unfold SPFGSeg.setC; split_ifs
  · exact hv
  · exact hu j

lemma InA.const {v : ℝ} (hv : v ∈ Set.Icc a b) : InA a b (fun _ : Fin n => v) := fun _ => hv

lemma setC_insert (C : Finset (Fin n)) (c : Fin n) (u : Fin n → ℝ) (v : ℝ) :
    setC (insert c C) u v = Function.update (setC C u v) c v := by
  classical
  funext j
  by_cases h : j = c
  · subst h; simp [setC]
  · simp [setC, Function.update_of_ne h, h]

lemma setC_insert' (C : Finset (Fin n)) (c : Fin n) (u : Fin n → ℝ) (v : ℝ) :
    setC (insert c C) u v = setC C (Function.update u c v) v := by
  classical
  funext j
  by_cases h : j = c
  · subst h; simp [setC]
  · simp [setC, Function.update_of_ne h, h]

lemma setC_empty (u : Fin n → ℝ) (v : ℝ) : setC ∅ u v = u := by
  funext j; simp [setC]

lemma setC_univ (u : Fin n → ℝ) (v : ℝ) : setC Finset.univ u v = fun _ => v := by
  funext j; simp [setC]

/-- unanimity -/
lemma unanimity (hF : Hyp a b F) {s : ℝ} (hs : s ∈ Set.Icc a b) : F (fun _ => s) = s := by
  classical
  obtain ⟨u, hu, hFu⟩ := hF.onto s hs
  have key : ∀ C : Finset (Fin n), F (setC C u s) = s := by
    intro C
    induction C using Finset.induction_on with
    | empty => rw [setC_empty]; exact hFu
    | insert c C hc ih =>
      rw [setC_insert]
      have h1 := hF.sp (Function.update (setC C u s) c s) ((hu.setC C hs).update c hs) c (u c) (hu c)
      have e1 : Function.update (Function.update (setC C u s) c s) c (u c) = setC C u s := by
        funext j
        by_cases h : j = c
        · subst h; simp [setC, hc]
        · simp [Function.update_of_ne h]
      rw [e1, ih] at h1
      simp only [Function.update_self, sub_self, abs_zero] at h1
      exact sub_eq_zero.1 (abs_nonpos_iff.1 h1)
  have := key Finset.univ
  rwa [setC_univ] at this

/-- monotonicity in one coordinate -/
lemma mono1 (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) (i : Fin n) {v v' : ℝ}
    (hv : v ∈ Set.Icc a b) (hv' : v' ∈ Set.Icc a b) (hvv : v ≤ v') :
    F (Function.update u i v) ≤ F (Function.update u i v') := by
  by_contra hc
  push Not at hc
  rcases hvv.lt_or_eq with hlt | heq
  · have h1 := hF.sp (Function.update u i v) (hu.update i hv) i v' hv'
    have h2 := hF.sp (Function.update u i v') (hu.update i hv') i v hv
    simp only [Function.update_self, Function.update_idem] at h1 h2
    rw [← sq_le_sq] at h1 h2
    nlinarith [mul_pos (sub_pos.2 hc) (sub_pos.2 hlt)]
  · subst heq; exact lt_irrefl _ hc

/-- monotonicity in all coordinates -/
lemma mono (hF : Hyp a b F) {u u' : Fin n → ℝ} (hu : InA a b u) (hu' : InA a b u')
    (huu : ∀ j, u j ≤ u' j) : F u ≤ F u' := by
  classical
  have key : ∀ C : Finset (Fin n), F u ≤ F (fun j => if j ∈ C then u' j else u j) := by
    intro C
    induction C using Finset.induction_on with
    | empty => simp
    | insert c C hc ih =>
      have hmix : InA a b (fun j => if j ∈ C then u' j else u j) := by
        intro j; dsimp only; split_ifs
        · exact hu' j
        · exact hu j
      have e1 : (fun j => if j ∈ insert c C then u' j else u j) =
          Function.update (fun j => if j ∈ C then u' j else u j) c (u' c) := by
        funext j; by_cases h : j = c
        · subst h; simp
        · simp [Function.update_of_ne h, h]
      have e2 : (fun j => if j ∈ C then u' j else u j) =
          Function.update (fun j => if j ∈ C then u' j else u j) c (u c) := by
        funext j; by_cases h : j = c
        · subst h; simp [hc]
        · simp [Function.update_of_ne h]
      rw [e1]
      refine ih.trans ?_
      conv_lhs => rw [e2]
      exact mono1 hF hmix c (hu c) (hu' c) (huu c)
  simpa using key Finset.univ

/-- coalition cloning preserves strategy-proofness -/
lemma clone (hF : Hyp a b F) (C : Finset (Fin n)) {u : Fin n → ℝ} (hu : InA a b u)
    {v v' : ℝ} (hv : v ∈ Set.Icc a b) (hv' : v' ∈ Set.Icc a b) :
    |F (setC C u v) - v| ≤ |F (setC C u v') - v| := by
  classical
  induction C using Finset.induction_on generalizing u with
  | empty => simp [setC_empty]
  | insert c C hc ih =>
    rw [setC_insert', setC_insert']
    refine (ih (hu.update c hv)).trans ?_
    have hP : InA a b (setC C (Function.update u c v) v') := (hu.update c hv).setC C hv'
    have h := hF.sp _ hP c v' hv'
    have e1 : setC C (Function.update u c v) v' c = v := by simp [setC, hc]
    have e2 : Function.update (setC C (Function.update u c v) v') c v' =
        setC C (Function.update u c v') v' := by
      funext j; by_cases h : j = c
      · subst h; simp [setC, hc]
      · simp [setC, Function.update_of_ne h]
    rw [e1, e2] at h
    exact h

/-- extraction of a gap in the range of a nearest-point function -/
lemma gap_extract (g : ℝ → ℝ) (hsp : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b, |g v - v| ≤ |g v' - v|)
    (hrange : ∀ v ∈ Set.Icc a b, g v ∈ Set.Icc a b) (z : ℝ) {v1 v2 : ℝ}
    (hv1 : v1 ∈ Set.Icc a b) (hv2 : v2 ∈ Set.Icc a b) (h1 : g v1 < z) (h2 : z < g v2)
    (hnot : ∀ v ∈ Set.Icc a b, g v ≠ z) :
    ∃ α β, α < z ∧ z < β ∧ (∃ va ∈ Set.Icc a b, g va = α) ∧ (∃ vb ∈ Set.Icc a b, g vb = β) ∧
      ∀ v ∈ Set.Icc a b, g v ≤ α ∨ β ≤ g v := by
  set O := {y | ∃ v ∈ Set.Icc a b, g v = y} with hO
  have hOA : ∀ y ∈ O, y ∈ Set.Icc a b := by rintro y ⟨v, hv, rfl⟩; exact hrange v hv
  have hne1 : (O ∩ Set.Iic z).Nonempty := ⟨g v1, ⟨v1, hv1, rfl⟩, h1.le⟩
  have hne2 : (O ∩ Set.Ici z).Nonempty := ⟨g v2, ⟨v2, hv2, rfl⟩, h2.le⟩
  have hb1 : BddAbove (O ∩ Set.Iic z) := ⟨z, fun y hy => hy.2⟩
  have hb2 : BddBelow (O ∩ Set.Ici z) := ⟨z, fun y hy => hy.2⟩
  set α := sSup (O ∩ Set.Iic z)
  set β := sInf (O ∩ Set.Ici z)
  have hαz : α ≤ z := csSup_le hne1 (fun y hy => hy.2)
  have hzβ : z ≤ β := le_csInf hne2 (fun y hy => hy.2)
  have hαA : α ∈ Set.Icc a b := ⟨(hOA _ hne1.some_mem.1).1.trans (le_csSup hb1 hne1.some_mem),
    hαz.trans (h2.le.trans (hrange v2 hv2).2)⟩
  have hβA : β ∈ Set.Icc a b := ⟨((hrange v1 hv1).1.trans h1.le).trans hzβ,
    (csInf_le hb2 hne2.some_mem).trans (hOA _ hne2.some_mem.1).2⟩
  have hαO : α ∈ O := by
    by_contra hc
    have hδ : 0 < |g α - α| := abs_pos.2 (fun h => hc ⟨α, hαA, sub_eq_zero.1 h⟩)
    obtain ⟨o, ⟨⟨vo, hvo, rfl⟩, hoz⟩, hlt⟩ := exists_lt_of_lt_csSup hne1 (show α - |g α - α| < α by linarith)
    have := hsp α hαA vo hvo
    have hle : g vo ≤ α := le_csSup hb1 ⟨⟨vo, hvo, rfl⟩, hoz⟩
    rw [abs_of_nonpos (by linarith : g vo - α ≤ 0)] at this
    linarith
  have hβO : β ∈ O := by
    by_contra hc
    have hδ : 0 < |g β - β| := abs_pos.2 (fun h => hc ⟨β, hβA, sub_eq_zero.1 h⟩)
    obtain ⟨o, ⟨⟨vo, hvo, rfl⟩, hoz⟩, hlt⟩ := exists_lt_of_csInf_lt hne2 (show β < β + |g β - β| by linarith)
    have := hsp β hβA vo hvo
    have hle : β ≤ g vo := csInf_le hb2 ⟨⟨vo, hvo, rfl⟩, hoz⟩
    rw [abs_of_nonneg (by linarith : 0 ≤ g vo - β)] at this
    linarith
  obtain ⟨va, hva, hga⟩ := hαO
  obtain ⟨vb, hvb, hgb⟩ := hβO
  refine ⟨α, β, lt_of_le_of_ne hαz (fun h => hnot va hva (hga.trans h)),
    lt_of_le_of_ne hzβ (fun h => hnot vb hvb (hgb.trans h.symm)), ⟨va, hva, hga⟩, ⟨vb, hvb, hgb⟩, ?_⟩
  intro v hv
  rcases le_total (g v) z with h | h
  · left; exact le_csSup hb1 ⟨⟨v, hv, rfl⟩, h⟩
  · right; exact csInf_le hb2 ⟨⟨v, hv, rfl⟩, h⟩

/-- values of a nearest-point function inside a gap -/
lemma gap_values (g : ℝ → ℝ) (hsp : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b, |g v - v| ≤ |g v' - v|)
    {α β : ℝ} (hαβ : α < β) (va vb : ℝ) (hva : va ∈ Set.Icc a b) (hvb : vb ∈ Set.Icc a b)
    (hga : g va = α) (hgb : g vb = β) (hgap : ∀ v ∈ Set.Icc a b, g v ≤ α ∨ β ≤ g v)
    (y : ℝ) (hy : y ∈ Set.Icc a b) :
    ((α + β) / 2 < y → y < β → g y = β) ∧ (α < y → y < (α + β) / 2 → g y = α) := by
  constructor
  · intro h1 h2
    have := hsp y hy vb hvb
    rw [hgb] at this
    rcases hgap y hy with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ β - y)] at this
      have : y - g y ≤ |g y - y| := by rw [abs_sub_comm]; exact le_abs_self _
      linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ β - y), abs_of_nonneg (by linarith : 0 ≤ g y - y)] at this
      linarith
  · intro h1 h2
    have := hsp y hy va hva
    rw [hga] at this
    rcases hgap y hy with h | h
    · rw [abs_of_nonpos (by linarith : α - y ≤ 0), abs_of_nonpos (by linarith : g y - y ≤ 0)] at this
      linarith
    · rw [abs_of_nonpos (by linarith : α - y ≤ 0)] at this
      have : g y - y ≤ |g y - y| := le_abs_self _
      linarith

/-- clamp form from the interval property -/
lemma clamp_of_interval (g : ℝ → ℝ) (hab : a ≤ b)
    (hsp : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b, |g v - v| ≤ |g v' - v|)
    (hmono : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b, v ≤ v' → g v ≤ g v')
    (hint : ∀ z, g a ≤ z → z ≤ g b → ∃ v ∈ Set.Icc a b, g v = z) :
    ∀ v ∈ Set.Icc a b, g v = max (g a) (min v (g b)) := by
  intro v hv
  have haA : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbA : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hlo : g a ≤ g v := hmono a haA v hv hv.1
  have hhi : g v ≤ g b := hmono v hv b hbA hv.2
  have hab' : g a ≤ g b := hlo.trans hhi
  obtain ⟨v', hv', hgv'⟩ := hint (max (g a) (min v (g b))) (le_max_left _ _)
    (max_le hab' (min_le_right _ _))
  have := hsp v hv v' hv'
  rw [hgv'] at this
  rcases le_or_gt v (g a) with h1 | h1
  · rw [max_eq_left (min_le_of_left_le h1)] at this ⊢
    rw [abs_of_nonneg (by linarith : 0 ≤ g v - v), abs_of_nonneg (by linarith : 0 ≤ g a - v)] at this
    linarith
  · rcases le_or_gt v (g b) with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1.le] at this ⊢
      rw [sub_self, abs_zero] at this
      exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
    · rw [min_eq_right h2.le, max_eq_right hab'] at this ⊢
      rw [abs_of_nonpos (by linarith : g v - v ≤ 0), abs_of_nonpos (by linarith : g b - v ≤ 0)] at this
      linarith

lemma setC_const_self (C : Finset (Fin n)) (w : ℝ) : setC C (fun _ => w) w = fun _ => w := by
  funext j; simp [setC]

lemma setC_compl_const (C : Finset (Fin n)) (w v : ℝ) :
    setC Cᶜ (setC C (fun _ => w) v) v = fun _ => v := by
  classical
  funext j; by_cases h : j ∈ C <;> simp [setC, h]

lemma setC_compl_self (C : Finset (Fin n)) (w v : ℝ) :
    setC Cᶜ (setC C (fun _ => w) v) w = setC C (fun _ => w) v := by
  classical
  funext j; by_cases h : j ∈ C <;> simp [setC, h]

/-- the range of a two-group cloned rule is an interval -/
lemma two_group_interval (hF : Hyp a b F) (C : Finset (Fin n)) {w : ℝ} (hw : w ∈ Set.Icc a b) :
    ∀ z, F (setC C (fun _ => w) a) ≤ z → z ≤ F (setC C (fun _ => w) b) →
      ∃ v ∈ Set.Icc a b, F (setC C (fun _ => w) v) = z := by
  classical
  have haA : a ∈ Set.Icc a b := ⟨le_rfl, hF.hab⟩
  have hbA : b ∈ Set.Icc a b := ⟨hF.hab, le_rfl⟩
  set g : ℝ → ℝ := fun v => F (setC C (fun _ => w) v) with hg
  have hsp : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b, |g v - v| ≤ |g v' - v| :=
    fun v hv v' hv' => clone hF C (InA.const hw) hv hv'
  have hrange : ∀ v ∈ Set.Icc a b, g v ∈ Set.Icc a b :=
    fun v hv => hF.range _ ((InA.const hw).setC C hv)
  intro z hz1 hz2
  by_contra hnot
  push Not at hnot
  have hz1' : g a < z := lt_of_le_of_ne hz1 (fun h => hnot a haA h)
  have hz2' : z < g b := lt_of_le_of_ne hz2 (fun h => hnot b hbA h.symm)
  obtain ⟨α, β, hαz, hzβ, ⟨va, hva, hga⟩, ⟨vb, hvb, hgb⟩, hgap⟩ :=
    gap_extract g hsp hrange z haA hbA hz1' hz2' hnot
  have hαβ : α < β := hαz.trans hzβ
  have hwg : g w = w := by simp only [g]; rw [setC_const_self]; exact unanimity hF hw
  have hαA : α ∈ Set.Icc a b := hga ▸ hrange va hva
  have hβA : β ∈ Set.Icc a b := hgb ▸ hrange vb hvb
  rcases hgap w hw with hwα | hwβ
  · -- w ≤ α : take y in the upper half
    rw [hwg] at hwα
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((α + β) / 2 + β) / 2 := ⟨_, rfl⟩
    have hyA : y ∈ Set.Icc a b := ⟨by linarith [hαA.1], by linarith [hβA.2]⟩
    have hgy := (gap_values g hsp hαβ va vb hva hvb hga hgb hgap y hyA).1 (by linarith) (by linarith)
    have hc := clone hF Cᶜ ((InA.const hw).setC C hyA) hw hyA
    rw [setC_compl_self, setC_compl_const, unanimity hF hyA] at hc
    have : F (setC C (fun _ => w) y) = β := hgy
    rw [this, abs_of_nonneg (by linarith : 0 ≤ β - w), abs_of_nonneg (by linarith : 0 ≤ y - w)] at hc
    linarith
  · rw [hwg] at hwβ
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (α + (α + β) / 2) / 2 := ⟨_, rfl⟩
    have hyA : y ∈ Set.Icc a b := ⟨by linarith [hαA.1], by linarith [hβA.2]⟩
    have hgy := (gap_values g hsp hαβ va vb hva hvb hga hgb hgap y hyA).2 (by linarith) (by linarith)
    have hc := clone hF Cᶜ ((InA.const hw).setC C hyA) hw hyA
    rw [setC_compl_self, setC_compl_const, unanimity hF hyA] at hc
    have : F (setC C (fun _ => w) y) = α := hgy
    rw [this, abs_of_nonpos (by linarith : α - w ≤ 0), abs_of_nonpos (by linarith : y - w ≤ 0)] at hc
    linarith

/-- clamp form of a two-group cloned rule -/
lemma two_group_clamp (hF : Hyp a b F) (C : Finset (Fin n)) {w : ℝ} (hw : w ∈ Set.Icc a b) :
    ∀ v ∈ Set.Icc a b, F (setC C (fun _ => w) v) =
      max (F (setC C (fun _ => w) a)) (min v (F (setC C (fun _ => w) b))) := by
  refine clamp_of_interval (fun v => F (setC C (fun _ => w) v)) hF.hab
    (fun v hv v' hv' => clone hF C (InA.const hw) hv hv') ?_ (two_group_interval hF C hw)
  intro v hv v' hv' hvv
  refine mono hF ((InA.const hw).setC C hv) ((InA.const hw).setC C hv') ?_
  intro j; simp only [setC]; split_ifs
  · exact hvv
  · exact le_rfl

/-- option sets are intervals -/
lemma option_interval (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) (i : Fin n) :
    ∀ z, F (Function.update u i a) ≤ z → z ≤ F (Function.update u i b) →
      ∃ v ∈ Set.Icc a b, F (Function.update u i v) = z := by
  classical
  have haA : a ∈ Set.Icc a b := ⟨le_rfl, hF.hab⟩
  have hbA : b ∈ Set.Icc a b := ⟨hF.hab, le_rfl⟩
  set g : ℝ → ℝ := fun v => F (Function.update u i v) with hg
  have hsp : ∀ v ∈ Set.Icc a b, ∀ v' ∈ Set.Icc a b, |g v - v| ≤ |g v' - v| := by
    intro v hv v' hv'
    have := hF.sp (Function.update u i v) (hu.update i hv) i v' hv'
    simpa only [Function.update_self, Function.update_idem] using this
  have hrange : ∀ v ∈ Set.Icc a b, g v ∈ Set.Icc a b := fun v hv => hF.range _ (hu.update i hv)
  intro z hz1 hz2
  by_contra hnot
  push Not at hnot
  have hz1' : g a < z := lt_of_le_of_ne hz1 (fun h => hnot a haA h)
  have hz2' : z < g b := lt_of_le_of_ne hz2 (fun h => hnot b hbA h.symm)
  obtain ⟨α, β, hαz, hzβ, ⟨va, hva, hga⟩, ⟨vb, hvb, hgb⟩, hgap⟩ :=
    gap_extract g hsp hrange z haA hbA hz1' hz2' hnot
  have hαβ : α < β := hαz.trans hzβ
  have hαA : α ∈ Set.Icc a b := hga ▸ hrange va hva
  have hβA : β ∈ Set.Icc a b := hgb ▸ hrange vb hvb
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((α + β) / 2 + β) / 2 := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y : ℝ, y = (α + (α + β) / 2) / 2 := ⟨_, rfl⟩
  have hyA : y ∈ Set.Icc a b := ⟨by linarith [hαA.1], by linarith [hβA.2]⟩
  have hyA' : y' ∈ Set.Icc a b := ⟨by linarith [hαA.1], by linarith [hβA.2]⟩
  have hgy : g y = β :=
    (gap_values g hsp hαβ va vb hva hvb hga hgb hgap y hyA).1 (by linarith) (by linarith)
  have hgy' : g y' = α :=
    (gap_values g hsp hαβ va vb hva hvb hga hgb hgap y' hyA').2 (by linarith) (by linarith)
  -- upper construction
  let C : Finset (Fin n) := insert i (Finset.univ.filter (fun j => u j < y))
  have hQ : β ≤ F (setC C (fun _ => b) y) := by
    rw [← hgy]
    refine mono hF (hu.update i hyA) ((InA.const hbA).setC C hyA) ?_
    intro j
    by_cases hji : j = i
    · subst hji; simp [setC, C]
    · rw [Function.update_of_ne hji]
      by_cases hj : u j < y
      · simp only [setC, C, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, hj,
          or_true, if_true]; exact hj.le
      · simp only [setC, C, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, hj,
          hji, or_false, if_false]; exact (hu j).2
  have hΦ := two_group_clamp hF C hbA y hyA
  have hΦa : β ≤ F (setC C (fun _ => b) a) := by
    have h1 : y < F (setC C (fun _ => b) y) := by linarith
    rw [hΦ] at h1 hQ
    have h2 : min y (F (setC C (fun _ => b) b)) ≤ y := min_le_left _ _
    rcases le_total (F (setC C (fun _ => b) a)) (min y (F (setC C (fun _ => b) b))) with h | h
    · rw [max_eq_right h] at h1; linarith
    · rw [max_eq_left h] at hQ; exact hQ
  -- lower construction
  let C' : Finset (Fin n) := insert i (Finset.univ.filter (fun j => y' < u j))
  have hQ' : F (setC C' (fun _ => a) y') ≤ α := by
    rw [← hgy']
    refine mono hF ((InA.const haA).setC C' hyA') (hu.update i hyA') ?_
    intro j
    by_cases hji : j = i
    · subst hji; simp [setC, C']
    · rw [Function.update_of_ne hji]
      by_cases hj : y' < u j
      · simp only [setC, C', Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, hj,
          or_true, if_true]; exact hj.le
      · simp only [setC, C', Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, hj,
          hji, or_false, if_false]; exact (hu j).1
  have hΦ' := two_group_clamp hF C' haA y' hyA'
  have hΦb : F (setC C' (fun _ => a) b) ≤ α := by
    have h1 : F (setC C' (fun _ => a) y') < y' := by linarith
    rw [hΦ'] at h1 hQ'
    have hlb : F (setC C' (fun _ => a) a) ≤ F (setC C' (fun _ => a) b) :=
      mono hF ((InA.const haA).setC C' haA) ((InA.const haA).setC C' hbA) (by
        intro j; simp only [setC]; split_ifs
        · exact hF.hab
        · exact le_rfl)
    rcases le_total y' (F (setC C' (fun _ => a) b)) with h | h
    · rw [min_eq_left h] at h1
      have := le_max_right (F (setC C' (fun _ => a) a)) y'
      linarith
    · rw [min_eq_right h, max_eq_right hlb] at hQ'; exact hQ'
  -- comparison
  have hcomp : F (setC C (fun _ => b) a) ≤ F (setC C' (fun _ => a) b) := by
    refine mono hF ((InA.const hbA).setC C haA) ((InA.const haA).setC C' hbA) ?_
    intro j
    by_cases hj : j ∈ C
    · simp only [setC, hj, if_true]
      split_ifs
      · exact hF.hab
      · exact le_rfl
    · have hj' : j ∈ C' := by
        simp only [C, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
          not_lt] at hj
        simp only [C', Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        right; linarith [hj.2]
      simp only [setC, hj, hj', if_true, if_false]; exact le_rfl
  linarith

/-- clamp form of a slice -/
lemma clampF (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) (i : Fin n) :
    ∀ v ∈ Set.Icc a b, F (Function.update u i v) =
      max (F (Function.update u i a)) (min v (F (Function.update u i b))) := by
  refine clamp_of_interval (fun v => F (Function.update u i v)) hF.hab ?_ ?_
    (option_interval hF hu i)
  · intro v hv v' hv'
    have := hF.sp (Function.update u i v) (hu.update i hv) i v' hv'
    simpa only [Function.update_self, Function.update_idem] using this
  · intro v hv v' hv' hvv; exact mono1 hF hu i hv hv' hvv

lemma uncomp_up (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) (i : Fin n) (h : F u < u i) :
    F (Function.update u i b) = F u := by
  have hbA : b ∈ Set.Icc a b := ⟨hF.hab, le_rfl⟩
  have hc := clampF hF hu i
  have e := hc (u i) (hu i)
  rw [Function.update_eq_self] at e
  have hb := hc b hbA
  have hlohi : F (Function.update u i a) ≤ F (Function.update u i b) :=
    mono1 hF hu i ⟨le_rfl, hF.hab⟩ hbA hF.hab
  have hhi : F (Function.update u i b) ≤ b := (hF.range _ (hu.update i hbA)).2
  rw [e] at h ⊢
  rcases le_total (u i) (F (Function.update u i b)) with h1 | h1
  · rw [min_eq_left h1] at h; have := le_max_right (F (Function.update u i a)) (u i); linarith
  · rw [min_eq_right h1]
    rw [min_eq_right hhi] at hb
    rw [max_eq_right hlohi] at hb ⊢

lemma uncomp_down (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) (i : Fin n) (h : u i < F u) :
    F (Function.update u i a) = F u := by
  have haA : a ∈ Set.Icc a b := ⟨le_rfl, hF.hab⟩
  have hbA : b ∈ Set.Icc a b := ⟨hF.hab, le_rfl⟩
  have hc := clampF hF hu i
  have e := hc (u i) (hu i)
  rw [Function.update_eq_self] at e
  have ha := hc a haA
  have hlo : a ≤ F (Function.update u i a) := (hF.range _ (hu.update i haA)).1
  rw [e] at h ⊢
  rcases le_total (F (Function.update u i a)) (min (u i) (F (Function.update u i b))) with h1 | h1
  · rw [max_eq_right h1] at h
    have := min_le_left (u i) (F (Function.update u i b)); linarith
  · rw [max_eq_left h1]

/-- the extreme profile of a coalition -/
def ext (S : Finset (Fin n)) (a b : ℝ) : Fin n → ℝ := fun j => if j ∈ S then b else a

/-- thresholds -/
def thr (F : (Fin n → ℝ) → ℝ) (a b : ℝ) (S : Finset (Fin n)) : ℝ := F (ext S a b)

lemma InA.ext (hab : a ≤ b) (S : Finset (Fin n)) : InA a b (ext S a b) := by
  intro j; unfold SPFGSeg.ext; split_ifs
  · exact ⟨hab, le_rfl⟩
  · exact ⟨le_rfl, hab⟩

/-- moving agents not at the outcome to the extremes keeps the outcome -/
lemma push_extremes (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) :
    F (fun j => if F u < u j then b else if u j < F u then a else u j) = F u := by
  classical
  set m := F u
  set P : Fin n → ℝ := fun j => if m < u j then b else if u j < m then a else u j
  have hP : InA a b P := by
    intro j; simp only [P]; split_ifs
    · exact ⟨hF.hab, le_rfl⟩
    · exact ⟨le_rfl, hF.hab⟩
    · exact hu j
  have key : ∀ S : Finset (Fin n), F (fun j => if j ∈ S then P j else u j) = m := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [m]
    | insert c S hc ih =>
      set Z : Fin n → ℝ := fun j => if j ∈ S then P j else u j
      have hZ : InA a b Z := by
        intro j; simp only [Z]; split_ifs
        · exact hP j
        · exact hu j
      have e1 : (fun j => if j ∈ insert c S then P j else u j) = Function.update Z c (P c) := by
        funext j; by_cases h : j = c
        · subst h; simp
        · simp [Function.update_of_ne h, h, Z]
      have hZc : Z c = u c := by simp [Z, hc]
      rw [e1]
      by_cases h1 : m < u c
      · have hPc : P c = b := by simp [P, h1]
        rw [hPc, uncomp_up hF hZ c (by rw [ih, hZc]; exact h1), ih]
      · by_cases h2 : u c < m
        · have hPc : P c = a := by simp [P, h1, h2]
          rw [hPc, uncomp_down hF hZ c (by rw [ih, hZc]; exact h2), ih]
        · have hPc : P c = u c := by simp [P, h1, h2]
          rw [hPc, ← hZc, Function.update_eq_self, ih]
  simpa using key Finset.univ

/-- the generalized median voter scheme formula -/
theorem gmvs (hF : Hyp a b F) {u : Fin n → ℝ} (hu : InA a b u) :
    F u = Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
      (insert (thr F a b S) (S.image u)).min' (Finset.insert_nonempty _ _)) := by
  classical
  set m := F u
  set P : Fin n → ℝ := fun j => if m < u j then b else if u j < m then a else u j
  have hP : InA a b P := by
    intro j; simp only [P]; split_ifs
    · exact ⟨hF.hab, le_rfl⟩
    · exact ⟨le_rfl, hF.hab⟩
    · exact hu j
  have hFP : F P = m := push_extremes hF hu
  apply le_antisymm
  · -- choose S = {j | m ≤ u j}
    let T := Finset.univ.filter (fun j => m ≤ u j)
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ T))
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [← hFP]
      refine mono hF hP (InA.ext hF.hab T) ?_
      intro j
      simp only [ext, T, Finset.mem_filter, Finset.mem_univ, true_and, P]
      split_ifs <;> first | exact le_rfl | exact hF.hab | (exfalso; linarith) | exact (hu j).2 | linarith
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 hj).2
  · apply Finset.sup'_le
    intro S _
    by_cases hS : ∃ j ∈ S, u j ≤ m
    · obtain ⟨j, hj, hjm⟩ := hS
      exact (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj))).trans hjm
    · push Not at hS
      refine (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans ?_
      rw [← hFP]
      refine mono hF (InA.ext hF.hab S) hP ?_
      intro j
      simp only [ext, P]
      by_cases hj : j ∈ S
      · simp [hj, hS j hj]
      · simp only [hj, if_false]
        split_ifs
        · exact hF.hab
        · exact le_rfl
        · exact (hu j).1

end SPFGSeg



namespace SPFGSegGeo

open SPFacilityGraph

variable {k : ℕ}

lemma norm_le_dist (G : MetricGraph k) (a b : G.Pt) :
    ‖(a : EuclideanSpace ℝ (Fin k)) - b‖ ≤ G.dist a b := by
  obtain ⟨m, p, h0, hm, -, hL⟩ := G.exists_walk_eq_dist a b
  rw [← hL]
  have h := Finset.sum_range_sub p m
  rw [hm, h0] at h
  rw [norm_sub_rev, ← h]
  exact norm_sum_le _ _

/-- a straight segment inside the graph bounds the graph distance -/
lemma dist_le_norm_of_segment_sub (G : MetricGraph k) (x y : G.Pt)
    (hxy : segment ℝ (x : EuclideanSpace ℝ (Fin k)) y ⊆ G.carrier) :
    G.dist x y ≤ ‖(x : EuclideanSpace ℝ (Fin k)) - y‖ := by
  classical
  set X : EuclideanSpace ℝ (Fin k) := (x : EuclideanSpace ℝ (Fin k)) with hX
  set Y : EuclideanSpace ℝ (Fin k) := (y : EuclideanSpace ℝ (Fin k)) with hY
  let γ : ℝ → EuclideanSpace ℝ (Fin k) := fun s => X + s • (Y - X)
  let 𝒰 : Finset (Finset (EuclideanSpace ℝ (Fin k))) := G.edges.image (fun e => ({e.1, e.2} : Finset _))
  have hcov : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ ⋃ P ∈ 𝒰, convexHull ℝ (P : Set (EuclideanSpace ℝ (Fin k))) := by
    intro s hs
    have hmem : γ s ∈ G.carrier := hxy (by rw [segment_eq_image']; exact ⟨s, hs, rfl⟩)
    obtain ⟨e, he, hse⟩ := Set.mem_iUnion₂.1 hmem
    refine Set.mem_biUnion (Finset.mem_image_of_mem _ he) ?_
    rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair]; exact hse
  have hcont : ContinuousOn γ (Set.Icc 0 1) := by fun_prop
  have hpw : ∃ (p : ℕ) (r : Fin (p + 1) → ℝ), StrictMono r ∧ r 0 = 0 ∧ r (Fin.last p) = 1 ∧
      ∀ j : Fin p, ∃ a' b' : EuclideanSpace ℝ (Fin k), ∀ s ∈ Set.Icc (r j.castSucc) (r j.succ),
        γ s = a' + s • b' :=
    ⟨1, ![0, 1], by
      refine Fin.strictMono_iff_lt_succ.2 ?_
      intro j; fin_cases j; simp, rfl, rfl, fun _ => ⟨X, Y - X, fun s _ => rfl⟩⟩
  obtain ⟨M, s, hsm, hs0, hs1, hsP⟩ := lemma_I_1 𝒰 γ hcov hcont hpw
  let σ : ℕ → ℝ := fun l => if h : l ≤ M then s ⟨l, by omega⟩ else 1
  have hσ0 : σ 0 = 0 := by simp only [σ, dif_pos (Nat.zero_le _)]; exact hs0
  have hσM : σ M = 1 := by simp only [σ, dif_pos le_rfl]; exact hs1
  have hmono : ∀ l < M, σ l ≤ σ (l+1) := by
    intro l hl
    simp only [σ, dif_pos (show l ≤ M by omega), dif_pos (show l + 1 ≤ M by omega)]
    exact hsm.monotone (by simp [Fin.le_def])
  have hwalk := G.dist_le_walk x y M (fun l => γ (σ l)) (by simp [γ, hσ0, X]) (by simp [γ, hσM, X, Y]) (by
    intro l hl
    obtain ⟨P, hP, hsub⟩ := hsP ⟨l, hl⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hP
    rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at hsub
    refine ⟨e, he, ?_, ?_⟩
    · have h1 : σ l = s (Fin.castSucc ⟨l, hl⟩) := by
        simp only [σ, dif_pos (show l ≤ M by omega)]; rfl
      apply hsub
      exact ⟨σ l, ⟨by rw [h1], by rw [h1]; exact hsm.monotone (Fin.castSucc_le_succ _)⟩, rfl⟩
    · have h1 : σ (l+1) = s (Fin.succ ⟨l, hl⟩) := by
        simp only [σ, dif_pos (show l + 1 ≤ M by omega)]; rfl
      apply hsub
      exact ⟨σ (l+1), ⟨by rw [h1]; exact hsm.monotone (Fin.castSucc_le_succ _), by rw [h1]⟩, rfl⟩)
  refine hwalk.trans (le_of_eq ?_)
  have : ∀ l ∈ Finset.range M, ‖γ (σ (l+1)) - γ (σ l)‖ = (σ (l+1) - σ l) * ‖Y - X‖ := by
    intro l hl
    rw [Finset.mem_range] at hl
    simp only [γ]
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 (hmono l hl))]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, Finset.sum_range_sub, hσ0, hσM, norm_sub_rev]
  ring

end SPFGSegGeo



namespace SPFGSegGeo

open SPFacilityGraph

variable {k n : ℕ}

lemma seg_ne (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q) :
    p ≠ q := by
  intro hpq
  subst hpq
  obtain ⟨e, he⟩ := G.edges_nonempty
  have h1 : e.1 ∈ G.carrier := Set.mem_biUnion he (left_mem_segment ℝ _ _)
  have h2 : e.2 ∈ G.carrier := Set.mem_biUnion he (right_mem_segment ℝ _ _)
  rw [hG, segment_same] at h1 h2
  exact G.fst_ne_snd e he (h1.trans h2.symm)

lemma seg_param (p q z : EuclideanSpace ℝ (Fin k)) (hz : z ∈ segment ℝ p q) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, z = p + t • (q - p) ∧ ‖z - p‖ = t * ‖q - p‖ := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ht, rfl, ?_⟩
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]

/-- graph distance on a segment carrier is the difference of arclength coordinates -/
lemma seg_dist (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (x y : G.Pt) :
    G.dist x y = |‖(x : EuclideanSpace ℝ (Fin k)) - p‖ - ‖(y : EuclideanSpace ℝ (Fin k)) - p‖| := by
  have hx : (x : EuclideanSpace ℝ (Fin k)) ∈ segment ℝ p q := hG ▸ x.2
  have hy : (y : EuclideanSpace ℝ (Fin k)) ∈ segment ℝ p q := hG ▸ y.2
  obtain ⟨tx, htx, ex, nx⟩ := seg_param p q _ hx
  obtain ⟨ty, hty, ey, ny⟩ := seg_param p q _ hy
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin k)) - y‖ =
      |‖(x : EuclideanSpace ℝ (Fin k)) - p‖ - ‖(y : EuclideanSpace ℝ (Fin k)) - p‖| := by
    rw [nx, ny, ex, ey, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, ← sub_mul,
      abs_mul, abs_of_nonneg (norm_nonneg (q - p))]
  apply le_antisymm
  · rw [← hnorm]
    apply dist_le_norm_of_segment_sub
    intro z hz
    rw [hG]
    exact (convex_segment p q).segment_subset hx hy hz
  · rw [← hnorm]; exact norm_le_dist G x y

/-- point of the segment at arclength coordinate `s` -/
noncomputable def segPt (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k))
    (hG : G.carrier = segment ℝ p q) (s : ℝ) : G.Pt :=
  ⟨p + (min (max s 0) ‖q - p‖ / ‖q - p‖) • (q - p), by
    rw [hG, segment_eq_image']
    refine ⟨min (max s 0) ‖q - p‖ / ‖q - p‖, ⟨?_, ?_⟩, rfl⟩
    · exact div_nonneg (le_min (le_max_right _ _) (norm_nonneg _)) (norm_nonneg _)
    · rcases eq_or_lt_of_le (norm_nonneg (q - p)) with h | h
      · rw [← h]; simp
      · rw [div_le_one h]; exact min_le_right _ _⟩

lemma segPt_coord (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (s : ℝ) (hs : s ∈ Set.Icc 0 ‖q - p‖) :
    ‖((segPt G p q hG s : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖ = s := by
  have hL : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 (seg_ne G p q hG).symm)
  simp only [segPt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [max_eq_left hs.1, min_eq_left hs.2, abs_of_nonneg (div_nonneg hs.1 hL.le)]
  field_simp

lemma segPt_of_coord (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (x : G.Pt) : segPt G p q hG ‖(x : EuclideanSpace ℝ (Fin k)) - p‖ = x := by
  have hL : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 (seg_ne G p q hG).symm)
  have hx : (x : EuclideanSpace ℝ (Fin k)) ∈ segment ℝ p q := hG ▸ x.2
  obtain ⟨t, ht, ex, nx⟩ := seg_param p q _ hx
  apply Subtype.ext
  simp only [segPt]
  rw [nx, max_eq_left (mul_nonneg ht.1 hL.le),
    min_eq_left (by nlinarith [ht.2] : t * ‖q - p‖ ≤ ‖q - p‖), ex]
  congr 2
  field_simp

lemma coord_mem (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (x : G.Pt) : ‖(x : EuclideanSpace ℝ (Fin k)) - p‖ ∈ Set.Icc 0 ‖q - p‖ := by
  have hx : (x : EuclideanSpace ℝ (Fin k)) ∈ segment ℝ p q := hG ▸ x.2
  obtain ⟨t, ht, -, nx⟩ := seg_param p q _ hx
  rw [nx]
  exact ⟨mul_nonneg ht.1 (norm_nonneg _), by nlinarith [ht.2, norm_nonneg (q - p)]⟩

/-- the coordinate mechanism -/
noncomputable def coordF (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k))
    (hG : G.carrier = segment ℝ p q) (M : Profile G n → G.Pt) : (Fin n → ℝ) → ℝ :=
  fun u => ‖((M (fun j => segPt G p q hG (u j)) : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖

lemma coordF_coord (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k))
    (hG : G.carrier = segment ℝ p q) (M : Profile G n → G.Pt) (x : Profile G n) :
    coordF G p q hG M (fun j => ‖((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖) =
      ‖((M x : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖ := by
  simp only [coordF, segPt_of_coord]

lemma coordF_hyp (G : MetricGraph k) (p q : EuclideanSpace ℝ (Fin k))
    (hG : G.carrier = segment ℝ p q) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) : SPFGSeg.Hyp 0 ‖q - p‖ (coordF G p q hG M) := by
  refine ⟨norm_nonneg _, ?_, ?_, ?_⟩
  · intro u hu i v hv
    have h := hSP (fun j => segPt G p q hG (u j)) i (segPt G p q hG v)
    rw [seg_dist G p q hG, seg_dist G p q hG, segPt_coord G p q hG _ (hu i)] at h
    have e : (Function.update (fun j => segPt G p q hG (u j)) i (segPt G p q hG v)) =
        (fun j => segPt G p q hG (Function.update u i v j)) := by
      funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [e] at h
    exact h
  · intro u _; exact coord_mem G p q hG _
  · intro s hs
    obtain ⟨x, hx⟩ := hM (segPt G p q hG s)
    refine ⟨fun j => ‖((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖, fun j => coord_mem G p q hG _, ?_⟩
    rw [coordF_coord, hx, segPt_coord G p q hG s hs]

end SPFGSegGeo



namespace SPFGSegGeo

open SPFacilityGraph

variable {n : ℕ}

/-- one-coordinate perturbation of a max-min expression -/
lemma maxmin_le (t : Finset (Fin n) → ℝ) (u u' : Fin n → ℝ) (δ : ℝ)
    (h : ∀ j, u' j ≤ u j + δ) (hδ : 0 ≤ δ) :
    Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
        (insert (t S) (S.image u')).min' (Finset.insert_nonempty _ _)) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
        (insert (t S) (S.image u)).min' (Finset.insert_nonempty _ _)) + δ := by
  classical
  apply Finset.sup'_le
  intro S _
  refine le_trans ?_ (add_le_add_left (Finset.le_sup' (fun S : Finset (Fin n) =>
        (insert (t S) (S.image u)).min' (Finset.insert_nonempty _ _)) (Finset.mem_univ S)) δ)
  obtain hm := Finset.min'_mem (insert (t S) (S.image u)) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 hm with h1 | h1
  · rw [h1]
    exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (by linarith)
  · obtain ⟨j, hj, hju⟩ := Finset.mem_image.1 h1
    rw [← hju]
    exact (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u' hj))).trans (h j)

end SPFGSegGeo

open SPFacilityGraph SPFGSegGeo in
theorem SPFGSegGeo.Q3 {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K := by
  classical
  obtain ⟨t, ht, -, -, -, hform⟩ := lemma_Q_3_median_representation hn G p q hG M hSP hM
  set c : G.Pt → ℝ := fun x => ‖(x : EuclideanSpace ℝ (Fin k)) - p‖ with hc
  let W : Finset G.Pt := Finset.univ.image (fun S : Finset (Fin n) => segPt G p q hG (t S))
  have hLip : ∀ (x : Profile G n) (i : Fin n) (y : G.Pt),
      G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i) := by
    intro x i y
    rw [seg_dist G p q hG, seg_dist G p q hG, hform, hform]
    set δ := |‖(y : EuclideanSpace ℝ (Fin k)) - p‖ - ‖((x i : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖|
    have h1 : ∀ j, (fun j => ‖((Function.update x i y j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖) j ≤
        (fun j => ‖((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖) j + δ := by
      intro j; by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
        have := le_abs_self (‖(y : EuclideanSpace ℝ (Fin k)) - p‖ - ‖((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖)
        linarith
      · simp only [Function.update_of_ne hj]; linarith [abs_nonneg (‖(y : EuclideanSpace ℝ (Fin k)) - p‖ - ‖((x i : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖)]
    have h2 : ∀ j, (fun j => ‖((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖) j ≤
        (fun j => ‖((Function.update x i y j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖) j + δ := by
      intro j; by_cases hj : j = i
      · subst hj; simp only [Function.update_self]
        have := neg_abs_le (‖(y : EuclideanSpace ℝ (Fin k)) - p‖ - ‖((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖)
        linarith
      · simp only [Function.update_of_ne hj]; linarith [abs_nonneg (‖(y : EuclideanSpace ℝ (Fin k)) - p‖ - ‖((x i : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖)]
    have hδ : 0 ≤ δ := abs_nonneg _
    have e1 := maxmin_le t _ _ δ h1 hδ
    have e2 := maxmin_le t _ _ δ h2 hδ
    rw [abs_le]
    constructor <;> linarith
  have hval : ∀ x : Profile G n, (∃ i, M x = x i) ∨ M x ∈ W := by
    intro x
    have hf := hform x
    obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
          (insert (t S) (S.image fun i => ‖((x i : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖)).min'
            (Finset.insert_nonempty _ _))
    rw [hS] at hf
    have hmem := Finset.min'_mem (insert (t S) (S.image fun i => ‖((x i : G.Pt) : EuclideanSpace ℝ (Fin k)) - p‖))
      (Finset.insert_nonempty _ _)
    rw [← hf] at hmem
    rcases Finset.mem_insert.1 hmem with h | h
    · right
      refine Finset.mem_image.2 ⟨S, Finset.mem_univ _, ?_⟩
      rw [← h, segPt_of_coord]
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
      left; refine ⟨j, ?_⟩
      rw [← segPt_of_coord G p q hG (M x), ← hj, segPt_of_coord]
  obtain ⟨K, hK⟩ := attribution_of_lipschitz G M W hLip hval
  exact ⟨W, K, hK⟩


open SPFacilityGraph in
theorem solution {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k)
    (p q : EuclideanSpace ℝ (Fin k)) (hG : G.carrier = segment ℝ p q)
    (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ (W : Finset G.Pt) (K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k))),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K :=
  SPFGSegGeo.Q3 hn G p q hG M hSP hM
