-- Prove2me | solution 1 for SPFacilityGraph.sp_onto_finite_values
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:31:22.942742+00:00
-- url     : https://prove2.me/submissions/eeb79a41-f6cc-4b2d-bead-ad40ab0a34a6

import Mathlib
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_triangle
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_comm
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



namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

lemma dist_self (G : MetricGraph k) (x : G.Pt) : G.dist x x = 0 := by
  apply le_antisymm
  · have := G.dist_le_walk x x 0 (fun _ => (x : E k)) rfl rfl (fun j hj => absurd hj (by omega))
    simpa using this
  · obtain ⟨m, p, -, -, -, hL⟩ := G.exists_walk_eq_dist x x
    rw [← hL]; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma dist_nonneg (G : MetricGraph k) (x y : G.Pt) : 0 ≤ G.dist x y := by
  obtain ⟨m, p, -, -, -, hL⟩ := G.exists_walk_eq_dist x y
  rw [← hL]; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma norm_le_dist (G : MetricGraph k) (a b : G.Pt) : ‖(a : E k) - b‖ ≤ G.dist a b := by
  obtain ⟨m, p, h0, hm, -, hL⟩ := G.exists_walk_eq_dist a b
  rw [← hL]
  have h := Finset.sum_range_sub p m
  rw [hm, h0] at h
  rw [norm_sub_rev, ← h]
  exact norm_sum_le _ _

lemma dist_le_norm_of_edge (G : MetricGraph k) (a b : G.Pt) (e) (he : e ∈ G.edges)
    (ha : (a : E k) ∈ segment ℝ e.1 e.2) (hb : (b : E k) ∈ segment ℝ e.1 e.2) :
    G.dist a b ≤ ‖(a : E k) - b‖ := by
  have := G.dist_le_walk a b 1 (fun j => if j = 0 then (a : E k) else b)
    (by simp) (by simp) (by
      intro j hj
      have : j = 0 := by omega
      subst this
      exact ⟨e, he, by simpa using ha, by simpa using hb⟩)
  simpa [norm_sub_rev] using this

lemma dist_eq_norm_of_edge (G : MetricGraph k) (a b : G.Pt) (e) (he : e ∈ G.edges)
    (ha : (a : E k) ∈ segment ℝ e.1 e.2) (hb : (b : E k) ∈ segment ℝ e.1 e.2) :
    G.dist a b = ‖(a : E k) - b‖ :=
  le_antisymm (dist_le_norm_of_edge G a b e he ha hb) (norm_le_dist G a b)

lemma eq_of_dist_eq_zero (G : MetricGraph k) (a b : G.Pt) (h : G.dist a b = 0) : a = b := by
  have := norm_le_dist G a b
  rw [h] at this
  exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 this))

/-- Boundary crossing: a shortest walk from outside `U` to a point of `U` passes through a
boundary point. -/
lemma cross (G : MetricGraph k) (U : Set (E k)) (Bd : Set (E k))
    (hcross : ∀ e ∈ G.edges, ∀ a ∈ segment ℝ e.1 e.2, ∀ b ∈ segment ℝ e.1 e.2,
      a ∉ U → b ∈ U → ∃ q ∈ Bd, q ∈ segment ℝ a b)
    (p z : G.Pt) (hp : (p : E k) ∉ U) (hz : (z : E k) ∈ U) :
    ∃ q : G.Pt, (q : E k) ∈ Bd ∧ G.dist p z = G.dist p q + G.dist q z := by
  classical
  obtain ⟨m, w, h0, hm, hw, hL⟩ := G.exists_walk_eq_dist p z
  -- first index entering U
  have hex : ∃ j, w (j + 1) ∈ U ∧ j < m := by
    by_contra hc
    push Not at hc
    have : ∀ j, j ≤ m → w j ∉ U := by
      intro j hj
      induction j with
      | zero => rw [h0]; exact hp
      | succ j ih => intro hU; exact absurd (hc j hU) (by omega)
    exact this m le_rfl (hm ▸ hz)
  let j := Nat.find hex
  have hj : w (j + 1) ∈ U ∧ j < m := Nat.find_spec hex
  have hjU : w j ∉ U := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, h0]; exact hp
    · intro hU
      have := Nat.find_min hex (show j - 1 < j by omega)
      apply this
      rw [show j - 1 + 1 = j by omega]
      exact ⟨hU, by omega⟩
  obtain ⟨e, he, hwe, hwe'⟩ := hw j hj.2
  obtain ⟨q, hqB, hqs⟩ := hcross e he _ hwe _ hwe' hjU hj.1
  have hqe : q ∈ segment ℝ e.1 e.2 := (convex_segment _ _).segment_subset hwe hwe' hqs
  have hqc : q ∈ G.carrier := Set.mem_biUnion he hqe
  refine ⟨⟨q, hqc⟩, hqB, le_antisymm (G.dist_triangle _ _ _) ?_⟩
  -- the two half walks
  have h1 := G.dist_le_walk p ⟨q, hqc⟩ (j + 1) (fun l => if l ≤ j then w l else q)
    (by simp [h0]) (by simp) (by
      intro l hl
      by_cases hl' : l + 1 ≤ j
      · simpa [show l ≤ j by omega, hl'] using hw l (by omega)
      · have hlj : l = j := by omega
        rw [hlj]
        simp only [le_refl, if_true, show ¬ (j + 1 ≤ j) by omega, if_false]
        exact ⟨e, he, hwe, hqe⟩)
  have h2 := G.dist_le_walk ⟨q, hqc⟩ z (m - j) (fun l => if l = 0 then q else w (j + l))
    (by simp) (by
      simp only [show m - j ≠ 0 by omega, if_false]
      rw [show j + (m - j) = m by omega, hm]) (by
      intro l hl
      by_cases hl0 : l = 0
      · subst hl0; simp only [if_true, zero_add, one_ne_zero, if_false]
        exact ⟨e, he, hqe, hwe'⟩
      · simp only [hl0, if_false, show l + 1 ≠ 0 by omega]
        rw [show j + (l + 1) = j + l + 1 by omega]
        exact hw (j + l) (by omega))
  have hsplit : ‖q - w j‖ + ‖w (j + 1) - q‖ = ‖w (j + 1) - w j‖ := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hqs
    have e1 : a • w j + b • w (j + 1) - w j = b • (w (j + 1) - w j) := by
      rw [show a = 1 - b by linarith]; simp [sub_smul, smul_sub]; abel
    have e2 : w (j + 1) - (a • w j + b • w (j + 1)) = a • (w (j + 1) - w j) := by
      rw [show b = 1 - a by linarith]; simp [sub_smul, smul_sub]; abel
    rw [e1, e2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
      abs_of_nonneg hb, ← add_mul, add_comm b a, hab, one_mul]
  have hsum1 : ∑ l ∈ Finset.range (j + 1),
      ‖(if l + 1 ≤ j then w (l + 1) else q) - (if l ≤ j then w l else q)‖ =
      ∑ l ∈ Finset.range j, ‖w (l + 1) - w l‖ + ‖q - w j‖ := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_range] at hl
      simp [show l + 1 ≤ j by omega, show l ≤ j by omega]
    · simp only [le_refl, if_true, show ¬ (j + 1 ≤ j) by omega, if_false]
  have hsum2 : ∑ l ∈ Finset.range (m - j),
      ‖(if l + 1 = 0 then q else w (j + (l + 1))) - (if l = 0 then q else w (j + l))‖ =
      ‖w (j + 1) - q‖ + ∑ l ∈ Finset.range (m - (j + 1)), ‖w (j + 1 + l + 1) - w (j + 1 + l)‖ := by
    rw [show m - j = (m - (j + 1)) + 1 by omega, Finset.sum_range_succ', add_comm]
    refine congrArg₂ (· + ·) ?_ ?_
    · simp
    · apply Finset.sum_congr rfl; intro l _
      simp only [show l + 1 + 1 ≠ 0 by omega, show l + 1 ≠ 0 by omega, if_false]
      rw [show j + (l + 1 + 1) = j + 1 + l + 1 by omega, show j + (l + 1) = j + 1 + l by omega]
  have htot : ∑ l ∈ Finset.range m, ‖w (l + 1) - w l‖ =
      ∑ l ∈ Finset.range j, ‖w (l + 1) - w l‖ + ‖w (j + 1) - w j‖ +
        ∑ l ∈ Finset.range (m - (j + 1)), ‖w (j + 1 + l + 1) - w (j + 1 + l)‖ := by
    conv_lhs => rw [show m = (j + 1) + (m - (j + 1)) by omega, Finset.sum_range_add,
      Finset.sum_range_succ]
  rw [hsum1] at h1
  rw [hsum2] at h2
  rw [← hL, htot]
  linarith

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

/-- point of an edge at parameter `t` -/
def epar (e : E k × E k) (t : ℝ) : E k := e.1 + t • (e.2 - e.1)

lemma epar_mem {e : E k × E k} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : epar e t ∈ segment ℝ e.1 e.2 := by
  rw [segment_eq_image']; exact ⟨t, ht, rfl⟩

lemma mem_seg_iff (e : E k × E k) (q : E k) :
    q ∈ segment ℝ e.1 e.2 ↔ ∃ t ∈ Set.Icc (0:ℝ) 1, q = epar e t := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

lemma epar_inj {e : E k × E k} (he : e.1 ≠ e.2) {t s : ℝ} (h : epar e t = epar e s) : t = s := by
  have : (t - s) • (e.2 - e.1) = 0 := by
    rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel h)
  rcases smul_eq_zero.1 this with h' | h'
  · linarith
  · exact absurd (sub_eq_zero.1 h').symm he

lemma epar_sub (e : E k × E k) (t s : ℝ) : epar e t - epar e s = (t - s) • (e.2 - e.1) := by
  simp only [epar]; rw [sub_smul]; abel

lemma norm_epar_sub (e : E k × E k) (t s : ℝ) :
    ‖epar e t - epar e s‖ = |t - s| * ‖e.2 - e.1‖ := by
  rw [epar_sub, norm_smul, Real.norm_eq_abs]

lemma epar_zero (e : E k × E k) : epar e 0 = e.1 := by simp [epar]
lemma epar_one (e : E k × E k) : epar e 1 = e.2 := by simp [epar]

/-- open parameter interval of an edge -/
def eint (e : E k × E k) (α β : ℝ) : Set (E k) := {q | ∃ t, α < t ∧ t < β ∧ q = epar e t}

/-- points of the segment between two parameters -/
lemma epar_mem_segment (e : E k × E k) {s t r : ℝ} (h : r ∈ Set.uIcc s t) :
    epar e r ∈ segment ℝ (epar e s) (epar e t) := by
  have hpar : epar e = (AffineMap.lineMap e.1 e.2 : ℝ →ᵃ[ℝ] E k) := by
    funext t; simp [epar, AffineMap.lineMap_apply, add_comm]
  rw [hpar, ← image_segment, segment_eq_uIcc]
  exact ⟨r, h, rfl⟩

/-- the crossing condition for an open parameter interval of an edge -/
lemma eint_cross (G : MetricGraph k) (e : E k × E k) (he : e ∈ G.edges) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) :
    ∀ e' ∈ G.edges, ∀ a ∈ segment ℝ e'.1 e'.2, ∀ b ∈ segment ℝ e'.1 e'.2,
      a ∉ eint e α β → b ∈ eint e α β → ∃ q ∈ ({epar e α, epar e β} : Set (E k)), q ∈ segment ℝ a b := by
  intro e' he' a ha b hb haU hbU
  obtain ⟨tb, htb1, htb2, rfl⟩ := hbU
  have hne := G.fst_ne_snd e he
  -- b is not an endpoint of e, hence e' = e
  have hb_e : epar e tb ∈ segment ℝ e.1 e.2 := epar_mem ⟨by linarith, by linarith⟩
  have hee : e' = e := by
    by_contra hc
    have := G.meet e he e' he' (Ne.symm hc) ⟨hb_e, hb⟩
    rcases this.1 with h | h
    · rw [← epar_zero e] at h; have := epar_inj hne h; linarith
    · rw [← epar_one e] at h; have := epar_inj hne h; linarith
  subst hee
  obtain ⟨ta, hta, rfl⟩ := (mem_seg_iff e' a).1 ha
  have hta' : ta ≤ α ∨ β ≤ ta := by
    by_contra hc; push Not at hc
    exact haU ⟨ta, hc.1, hc.2, rfl⟩
  rcases hta' with h | h
  · refine ⟨epar e' α, by simp, epar_mem_segment e' ?_⟩
    rw [Set.mem_uIcc]; left; exact ⟨h, by linarith⟩
  · refine ⟨epar e' β, by simp, epar_mem_segment e' ?_⟩
    rw [Set.mem_uIcc]; right; exact ⟨by linarith, h⟩

lemma dist_epar (G : MetricGraph k) (e : E k × E k) (he : e ∈ G.edges) (a b : G.Pt) {t s : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hs : s ∈ Set.Icc (0:ℝ) 1) (ha : (a : E k) = epar e t)
    (hb : (b : E k) = epar e s) : G.dist a b = |t - s| * ‖e.2 - e.1‖ := by
  rw [dist_eq_norm_of_edge G a b e he (ha ▸ epar_mem ht) (hb ▸ epar_mem hs), ha, hb, norm_epar_sub]

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- Schummer–Vohra Lemma 1 (limited uncompromisingness), parametrized along an edge. -/
lemma lemma1 (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M) (p : Profile G n)
    (j : Fin n) (p' : G.Pt) (e : E k × E k) (he : e ∈ G.edges) (tx t' : ℝ)
    (htx : tx ∈ Set.Icc (0:ℝ) 1) (hs : tx + 3 * (t' - tx) ∈ Set.Icc (0:ℝ) 1)
    (hx : ((M p : G.Pt) : E k) = epar e tx) (hp' : (p' : E k) = epar e t') (hne : t' ≠ tx)
    (hgeo : G.dist (p j) p' + G.dist p' (M p) = G.dist (p j) (M p))
    (hfar : 3 * G.dist p' (M p) ≤ G.dist (p j) (M p)) :
    M (Function.update p j p') = M p := by
  set x := M p with hxdef
  set y := M (Function.update p j p') with hydef
  set L := ‖e.2 - e.1‖ with hL
  have hLpos : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 (G.fst_ne_snd e he).symm)
  set s := tx + 3 * (t' - tx) with hsdef
  have ht' : t' ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · rcases le_total tx t' with h | h
      · linarith [htx.1]
      · linarith [hs.1]
    · rcases le_total tx t' with h | h
      · linarith [hs.2]
      · linarith [htx.2]
  set δ := G.dist p' x with hδ
  have hδval : δ = |t' - tx| * L := dist_epar G e he p' x ht' htx hp' hx
  have hδpos : 0 < δ := by rw [hδval]; exact mul_pos (abs_pos.2 (sub_ne_zero.2 hne)) hLpos
  -- SP consequences
  have h1 : G.dist (p j) x ≤ G.dist (p j) y := by
    have := hSP p j p'; rwa [G.dist_comm x, G.dist_comm y] at this
  have h2 : G.dist p' y ≤ δ := by
    have := hSP (Function.update p j p') j (p j)
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self] at this
    rw [G.dist_comm y, G.dist_comm x] at this; exact this
  have htri := G.dist_triangle (p j) p' y
  have hdy : G.dist p' y = δ := by linarith
  have hdpy : G.dist (p j) y = G.dist (p j) x := by linarith
  -- the interval
  set α := min tx s
  set β := max tx s
  have hα : 0 ≤ α := le_min htx.1 hs.1
  have hβ : β ≤ 1 := max_le htx.2 hs.2
  have hcross := eint_cross G e he hα hβ
  have hp'U : (p' : E k) ∈ eint e α β := by
    refine ⟨t', ?_, ?_, hp'⟩
    · rcases lt_or_gt_of_ne hne with h | h
      · simp only [α, hsdef]; rw [min_lt_iff]; right; linarith
      · simp only [α, hsdef]; rw [min_lt_iff]; left; linarith
    · rcases lt_or_gt_of_ne hne with h | h
      · simp only [β, hsdef]; rw [lt_max_iff]; left; linarith
      · simp only [β, hsdef]; rw [lt_max_iff]; right; linarith
  have hαβ : ({epar e α, epar e β} : Set (E k)) = {epar e tx, epar e s} := by
    rcases le_total tx s with h | h
    · simp [α, β, min_eq_left h, max_eq_right h]
    · simp [α, β, min_eq_right h, max_eq_left h, Set.pair_comm]
  have hsI : s ∈ Set.Icc (0:ℝ) 1 := hs
  have hds : ∀ q : G.Pt, (q : E k) = epar e s → G.dist q p' = 2 * δ := by
    intro q hq
    rw [dist_epar G e he q p' hsI ht' hq hp', hδval, hsdef]
    rw [show tx + 3 * (t' - tx) - t' = 2 * (t' - tx) by ring, abs_mul]; norm_num; ring
  by_cases hyU : (y : E k) ∈ eint e α β
  · exfalso
    obtain ⟨ty, hty1, hty2, hy⟩ := hyU
    have htyI : ty ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hdy' := dist_epar G e he p' y ht' htyI hp' hy
    rw [hdy, hδval] at hdy'
    have habs : |t' - tx| = |t' - ty| := by
      have := mul_right_cancel₀ (ne_of_gt hLpos) hdy'; exact this
    -- ty = 2 t' - tx
    have hty : ty = 2 * t' - tx := by
      rcases abs_eq_abs.1 habs with h | h
      · exfalso
        have : ty = tx := by linarith
        rw [this] at hty1 hty2
        rcases le_total tx s with h' | h'
        · simp [α, min_eq_left h'] at hty1
        · simp [β, max_eq_left h'] at hty2
      · linarith
    -- p j is outside the interval
    have hpjU : ((p j : G.Pt) : E k) ∉ eint e α β := by
      rintro ⟨tj, htj1, htj2, hpj⟩
      have htjI : tj ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
      have := dist_epar G e he (p j) p' htjI ht' hpj hp'
      have hlt : |tj - t'| < 2 * |t' - tx| := by
        rcases lt_or_gt_of_ne hne with h | h
        · simp only [α, β, hsdef] at htj1 htj2
          rw [min_eq_right (by linarith), max_eq_left (by linarith)] at *
          rw [abs_lt, abs_of_neg (by linarith)]; constructor <;> linarith
        · simp only [α, β, hsdef] at htj1 htj2
          rw [min_eq_left (by linarith), max_eq_right (by linarith)] at *
          rw [abs_lt, abs_of_pos (by linarith)]; constructor <;> linarith
      have : G.dist (p j) p' < 2 * δ := by
        rw [this, hδval]; nlinarith
      linarith
    obtain ⟨q, hqB, hq⟩ := cross G (eint e α β) _ hcross (p j) p' hpjU hp'U
    rw [hαβ] at hqB
    rcases hqB with hq1 | hq1
    · -- q = x
      have : q = x := Subtype.ext (hq1.trans hx.symm)
      rw [this] at hq
      rw [G.dist_comm x p'] at hq
      linarith
    · have hqp := hds q hq1
      obtain ⟨q2, hqB2, hq2⟩ := cross G (eint e α β) _ hcross (p j) y hpjU ⟨ty, hty1, hty2, hy⟩
      have hdq2 : G.dist q y = δ := by
        rw [G.dist_comm] at hqp
        rw [dist_epar G e he q y hsI htyI hq1 hy, hty, hsdef, hδval]
        rw [show tx + 3 * (t' - tx) - (2 * t' - tx) = t' - tx by ring]
      have := G.dist_triangle (p j) q y
      have hX : G.dist (p j) q = G.dist (p j) x - 3 * δ := by linarith
      linarith
  · -- y outside: y = x
    obtain ⟨q, hqB, hq⟩ := cross G (eint e α β) _ hcross y p' hyU hp'U
    rw [hαβ] at hqB
    rcases hqB with hq1 | hq1
    · have : q = x := Subtype.ext (hq1.trans hx.symm)
      rw [this, G.dist_comm y p', hdy, G.dist_comm x p'] at hq
      have h0 : G.dist y x = 0 := by linarith
      exact eq_of_dist_eq_zero G y x h0
    · have := hds q hq1
      rw [G.dist_comm y p', hdy] at hq
      have := dist_nonneg G y q
      linarith

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- unanimity for SP onto mechanisms on graphs -/
lemma unanimity (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (s : G.Pt) : M (fun _ => s) = s := by
  classical
  obtain ⟨u, hu⟩ := hM s
  have key : ∀ C : Finset (Fin n), M (fun j => if j ∈ C then s else u j) = s := by
    intro C
    induction C using Finset.induction_on with
    | empty => simpa using hu
    | insert c C hc ih =>
      have e1 : (fun j => if j ∈ insert c C then s else u j) =
          Function.update (fun j => if j ∈ C then s else u j) c s := by
        funext j; by_cases h : j = c
        · subst h; simp
        · simp [Function.update_of_ne h, h]
      rw [e1]
      have h1 := hSP (Function.update (fun j => if j ∈ C then s else u j) c s) c (u c)
      have e2 : Function.update (Function.update (fun j => if j ∈ C then s else u j) c s) c (u c) =
          (fun j => if j ∈ C then s else u j) := by
        funext j; by_cases h : j = c
        · subst h; simp [hc]
        · simp [Function.update_of_ne h]
      rw [e2, ih] at h1
      simp only [Function.update_self, dist_self] at h1
      exact (eq_of_dist_eq_zero G _ _ (le_antisymm h1 (dist_nonneg G _ _))).symm ▸ rfl
  have := key Finset.univ
  simpa using this

/-- interval transitivity -/
lemma between_trans (G : MetricGraph k) {a z P x : G.Pt}
    (hz : G.dist a z + G.dist z x = G.dist a x) (hP : G.dist z P + G.dist P x = G.dist z x) :
    G.dist a P + G.dist P x = G.dist a x := by
  have h1 := G.dist_triangle a z P
  have h2 := G.dist_triangle a P x
  linarith

/-- points of a geodesic close to its endpoint `x`, along the last edge of a shortest walk -/
lemma near_geo (G : MetricGraph k) (a x : G.Pt) (hax : a ≠ x) :
    ∃ e ∈ G.edges, ∃ tx tw : ℝ, tx ∈ Set.Icc (0:ℝ) 1 ∧ tw ∈ Set.Icc (0:ℝ) 1 ∧ tw ≠ tx ∧
      (x : E k) = epar e tx ∧ ∀ (P : G.Pt) (t : ℝ), t ∈ Set.uIcc tx tw → (P : E k) = epar e t →
        G.dist a P + G.dist P x = G.dist a x := by
  classical
  obtain ⟨m, w, h0, hm, hw, hL⟩ := G.exists_walk_eq_dist a x
  have hex : ∃ l, l < m ∧ w l ≠ x := by
    refine ⟨0, ?_, ?_⟩
    · by_contra h; push Not at h
      have : m = 0 := by omega
      rw [this, h0] at hm; exact hax (Subtype.ext hm)
    · rw [h0]; intro h; exact hax (Subtype.ext h)
  -- the last index with w l ≠ x
  let S := (Finset.range m).filter (fun l => w l ≠ x)
  have hS : S.Nonempty := by
    obtain ⟨l, hl, hlx⟩ := hex; exact ⟨l, Finset.mem_filter.2 ⟨Finset.mem_range.2 hl, hlx⟩⟩
  set l := S.max' hS with hl
  have hlS := Finset.mem_filter.1 (S.max'_mem hS)
  have hlm : l < m := Finset.mem_range.1 hlS.1
  have hwl : w l ≠ x := hlS.2
  have hwl1 : w (l + 1) = x := by
    by_cases h : l + 1 = m
    · rw [h, hm]
    · by_contra hc
      have : l + 1 ≤ l := S.le_max' _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hc⟩)
      omega
  obtain ⟨e, he, hwe, hwe'⟩ := hw l hlm
  rw [hwl1] at hwe'
  obtain ⟨tw, htw, hwt⟩ := (mem_seg_iff e _).1 hwe
  obtain ⟨tx, htx, hxt⟩ := (mem_seg_iff e _).1 hwe'
  have hne : tw ≠ tx := by
    intro h; apply hwl; rw [hwt, hxt, h]
  refine ⟨e, he, tx, tw, htx, htw, hne, hxt, ?_⟩
  intro P t ht hP
  have htI : t ∈ Set.Icc (0:ℝ) 1 := by
    rcases Set.mem_uIcc.1 ht with h | h
    · exact ⟨by linarith [htx.1, h.1], by linarith [htw.2, h.2]⟩
    · exact ⟨by linarith [htw.1, h.1], by linarith [htx.2, h.2]⟩
  have hPe : (P : E k) ∈ segment ℝ e.1 e.2 := hP ▸ epar_mem htI
  apply le_antisymm _ (G.dist_triangle a P x)
  -- walk a → w l → P
  have h1 := G.dist_le_walk a P (l + 1) (fun j => if j ≤ l then w j else (P : E k))
    (by simp [h0]) (by simp) (by
      intro j hj
      by_cases hj' : j + 1 ≤ l
      · simpa [show j ≤ l by omega, hj'] using hw j (by omega)
      · have hjl : j = l := by omega
        rw [hjl]
        simp only [le_refl, if_true, show ¬ (l + 1 ≤ l) by omega, if_false]
        exact ⟨e, he, hwe, hPe⟩)
  have hsum1 : ∑ j ∈ Finset.range (l + 1),
      ‖(if j + 1 ≤ l then w (j + 1) else (P : E k)) - (if j ≤ l then w j else (P : E k))‖ =
      ∑ j ∈ Finset.range l, ‖w (j + 1) - w j‖ + ‖(P : E k) - w l‖ := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
      simp [show j + 1 ≤ l by omega, show j ≤ l by omega]
    · simp only [le_refl, if_true, show ¬ (l + 1 ≤ l) by omega, if_false]
  rw [hsum1] at h1
  have h2 := dist_le_norm_of_edge G P x e he hPe (by rw [hxt]; exact epar_mem htx)
  -- collinearity on the last step
  have hcol : ‖(P : E k) - w l‖ + ‖(P : E k) - (x : E k)‖ = ‖w (l + 1) - w l‖ := by
    rw [hwl1, hP, hwt, hxt, norm_epar_sub, norm_epar_sub, norm_epar_sub, ← add_mul]
    congr 1
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonpos (by linarith : t - tw ≤ 0), abs_of_nonneg (by linarith : 0 ≤ t - tx),
        abs_of_nonpos (by linarith : tx - tw ≤ 0)]; ring
    · rw [abs_of_nonneg (by linarith : 0 ≤ t - tw), abs_of_nonpos (by linarith : t - tx ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ tx - tw)]; ring
  have htot : ∑ j ∈ Finset.range m, ‖w (j + 1) - w j‖ ≥
      ∑ j ∈ Finset.range l, ‖w (j + 1) - w j‖ + ‖w (l + 1) - w l‖ := by
    have : ∑ j ∈ Finset.range (l + 1), ‖w (j + 1) - w j‖ ≤ ∑ j ∈ Finset.range m, ‖w (j + 1) - w j‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        (fun _ _ _ => norm_nonneg _)
    rw [Finset.sum_range_succ] at this; linarith
  rw [← hL]
  linarith

/-- coalition `C` reports `P` -/
def setP {G : MetricGraph k} (C : Finset (Fin n)) (p : Profile G n) (P : G.Pt) : Profile G n :=
  fun j => if j ∈ C then P else p j

lemma setP_empty {G : MetricGraph k} (p : Profile G n) (P : G.Pt) : setP ∅ p P = p := by
  funext j; simp [setP]

lemma setP_insert {G : MetricGraph k} (C : Finset (Fin n)) (c : Fin n) (p : Profile G n) (P : G.Pt) :
    setP (insert c C) p P = Function.update (setP C p P) c P := by
  classical
  funext j; by_cases h : j = c
  · subst h; simp [setP]
  · simp [setP, Function.update_of_ne h, h]

/-- Schummer–Vohra Lemma 2 (no intersecting shortest paths). -/
lemma lemma2 (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (p : Profile G n) (z : G.Pt) (hz : z ≠ M p)
    (hall : ∀ j, G.dist (p j) z + G.dist z (M p) = G.dist (p j) (M p)) : False := by
  classical
  set x := M p with hxdef
  obtain ⟨e, he, tx, tw, htx, htw, hne, hxt, hseg⟩ := near_geo G z x hz
  set L := ‖e.2 - e.1‖
  have hLpos : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 (G.fst_ne_snd e he).symm)
  have hdzx : 0 < G.dist z x := by
    rcases (dist_nonneg G z x).lt_or_eq with h | h
    · exact h
    · exact absurd (eq_of_dist_eq_zero G z x h.symm) hz
  set θ := min (1/3 : ℝ) (G.dist z x / (3 * (|tw - tx| * L) + 1)) with hθ
  have hθpos : 0 < θ := lt_min (by norm_num) (div_pos hdzx (by positivity))
  have hθ3 : θ ≤ 1/3 := min_le_left _ _
  have hθb : θ * (3 * (|tw - tx| * L) + 1) ≤ G.dist z x := by
    have := min_le_right (1/3 : ℝ) (G.dist z x / (3 * (|tw - tx| * L) + 1))
    rw [← hθ] at this
    calc θ * (3 * (|tw - tx| * L) + 1) ≤ G.dist z x / (3 * (|tw - tx| * L) + 1) *
          (3 * (|tw - tx| * L) + 1) := by gcongr
      _ = G.dist z x := by field_simp
  set t' := tx + θ * (tw - tx) with ht'
  have hmem : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → tx + c * (tw - tx) ∈ Set.uIcc tx tw := by
    intro c hc0 hc1
    rcases le_total tx tw with h | h
    · rw [Set.uIcc_of_le h]; constructor <;> nlinarith
    · rw [Set.uIcc_of_ge h]; constructor <;> nlinarith
  have huI : ∀ r ∈ Set.uIcc tx tw, r ∈ Set.Icc (0:ℝ) 1 := by
    intro r hr
    rcases Set.mem_uIcc.1 hr with h | h
    · exact ⟨by linarith [htx.1, h.1], by linarith [htw.2, h.2]⟩
    · exact ⟨by linarith [htw.1, h.1], by linarith [htx.2, h.2]⟩
  have ht'I : t' ∈ Set.Icc (0:ℝ) 1 := huI _ (hmem θ hθpos.le (by linarith))
  have hsI : tx + 3 * (t' - tx) ∈ Set.Icc (0:ℝ) 1 := by
    have : tx + 3 * (t' - tx) = tx + (3 * θ) * (tw - tx) := by rw [ht']; ring
    rw [this]; exact huI _ (hmem (3 * θ) (by linarith) (by linarith))
  let P : G.Pt := ⟨epar e t', Set.mem_biUnion he (epar_mem ht'I)⟩
  have hPne : t' ≠ tx := by
    intro h; rw [ht'] at h
    have : θ * (tw - tx) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact hne (by linarith)
  have hzP : G.dist z P + G.dist P x = G.dist z x := hseg P t' (hmem θ hθpos.le (by linarith)) rfl
  have hPx : G.dist P x = θ * (|tw - tx| * L) := by
    rw [dist_epar G e he P x ht'I htx rfl hxt, ht']
    rw [show tx + θ * (tw - tx) - tx = θ * (tw - tx) by ring, abs_mul, abs_of_pos hθpos]; ring
  have hfar : ∀ j, 3 * G.dist P x ≤ G.dist (p j) x := by
    intro j
    have h1 := hall j
    have h2 := dist_nonneg G (p j) z
    rw [hPx]; nlinarith [abs_nonneg (tw - tx)]
  have key : ∀ C : Finset (Fin n), M (setP C p P) = x := by
    intro C
    induction C using Finset.induction_on with
    | empty => rw [setP_empty]
    | insert c C hc ih =>
      rw [setP_insert]
      have hqc : setP C p P c = p c := by simp [setP, hc]
      have := lemma1 G M hSP (setP C p P) c P e he tx t' htx hsI (by rw [ih]; exact hxt) rfl hPne
        (by rw [hqc, ih]; exact between_trans G (hall c) hzP) (by rw [hqc, ih]; exact hfar c)
      rw [this, ih]
  have h := key Finset.univ
  have e1 : setP Finset.univ p P = fun _ => P := by funext j; simp [setP]
  rw [e1, unanimity G M hSP hM P] at h
  apply hPne
  have : (P : E k) = epar e tx := by rw [h]; exact hxt
  exact epar_inj (G.fst_ne_snd e he) this

/-- approximate efficiency: the outcome is within `n` times the diameter of some report -/
lemma approx_eff (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) (x : Profile G n) (D : ℝ)
    (hD : ∀ i j, G.dist (x i) (x j) ≤ D) : ∃ i, G.dist (x i) (M x) ≤ n * D := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let μ : Profile G n → ℝ := fun z => Finset.univ.inf' ⟨i0, Finset.mem_univ _⟩ (fun j => G.dist (z j) (M z))
  have hD0 : 0 ≤ D := (dist_nonneg G _ _).trans (hD i0 i0)
  have key : ∀ C : Finset (Fin n), μ x ≤ μ (setP C x (x i0)) + C.card * D := by
    intro C
    induction C using Finset.induction_on with
    | empty => rw [setP_empty]; simp
    | insert c C hc ih =>
      rw [setP_insert, Finset.card_insert_of_notMem hc]
      set z := setP C x (x i0)
      have hzc : z c = x c := by simp [z, setP, hc]
      have hsp := hSP z c (x i0)
      rw [hzc] at hsp
      have hstep : μ z ≤ μ (Function.update z c (x i0)) + D := by
        set z' := Function.update z c (x i0)
        have h1 : μ z ≤ G.dist (x c) (M z) := by
          have := Finset.inf'_le (fun j => G.dist (z j) (M z)) (Finset.mem_univ c)
          simpa [hzc] using this
        have h2 : G.dist (x c) (M z) ≤ G.dist (x c) (M z') := by
          rw [G.dist_comm (x c), G.dist_comm (x c)]; exact hsp
        have h3 : G.dist (x c) (M z') - D ≤ μ z' := by
          refine Finset.le_inf' _ _ (fun j _ => ?_)
          have hz'j : G.dist (x c) (z' j) ≤ D := by
            by_cases hj : j = c
            · rw [hj]; simp only [z', Function.update_self]; exact hD c i0
            · simp only [z', Function.update_of_ne hj, z, setP]
              split_ifs
              · exact hD c i0
              · exact hD c j
          have := G.dist_triangle (x c) (z' j) (M z')
          linarith
        linarith
      push_cast; linarith
  have h := key Finset.univ
  have e1 : setP Finset.univ x (x i0) = fun _ => x i0 := by funext j; simp [setP]
  rw [e1] at h
  have hμ0 : μ (fun _ => x i0) = 0 := by
    apply le_antisymm
    · refine (Finset.inf'_le _ (Finset.mem_univ i0)).trans ?_
      simp only [unanimity G M hSP hM (x i0), dist_self]; exact le_rfl
    · exact Finset.le_inf' _ _ (fun j _ => dist_nonneg G _ _)
  rw [hμ0, Finset.card_univ, Fintype.card_fin] at h
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' ⟨i0, Finset.mem_univ i0⟩ (fun j => G.dist (x j) (M x))
  refine ⟨i, ?_⟩
  have : μ x = G.dist (x i) (M x) := hi
  linarith

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- local efficiency on a short parameter interval of an edge -/
lemma local_eff (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) (e : E k × E k) (he : e ∈ G.edges)
    (t1 t2 η : ℝ) (h12 : t1 ≤ t2) (hη : (n + 1) * (t2 - t1) < η) (hη1 : η ≤ 1)
    (hleft : t1 = 0 ∨ 0 ≤ t1 - η) (hright : t2 = 1 ∨ t2 + η ≤ 1)
    (x : Profile G n) (τ : Fin n → ℝ) (hτ : ∀ j, τ j ∈ Set.Icc t1 t2)
    (hx : ∀ j, ((x j : G.Pt) : E k) = epar e (τ j)) :
    ∃ τm, Finset.univ.inf' (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) τ ≤ τm ∧
      τm ≤ Finset.univ.sup' (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) τ ∧
      ((M x : G.Pt) : E k) = epar e τm := by
  classical
  have hne : Finset.univ.Nonempty := Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩
  set L := ‖e.2 - e.1‖
  have hLpos : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 (G.fst_ne_snd e he).symm)
  have hηpos : 0 < η := by
    have : (0:ℝ) ≤ n + 1 := by positivity
    have : 0 ≤ ((n:ℝ) + 1) * (t2 - t1) := mul_nonneg this (by linarith)
    linarith
  have ht1 : 0 ≤ t1 := by rcases hleft with h | h <;> linarith
  have ht2 : t2 ≤ 1 := by rcases hright with h | h <;> linarith
  have hτI : ∀ j, τ j ∈ Set.Icc (0:ℝ) 1 := fun j => ⟨ht1.trans (hτ j).1, (hτ j).2.trans ht2⟩
  have hlen : t2 - t1 < 1 := by
    have : (1:ℝ) ≤ n + 1 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    nlinarith
  set m := M x with hmdef
  set D := (t2 - t1) * L
  have hD : ∀ i j, G.dist (x i) (x j) ≤ D := by
    intro i j
    rw [dist_epar G e he _ _ (hτI i) (hτI j) (hx i) (hx j)]
    apply mul_le_mul_of_nonneg_right _ hLpos.le
    rw [abs_le]; constructor <;> linarith [(hτ i).1, (hτ i).2, (hτ j).1, (hτ j).2]
  obtain ⟨i0, hi0⟩ := approx_eff G M hSP hM hn x D hD
  have hdm : ∀ j, G.dist m (x j) ≤ (n + 1) * D := by
    intro j
    have := G.dist_triangle m (x i0) (x j)
    rw [G.dist_comm m (x i0)] at this
    have := hD i0 j
    nlinarith
  set τmin := Finset.univ.inf' hne τ
  set τmax := Finset.univ.sup' hne τ
  obtain ⟨jmin, -, hjmin⟩ := Finset.exists_mem_eq_inf' hne τ
  obtain ⟨jmax, -, hjmax⟩ := Finset.exists_mem_eq_sup' hne τ
  have hmin_le : ∀ j, τmin ≤ τ j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hle_max : ∀ j, τ j ≤ τmax := fun j => Finset.le_sup' _ (Finset.mem_univ j)
  -- hull argument for outcomes on the edge
  have hull : ∀ τm, τm ∈ Set.Icc (0:ℝ) 1 → (m : E k) = epar e τm → τmin ≤ τm ∧ τm ≤ τmax := by
    intro τm hτm hm
    constructor
    · by_contra hc; push Not at hc
      apply lemma2 G M hSP hM x (x jmin)
      · intro h; rw [← hmdef] at h
        have : τ jmin = τm := epar_inj (G.fst_ne_snd e he) ((hx jmin).symm.trans (congrArg Subtype.val h ▸ hm))
        have h' : τmin = τ jmin := hjmin; linarith
      · intro j
        rw [← hmdef, dist_epar G e he _ _ (hτI j) (hτI jmin) (hx j) (hx jmin),
          dist_epar G e he _ _ (hτI jmin) hτm (hx jmin) hm,
          dist_epar G e he _ _ (hτI j) hτm (hx j) hm, ← add_mul]
        congr 1
        have h' : τ jmin = τmin := hjmin.symm
        rw [h', abs_of_nonneg (by linarith [hmin_le j] : 0 ≤ τ j - τmin),
          abs_of_pos (by linarith : 0 < τmin - τm), abs_of_pos (by linarith [hmin_le j] : 0 < τ j - τm)]
        ring
    · by_contra hc; push Not at hc
      apply lemma2 G M hSP hM x (x jmax)
      · intro h; rw [← hmdef] at h
        have : τ jmax = τm := epar_inj (G.fst_ne_snd e he) ((hx jmax).symm.trans (congrArg Subtype.val h ▸ hm))
        have h' : τmax = τ jmax := hjmax; linarith
      · intro j
        rw [← hmdef, dist_epar G e he _ _ (hτI j) (hτI jmax) (hx j) (hx jmax),
          dist_epar G e he _ _ (hτI jmax) hτm (hx jmax) hm,
          dist_epar G e he _ _ (hτI j) hτm (hx j) hm, ← add_mul]
        congr 1
        have h' : τ jmax = τmax := hjmax.symm
        rw [h', abs_of_nonpos (by linarith [hle_max j] : τ j - τmax ≤ 0),
          abs_of_neg (by linarith : τmax - τm < 0), abs_of_neg (by linarith [hle_max j] : τ j - τm < 0)]
        ring
  -- the open interval around J
  set α := if t1 = 0 then 0 else t1 - η
  set β := if t2 = 1 then 1 else t2 + η
  have hα : 0 ≤ α := by simp only [α]; split_ifs with h; exact le_rfl; rcases hleft with h' | h'; exact absurd h' h; exact h'
  have hβ : β ≤ 1 := by simp only [β]; split_ifs with h; exact le_rfl; rcases hright with h' | h'; exact absurd h' h; exact h'
  have hαt : α ≤ t1 := by simp only [α]; split_ifs with h <;> linarith
  have htβ : t2 ≤ β := by simp only [β]; split_ifs with h <;> linarith
  by_cases hmU : (m : E k) ∈ eint e α β
  · obtain ⟨τm, h1, h2, hm⟩ := hmU
    have hτmI : τm ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    exact ⟨τm, (hull τm hτmI hm).1, (hull τm hτmI hm).2, hm⟩
  · -- every agent reaches `m` through a boundary point
    have hcr := eint_cross G e he hα hβ
    -- distance bound to far boundary points
    have hfarα : t1 ≠ 0 → ∀ j, ∀ q : G.Pt, (q : E k) = epar e α → (n + 1) * D < G.dist q (x j) := by
      intro h1 j q hq
      have hαv : α = t1 - η := by simp [α, h1]
      have hαI : α ∈ Set.Icc (0:ℝ) 1 := ⟨hα, by linarith⟩
      rw [dist_epar G e he q (x j) hαI (hτI j) hq (hx j), hαv]
      rw [abs_of_neg (by linarith [(hτ j).1] : t1 - η - τ j < 0)]
      have : η ≤ -(t1 - η - τ j) := by linarith [(hτ j).1]
      calc (n + 1) * D = ((n + 1) * (t2 - t1)) * L := by ring
        _ < η * L := by gcongr
        _ ≤ _ := by gcongr
    have hfarβ : t2 ≠ 1 → ∀ j, ∀ q : G.Pt, (q : E k) = epar e β → (n + 1) * D < G.dist q (x j) := by
      intro h1 j q hq
      have hβv : β = t2 + η := by simp [β, h1]
      have hβI : β ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hβ⟩
      rw [dist_epar G e he q (x j) hβI (hτI j) hq (hx j), hβv]
      rw [abs_of_pos (by linarith [(hτ j).2] : 0 < t2 + η - τ j)]
      have : η ≤ t2 + η - τ j := by linarith [(hτ j).2]
      calc (n + 1) * D = ((n + 1) * (t2 - t1)) * L := by ring
        _ < η * L := by gcongr
        _ ≤ _ := by gcongr
    -- reduce to the vertex cases
    have hvertex : ∀ v : G.Pt, (∀ j, G.dist (x j) v + G.dist v m = G.dist (x j) m) →
        (∃ tv, tv ∈ Set.Icc (0:ℝ) 1 ∧ (v : E k) = epar e tv) →
        ∃ τm, τmin ≤ τm ∧ τm ≤ τmax ∧ (m : E k) = epar e τm := by
      intro v hv ⟨tv, htv, hve⟩
      by_cases hvm : v = m
      · rw [← hvm]; exact ⟨tv, (hull tv htv (hvm ▸ hve)).1, (hull tv htv (hvm ▸ hve)).2, hve⟩
      · exact absurd (lemma2 G M hSP hM x v hvm hv) id
    have hv1 : ∀ j, ∀ q : G.Pt, ((q : E k) = epar e α ∨ (q : E k) = epar e β) →
        G.dist m (x j) = G.dist m q + G.dist q (x j) →
        ((t1 = 0 ∧ (q : E k) = epar e 0) ∨ (t2 = 1 ∧ (q : E k) = epar e 1)) := by
      intro j q hq hd
      have hle : G.dist q (x j) ≤ (n + 1) * D := by
        have := dist_nonneg G m q; have := hdm j; linarith
      rcases hq with hq | hq
      · by_cases h1 : t1 = 0
        · left; refine ⟨h1, ?_⟩; rw [hq]; simp [α, h1]
        · exact absurd (hfarα h1 j q hq) (not_lt.2 hle)
      · by_cases h1 : t2 = 1
        · right; refine ⟨h1, ?_⟩; rw [hq]; simp [β, h1]
        · exact absurd (hfarβ h1 j q hq) (not_lt.2 hle)
    have hxU : ∀ j, τ j ≠ 0 → τ j ≠ 1 → ((x j : G.Pt) : E k) ∈ eint e α β := by
      intro j h0 h1
      refine ⟨τ j, ?_, ?_, hx j⟩
      · simp only [α]; split_ifs with h
        · exact lt_of_le_of_ne (hτI j).1 (Ne.symm h0)
        · linarith [(hτ j).1]
      · simp only [β]; split_ifs with h
        · exact lt_of_le_of_ne (hτI j).2 h1
        · linarith [(hτ j).2]
    rcases hleft with hl | hl
    · -- left end is the vertex `e.1`
      have ht2' : t2 ≠ 1 := by intro h; rw [hl, h] at hlen; linarith
      let v : G.Pt := ⟨epar e 0, Set.mem_biUnion he (epar_mem ⟨le_rfl, zero_le_one⟩)⟩
      refine hvertex v ?_ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      intro j
      by_cases h0 : τ j = 0
      · have : x j = v := Subtype.ext (by rw [hx j, h0])
        rw [this, dist_self, zero_add]
      · have h1 : τ j ≠ 1 := by intro h; have := (hτ j).2; rw [h] at this; exact ht2' (le_antisymm ht2 this)
        obtain ⟨q, hq, hd⟩ := cross G (eint e α β) _ hcr m (x j) hmU (hxU j h0 h1)
        rcases hv1 j q hq hd with ⟨-, hq0⟩ | ⟨h, -⟩
        · have : q = v := Subtype.ext hq0
          rw [this] at hd
          rw [G.dist_comm (x j) v, G.dist_comm v m, G.dist_comm (x j) m, hd]; ring
        · exact absurd h ht2'
    · rcases hright with hr | hr
      · -- right end is the vertex `e.2`
        let v : G.Pt := ⟨epar e 1, Set.mem_biUnion he (epar_mem ⟨zero_le_one, le_rfl⟩)⟩
        have ht1' : t1 ≠ 0 := by intro h; rw [hr, h] at hlen; linarith
        refine hvertex v ?_ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
        intro j
        by_cases h1 : τ j = 1
        · have : x j = v := Subtype.ext (by rw [hx j, h1])
          rw [this, dist_self, zero_add]
        · have h0 : τ j ≠ 0 := by
            intro h; have := (hτ j).1; rw [h] at this
            exact ht1' (le_antisymm this ht1)
          obtain ⟨q, hq, hd⟩ := cross G (eint e α β) _ hcr m (x j) hmU (hxU j h0 h1)
          rcases hv1 j q hq hd with ⟨h, -⟩ | ⟨-, hq1⟩
          · exact absurd h ht1'
          · have : q = v := Subtype.ext hq1
            rw [this] at hd
            rw [G.dist_comm (x j) v, G.dist_comm v m, G.dist_comm (x j) m, hd]; ring
      · -- both margins: impossible
        exfalso
        have ht1' : t1 ≠ 0 := by intro h; rw [h] at hl; linarith
        have ht2' : t2 ≠ 1 := by intro h; rw [h] at hr; linarith
        let j0 : Fin n := ⟨0, hn⟩
        have h0 : τ j0 ≠ 0 := by intro h; have := (hτ j0).1; rw [h] at this; exact ht1' (le_antisymm this ht1)
        have h1 : τ j0 ≠ 1 := by intro h; have := (hτ j0).2; rw [h] at this; exact ht2' (le_antisymm ht2 this)
        obtain ⟨q, hq, hd⟩ := cross G (eint e α β) _ hcr m (x j0) hmU (hxU j0 h0 h1)
        rcases hv1 j0 q hq hd with ⟨h, -⟩ | ⟨h, -⟩
        · exact ht1' h
        · exact ht2' h

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- parameter of a point on the line of an edge -/
noncomputable def epara (e : E k × E k) (q : E k) : ℝ :=
  inner ℝ (q - e.1) (e.2 - e.1) / ‖e.2 - e.1‖ ^ 2

lemma epara_epar (e : E k × E k) (he : e.1 ≠ e.2) (t : ℝ) : epara e (epar e t) = t := by
  have hd : ‖e.2 - e.1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 he.symm)
  simp only [epara, epar, add_sub_cancel_left, inner_smul_left, real_inner_self_eq_norm_sq]
  simp
  field_simp

lemma seg_gmvs (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) (e : E k × E k) (he : e ∈ G.edges)
    (t1 t2 η : ℝ) (h12 : t1 ≤ t2) (hη : (n + 1) * (t2 - t1) < η) (hη1 : η ≤ 1)
    (hleft : t1 = 0 ∨ 0 ≤ t1 - η) (hright : t2 = 1 ∨ t2 + η ≤ 1) :
    ∃ T : Finset (Fin n) → ℝ, (∀ S, T S ∈ Set.Icc t1 t2) ∧
      ∀ (x : Profile G n) (τ : Fin n → ℝ), (∀ j, τ j ∈ Set.Icc t1 t2) →
        (∀ j, ((x j : G.Pt) : E k) = epar e (τ j)) →
        (∃ j, M x = x j) ∨ ∃ S, ((M x : G.Pt) : E k) = epar e (T S) := by
  classical
  have hne := G.fst_ne_snd e he
  have hηpos : 0 < η := by
    have : (0:ℝ) ≤ n + 1 := by positivity
    have : 0 ≤ ((n:ℝ) + 1) * (t2 - t1) := mul_nonneg this (by linarith)
    linarith
  have ht1 : 0 ≤ t1 := by rcases hleft with h | h <;> linarith
  have ht2 : t2 ≤ 1 := by rcases hright with h | h <;> linarith
  set L := ‖e.2 - e.1‖
  have hLpos : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  let cl : ℝ → ℝ := fun s => max t1 (min s t2)
  have hcl : ∀ s, cl s ∈ Set.Icc t1 t2 := fun s => ⟨le_max_left _ _, max_le h12 (min_le_right _ _)⟩
  have hclI : ∀ s, cl s ∈ Set.Icc (0:ℝ) 1 := fun s => ⟨ht1.trans (hcl s).1, (hcl s).2.trans ht2⟩
  have hcl_id : ∀ s ∈ Set.Icc t1 t2, cl s = s := fun s hs => by
    simp only [cl]; rw [min_eq_left hs.2, max_eq_right hs.1]
  let pt : ℝ → G.Pt := fun s => ⟨epar e (cl s), Set.mem_biUnion he (epar_mem (hclI s))⟩
  let F : (Fin n → ℝ) → ℝ := fun u => epara e ((M (fun j => pt (u j)) : G.Pt) : E k)
  -- outcomes of interval profiles lie in the interval
  have hloc : ∀ u : Fin n → ℝ, ∃ τm ∈ Set.Icc t1 t2,
      ((M (fun j => pt (u j)) : G.Pt) : E k) = epar e τm := by
    intro u
    obtain ⟨τm, h1, h2, hm⟩ := local_eff G M hSP hM hn e he t1 t2 η h12 hη hη1 hleft hright
      (fun j => pt (u j)) (fun j => cl (u j)) (fun j => hcl _) (fun j => rfl)
    refine ⟨τm, ⟨?_, ?_⟩, hm⟩
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩)
        (fun j => cl (u j))
      rw [hj] at h1; exact (hcl _).1.trans h1
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩)
        (fun j => cl (u j))
      rw [hj] at h2; exact h2.trans (hcl _).2
  have hFpt : ∀ u, ((M (fun j => pt (u j)) : G.Pt) : E k) = epar e (F u) := by
    intro u
    obtain ⟨τm, -, hm⟩ := hloc u
    simp only [F]; rw [hm, epara_epar e hne]
  have hFI : ∀ u, F u ∈ Set.Icc t1 t2 := by
    intro u
    obtain ⟨τm, hτm, hm⟩ := hloc u
    simp only [F]; rw [hm, epara_epar e hne]; exact hτm
  have hH : SPFGSeg.Hyp t1 t2 F := by
    refine ⟨h12, ?_, fun u _ => hFI u, ?_⟩
    · intro u hu i v hv
      have h := hSP (fun j => pt (u j)) i (pt v)
      have e1 : Function.update (fun j => pt (u j)) i (pt v) = fun j => pt (Function.update u i v j) := by
        funext j; by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      rw [e1] at h
      have hFI1 := hFI u
      have hFI2 := hFI (Function.update u i v)
      have hI1 : F u ∈ Set.Icc (0:ℝ) 1 := ⟨ht1.trans hFI1.1, hFI1.2.trans ht2⟩
      have hI2 : F (Function.update u i v) ∈ Set.Icc (0:ℝ) 1 := ⟨ht1.trans hFI2.1, hFI2.2.trans ht2⟩
      rw [dist_epar G e he _ _ hI1 (hclI (u i)) (hFpt u) rfl,
        dist_epar G e he _ _ hI2 (hclI (u i)) (hFpt _) rfl, hcl_id _ (hu i)] at h
      exact le_of_mul_le_mul_right h hLpos
    · intro s hs
      refine ⟨fun _ => s, fun _ => hs, ?_⟩
      simp only [F]
      rw [unanimity G M hSP hM (pt s)]
      simp only [pt]; rw [epara_epar e hne, hcl_id s hs]
  refine ⟨SPFGSeg.thr F t1 t2, fun S => hH.range _ (SPFGSeg.InA.ext hH.hab S), ?_⟩
  intro x τ hτ hx
  have hxpt : (fun j => pt (τ j)) = x := by
    funext j; apply Subtype.ext; simp only [pt]; rw [hcl_id _ (hτ j), hx j]
  have hg := SPFGSeg.gmvs hH (u := τ) hτ
  obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
      (insert (SPFGSeg.thr F t1 t2 S) (S.image τ)).min' (Finset.insert_nonempty _ _))
  rw [hS] at hg
  have hmem := Finset.min'_mem (insert (SPFGSeg.thr F t1 t2 S) (S.image τ)) (Finset.insert_nonempty _ _)
  rw [← hg] at hmem
  have hMx : ((M x : G.Pt) : E k) = epar e (F τ) := by rw [← hxpt]; exact hFpt τ
  rcases Finset.mem_insert.1 hmem with h | h
  · right; exact ⟨S, by rw [hMx, h]⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
    left; refine ⟨j, Subtype.ext ?_⟩
    rw [hMx, ← hj, hx j]

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

def setF {G : MetricGraph k} (C : Finset (Fin n)) (p : Profile G n) (P : Fin n → G.Pt) : Profile G n :=
  fun j => if j ∈ C then P j else p j

lemma setF_empty {G : MetricGraph k} (p : Profile G n) (P : Fin n → G.Pt) : setF ∅ p P = p := by
  funext j; simp [setF]

lemma setF_insert {G : MetricGraph k} (C : Finset (Fin n)) (c : Fin n) (p : Profile G n)
    (P : Fin n → G.Pt) : setF (insert c C) p P = Function.update (setF C p P) c (P c) := by
  classical
  funext j; by_cases h : j = c
  · subst h; simp [setF]
  · simp [setF, Function.update_of_ne h, h]

/-- an interior point of an edge lies on no other edge -/
lemma edge_unique (G : MetricGraph k) (e : E k × E k) (he : e ∈ G.edges) (τ : ℝ)
    (hτ : τ ∈ Set.Ioo (0:ℝ) 1) (e' : E k × E k) (he' : e' ∈ G.edges)
    (hm : epar e τ ∈ segment ℝ e'.1 e'.2) : e' = e := by
  by_contra hc
  have hne := G.fst_ne_snd e he
  have := G.meet e he e' he' (Ne.symm hc) ⟨epar_mem ⟨hτ.1.le, hτ.2.le⟩, hm⟩
  rcases this.1 with h | h
  · rw [← epar_zero e] at h; have := epar_inj hne h; linarith [hτ.1]
  · rw [← epar_one e] at h; have := epar_inj hne h; linarith [hτ.2]

/-- moving all agents next to an interior outcome keeps the outcome -/
lemma move_near (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (x : Profile G n) (e : E k × E k) (he : e ∈ G.edges) (τ : ℝ)
    (hτ : τ ∈ Set.Ioo (0:ℝ) 1) (hm : ((M x : G.Pt) : E k) = epar e τ) (hxm : ∀ i, x i ≠ M x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (x' : Profile G n) (τ' : Fin n → ℝ), (∀ i, τ' i ∈ Set.Icc (τ - ε) (τ + ε)) ∧
      (∀ i, ((x' i : G.Pt) : E k) = epar e (τ' i)) ∧ (∀ i, τ' i ≠ τ) ∧ M x' = M x := by
  classical
  set m := M x with hmdef
  have hne := G.fst_ne_snd e he
  set L := ‖e.2 - e.1‖
  have hLpos : 0 < L := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have hτI : τ ∈ Set.Icc (0:ℝ) 1 := ⟨hτ.1.le, hτ.2.le⟩
  have hdata : ∀ i, ∃ tw : ℝ, tw ∈ Set.Icc (0:ℝ) 1 ∧ tw ≠ τ ∧ ∀ (P : G.Pt) (t : ℝ),
      t ∈ Set.uIcc τ tw → (P : E k) = epar e t → G.dist (x i) P + G.dist P m = G.dist (x i) m := by
    intro i
    obtain ⟨e', he', tx, tw, htx, htw, hne', hxt, hseg⟩ := near_geo G (x i) m (hxm i)
    have hee : e' = e := edge_unique G e he τ hτ e' he' (by rw [← hm, hxt]; exact epar_mem htx)
    subst hee
    have : tx = τ := epar_inj hne (hxt.symm.trans hm)
    subst this
    exact ⟨tw, htw, hne', hseg⟩
  choose tw htw htwne hseg using hdata
  have hdpos : ∀ i, 0 < G.dist (x i) m := by
    intro i
    rcases (dist_nonneg G (x i) m).lt_or_eq with h | h
    · exact h
    · exact absurd (eq_of_dist_eq_zero G _ _ h.symm) (hxm i)
  let θ : Fin n → ℝ := fun i => min (1/3) (min (ε / (|tw i - τ| + 1))
    (G.dist (x i) m / (3 * (|tw i - τ| * L) + 1)))
  have hθpos : ∀ i, 0 < θ i := fun i =>
    lt_min (by norm_num) (lt_min (div_pos hε (by positivity)) (div_pos (hdpos i) (by positivity)))
  have hθ3 : ∀ i, θ i ≤ 1/3 := fun i => min_le_left _ _
  have hθε : ∀ i, θ i * |tw i - τ| ≤ ε := by
    intro i
    have h1 : θ i ≤ ε / (|tw i - τ| + 1) := (min_le_right _ _).trans (min_le_left _ _)
    calc θ i * |tw i - τ| ≤ ε / (|tw i - τ| + 1) * |tw i - τ| := by gcongr
      _ ≤ ε / (|tw i - τ| + 1) * (|tw i - τ| + 1) := by gcongr; linarith
      _ = ε := by field_simp
  have hθd : ∀ i, 3 * (θ i * (|tw i - τ| * L)) ≤ G.dist (x i) m := by
    intro i
    have h1 : θ i ≤ G.dist (x i) m / (3 * (|tw i - τ| * L) + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc 3 * (θ i * (|tw i - τ| * L)) = θ i * (3 * (|tw i - τ| * L)) := by ring
      _ ≤ θ i * (3 * (|tw i - τ| * L) + 1) := by have := hθpos i; nlinarith
      _ ≤ G.dist (x i) m / (3 * (|tw i - τ| * L) + 1) * (3 * (|tw i - τ| * L) + 1) := by gcongr
      _ = G.dist (x i) m := by field_simp
  have hmem : ∀ i, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → τ + c * (tw i - τ) ∈ Set.uIcc τ (tw i) := by
    intro i c hc0 hc1
    rcases le_total τ (tw i) with h | h
    · rw [Set.uIcc_of_le h]; constructor <;> nlinarith
    · rw [Set.uIcc_of_ge h]; constructor <;> nlinarith
  have huI : ∀ i, ∀ r ∈ Set.uIcc τ (tw i), r ∈ Set.Icc (0:ℝ) 1 := by
    intro i r hr
    rcases Set.mem_uIcc.1 hr with h | h
    · exact ⟨by linarith [hτI.1, h.1], by linarith [(htw i).2, h.2]⟩
    · exact ⟨by linarith [(htw i).1, h.1], by linarith [hτI.2, h.2]⟩
  let τ' : Fin n → ℝ := fun i => τ + θ i * (tw i - τ)
  have hτ'I : ∀ i, τ' i ∈ Set.Icc (0:ℝ) 1 := fun i => huI i _ (hmem i _ (hθpos i).le (by linarith [hθ3 i]))
  let P : Fin n → G.Pt := fun i => ⟨epar e (τ' i), Set.mem_biUnion he (epar_mem (hτ'I i))⟩
  have hτ'ne : ∀ i, τ' i ≠ τ := by
    intro i h
    have : θ i * (tw i - τ) = 0 := by simp only [τ'] at h; linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith [hθpos i]
    · exact htwne i (by linarith)
  have hPm : ∀ i, G.dist (P i) m = θ i * (|tw i - τ| * L) := by
    intro i
    rw [dist_epar G e he (P i) m (hτ'I i) hτI rfl hm]
    simp only [τ']
    rw [show τ + θ i * (tw i - τ) - τ = θ i * (tw i - τ) by ring, abs_mul, abs_of_pos (hθpos i)]; ring
  have key : ∀ C : Finset (Fin n), M (setF C x P) = m := by
    intro C
    induction C using Finset.induction_on with
    | empty => rw [setF_empty]
    | insert c C hc ih =>
      rw [setF_insert]
      have hqc : setF C x P c = x c := by simp [setF, hc]
      have hs : τ + 3 * (τ' c - τ) ∈ Set.Icc (0:ℝ) 1 := by
        have : τ + 3 * (τ' c - τ) = τ + (3 * θ c) * (tw c - τ) := by simp only [τ']; ring
        rw [this]; exact huI c _ (hmem c _ (by linarith [hθpos c]) (by linarith [hθ3 c]))
      have := lemma1 G M hSP (setF C x P) c (P c) e he τ (τ' c) hτI hs (by rw [ih]; exact hm) rfl
        (hτ'ne c)
        (by rw [hqc, ih]; exact hseg c (P c) (τ' c) (hmem c _ (hθpos c).le (by linarith [hθ3 c])) rfl)
        (by rw [hqc, ih, hPm]; exact hθd c)
      rw [this, ih]
  refine ⟨P, τ', ?_, fun i => rfl, hτ'ne, ?_⟩
  · intro i
    have := hθε i
    have h2 : |τ' i - τ| ≤ ε := by
      simp only [τ']; rw [show τ + θ i * (tw i - τ) - τ = θ i * (tw i - τ) by ring, abs_mul,
        abs_of_pos (hθpos i)]; exact this
    rw [abs_le] at h2
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · have := key Finset.univ
    have e1 : setF Finset.univ x P = P := by funext j; simp [setF]
    rwa [e1] at this

end SPFGGeo



namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

theorem finite_values (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ W : Finset G.Pt, ∀ x : Profile G n, (∃ i, M x = x i) ∨ M x ∈ W := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  set h : ℝ := 1 / (4 * (n + 2)) with hh
  have hpos : 0 < h := by positivity
  set h' : ℝ := h / (2 * (2 * n + 5)) with hh'
  have hpos' : 0 < h' := by positivity
  have hnh : ((n:ℝ) + 2) * h = 1 / 4 := by rw [hh]; field_simp
  have hh'2 : (2 * (n:ℝ) + 5) * h' = h / 2 := by rw [hh']; field_simp
  set N : ℕ := Nat.floor ((1 - h) / (h' / 2)) + 1 with hN
  let c : ℕ → ℝ := fun i => h / 2 + i * (h' / 2)
  let t1 : ℕ → ℝ := fun j => if j = 0 then 0 else if j = 1 then 1 - h else c (j - 2) - h'
  let t2 : ℕ → ℝ := fun j => if j = 0 then h else if j = 1 then 1 else c (j - 2) + h'
  let η : ℕ → ℝ := fun j => if j = 0 then (n + 2) * h else if j = 1 then (n + 2) * h
    else 2 * (n + 2) * h'
  have hcN : ∀ i < N, c i ≤ 1 - h / 2 := by
    intro i hi
    have hi' : (i : ℝ) ≤ (1 - h) / (h' / 2) := by
      have : i ≤ Nat.floor ((1 - h) / (h' / 2)) := by omega
      have h0 : 0 ≤ (1 - h) / (h' / 2) := by
        apply div_nonneg _ (by positivity)
        have : h ≤ 1 / 4 := by nlinarith
        linarith
      exact (Nat.cast_le.2 this).trans (Nat.floor_le h0)
    simp only [c]
    have := mul_le_mul_of_nonneg_right hi' (show (0:ℝ) ≤ h' / 2 by positivity)
    rw [div_mul_cancel₀ _ (by positivity)] at this
    linarith
  have hcond : ∀ j < N + 2, t1 j ≤ t2 j ∧ (n + 1) * (t2 j - t1 j) < η j ∧ η j ≤ 1 ∧
      (t1 j = 0 ∨ 0 ≤ t1 j - η j) ∧ (t2 j = 1 ∨ t2 j + η j ≤ 1) := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · have e1 : t1 0 = 0 := by simp [t1]
        have e2 : t2 0 = h := by simp [t2]
        have e3 : η 0 = (n + 2) * h := by simp [η]
        rw [e1, e2, e3]
        exact ⟨hpos.le, by nlinarith, by linarith, Or.inl rfl, Or.inr (by nlinarith)⟩
      · have e1 : t1 1 = 1 - h := by simp [t1]
        have e2 : t2 1 = 1 := by simp [t2]
        have e3 : η 1 = (n + 2) * h := by simp [η]
        rw [e1, e2, e3]
        exact ⟨by linarith, by nlinarith, by linarith, Or.inr (by nlinarith), Or.inl rfl⟩
    · have hj0 : j ≠ 0 := by omega
      have hj1 : j ≠ 1 := by omega
      have hci := hcN (j - 2) (by omega)
      have hci0 : h / 2 ≤ c (j - 2) := by
        simp only [c]
        have : (0:ℝ) ≤ (j - 2 : ℕ) * (h' / 2) := by positivity
        linarith
      have e1 : t1 j = c (j - 2) - h' := by simp [t1, hj0, hj1]
      have e2 : t2 j = c (j - 2) + h' := by simp [t2, hj0, hj1]
      have e3 : η j = 2 * (n + 2) * h' := by simp [η, hj0, hj1]
      rw [e1, e2, e3]
      have hh'h : h' ≤ h := by rw [hh']; apply div_le_self hpos.le; nlinarith
      refine ⟨by linarith, by nlinarith, by nlinarith, Or.inr (by nlinarith), Or.inr (by nlinarith)⟩
  have hcover : ∀ τ ∈ Set.Ioo (0:ℝ) 1, ∃ j < N + 2, ∃ ε > 0, Set.Icc (τ - ε) (τ + ε) ⊆ Set.Icc (t1 j) (t2 j) := by
    intro τ hτ
    by_cases h1 : τ ≤ h / 2
    · refine ⟨0, by omega, τ / 2, by linarith [hτ.1], ?_⟩
      intro y hy; simp only [t1, t2, if_true]; exact ⟨by linarith [hy.1, hτ.1], by linarith [hy.2]⟩
    · by_cases h2 : 1 - h / 2 ≤ τ
      · refine ⟨1, by omega, (1 - τ) / 2, by linarith [hτ.2], ?_⟩
        intro y hy; simp only [t1, t2, if_true, one_ne_zero, if_false]
        exact ⟨by linarith [hy.1], by linarith [hy.2, hτ.2]⟩
      · push Not at h1 h2
        set i := Nat.floor ((τ - h / 2) / (h' / 2)) with hi
        have h0 : 0 ≤ (τ - h / 2) / (h' / 2) := div_nonneg (by linarith) (by positivity)
        have hi1 : (i : ℝ) ≤ (τ - h / 2) / (h' / 2) := Nat.floor_le h0
        have hi2 : (τ - h / 2) / (h' / 2) < i + 1 := Nat.lt_floor_add_one _
        have hci1 : c i ≤ τ := by
          simp only [c]
          have := mul_le_mul_of_nonneg_right hi1 (show (0:ℝ) ≤ h' / 2 by positivity)
          rw [div_mul_cancel₀ _ (by positivity)] at this; linarith
        have hci2 : τ < c i + h' / 2 := by
          simp only [c]
          have := mul_lt_mul_of_pos_right hi2 (show (0:ℝ) < h' / 2 by positivity)
          rw [div_mul_cancel₀ _ (by positivity)] at this; linarith
        have hiN : i < N := by
          have : i ≤ Nat.floor ((1 - h) / (h' / 2)) := by
            apply Nat.floor_le_floor
            apply div_le_div_of_nonneg_right _ (by positivity)
            linarith
          omega
        refine ⟨i + 2, by omega, h' / 4, by positivity, ?_⟩
        intro y hy
        simp only [t1, t2, show i + 2 ≠ 0 by omega, show i + 2 ≠ 1 by omega, if_false,
          show i + 2 - 2 = i by omega]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- thresholds for every edge and interval
  have hJ : ∀ (e : G.edges) (j : ℕ), ∃ T : Finset (Fin n) → ℝ, j < N + 2 →
      (∀ S, T S ∈ Set.Icc (t1 j) (t2 j)) ∧
      ∀ (x : Profile G n) (τ : Fin n → ℝ), (∀ i, τ i ∈ Set.Icc (t1 j) (t2 j)) →
        (∀ i, ((x i : G.Pt) : E k) = epar e.1 (τ i)) →
        (∃ i, M x = x i) ∨ ∃ S, ((M x : G.Pt) : E k) = epar e.1 (T S) := by
    intro e j
    by_cases hj : j < N + 2
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hcond j hj
      obtain ⟨T, hT1, hT2⟩ := seg_gmvs G M hSP hM hn0 e.1 e.2 (t1 j) (t2 j) (η j) a1 a2 a3 a4 a5
      exact ⟨T, fun _ => ⟨hT1, hT2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hj⟩
  choose T hT using hJ
  let cl : ℝ → ℝ := fun t => max 0 (min t 1)
  have hcl : ∀ t, cl t ∈ Set.Icc (0:ℝ) 1 := fun t => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  let ptc : G.edges → ℝ → G.Pt := fun e t => ⟨epar e.1 (cl t), Set.mem_biUnion e.2 (epar_mem (hcl t))⟩
  let V : Finset G.Pt := G.edges.attach.biUnion (fun e =>
    {⟨e.1.1, Set.mem_biUnion e.2 (left_mem_segment ℝ _ _)⟩, ⟨e.1.2, Set.mem_biUnion e.2 (right_mem_segment ℝ _ _)⟩})
  let W : Finset G.Pt := V ∪ ((G.edges.attach ×ˢ Finset.range (N + 2) ×ˢ (Finset.univ : Finset (Finset (Fin n)))).image
    (fun ejS => ptc ejS.1 (T ejS.1 ejS.2.1 ejS.2.2)))
  refine ⟨W, fun x => ?_⟩
  by_cases hrep : ∃ i, M x = x i
  · exact Or.inl hrep
  right
  push Not at hrep
  set m := M x with hmdef
  by_cases hV : ∃ e ∈ G.edges, (m : E k) = e.1 ∨ (m : E k) = e.2
  · obtain ⟨e, he, h1 | h1⟩ := hV
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton]; left; exact Subtype.ext h1
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, ?_⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton]; right; exact Subtype.ext h1
  push Not at hV
  obtain ⟨e, he, hme⟩ := Set.mem_iUnion₂.1 m.2
  obtain ⟨τ, hτI, hmτ⟩ := (mem_seg_iff e _).1 hme
  have hτ : τ ∈ Set.Ioo (0:ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hτI.1 ?_, lt_of_le_of_ne hτI.2 ?_⟩
    · intro h0; apply (hV e he).1; rw [hmτ, ← h0, epar_zero]
    · intro h1; apply (hV e he).2; rw [hmτ, h1, epar_one]
  obtain ⟨j, hj, ε, hε, hsub⟩ := hcover τ hτ
  obtain ⟨x', τ', hτ'ε, hx', hτ'ne, hMx'⟩ :=
    move_near G M hSP hM x e he τ hτ hmτ (fun i h => hrep i h.symm) ε hε
  obtain ⟨hT1, hT2⟩ := hT ⟨e, he⟩ j hj
  rcases hT2 x' τ' (fun i => hsub (hτ'ε i)) hx' with ⟨i, hi⟩ | ⟨S, hS⟩
  · exfalso
    apply hτ'ne i
    apply epar_inj (G.fst_ne_snd e he)
    rw [← hx' i, ← hi, hMx', hmτ]
  · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(⟨e, he⟩, j, S), ?_, ?_⟩)
    · simp [hj]
    · apply Subtype.ext
      have hTI : T ⟨e, he⟩ j S ∈ Set.Icc (0:ℝ) 1 := by
        obtain ⟨a1, -, -, a4, a5⟩ := hcond j hj
        have ht1 : 0 ≤ t1 j := by
          rcases a4 with h | h
          · linarith
          · have : 0 ≤ η j := by
              have := hcond j hj
              have h0 : 0 ≤ ((n:ℝ) + 1) * (t2 j - t1 j) := mul_nonneg (by positivity) (by linarith)
              linarith [this.2.1]
            linarith
        have ht2 : t2 j ≤ 1 := by
          rcases a5 with h | h
          · linarith
          · have : 0 ≤ η j := by
              have := hcond j hj
              have h0 : 0 ≤ ((n:ℝ) + 1) * (t2 j - t1 j) := mul_nonneg (by positivity) (by linarith)
              linarith [this.2.1]
            linarith
        exact ⟨ht1.trans (hT1 S).1, (hT1 S).2.trans ht2⟩
      show epar e (cl (T ⟨e, he⟩ j S)) = (m : E k)
      rw [show cl (T ⟨e, he⟩ j S) = T ⟨e, he⟩ j S by simp only [cl]; rw [min_eq_left hTI.2, max_eq_right hTI.1]]
      rw [← hS, hMx']

end SPFGGeo


open SPFacilityGraph in
theorem solution {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ W : Finset G.Pt, ∀ x : Profile G n, (∃ i, M x = x i) ∨ M x ∈ W :=
  SPFGGeo.finite_values hn G M hSP hM
