-- Prove2me | solution 1 for SPFacilityGraph.sp_onto_gate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:23:20.20324+00:00
-- url     : https://prove2.me/submissions/c08bc1fd-f3b3-4d5a-9708-958cb046dab4

import Mathlib
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_triangle
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_comm
import Definitions.Def_SPFacilityGraph_IsSP

set_option autoImplicit false

-- ===== Seg1 =====


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

-- ===== Seg6 =====


namespace SPFGSeg

variable {n : ℕ} {a b : ℝ} {F : (Fin n → ℝ) → ℝ}

lemma thr_mono (hF : Hyp a b F) {S T : Finset (Fin n)} (h : S ⊆ T) : thr F a b S ≤ thr F a b T := by
  refine mono hF (InA.ext hF.hab S) (InA.ext hF.hab T) ?_
  intro j; simp only [ext]
  by_cases hj : j ∈ S
  · simp [hj, h hj]
  · simp only [hj, if_false]; split_ifs
    · exact hF.hab
    · exact le_rfl

lemma thr_empty (hF : Hyp a b F) : thr F a b ∅ = a := by
  have : ext (∅ : Finset (Fin n)) a b = fun _ => a := by funext j; simp [ext]
  simp only [thr, this]; exact unanimity hF ⟨le_rfl, hF.hab⟩

lemma thr_univ (hF : Hyp a b F) : thr F a b Finset.univ = b := by
  have : ext (Finset.univ : Finset (Fin n)) a b = fun _ => b := by funext j; simp [ext]
  simp only [thr, this]; exact unanimity hF ⟨hF.hab, le_rfl⟩

/-- the extreme profile of a sub-interval gives the clamped threshold -/
lemma ext_sub (hF : Hyp a b F) {a' b' : ℝ} (h1 : a ≤ a') (h2 : a' ≤ b') (h3 : b' ≤ b)
    (S : Finset (Fin n)) : F (ext S a' b') = max a' (min (thr F a b S) b') := by
  classical
  have hu : InA a b (ext S a' b') := by
    intro j; simp only [ext]; split_ifs
    · exact ⟨by linarith, h3⟩
    · exact ⟨h1, by linarith⟩
  rw [gmvs hF hu]
  apply le_antisymm
  · apply Finset.sup'_le
    intro T _
    by_cases hT : T ⊆ S
    · -- all of T at b'
      rcases T.eq_empty_or_nonempty with hTe | hTne
      · subst hTe
        refine (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans ?_
        rw [thr_empty hF]; exact h1.trans (le_max_left _ _)
      · apply le_max_of_le_right
        apply le_min
        · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (thr_mono hF hT)
        · obtain ⟨j, hj⟩ := hTne
          refine (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))).trans ?_
          simp [ext, hT hj]
    · obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.1 hT
      refine (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hjT))).trans ?_
      simp [ext, hjS]
  · apply max_le
    · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ Finset.univ))
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rw [thr_univ hF]; linarith
      · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
        simp only [ext]; split_ifs <;> linarith
    · refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ S))
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact min_le_left _ _
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
        simp [ext, hj]

end SPFGSeg

-- ===== Geo1 =====


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

-- ===== Geo2 =====


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

-- ===== Geo3 =====


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

-- ===== Geo4 =====


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

-- ===== Geo5 =====


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

-- ===== Geo6 =====


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

-- ===== Geo7 =====


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

-- ===== Geo8 =====


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

-- ===== Geo9 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- parameter from an endpoint `v` of an edge: `v + t (w - v)` where `w` is the other end -/
def vpar (v w : E k) (t : ℝ) : E k := v + t • (w - v)

/-- star around a vertex `v`: `v` together with the open initial pieces of length parameter `θ`
of all edges having `v` as an endpoint -/
def star (G : MetricGraph k) (v : E k) (θ : ℝ) : Set (E k) :=
  {v} ∪ {q | ∃ e ∈ G.edges, ∃ t, 0 < t ∧ t < θ ∧
    ((e.1 = v ∧ q = vpar e.1 e.2 t) ∨ (e.2 = v ∧ q = vpar e.2 e.1 t))}

/-- boundary of the star -/
def starBd (G : MetricGraph k) (v : E k) (θ : ℝ) : Set (E k) :=
  {q | ∃ e ∈ G.edges, (e.1 = v ∧ q = vpar e.1 e.2 θ) ∨ (e.2 = v ∧ q = vpar e.2 e.1 θ)}

lemma vpar_eq_epar (e : E k × E k) (t : ℝ) : vpar e.1 e.2 t = epar e t := rfl

lemma vpar_eq_epar' (e : E k × E k) (t : ℝ) : vpar e.2 e.1 t = epar e (1 - t) := by
  simp only [vpar, epar]
  rw [sub_smul, one_smul]
  module

/-- a vertex on an edge segment is an endpoint of that edge -/
lemma vertex_endpoint (G : MetricGraph k) (v : E k) (hv : ∃ e0 ∈ G.edges, v = e0.1 ∨ v = e0.2)
    (e : E k × E k) (he : e ∈ G.edges) (hve : v ∈ segment ℝ e.1 e.2) : v = e.1 ∨ v = e.2 := by
  obtain ⟨e0, he0, h0⟩ := hv
  by_cases hee : e = e0
  · subst hee; exact h0
  · have hv0 : v ∈ segment ℝ e0.1 e0.2 := by
      rcases h0 with h | h <;> rw [h]
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    exact (G.meet e he e0 he0 hee ⟨hve, hv0⟩).1

lemma star_cross (G : MetricGraph k) (v : E k) (hv : ∃ e0 ∈ G.edges, v = e0.1 ∨ v = e0.2)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∀ e' ∈ G.edges, ∀ a ∈ segment ℝ e'.1 e'.2, ∀ b ∈ segment ℝ e'.1 e'.2,
      a ∉ star G v θ → b ∈ star G v θ → ∃ q ∈ starBd G v θ, q ∈ segment ℝ a b := by
  intro e' he' a ha b hb haS hbS
  have hne' := G.fst_ne_snd e' he'
  obtain ⟨ta, hta, rfl⟩ := (mem_seg_iff e' a).1 ha
  -- generic finish on edge `e'` with `v = e'.1`
  have fin1 : v = e'.1 → ∀ tb ∈ Set.Icc (0:ℝ) θ, b = epar e' tb →
      ∃ q ∈ starBd G v θ, q ∈ segment ℝ (epar e' ta) b := by
    intro hv1 tb htb hbt
    have hta' : θ ≤ ta := by
      by_contra hc; push Not at hc
      apply haS
      rcases (eq_or_lt_of_le hta.1) with h | h
      · left; rw [← h, epar_zero, hv1]; rfl
      · right; exact ⟨e', he', ta, h, hc, Or.inl ⟨hv1.symm, by rw [vpar_eq_epar]⟩⟩
    refine ⟨epar e' θ, ⟨e', he', Or.inl ⟨hv1.symm, by rw [vpar_eq_epar]⟩⟩, ?_⟩
    rw [hbt]; apply epar_mem_segment; rw [Set.mem_uIcc]; right; exact ⟨htb.2, hta'⟩
  have fin2 : v = e'.2 → ∀ tb ∈ Set.Icc (1 - θ) 1, b = epar e' tb →
      ∃ q ∈ starBd G v θ, q ∈ segment ℝ (epar e' ta) b := by
    intro hv2 tb htb hbt
    have hta' : ta ≤ 1 - θ := by
      by_contra hc; push Not at hc
      apply haS
      rcases (eq_or_lt_of_le hta.2) with h | h
      · left; rw [h, epar_one, hv2]; rfl
      · right; refine ⟨e', he', 1 - ta, by linarith, by linarith, Or.inr ⟨hv2.symm, ?_⟩⟩
        rw [vpar_eq_epar']; congr 1; ring
    refine ⟨epar e' (1 - θ), ⟨e', he', Or.inr ⟨hv2.symm, by rw [vpar_eq_epar']⟩⟩, ?_⟩
    rw [hbt]; apply epar_mem_segment; rw [Set.mem_uIcc]; left; exact ⟨hta', htb.1⟩
  rcases hbS with hbv | ⟨e, he, t, ht0, htθ, hcase⟩
  · rw [Set.mem_singleton_iff] at hbv
    subst hbv
    rcases vertex_endpoint G b hv e' he' hb with h | h
    · exact fin1 h 0 ⟨le_rfl, hθ0.le⟩ (by rw [epar_zero]; exact h)
    · exact fin2 h 1 ⟨by linarith, le_rfl⟩ (by rw [epar_one]; exact h)
  · have hne := G.fst_ne_snd e he
    rcases hcase with ⟨hv1, rfl⟩ | ⟨hv2, rfl⟩
    · have hee : e' = e := edge_unique G e he t ⟨ht0, by linarith⟩ e' he' (by rw [← vpar_eq_epar]; exact hb)
      subst hee
      exact fin1 hv1.symm t ⟨ht0.le, htθ.le⟩ (vpar_eq_epar _ _)
    · have hee : e' = e := edge_unique G e he (1 - t) ⟨by linarith, by linarith⟩ e' he'
        (by rw [← vpar_eq_epar']; exact hb)
      subst hee
      exact fin2 hv2.symm (1 - t) ⟨by linarith, by linarith⟩ (vpar_eq_epar' _ _)

end SPFGGeo

-- ===== Geo10 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- A window: an isometric parametrization `φ` of `[α, β]` inside `G` on which outcomes of
window profiles lie in the hull of the reports. Then the restricted mechanism is a generalized
median voter scheme in the window coordinate. -/
lemma window_gmvs (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) (φ : ℝ → G.Pt) (α β : ℝ) (hαβ : α ≤ β)
    (hiso : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, G.dist (φ s) (φ t) = |s - t|)
    (hle : ∀ u : Fin n → ℝ, (∀ j, u j ∈ Set.Icc α β) → ∃ τ ∈ Set.Icc α β, M (fun j => φ (u j)) = φ τ) :
    ∃ F : (Fin n → ℝ) → ℝ, SPFGSeg.Hyp α β F ∧
      ∀ u : Fin n → ℝ, (∀ j, u j ∈ Set.Icc α β) → M (fun j => φ (u j)) = φ (F u) := by
  classical
  have hinj : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, φ s = φ t → s = t := by
    intro s hs t ht h
    have := hiso s hs t ht
    rw [h, dist_self] at this
    exact sub_eq_zero.1 (abs_eq_zero.1 this.symm)
  let cl : ℝ → ℝ := fun s => max α (min s β)
  have hcl : ∀ s, cl s ∈ Set.Icc α β := fun s => ⟨le_max_left _ _, max_le hαβ (min_le_right _ _)⟩
  have hcl_id : ∀ s ∈ Set.Icc α β, cl s = s := fun s hs => by
    simp only [cl]; rw [min_eq_left hs.2, max_eq_right hs.1]
  choose F hFI hF using fun u : Fin n → ℝ => hle (fun j => cl (u j)) (fun j => hcl _)
  refine ⟨F, ⟨hαβ, ?_, fun u _ => hFI u, ?_⟩, ?_⟩
  · intro u hu i v hv
    have h := hSP (fun j => φ (cl (u j))) i (φ (cl v))
    have e1 : Function.update (fun j => φ (cl (u j))) i (φ (cl v)) =
        fun j => φ (cl (Function.update u i v j)) := by
      funext j; by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [e1, hF u, hF (Function.update u i v), hiso _ (hFI _) _ (hcl _), hiso _ (hFI _) _ (hcl _),
      hcl_id _ (hu i)] at h
    exact h
  · intro s hs
    refine ⟨fun _ => s, fun _ => hs, ?_⟩
    have h1 := hF (fun _ => s)
    simp only [hcl_id s hs] at h1
    rw [unanimity G M hSP hM (φ s)] at h1
    exact (hinj _ hs _ (hFI _) h1).symm
  · intro u hu
    have : (fun j => φ (cl (u j))) = fun j => φ (u j) := by funext j; rw [hcl_id _ (hu j)]
    rw [← this]; exact hF u

end SPFGGeo

-- ===== Geo11 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- edge length -/
noncomputable def elen (e : E k × E k) : ℝ := ‖e.2 - e.1‖

lemma elen_pos (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) : 0 < elen e :=
  norm_pos_iff.2 (sub_ne_zero.2 (G.fst_ne_snd e he).symm)

/-- edge parameter of the point at distance `r` from the endpoint `v` -/
noncomputable def rpar (e : E k × E k) (v : E k) (r : ℝ) : ℝ :=
  if v = e.1 then r / elen e else 1 - r / elen e

lemma rpar_I (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (v : E k) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ elen e) : rpar e v r ∈ Set.Icc (0:ℝ) 1 := by
  have hL := elen_pos G he
  unfold rpar; split_ifs
  · exact ⟨div_nonneg hr0 hL.le, (div_le_one hL).2 hr⟩
  · exact ⟨by rw [sub_nonneg]; exact (div_le_one hL).2 hr, by linarith [div_nonneg hr0 hL.le]⟩

lemma rpar_zero (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v : E k}
    (hv : v = e.1 ∨ v = e.2) : epar e (rpar e v 0) = v := by
  unfold rpar; split_ifs with h
  · simp [epar_zero, h]
  · rcases hv with h' | h'
    · exact absurd h' h
    · simp [epar_one, h']

lemma rpar_sub (e : E k × E k) (v : E k) (hL : 0 < elen e) (r r' : ℝ) :
    |rpar e v r - rpar e v r'| * elen e = |r - r'| := by
  unfold rpar; split_ifs
  · rw [div_sub_div_same, abs_div, abs_of_pos hL]; field_simp
  · rw [show 1 - r / elen e - (1 - r' / elen e) = -(r - r') / elen e by field_simp; ring, abs_div,
      abs_neg, abs_of_pos hL]; field_simp

/-- point at distance `r` from `v` along `e` -/
noncomputable def rayPt (e : E k × E k) (v : E k) (r : ℝ) : E k := epar e (rpar e v r)

lemma rayPt_mem (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (v : E k) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ elen e) : rayPt e v r ∈ G.carrier :=
  Set.mem_biUnion he (epar_mem (rpar_I G he v hr0 hr))

lemma dist_rayPt (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (v : E k) (P Q : G.Pt)
    {r r' : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ elen e) (hr0' : 0 ≤ r') (hr' : r' ≤ elen e)
    (hP : (P : E k) = rayPt e v r) (hQ : (Q : E k) = rayPt e v r') : G.dist P Q = |r - r'| := by
  rw [dist_epar G e he P Q (rpar_I G he v hr0 hr) (rpar_I G he v hr0' hr') hP hQ]
  exact rpar_sub e v (elen_pos G he) r r'

/-- distance from outside an open edge to a point inside -/
lemma dist_open_edge (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (P Q : G.Pt)
    (hP : (P : E k) ∉ eint e 0 1) (hQ : (Q : E k) ∈ eint e 0 1) :
    ∃ b : G.Pt, ((b : E k) = e.1 ∨ (b : E k) = e.2) ∧ G.dist P Q = G.dist P b + G.dist b Q := by
  obtain ⟨b, hb, hd⟩ := cross G (eint e 0 1) _ (eint_cross G e he le_rfl le_rfl) P Q hP hQ
  refine ⟨b, ?_, hd⟩
  rcases hb with h | h
  · left; rw [h, epar_zero]
  · right; rw [Set.mem_singleton_iff] at h; rw [h, epar_one]

/-- a point of `e` at distance `r'` (strictly inside) lies in the open edge -/
lemma rayPt_open (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (v : E k) {r : ℝ}
    (hr0 : 0 < r) (hr : r < elen e) : rayPt e v r ∈ eint e 0 1 := by
  have hL := elen_pos G he
  refine ⟨rpar e v r, ?_, ?_, rfl⟩ <;> unfold rpar <;> split_ifs
  · exact div_pos hr0 hL
  · rw [sub_pos]; exact (div_lt_one hL).2 hr
  · exact (div_lt_one hL).2 hr
  · linarith [div_pos hr0 hL]

lemma dist_v_rayPt (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v : E k}
    (hv : v = e.1 ∨ v = e.2) (V P : G.Pt) (hV : (V : E k) = v) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ elen e) (hP : (P : E k) = rayPt e v r) : G.dist V P = r := by
  have := dist_rayPt G he v V P le_rfl (elen_pos G he).le hr0 hr
    (by rw [hV]; unfold rayPt; rw [rpar_zero G he hv]) hP
  rw [this, zero_sub, abs_neg, abs_of_nonneg hr0]

end SPFGGeo

-- ===== Geo12 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- a point of the open edge is not an endpoint -/
lemma endpoint_not_open (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v : E k}
    (hv : v = e.1 ∨ v = e.2) : v ∉ eint e 0 1 := by
  rintro ⟨t, ht0, ht1, h⟩
  have hne := G.fst_ne_snd e he
  rcases hv with rfl | rfl
  · rw [← epar_zero e] at h; have := epar_inj hne h; linarith
  · rw [← epar_one e] at h; have := epar_inj hne h; linarith

lemma seg_not_open (G : MetricGraph k) {e e' : E k × E k} (he : e ∈ G.edges) (he' : e' ∈ G.edges)
    (hee : e ≠ e') {P : E k} (hP : P ∈ segment ℝ e.1 e.2) : P ∉ eint e' 0 1 := by
  rintro ⟨t, ht0, ht1, rfl⟩
  exact hee (edge_unique G e' he' t ⟨ht0, ht1⟩ e he hP)

/-- bent window through the common endpoint `v` of two distinct edges -/
noncomputable def bwin (e1 e2 : E k × E k) (v : E k) (s : ℝ) : E k :=
  if s ≤ 0 then rayPt e1 v (-s) else rayPt e2 v s

lemma bwin_mem (G : MetricGraph k) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges) (he2 : e2 ∈ G.edges)
    (v : E k) {s : ℝ} (hs1 : -elen e1 ≤ s) (hs2 : s ≤ elen e2) : bwin e1 e2 v s ∈ G.carrier := by
  unfold bwin; split_ifs with h
  · exact rayPt_mem G he1 v (by linarith) (by linarith)
  · exact rayPt_mem G he2 v (by linarith) hs2

lemma bwin_seg1 (G : MetricGraph k) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges) (v : E k) {s : ℝ}
    (hs1 : -elen e1 ≤ s) (hs : s ≤ 0) : bwin e1 e2 v s ∈ segment ℝ e1.1 e1.2 := by
  unfold bwin; rw [if_pos hs]
  exact epar_mem (rpar_I G he1 v (by linarith) (by linarith))

lemma rayPt_zero (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v : E k}
    (hv : v = e.1 ∨ v = e.2) : rayPt e v 0 = v := rpar_zero G he hv

lemma bwin_zero (G : MetricGraph k) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges) {v : E k}
    (hv1 : v = e1.1 ∨ v = e1.2) : bwin e1 e2 v 0 = v := by
  unfold bwin; rw [if_pos le_rfl, neg_zero, rayPt_zero G he1 hv1]

lemma bwin_seg2 (G : MetricGraph k) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges) (he2 : e2 ∈ G.edges)
    {v : E k} (hv1 : v = e1.1 ∨ v = e1.2) (hv2 : v = e2.1 ∨ v = e2.2) {s : ℝ}
    (hs : 0 ≤ s) (hs2 : s ≤ elen e2) : bwin e1 e2 v s ∈ segment ℝ e2.1 e2.2 := by
  by_cases h : s ≤ 0
  · have : s = 0 := le_antisymm h hs
    subst this; rw [bwin_zero G he1 hv1]
    rcases hv2 with h' | h' <;> rw [h']
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  · unfold bwin; rw [if_neg h]; exact epar_mem (rpar_I G he2 v hs hs2)

/-- bent windows are isometric near the vertex -/
lemma bwin_iso (G : MetricGraph k) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges) (he2 : e2 ∈ G.edges)
    (hne : e1 ≠ e2) {v : E k} (hv1 : v = e1.1 ∨ v = e1.2) (hv2 : v = e2.1 ∨ v = e2.2) {A : ℝ}
    (hA1 : 2 * A ≤ elen e1) (hA2 : 2 * A ≤ elen e2) (P Q : G.Pt) {s t : ℝ}
    (hs : s ∈ Set.Icc (-A) A) (ht : t ∈ Set.Icc (-A) A)
    (hP : (P : E k) = bwin e1 e2 v s) (hQ : (Q : E k) = bwin e1 e2 v t) :
    G.dist P Q = |s - t| := by
  have hL1 := elen_pos G he1
  have hL2 := elen_pos G he2
  have hA0 : 0 ≤ A := by linarith [hs.1, hs.2]
  -- the vertex as a point
  have hvc : v ∈ G.carrier := by
    have := bwin_mem G he1 he2 v (s := 0) (by linarith) (by linarith)
    rwa [bwin_zero G he1 hv1] at this
  let V : G.Pt := ⟨v, hvc⟩
  -- same side cases
  have side1 : ∀ (P Q : G.Pt) (s t : ℝ), s ∈ Set.Icc (-A) 0 → t ∈ Set.Icc (-A) 0 →
      (P : E k) = bwin e1 e2 v s → (Q : E k) = bwin e1 e2 v t → G.dist P Q = |s - t| := by
    intro P Q s t hs ht hP hQ
    unfold bwin at hP hQ; rw [if_pos hs.2] at hP; rw [if_pos ht.2] at hQ
    rw [dist_rayPt G he1 v P Q (by linarith [hs.2]) (by linarith [hs.1]) (by linarith [ht.2])
      (by linarith [ht.1]) hP hQ]
    rw [show -s - -t = -(s - t) by ring, abs_neg]
  have side2 : ∀ (P Q : G.Pt) (s t : ℝ), s ∈ Set.Icc 0 A → t ∈ Set.Icc 0 A →
      (P : E k) = bwin e1 e2 v s → (Q : E k) = bwin e1 e2 v t → G.dist P Q = |s - t| := by
    intro P Q s t hs ht hP hQ
    have e1' : ∀ r, 0 ≤ r → bwin e1 e2 v r = rayPt e2 v r := by
      intro r hr
      by_cases h : r ≤ 0
      · have : r = 0 := le_antisymm h hr
        subst this; rw [bwin_zero G he1 hv1, rayPt_zero G he2 hv2]
      · unfold bwin; rw [if_neg h]
    rw [e1' s hs.1] at hP; rw [e1' t ht.1] at hQ
    exact dist_rayPt G he2 v P Q hs.1 (by linarith [hs.2]) ht.1 (by linarith [ht.2]) hP hQ
  -- opposite sides
  have cross12 : ∀ (P Q : G.Pt) (s t : ℝ), s ∈ Set.Icc (-A) 0 → t ∈ Set.Ioc 0 A →
      (P : E k) = bwin e1 e2 v s → (Q : E k) = bwin e1 e2 v t → G.dist P Q = t - s := by
    intro P Q s t hs ht hP hQ
    have hQ' : (Q : E k) = rayPt e2 v t := by unfold bwin at hQ; rwa [if_neg (not_le.2 ht.1)] at hQ
    have hPV : G.dist P V = -s := by
      rw [G.dist_comm]
      refine dist_v_rayPt G he1 hv1 V P rfl (by linarith [hs.2]) (by linarith [hs.1]) ?_
      unfold bwin at hP; rwa [if_pos hs.2] at hP
    have hVQ : G.dist V Q = t := dist_v_rayPt G he2 hv2 V Q rfl ht.1.le (by linarith [ht.2]) hQ'
    apply le_antisymm
    · have := G.dist_triangle P V Q; linarith
    · have hPo : (P : E k) ∉ eint e2 0 1 := by
        by_cases hs0 : s = 0
        · rw [hP, hs0, bwin_zero G he1 hv1]; exact endpoint_not_open G he2 hv2
        · exact seg_not_open G he1 he2 hne (hP ▸ bwin_seg1 G he1 v (by linarith [hs.1]) hs.2)
      have hQo : (Q : E k) ∈ eint e2 0 1 := hQ' ▸ rayPt_open G he2 v ht.1 (by linarith [ht.2])
      obtain ⟨b, hb, hd⟩ := dist_open_edge G he2 P Q hPo hQo
      by_cases hbv : (b : E k) = v
      · have : b = V := Subtype.ext hbv
        rw [hd, this, hPV, hVQ]; linarith
      · -- b is the other endpoint
        have hbL : G.dist V b = elen e2 := by
          have hb' : (b : E k) = rayPt e2 v (elen e2) := by
            unfold rayPt rpar
            rcases hv2 with h2 | h2 <;> rcases hb with h3 | h3
            · exact absurd (h3.trans h2.symm) hbv
            · rw [if_pos h2, div_self (ne_of_gt hL2), epar_one]; exact h3
            · rw [if_neg (by intro h; exact (G.fst_ne_snd e2 he2) (h.symm.trans h2)), div_self (ne_of_gt hL2),
                sub_self, epar_zero]; exact h3
            · exact absurd (h3.trans h2.symm) hbv
          exact dist_v_rayPt G he2 hv2 V b rfl hL2.le le_rfl hb'
        have hbQ : G.dist b Q = elen e2 - t := by
          have hb' : (b : E k) = rayPt e2 v (elen e2) := by
            unfold rayPt rpar
            rcases hv2 with h2 | h2 <;> rcases hb with h3 | h3
            · exact absurd (h3.trans h2.symm) hbv
            · rw [if_pos h2, div_self (ne_of_gt hL2), epar_one]; exact h3
            · rw [if_neg (by intro h; exact (G.fst_ne_snd e2 he2) (h.symm.trans h2)), div_self (ne_of_gt hL2),
                sub_self, epar_zero]; exact h3
            · exact absurd (h3.trans h2.symm) hbv
          rw [dist_rayPt G he2 v b Q hL2.le le_rfl ht.1.le (by linarith [ht.2]) hb' hQ',
            abs_of_nonneg (by linarith [ht.2])]
        have t1 := G.dist_triangle V P b
        rw [G.dist_comm V P, hPV] at t1
        rw [hd, hbQ]
        linarith [ht.2, hs.1]
  rcases le_total s 0 with hs0 | hs0 <;> rcases le_total t 0 with ht0 | ht0
  · exact side1 P Q s t ⟨hs.1, hs0⟩ ⟨ht.1, ht0⟩ hP hQ
  · rcases eq_or_lt_of_le ht0 with h | h
    · exact side1 P Q s t ⟨hs.1, hs0⟩ ⟨ht.1, h.symm.le⟩ hP hQ
    · rw [cross12 P Q s t ⟨hs.1, hs0⟩ ⟨h, ht.2⟩ hP hQ, abs_of_nonpos (by linarith)]; ring
  · rcases eq_or_lt_of_le hs0 with h | h
    · exact side1 P Q s t ⟨hs.1, h.symm.le⟩ ⟨ht.1, ht0⟩ hP hQ
    · rw [G.dist_comm, cross12 Q P t s ⟨ht.1, ht0⟩ ⟨h, hs.2⟩ hQ hP, abs_of_nonneg (by linarith)]
  · exact side2 P Q s t ⟨hs0, hs.2⟩ ⟨ht0, ht.2⟩ hP hQ

end SPFGGeo

-- ===== Geo13 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- on an isometric window, an outcome lying on the window lies between the extreme reports -/
lemma window_hull (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) (φ : ℝ → G.Pt) (α β : ℝ)
    (hiso : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, G.dist (φ s) (φ t) = |s - t|)
    (u : Fin n → ℝ) (hu : ∀ j, u j ∈ Set.Icc α β) (τ : ℝ) (hτ : τ ∈ Set.Icc α β)
    (hm : M (fun j => φ (u j)) = φ τ) :
    Finset.univ.inf' (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) u ≤ τ ∧
      τ ≤ Finset.univ.sup' (Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩) u := by
  classical
  have hne : Finset.univ.Nonempty := Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩
  obtain ⟨jmin, -, hjmin⟩ := Finset.exists_mem_eq_inf' hne u
  obtain ⟨jmax, -, hjmax⟩ := Finset.exists_mem_eq_sup' hne u
  have hmin_le : ∀ j, Finset.univ.inf' hne u ≤ u j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hle_max : ∀ j, u j ≤ Finset.univ.sup' hne u := fun j => Finset.le_sup' _ (Finset.mem_univ j)
  set x : Profile G n := fun j => φ (u j)
  constructor
  · by_contra hc; push Not at hc
    rw [hjmin] at hc hmin_le
    apply lemma2 G M hSP hM x (x jmin)
    · intro h
      have h' : φ (u jmin) = φ τ := h.trans hm
      have := hiso _ (hu jmin) _ hτ
      rw [h', dist_self] at this
      have : u jmin - τ = 0 := abs_eq_zero.1 this.symm
      linarith
    · intro j
      show G.dist (φ (u j)) (φ (u jmin)) + G.dist (φ (u jmin)) (M x) = G.dist (φ (u j)) (M x)
      rw [hm, hiso _ (hu j) _ (hu jmin), hiso _ (hu jmin) _ hτ, hiso _ (hu j) _ hτ,
        abs_of_nonneg (by linarith [hmin_le j] : 0 ≤ u j - u jmin),
        abs_of_pos (by linarith : 0 < u jmin - τ), abs_of_pos (by linarith [hmin_le j] : 0 < u j - τ)]
      ring
  · by_contra hc; push Not at hc
    rw [hjmax] at hc hle_max
    apply lemma2 G M hSP hM x (x jmax)
    · intro h
      have h' : φ (u jmax) = φ τ := h.trans hm
      have := hiso _ (hu jmax) _ hτ
      rw [h', dist_self] at this
      have : u jmax - τ = 0 := abs_eq_zero.1 this.symm
      linarith
    · intro j
      show G.dist (φ (u j)) (φ (u jmax)) + G.dist (φ (u jmax)) (M x) = G.dist (φ (u j)) (M x)
      rw [hm, hiso _ (hu j) _ (hu jmax), hiso _ (hu jmax) _ hτ, hiso _ (hu j) _ hτ,
        abs_of_nonpos (by linarith [hle_max j] : u j - u jmax ≤ 0),
        abs_of_neg (by linarith : u jmax - τ < 0), abs_of_neg (by linarith [hle_max j] : u j - τ < 0)]
      ring

end SPFGGeo

-- ===== Geo14 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- minimal edge length -/
noncomputable def Lmin (G : MetricGraph k) : ℝ := G.edges.inf' G.edges_nonempty elen

lemma Lmin_le (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) : Lmin G ≤ elen e :=
  Finset.inf'_le _ he

lemma Lmin_pos (G : MetricGraph k) : 0 < Lmin G := by
  obtain ⟨e, he, h⟩ := Finset.exists_mem_eq_inf' G.edges_nonempty elen
  unfold Lmin; rw [h]; exact elen_pos G he

lemma vpar_rayPt1 (e : E k × E k) (hL : 0 < elen e) (t : ℝ) :
    vpar e.1 e.2 t = rayPt e e.1 (t * elen e) := by
  unfold rayPt rpar; rw [if_pos rfl, mul_div_assoc, div_self (ne_of_gt hL), mul_one]; rfl

lemma vpar_rayPt2 (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (t : ℝ) :
    vpar e.2 e.1 t = rayPt e e.2 (t * elen e) := by
  have hL := elen_pos G he
  unfold rayPt rpar
  rw [if_neg (fun h => G.fst_ne_snd e he h.symm), mul_div_assoc, div_self (ne_of_gt hL), mul_one,
    vpar_eq_epar']

/-- points of the star around `v` -/
lemma star_cases (G : MetricGraph k) (v : E k) (m : E k) (hm : m ∈ star G v (1/2)) :
    m = v ∨ ∃ e ∈ G.edges, (v = e.1 ∨ v = e.2) ∧ ∃ r, 0 < r ∧ r < elen e / 2 ∧ m = rayPt e v r := by
  rcases hm with h | ⟨e, he, t, ht0, ht1, h⟩
  · left; exact h
  · right
    have hL := elen_pos G he
    rcases h with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · refine ⟨e, he, Or.inl hv.symm, t * elen e, mul_pos ht0 hL, by nlinarith, ?_⟩
      rw [← hv, vpar_rayPt1 e hL]
    · refine ⟨e, he, Or.inr hv.symm, t * elen e, mul_pos ht0 hL, by nlinarith, ?_⟩
      rw [← hv, vpar_rayPt2 G he]

lemma starBd_cases (G : MetricGraph k) (v : E k) (q : E k) (hq : q ∈ starBd G v (1/2)) :
    ∃ e ∈ G.edges, (v = e.1 ∨ v = e.2) ∧ q = rayPt e v (elen e / 2) := by
  obtain ⟨e, he, h⟩ := hq
  have hL := elen_pos G he
  rcases h with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
  · refine ⟨e, he, Or.inl hv.symm, ?_⟩; rw [← hv, vpar_rayPt1 e hL]; ring_nf
  · refine ⟨e, he, Or.inr hv.symm, ?_⟩; rw [← hv, vpar_rayPt2 G he]; ring_nf

/-- local efficiency on bent windows -/
lemma bwin_le (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges)
    (he2 : e2 ∈ G.edges) (hne : e1 ≠ e2) {v : E k} (hv1 : v = e1.1 ∨ v = e1.2)
    (hv2 : v = e2.1 ∨ v = e2.2) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G)
    (φ : ℝ → G.Pt) (hφ : ∀ s ∈ Set.Icc (-(2 * (n + 1) * α)) (2 * (n + 1) * α),
      (φ s : E k) = bwin e1 e2 v s)
    (u : Fin n → ℝ) (hu : ∀ j, u j ∈ Set.Icc (-α) α) :
    ∃ τ ∈ Set.Icc (-α) α, M (fun j => φ (u j)) = φ τ := by
  classical
  set A := 2 * (n + 1) * α with hAdef
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hαA : α ≤ A := by rw [hAdef]; nlinarith
  have hA1 : 2 * A ≤ elen e1 := by rw [hAdef]; linarith [Lmin_le G he1]
  have hA2 : 2 * A ≤ elen e2 := by rw [hAdef]; linarith [Lmin_le G he2]
  have hiso : ∀ s ∈ Set.Icc (-A) A, ∀ t ∈ Set.Icc (-A) A, G.dist (φ s) (φ t) = |s - t| :=
    fun s hs t ht => bwin_iso G he1 he2 hne hv1 hv2 hA1 hA2 _ _ hs ht (hφ s hs) (hφ t ht)
  have huA : ∀ j, u j ∈ Set.Icc (-A) A := fun j => ⟨by linarith [(hu j).1], by linarith [(hu j).2]⟩
  have h0A : (0:ℝ) ∈ Set.Icc (-A) A := ⟨by linarith, by linarith⟩
  set x : Profile G n := fun j => φ (u j)
  set m := M x
  set V := φ 0
  have hV : (V : E k) = v := by rw [hφ 0 h0A, bwin_zero G he1 hv1]
  have hD : ∀ i j, G.dist (x i) (x j) ≤ 2 * α := by
    intro i j; show G.dist (φ (u i)) (φ (u j)) ≤ 2 * α
    rw [hiso _ (huA i) _ (huA j), abs_le]
    constructor <;> linarith [(hu i).1, (hu i).2, (hu j).1, (hu j).2]
  obtain ⟨i0, hi0⟩ := approx_eff G M hSP hM hn x (2 * α) hD
  have hVm : G.dist V m ≤ (2 * n + 1) * α := by
    have h1 : G.dist V (x i0) ≤ α := by
      show G.dist (φ 0) (φ (u i0)) ≤ α
      rw [hiso _ h0A _ (huA i0), zero_sub, abs_neg, abs_le]
      constructor <;> linarith [(hu i0).1, (hu i0).2]
    have := G.dist_triangle V (x i0) m
    nlinarith
  have hvert : ∃ e0 ∈ G.edges, v = e0.1 ∨ v = e0.2 := ⟨e1, he1, hv1⟩
  -- the outcome lies in the star around `v`
  have hmS : (m : E k) ∈ star G v (1/2) := by
    by_contra hc
    have hVS : (V : E k) ∈ star G v (1/2) := by left; exact hV
    obtain ⟨q, hqB, hq⟩ := cross G _ _ (star_cross G v hvert (1/2) (by norm_num) (by norm_num)) m V hc hVS
    obtain ⟨e, he, hve, hqe⟩ := starBd_cases G v q hqB
    have hdq : G.dist V q = elen e / 2 := dist_v_rayPt G he hve V q hV (by linarith [elen_pos G he])
      (by linarith [elen_pos G he]) hqe
    have := dist_nonneg G m q
    rw [G.dist_comm q V, hdq] at hq
    rw [G.dist_comm V m] at hVm
    have := Lmin_le G he
    nlinarith
  rcases star_cases G v m hmS with hmv | ⟨e, he, hve, r, hr0, hr1, hmr⟩
  · exact ⟨0, ⟨by linarith, by linarith⟩, Subtype.ext (by rw [hmv, ← hV])⟩
  · have hVm' : G.dist V m = r := dist_v_rayPt G he hve V m hV hr0.le (by linarith) hmr
    have hrA : r ≤ A := by rw [← hVm']; rw [hAdef]; nlinarith
    by_cases h1 : e = e1
    · subst h1
      have hφm : m = φ (-r) := by
        apply Subtype.ext
        rw [hφ (-r) ⟨by linarith, by linarith⟩, hmr]
        unfold bwin; rw [if_pos (by linarith), neg_neg]
      obtain ⟨hl, hh⟩ := window_hull G M hSP hM hn φ (-A) A hiso u huA (-r) ⟨by linarith, by linarith⟩ hφm
      refine ⟨-r, ⟨?_, ?_⟩, hφm⟩
      · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩) u
        rw [hj] at hl; linarith [(hu j).1]
      · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩) u
        rw [hj] at hh; linarith [(hu j).2]
    · by_cases h2 : e = e2
      · subst h2
        have hφm : m = φ r := by
          apply Subtype.ext
          rw [hφ r ⟨by linarith, hrA⟩, hmr]
          unfold bwin; rw [if_neg (by linarith)]
        obtain ⟨hl, hh⟩ := window_hull G M hSP hM hn φ (-A) A hiso u huA r ⟨by linarith, hrA⟩ hφm
        refine ⟨r, ⟨?_, ?_⟩, hφm⟩
        · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩) u
          rw [hj] at hl; linarith [(hu j).1]
        · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩) u
          rw [hj] at hh; linarith [(hu j).2]
      · -- outcome on a third edge: contradiction with Lemma 2
        exfalso
        have hLe := Lmin_le G he
        have hmo : (m : E k) ∈ eint e 0 1 := hmr ▸ rayPt_open G he v hr0 (by linarith)
        apply lemma2 G M hSP hM x V
        · intro h; apply endpoint_not_open G he hve; rw [← hV, h]; exact hmo
        · intro j
          have hxj : ((x j : G.Pt) : E k) ∉ eint e 0 1 := by
            show ((φ (u j) : G.Pt) : E k) ∉ eint e 0 1
            rw [hφ _ (huA j)]
            by_cases hj : u j ≤ 0
            · exact seg_not_open G he1 he (Ne.symm h1) (bwin_seg1 G he1 v (by linarith [(huA j).1]) hj)
            · exact seg_not_open G he2 he (Ne.symm h2)
                (bwin_seg2 G he1 he2 hv1 hv2 (by linarith) (by linarith [(huA j).2]))
          obtain ⟨b, hb, hd⟩ := dist_open_edge G he (x j) m hxj hmo
          have hxV : G.dist (x j) V ≤ α := by
            show G.dist (φ (u j)) (φ 0) ≤ α
            rw [hiso _ (huA j) _ h0A, sub_zero, abs_le]; exact ⟨(hu j).1, (hu j).2⟩
          by_cases hbv : (b : E k) = v
          · have : b = V := Subtype.ext (hbv.trans hV.symm)
            rw [this] at hd; rw [hd]
          · exfalso
            have hbr : (b : E k) = rayPt e v (elen e) := by
              unfold rayPt rpar
              have hL := elen_pos G he
              rcases hve with h3 | h3 <;> rcases hb with h4 | h4
              · exact absurd (h4.trans h3.symm) hbv
              · rw [if_pos h3, div_self (ne_of_gt hL), epar_one]; exact h4
              · rw [if_neg (by intro h; exact (G.fst_ne_snd e he) (h.symm.trans h3)), div_self (ne_of_gt hL),
                  sub_self, epar_zero]; exact h4
              · exact absurd (h4.trans h3.symm) hbv
            have hVb : G.dist V b = elen e := dist_v_rayPt G he hve V b hV (elen_pos G he).le le_rfl hbr
            have hbm : G.dist b m = elen e - r := by
              rw [dist_rayPt G he v b m (elen_pos G he).le le_rfl hr0.le (by linarith) hbr hmr,
                abs_of_nonneg (by linarith)]
            have t1 := G.dist_triangle V (x j) b
            have t2 := G.dist_triangle (x j) V m
            rw [G.dist_comm V (x j)] at t1
            rw [hVm'] at t2
            nlinarith

end SPFGGeo

-- ===== Geo15 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- coalition `S` at `p'`, the others at `p` -/
def two (S : Finset (Fin n)) {G : MetricGraph k} (p p' : G.Pt) : Profile G n :=
  fun j => if j ∈ S then p' else p

/-- `S` standing at `p'` loses against the others at `p` -/
def Lose {G : MetricGraph k} (M : Profile G n → G.Pt) (S : Finset (Fin n)) (p p' : G.Pt) : Prop := M (two S p p') = p

/-- a window with its generalized median structure -/
structure Win (G : MetricGraph k) (M : Profile G n → G.Pt) where
  φ : ℝ → G.Pt
  α : ℝ
  β : ℝ
  F : (Fin n → ℝ) → ℝ
  hyp : SPFGSeg.Hyp α β F
  iso : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, G.dist (φ s) (φ t) = |s - t|
  eq : ∀ u : Fin n → ℝ, (∀ j, u j ∈ Set.Icc α β) → M (fun j => φ (u j)) = φ (F u)

lemma Win.inj {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) {s t : ℝ}
    (hs : s ∈ Set.Icc W.α W.β) (ht : t ∈ Set.Icc W.α W.β) (h : W.φ s = W.φ t) : s = t := by
  have := W.iso s hs t ht
  rw [h, dist_self] at this
  exact sub_eq_zero.1 (abs_eq_zero.1 this.symm)

lemma Win.two_eq {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (S : Finset (Fin n))
    {s t : ℝ} (hs : s ∈ Set.Icc W.α W.β) (ht : t ∈ Set.Icc W.α W.β) (hst : s ≤ t) :
    M (two S (W.φ s) (W.φ t)) = W.φ (max s (min (SPFGSeg.thr W.F W.α W.β S) t)) := by
  have e1 : two S (W.φ s) (W.φ t) = fun j => W.φ (SPFGSeg.ext S s t j) := by
    funext j; simp only [two, SPFGSeg.ext]; split_ifs <;> rfl
  rw [e1, W.eq _ (fun j => by simp only [SPFGSeg.ext]; split_ifs; exacts [ht, hs]),
    SPFGSeg.ext_sub W.hyp hs.1 hst ht.2]

/-- transition: losing propagates forward along a window -/
lemma Win.lose_step {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (S : Finset (Fin n))
    {s1 s2 s3 : ℝ} (h1 : W.α ≤ s1) (h12 : s1 < s2) (h23 : s2 < s3) (h3 : s3 ≤ W.β)
    (hL : Lose M S (W.φ s1) (W.φ s2)) : Lose M S (W.φ s2) (W.φ s3) := by
  have hs1 : s1 ∈ Set.Icc W.α W.β := ⟨h1, by linarith⟩
  have hs2 : s2 ∈ Set.Icc W.α W.β := ⟨by linarith, by linarith⟩
  have hs3 : s3 ∈ Set.Icc W.α W.β := ⟨by linarith, h3⟩
  unfold Lose at hL ⊢
  rw [W.two_eq S hs1 hs2 h12.le] at hL
  have hmem : max s1 (min (SPFGSeg.thr W.F W.α W.β S) s2) ∈ Set.Icc W.α W.β :=
    ⟨le_max_of_le_left h1, max_le (by linarith) (min_le_of_right_le (by linarith))⟩
  have h := W.inj hmem hs1 hL
  have ht : SPFGSeg.thr W.F W.α W.β S ≤ s1 := by
    by_contra hc; push Not at hc
    have : s1 < min (SPFGSeg.thr W.F W.α W.β S) s2 := lt_min hc h12
    have := le_max_right s1 (min (SPFGSeg.thr W.F W.α W.β S) s2)
    linarith
  rw [W.two_eq S hs2 hs3 h23.le, min_eq_left (by linarith), max_eq_left (by linarith)]

/-- an interior threshold: losing just right of it -/
lemma Win.thr_lose {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (S : Finset (Fin n))
    {s1 s2 : ℝ} (h1 : SPFGSeg.thr W.F W.α W.β S < s1) (h12 : s1 < s2) (h2 : s2 ≤ W.β) :
    Lose M S (W.φ s1) (W.φ s2) := by
  have hthr := (W.hyp.range _ (SPFGSeg.InA.ext W.hyp.hab S)).1
  have hs1 : s1 ∈ Set.Icc W.α W.β := ⟨by unfold SPFGSeg.thr at h1; linarith, by linarith⟩
  have hs2 : s2 ∈ Set.Icc W.α W.β := ⟨by linarith [hs1.1], h2⟩
  unfold Lose
  rw [W.two_eq S hs1 hs2 h12.le, min_eq_left (by linarith), max_eq_left (by linarith)]

/-- an interior threshold: not losing just left of it -/
lemma Win.thr_notlose {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (S : Finset (Fin n))
    {s1 s2 : ℝ} (h1 : W.α ≤ s1) (h12 : s1 < s2) (h2 : s2 < SPFGSeg.thr W.F W.α W.β S) :
    ¬ Lose M S (W.φ s1) (W.φ s2) := by
  have hthr := (W.hyp.range _ (SPFGSeg.InA.ext W.hyp.hab S)).2
  have hs1 : s1 ∈ Set.Icc W.α W.β := ⟨h1, by unfold SPFGSeg.thr at h2; linarith⟩
  have hs2 : s2 ∈ Set.Icc W.α W.β := ⟨by linarith, by unfold SPFGSeg.thr at h2; linarith⟩
  unfold Lose
  rw [W.two_eq S hs1 hs2 h12.le, min_eq_right h2.le, max_eq_right h12.le]
  intro h
  have := W.inj hs2 hs1 h
  linarith

end SPFGGeo

-- ===== Geo16 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- a bent window as a `Win` -/
lemma bwin_Win (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges)
    (he2 : e2 ∈ G.edges) (hne : e1 ≠ e2) {v : E k} (hv1 : v = e1.1 ∨ v = e1.2)
    (hv2 : v = e2.1 ∨ v = e2.2) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G) :
    ∃ W : Win G M, W.α = -α ∧ W.β = α ∧ ∀ s ∈ Set.Icc (-α) α, (W.φ s : E k) = bwin e1 e2 v s := by
  classical
  set A := 2 * (n + 1) * α with hAdef
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hαA : α ≤ A := by rw [hAdef]; nlinarith
  have hA1 : 2 * A ≤ elen e1 := by rw [hAdef]; linarith [Lmin_le G he1]
  have hA2 : 2 * A ≤ elen e2 := by rw [hAdef]; linarith [Lmin_le G he2]
  let cl : ℝ → ℝ := fun s => max (-A) (min s A)
  have hcl : ∀ s, cl s ∈ Set.Icc (-A) A := fun s => ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcl_id : ∀ s ∈ Set.Icc (-A) A, cl s = s := fun s hs => by
    simp only [cl]; rw [min_eq_left hs.2, max_eq_right hs.1]
  let φ : ℝ → G.Pt := fun s => ⟨bwin e1 e2 v (cl s), bwin_mem G he1 he2 v (by linarith [(hcl s).1])
    (by linarith [(hcl s).2])⟩
  have hφ : ∀ s ∈ Set.Icc (-A) A, (φ s : E k) = bwin e1 e2 v s := fun s hs => by
    show bwin e1 e2 v (cl s) = _; rw [hcl_id s hs]
  have hiso : ∀ s ∈ Set.Icc (-α) α, ∀ t ∈ Set.Icc (-α) α, G.dist (φ s) (φ t) = |s - t| := by
    intro s hs t ht
    exact bwin_iso G he1 he2 hne hv1 hv2 hA1 hA2 _ _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (hφ s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (hφ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  obtain ⟨F, hH, hF⟩ := window_gmvs G M hSP hM hn φ (-α) α (by linarith) hiso
    (fun u hu => bwin_le G M hSP hM hn he1 he2 hne hv1 hv2 hα hαL φ hφ u hu)
  exact ⟨⟨φ, -α, α, F, hH, hiso, hF⟩, rfl, rfl,
    fun s hs => hφ s ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩

/-- a straight window inside an edge (arclength coordinate from `e.1`) -/
lemma swin_Win (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) {e : E k × E k} (he : e ∈ G.edges)
    {r0 lm η : ℝ} (hlm : 0 < lm) (hη : (n + 1) * (2 * lm) < η)
    (hl : 0 ≤ r0 - lm - η) (hr : r0 + lm + η ≤ elen e) :
    ∃ W : Win G M, W.α = -lm ∧ W.β = lm ∧ ∀ s ∈ Set.Icc (-lm) lm,
      (W.φ s : E k) = rayPt e e.1 (r0 + s) := by
  classical
  have hL := elen_pos G he
  set L := elen e
  let cl : ℝ → ℝ := fun s => max (-lm) (min s lm)
  have hcl : ∀ s, cl s ∈ Set.Icc (-lm) lm := fun s => ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcl_id : ∀ s ∈ Set.Icc (-lm) lm, cl s = s := fun s hs => by
    simp only [cl]; rw [min_eq_left hs.2, max_eq_right hs.1]
  have hηpos : 0 < η := by nlinarith [show (0:ℝ) ≤ n by positivity]
  have hrI : ∀ s ∈ Set.Icc (-lm) lm, 0 ≤ r0 + s ∧ r0 + s ≤ L := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let φ : ℝ → G.Pt := fun s => ⟨rayPt e e.1 (r0 + cl s), rayPt_mem G he e.1 (hrI _ (hcl s)).1 (hrI _ (hcl s)).2⟩
  have hφ : ∀ s ∈ Set.Icc (-lm) lm, (φ s : E k) = rayPt e e.1 (r0 + s) := fun s hs => by
    show rayPt e e.1 (r0 + cl s) = _; rw [hcl_id s hs]
  have hiso : ∀ s ∈ Set.Icc (-lm) lm, ∀ t ∈ Set.Icc (-lm) lm, G.dist (φ s) (φ t) = |s - t| := by
    intro s hs t ht
    rw [dist_rayPt G he e.1 (φ s) (φ t) (hrI s hs).1 (hrI s hs).2 (hrI t ht).1 (hrI t ht).2 (hφ s hs) (hφ t ht)]
    congr 1; ring
  have hpar : ∀ r, rayPt e e.1 r = epar e (r / L) := fun r => by unfold rayPt rpar; rw [if_pos rfl]
  have hle : ∀ u : Fin n → ℝ, (∀ j, u j ∈ Set.Icc (-lm) lm) →
      ∃ τ ∈ Set.Icc (-lm) lm, M (fun j => φ (u j)) = φ τ := by
    intro u hu
    have hloc := local_eff G M hSP hM hn e he ((r0 - lm) / L) ((r0 + lm) / L) (η / L)
      (by apply div_le_div_of_nonneg_right _ hL.le; linarith)
      (by rw [← sub_div, mul_div_assoc', div_lt_div_iff_of_pos_right hL]; nlinarith)
      (by rw [div_le_one hL]; linarith)
      (Or.inr (by rw [← sub_div]; exact div_nonneg (by linarith) hL.le))
      (Or.inr (by rw [div_add_div _ _ (ne_of_gt hL) (ne_of_gt hL), div_le_one (by positivity)]; nlinarith))
      (fun j => φ (u j)) (fun j => (r0 + u j) / L)
      (fun j => ⟨by apply div_le_div_of_nonneg_right _ hL.le; linarith [(hu j).1],
        by apply div_le_div_of_nonneg_right _ hL.le; linarith [(hu j).2]⟩)
      (fun j => by rw [hφ _ (hu j), hpar])
    obtain ⟨τm, h1, h2, hm⟩ := hloc
    have hne : Finset.univ.Nonempty := Finset.univ_nonempty_iff.2 ⟨(⟨0, hn⟩ : Fin n)⟩
    obtain ⟨j1, -, hj1⟩ := Finset.exists_mem_eq_inf' hne (fun j => (r0 + u j) / L)
    obtain ⟨j2, -, hj2⟩ := Finset.exists_mem_eq_sup' hne (fun j => (r0 + u j) / L)
    rw [hj1] at h1; rw [hj2] at h2
    refine ⟨τm * L - r0, ⟨?_, ?_⟩, ?_⟩
    · have := (div_le_iff₀ hL).1 h1; linarith [(hu j1).1]
    · have := (le_div_iff₀ hL).1 h2; linarith [(hu j2).2]
    · apply Subtype.ext
      rw [hm, hφ _ ⟨by have := (div_le_iff₀ hL).1 h1; linarith [(hu j1).1],
        by have := (le_div_iff₀ hL).1 h2; linarith [(hu j2).2]⟩, hpar]
      congr 1; field_simp; ring
  obtain ⟨F, hH, hF⟩ := window_gmvs G M hSP hM hn φ (-lm) lm (by linarith) hiso hle
  exact ⟨⟨φ, -lm, lm, F, hH, hiso, hF⟩, rfl, rfl, hφ⟩

end SPFGGeo

-- ===== Geo17 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- shifting a window -/
def Win.shift {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (c : ℝ) : Win G M where
  φ := fun s => W.φ (s + c)
  α := W.α - c
  β := W.β - c
  F := fun u => W.F (fun j => u j + c) - c
  hyp := by
    obtain ⟨hab, hsp, hrange, honto⟩ := W.hyp
    refine ⟨by linarith, ?_, ?_, ?_⟩
    · intro u hu i v hv
      have hu' : SPFGSeg.InA W.α W.β (fun j => u j + c) := fun j => ⟨by linarith [(hu j).1], by linarith [(hu j).2]⟩
      have h := hsp _ hu' i (v + c) ⟨by linarith [hv.1], by linarith [hv.2]⟩
      have e1 : Function.update (fun j => u j + c) i (v + c) = fun j => Function.update u i v j + c := by
        funext j; by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      rw [e1] at h
      rw [show W.F (fun j => u j + c) - (u i + c) = W.F (fun j => u j + c) - c - u i by ring,
        show W.F (fun j => Function.update u i v j + c) - (u i + c) =
          W.F (fun j => Function.update u i v j + c) - c - u i by ring] at h
      exact h
    · intro u hu
      have hu' : SPFGSeg.InA W.α W.β (fun j => u j + c) := fun j => ⟨by linarith [(hu j).1], by linarith [(hu j).2]⟩
      have := hrange _ hu'
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    · intro s hs
      obtain ⟨u, hu, hFu⟩ := honto (s + c) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine ⟨fun j => u j - c, fun j => ⟨by linarith [(hu j).1], by linarith [(hu j).2]⟩, ?_⟩
      simp only [sub_add_cancel]; rw [hFu]; ring
  iso := by
    intro s hs t ht
    rw [W.iso _ ⟨by linarith [hs.1], by linarith [hs.2]⟩ _ ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1; ring
  eq := by
    intro u hu
    have := W.eq (fun j => u j + c) (fun j => ⟨by linarith [(hu j).1], by linarith [(hu j).2]⟩)
    show M (fun j => W.φ (u j + c)) = W.φ (W.F (fun j => u j + c) - c + c)
    rw [sub_add_cancel]; exact this

/-- reversing a window -/
def Win.rev {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) : Win G M where
  φ := fun s => W.φ (-s)
  α := -W.β
  β := -W.α
  F := fun u => -W.F (fun j => -u j)
  hyp := by
    obtain ⟨hab, hsp, hrange, honto⟩ := W.hyp
    refine ⟨by linarith, ?_, ?_, ?_⟩
    · intro u hu i v hv
      have hu' : SPFGSeg.InA W.α W.β (fun j => -u j) := fun j => ⟨by linarith [(hu j).2], by linarith [(hu j).1]⟩
      have h := hsp _ hu' i (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
      have e1 : Function.update (fun j => -u j) i (-v) = fun j => -Function.update u i v j := by
        funext j; by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      rw [e1] at h
      rw [show W.F (fun j => -u j) - -u i = -(-W.F (fun j => -u j) - u i) by ring, abs_neg,
        show W.F (fun j => -Function.update u i v j) - -u i =
          -(-W.F (fun j => -Function.update u i v j) - u i) by ring, abs_neg] at h
      exact h
    · intro u hu
      have hu' : SPFGSeg.InA W.α W.β (fun j => -u j) := fun j => ⟨by linarith [(hu j).2], by linarith [(hu j).1]⟩
      have := hrange _ hu'
      exact ⟨by linarith [this.2], by linarith [this.1]⟩
    · intro s hs
      obtain ⟨u, hu, hFu⟩ := honto (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      refine ⟨fun j => -u j, fun j => ⟨by linarith [(hu j).2], by linarith [(hu j).1]⟩, ?_⟩
      simp only [neg_neg]; rw [hFu]; ring
  iso := by
    intro s hs t ht
    rw [W.iso _ ⟨by linarith [hs.2], by linarith [hs.1]⟩ _ ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    rw [show -s - -t = -(s - t) by ring, abs_neg]
  eq := by
    intro u hu
    have := W.eq (fun j => -u j) (fun j => ⟨by linarith [(hu j).2], by linarith [(hu j).1]⟩)
    show M (fun j => W.φ (-u j)) = W.φ (- -W.F (fun j => -u j))
    rw [this, neg_neg]

/-- a point at distance `r` from one end is at distance `L - r` from the other end -/
lemma rayPt_flip (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) (r : ℝ) :
    rayPt e e.2 r = rayPt e e.1 (elen e - r) := by
  have hL := elen_pos G he
  unfold rayPt rpar
  rw [if_neg (fun h => G.fst_ne_snd e he h.symm), if_pos rfl]
  congr 1; field_simp

lemma rayPt_flip' (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v w : E k}
    (hvw : (v = e.1 ∧ w = e.2) ∨ (v = e.2 ∧ w = e.1)) (r : ℝ) :
    rayPt e w r = rayPt e v (elen e - r) := by
  rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rayPt_flip G he r
  · rw [rayPt_flip G he]; congr 1; ring

end SPFGGeo

-- ===== Geo18 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- a closed non-backtracking loop of edges, indexed periodically by `ℕ` -/
structure Loop (G : MetricGraph k) where
  m : ℕ
  hm : 0 < m
  e : ℕ → E k × E k
  c : ℕ → E k
  per_e : ∀ l, e (l + m) = e l
  per_c : ∀ l, c (l + m) = c l
  he : ∀ l, e l ∈ G.edges
  trav : ∀ l, (c l = (e l).1 ∧ c (l + 1) = (e l).2) ∨ (c l = (e l).2 ∧ c (l + 1) = (e l).1)
  turn : ∀ l, e l ≠ e (l + 1)

namespace Loop

variable {G : MetricGraph k} (Z : Loop G)

/-- cumulative arclength -/
noncomputable def Λ (l : ℕ) : ℝ := ∑ j ∈ Finset.range l, elen (Z.e j)

lemma Λ_succ (l : ℕ) : Z.Λ (l + 1) = Z.Λ l + elen (Z.e l) := Finset.sum_range_succ _ _

lemma Λ_zero : Z.Λ 0 = 0 := by simp [Λ]

lemma Λ_ge (l : ℕ) : l * Lmin G ≤ Z.Λ l := by
  induction l with
  | zero => simp [Λ_zero]
  | succ l ih => rw [Λ_succ]; push_cast; linarith [Lmin_le G (Z.he l)]

lemma Λ_mono {l l' : ℕ} (h : l ≤ l') : Z.Λ l ≤ Z.Λ l' := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih => rw [Λ_succ]; linarith [elen_pos G (Z.he m)]

lemma Λ_lt {l l' : ℕ} (h : l < l') : Z.Λ l < Z.Λ l' := by
  have h1 : Z.Λ (l + 1) ≤ Z.Λ l' := Z.Λ_mono h
  rw [Λ_succ] at h1; linarith [elen_pos G (Z.he l)]

/-- perimeter -/
noncomputable def P : ℝ := Z.Λ Z.m

lemma P_pos : 0 < Z.P := by
  have := Z.Λ_lt Z.hm; rw [Λ_zero] at this; exact this

lemma Λ_add_m (l : ℕ) : Z.Λ (l + Z.m) = Z.Λ l + Z.P := by
  induction l with
  | zero => simp [Λ_zero, P]
  | succ l ih =>
    rw [show l + 1 + Z.m = (l + Z.m) + 1 by ring, Λ_succ, ih, Λ_succ, Z.per_e]; ring

lemma ex_idx (θ : ℝ) : ∃ l, θ < Z.Λ (l + 1) := by
  obtain ⟨l, hl⟩ := exists_nat_gt (θ / Lmin G)
  refine ⟨l, ?_⟩
  have h1 := Z.Λ_ge (l + 1)
  have h2 := Lmin_pos G
  rw [div_lt_iff₀ h2] at hl
  push_cast at h1
  nlinarith

/-- index of the edge containing arclength `θ` -/
noncomputable def idx (θ : ℝ) : ℕ := Nat.find (Z.ex_idx θ)

lemma idx_lt (θ : ℝ) : θ < Z.Λ (Z.idx θ + 1) := Nat.find_spec (Z.ex_idx θ)

lemma idx_ge {θ : ℝ} (hθ : 0 ≤ θ) : Z.Λ (Z.idx θ) ≤ θ := by
  rcases Nat.eq_zero_or_pos (Z.idx θ) with h | h
  · rw [h, Λ_zero]; exact hθ
  · have := Nat.find_min (Z.ex_idx θ) (show Z.idx θ - 1 < Z.idx θ by omega)
    push Not at this
    rwa [show Z.idx θ - 1 + 1 = Z.idx θ by omega] at this

lemma idx_eq {θ : ℝ} {l : ℕ} (h1 : Z.Λ l ≤ θ) (h2 : θ < Z.Λ (l + 1)) : Z.idx θ = l := by
  apply le_antisymm
  · exact Nat.find_min' (Z.ex_idx θ) h2
  · by_contra hc; push Not at hc
    have := Z.idx_lt θ
    have := Z.Λ_mono (show Z.idx θ + 1 ≤ l by omega)
    linarith

/-- arclength parametrization (meaningful for `θ ≥ 0`) -/
noncomputable def γ (θ : ℝ) : E k := rayPt (Z.e (Z.idx θ)) (Z.c (Z.idx θ)) (θ - Z.Λ (Z.idx θ))

lemma other_end (l : ℕ) : rayPt (Z.e l) (Z.c l) (elen (Z.e l)) = Z.c (l + 1) := by
  have he := Z.he l
  rcases Z.trav l with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; unfold rayPt rpar; rw [if_pos rfl, div_self (ne_of_gt (elen_pos G he)), epar_one]
  · rw [h1, h2]; unfold rayPt rpar
    rw [if_neg (fun h => G.fst_ne_snd _ he h.symm), div_self (ne_of_gt (elen_pos G he)), sub_self, epar_zero]

lemma γ_eq {θ : ℝ} {l : ℕ} (h1 : Z.Λ l ≤ θ) (h2 : θ ≤ Z.Λ (l + 1)) :
    Z.γ θ = rayPt (Z.e l) (Z.c l) (θ - Z.Λ l) := by
  rcases lt_or_eq_of_le h2 with h2 | h2
  · unfold γ; rw [Z.idx_eq h1 h2]
  · have hi : Z.idx θ = l + 1 := Z.idx_eq (le_of_eq h2.symm) (by rw [h2]; exact Z.Λ_lt (by omega))
    unfold γ; rw [hi, h2, sub_self]
    have hv : Z.c (l + 1) = (Z.e (l + 1)).1 ∨ Z.c (l + 1) = (Z.e (l + 1)).2 := by
      rcases Z.trav (l + 1) with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    rw [rayPt_zero G (Z.he _) hv, Λ_succ, show Z.Λ l + elen (Z.e l) - Z.Λ l = elen (Z.e l) by ring,
      Z.other_end]

lemma γ_mem {θ : ℝ} (hθ : 0 ≤ θ) : Z.γ θ ∈ G.carrier := by
  have h1 := Z.idx_ge hθ
  have h2 := Z.idx_lt θ
  rw [Z.γ_eq h1 h2.le]
  rw [Λ_succ] at h2
  exact rayPt_mem G (Z.he _) _ (by linarith) (by linarith)

lemma γ_per {θ : ℝ} (hθ : 0 ≤ θ) : Z.γ (θ + Z.P) = Z.γ θ := by
  set l := Z.idx θ
  have h1 := Z.idx_ge hθ
  have h2 := Z.idx_lt θ
  rw [Z.γ_eq h1 h2.le, Z.γ_eq (l := l + Z.m) (by rw [Z.Λ_add_m]; linarith)
    (by rw [show l + Z.m + 1 = (l + 1) + Z.m by ring, Z.Λ_add_m]; linarith), Z.Λ_add_m, Z.per_e, Z.per_c]
  congr 1; ring

end Loop

end SPFGGeo

-- ===== Geo19 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

namespace Loop

variable {G : MetricGraph k} (Z : Loop G)

lemma c_end1 (l : ℕ) : Z.c (l + 1) = (Z.e l).1 ∨ Z.c (l + 1) = (Z.e l).2 := by
  rcases Z.trav l with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr h
  · exact Or.inl h

lemma c_end0 (l : ℕ) : Z.c l = (Z.e l).1 ∨ Z.c l = (Z.e l).2 := by
  rcases Z.trav l with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- the bent window at a junction, aligned with the loop -/
lemma junction_win (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G) (l : ℕ) :
    ∃ W : Win G M, W.α = -α ∧ W.β = α ∧ ∀ s ∈ Set.Icc (-α) α, (W.φ s : E k) = Z.γ (Z.Λ (l + 1) + s) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hαle : ∀ j, α ≤ elen (Z.e j) := fun j => by
    have := Lmin_le G (Z.he j); nlinarith
  obtain ⟨W, hWα, hWβ, hW⟩ := bwin_Win G M hSP hM hn (Z.he l) (Z.he (l + 1)) (Z.turn l)
    (Z.c_end1 l) (Z.c_end0 (l + 1)) hα hαL
  refine ⟨W, hWα, hWβ, fun s hs => ?_⟩
  rw [hW s hs]
  unfold bwin
  split_ifs with h
  · rw [Z.γ_eq (l := l) (by rw [Λ_succ]; linarith [hs.1, hαle l]) (by linarith),
      rayPt_flip' G (Z.he l) (Z.trav l), Λ_succ]
    congr 1; ring
  · rw [Z.γ_eq (l := l + 1) (by linarith) (by rw [Λ_succ (l := l + 1)]; linarith [hs.2, hαle (l + 1)])]
    congr 1; ring

/-- aligned windows along the loop -/
lemma loop_win (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G) (θ : ℝ) (hθ : Z.P ≤ θ) :
    ∃ W : Win G M, W.α ≤ -(α / (8 * (n + 2))) ∧ α / (8 * (n + 2)) ≤ W.β ∧
      ∀ s ∈ Set.Icc (-(α / (8 * (n + 2)))) (α / (8 * (n + 2))), (W.φ s : E k) = Z.γ (θ + s) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  set lm := α / (8 * (n + 2)) with hlm
  have hlm0 : 0 < lm := by positivity
  have hlmα : lm ≤ α / 16 := by
    rw [hlm]; apply div_le_div_of_nonneg_left hα.le (by norm_num); nlinarith
  have hαle : ∀ j, α ≤ elen (Z.e j) := fun j => by
    have := Lmin_le G (Z.he j); nlinarith
  have hθ0 : 0 ≤ θ := le_trans Z.P_pos.le hθ
  have h1 := Z.idx_ge hθ0
  have h2 := Z.idx_lt θ
  set l := Z.idx θ
  have hlm1 : 1 ≤ l := by
    by_contra hc; push Not at hc
    have : l = 0 := by omega
    rw [this] at h2
    have := Z.Λ_mono (show 0 + 1 ≤ Z.m by have := Z.hm; omega)
    unfold P at hθ; linarith
  set r := θ - Z.Λ l
  rw [Λ_succ] at h2
  by_cases hA : r < α / 2
  · -- near the junction at the start of edge `l`
    obtain ⟨W, hWα, hWβ, hW⟩ := Z.junction_win M hSP hM hn hα hαL (l - 1)
    rw [show l - 1 + 1 = l by omega] at hW
    refine ⟨W.shift r, ?_, ?_, fun s hs => ?_⟩
    · show W.α - r ≤ -lm; rw [hWα]; linarith
    · show lm ≤ W.β - r; rw [hWβ]; linarith
    · show (W.φ (s + r) : E k) = _
      rw [hW (s + r) ⟨by linarith [hs.1], by linarith [hs.2]⟩]; congr 1; ring
  · by_cases hB : elen (Z.e l) - α / 2 < r
    · obtain ⟨W, hWα, hWβ, hW⟩ := Z.junction_win M hSP hM hn hα hαL l
      refine ⟨W.shift (r - elen (Z.e l)), ?_, ?_, fun s hs => ?_⟩
      · show W.α - (r - elen (Z.e l)) ≤ -lm; rw [hWα]; linarith
      · show lm ≤ W.β - (r - elen (Z.e l)); rw [hWβ]; linarith
      · show (W.φ (s + (r - elen (Z.e l))) : E k) = _
        rw [hW _ ⟨by linarith [hs.1], by linarith [hs.2]⟩, Λ_succ]; congr 1; ring
    · push Not at hA hB
      have hγ : ∀ s ∈ Set.Icc (-lm) lm, Z.γ (θ + s) = rayPt (Z.e l) (Z.c l) (r + s) := by
        intro s hs
        rw [Z.γ_eq (l := l) (by linarith [hs.1]) (by rw [Λ_succ]; linarith [hs.2])]; congr 1; ring
      have hη : (n + 1) * (2 * lm) < α / 2 - lm := by
        rw [hlm]
        have : (0:ℝ) < n + 2 := by positivity
        rw [show (n + 1) * (2 * (α / (8 * (n + 2)))) = α * (n + 1) / (4 * (n + 2)) by field_simp; ring]
        rw [show α / 2 - α / (8 * (n + 2)) = α * (4 * n + 7) / (8 * (n + 2)) by field_simp; ring]
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos (mul_pos hα this) (show (0:ℝ) < 8 * n + 20 by positivity)]
      rcases Z.c_end0 l with hc | hc
      · obtain ⟨W, hWα, hWβ, hW⟩ := swin_Win G M hSP hM hn (Z.he l) (r0 := r) hlm0 hη
          (by linarith) (by linarith)
        refine ⟨W, by rw [hWα], by rw [hWβ], fun s hs => ?_⟩
        rw [hW s hs, hγ s hs, hc]
      · obtain ⟨W, hWα, hWβ, hW⟩ := swin_Win G M hSP hM hn (Z.he l) (r0 := elen (Z.e l) - r) hlm0 hη
          (by linarith) (by linarith)
        refine ⟨W.rev, ?_, ?_, fun s hs => ?_⟩
        · show -W.β ≤ -lm; rw [hWβ]
        · show lm ≤ -W.α; rw [hWα]; linarith
        · show (W.φ (-s) : E k) = _
          rw [hW (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩, hγ s hs, hc, rayPt_flip G (Z.he l)]
          congr 1; ring

end Loop

end SPFGGeo

-- ===== Geo20 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

lemma Win.lose_mono {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (S : Finset (Fin n))
    {s1 s2 s3 s4 : ℝ} (h1 : W.α ≤ s1) (h12 : s1 < s2) (h2 : s2 ≤ W.β) (h13 : s1 ≤ s3)
    (h34 : s3 < s4) (h4 : s4 ≤ W.β) (hL : Lose M S (W.φ s1) (W.φ s2)) : Lose M S (W.φ s3) (W.φ s4) := by
  have hs1 : s1 ∈ Set.Icc W.α W.β := ⟨h1, by linarith⟩
  have hs2 : s2 ∈ Set.Icc W.α W.β := ⟨by linarith, h2⟩
  have hs3 : s3 ∈ Set.Icc W.α W.β := ⟨by linarith, by linarith⟩
  have hs4 : s4 ∈ Set.Icc W.α W.β := ⟨by linarith, h4⟩
  unfold Lose at hL ⊢
  rw [W.two_eq S hs1 hs2 h12.le] at hL
  have hmem : max s1 (min (SPFGSeg.thr W.F W.α W.β S) s2) ∈ Set.Icc W.α W.β :=
    ⟨le_max_of_le_left h1, max_le (by linarith) (min_le_of_right_le h2)⟩
  have h := W.inj hmem hs1 hL
  have ht : SPFGSeg.thr W.F W.α W.β S ≤ s1 := by
    by_contra hc; push Not at hc
    have : s1 < min (SPFGSeg.thr W.F W.α W.β S) s2 := lt_min hc h12
    have := le_max_right s1 (min (SPFGSeg.thr W.F W.α W.β S) s2)
    linarith
  rw [W.two_eq S hs3 hs4 h34.le, min_eq_left (by linarith), max_eq_left (by linarith)]

namespace Loop

variable {G : MetricGraph k} (Z : Loop G)

/-- the loop as points of `G` -/
noncomputable def γP (θ : ℝ) : G.Pt := ⟨Z.γ (max θ 0), Z.γ_mem (le_max_right _ _)⟩

lemma γP_val {θ : ℝ} (hθ : 0 ≤ θ) : ((Z.γP θ : G.Pt) : E k) = Z.γ θ := by
  simp [γP, max_eq_left hθ]

lemma γP_per {θ : ℝ} (hθ : 0 ≤ θ) : Z.γP (θ + Z.P) = Z.γP θ := by
  apply Subtype.ext
  rw [Z.γP_val (by linarith [Z.P_pos]), Z.γP_val hθ, Z.γ_per hθ]

/-- one propagation step along the loop -/
lemma lose_step (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G) (S : Finset (Fin n))
    {θ ε δ : ℝ} (hθ : Z.P ≤ θ) (hε : 0 < ε) (hδ : 0 ≤ δ) (hεδ : δ + ε ≤ α / (8 * (n + 2)))
    (hL : Lose M S (Z.γP θ) (Z.γP (θ + ε))) : Lose M S (Z.γP (θ + δ)) (Z.γP (θ + δ + ε)) := by
  obtain ⟨W, hWα, hWβ, hW⟩ := Z.loop_win M hSP hM hn hα hαL θ hθ
  set lm := α / (8 * (n + 2)) with hlm
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlmP : lm ≤ Z.P := by
    have h1 : (Z.m : ℝ) * Lmin G ≤ Z.P := Z.Λ_ge Z.m
    have h2 : (1:ℝ) ≤ Z.m := by exact_mod_cast Z.hm
    have h3 := Lmin_pos G
    have h4 : lm ≤ α := by rw [hlm]; apply div_le_self hα.le; nlinarith
    nlinarith
  have hθ0 : 0 ≤ θ := le_trans Z.P_pos.le hθ
  have hφ : ∀ s ∈ Set.Icc (-lm) lm, W.φ s = Z.γP (θ + s) := fun s hs =>
    Subtype.ext (by rw [hW s hs, Z.γP_val (by linarith [hs.1])])
  have hlm0 : 0 < lm := by positivity
  have e0 := hφ 0 ⟨by linarith, by linarith⟩
  have e1 := hφ ε ⟨by linarith, by linarith⟩
  have e2 := hφ δ ⟨by linarith, by linarith⟩
  have e3 := hφ (δ + ε) ⟨by linarith, by linarith⟩
  rw [add_zero] at e0
  rw [← e0, ← e1] at hL
  rw [← e2, show θ + δ + ε = θ + (δ + ε) by ring, ← e3]
  exact W.lose_mono S (by linarith) hε (by linarith) hδ (by linarith) (by linarith) hL

/-- iterated propagation -/
lemma lose_iter (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G) (S : Finset (Fin n))
    {θ ε δ : ℝ} (hθ : Z.P ≤ θ) (hε : 0 < ε) (hδ : 0 ≤ δ) (hεδ : δ + ε ≤ α / (8 * (n + 2)))
    (hL : Lose M S (Z.γP θ) (Z.γP (θ + ε))) :
    ∀ K : ℕ, Lose M S (Z.γP (θ + K * δ)) (Z.γP (θ + K * δ + ε)) := by
  intro K
  induction K with
  | zero => simpa using hL
  | succ K ih =>
    have := Z.lose_step M hSP hM hn hα hαL S (θ := θ + K * δ) (by nlinarith) hε hδ hεδ ih
    push_cast
    rwa [show θ + K * δ + δ = θ + (K + 1) * δ by ring] at this

/-- **No threshold on a loop.** -/
lemma no_threshold (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hαL : 4 * (n + 1) * α ≤ Lmin G) (S : Finset (Fin n))
    {θq ε : ℝ} (hθ : Z.P ≤ θq) (hε : 0 < ε) (hε2 : 2 * ε ≤ α / (8 * (n + 2))) (hεP : 3 * ε < Z.P)
    (hA : Lose M S (Z.γP (θq + ε)) (Z.γP (θq + 2 * ε)))
    (hB : ¬ Lose M S (Z.γP (θq + Z.P - 2 * ε)) (Z.γP (θq + Z.P - ε))) : False := by
  set lm := α / (8 * (n + 2))
  set D := Z.P - 3 * ε with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * D / lm)
  have hlm0 : 0 < lm := by positivity
  have hK0 : (0:ℝ) < K := lt_of_le_of_lt (by positivity) hK
  set δ := D / K with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδle : δ ≤ lm / 2 := by
    rw [hδdef, div_le_iff₀ hK0]
    rw [div_lt_iff₀ hlm0] at hK; nlinarith
  have := Z.lose_iter M hSP hM hn hα hαL S (θ := θq + ε) (by linarith) hε hδ0 (by linarith)
    (by rw [show θq + ε + ε = θq + 2 * ε by ring]; exact hA) K
  rw [show (K : ℝ) * δ = D by rw [hδdef]; field_simp] at this
  rw [show θq + ε + D = θq + Z.P - 2 * ε by rw [hD]; ring,
    show θq + Z.P - 2 * ε + ε = θq + Z.P - ε by ring] at this
  exact hB this

end Loop

end SPFGGeo

-- ===== Geo21 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- point at distance `s` from `q` in the direction of `w` -/
noncomputable def qray (q w : E k) (s : ℝ) : E k := q + (s / ‖w - q‖) • (w - q)

/-- loops through any two distinct rays at any point -/
def LoopRich (G : MetricGraph k) : Prop :=
  ∀ (q : E k) (e1 e2 : E k × E k), e1 ∈ G.edges → e2 ∈ G.edges → ∀ w1 w2 : E k,
    (w1 = e1.1 ∨ w1 = e1.2) → (w2 = e2.1 ∨ w2 = e2.2) → q ∈ segment ℝ e1.1 e1.2 →
    q ∈ segment ℝ e2.1 e2.2 → w1 ≠ q → w2 ≠ q → (e1, w1) ≠ (e2, w2) →
    ∃ Z : Loop G, ∃ θq, Z.P ≤ θq ∧ ∃ δ > 0, ∀ s ∈ Set.Icc 0 δ,
      Z.γ (θq - s) = qray q w1 s ∧ Z.γ (θq + s) = qray q w2 s

lemma epar_qray (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {tx tw θ : ℝ}
    (htx : tx ∈ Set.Icc (0:ℝ) 1) (htw : tw ∈ Set.Icc (0:ℝ) 1) (hne : tw ≠ tx) :
    epar e (tx + θ * (tw - tx)) =
      qray (epar e tx) (if tx < tw then e.2 else e.1) (θ * |tw - tx| * elen e) := by
  have hL := elen_pos G he
  unfold qray elen at *
  split_ifs with h
  · have h1 : e.2 - epar e tx = (1 - tx) • (e.2 - e.1) := by simp only [epar]; module
    have h2 : (0:ℝ) < 1 - tx := by linarith [htw.2]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos h2, abs_of_pos (by linarith : (0:ℝ) < tw - tx)]
    simp only [epar, smul_smul]
    rw [add_assoc, ← add_smul]; congr 2; field_simp
  · have hlt : tw < tx := lt_of_le_of_ne (not_lt.1 h) hne
    have h1 : e.1 - epar e tx = (-tx) • (e.2 - e.1) := by simp only [epar]; module
    have h2 : (0:ℝ) < tx := by linarith [htw.1]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos h2, abs_of_neg (by linarith : tw - tx < 0)]
    simp only [epar, smul_smul]
    rw [add_assoc, ← add_smul]; congr 2; field_simp

lemma qray_zero (q w : E k) : qray q w 0 = q := by simp [qray]

lemma norm_qray_sub {q w : E k} (hqw : w ≠ q) (s s' : ℝ) :
    ‖qray q w s - qray q w s'‖ = |s - s'| := by
  have h : 0 < ‖w - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hqw)
  simp only [qray, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
  rw [← sub_div, abs_div, abs_of_pos h, div_mul_cancel₀ _ (ne_of_gt h)]

lemma qray_mem_seg {e : E k × E k} {q w : E k} (hq : q ∈ segment ℝ e.1 e.2)
    (hw : w ∈ segment ℝ e.1 e.2) (hqw : w ≠ q) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ ‖w - q‖) :
    qray q w s ∈ segment ℝ e.1 e.2 := by
  have h : 0 < ‖w - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hqw)
  apply (convex_segment e.1 e.2).add_smul_sub_mem hq hw
  exact ⟨div_nonneg hs0 h.le, (div_le_one h).2 hs⟩

/-- moving one agent toward the outcome along a given last edge keeps the outcome -/
lemma move_one (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M) (x : Profile G n)
    (j : Fin n) {e : E k × E k} (he : e ∈ G.edges) {tx tw : ℝ} (htx : tx ∈ Set.Icc (0:ℝ) 1)
    (htw : tw ∈ Set.Icc (0:ℝ) 1) (hne : tw ≠ tx) (hm : ((M x : G.Pt) : E k) = epar e tx)
    (hseg : ∀ (P : G.Pt) (t : ℝ), t ∈ Set.uIcc tx tw → (P : E k) = epar e t →
      G.dist (x j) P + G.dist P (M x) = G.dist (x j) (M x))
    (hxm : x j ≠ M x) (B : ℝ) (hB : 0 < B) :
    ∃ θ : ℝ, 0 < θ ∧ θ * |tw - tx| * elen e ≤ B ∧ ∃ P : G.Pt,
      (P : E k) = epar e (tx + θ * (tw - tx)) ∧ M (Function.update x j P) = M x := by
  have hL := elen_pos G he
  have hdpos : 0 < G.dist (x j) (M x) := by
    rcases (dist_nonneg G (x j) (M x)).lt_or_eq with h | h
    · exact h
    · exact absurd (eq_of_dist_eq_zero G _ _ h.symm) hxm
  set D := |tw - tx| * elen e with hDdef
  have hD0 : 0 ≤ D := mul_nonneg (abs_nonneg _) hL.le
  set θ := min (1/3) (min (B / (D + 1)) (G.dist (x j) (M x) / (3 * D + 1))) with hθ
  have hθpos : 0 < θ := lt_min (by norm_num) (lt_min (div_pos hB (by positivity)) (div_pos hdpos (by positivity)))
  have hθ3 : θ ≤ 1/3 := min_le_left _ _
  have hθB : θ * D ≤ B := by
    have h1 : θ ≤ B / (D + 1) := (min_le_right _ _).trans (min_le_left _ _)
    calc θ * D ≤ B / (D + 1) * D := by gcongr
      _ ≤ B / (D + 1) * (D + 1) := by gcongr; linarith
      _ = B := div_mul_cancel₀ _ (by linarith)
  have hθd : 3 * (θ * D) ≤ G.dist (x j) (M x) := by
    have h1 : θ ≤ G.dist (x j) (M x) / (3 * D + 1) := (min_le_right _ _).trans (min_le_right _ _)
    calc 3 * (θ * D) = θ * (3 * D) := by ring
      _ ≤ θ * (3 * D + 1) := by nlinarith
      _ ≤ G.dist (x j) (M x) / (3 * D + 1) * (3 * D + 1) := by gcongr
      _ = G.dist (x j) (M x) := div_mul_cancel₀ _ (by linarith)
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
  have ht'I := huI _ (hmem θ hθpos.le (by linarith))
  let P : G.Pt := ⟨epar e (tx + θ * (tw - tx)), Set.mem_biUnion he (epar_mem ht'I)⟩
  have hPne : tx + θ * (tw - tx) ≠ tx := by
    intro h
    have : θ * (tw - tx) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact hne (by linarith)
  have hPm : G.dist P (M x) = θ * D := by
    rw [dist_epar G e he P (M x) ht'I htx rfl hm]
    rw [show tx + θ * (tw - tx) - tx = θ * (tw - tx) by ring, abs_mul, abs_of_pos hθpos, hDdef]
    unfold elen; ring
  have hs : tx + 3 * (tx + θ * (tw - tx) - tx) ∈ Set.Icc (0:ℝ) 1 := by
    rw [show tx + 3 * (tx + θ * (tw - tx) - tx) = tx + (3 * θ) * (tw - tx) by ring]
    exact huI _ (hmem _ (by linarith) (by linarith))
  refine ⟨θ, hθpos, by rw [mul_assoc]; exact hθB, P, rfl, ?_⟩
  exact lemma1 G M hSP x j P e he tx _ htx hs hm rfl hPne
    (hseg P _ (hmem θ hθpos.le (by linarith)) rfl) (by rw [hPm]; exact hθd)

end SPFGGeo

-- ===== Geo22 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

/-- direction endpoint from parameters -/
noncomputable def wdir (e : E k × E k) (tx tw : ℝ) : E k := if tx < tw then e.2 else e.1

lemma wdir_end (e : E k × E k) (tx tw : ℝ) : wdir e tx tw = e.1 ∨ wdir e tx tw = e.2 := by
  unfold wdir; split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma wdir_ne (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {tx tw : ℝ}
    (htw : tw ∈ Set.Icc (0:ℝ) 1) (hne : tw ≠ tx) : wdir e tx tw ≠ epar e tx := by
  have hne' := G.fst_ne_snd e he
  unfold wdir; split_ifs with h
  · intro h'; rw [← epar_one e] at h'; have := epar_inj hne' h'; linarith [htw.2]
  · intro h'; rw [← epar_zero e] at h'; have := epar_inj hne' h'
    have : tw < tx := lt_of_le_of_ne (not_lt.1 h) hne
    linarith [htw.1]

/-- **Peak selection for two agents** on loop-rich graphs. -/
theorem peak2 (G : MetricGraph k) (hLR : LoopRich G) (M : Profile G 2 → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (x : Profile G 2) : M x = x 0 ∨ M x = x 1 := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨h0, h1⟩ := hc
  set m := M x with hmdef
  obtain ⟨e0, he0, tx0, tw0, htx0, htw0, hne0, hm0, hseg0⟩ := near_geo G (x 0) m (Ne.symm h0)
  obtain ⟨e1, he1, tx1, tw1, htx1, htw1, hne1, hm1, hseg1⟩ := near_geo G (x 1) m (Ne.symm h1)
  set w0 := wdir e0 tx0 tw0
  set w1 := wdir e1 tx1 tw1
  have hmseg0 : (m : E k) ∈ segment ℝ e0.1 e0.2 := hm0 ▸ epar_mem htx0
  have hmseg1 : (m : E k) ∈ segment ℝ e1.1 e1.2 := hm1 ▸ epar_mem htx1
  have hw0m : w0 ≠ m := by rw [hm0]; exact wdir_ne G he0 htw0 hne0
  have hw1m : w1 ≠ m := by rw [hm1]; exact wdir_ne G he1 htw1 hne1
  -- a general moving step producing points `qray m w d`
  have hmove : ∀ B > 0, ∃ d0 d1 : ℝ, 0 < d0 ∧ d0 ≤ B ∧ 0 < d1 ∧ d1 ≤ B ∧ ∃ P0 P1 : G.Pt,
      (P0 : E k) = qray m w0 d0 ∧ (P1 : E k) = qray m w1 d1 ∧
      M (Function.update (Function.update x 0 P0) 1 P1) = m := by
    intro B hB
    obtain ⟨θ0, hθ0, hθ0B, P0, hP0, hM0⟩ := move_one G M hSP x 0 he0 htx0 htw0 hne0 hm0 hseg0
      (Ne.symm h0) B hB
    set x' := Function.update x 0 P0
    have hx'1 : x' 1 = x 1 := by simp [x']
    have hseg1' : ∀ (P : G.Pt) (t : ℝ), t ∈ Set.uIcc tx1 tw1 → (P : E k) = epar e1 t →
        G.dist (x' 1) P + G.dist P (M x') = G.dist (x' 1) (M x') := by
      rw [hx'1, hM0]; exact hseg1
    obtain ⟨θ1, hθ1, hθ1B, P1, hP1, hM1⟩ := move_one G M hSP x' 1 he1 htx1 htw1 hne1
      (by rw [hM0]; exact hm1) hseg1' (by rw [hx'1, hM0]; exact Ne.symm h1) B hB
    refine ⟨θ0 * |tw0 - tx0| * elen e0, θ1 * |tw1 - tx1| * elen e1,
      by have := elen_pos G he0; have := abs_pos.2 (sub_ne_zero.2 hne0); positivity, hθ0B,
      by have := elen_pos G he1; have := abs_pos.2 (sub_ne_zero.2 hne1); positivity, hθ1B,
      P0, P1, ?_, ?_, ?_⟩
    · rw [hP0, epar_qray G he0 htx0 htw0 hne0, ← hm0]; rfl
    · rw [hP1, epar_qray G he1 htx1 htw1 hne1, ← hm1]; rfl
    · rw [hM1, hM0]
  have hd : ∀ (w : E k) (e : E k × E k), e ∈ G.edges → w ∈ segment ℝ e.1 e.2 →
      (m : E k) ∈ segment ℝ e.1 e.2 → w ≠ m → ∀ (P Q : G.Pt) (s s' : ℝ), 0 ≤ s → s ≤ ‖w - m‖ →
      0 ≤ s' → s' ≤ ‖w - m‖ → (P : E k) = qray m w s → (Q : E k) = qray m w s' →
      G.dist P Q = |s - s'| := by
    intro w e he hw hme hwm P Q s s' hs0 hs hs0' hs' hP hQ
    rw [dist_eq_norm_of_edge G P Q e he (hP ▸ qray_mem_seg hme hw hwm hs0 hs)
      (hQ ▸ qray_mem_seg hme hw hwm hs0' hs'), hP, hQ, norm_qray_sub hwm]
  have hw0seg : w0 ∈ segment ℝ e0.1 e0.2 := by
    rcases wdir_end e0 tx0 tw0 with h | h <;> rw [show w0 = wdir e0 tx0 tw0 from rfl, h]
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hw1seg : w1 ∈ segment ℝ e1.1 e1.2 := by
    rcases wdir_end e1 tx1 tw1 with h | h <;> rw [show w1 = wdir e1 tx1 tw1 from rfl, h]
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hn2 : (0:ℕ) < 2 := by norm_num
  by_cases hray : (e0, w0) = (e1, w1)
  · -- same ray: contradiction with Lemma 2
    obtain ⟨he01, hw01⟩ := Prod.mk.inj hray
    set B := min ‖w0 - m‖ 1
    have hB : 0 < B := lt_min (norm_pos_iff.2 (sub_ne_zero.2 hw0m)) one_pos
    obtain ⟨d0, d1, hd0, hd0B, hd1, hd1B, P0, P1, hP0, hP1, hMy⟩ := hmove B hB
    rw [← hw01] at hP1
    have hBw : B ≤ ‖w0 - m‖ := min_le_left _ _
    set y := Function.update (Function.update x 0 P0) 1 P1
    have hy0 : y 0 = P0 := by simp [y]
    have hy1 : y 1 = P1 := by simp [y]
    let mP : G.Pt := m
    have hmq : (m : E k) = qray m w0 0 := (qray_zero _ _).symm
    rcases le_total d0 d1 with hle | hle
    · apply lemma2 G M hSP hM y P0
      · rw [hMy]; intro h; rw [h] at hP0
        have := norm_qray_sub hw0m d0 0
        rw [← hP0, qray_zero, sub_self, norm_zero, sub_zero, abs_of_pos hd0] at this; linarith
      · intro j; rw [hMy]
        fin_cases j
        · simp only [Fin.zero_eta, hy0]
          rw [dist_self, zero_add]
        · simp only [Fin.mk_one, hy1]
          rw [hd w0 e0 he0 hw0seg hmseg0 hw0m P1 P0 d1 d0 hd1.le (by linarith) hd0.le (by linarith) hP1 hP0,
            hd w0 e0 he0 hw0seg hmseg0 hw0m P0 m d0 0 hd0.le (by linarith) le_rfl
              (norm_nonneg _) hP0 hmq,
            hd w0 e0 he0 hw0seg hmseg0 hw0m P1 m d1 0 hd1.le (by linarith) le_rfl
              (norm_nonneg _) hP1 hmq]
          rw [sub_zero, sub_zero, abs_of_nonneg (by linarith), abs_of_pos hd0, abs_of_pos hd1]; ring
    · apply lemma2 G M hSP hM y P1
      · rw [hMy]; intro h; rw [h] at hP1
        have := norm_qray_sub hw0m d1 0
        rw [← hP1, qray_zero, sub_self, norm_zero, sub_zero, abs_of_pos hd1] at this; linarith
      · intro j; rw [hMy]
        fin_cases j
        · simp only [Fin.zero_eta, hy0]
          rw [hd w0 e0 he0 hw0seg hmseg0 hw0m P0 P1 d0 d1 hd0.le (by linarith) hd1.le (by linarith) hP0 hP1,
            hd w0 e0 he0 hw0seg hmseg0 hw0m P1 m d1 0 hd1.le (by linarith) le_rfl
              (norm_nonneg _) hP1 hmq,
            hd w0 e0 he0 hw0seg hmseg0 hw0m P0 m d0 0 hd0.le (by linarith) le_rfl
              (norm_nonneg _) hP0 hmq]
          rw [sub_zero, sub_zero, abs_of_nonneg (by linarith), abs_of_pos hd0, abs_of_pos hd1]; ring
        · simp only [Fin.mk_one, hy1]
          rw [dist_self, zero_add]
  · -- distinct rays: a loop through them
    obtain ⟨Z, θq, hθq, δ, hδ, hγ⟩ := hLR m e0 e1 he0 he1 w0 w1 (wdir_end e0 tx0 tw0)
      (wdir_end e1 tx1 tw1) hmseg0 hmseg1 hw0m hw1m hray
    set α := Lmin G / 12 with hαdef
    have hα : 0 < α := by have := Lmin_pos G; positivity
    have hαL : 4 * ((2:ℕ) + 1 : ℝ) * α ≤ Lmin G := by rw [hαdef]; push_cast; linarith
    set lm := α / (8 * ((2:ℕ) + 2 : ℝ)) with hlm
    have hlm0 : 0 < lm := by positivity
    obtain ⟨W, hWα, hWβ, hW⟩ := Z.loop_win M hSP hM hn2 hα hαL θq hθq
    set B := min δ lm
    have hB : 0 < B := lt_min hδ hlm0
    obtain ⟨d0, d1, hd0, hd0B, hd1, hd1B, P0, P1, hP0, hP1, hMy⟩ := hmove B hB
    have hd0δ : d0 ≤ δ := hd0B.trans (min_le_left _ _)
    have hd1δ : d1 ≤ δ := hd1B.trans (min_le_left _ _)
    have hd0l : d0 ≤ lm := hd0B.trans (min_le_right _ _)
    have hd1l : d1 ≤ lm := hd1B.trans (min_le_right _ _)
    have hθ0 : 0 ≤ θq := le_trans Z.P_pos.le hθq
    have hlmP : lm ≤ Z.P := by
      have h1 : (Z.m : ℝ) * Lmin G ≤ Z.P := Z.Λ_ge Z.m
      have h2 : (1:ℝ) ≤ Z.m := by exact_mod_cast Z.hm
      have h3 := Lmin_pos G
      have h4 : lm ≤ α := by rw [hlm]; apply div_le_self hα.le; push_cast; norm_num
      nlinarith
    have hWγ : ∀ s ∈ Set.Icc (-lm) lm, W.φ s = Z.γP (θq + s) := fun s hs =>
      Subtype.ext (by rw [hW s hs, Z.γP_val (by linarith [hs.1])])
    have hφ0 : W.φ (-d0) = P0 := by
      apply Subtype.ext; rw [hW (-d0) ⟨by linarith, by linarith⟩, hP0, ← sub_eq_add_neg]
      exact (hγ d0 ⟨hd0.le, hd0δ⟩).1
    have hφ1 : W.φ d1 = P1 := by
      apply Subtype.ext; rw [hW d1 ⟨by linarith, by linarith⟩, hP1]
      exact (hγ d1 ⟨hd1.le, hd1δ⟩).2
    have hφm : W.φ 0 = m := by
      apply Subtype.ext; rw [hW 0 ⟨by linarith, by linarith⟩]
      have := (hγ 0 ⟨le_rfl, hδ.le⟩).2
      rw [qray_zero] at this; exact this
    have hy : Function.update (Function.update x 0 P0) 1 P1 = two {1} (W.φ (-d0)) (W.φ d1) := by
      funext j; fin_cases j <;> simp [two, hφ0, hφ1]
    rw [hy] at hMy
    have hs0 : -d0 ∈ Set.Icc W.α W.β := ⟨by linarith, by linarith⟩
    have hs1 : d1 ∈ Set.Icc W.α W.β := ⟨by linarith, by linarith⟩
    rw [W.two_eq {1} hs0 hs1 (by linarith), ← hφm] at hMy
    have hmem : max (-d0) (min (SPFGSeg.thr W.F W.α W.β {1}) d1) ∈ Set.Icc W.α W.β :=
      ⟨le_max_of_le_left hs0.1, max_le hs0.2 (min_le_of_right_le hs1.2)⟩
    have hz := W.inj hmem ⟨by linarith, by linarith⟩ hMy
    have hthr : SPFGSeg.thr W.F W.α W.β {1} = 0 := by
      have hmin : min (SPFGSeg.thr W.F W.α W.β {1}) d1 = 0 := by
        rcases le_total (-d0) (min (SPFGSeg.thr W.F W.α W.β {1}) d1) with h | h
        · rw [max_eq_right h] at hz; exact hz
        · rw [max_eq_left h] at hz; linarith
      rcases le_total (SPFGSeg.thr W.F W.α W.β {1}) d1 with h | h
      · rw [min_eq_left h] at hmin; exact hmin
      · rw [min_eq_right h] at hmin; linarith
    set ε := lm / 4 with hε
    have hε0 : 0 < ε := by positivity
    have hA := W.thr_lose {1} (s1 := ε) (s2 := 2 * ε) (by rw [hthr]; exact hε0) (by linarith) (by linarith)
    have hB' := W.thr_notlose {1} (s1 := -(2 * ε)) (s2 := -ε) (by linarith) (by linarith) (by rw [hthr]; linarith)
    rw [hWγ ε ⟨by linarith, by linarith⟩, hWγ (2 * ε) ⟨by linarith, by linarith⟩] at hA
    rw [hWγ (-(2 * ε)) ⟨by linarith, by linarith⟩, hWγ (-ε) ⟨by linarith, by linarith⟩] at hB'
    rw [← Z.γP_per (θ := θq + -(2 * ε)) (by linarith), ← Z.γP_per (θ := θq + -ε) (by linarith)] at hB'
    rw [show θq + -(2 * ε) + Z.P = θq + Z.P - 2 * ε by ring, show θq + -ε + Z.P = θq + Z.P - ε by ring] at hB'
    exact Z.no_threshold M hSP hM hn2 hα hαL {1} hθq hε0 (by linarith) (by linarith) hA hB'

end SPFGGeo

-- ===== Geo23 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

lemma Win.lose_iff_thr {G : MetricGraph k} {M : Profile G n → G.Pt} (W : Win G M) (S : Finset (Fin n))
    {s s' : ℝ} (hs : W.α ≤ s) (hss' : s < s') (hs' : s' ≤ W.β) :
    Lose M S (W.φ s) (W.φ s') ↔ SPFGSeg.thr W.F W.α W.β S ≤ s := by
  have hsm : s ∈ Set.Icc W.α W.β := ⟨hs, by linarith⟩
  have hs'm : s' ∈ Set.Icc W.α W.β := ⟨by linarith, hs'⟩
  unfold Lose
  rw [W.two_eq S hsm hs'm hss'.le]
  have hmem : max s (min (SPFGSeg.thr W.F W.α W.β S) s') ∈ Set.Icc W.α W.β :=
    ⟨le_max_of_le_left hs, max_le hsm.2 (min_le_of_right_le hs')⟩
  constructor
  · intro h
    have h2 := W.inj hmem hsm h
    by_contra hc; push Not at hc
    have : min (SPFGSeg.thr W.F W.α W.β S) s' > s := lt_min hc hss'
    have := le_max_right s (min (SPFGSeg.thr W.F W.α W.β S) s')
    linarith
  · intro h
    rw [min_eq_left (by linarith), max_eq_left h]

/-- the two-agent profile `(a, b)` -/
def pr {G : MetricGraph k} (a b : G.Pt) : Profile G 2 := fun j => if j = 0 then a else b

lemma two1 {G : MetricGraph k} (p p' : G.Pt) : two ({1} : Finset (Fin 2)) p p' = pr p p' := by
  funext j; fin_cases j <;> simp [two, pr]

lemma two0 {G : MetricGraph k} (p p' : G.Pt) : two ({0} : Finset (Fin 2)) p p' = pr p' p := by
  funext j; fin_cases j <;> simp [two, pr]

/-- with peak selection, losing is uniform on a window -/
lemma Win.lose_unif {G : MetricGraph k} {M : Profile G 2 → G.Pt} (W : Win G M)
    (hps : ∀ x : Profile G 2, M x = x 0 ∨ M x = x 1) (S : Finset (Fin 2)) {a b : ℝ}
    (ha : W.α ≤ a) (hab : a < b) (hb : b ≤ W.β)
    {s1 s2 : ℝ} (h1 : a ≤ s1) (h12 : s1 < s2) (h2 : s2 ≤ b) :
    Lose M S (W.φ s1) (W.φ s2) ↔ Lose M S (W.φ a) (W.φ b) := by
  rw [W.lose_iff_thr S (by linarith) h12 (by linarith), W.lose_iff_thr S ha hab hb]
  set t := SPFGSeg.thr W.F W.α W.β S
  have ham : a ∈ Set.Icc W.α W.β := ⟨ha, by linarith⟩
  have hbm : b ∈ Set.Icc W.α W.β := ⟨by linarith, hb⟩
  have hmem : max a (min t b) ∈ Set.Icc W.α W.β :=
    ⟨le_max_of_le_left ha, max_le ham.2 (min_le_of_right_le hb)⟩
  have hdich : t ≤ a ∨ b ≤ t := by
    have hp := hps (two S (W.φ a) (W.φ b))
    rw [W.two_eq S ham hbm hab.le] at hp
    have hab' : max a (min t b) = a ∨ max a (min t b) = b := by
      rcases hp with hp | hp <;> simp only [two] at hp <;> split_ifs at hp
      · exact Or.inr (W.inj hmem hbm hp)
      · exact Or.inl (W.inj hmem ham hp)
      · exact Or.inr (W.inj hmem hbm hp)
      · exact Or.inl (W.inj hmem ham hp)
    rcases hab' with h | h
    · left; by_contra hc; push Not at hc
      have : min t b > a := lt_min hc hab
      have := le_max_right a (min t b); linarith
    · right; by_contra hc; push Not at hc
      have h3 : min t b < b := min_lt_of_left_lt hc
      have h4 : max a (min t b) < b := max_lt hab h3
      linarith
  constructor
  · intro h; rcases hdich with hd | hd
    · exact hd
    · linarith
  · intro h; linarith

namespace Loop

variable {G : MetricGraph k} (Z : Loop G)

/-- the window radius used for two agents -/
noncomputable def lm2 (G : MetricGraph k) : ℝ := Lmin G / 12 / (8 * ((2:ℕ) + 2 : ℝ))

lemma lm2_pos (G : MetricGraph k) : 0 < lm2 G := by
  unfold lm2; have := Lmin_pos G; positivity

lemma lm2_le_P : lm2 G ≤ Z.P := by
  have h1 : (Z.m : ℝ) * Lmin G ≤ Z.P := Z.Λ_ge Z.m
  have h2 : (1:ℝ) ≤ Z.m := by exact_mod_cast Z.hm
  have h3 := Lmin_pos G
  have h4 : lm2 G ≤ Lmin G := by
    unfold lm2; rw [div_div]; apply div_le_self h3.le; push_cast; norm_num
  nlinarith

lemma lwin (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (θ : ℝ) (hθ : Z.P ≤ θ) :
    ∃ W : Win G M, W.α ≤ -lm2 G ∧ lm2 G ≤ W.β ∧
      ∀ s ∈ Set.Icc (-lm2 G) (lm2 G), W.φ s = Z.γP (θ + s) := by
  have hα : 0 < Lmin G / 12 := by have := Lmin_pos G; positivity
  have hαL : 4 * ((2:ℕ) + 1 : ℝ) * (Lmin G / 12) ≤ Lmin G := by push_cast; linarith
  obtain ⟨W, hWα, hWβ, hW⟩ := Z.loop_win M hSP hM (by norm_num) hα hαL θ hθ
  refine ⟨W, hWα, hWβ, fun s hs => Subtype.ext ?_⟩
  have := Z.lm2_le_P
  rw [hW s hs, Z.γP_val (by linarith [hs.1])]

/-- canonical losing predicate at arclength `θ` -/
def L0 (M : Profile G 2 → G.Pt) (S : Finset (Fin 2)) (θ : ℝ) : Prop :=
  Lose M S (Z.γP θ) (Z.γP (θ + lm2 G / 2))

lemma lose_iff_L0 (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hps : ∀ x : Profile G 2, M x = x 0 ∨ M x = x 1) (S : Finset (Fin 2))
    {θ ε : ℝ} (hθ : Z.P ≤ θ) (hε : 0 < ε) (hε' : ε ≤ lm2 G) :
    Lose M S (Z.γP θ) (Z.γP (θ + ε)) ↔ Z.L0 M S θ := by
  have hl := lm2_pos G
  obtain ⟨W, hWα, hWβ, hW⟩ := Z.lwin M hSP hM (θ + lm2 G / 2) (by linarith)
  have e1 : Z.γP θ = W.φ (-(lm2 G / 2)) := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  have e2 : Z.γP (θ + ε) = W.φ (ε - lm2 G / 2) := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  have e3 : Z.γP (θ + lm2 G / 2) = W.φ 0 := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  unfold L0
  rw [e1, e2, e3, W.lose_unif hps S (a := -lm2 G) (b := lm2 G) (s1 := -(lm2 G / 2))
    (s2 := ε - lm2 G / 2) hWα (by linarith) hWβ (by linarith) (by linarith) (by linarith),
    W.lose_unif hps S (a := -lm2 G) (b := lm2 G) (s1 := -(lm2 G / 2)) (s2 := 0) hWα (by linarith) hWβ
    (by linarith) (by linarith) (by linarith)]

lemma L0_step (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hps : ∀ x : Profile G 2, M x = x 0 ∨ M x = x 1) (S : Finset (Fin 2))
    {θ δ : ℝ} (hθ : Z.P ≤ θ) (hδ : 0 ≤ δ) (hδ' : δ ≤ lm2 G / 2) :
    Z.L0 M S θ ↔ Z.L0 M S (θ + δ) := by
  have hl := lm2_pos G
  obtain ⟨W, hWα, hWβ, hW⟩ := Z.lwin M hSP hM (θ + lm2 G / 2) (by linarith)
  have e1 : Z.γP θ = W.φ (-(lm2 G / 2)) := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  have e3 : Z.γP (θ + lm2 G / 2) = W.φ 0 := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  have e4 : Z.γP (θ + δ) = W.φ (δ - lm2 G / 2) := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  have e5 : Z.γP (θ + δ + lm2 G / 2) = W.φ δ := by
    rw [hW _ ⟨by linarith, by linarith⟩]; congr 1; ring
  unfold L0
  rw [e1, e3, e4, e5, W.lose_unif hps S (a := -lm2 G) (b := lm2 G) (s1 := -(lm2 G / 2)) (s2 := 0)
    hWα (by linarith) hWβ (by linarith) (by linarith) (by linarith),
    W.lose_unif hps S (a := -lm2 G) (b := lm2 G) (s1 := δ - lm2 G / 2) (s2 := δ) hWα (by linarith) hWβ
    (by linarith) (by linarith) (by linarith)]

lemma L0_const (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hps : ∀ x : Profile G 2, M x = x 0 ∨ M x = x 1) (S : Finset (Fin 2))
    {θ : ℝ} (hθ : Z.P ≤ θ) : Z.L0 M S θ ↔ Z.L0 M S Z.P := by
  have hl := lm2_pos G
  obtain ⟨K, hK⟩ := exists_nat_gt ((θ - Z.P) / (lm2 G / 2))
  have hK0 : (0:ℝ) < K := lt_of_le_of_lt (div_nonneg (by linarith) (by linarith)) hK
  set δ := (θ - Z.P) / K
  have hδ : 0 ≤ δ := div_nonneg (by linarith) hK0.le
  have hδ' : δ ≤ lm2 G / 2 := by
    rw [div_le_iff₀ hK0]; rw [div_lt_iff₀ (by linarith)] at hK; nlinarith
  have key : ∀ j : ℕ, Z.L0 M S Z.P ↔ Z.L0 M S (Z.P + j * δ) := by
    intro j; induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, Z.L0_step M hSP hM hps S (θ := Z.P + j * δ) (δ := δ)
        (by nlinarith) hδ hδ']
      push_cast; rw [show Z.P + (j + 1) * δ = Z.P + j * δ + δ by ring]
  have : Z.P + K * δ = θ := by
    simp only [δ]; field_simp; ring
  rw [key K, this]

end Loop

end SPFGGeo

-- ===== Geo24 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

lemma pr_update0 {G : MetricGraph k} (a a' b : G.Pt) : Function.update (pr a b) 0 a' = pr a' b := by
  funext j; fin_cases j <;> simp [pr]

lemma pr_update1 {G : MetricGraph k} (a b b' : G.Pt) : Function.update (pr a b) 1 b' = pr a b' := by
  funext j; fin_cases j <;> simp [pr]

/-- agent 0's option set spreads: points closer to an option than to `b` are options -/
lemma A_spread {G : MetricGraph k} {M : Profile G 2 → G.Pt} (hSP : IsSP G M)
    (hps : ∀ x : Profile G 2, M x = x 0 ∨ M x = x 1) {a a' b : G.Pt}
    (ha : M (pr a b) = a) (h : G.dist a' a < G.dist a' b) : M (pr a' b) = a' := by
  by_contra hne
  have hb : M (pr a' b) = b := by
    rcases hps (pr a' b) with h1 | h1
    · exact absurd h1 (by simpa [pr] using hne)
    · simpa [pr] using h1
  have := hSP (pr a' b) 0 a
  have e : (pr a' b) 0 = a' := by simp [pr]
  rw [pr_update0, ha, hb, e] at this
  rw [G.dist_comm b a', G.dist_comm a a'] at this
  linarith

namespace Loop

variable {G : MetricGraph k} (Z : Loop G)

lemma γP_iso (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    {t t' : ℝ} (ht : Z.P ≤ t) (h : |t' - t| ≤ lm2 G) :
    G.dist (Z.γP t') (Z.γP t) = |t' - t| := by
  obtain ⟨W, hWα, hWβ, hW⟩ := Z.lwin M hSP hM t ht
  have hm : t' - t ∈ Set.Icc (-lm2 G) (lm2 G) := abs_le.1 h
  have hl := lm2_pos G
  have e1 : Z.γP t' = W.φ (t' - t) := by rw [hW _ hm]; congr 1; ring
  have e2 : Z.γP t = W.φ 0 := by rw [hW 0 ⟨by linarith, by linarith⟩]; congr 1; ring
  rw [e1, e2, W.iso _ ⟨by linarith [hm.1], by linarith [hm.2]⟩ _ ⟨by linarith, by linarith⟩, sub_zero]

lemma γP_cont (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    ContinuousOn (fun t => ((Z.γP t : G.Pt) : E k)) (Set.Ici Z.P) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min ε (lm2 G), lt_min hε (lm2_pos G), fun x _ hx => ?_⟩
  rw [Real.dist_eq] at hx
  rw [dist_eq_norm]
  calc ‖((Z.γP x : G.Pt) : E k) - Z.γP t‖ ≤ G.dist (Z.γP x) (Z.γP t) := norm_le_dist G _ _
    _ = |x - t| := Z.γP_iso M hSP hM ht (le_trans hx.le (min_le_right _ _))
    _ < ε := lt_of_lt_of_le hx (min_le_left _ _)

/-- the loop type is dictatorial: not "forward wins" nor "backward wins" -/
theorem type_dict (M : Profile G 2 → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hps : ∀ x : Profile G 2, M x = x 0 ∨ M x = x 1) :
    (Z.L0 M {1} Z.P ↔ ¬ Z.L0 M {0} Z.P) := by
  classical
  by_contra hcon
  have hX : (Z.L0 M {1} Z.P ↔ Z.L0 M {0} Z.P) := by tauto
  set lm := lm2 G with hlmdef
  have hl : 0 < lm := lm2_pos G
  have hlP : lm ≤ Z.P := Z.lm2_le_P
  have hP := Z.P_pos
  set θ0 := Z.P with hθ0
  set b := Z.γP θ0 with hb
  -- forward and backward statuses at a visit
  have fwd : ∀ t s, Z.P ≤ t → Z.γP t = b → 0 < s → s ≤ lm →
      (M (pr (Z.γP (t + s)) b) = Z.γP (t + s) ↔ ¬ Z.L0 M {0} Z.P) := by
    intro t s ht hbt hs hs'
    have h1 := Z.lose_iff_L0 M hSP hM hps {0} ht hs hs'
    rw [Z.L0_const M hSP hM hps {0} ht] at h1
    unfold Lose at h1; rw [two0, hbt] at h1
    have hne : Z.γP (t + s) ≠ b := by
      intro h
      have := Z.γP_iso M hSP hM (t := t) (t' := t + s) ht (by rw [abs_le]; constructor <;> linarith)
      rw [h, hbt, dist_self] at this
      rw [show t + s - t = s by ring, abs_of_pos hs] at this; linarith
    constructor
    · intro h h'; rw [h1.2 h'] at h; exact hne h.symm
    · intro h
      rcases hps (pr (Z.γP (t + s)) b) with h2 | h2
      · simpa [pr] using h2
      · exact absurd (h1.1 (by simpa [pr] using h2)) h
  have bwd : ∀ t s, Z.P ≤ t - s → Z.γP t = b → 0 < s → s ≤ lm →
      (M (pr (Z.γP (t - s)) b) = Z.γP (t - s) ↔ Z.L0 M {1} Z.P) := by
    intro t s ht hbt hs hs'
    have h1 := Z.lose_iff_L0 M hSP hM hps {1} ht hs hs'
    rw [Z.L0_const M hSP hM hps {1} ht, show t - s + s = t by ring] at h1
    unfold Lose at h1; rw [two1, hbt] at h1
    exact h1
  -- the first return time
  set T := Set.Icc (θ0 + lm / 2) (θ0 + Z.P) ∩ (fun t => ((Z.γP t : G.Pt) : E k)) ⁻¹' {(b : E k)}
    with hT
  have hTc : IsClosed T :=
    ((Z.γP_cont M hSP hM).mono (fun t ht => by simp only [Set.mem_Ici]; linarith [ht.1])).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hPT : θ0 + Z.P ∈ T := by
    refine ⟨⟨by linarith, le_rfl⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hb, Z.γP_per (by linarith)]
  have hTne : T.Nonempty := ⟨_, hPT⟩
  have hTb : BddBelow T := ⟨θ0 + lm / 2, fun t ht => ht.1.1⟩
  set t2 := sInf T with ht2
  have ht2T : t2 ∈ T := hTc.csInf_mem hTne hTb
  have ht2lo : θ0 + lm / 2 ≤ t2 := ht2T.1.1
  have ht2hi : t2 ≤ θ0 + Z.P := ht2T.1.2
  have ht2b : Z.γP t2 = b := Subtype.ext ht2T.2
  -- no visits in between
  have hnov : ∀ t ∈ Set.Ioo θ0 t2, Z.γP t ≠ b := by
    intro t ht hbt
    by_cases h : θ0 + lm / 2 ≤ t
    · have : t ∈ T := ⟨⟨h, by linarith [ht.2]⟩, by simp [hbt]⟩
      have := csInf_le hTb this
      linarith [ht.2]
    · push Not at h
      have := Z.γP_iso M hSP hM (t := θ0) (t' := t) le_rfl
        (by rw [abs_le]; constructor <;> linarith [ht.1])
      rw [hbt, dist_self, abs_of_pos (by linarith [ht.1])] at this
      linarith [ht.1]
  -- local constancy
  set f : ℝ → Bool := fun t => decide (M (pr (Z.γP t) b) = Z.γP t) with hf
  have hcont : ContinuousOn f (Set.Ioo θ0 t2) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply tendsto_nhds_of_eventually_eq
    have htP : Z.P ≤ t := by linarith [ht.1]
    set ρ := G.dist (Z.γP t) b with hρ
    have hρ0 : 0 < ρ := by
      rcases (dist_nonneg G (Z.γP t) b).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_of_dist_eq_zero G _ _ h.symm) (hnov t ht)
    have hball : Metric.ball t (min (ρ / 2) lm) ∈ nhds t :=
      Metric.ball_mem_nhds _ (lt_min (by linarith) hl)
    filter_upwards [hball] with t' ht'
    rw [Metric.mem_ball, Real.dist_eq] at ht'
    have hd : G.dist (Z.γP t') (Z.γP t) = |t' - t| :=
      Z.γP_iso M hSP hM htP (le_trans ht'.le (min_le_right _ _))
    have hd2 : G.dist (Z.γP t') (Z.γP t) < ρ / 2 := by
      rw [hd]; exact lt_of_lt_of_le ht' (min_le_left _ _)
    have htri := G.dist_triangle (Z.γP t) (Z.γP t') b
    have hcomm := G.dist_comm (Z.γP t') (Z.γP t)
    simp only [hf, decide_eq_decide]
    constructor
    · intro h
      exact A_spread hSP hps h (by rw [← hcomm]; linarith)
    · intro h
      exact A_spread hSP hps h (by linarith)
  set s1 := min (lm / 4) ((t2 - θ0) / 2) with hs1
  have hs1pos : 0 < s1 := lt_min (by linarith) (by linarith)
  have hs1a : s1 ≤ lm / 4 := min_le_left _ _
  have hs1b : s1 ≤ (t2 - θ0) / 2 := min_le_right _ _
  have hA : θ0 + s1 ∈ Set.Ioo θ0 t2 := ⟨by linarith, by linarith⟩
  have hB : t2 - s1 ∈ Set.Ioo θ0 t2 := ⟨by linarith, by linarith⟩
  have := isPreconnected_Ioo.constant hcont hA hB
  simp only [hf, decide_eq_decide] at this
  rw [fwd θ0 s1 le_rfl rfl hs1pos (by linarith),
    bwd t2 s1 (by linarith) ht2b hs1pos (by linarith)] at this
  tauto

end Loop

end SPFGGeo

-- ===== Geo25 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

/-- points of a geodesic from `a` arbitrarily close to `b`, on a ray at `b` -/
lemma geo_ray (G : MetricGraph k) (a b : G.Pt) (hab : a ≠ b) :
    ∃ e ∈ G.edges, ∃ tx tw : ℝ, tx ∈ Set.Icc (0:ℝ) 1 ∧ tw ∈ Set.Icc (0:ℝ) 1 ∧ tw ≠ tx ∧
      (b : E k) = epar e tx ∧ ∀ B > 0, ∃ s, 0 < s ∧ s ≤ B ∧ ∃ P : G.Pt,
        (P : E k) = qray b (wdir e tx tw) s ∧ G.dist a P + G.dist P b = G.dist a b := by
  obtain ⟨e, he, tx, tw, htx, htw, hne, hbt, hseg⟩ := near_geo G a b hab
  refine ⟨e, he, tx, tw, htx, htw, hne, hbt, fun B hB => ?_⟩
  have hL := elen_pos G he
  have hd : 0 < |tw - tx| := abs_pos.2 (sub_ne_zero.2 hne)
  set θ := min 1 (B / (|tw - tx| * elen e)) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθB : θ * |tw - tx| * elen e ≤ B := by
    have := min_le_right 1 (B / (|tw - tx| * elen e))
    rw [← hθ, le_div_iff₀ (by positivity)] at this; linarith
  set t := tx + θ * (tw - tx)
  have htu : t ∈ Set.uIcc tx tw := by
    rcases le_total tx tw with h | h
    · rw [Set.uIcc_of_le h]; constructor <;> nlinarith
    · rw [Set.uIcc_of_ge h]; constructor <;> nlinarith
  have htI : t ∈ Set.Icc (0:ℝ) 1 := by
    rcases le_total tx tw with h | h
    · rw [Set.uIcc_of_le h] at htu; exact ⟨by linarith [htx.1, htu.1], by linarith [htw.2, htu.2]⟩
    · rw [Set.uIcc_of_ge h] at htu; exact ⟨by linarith [htw.1, htu.1], by linarith [htx.2, htu.2]⟩
  have hmem : epar e t ∈ G.carrier := Set.mem_biUnion he (epar_mem htI)
  refine ⟨θ * |tw - tx| * elen e, by positivity, hθB, ⟨epar e t, hmem⟩, ?_, hseg _ t htu rfl⟩
  show epar e t = _
  rw [epar_qray G he htx htw hne, ← hbt]; rfl

/-- interior points of edges -/
def IntPt (G : MetricGraph k) (b : G.Pt) : Prop :=
  ∃ e ∈ G.edges, ∃ τ ∈ Set.Ioo (0:ℝ) 1, (b : E k) = epar e τ

lemma near_int (G : MetricGraph k) (b : G.Pt) {ε : ℝ} (hε : 0 < ε) :
    ∃ b' : G.Pt, IntPt G b' ∧ G.dist b b' < ε := by
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.1 b.2
  obtain ⟨τ, hτ, hbτ⟩ := (mem_seg_iff e b).1 hb
  have hL := elen_pos G he
  set η := min (1 / 4) (ε / (2 * elen e)) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 4 := min_le_left _ _
  have hηε : η * elen e < ε := by
    have := min_le_right (1/4 : ℝ) (ε / (2 * elen e))
    rw [← hη, le_div_iff₀ (by positivity)] at this; nlinarith
  set τ' := if τ ≤ 1 / 2 then τ + η else τ - η with hτ'
  have hτ'I : τ' ∈ Set.Ioo (0:ℝ) 1 := by
    rw [hτ']; split_ifs with h
    · exact ⟨by linarith [hτ.1], by linarith⟩
    · exact ⟨by linarith, by linarith [hτ.2]⟩
  have hd : |τ - τ'| = η := by
    rw [hτ']; split_ifs
    · rw [show τ - (τ + η) = -η by ring, abs_neg, abs_of_pos hη0]
    · rw [show τ - (τ - η) = η by ring, abs_of_pos hη0]
  have hmem : epar e τ' ∈ G.carrier := Set.mem_biUnion he (epar_mem ⟨hτ'I.1.le, hτ'I.2.le⟩)
  refine ⟨⟨epar e τ', hmem⟩, ⟨e, he, τ', hτ'I, rfl⟩, ?_⟩
  rw [dist_epar G e he b ⟨epar e τ', hmem⟩ hτ ⟨hτ'I.1.le, hτ'I.2.le⟩ hbτ rfl, hd]
  exact hηε

/-- through an interior point, agent 0 or agent 1 dictates -/
lemma int_dict (G : MetricGraph k) (hLR : LoopRich G) (M : Profile G 2 → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (b : G.Pt) (hb : IntPt G b) :
    (∀ a, M (pr a b) = a) ∨ (∀ c, M (pr b c) = c) := by
  classical
  have hps := peak2 G hLR M hSP hM
  obtain ⟨e, he, τ, hτ, hbτ⟩ := hb
  have hne := G.fst_ne_snd e he
  have hbseg : (b : E k) ∈ segment ℝ e.1 e.2 := hbτ ▸ epar_mem ⟨hτ.1.le, hτ.2.le⟩
  have hb1 : e.1 ≠ (b : E k) := by
    rw [hbτ, ← epar_zero e]; intro h; have := epar_inj hne h; linarith [hτ.1]
  have hb2 : e.2 ≠ (b : E k) := by
    rw [hbτ, ← epar_one e]; intro h; have := epar_inj hne h; linarith [hτ.2]
  have hpair : (e, e.1) ≠ (e, e.2) := by intro h; simp at h; exact hne h
  obtain ⟨Z, θq, hθq, δ, hδ, hγ⟩ := hLR (b : E k) e e he he e.1 e.2 (Or.inl rfl) (Or.inr rfl)
    hbseg hbseg hb1 hb2 hpair
  have hl := Loop.lm2_pos G
  have hlP := Z.lm2_le_P
  have hP := Z.P_pos
  have hθ0 : 0 ≤ θq := by linarith
  have hbγ : Z.γP θq = b := by
    apply Subtype.ext; rw [Z.γP_val hθ0]
    have := (hγ 0 ⟨le_rfl, hδ.le⟩).2; rw [add_zero, qray_zero] at this; exact this
  have hbγ' : Z.γP (θq + Z.P) = b := by rw [Z.γP_per hθ0, hbγ]
  -- points of the loop near `b`
  have hfwd : ∀ s, 0 < s → s ≤ min δ (Loop.lm2 G) → ∀ P : G.Pt, (P : E k) = qray b e.2 s →
      P = Z.γP (θq + s) := by
    intro s hs hsB P hP
    apply Subtype.ext; rw [Z.γP_val (by linarith), hP]
    exact ((hγ s ⟨hs.le, hsB.trans (min_le_left _ _)⟩).2).symm
  have hbwd : ∀ s, 0 < s → s ≤ min δ (Loop.lm2 G) → ∀ P : G.Pt, (P : E k) = qray b e.1 s →
      P = Z.γP (θq + Z.P - s) := by
    intro s hs hsB P hP
    have hs' : s ≤ Loop.lm2 G := hsB.trans (min_le_right _ _)
    apply Subtype.ext
    rw [Z.γP_val (by linarith), hP, show θq + Z.P - s = (θq - s) + Z.P by ring,
      Z.γ_per (by linarith)]
    exact ((hγ s ⟨hs.le, hsB.trans (min_le_left _ _)⟩).1).symm
  have hB : 0 < min δ (Loop.lm2 G) := lt_min hδ hl
  -- direction of a geodesic arriving at `b`
  have hdir : ∀ (e' : E k × E k), e' ∈ G.edges → ∀ tx tw : ℝ, tx ∈ Set.Icc (0:ℝ) 1 →
      (b : E k) = epar e' tx → wdir e' tx tw = e.1 ∨ wdir e' tx tw = e.2 := by
    intro e' he' tx tw htx hbt
    have : e' = e := edge_unique G e he τ hτ e' he' (by rw [← hbτ, hbt]; exact epar_mem htx)
    subst this; exact wdir_end e' tx tw
  rcases Z.type_dict M hSP hM hps with ⟨h1, h2⟩
  by_cases hL1 : Z.L0 M {1} Z.P
  · -- agent 0 dictates locally
    have hL0 : ¬ Z.L0 M {0} Z.P := h1 hL1
    left
    intro a
    by_contra hne'
    have hab : a ≠ b := by
      intro h; subst h
      have := unanimity G M hSP hM a
      exact hne' (by rw [show pr a a = fun _ => a by funext j; simp [pr]]; exact this)
    have hMb : M (pr a b) = b := by
      rcases hps (pr a b) with h | h
      · exact absurd (by simpa [pr] using h) hne'
      · simpa [pr] using h
    obtain ⟨e', he', tx, tw, htx, htw, hne'', hbt, hray⟩ := geo_ray G a b hab
    obtain ⟨s, hs, hsB, P, hPq, hgeo⟩ := hray _ hB
    have hs' : s ≤ Loop.lm2 G := hsB.trans (min_le_right _ _)
    have hPloc : M (pr P b) = P := by
      rcases hdir e' he' tx tw htx hbt with hw | hw
      · rw [hw] at hPq
        have hPe := hbwd s hs hsB P hPq
        have := (Z.lose_iff_L0 M hSP hM hps {1} (θ := θq + Z.P - s) (by linarith) hs hs').2
          (by rw [Z.L0_const M hSP hM hps {1} (by linarith)]; exact hL1)
        unfold Lose at this
        rw [two1, show θq + Z.P - s + s = θq + Z.P by ring, hbγ', ← hPe] at this
        exact this
      · rw [hw] at hPq
        have hPe := hfwd s hs hsB P hPq
        have := mt (Z.lose_iff_L0 M hSP hM hps {0} (θ := θq) hθq hs hs').1
          (by rw [Z.L0_const M hSP hM hps {0} hθq]; exact hL0)
        unfold Lose at this
        rw [two0, hbγ, ← hPe] at this
        rcases hps (pr P b) with h | h
        · simpa [pr] using h
        · exact absurd (by simpa [pr] using h) this
    have hPb : 0 < G.dist P b := by
      have := norm_le_dist G P b
      have hn : ‖(P : E k) - b‖ = s := by
        rw [hPq]
        have hw0 : wdir e' tx tw ≠ (b : E k) := by rw [hbt]; exact wdir_ne G he' htw hne''
        have := norm_qray_sub (q := (b : E k)) hw0 s 0
        rw [qray_zero, sub_zero, abs_of_pos hs] at this; exact this
      linarith
    have hsp := hSP (pr a b) 0 P
    have e0 : (pr a b) 0 = a := by simp [pr]
    rw [pr_update0, hMb, hPloc, e0] at hsp
    rw [G.dist_comm b a, G.dist_comm P a] at hsp
    linarith
  · -- agent 1 dictates locally
    have hL0 : Z.L0 M {0} Z.P := by by_contra h; exact hL1 (h2 h)
    right
    intro c
    by_contra hne'
    have hcb : c ≠ b := by
      intro h; subst h
      have := unanimity G M hSP hM c
      exact hne' (by rw [show pr c c = fun _ => c by funext j; simp [pr]]; exact this)
    have hMb : M (pr b c) = b := by
      rcases hps (pr b c) with h | h
      · simpa [pr] using h
      · exact absurd (by simpa [pr] using h) hne'
    obtain ⟨e', he', tx, tw, htx, htw, hne'', hbt, hray⟩ := geo_ray G c b hcb
    obtain ⟨s, hs, hsB, P, hPq, hgeo⟩ := hray _ hB
    have hs' : s ≤ Loop.lm2 G := hsB.trans (min_le_right _ _)
    have hPloc : M (pr b P) = P := by
      rcases hdir e' he' tx tw htx hbt with hw | hw
      · rw [hw] at hPq
        have hPe := hbwd s hs hsB P hPq
        have := (Z.lose_iff_L0 M hSP hM hps {0} (θ := θq + Z.P - s) (by linarith) hs hs').2
          (by rw [Z.L0_const M hSP hM hps {0} (by linarith)]; exact hL0)
        unfold Lose at this
        rw [two0, show θq + Z.P - s + s = θq + Z.P by ring, hbγ', ← hPe] at this
        exact this
      · rw [hw] at hPq
        have hPe := hfwd s hs hsB P hPq
        have := mt (Z.lose_iff_L0 M hSP hM hps {1} (θ := θq) hθq hs hs').1
          (by rw [Z.L0_const M hSP hM hps {1} hθq]; exact hL1)
        unfold Lose at this
        rw [two1, hbγ, ← hPe] at this
        rcases hps (pr b P) with h | h
        · exact absurd (by simpa [pr] using h) this
        · simpa [pr] using h
    have hPb : 0 < G.dist P b := by
      have := norm_le_dist G P b
      have hn : ‖(P : E k) - b‖ = s := by
        rw [hPq]
        have hw0 : wdir e' tx tw ≠ (b : E k) := by rw [hbt]; exact wdir_ne G he' htw hne''
        have := norm_qray_sub (q := (b : E k)) hw0 s 0
        rw [qray_zero, sub_zero, abs_of_pos hs] at this; exact this
      linarith
    have hsp := hSP (pr b c) 1 P
    have e1 : (pr b c) 1 = c := by simp [pr]
    rw [pr_update1, hMb, hPloc, e1] at hsp
    rw [G.dist_comm b c, G.dist_comm P c] at hsp
    linarith

end SPFGGeo

-- ===== Geo26 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

lemma pr_eta {G : MetricGraph k} (x : Profile G 2) : pr (x 0) (x 1) = x := by
  funext j; fin_cases j <;> simp [pr]

/-- **Two-agent dictatorship** on loop-rich graphs. -/
theorem dict2 (G : MetricGraph k) (hLR : LoopRich G) (M : Profile G 2 → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) : (∀ x, M x = x 0) ∨ (∀ x, M x = x 1) := by
  classical
  have hps := peak2 G hLR M hSP hM
  obtain ⟨e0, he0⟩ := G.edges_nonempty
  have hne0 := G.fst_ne_snd e0 he0
  have hm1 : epar e0 (1/2) ∈ G.carrier := Set.mem_biUnion he0 (epar_mem ⟨by norm_num, by norm_num⟩)
  have hm2 : epar e0 (1/4) ∈ G.carrier := Set.mem_biUnion he0 (epar_mem ⟨by norm_num, by norm_num⟩)
  set b0 : G.Pt := ⟨epar e0 (1/2), hm1⟩
  set b1 : G.Pt := ⟨epar e0 (1/4), hm2⟩
  have hb0 : IntPt G b0 := ⟨e0, he0, 1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hb1 : IntPt G b1 := ⟨e0, he0, 1/4, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hb01 : b0 ≠ b1 := by
    intro h; have := congrArg Subtype.val h
    have := epar_inj hne0 this; norm_num at this
  -- incompatibility of the two local types at distinct points
  have incompat : ∀ b b' : G.Pt, b ≠ b' → (∀ a, M (pr a b) = a) → (∀ c, M (pr b' c) = c) → False :=
    fun b b' hbb' h0 h1 => hbb' ((h1 b).symm.trans (h0 b'))
  have allD0 : (∀ a, M (pr a b0) = a) → ∀ b, IntPt G b → ∀ a, M (pr a b) = a := by
    intro h0 b hb
    rcases int_dict G hLR M hSP hM b hb with h | h
    · exact h
    · by_cases hbb : b = b0
      · rw [hbb]; exact h0
      · exact absurd (incompat b0 b (Ne.symm hbb) h0 h) id
  have allD1 : (∀ c, M (pr b0 c) = c) → ∀ b, IntPt G b → ∀ c, M (pr b c) = c := by
    intro h1 b hb
    rcases int_dict G hLR M hSP hM b hb with h | h
    · by_cases hbb : b = b0
      · rw [hbb] at h
        rcases int_dict G hLR M hSP hM b1 hb1 with h' | h'
        · exact absurd (incompat b1 b0 hb01.symm h' h1) id
        · exact absurd (incompat b0 b1 hb01 h h') id
      · exact absurd (incompat b b0 hbb h h1) id
    · exact h
  rcases int_dict G hLR M hSP hM b0 hb0 with h0 | h1
  · left
    have hall := allD0 h0
    suffices key : ∀ a b, M (pr a b) = a by
      intro x; have := key (x 0) (x 1); rwa [pr_eta] at this
    intro a b
    by_contra hne
    have hMb : M (pr a b) = b := by
      rcases hps (pr a b) with h | h
      · exact absurd (by simpa [pr] using h) hne
      · simpa [pr] using h
    have hab : a ≠ b := by
      intro h; apply hne; rw [h]; rw [h] at hMb; exact hMb
    have hd : 0 < G.dist a b := by
      rcases (dist_nonneg G a b).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_of_dist_eq_zero G _ _ h.symm) hab
    obtain ⟨b', hb', hbb'⟩ := near_int G b (ε := G.dist a b / 2) (by linarith)
    have h1 := hall b' hb' a
    have hsp := hSP (pr a b') 1 b
    have e1 : (pr a b') 1 = b' := by simp [pr]
    rw [pr_update1, h1, hMb, e1] at hsp
    have t1 : G.dist a b ≤ G.dist a b' + G.dist b' b := G.dist_triangle a b' b
    have c1 : G.dist b' b = G.dist b b' := G.dist_comm b' b
    have c2 : G.dist a b' ≤ G.dist b b' := hsp
    linarith
  · right
    have hall := allD1 h1
    suffices key : ∀ a c, M (pr a c) = c by
      intro x; have := key (x 0) (x 1); rwa [pr_eta] at this
    intro a c
    by_contra hne
    have hMa : M (pr a c) = a := by
      rcases hps (pr a c) with h | h
      · simpa [pr] using h
      · exact absurd (by simpa [pr] using h) hne
    have hac : a ≠ c := by
      intro h; apply hne; rw [← h]; rw [h] at hMa; rw [h]; exact hMa
    have hd : 0 < G.dist a c := by
      rcases (dist_nonneg G a c).lt_or_eq with h | h
      · exact h
      · exact absurd (eq_of_dist_eq_zero G _ _ h.symm) hac
    obtain ⟨a', ha', haa'⟩ := near_int G a (ε := G.dist a c / 2) (by linarith)
    have h1 := hall a' ha' c
    have hsp := hSP (pr a' c) 0 a
    have e0 : (pr a' c) 0 = a' := by simp [pr]
    rw [pr_update0, h1, hMa, e0] at hsp
    have t1 : G.dist a c ≤ G.dist a a' + G.dist a' c := G.dist_triangle a a' c
    have c1 : G.dist a' c = G.dist c a' := G.dist_comm a' c
    have c2 : G.dist a a' = G.dist a' a := G.dist_comm a a'
    have c3 : G.dist c a' ≤ G.dist a a' := hsp
    linarith

end SPFGGeo

-- ===== Geo27 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

lemma exists_ne_pt (G : MetricGraph k) (w : G.Pt) : ∃ a : G.Pt, a ≠ w := by
  obtain ⟨e, he⟩ := G.edges_nonempty
  have h1 : e.1 ∈ G.carrier := Set.mem_biUnion he (left_mem_segment ℝ e.1 e.2)
  have h2 : e.2 ∈ G.carrier := Set.mem_biUnion he (right_mem_segment ℝ e.1 e.2)
  by_cases h : (⟨e.1, h1⟩ : G.Pt) = w
  · refine ⟨⟨e.2, h2⟩, fun h' => G.fst_ne_snd e he ?_⟩
    have := congrArg Subtype.val (h.trans h'.symm); exact this
  · exact ⟨_, h⟩

/-- merging agents `0` and `1` -/
def mrg {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) : Fin n := ⟨i.val - 1, by omega⟩

lemma merge_succ {n : ℕ} (hn : 1 ≤ n) {G : MetricGraph k} (y : Profile G (n + 1))
    (hy : y ⟨0, by omega⟩ = y ⟨1, by omega⟩) : (fun i => (y ∘ Fin.succ) (mrg hn i)) = y := by
  funext i
  simp only [Function.comp, mrg]
  by_cases h : i.val = 0
  · rw [show (⟨i.val - 1, by omega⟩ : Fin n).succ = ⟨1, by omega⟩ from Fin.ext (by simp [h]),
      show i = ⟨0, by omega⟩ from Fin.ext h, hy]
  · congr 1; exact Fin.ext (by simp; omega)

lemma upd01_comm {n : ℕ} (hn : 1 ≤ n) {G : MetricGraph k} (x : Profile G (n + 1)) (h01 : (⟨0, by omega⟩ : Fin (n+1)) ≠ ⟨1, by omega⟩)
    (a b c : G.Pt) :
    Function.update (Function.update (Function.update x ⟨0, by omega⟩ a) ⟨1, by omega⟩ b) ⟨0, by omega⟩ c =
      Function.update (Function.update x ⟨0, by omega⟩ c) ⟨1, by omega⟩ b := by
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem dictN (G : MetricGraph k) (hLR : LoopRich G) :
    ∀ n, 2 ≤ n → ∀ M : Profile G n → G.Pt, IsSP G M → Function.Surjective M →
      ∃ j, ∀ x, M x = x j := by
  classical
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro M hSP hM
    rcases dict2 G hLR M hSP hM with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  | succ n hn ih =>
    intro M hSP hM
    have hn1 : 1 ≤ n := by omega
    set i0 : Fin (n + 1) := ⟨0, by omega⟩
    set i1 : Fin (n + 1) := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    set M' : Profile G n → G.Pt := fun z => M (fun i => z (mrg hn1 i)) with hM'
    have hdiag : ∀ y : Profile G (n + 1), y i0 = y i1 → M y = M' (y ∘ Fin.succ) := by
      intro y hy; simp only [hM']; rw [merge_succ hn1 y hy]
    -- M' is SP and onto
    have hSP' : IsSP G M' := by
      intro z j y
      by_cases hj : j.val = 0
      · have hj0 : j = ⟨0, by omega⟩ := Fin.ext hj
        set x : Profile G (n + 1) := fun i => z (mrg hn1 i)
        have e1 : (fun i => (Function.update z j y) (mrg hn1 i)) =
            Function.update (Function.update x i0 y) i1 y := by
          funext i
          simp only [Function.update_apply, x, Fin.ext_iff, mrg, i0, i1, hj0]
          split_ifs <;> first | rfl | omega | (congr 1; ext; simp; omega)
        have hx0 : x i0 = z j := by simp only [x, mrg, i0, hj0]
        have hx1 : x i1 = z j := by simp only [x, mrg, i1, hj0]
        show G.dist (M x) (z j) ≤ G.dist (M (fun i => (Function.update z j y) (mrg hn1 i))) (z j)
        rw [e1]
        have s1 := hSP x i0 y
        have s2 := hSP (Function.update x i0 y) i1 y
        rw [Function.update_of_ne h01.symm, hx1] at s2
        rw [hx0] at s1
        linarith
      · set x : Profile G (n + 1) := fun i => z (mrg hn1 i)
        set jj : Fin (n + 1) := ⟨j.val + 1, by omega⟩
        have e1 : (fun i => (Function.update z j y) (mrg hn1 i)) = Function.update x jj y := by
          funext i
          simp only [Function.update_apply, x, Fin.ext_iff, mrg, jj]
          split_ifs <;> first | rfl | omega
        have hxj : x jj = z j := by simp only [x, mrg, jj]; congr 1
        show G.dist (M x) (z j) ≤ G.dist (M (fun i => (Function.update z j y) (mrg hn1 i))) (z j)
        rw [e1, ← hxj]; exact hSP x jj y
    have hM' : Function.Surjective M' := fun c => ⟨fun _ => c, unanimity G M hSP hM c⟩
    obtain ⟨j, hj⟩ := ih M' hSP' hM'
    by_cases hj0 : j.val = 0
    · -- the merged pair dictates when it agrees
      have hagree : ∀ y : Profile G (n + 1), y i0 = y i1 → M y = y i0 := by
        intro y hy
        rw [hdiag y hy, hj]
        simp only [Function.comp]
        rw [show j.succ = i1 from Fin.ext (by simp [i1]; omega)]; exact hy.symm
      set P0 : Profile G (n + 1) → Prop := fun x => ∀ a b,
        M (Function.update (Function.update x i0 a) i1 b) = a
      set P1 : Profile G (n + 1) → Prop := fun x => ∀ a b,
        M (Function.update (Function.update x i0 a) i1 b) = b
      have hdich : ∀ x, P0 x ∨ P1 x := by
        intro x
        set N : Profile G 2 → G.Pt := fun u => M (Function.update (Function.update x i0 (u 0)) i1 (u 1))
        have hNSP : IsSP G N := by
          intro u i z
          rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
          · have hu0 : (Function.update u 0 z) 0 = z := Function.update_self _ _ _
            have hu1 : (Function.update u 0 z) 1 = u 1 := Function.update_of_ne (by decide) _ _
            have := hSP (Function.update (Function.update x i0 (u 0)) i1 (u 1)) i0 z
            rw [Function.update_of_ne h01, Function.update_self, upd01_comm hn1 x h01] at this
            show _ ≤ G.dist (M (Function.update (Function.update x i0 ((Function.update u 0 z) 0)) i1
              ((Function.update u 0 z) 1))) (u 0)
            rw [hu0, hu1]; exact this
          · have hu0 : (Function.update u 1 z) 0 = u 0 := Function.update_of_ne (by decide) _ _
            have hu1 : (Function.update u 1 z) 1 = z := Function.update_self _ _ _
            have := hSP (Function.update (Function.update x i0 (u 0)) i1 (u 1)) i1 z
            rw [Function.update_self, Function.update_idem] at this
            show _ ≤ G.dist (M (Function.update (Function.update x i0 ((Function.update u 1 z) 0)) i1
              ((Function.update u 1 z) 1))) (u 1)
            rw [hu0, hu1]; exact this
        have hNon : Function.Surjective N := by
          intro c; refine ⟨fun _ => c, ?_⟩
          simp only [N]
          rw [hagree _ (by rw [Function.update_of_ne h01, Function.update_self, Function.update_self])]
          rw [Function.update_of_ne h01, Function.update_self]
        rcases dict2 G hLR N hNSP hNon with h | h
        · left; intro a b; have := h (pr a b); simpa [N, pr] using this
        · right; intro a b; have := h (pr a b); simpa [N, pr] using this
      have hnot : ∀ x, P0 x → P1 x → False := by
        intro x h0 h1
        obtain ⟨a, ha⟩ := exists_ne_pt G (x i0)
        exact ha ((h0 a (x i0)).symm.trans (h1 a (x i0)))
      -- invariance under one coordinate change
      have hinv : ∀ x (c : Fin (n + 1)) (v : G.Pt), P0 x → P0 (Function.update x c v) := by
        intro x c v h0
        by_cases hc0 : c = i0
        · subst hc0; intro a b; rw [Function.update_idem]; exact h0 a b
        by_cases hc1 : c = i1
        · subst hc1; intro a b
          have : Function.update (Function.update (Function.update x i1 v) i0 a) i1 b =
              Function.update (Function.update x i0 a) i1 b := by
            funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
          rw [this]; exact h0 a b
        rcases hdich (Function.update x c v) with h | h1
        · exact h
        · exfalso
          obtain ⟨a, ha⟩ := exists_ne_pt G (x c)
          have hsp := hSP (Function.update (Function.update x i0 a) i1 (x c)) c v
          have e1 : Function.update (Function.update (Function.update x i0 a) i1 (x c)) c v =
              Function.update (Function.update (Function.update x c v) i0 a) i1 (x c) := by
            funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
          rw [e1, h0 a (x c), h1 a (x c), Function.update_of_ne hc1, Function.update_of_ne hc0,
            dist_self] at hsp
          exact ha (eq_of_dist_eq_zero G _ _ (le_antisymm hsp (dist_nonneg G _ _)))
      have hreach : ∀ x x', P0 x → P0 x' := by
        intro x x' h0
        have key : ∀ C : Finset (Fin (n + 1)), P0 (fun i => if i ∈ C then x' i else x i) := by
          intro C
          induction C using Finset.induction_on with
          | empty => simpa using h0
          | insert c C hc ih =>
            have e1 : (fun i => if i ∈ insert c C then x' i else x i) =
                Function.update (fun i => if i ∈ C then x' i else x i) c (x' c) := by
              funext i; by_cases h : i = c
              · subst h; simp
              · simp [Function.update_of_ne h, h]
            rw [e1]; exact hinv _ c (x' c) ih
        simpa using key Finset.univ
      have hfin : ∀ x, P0 x → M x = x i0 := by
        intro x h0
        have := h0 (x i0) (x i1)
        rwa [Function.update_eq_self, Function.update_eq_self] at this
      have hfin1 : ∀ x, P1 x → M x = x i1 := by
        intro x h1
        have := h1 (x i0) (x i1)
        rwa [Function.update_eq_self, Function.update_eq_self] at this
      by_cases hex : ∃ x, P0 x
      · obtain ⟨x0, hx0⟩ := hex
        exact ⟨i0, fun x => hfin x (hreach x0 x hx0)⟩
      · push Not at hex
        exact ⟨i1, fun x => hfin1 x ((hdich x).resolve_left (hex x))⟩
    · -- another agent dictates
      set jj : Fin (n + 1) := ⟨j.val + 1, by omega⟩
      have hjj0 : jj ≠ i0 := by simp [jj, i0, Fin.ext_iff]
      have hjj1 : jj ≠ i1 := by simp [jj, i1, Fin.ext_iff]; omega
      refine ⟨jj, fun x => ?_⟩
      set N : G.Pt → G.Pt → G.Pt := fun a b => M (Function.update (Function.update x i0 a) i1 b)
      have hNd : ∀ a, N a a = x jj := by
        intro a
        simp only [N]
        rw [hdiag _ (by rw [Function.update_of_ne h01, Function.update_self, Function.update_self]), hj]
        simp only [Function.comp]
        rw [show Fin.succ j = jj by ext; simp [jj], Function.update_of_ne hjj1, Function.update_of_ne hjj0]
      have hN : ∀ a b, N a b = x jj := by
        intro a b
        set o := N a b with ho
        have s1 := hSP (Function.update (Function.update x i0 o) i1 b) i0 a
        rw [upd01_comm hn1 x h01, Function.update_of_ne h01, Function.update_self] at s1
        have hob : N o b = o := by
          simp only [N] at ho ⊢
          rw [← ho, dist_self] at s1
          exact eq_of_dist_eq_zero G _ _ (le_antisymm s1 (dist_nonneg G _ _))
        have s2 := hSP (Function.update (Function.update x i0 o) i1 o) i1 b
        rw [Function.update_self, Function.update_idem] at s2
        have hoo : N o o = o := by
          simp only [N] at hob ⊢
          rw [hob, dist_self] at s2
          exact eq_of_dist_eq_zero G _ _ (le_antisymm s2 (dist_nonneg G _ _))
        rw [hNd] at hoo; exact hoo.symm
      have := hN (x i0) (x i1)
      simp only [N] at this
      rwa [Function.update_eq_self, Function.update_eq_self] at this

end SPFGGeo

-- ===== Geo28 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k n : ℕ}

/-- the gate property of a mechanism -/
def Gate (G : MetricGraph k) (M : Profile G n → G.Pt) : Prop :=
  ∀ (x : Profile G n) (i : Fin n) (y z : G.Pt),
    G.dist y (M (Function.update x i z)) =
      G.dist y (M (Function.update x i y)) +
        G.dist (M (Function.update x i y)) (M (Function.update x i z))

lemma gate_of_dict (G : MetricGraph k) (M : Profile G n → G.Pt) (j : Fin n)
    (hj : ∀ x, M x = x j) : Gate G M := by
  intro x i y z
  by_cases h : i = j
  · subst h; simp only [hj, Function.update_self, dist_self, zero_add]
  · simp only [hj, Function.update_of_ne (Ne.symm h), dist_self, add_zero]

lemma clamp_gate (l r a b : ℝ) (hlr : l ≤ r) :
    |a - max l (min b r)| = |a - max l (min a r)| + |max l (min a r) - max l (min b r)| := by
  set c := max l (min b r) with hc
  have hc1 : l ≤ c := le_max_left _ _
  have hc2 : c ≤ r := max_le hlr (min_le_right _ _)
  rcases le_total a l with h | h
  · rw [min_eq_left (h.trans hlr), max_eq_left h]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
  · rcases le_total a r with h' | h'
    · rw [min_eq_left h', max_eq_right h, sub_self, abs_zero, zero_add]
    · rw [min_eq_right h', max_eq_right hlr]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring

/-- **Base case**: on a single-edge graph, SP onto mechanisms have the gate property. -/
theorem gate_one_edge (G : MetricGraph k) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M) (hn : 0 < n) (e : E k × E k) (hE : G.edges = {e}) : Gate G M := by
  classical
  have he : e ∈ G.edges := by rw [hE]; exact Finset.mem_singleton_self e
  have hL := elen_pos G he
  set L := elen e
  have hcar : ∀ p : G.Pt, (p : E k) ∈ segment ℝ e.1 e.2 := by
    intro p
    obtain ⟨e', he', hp⟩ := Set.mem_iUnion₂.1 p.2
    rw [hE, Finset.mem_singleton] at he'; subst he'; exact hp
  set cl : ℝ → ℝ := fun s => max 0 (min (s / L) 1)
  have hcl : ∀ s, cl s ∈ Set.Icc (0:ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hclv : ∀ s ∈ Set.Icc (0:ℝ) L, cl s = s / L := by
    intro s hs
    simp only [cl]
    rw [min_eq_left ((div_le_one hL).2 hs.2), max_eq_right (div_nonneg hs.1 hL.le)]
  set φ : ℝ → G.Pt := fun s => ⟨epar e (cl s), Set.mem_biUnion he (epar_mem (hcl s))⟩
  have hiso : ∀ s ∈ Set.Icc 0 L, ∀ t ∈ Set.Icc 0 L, G.dist (φ s) (φ t) = |s - t| := by
    intro s hs t ht
    rw [dist_epar G e he (φ s) (φ t) (hcl s) (hcl t) rfl rfl, hclv s hs, hclv t ht]
    rw [show ‖e.2 - e.1‖ = L from rfl, ← sub_div, abs_div, abs_of_pos hL, div_mul_cancel₀ _ hL.ne']
  -- every point is some φ s
  have hsur : ∀ p : G.Pt, ∃ s ∈ Set.Icc 0 L, φ s = p := by
    intro p
    obtain ⟨t, ht, hpt⟩ := (mem_seg_iff e p).1 (hcar p)
    refine ⟨t * L, ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, Subtype.ext ?_⟩
    show epar e (cl (t * L)) = p
    rw [hclv _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, mul_div_cancel_right₀ _ hL.ne', hpt]
  have hle : ∀ u : Fin n → ℝ, (∀ j, u j ∈ Set.Icc 0 L) →
      ∃ τ ∈ Set.Icc 0 L, M (fun j => φ (u j)) = φ τ := by
    intro u _
    obtain ⟨s, hs, hps⟩ := hsur (M (fun j => φ (u j)))
    exact ⟨s, hs, hps.symm⟩
  obtain ⟨F, hF, hFeq⟩ := window_gmvs G M hSP hM hn φ 0 L hL.le hiso hle
  intro x i y z
  choose σ hσ hσφ using hsur
  set u : Fin n → ℝ := fun j => σ (x j)
  have hu : SPFGSeg.InA 0 L u := fun j => hσ _
  have hx : ∀ w : G.Pt, Function.update x i w = fun j => φ (Function.update u i (σ w) j) := by
    intro w; funext j
    by_cases h : j = i
    · subst h; simp [hσφ]
    · simp [Function.update_of_ne h, u, hσφ]
  have hf : ∀ w : G.Pt, M (Function.update x i w) =
      φ (max (F (Function.update u i 0)) (min (σ w) (F (Function.update u i L)))) := by
    intro w
    rw [hx w, hFeq _ (fun j => (hu.update i (hσ w)) j), SPFGSeg.clampF hF hu i (σ w) (hσ w)]
  have hl : F (Function.update u i 0) ≤ F (Function.update u i L) :=
    SPFGSeg.mono1 hF hu i ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL.le
  have hlI : F (Function.update u i 0) ∈ Set.Icc 0 L := hF.range _ (hu.update i ⟨le_rfl, hL.le⟩)
  have hrI : F (Function.update u i L) ∈ Set.Icc 0 L := hF.range _ (hu.update i ⟨hL.le, le_rfl⟩)
  have hcI : ∀ v, max (F (Function.update u i 0)) (min v (F (Function.update u i L))) ∈ Set.Icc 0 L :=
    fun v => ⟨le_trans hlI.1 (le_max_left _ _), max_le hlI.2 (le_trans (min_le_right _ _) hrI.2)⟩
  have hdy : ∀ a ∈ Set.Icc 0 L, G.dist y (φ a) = |σ y - a| := by
    intro a ha; rw [← hiso _ (hσ y) _ ha, hσφ]
  rw [hf z, hf y, hdy _ (hcI _), hdy _ (hcI _), hiso _ (hcI _) _ (hcI _)]
  exact clamp_gate _ _ (σ y) (σ z) hl

end SPFGGeo

-- ===== Geo29 =====


namespace SPFGGeo

open SPFacilityGraph

variable {k : ℕ}

lemma seg_combo {e : E k × E k} {a b : E k} (ha : a ∈ segment ℝ e.1 e.2) (hb : b ∈ segment ℝ e.1 e.2)
    {l : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) : a + l • (b - a) ∈ segment ℝ e.1 e.2 := by
  have : a + l • (b - a) = (1 - l) • a + l • b := by module
  rw [this]
  exact (convex_segment e.1 e.2) ha hb (by linarith [hl.2]) hl.1 (by ring)

/-- points on the steps of a shortest walk are on a geodesic -/
lemma geo_pts (G : MetricGraph k) (o w : G.Pt) :
    ∃ (m : ℕ) (p : ℕ → E k), p 0 = o ∧ p m = w ∧
      (∀ j < m, ∃ e ∈ G.edges, p j ∈ segment ℝ e.1 e.2 ∧ p (j + 1) ∈ segment ℝ e.1 e.2) ∧
      ∀ j < m, ∀ l ∈ Set.Icc (0:ℝ) 1, ∀ q : G.Pt, (q : E k) = p j + l • (p (j + 1) - p j) →
        G.dist o q + G.dist q w = G.dist o w := by
  classical
  obtain ⟨m, p, h0, hm, hw, hL⟩ := G.exists_walk_eq_dist o w
  refine ⟨m, p, h0, hm, hw, fun j hj l hl q hq => ?_⟩
  obtain ⟨e, he, hpj, hpj1⟩ := hw j hj
  have hqe : (q : E k) ∈ segment ℝ e.1 e.2 := hq ▸ seg_combo hpj hpj1 hl
  set Δ := ‖p (j + 1) - p j‖
  have hq1 : ‖(q : E k) - p j‖ = l * Δ := by
    rw [hq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl.1]
  have hq2 : ‖p (j + 1) - (q : E k)‖ = (1 - l) * Δ := by
    rw [hq, show p (j + 1) - (p j + l • (p (j + 1) - p j)) = (1 - l) • (p (j + 1) - p j) by module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hl.2])]
  -- first part
  have d1 : G.dist o q ≤ ∑ i ∈ Finset.range j, ‖p (i + 1) - p i‖ + l * Δ := by
    have := G.dist_le_walk o q (j + 1) (fun i => if i ≤ j then p i else q) (by simp [h0])
      (by simp) (by
        intro i hi
        by_cases hij : i < j
        · obtain ⟨e', he', h1, h2⟩ := hw i (by omega)
          refine ⟨e', he', ?_, ?_⟩
          · simp only [show i ≤ j by omega, if_true]; exact h1
          · simp only [show i + 1 ≤ j by omega, if_true]; exact h2
        · have : i = j := by omega
          subst this
          refine ⟨e, he, ?_, ?_⟩
          · simp only [le_refl, if_true]; exact hpj
          · simp only [show ¬ (i + 1 ≤ i) by omega, if_false]; exact hqe)
    rw [Finset.sum_range_succ] at this
    simp only [le_refl, if_true, show ¬ (j + 1 ≤ j) by omega, if_false] at this
    rw [Finset.sum_congr rfl (g := fun i => ‖p (i + 1) - p i‖) (fun i hi => by
      have := Finset.mem_range.1 hi
      simp only [show i ≤ j by omega, show i + 1 ≤ j by omega, if_true])] at this
    rw [hq1] at this; exact this
  have d2 : G.dist q w ≤ (1 - l) * Δ + ∑ i ∈ Finset.range (m - (j + 1)), ‖p (j + 1 + i + 1) - p (j + 1 + i)‖ := by
    have := G.dist_le_walk q w (m - (j + 1) + 1) (fun i => if i = 0 then (q : E k) else p (j + i))
      (by simp) (by simp only [show m - (j + 1) + 1 ≠ 0 by omega, if_false]; rw [← hm]; congr 1; omega) (by
        intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          refine ⟨e, he, ?_, ?_⟩
          · simp only [if_true]; exact hqe
          · simp only [show (0:ℕ) + 1 ≠ 0 by omega, if_false]; rw [show j + (0 + 1) = j + 1 by ring]; exact hpj1
        · obtain ⟨e', he', h1, h2⟩ := hw (j + i) (by omega)
          refine ⟨e', he', ?_, ?_⟩
          · simp only [hi0, if_false]; exact h1
          · simp only [show i + 1 ≠ 0 by omega, if_false]; rw [show j + (i + 1) = j + i + 1 by ring]; exact h2)
    rw [Finset.sum_range_succ'] at this
    simp only [show (0:ℕ) + 1 ≠ 0 by omega, if_true, if_false, show j + (0 + 1) = j + 1 by ring] at this
    rw [Finset.sum_congr rfl (g := fun i => ‖p (j + 1 + i + 1) - p (j + 1 + i)‖) (fun i _ => by
      simp only [show i + 1 + 1 ≠ 0 by omega, show i + 1 ≠ 0 by omega, if_false]
      rw [show j + (i + 1 + 1) = j + 1 + i + 1 by ring, show j + (i + 1) = j + 1 + i by ring])] at this
    rw [hq2] at this; linarith
  have htot : ∑ i ∈ Finset.range m, ‖p (i + 1) - p i‖ =
      ∑ i ∈ Finset.range j, ‖p (i + 1) - p i‖ + Δ +
        ∑ i ∈ Finset.range (m - (j + 1)), ‖p (j + 1 + i + 1) - p (j + 1 + i)‖ := by
    conv_lhs => rw [show m = (j + 1) + (m - (j + 1)) by omega, Finset.sum_range_add, Finset.sum_range_succ]
  have htri := G.dist_triangle o q w
  linarith

/-- propagating a property along a geodesic in steps shorter than `δ` -/
lemma geo_chain (G : MetricGraph k) (o w : G.Pt) {δ : ℝ} (hδ : 0 < δ) (Q : G.Pt → Prop)
    (hQo : Q o)
    (hstep : ∀ t t' : G.Pt, G.dist o t + G.dist t w = G.dist o w →
      G.dist o t' + G.dist t' w = G.dist o w → G.dist t t' < δ → Q t → Q t') : Q w := by
  classical
  obtain ⟨m, p, h0, hm, hw, hgeo⟩ := geo_pts G o w
  have claim : ∀ j ≤ m, ∀ P : G.Pt, (P : E k) = p j → Q P := by
    intro j
    induction j with
    | zero => intro _ P hP; rw [show P = o from Subtype.ext (hP.trans h0)]; exact hQo
    | succ j ih =>
      intro hj P hP
      obtain ⟨e, he, hpj, hpj1⟩ := hw j (by omega)
      set Δ := p (j + 1) - p j
      obtain ⟨R, hR⟩ := exists_nat_gt (‖Δ‖ / δ)
      have hR0 : (0:ℝ) < R := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hδ.le) hR
      have hpt : ∀ r : ℕ, r ≤ R → p j + ((r : ℝ) / R) • Δ ∈ G.carrier := fun r hr =>
        Set.mem_biUnion he (seg_combo hpj hpj1 ⟨by positivity,
          (div_le_one hR0).2 (by exact_mod_cast hr)⟩)
      have inner : ∀ r : ℕ, r ≤ R → ∀ P : G.Pt, (P : E k) = p j + ((r : ℝ) / R) • Δ → Q P := by
        intro r
        induction r with
        | zero => intro _ P hP; exact ih (by omega) P (by simpa using hP)
        | succ r ihr =>
          intro hr P' hP'
          have hr' : r ≤ R := by omega
          set P : G.Pt := ⟨p j + ((r : ℝ) / R) • Δ, hpt r hr'⟩
          have hQP := ihr hr' P rfl
          have hl : (r : ℝ) / R ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by positivity, (div_le_one hR0).2 (by exact_mod_cast hr')⟩
          have hl' : ((r + 1 : ℕ) : ℝ) / R ∈ Set.Icc (0:ℝ) 1 :=
            ⟨by positivity, (div_le_one hR0).2 (by exact_mod_cast hr)⟩
          apply hstep P P' (hgeo j (by omega) _ hl P rfl) (hgeo j (by omega) _ hl' P' hP') _ hQP
          calc G.dist P P' ≤ ‖(P : E k) - P'‖ :=
                dist_le_norm_of_edge G P P' e he (seg_combo hpj hpj1 hl) (hP' ▸ seg_combo hpj hpj1 hl')
            _ = ‖Δ‖ / R := by
                simp only [P, hP']
                rw [show p j + ((r : ℝ) / R) • Δ - (p j + (((r + 1 : ℕ) : ℝ) / R) • Δ) =
                  (-(1 / (R : ℝ))) • Δ by push_cast; module, norm_smul, Real.norm_eq_abs, abs_neg,
                  abs_of_pos (by positivity)]
                ring
            _ < δ := by rw [div_lt_iff₀ hR0]; rw [div_lt_iff₀ hδ] at hR; linarith
      exact inner R le_rfl P (by rw [hP, div_self hR0.ne', one_smul]; simp [Δ])
  exact claim m le_rfl w hm.symm

end SPFGGeo

-- ===== Geo30 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k n : ℕ}

/-- an abstract decomposition of a graph at a cut point `w`, with gated sides -/
structure Side (G : MetricGraph k) (M : Profile G n → G.Pt) where
  In1 : G.Pt → Prop
  In2 : G.Pt → Prop
  w : G.Pt
  P1 : G.Pt → G.Pt
  P2 : G.Pt → G.Pt
  cover : ∀ p, In1 p ∨ In2 p
  inter : ∀ p, In1 p → In2 p → p = w
  w1 : In1 w
  w2 : In2 w
  P1_in : ∀ p, In1 p → P1 p = p
  P1_out : ∀ p, ¬ In1 p → P1 p = w
  P2_in : ∀ p, In2 p → P2 p = p
  P2_out : ∀ p, ¬ In2 p → P2 p = w
  sum3 : ∀ p q, In1 p → In2 q → G.dist p q = G.dist p w + G.dist w q
  gate1 : ∀ x : Profile G n, (∀ j, In1 (x j)) → ∀ i y z, In1 y → In1 z →
    G.dist y (M (update x i z)) =
      G.dist y (M (update x i y)) + G.dist (M (update x i y)) (M (update x i z))
  gate2 : ∀ x : Profile G n, (∀ j, In2 (x j)) → ∀ i y z, In2 y → In2 z →
    G.dist y (M (update x i z)) =
      G.dist y (M (update x i y)) + G.dist (M (update x i y)) (M (update x i z))

namespace Side

variable {G : MetricGraph k} {M : Profile G n → G.Pt} (S : Side G M)

def swap : Side G M where
  In1 := S.In2
  In2 := S.In1
  w := S.w
  P1 := S.P2
  P2 := S.P1
  cover := fun p => (S.cover p).symm
  inter := fun p h1 h2 => S.inter p h2 h1
  w1 := S.w2
  w2 := S.w1
  P1_in := S.P2_in
  P1_out := S.P2_out
  P2_in := S.P1_in
  P2_out := S.P1_out
  sum3 := fun p q h1 h2 => by
    rw [G.dist_comm p q, S.sum3 q p h2 h1, G.dist_comm q S.w, G.dist_comm S.w p]; ring
  gate1 := S.gate2
  gate2 := S.gate1

lemma swap_swap : S.swap.swap = S := rfl

lemma P1_mem (p : G.Pt) : S.In1 (S.P1 p) := by
  by_cases h : S.In1 p
  · rw [S.P1_in p h]; exact h
  · rw [S.P1_out p h]; exact S.w1

lemma P2_of1 (p : G.Pt) (h : S.In1 p) : S.P2 p = S.w := by
  by_cases h2 : S.In2 p
  · rw [S.P2_in p h2]; exact S.inter p h h2
  · exact S.P2_out p h2

lemma not1 {p : G.Pt} (h : ¬ S.In1 p) : S.In2 p ∧ p ≠ S.w :=
  ⟨(S.cover p).resolve_left h, fun e => h (e ▸ S.w1)⟩

/-- outcomes of profiles inside side 1 stay in side 1 -/
lemma In1_M (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n)
    (hx : ∀ j, S.In1 (x j)) : S.In1 (M x) := by
  by_contra h
  obtain ⟨h2, hw⟩ := S.not1 h
  exact lemma2 G M hSP hM x S.w (Ne.symm hw) (fun j => (S.sum3 (x j) (M x) (hx j) h2).symm)

def A (x : Profile G n) : G.Pt := M (fun j => S.P1 (x j))

def Φ1 (x : Profile G n) : Prop := S.In1 (M x) → M x = S.A x

def Φ3 (x : Profile G n) : Prop := S.A x = S.w ∨ S.swap.A x = S.w

open Classical in
noncomputable def Nw (x : Profile G n) : ℕ := (Finset.univ.filter fun j => x j ≠ S.w).card

open Classical in
noncomputable def m2 (x : Profile G n) : ℕ :=
  (Finset.univ.filter fun j => S.In2 (x j) ∧ x j ≠ S.w).card

lemma A_upd (x : Profile G n) (i : Fin n) (t : G.Pt) (ht : S.In1 t) :
    S.A (update x i t) = M (update (fun j => S.P1 (x j)) i t) := by
  unfold A; congr 1; funext j
  by_cases h : j = i
  · subst h; simp [S.P1_in t ht]
  · simp [update_of_ne h]

end Side

lemma card_upd_le {α : Type*} (R : α → Prop) [DecidablePred R] (f : Fin n → α) (j : Fin n) (v : α)
    (h : R v → R (f j)) :
    (Finset.univ.filter fun i => R (update f j v i)).card ≤ (Finset.univ.filter fun i => R (f i)).card := by
  classical
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  by_cases hij : i = j
  · subst hij; simp at hi; exact h hi
  · rwa [update_of_ne hij] at hi

lemma card_upd_lt {α : Type*} (R : α → Prop) [DecidablePred R] (f : Fin n → α) (j : Fin n) (v : α)
    (h1 : R (f j)) (h2 : ¬ R v) :
    (Finset.univ.filter fun i => R (update f j v i)).card < (Finset.univ.filter fun i => R (f i)).card := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, by simp [h1], by simp [h2]⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases hij : i = j
    · subst hij; simp at hi; exact absurd hi h2
    · rwa [update_of_ne hij] at hi

lemma mto {G : MetricGraph k} {M : Profile G n → G.Pt} (hSP : IsSP G M) (x : Profile G n) (i : Fin n) :
    M (update x i (M x)) = M x := by
  have := hSP (update x i (M x)) i (x i)
  rw [update_self, update_idem, update_eq_self, dist_self] at this
  exact eq_of_dist_eq_zero G _ _ (le_antisymm this (dist_nonneg G _ _))

namespace Side

variable {G : MetricGraph k} {M : Profile G n → G.Pt} (S : Side G M)

/-- **flip exclusion**: an agent cannot flip the outcome from side 1 to side 2 by moving to `w` -/
lemma flip_excl (hSP : IsSP G M) (x : Profile G n) (i : Fin n) (o : G.Pt) (ho : S.In1 o)
    (how : o ≠ S.w) (hMo : M (update x i o) = o) (hc1 : ¬ S.In1 (M (update x i S.w)))
    (hΦ : ∀ t, S.In1 t → S.In1 (M (update x i t)) →
      M (update x i t) = M (update (fun j => S.P1 (x j)) i t))
    (hhw : M (update (fun j => S.P1 (x j)) i S.w) = S.w) : False := by
  set u : Profile G n := fun j => S.P1 (x j) with hu
  have huI : ∀ j, S.In1 (u j) := fun j => S.P1_mem _
  have hho : M (update u i o) = o := by
    have := hΦ o ho (by rw [hMo]; exact ho); rw [hMo] at this; exact this.symm
  set c := M (update x i S.w) with hc
  obtain ⟨hc2, hcw⟩ := S.not1 hc1
  set δ := G.dist S.w c with hδ
  have hδ0 : 0 < δ := by
    rcases (dist_nonneg G S.w c).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (eq_of_dist_eq_zero G _ _ h'.symm).symm hcw
  -- geodesic points lie in side 1 and are fixed by `h`
  have geo1 : ∀ t, G.dist o t + G.dist t S.w = G.dist o S.w → S.In1 t := by
    intro t ht
    by_contra h1
    obtain ⟨h2, htw⟩ := S.not1 h1
    have := S.sum3 o t ho h2
    have h3 : G.dist t S.w = 0 := by rw [G.dist_comm S.w t] at this; linarith [dist_nonneg G t S.w]
    exact htw (eq_of_dist_eq_zero G _ _ h3)
  have hfix : ∀ t, G.dist o t + G.dist t S.w = G.dist o S.w → M (update u i t) = t := by
    intro t ht
    have ht1 := geo1 t ht
    have g1 := S.gate1 u huI i t o ht1 ho
    have g2 := S.gate1 u huI i t S.w ht1 S.w1
    rw [hho] at g1; rw [hhw] at g2
    have tri := G.dist_triangle o (M (update u i t)) S.w
    rw [G.dist_comm t o, G.dist_comm (M (update u i t)) o] at g1
    have : G.dist t (M (update u i t)) = 0 := by linarith [dist_nonneg G t (M (update u i t))]
    exact (eq_of_dist_eq_zero G _ _ this).symm
  apply hcw
  have key := geo_chain G o S.w hδ0 (fun t => M (update x i t) = t) hMo (by
    intro t t' ht ht' hdt hQ
    have ht1' := geo1 t' ht'
    by_cases hr : S.In1 (M (update x i t'))
    · rw [hΦ t' ht1' hr]; exact hfix t' ht'
    · exfalso
      obtain ⟨hr2, -⟩ := S.not1 hr
      have s1 := hSP (update x i S.w) i t'
      rw [update_self, update_idem, ← hc] at s1
      have s2 := hSP (update x i t') i t
      rw [update_self, update_idem, hQ] at s2
      have e1 := S.sum3 t' (M (update x i t')) ht1' hr2
      rw [G.dist_comm (M (update x i t')) t', e1] at s2
      rw [G.dist_comm c S.w, G.dist_comm (M (update x i t')) S.w] at s1
      linarith [dist_nonneg G t' S.w])
  rw [← key]

end Side

end SPFGGeo

-- ===== Geo31 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k n : ℕ}

namespace Side

variable {G : MetricGraph k} {M : Profile G n → G.Pt} (S : Side G M)

def Φall (x : Profile G n) : Prop := S.Φ1 x ∧ S.swap.Φ1 x ∧ S.Φ3 x

lemma swap_Φall (x : Profile G n) : S.swap.Φall x ↔ S.Φall x := by
  unfold Φall Φ3
  rw [swap_swap]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩

lemma swap_Nw (x : Profile G n) : S.swap.Nw x = S.Nw x := rfl

lemma Nw_upd_le (x : Profile G n) (j : Fin n) (t : G.Pt) (h : t ≠ S.w → x j ≠ S.w) :
    S.Nw (update x j t) ≤ S.Nw x := by
  classical
  unfold Nw
  convert card_upd_le (fun p : G.Pt => p ≠ S.w) x j t h

lemma Nw_upd_lt (x : Profile G n) (j : Fin n) (h : x j ≠ S.w) :
    S.Nw (update x j S.w) < S.Nw x := by
  classical
  unfold Nw
  convert card_upd_lt (fun p : G.Pt => p ≠ S.w) x j S.w h (by simp)

lemma m2_upd_lt (x : Profile G n) (j : Fin n) (t : G.Pt) (h1 : S.In2 (x j) ∧ x j ≠ S.w)
    (ht : S.In1 t) : S.m2 (update x j t) < S.m2 x := by
  classical
  unfold m2
  convert card_upd_lt (fun p : G.Pt => S.In2 p ∧ p ≠ S.w) x j t h1
    (fun h => h.2 (S.inter t ht h.1))

lemma P1_upd (x : Profile G n) (j : Fin n) (h : S.P1 (x j) = S.w) :
    (fun i => S.P1 (update x j S.w i)) = fun i => S.P1 (x i) := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [S.P1_in S.w S.w1, h]
  · simp [update_of_ne hi]

lemma upd_P1_w (x : Profile G n) (j : Fin n) (h : S.P1 (x j) = S.w) :
    update (fun i => S.P1 (x i)) j S.w = fun i => S.P1 (x i) := by
  rw [← h]; exact update_eq_self _ _

/-- the inductive step for `Φ1` -/
lemma phi1_step (hSP : IsSP G M) (x : Profile G n)
    (hlow : ∀ x', S.Nw x' < S.Nw x → S.Φall x')
    (hsame : ∀ x', S.Nw x' ≤ S.Nw x → S.m2 x' < S.m2 x → S.Φ1 x') : S.Φ1 x := by
  intro ho
  set o := M x with hodef
  by_cases hall : ∀ j, S.In1 (x j)
  · show M x = M _; congr 1; funext j; exact (S.P1_in _ (hall j)).symm
  push Not at hall
  obtain ⟨j, hj⟩ := hall
  obtain ⟨hj2, hjw⟩ := S.not1 hj
  set u : Profile G n := fun i => S.P1 (x i) with hu
  have hPj : S.P1 (x j) = S.w := S.P1_out _ hj
  set x' := update x j S.w with hx'
  obtain ⟨hΦ1', hΦ2', hΦ3'⟩ := hlow x' (S.Nw_upd_lt x j hjw)
  have hΦ : ∀ t, S.In1 t → S.In1 (M (update x j t)) → M (update x j t) = M (update u j t) := by
    intro t ht hr
    have := hsame (update x j t) (S.Nw_upd_le x j t (fun _ => hjw)) (S.m2_upd_lt x j t ⟨hj2, hjw⟩ ht) hr
    rw [this, S.A_upd x j t ht]
  have hMo : M (update x j o) = o := mto hSP x j
  set c := M x' with hc
  have hAx : S.A x' = M u := by unfold A; rw [S.P1_upd x j hPj]
  by_cases hc1 : S.In1 c
  · have hcu : c = M u := by rw [hc, hΦ1' hc1, hAx]
    have s1 := hSP x j S.w
    rw [← hx', ← hc] at s1
    have s2 := hSP x' j (x j)
    rw [hx', update_self, update_idem, update_eq_self, ← hx', ← hc, ← hodef] at s2
    rw [S.sum3 o (x j) ho hj2, S.sum3 c (x j) hc1 hj2] at s1
    rw [G.dist_comm c S.w, G.dist_comm o S.w] at s2
    have hg := S.gate1 u (fun i => S.P1_mem _) j S.w o S.w1 ho
    rw [← hΦ o ho (by rw [hMo]; exact ho), hMo, S.upd_P1_w x j hPj, ← hcu] at hg
    rw [G.dist_comm o S.w, G.dist_comm c S.w] at s1
    have : G.dist c o = 0 := by linarith
    show o = M u
    rw [← hcu]; exact (eq_of_dist_eq_zero G _ _ this).symm
  · obtain ⟨hc2, hcw⟩ := S.not1 hc1
    have hcB : c = S.swap.A x' := hΦ2' hc2
    have hAw : M u = S.w := by
      rcases hΦ3' with h | h
      · rw [← hAx]; exact h
      · exact absurd (hcB.trans h) hcw
    show o = M u
    rw [hAw]
    by_contra how
    exact S.flip_excl hSP x j o ho how hMo hc1 hΦ (by rw [S.upd_P1_w x j hPj]; exact hAw)

/-- one half of `Φ3`: no core profile with outcome in side 1 -/
lemma phi3_half (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n)
    (hΦ1N : ∀ x', S.Nw x' ≤ S.Nw x → S.Φ1 x')
    (hlow : ∀ x', S.Nw x' < S.Nw x → S.Φall x')
    (hA : S.A x ≠ S.w) (hB : S.swap.A x ≠ S.w) (ho : S.In1 (M x)) : False := by
  set o := M x with hodef
  have hoA : o = S.A x := hΦ1N x le_rfl ho
  have how : o ≠ S.w := hoA ▸ hA
  set u : Profile G n := fun i => S.P1 (x i) with hu
  have hex : ∃ i, S.In1 (x i) ∧ x i ≠ S.w := by
    by_contra hne
    push Not at hne
    apply hA
    have : u = fun _ => S.w := by
      funext i
      by_cases h : S.In1 (x i)
      · show S.P1 (x i) = S.w; rw [S.P1_in _ h]; exact hne i h
      · show S.P1 (x i) = S.w; exact S.P1_out _ h
    unfold A; rw [← hu, this]; exact unanimity G M hSP hM S.w
  obtain ⟨i, hi1, hiw⟩ := hex
  set x'' := update x i S.w with hx''
  obtain ⟨hΦ1'', hΦ2'', hΦ3''⟩ := hlow x'' (S.Nw_upd_lt x i hiw)
  have hP2i : S.P2 (x i) = S.w := S.P2_of1 _ hi1
  have hB'' : S.swap.A x'' = S.swap.A x := by
    unfold A; congr 1; exact S.swap.P1_upd x i hP2i
  have hA'' : S.A x'' = S.w := by
    rcases hΦ3'' with h | h
    · exact h
    · exact absurd (hB''.symm.trans h) hB
  set c := M x'' with hc
  have hc1 : ¬ S.In1 c := by
    intro h1
    have h2 : c = S.w := (hΦ1'' h1).trans hA''
    have : c = S.swap.A x'' := hΦ2'' (by show S.In2 c; rw [h2]; exact S.w2)
    exact hB (hB''.symm.trans (this.symm.trans h2))
  have hPi : S.P1 S.w = S.w := S.P1_in _ S.w1
  apply S.flip_excl hSP x i o ho how (mto hSP x i) hc1
  · intro t ht hr
    rw [hΦ1N (update x i t) (S.Nw_upd_le x i t (fun _ => hiw)) hr, S.A_upd x i t ht]
  · have : update u i S.w = fun j => S.P1 (x'' j) := by
      funext j; by_cases hj : j = i
      · subst hj; simp [hx'', hPi]
      · rw [hx'', update_of_ne hj, update_of_ne hj]
    rw [this]; exact hA''

end Side

end SPFGGeo

-- ===== Geo32 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k n : ℕ}

namespace Side

variable {G : MetricGraph k} {M : Profile G n → G.Pt} (S : Side G M)

theorem phi_all (hSP : IsSP G M) (hM : Function.Surjective M) : ∀ x, S.Φall x := by
  suffices h : ∀ N, ∀ x, S.Nw x = N → S.Φall x from fun x => h _ x rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x hx
  have hlowN : ∀ x', S.Nw x' < N → S.Φall x' := fun x' h => ih _ h x' rfl
  have gen : ∀ T : Side G M, (∀ x', T.Nw x' < N → T.Φall x') → ∀ x', T.Nw x' ≤ N → T.Φ1 x' := by
    intro T hlowT x' hx'
    suffices hm : ∀ m, ∀ x', T.Nw x' ≤ N → T.m2 x' = m → T.Φ1 x' from hm _ x' hx' rfl
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    intro x' hx' hm
    rcases lt_or_eq_of_le hx' with hlt | heq
    · exact (hlowT x' hlt).1
    · apply T.phi1_step hSP x'
      · intro x'' h; exact hlowT x'' (heq ▸ h)
      · intro x'' h1 h2; exact ihm _ (hm ▸ h2) x'' (heq ▸ h1) rfl
  have h1 := gen S hlowN
  have h2 := gen S.swap (fun x' h => (S.swap_Φall x').2 (hlowN x' h))
  refine ⟨h1 x hx.le, h2 x hx.le, ?_⟩
  by_contra h3
  unfold Φ3 at h3
  push Not at h3
  obtain ⟨hA, hB⟩ := h3
  rcases S.cover (M x) with ho | ho
  · exact S.phi3_half hSP hM x (fun x' h => h1 x' (h.trans hx.le))
      (fun x' h => hlowN x' (hx ▸ h)) hA hB ho
  · exact S.swap.phi3_half hSP hM x (fun x' h => h2 x' (h.trans hx.le))
      (fun x' h => (S.swap_Φall x').2 (hlowN x' (hx ▸ h))) hB hA ho

lemma proj (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n) :
    S.P1 (M x) = S.A x ∧ S.P2 (M x) = S.swap.A x := by
  obtain ⟨h1, h2, h3⟩ := S.phi_all hSP hM x
  by_cases ho : S.In1 (M x)
  · refine ⟨by rw [S.P1_in _ ho]; exact h1 ho, ?_⟩
    by_cases ho2 : S.In2 (M x)
    · rw [S.P2_in _ ho2]; exact h2 ho2
    · rw [S.P2_out _ ho2]
      rcases h3 with h | h
      · exact absurd ((h1 ho).trans h ▸ S.w2) ho2
      · exact h.symm
  · have ho2 : S.In2 (M x) := (S.cover _).resolve_left ho
    refine ⟨?_, by rw [S.P2_in _ ho2]; exact h2 ho2⟩
    rw [S.P1_out _ ho]
    rcases h3 with h | h
    · exact h.symm
    · exact absurd ((h2 ho2).trans h ▸ S.w1) ho

lemma dsum (p q : G.Pt) :
    G.dist p q = G.dist (S.P1 p) (S.P1 q) + G.dist (S.P2 p) (S.P2 q) := by
  by_cases hp : S.In1 p <;> by_cases hq : S.In1 q
  · rw [S.P1_in _ hp, S.P1_in _ hq, S.P2_of1 _ hp, S.P2_of1 _ hq, dist_self, add_zero]
  · have hq2 := (S.cover q).resolve_left hq
    rw [S.P1_in _ hp, S.P1_out _ hq, S.P2_of1 _ hp, S.P2_in _ hq2]
    exact S.sum3 p q hp hq2
  · have hp2 := (S.cover p).resolve_left hp
    rw [S.P1_out _ hp, S.P1_in _ hq, S.P2_in _ hp2, S.P2_of1 _ hq]
    rw [G.dist_comm p q, S.sum3 q p hq hp2, G.dist_comm S.w q, G.dist_comm p S.w, add_comm]
  · have hp2 := (S.cover p).resolve_left hp
    have hq2 := (S.cover q).resolve_left hq
    rw [S.P1_out _ hp, S.P1_out _ hq, S.P2_in _ hp2, S.P2_in _ hq2, dist_self, zero_add]

include S in
theorem gate (hSP : IsSP G M) (hM : Function.Surjective M) : Gate G M := by
  intro x i y z
  set u1 : Profile G n := fun j => S.P1 (x j)
  set u2 : Profile G n := fun j => S.P2 (x j)
  have key1 : ∀ t, S.P1 (M (update x i t)) = M (update u1 i (S.P1 t)) := by
    intro t; rw [(S.proj hSP hM _).1]; unfold A; congr 1; funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [update_of_ne hj, u1]
  have key2 : ∀ t, S.P2 (M (update x i t)) = M (update u2 i (S.P2 t)) := by
    intro t; rw [(S.proj hSP hM _).2]; unfold A; congr 1; funext j
    by_cases hj : j = i
    · subst hj; simp [swap]
    · simp [update_of_ne hj, u2, swap]
  have g1 := S.gate1 u1 (fun j => S.P1_mem _) i (S.P1 y) (S.P1 z) (S.P1_mem _) (S.P1_mem _)
  have g2 := S.gate2 u2 (fun j => S.swap.P1_mem _) i (S.P2 y) (S.P2 z) (S.swap.P1_mem _)
    (S.swap.P1_mem _)
  rw [S.dsum y (M (update x i z)), S.dsum y (M (update x i y)),
    S.dsum (M (update x i y)) (M (update x i z)), key1 z, key1 y, key2 z, key2 y, g1, g2]
  ring

end Side

end SPFGGeo

-- ===== Geo33 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k n : ℕ}

/-- carrier of a set of edges -/
def car (E1 : Finset (E k × E k)) : Set (E k) := ⋃ e ∈ E1, segment ℝ e.1 e.2

lemma isClosed_car (E1 : Finset (E k × E k)) : IsClosed (car E1) := by
  apply IsCompact.isClosed
  exact E1.finite_toSet.isCompact_biUnion (fun e _ => by
    rw [← convexHull_pair]; exact (Set.toFinite ({e.1, e.2} : Set (E k))).isCompact_convexHull ℝ)

lemma topo_piece {A B : Set (E k)} {w : E k} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : IsPreconnected (A ∪ B)) (hwA : w ∈ A) (hwB : w ∈ B) (hint : ∀ p ∈ A, p ∈ B → p = w) :
    IsPreconnected A := by
  rw [isPreconnected_closed_iff] at hAB ⊢
  intro t t' ht ht' hcov hne hne'
  rcases hcov hwA with hwt | hwt'
  · obtain ⟨p, hp, hpT, hpT'⟩ := hAB (t ∪ B) (t' ∩ A) (ht.union hB) (ht'.inter hA)
      (by
        intro p hp
        rcases hp with hp | hp
        · rcases hcov hp with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, hp⟩
        · exact Or.inl (Or.inr hp))
      ⟨w, Or.inl hwA, Or.inl hwt⟩
      (by obtain ⟨q, hq, hq'⟩ := hne'; exact ⟨q, Or.inl hq, hq', hq⟩)
    refine ⟨p, hpT'.2, ?_, hpT'.1⟩
    rcases hpT with h | h
    · exact h
    · rw [hint p hpT'.2 h]; exact hwt
  · obtain ⟨p, hp, hpT, hpT'⟩ := hAB (t ∩ A) (t' ∪ B) (ht.inter hA) (ht'.union hB)
      (by
        intro p hp
        rcases hp with hp | hp
        · rcases hcov hp with h | h
          · exact Or.inl ⟨h, hp⟩
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr hp))
      (by obtain ⟨q, hq, hq'⟩ := hne; exact ⟨q, Or.inl hq, hq', hq⟩)
      ⟨w, Or.inl hwA, Or.inl hwt'⟩
    refine ⟨p, hpT.2, hpT.1, ?_⟩
    rcases hpT' with h | h
    · exact h
    · rw [hint p hpT.2 h]; exact hwt'

/-- a decomposition of the edge set whose carriers meet in a single point -/
structure Split (G : MetricGraph k) where
  E1 : Finset (E k × E k)
  E2 : Finset (E k × E k)
  w : E k
  sub1 : E1 ⊆ G.edges
  sub2 : E2 ⊆ G.edges
  cov : ∀ e ∈ G.edges, e ∈ E1 ∨ e ∈ E2
  ne1 : E1.Nonempty
  ne2 : E2.Nonempty
  inter : ∀ p, p ∈ car E1 → p ∈ car E2 → p = w
  w1 : w ∈ car E1
  w2 : w ∈ car E2

namespace Split

variable {G : MetricGraph k} (S : Split G)

def swap : Split G where
  E1 := S.E2
  E2 := S.E1
  w := S.w
  sub1 := S.sub2
  sub2 := S.sub1
  cov := fun e he => (S.cov e he).symm
  ne1 := S.ne2
  ne2 := S.ne1
  inter := fun p h1 h2 => S.inter p h2 h1
  w1 := S.w2
  w2 := S.w1

lemma car_G : G.carrier = car S.E1 ∪ car S.E2 := by
  ext p
  simp only [MetricGraph.carrier, car, Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨e, he, hp⟩
    rcases S.cov e he with h | h
    · exact Or.inl ⟨e, h, hp⟩
    · exact Or.inr ⟨e, h, hp⟩
  · rintro (⟨e, he, hp⟩ | ⟨e, he, hp⟩)
    · exact ⟨e, S.sub1 he, hp⟩
    · exact ⟨e, S.sub2 he, hp⟩

/-- the first piece as a metric graph -/
def G1 : MetricGraph k where
  edges := S.E1
  edges_nonempty := S.ne1
  fst_ne_snd := fun e he => G.fst_ne_snd e (S.sub1 he)
  meet := fun e he e' he' hne => G.meet e (S.sub1 he) e' (S.sub1 he') hne
  connected := by
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := S.ne1
      exact ⟨e.1, Set.mem_biUnion he (left_mem_segment ℝ e.1 e.2)⟩
    · have hG := G.connected.isPreconnected
      have : (⋃ e ∈ G.edges, segment ℝ e.1 e.2) = car S.E1 ∪ car S.E2 := S.car_G
      rw [this] at hG
      exact topo_piece (isClosed_car _) (isClosed_car _) hG S.w1 S.w2 S.inter

lemma G1_carrier : S.G1.carrier = car S.E1 := rfl

lemma card_lt : S.E1.card < G.edges.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset S.sub1]
  obtain ⟨e, he⟩ := S.ne2
  refine ⟨e, S.sub2 he, fun h1 => ?_⟩
  have hne := G.fst_ne_snd e (S.sub2 he)
  have a1 := S.inter e.1 (Set.mem_biUnion h1 (left_mem_segment ℝ e.1 e.2))
    (Set.mem_biUnion he (left_mem_segment ℝ e.1 e.2))
  have a2 := S.inter e.2 (Set.mem_biUnion h1 (right_mem_segment ℝ e.1 e.2))
    (Set.mem_biUnion he (right_mem_segment ℝ e.1 e.2))
  exact hne (a1.trans a2.symm)

/-- projection onto the first piece -/
noncomputable def f1 (p : E k) : E k := by
  classical exact if p ∈ car S.E1 then p else S.w

lemma f1_mem (p : E k) : S.f1 p ∈ car S.E1 := by
  unfold f1; split_ifs with h
  · exact h
  · exact S.w1

lemma f1_in {p : E k} (h : p ∈ car S.E1) : S.f1 p = p := by unfold f1; simp [h]

lemma f1_out2 {p : E k} (h : p ∈ car S.E2) : S.f1 p = S.w := by
  unfold f1; split_ifs with h1
  · exact S.inter p h1 h
  · rfl

/-- a common edge of `G` for two points gives a common edge of the first piece after projecting,
  and the step length splits -/
lemma step (a b : E k) (h : ∃ e ∈ G.edges, a ∈ segment ℝ e.1 e.2 ∧ b ∈ segment ℝ e.1 e.2) :
    (∃ e ∈ S.E1, S.f1 a ∈ segment ℝ e.1 e.2 ∧ S.f1 b ∈ segment ℝ e.1 e.2) ∧
      ‖b - a‖ = ‖S.f1 b - S.f1 a‖ + ‖S.swap.f1 b - S.swap.f1 a‖ := by
  obtain ⟨e, he, ha, hb⟩ := h
  rcases S.cov e he with h1 | h2
  · have ha1 : a ∈ car S.E1 := Set.mem_biUnion h1 ha
    have hb1 : b ∈ car S.E1 := Set.mem_biUnion h1 hb
    refine ⟨⟨e, h1, by rw [S.f1_in ha1]; exact ha, by rw [S.f1_in hb1]; exact hb⟩, ?_⟩
    rw [S.f1_in ha1, S.f1_in hb1, S.swap.f1_out2 ha1, S.swap.f1_out2 hb1, sub_self, norm_zero, add_zero]
  · have ha2 : a ∈ car S.E2 := Set.mem_biUnion h2 ha
    have hb2 : b ∈ car S.E2 := Set.mem_biUnion h2 hb
    obtain ⟨e1, he1, hw1⟩ := Set.mem_iUnion₂.1 S.w1
    refine ⟨⟨e1, he1, by rw [S.f1_out2 ha2]; exact hw1, by rw [S.f1_out2 hb2]; exact hw1⟩, ?_⟩
    rw [S.f1_out2 ha2, S.f1_out2 hb2, sub_self, norm_zero, zero_add]
    rw [show S.swap.f1 b = b from S.swap.f1_in hb2, show S.swap.f1 a = a from S.swap.f1_in ha2]

/-- inclusion of points of the first piece -/
def ι (p : S.G1.Pt) : G.Pt := ⟨p, by rw [S.car_G]; exact Or.inl p.2⟩

/-- distances inside the first piece agree -/
lemma dist_G1 (a b : S.G1.Pt) : G.dist (S.ι a) (S.ι b) = S.G1.dist a b := by
  apply le_antisymm
  · obtain ⟨m, p, h0, hm, hw, hL⟩ := S.G1.exists_walk_eq_dist a b
    rw [← hL]
    exact G.dist_le_walk _ _ m p h0 hm (fun j hj => by
      obtain ⟨e, he, h1, h2⟩ := hw j hj; exact ⟨e, S.sub1 he, h1, h2⟩)
  · obtain ⟨m, p, h0, hm, hw, hL⟩ := G.exists_walk_eq_dist (S.ι a) (S.ι b)
    rw [← hL]
    calc S.G1.dist a b ≤ ∑ j ∈ Finset.range m, ‖S.f1 (p (j + 1)) - S.f1 (p j)‖ :=
          S.G1.dist_le_walk a b m (fun j => S.f1 (p j)) (by rw [h0]; exact S.f1_in a.2)
            (by rw [hm]; exact S.f1_in b.2) (fun j hj => (S.step _ _ (hw j hj)).1)
      _ ≤ ∑ j ∈ Finset.range m, ‖p (j + 1) - p j‖ := Finset.sum_le_sum (fun j hj => by
          rw [(S.step _ _ (hw j (Finset.mem_range.1 hj))).2]; linarith [norm_nonneg
            (S.swap.f1 (p (j + 1)) - S.swap.f1 (p j))])

/-- the cut point as a point of `G` -/
def wG : G.Pt := ⟨S.w, by rw [S.car_G]; exact Or.inl S.w1⟩

/-- distances across the cut point add up -/
lemma sum3 (p q : G.Pt) (hp : (p : E k) ∈ car S.E1) (hq : (q : E k) ∈ car S.E2) :
    G.dist p q = G.dist p S.wG + G.dist S.wG q := by
  apply le_antisymm (G.dist_triangle _ _ _)
  obtain ⟨m, r, h0, hm, hw, hL⟩ := G.exists_walk_eq_dist p q
  have d1 := G.dist_le_walk p S.wG m (fun j => S.f1 (r j)) (by rw [h0]; exact S.f1_in hp)
    (by rw [hm]; exact S.f1_out2 hq) (fun j hj => by
      obtain ⟨e, he, h1, h2⟩ := (S.step _ _ (hw j hj)).1; exact ⟨e, S.sub1 he, h1, h2⟩)
  have d2 := G.dist_le_walk S.wG q m (fun j => S.swap.f1 (r j)) (by rw [h0]; exact S.swap.f1_out2 hp)
    (by rw [hm]; exact S.swap.f1_in hq) (fun j hj => by
      obtain ⟨e, he, h1, h2⟩ := (S.swap.step _ _ (hw j hj)).1; exact ⟨e, S.sub2 he, h1, h2⟩)
  have hsplit : ∑ j ∈ Finset.range m, ‖r (j + 1) - r j‖ =
      ∑ j ∈ Finset.range m, ‖S.f1 (r (j + 1)) - S.f1 (r j)‖ +
        ∑ j ∈ Finset.range m, ‖S.swap.f1 (r (j + 1)) - S.swap.f1 (r j)‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j hj => (S.step _ _ (hw j (Finset.mem_range.1 hj))).2)
  linarith

end Split

end SPFGGeo

-- ===== Geo34 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k n : ℕ}

namespace Split

variable {G : MetricGraph k} (S : Split G)

lemma M_in1 (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (x : Profile G n) (hx : ∀ j, ((x j : G.Pt) : E k) ∈ car S.E1) : ((M x : G.Pt) : E k) ∈ car S.E1 := by
  by_contra h
  have h2 : ((M x : G.Pt) : E k) ∈ car S.E2 := by
    exact ((Set.ext_iff.1 S.car_G _).1 (M x).2).resolve_left h
  have hw : S.wG ≠ M x := by
    intro e; apply h; rw [← e]; exact S.w1
  exact lemma2 G M hSP hM x S.wG hw (fun j => (S.sum3 (x j) (M x) (hx j) h2).symm)

/-- the restriction of `M` to the first piece -/
def M1 (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    Profile S.G1 n → S.G1.Pt :=
  fun u => ⟨M (fun j => S.ι (u j)), S.M_in1 M hSP hM _ (fun j => (u j).2)⟩

lemma ι_M1 (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (u : Profile S.G1 n) : S.ι (S.M1 M hSP hM u) = M (fun j => S.ι (u j)) := rfl

lemma ι_upd (u : Profile S.G1 n) (i : Fin n) (z : S.G1.Pt) :
    (fun j => S.ι (update u i z j)) = update (fun j => S.ι (u j)) i (S.ι z) := by
  funext j; by_cases h : j = i
  · subst h; simp
  · simp [update_of_ne h]

lemma M1_sp (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    IsSP S.G1 (S.M1 M hSP hM) := by
  intro u j z
  rw [← S.dist_G1, ← S.dist_G1, S.ι_M1, S.ι_M1, S.ι_upd]
  exact hSP _ j (S.ι z)

lemma M1_onto (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M) :
    Function.Surjective (S.M1 M hSP hM) := by
  intro c
  refine ⟨fun _ => c, Subtype.ext ?_⟩
  have := unanimity G M hSP hM (S.ι c)
  show ((M (fun _ => S.ι c) : G.Pt) : E k) = ((S.ι c : G.Pt) : E k)
  rw [this]

lemma gate_tr (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hg : Gate S.G1 (S.M1 M hSP hM)) (x : Profile G n) (hx : ∀ j, ((x j : G.Pt) : E k) ∈ car S.E1)
    (i : Fin n) (y z : G.Pt) (hy : (y : E k) ∈ car S.E1) (hz : (z : E k) ∈ car S.E1) :
    G.dist y (M (update x i z)) =
      G.dist y (M (update x i y)) + G.dist (M (update x i y)) (M (update x i z)) := by
  set u : Profile S.G1 n := fun j => ⟨x j, hx j⟩
  have hxu : x = fun j => S.ι (u j) := rfl
  have h := hg u i ⟨y, hy⟩ ⟨z, hz⟩
  rw [← S.dist_G1, ← S.dist_G1, ← S.dist_G1, S.ι_M1, S.ι_M1, S.ι_upd, S.ι_upd] at h
  rw [hxu]; exact h

/-- the side structure of a split, given gated pieces -/
noncomputable def side (M : Profile G n → G.Pt) (hSP : IsSP G M) (hM : Function.Surjective M)
    (hg1 : Gate S.G1 (S.M1 M hSP hM)) (hg2 : Gate S.swap.G1 (S.swap.M1 M hSP hM)) : Side G M := by
  classical
  exact {
  In1 := fun p => (p : E k) ∈ car S.E1
  In2 := fun p => (p : E k) ∈ car S.E2
  w := S.wG
  P1 := fun p => if (p : E k) ∈ car S.E1 then p else S.wG
  P2 := fun p => if (p : E k) ∈ car S.E2 then p else S.wG
  cover := fun p => (Set.ext_iff.1 S.car_G _).1 p.2
  inter := fun p h1 h2 => Subtype.ext (S.inter p h1 h2)
  w1 := S.w1
  w2 := S.w2
  P1_in := fun p h => by simp [h]
  P1_out := fun p h => by simp [h]
  P2_in := fun p h => by simp [h]
  P2_out := fun p h => by simp [h]
  sum3 := fun p q h1 h2 => S.sum3 p q h1 h2
  gate1 := fun x hx i y z hy hz => S.gate_tr M hSP hM hg1 x hx i y z hy hz
  gate2 := fun x hx i y z hy hz => S.swap.gate_tr M hSP hM hg2 x hx i y z hy hz }

end Split

/-- **Gluing**: on a split graph, gated pieces give a gated mechanism. -/
theorem gate_split {G : MetricGraph k} (S : Split G) (M : Profile G n → G.Pt) (hSP : IsSP G M)
    (hM : Function.Surjective M)
    (IH1 : ∀ M1 : Profile S.G1 n → S.G1.Pt, IsSP S.G1 M1 → Function.Surjective M1 → Gate S.G1 M1)
    (IH2 : ∀ M2 : Profile S.swap.G1 n → S.swap.G1.Pt, IsSP S.swap.G1 M2 → Function.Surjective M2 →
      Gate S.swap.G1 M2) : Gate G M :=
  (S.side M hSP hM (IH1 _ (S.M1_sp M hSP hM) (S.M1_onto M hSP hM))
    (IH2 _ (S.swap.M1_sp M hSP hM) (S.swap.M1_onto M hSP hM))).gate hSP hM

end SPFGGeo

-- ===== Geo35 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k : ℕ}

/-- `f` joins `a` and `b` -/
def Joins (f : E k × E k) (a b : E k) : Prop := (f.1 = a ∧ f.2 = b) ∨ (f.1 = b ∧ f.2 = a)

/-- an edge path of length `r` inside `F` -/
def IsPath (F : Finset (E k × E k)) (r : ℕ) (f : ℕ → E k × E k) (v : ℕ → E k) : Prop :=
  ∀ i < r, f i ∈ F ∧ Joins (f i) (v i) (v (i + 1))

def Reach (F : Finset (E k × E k)) (a b : E k) : Prop :=
  ∃ r f v, v 0 = a ∧ v r = b ∧ IsPath F r f v

lemma reach_refl (F : Finset (E k × E k)) (a : E k) : Reach F a a :=
  ⟨0, fun _ => (a, a), fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

lemma reach_step {F : Finset (E k × E k)} {a b c : E k} (h : Reach F a b) {f : E k × E k}
    (hf : f ∈ F) (hj : Joins f b c) : Reach F a c := by
  obtain ⟨r, g, v, h0, hr, hp⟩ := h
  refine ⟨r + 1, fun i => if i < r then g i else f, fun i => if i ≤ r then v i else c,
    by simp [h0], by simp, fun i hi => ?_⟩
  by_cases hir : i < r
  · simp only [hir, if_true, show i ≤ r by omega, show i + 1 ≤ r by omega]; exact hp i hir
  · have : i = r := by omega
    subst this
    simp only [lt_irrefl, if_false, le_refl, if_true, show ¬ (i + 1 ≤ i) by omega]
    rw [hr]; exact ⟨hf, hj⟩

lemma joins_other {f : E k × E k} (hf : f.1 ≠ f.2) {a b c : E k} (h1 : Joins f a b) (h2 : Joins f b c) :
    c = a := by
  unfold Joins at h1 h2
  rcases h1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩
  · exact absurd (h2.trans h1'.symm) hf
  · exact h2.symm.trans h1
  · exact h2'.symm.trans h1'
  · exact absurd (h1.trans h2'.symm) hf

/-- a reachable vertex is reachable along a non-backtracking path -/
lemma reach_nb (G : MetricGraph k) {F : Finset (E k × E k)} (hF : F ⊆ G.edges) {a b : E k}
    (h : Reach F a b) : ∃ r f v, v 0 = a ∧ v r = b ∧ IsPath F r f v ∧
      ∀ i, i + 1 < r → f i ≠ f (i + 1) := by
  classical
  have hex : ∃ r, ∃ f v, v 0 = a ∧ v r = b ∧ IsPath F r f v := by
    obtain ⟨r, f, v, h⟩ := h; exact ⟨r, f, v, h⟩
  set r := Nat.find hex
  obtain ⟨f, v, h0, hr, hp⟩ := Nat.find_spec hex
  refine ⟨r, f, v, h0, hr, hp, fun i hi heq => ?_⟩
  have hfi := hp i (by omega)
  have hfi1 := hp (i + 1) hi
  rw [← heq] at hfi1
  have hv : v (i + 2) = v i := joins_other (G.fst_ne_snd _ (hF hfi.1)) hfi.2 hfi1.2
  have hlt : r - 2 < r := by omega
  apply Nat.find_min hex hlt
  refine ⟨fun j => if j < i then f j else f (j + 2), fun j => if j ≤ i then v j else v (j + 2),
    by simp [h0], ?_, fun j hj => ?_⟩
  · by_cases hri : r - 2 ≤ i
    · simp only [hri, if_true]
      have hi' : i = r - 2 := by omega
      rw [← hi', ← hv, show i + 2 = r by omega, hr]
    · simp only [hri, if_false]; rw [show r - 2 + 2 = r by omega, hr]
  · by_cases hji : j < i
    · simp only [hji, if_true, show j ≤ i by omega, show j + 1 ≤ i by omega]; exact hp j (by omega)
    · by_cases hje : j = i
      · subst hje
        simp only [lt_irrefl, if_false, le_refl, if_true, show ¬ (j + 1 ≤ j) by omega]
        have := hp (j + 2) (by omega)
        rw [← hv, show j + 1 + 2 = j + 2 + 1 by ring]; exact this
      · simp only [hji, if_false, show ¬ (j ≤ i) by omega, show ¬ (j + 1 ≤ i) by omega]
        have := hp (j + 2) (by omega)
        rw [show j + 1 + 2 = j + 2 + 1 by ring]; exact this

/-- a partition of the edges whose carriers meet in at most one point is a split -/
noncomputable def split_of_part (G : MetricGraph k) (E1 E2 : Finset (E k × E k))
    (sub1 : E1 ⊆ G.edges) (sub2 : E2 ⊆ G.edges) (cov : ∀ e ∈ G.edges, e ∈ E1 ∨ e ∈ E2)
    (ne1 : E1.Nonempty) (ne2 : E2.Nonempty) (pt : E k)
    (h : ∀ p, p ∈ car E1 → p ∈ car E2 → p = pt) : Split G := by
  have hcar : (⋃ e ∈ G.edges, segment ℝ e.1 e.2) = car E1 ∪ car E2 := by
    ext p; simp only [car, Set.mem_union, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨e, he, hp⟩
      rcases cov e he with h' | h'
      · exact Or.inl ⟨e, h', hp⟩
      · exact Or.inr ⟨e, h', hp⟩
    · rintro (⟨e, he, hp⟩ | ⟨e, he, hp⟩)
      · exact ⟨e, sub1 he, hp⟩
      · exact ⟨e, sub2 he, hp⟩
  have hpc := G.connected.isPreconnected
  rw [hcar, isPreconnected_closed_iff] at hpc
  have hne : (car E1 ∩ car E2).Nonempty := by
    obtain ⟨e1, he1⟩ := ne1
    obtain ⟨e2, he2⟩ := ne2
    obtain ⟨p, -, hp⟩ := hpc (car E1) (car E2) (isClosed_car _) (isClosed_car _) le_rfl
      ⟨e1.1, Or.inl (Set.mem_biUnion he1 (left_mem_segment ℝ _ _)),
        Set.mem_biUnion he1 (left_mem_segment ℝ _ _)⟩
      ⟨e2.1, Or.inr (Set.mem_biUnion he2 (left_mem_segment ℝ _ _)),
        Set.mem_biUnion he2 (left_mem_segment ℝ _ _)⟩
    exact ⟨p, hp⟩
  have hpt : pt ∈ car E1 ∧ pt ∈ car E2 := by
    obtain ⟨p, hp1, hp2⟩ := hne; rw [← h p hp1 hp2]; exact ⟨hp1, hp2⟩
  exact ⟨E1, E2, pt, sub1, sub2, cov, ne1, ne2, h, hpt.1, hpt.2⟩

lemma meet_end (G : MetricGraph k) {f g : E k × E k} (hf : f ∈ G.edges) (hg : g ∈ G.edges)
    (hfg : f ≠ g) {p : E k} (h1 : p ∈ segment ℝ f.1 f.2) (h2 : p ∈ segment ℝ g.1 g.2) :
    (p = f.1 ∨ p = f.2) ∧ (p = g.1 ∨ p = g.2) := by
  have := G.meet f hf g hg hfg ⟨h1, h2⟩
  exact ⟨this.1, this.2⟩

end SPFGGeo

-- ===== Geo36 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k : ℕ}

lemma mem_car {E1 : Finset (E k × E k)} {p : E k} :
    p ∈ car E1 ↔ ∃ f ∈ E1, p ∈ segment ℝ f.1 f.2 := by
  simp [car]

lemma joins_self (f : E k × E k) : Joins f f.1 f.2 := Or.inl ⟨rfl, rfl⟩

lemma reach_other {F : Finset (E k × E k)} {a : E k} {f : E k × E k} (hf : f ∈ F)
    (h : Reach F a f.1 ∨ Reach F a f.2) : Reach F a f.1 ∧ Reach F a f.2 := by
  rcases h with h | h
  · exact ⟨h, reach_step h hf (joins_self f)⟩
  · exact ⟨reach_step h hf (Or.inr ⟨rfl, rfl⟩), h⟩

/-- around a vertex: in a non-split graph the far ends of two edges at `q` are joined
  avoiding `q` -/
lemma reach_vertex (G : MetricGraph k) (hns : Split G → False) {q w1 w2 : E k}
    {e1 e2 : E k × E k} (he1 : e1 ∈ G.edges) (he2 : e2 ∈ G.edges) (h1 : Joins e1 q w1)
    (h2 : Joins e2 q w2) (hne : e1 ≠ e2) :
    Reach (G.edges.filter fun f => f.1 ≠ q ∧ f.2 ≠ q) w2 w1 := by
  classical
  set F := G.edges.filter fun f => f.1 ≠ q ∧ f.2 ≠ q with hF
  by_contra hR
  set Rch : E k → Prop := fun a => Reach F w2 a
  have hw2q : w2 ≠ q := by
    intro h; rcases h2 with ⟨a, b⟩ | ⟨a, b⟩ <;> exact G.fst_ne_snd e2 he2 (by rw [a, b, h])
  have hq : ¬ Rch q := by
    rintro ⟨r, f, v, h0, hr, hp⟩
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0; exact hw2q (h0.symm.trans hr)
    · obtain ⟨hfF, hj⟩ := hp (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega, hr] at hj
      have := (Finset.mem_filter.1 hfF).2
      rcases hj with ⟨-, b⟩ | ⟨b, -⟩
      · exact this.2 b
      · exact this.1 b
  set E1 := G.edges.filter fun f => Rch f.1 ∨ Rch f.2
  set E2 := G.edges.filter fun f => ¬ (Rch f.1 ∨ Rch f.2)
  have he2E1 : e2 ∈ E1 := by
    refine Finset.mem_filter.2 ⟨he2, ?_⟩
    rcases h2 with ⟨-, b⟩ | ⟨b, -⟩
    · right; rw [b]; exact reach_refl F w2
    · left; rw [b]; exact reach_refl F w2
  have he1E2 : e1 ∈ E2 := by
    refine Finset.mem_filter.2 ⟨he1, ?_⟩
    rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a, b]; rintro (h | h); exacts [hq h, hR h]
    · rw [a, b]; rintro (h | h); exacts [hR h, hq h]
  apply hns
  refine split_of_part G E1 E2 (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (fun e he => by by_cases h : Rch e.1 ∨ Rch e.2
                    · exact Or.inl (Finset.mem_filter.2 ⟨he, h⟩)
                    · exact Or.inr (Finset.mem_filter.2 ⟨he, h⟩))
    ⟨e2, he2E1⟩ ⟨e1, he1E2⟩ q ?_
  intro p hp1 hp2
  obtain ⟨f, hf, hpf⟩ := mem_car.1 hp1
  obtain ⟨g, hg, hpg⟩ := mem_car.1 hp2
  have hfE := Finset.mem_filter.1 hf
  have hgE := Finset.mem_filter.1 hg
  have hfg : f ≠ g := by rintro rfl; exact hgE.2 hfE.2
  obtain ⟨hpf', hpg'⟩ := meet_end G hfE.1 hgE.1 hfg hpf hpg
  have hpR : ¬ Rch p := by
    intro h; apply hgE.2; rcases hpg' with e | e
    · left; rw [← e]; exact h
    · right; rw [← e]; exact h
  have hfF : f ∉ F := by
    intro hfF
    have := reach_other hfF hfE.2
    rcases hpf' with e | e
    · exact hpR (e ▸ this.1)
    · exact hpR (e ▸ this.2)
  have hfq : f.1 = q ∨ f.2 = q := by
    by_contra hc; push Not at hc; exact hfF (Finset.mem_filter.2 ⟨hfE.1, hc⟩)
  rcases hfq with hq1 | hq2
  · rcases hpf' with e | e
    · rw [e, hq1]
    · exfalso; rcases hfE.2 with h | h
      · rw [hq1] at h; exact hq h
      · exact hpR (e ▸ h)
  · rcases hpf' with e | e
    · exfalso; rcases hfE.2 with h | h
      · exact hpR (e ▸ h)
      · rw [hq2] at h; exact hq h
    · rw [e, hq2]

/-- around an edge: in a non-split graph with two edges, the ends of an edge are joined avoiding it -/
lemma reach_edge (G : MetricGraph k) (hns : Split G → False) (h2 : 2 ≤ G.edges.card)
    {e : E k × E k} (he : e ∈ G.edges) {w1 w2 : E k} (hj : Joins e w1 w2) :
    Reach (G.edges.erase e) w2 w1 := by
  classical
  set F := G.edges.erase e with hF
  by_contra hR
  set Rch : E k → Prop := fun a => Reach F w2 a
  set A := F.filter fun f => Rch f.1 ∨ Rch f.2
  set B := F.filter fun f => ¬ (Rch f.1 ∨ Rch f.2)
  have hFsub : F ⊆ G.edges := Finset.erase_subset _ _
  have hAsub : A ⊆ G.edges := (Finset.filter_subset _ _).trans hFsub
  have hBsub : B ⊆ G.edges := (Finset.filter_subset _ _).trans hFsub
  have hAB : ∀ p, p ∈ car A → p ∈ car B → False := by
    intro p hp1 hp2
    obtain ⟨f, hf, hpf⟩ := mem_car.1 hp1
    obtain ⟨g, hg, hpg⟩ := mem_car.1 hp2
    have hfE := Finset.mem_filter.1 hf
    have hgE := Finset.mem_filter.1 hg
    have hfg : f ≠ g := by rintro rfl; exact hgE.2 hfE.2
    obtain ⟨hpf', hpg'⟩ := meet_end G (hFsub hfE.1) (hFsub hgE.1) hfg hpf hpg
    have hboth := reach_other hfE.1 hfE.2
    have hpR : Rch p := by rcases hpf' with e' | e'
                           · rw [e']; exact hboth.1
                           · rw [e']; exact hboth.2
    apply hgE.2; rcases hpg' with e' | e'
    · left; rw [← e']; exact hpR
    · right; rw [← e']; exact hpR
  have hends : ∀ p, p = e.1 ∨ p = e.2 → p = w1 ∨ p = w2 := by
    intro p hp
    rcases hj with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hp with h | h
    · left; rw [h, a]
    · right; rw [h, b]
    · right; rw [h, a]
    · left; rw [h, b]
  have heB : ∀ p, p ∈ car B → p ∈ segment ℝ e.1 e.2 → p = w1 := by
    intro p hp1 hpe
    obtain ⟨g, hg, hpg⟩ := mem_car.1 hp1
    have hgE := Finset.mem_filter.1 hg
    have hge : g ≠ e := (Finset.mem_erase.1 hgE.1).1
    obtain ⟨hpg', hpe'⟩ := meet_end G (hFsub hgE.1) he hge hpg hpe
    rcases hends p hpe' with h | h
    · exact h
    · exfalso; apply hgE.2
      rcases hpg' with e' | e'
      · left; rw [← e', h]; exact reach_refl F w2
      · right; rw [← e', h]; exact reach_refl F w2
  have heA : ∀ p, p ∈ car A → p ∈ segment ℝ e.1 e.2 → p = w2 := by
    intro p hp1 hpe
    obtain ⟨f, hf, hpf⟩ := mem_car.1 hp1
    have hfE := Finset.mem_filter.1 hf
    have hfe : f ≠ e := (Finset.mem_erase.1 hfE.1).1
    obtain ⟨hpf', hpe'⟩ := meet_end G (hFsub hfE.1) he hfe hpf hpe
    have hboth := reach_other hfE.1 hfE.2
    rcases hends p hpe' with h | h
    · exfalso; apply hR; rw [← h]
      rcases hpf' with e' | e'
      · rw [e']; exact hboth.1
      · rw [e']; exact hboth.2
    · exact h
  have hsplitF : ∀ f ∈ F, f ∈ A ∨ f ∈ B := by
    intro f hf
    by_cases h : Rch f.1 ∨ Rch f.2
    · exact Or.inl (Finset.mem_filter.2 ⟨hf, h⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hf, h⟩)
  apply hns
  by_cases hB : B.Nonempty
  · refine split_of_part G (insert e A) B (Finset.insert_subset he hAsub) hBsub
      (fun f hf => by
        by_cases hfe : f = e
        · exact Or.inl (hfe ▸ Finset.mem_insert_self e A)
        · rcases hsplitF f (Finset.mem_erase.2 ⟨hfe, hf⟩) with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr h)
      ⟨e, Finset.mem_insert_self e A⟩ hB w1 ?_
    intro p hp1 hp2
    obtain ⟨f, hf, hpf⟩ := mem_car.1 hp1
    rcases Finset.mem_insert.1 hf with rfl | hfA
    · exact heB p hp2 hpf
    · exact (hAB p (mem_car.2 ⟨f, hfA, hpf⟩) hp2).elim
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.1 hB
    have hAne : A.Nonempty := by
      have hc : 1 ≤ F.card := by rw [hF, Finset.card_erase_of_mem he]; omega
      obtain ⟨f, hf⟩ := Finset.card_pos.1 (by omega : 0 < F.card)
      rcases hsplitF f hf with h | h
      · exact ⟨f, h⟩
      · rw [hBe] at h; exact absurd h (Finset.notMem_empty _)
    refine split_of_part G A {e} hAsub (Finset.singleton_subset_iff.2 he)
      (fun f hf => by
        by_cases hfe : f = e
        · exact Or.inr (hfe ▸ Finset.mem_singleton_self e)
        · rcases hsplitF f (Finset.mem_erase.2 ⟨hfe, hf⟩) with h | h
          · exact Or.inl h
          · rw [hBe] at h; exact absurd h (Finset.notMem_empty _))
      hAne ⟨e, Finset.mem_singleton_self e⟩ w2 ?_
    intro p hp1 hp2
    obtain ⟨f, hf, hpf⟩ := mem_car.1 hp2
    rw [Finset.mem_singleton] at hf; subst hf
    exact heA p hp1 hpf

end SPFGGeo

-- ===== Geo37 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k : ℕ}

/-- a loop from a finite cyclic sequence of edges -/
def mkLoop (G : MetricGraph k) (m : ℕ) (hm : 0 < m) (E0 : ℕ → E k × E k) (C0 : ℕ → E k)
    (hE : ∀ j < m, E0 j ∈ G.edges) (hC : C0 m = C0 0)
    (htrav : ∀ j < m, Joins (E0 j) (C0 j) (C0 (j + 1)))
    (hturn : ∀ j < m, E0 j ≠ E0 ((j + 1) % m)) : Loop G where
  m := m
  hm := hm
  e := fun l => E0 (l % m)
  c := fun l => C0 (l % m)
  per_e := fun l => by simp
  per_c := fun l => by simp
  he := fun l => hE _ (Nat.mod_lt _ hm)
  trav := fun l => by
    have hj := Nat.mod_lt l hm
    have h1 : (l + 1) % m = (l % m + 1) % m := (Nat.mod_add_mod l m 1).symm
    have hc : C0 ((l + 1) % m) = C0 (l % m + 1) := by
      rcases Nat.lt_or_ge (l % m + 1) m with h | h
      · rw [h1, Nat.mod_eq_of_lt h]
      · have : l % m + 1 = m := by omega
        rw [h1, this, Nat.mod_self, hC]
    show (C0 (l % m) = (E0 (l % m)).1 ∧ C0 ((l + 1) % m) = (E0 (l % m)).2) ∨
      (C0 (l % m) = (E0 (l % m)).2 ∧ C0 ((l + 1) % m) = (E0 (l % m)).1)
    rw [hc]
    rcases htrav _ hj with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.symm, b.symm⟩
    · exact Or.inr ⟨b.symm, a.symm⟩
  turn := fun l => by
    show E0 (l % m) ≠ E0 ((l + 1) % m)
    rw [show (l + 1) % m = (l % m + 1) % m from (Nat.mod_add_mod l m 1).symm]
    exact hturn _ (Nat.mod_lt _ hm)

lemma joins_symm {f : E k × E k} {a b : E k} (h : Joins f a b) : Joins f b a := h.symm

lemma joins_len {f : E k × E k} {a b : E k} (h : Joins f a b) : ‖b - a‖ = elen f := by
  unfold elen; rcases h with ⟨x, y⟩ | ⟨x, y⟩
  · rw [x, y]
  · rw [x, y, norm_sub_rev]

lemma rayPt_eq (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v w : E k}
    (hvw : Joins e v w) (r : ℝ) : rayPt e v r = v + (r / elen e) • (w - v) := by
  have hL := elen_pos G he
  have hne := G.fst_ne_snd e he
  unfold rayPt rpar epar
  rcases hvw with ⟨a, b⟩ | ⟨a, b⟩
  · rw [if_pos a.symm, a, b]
  · rw [if_neg (fun h => hne (h.symm.trans b.symm)), a, b]
    module

lemma qA (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v w : E k}
    (hvw : Joins e v w) (s : ℝ) : rayPt e v s = qray v w s := by
  rw [rayPt_eq G he hvw, qray, joins_len hvw]

lemma qB (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v w : E k}
    (hwv : Joins e w v) (s : ℝ) : rayPt e w (elen e - s) = qray v w s := by
  have hL := elen_pos G he
  rw [rayPt_eq G he hwv, qray, joins_len (joins_symm hwv)]
  rw [show w + ((elen e - s) / elen e) • (v - w) = v + (s / elen e) • (w - v) by
    rw [sub_div, div_self hL.ne']; module]

lemma qC (G : MetricGraph k) {e : E k × E k} (he : e ∈ G.edges) {v w : E k}
    (hvw : Joins e v w) {a : ℝ} (ha : 0 < a) (haL : a < elen e) (s : ℝ) :
    rayPt e v (a + s) = qray (v + (a / elen e) • (w - v)) w s ∧
      rayPt e v (a - s) = qray (v + (a / elen e) • (w - v)) v s := by
  have hL := elen_pos G he
  set L := elen e
  have hwv : ‖w - v‖ = L := joins_len hvw
  have hLa : L - a ≠ 0 := (by linarith : (0:ℝ) < L - a).ne'
  have e1 : w - (v + (a / L) • (w - v)) = ((L - a) / L) • (w - v) := by
    rw [sub_div, div_self hL.ne']; module
  have e2 : v - (v + (a / L) • (w - v)) = (-(a / L)) • (w - v) := by module
  have n1 : ‖w - (v + (a / L) • (w - v))‖ = L - a := by
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hL), hwv]; field_simp
  have n2 : ‖v - (v + (a / L) • (w - v))‖ = a := by
    rw [e2, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos ha hL), hwv]; field_simp
  constructor
  · rw [rayPt_eq G he hvw, qray, n1, e1, smul_smul]
    rw [show (s / (L - a)) * ((L - a) / L) = s / L by field_simp]
    rw [add_div]; module
  · rw [rayPt_eq G he hvw, qray, n2, e2, smul_smul]
    rw [show (s / a) * (-(a / L)) = -(s / L) by field_simp]
    rw [sub_div]; module

end SPFGGeo

-- ===== Geo38 =====


namespace SPFGGeo

open SPFacilityGraph Function

variable {k : ℕ}

namespace Loop

variable {G : MetricGraph k} (Z : Loop G)

lemma γ_after {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ elen (Z.e Z.m)) :
    Z.γ (Z.P + s) = rayPt (Z.e Z.m) (Z.c Z.m) s := by
  have h1 : Z.Λ Z.m ≤ Z.P + s := by unfold P; linarith
  have h2 : Z.P + s ≤ Z.Λ (Z.m + 1) := by rw [Λ_succ]; unfold P; linarith
  rw [Z.γ_eq h1 h2]; unfold P; congr 1; ring

lemma γ_before {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ elen (Z.e (Z.m - 1))) :
    Z.γ (Z.P - s) = rayPt (Z.e (Z.m - 1)) (Z.c (Z.m - 1)) (elen (Z.e (Z.m - 1)) - s) := by
  have hm := Z.hm
  have hΛ : Z.Λ Z.m = Z.Λ (Z.m - 1) + elen (Z.e (Z.m - 1)) := by
    rw [← Λ_succ, Nat.sub_add_cancel hm]
  have h1 : Z.Λ (Z.m - 1) ≤ Z.P - s := by unfold P; linarith
  have h2 : Z.P - s ≤ Z.Λ (Z.m - 1 + 1) := by rw [Nat.sub_add_cancel hm]; unfold P; linarith
  rw [Z.γ_eq h1 h2]; unfold P; congr 1; linarith

end Loop

lemma joins_of_ends {e : E k × E k} (hne : e.1 ≠ e.2) {a b : E k} (ha : a = e.1 ∨ a = e.2)
    (hb : b = e.1 ∨ b = e.2) (hab : a ≠ b) : Joins e a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hab

lemma joins_end {f : E k × E k} {a b : E k} (h : Joins f a b) : f.1 = a ∨ f.2 = a := by
  rcases h with ⟨x, -⟩ | ⟨-, y⟩
  · exact Or.inl x
  · exact Or.inr y

/-- **Loop richness** of non-split graphs with at least two edges. -/
theorem loopRich_of (G : MetricGraph k) (hns : Split G → False) (h2 : 2 ≤ G.edges.card) :
    LoopRich G := by
  classical
  intro q e1 e2 he1 he2 w1 w2 hw1 hw2 hq1 hq2 hw1q hw2q hne
  have hne1 := G.fst_ne_snd e1 he1
  have hne2 := G.fst_ne_snd e2 he2
  by_cases hqv : q = e1.1 ∨ q = e1.2
  · -- `q` is a vertex: case (I)
    have hJ1 : Joins e1 q w1 := joins_of_ends hne1 hqv hw1 (Ne.symm hw1q)
    have he12 : e1 ≠ e2 := by
      rintro rfl
      apply hne
      have : w1 = w2 := by
        rcases hqv with h | h <;> rcases hw1 with h1 | h1 <;> rcases hw2 with h2' | h2'
        all_goals first | (rw [h1, h2']; done) | (exfalso; apply hw1q; rw [h1, h]; done) | (exfalso; apply hw2q; rw [h2', h]; done)
      rw [this]
    have hqv2 : q = e2.1 ∨ q = e2.2 := (G.meet e1 he1 e2 he2 he12 ⟨hq1, hq2⟩).2
    have hJ2 : Joins e2 q w2 := joins_of_ends hne2 hqv2 hw2 (Ne.symm hw2q)
    set F := G.edges.filter fun f => f.1 ≠ q ∧ f.2 ≠ q
    obtain ⟨r, f, v, h0, hr, hp, hnb⟩ := reach_nb G (Finset.filter_subset _ _)
      (reach_vertex G hns he1 he2 hJ1 hJ2 he12)
    have hFq : ∀ i < r, f i ≠ e1 ∧ f i ≠ e2 := by
      intro i hi
      have := (Finset.mem_filter.1 (hp i hi).1).2
      constructor
      · rintro h; rw [h] at this; rcases joins_end hJ1 with h' | h'
        · exact this.1 h'
        · exact this.2 h'
      · rintro h; rw [h] at this; rcases joins_end hJ2 with h' | h'
        · exact this.1 h'
        · exact this.2 h'
    set E0 : ℕ → E k × E k := fun j => if j = 0 then e2 else if j ≤ r then f (j - 1) else e1
    set C0 : ℕ → E k := fun j => if j = 0 then q else if j ≤ r + 1 then v (j - 1) else q
    have hE : ∀ j < r + 2, E0 j ∈ G.edges := by
      intro j hj; simp only [E0]; split_ifs with h h'
      · exact he2
      · exact (Finset.mem_filter.1 (hp (j - 1) (by omega)).1).1
      · exact he1
    have hC : C0 (r + 2) = C0 0 := by simp [C0]
    have htrav : ∀ j < r + 2, Joins (E0 j) (C0 j) (C0 (j + 1)) := by
      intro j hj
      simp only [E0, C0]
      by_cases hj0 : j = 0
      · subst hj0; simp only [if_true, show (0:ℕ) + 1 ≠ 0 by omega, if_false,
          show (0:ℕ) + 1 ≤ r + 1 by omega, Nat.add_sub_cancel, h0]; exact hJ2
      · by_cases hjr : j ≤ r
        · simp only [hj0, if_false, hjr, if_true, show j ≤ r + 1 by omega,
            show j + 1 ≠ 0 by omega, show j + 1 ≤ r + 1 by omega, Nat.add_sub_cancel]
          have := (hp (j - 1) (by omega)).2
          rwa [show j - 1 + 1 = j by omega] at this
        · have hjr1 : j = r + 1 := by omega
          subst hjr1
          simp only [hj0, if_false, hjr, show r + 1 ≤ r + 1 by omega, if_true,
            show r + 1 + 1 ≠ 0 by omega, show ¬ (r + 1 + 1 ≤ r + 1) by omega,
            show r + 1 - 1 = r by omega, hr]
          exact joins_symm hJ1
    have hturn : ∀ j < r + 2, E0 j ≠ E0 ((j + 1) % (r + 2)) := by
      intro j hj
      by_cases hjl : j + 1 < r + 2
      · rw [Nat.mod_eq_of_lt hjl]
        simp only [E0]
        by_cases hj0 : j = 0
        · subst hj0
          simp only [if_true, show (0:ℕ) + 1 ≠ 0 by omega, if_false]
          split_ifs with h
          · exact fun h' => (hFq 0 (by omega)).2 h'.symm
          · exact Ne.symm he12
        · by_cases hjr : j + 1 ≤ r
          · simp only [hj0, if_false, show j ≤ r by omega, if_true, show j + 1 ≠ 0 by omega, hjr]
            have := hnb (j - 1) (by omega)
            rwa [show j - 1 + 1 = j + 1 - 1 by omega] at this
          · simp only [hj0, if_false, show j + 1 ≠ 0 by omega, hjr]
            have hjr' : j = r := by omega
            subst hjr'
            simp only [le_refl, if_true]
            exact (hFq (j - 1) (by omega)).1
      · have : j = r + 1 := by omega
        subst this
        rw [show r + 1 + 1 = r + 2 by ring, Nat.mod_self]
        simp only [E0, show r + 1 ≠ 0 by omega, if_false, show ¬ (r + 1 ≤ r) by omega, if_true]
        exact he12
    set Z := mkLoop G (r + 2) (by omega) E0 C0 hE hC htrav hturn
    have hZm : Z.m = r + 2 := rfl
    have hZe : Z.e Z.m = e2 := by show E0 ((r + 2) % (r + 2)) = e2; rw [Nat.mod_self]; simp [E0]
    have hZc : Z.c Z.m = q := by show C0 ((r + 2) % (r + 2)) = q; rw [Nat.mod_self]; simp [C0]
    have hZe' : Z.e (Z.m - 1) = e1 := by
      show E0 ((r + 2 - 1) % (r + 2)) = e1
      rw [Nat.mod_eq_of_lt (by omega)]
      simp [E0, show r + 2 - 1 = r + 1 by omega]
    have hZc' : Z.c (Z.m - 1) = w1 := by
      show C0 ((r + 2 - 1) % (r + 2)) = w1
      rw [Nat.mod_eq_of_lt (by omega)]
      simp [C0, show r + 2 - 1 = r + 1 by omega, hr]
    have hL1 := elen_pos G he1
    have hL2 := elen_pos G he2
    refine ⟨Z, Z.P, le_rfl, min (elen e1) (elen e2), lt_min hL1 hL2, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Z.γ_before hs.1 (by rw [hZe']; exact hs.2.trans (min_le_left _ _)), hZe', hZc']
      exact qB G he1 (joins_symm hJ1) s
    · rw [Z.γ_after hs.1 (by rw [hZe]; exact hs.2.trans (min_le_right _ _)), hZe, hZc]
      exact qA G he2 hJ2 s
  · -- `q` interior: case (II)
    push Not at hqv
    have he12 : e2 = e1 := by
      by_contra h
      have := (G.meet e1 he1 e2 he2 (Ne.symm h) ⟨hq1, hq2⟩).1
      rcases this with h' | h'
      · exact hqv.1 h'
      · exact hqv.2 h'
    subst he12
    set e := e2
    have hw12 : w1 ≠ w2 := by intro h; apply hne; rw [h]
    have hJ : Joins e w1 w2 := joins_of_ends hne1 hw1 hw2 hw12
    obtain ⟨r, f, v, h0, hr, hp, hnb⟩ := reach_nb G (Finset.erase_subset _ _)
      (reach_edge G hns h2 he1 hJ)
    have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; exact absurd (h0.symm.trans hr) (Ne.symm hw12)
      · exact h
    have hFe : ∀ i < r, f i ≠ e := fun i hi => (Finset.mem_erase.1 (hp i hi).1).1
    set E0 : ℕ → E k × E k := fun j => if j = 0 then e else f (j - 1)
    set C0 : ℕ → E k := fun j => if j = 0 then w1 else v (j - 1)
    have hE : ∀ j < r + 1, E0 j ∈ G.edges := by
      intro j hj; simp only [E0]; split_ifs with h
      · exact he1
      · exact (Finset.mem_erase.1 (hp (j - 1) (by omega)).1).2
    have hC : C0 (r + 1) = C0 0 := by simp [C0, hr]
    have htrav : ∀ j < r + 1, Joins (E0 j) (C0 j) (C0 (j + 1)) := by
      intro j hj
      simp only [E0, C0]
      by_cases hj0 : j = 0
      · subst hj0; simp only [if_true, show (0:ℕ) + 1 ≠ 0 by omega, if_false,
          Nat.add_sub_cancel, h0]; exact hJ
      · simp only [hj0, if_false, show j + 1 ≠ 0 by omega, Nat.add_sub_cancel]
        have := (hp (j - 1) (by omega)).2
        rwa [show j - 1 + 1 = j by omega] at this
    have hturn : ∀ j < r + 1, E0 j ≠ E0 ((j + 1) % (r + 1)) := by
      intro j hj
      by_cases hjl : j + 1 < r + 1
      · rw [Nat.mod_eq_of_lt hjl]
        simp only [E0, show j + 1 ≠ 0 by omega, if_false, Nat.add_sub_cancel]
        by_cases hj0 : j = 0
        · subst hj0; simp only [if_true]; exact fun h => hFe 0 (by omega) h.symm
        · simp only [hj0, if_false]
          have := hnb (j - 1) (by omega)
          rwa [show j - 1 + 1 = j by omega] at this
      · have : j = r := by omega
        subst this
        rw [Nat.mod_self]
        simp only [E0, show j ≠ 0 by omega, if_false, if_true]
        exact hFe (j - 1) (by omega)
    set Z := mkLoop G (r + 1) (by omega) E0 C0 hE hC htrav hturn
    have hZe : Z.e Z.m = e := by show E0 ((r + 1) % (r + 1)) = e; rw [Nat.mod_self]; simp [E0]
    have hZc : Z.c Z.m = w1 := by show C0 ((r + 1) % (r + 1)) = w1; rw [Nat.mod_self]; simp [C0]
    have hL := elen_pos G he1
    -- position of `q` on `e`
    obtain ⟨τ, hτ, hqτ⟩ := (mem_seg_iff e q).1 hq1
    have hτ0 : τ ≠ 0 := by intro h; apply hqv.1; rw [hqτ, h, epar_zero]
    have hτ1 : τ ≠ 1 := by intro h; apply hqv.2; rw [hqτ, h, epar_one]
    have hτI : 0 < τ ∧ τ < 1 := ⟨lt_of_le_of_ne hτ.1 (Ne.symm hτ0), lt_of_le_of_ne hτ.2 hτ1⟩
    obtain ⟨a, ha0, haL, hqa⟩ : ∃ a, 0 < a ∧ a < elen e ∧ q = w1 + (a / elen e) • (w2 - w1) := by
      rcases hJ with ⟨x, y⟩ | ⟨x, y⟩
      · refine ⟨τ * elen e, by nlinarith [hτI.1], by nlinarith [hτI.2], ?_⟩
        rw [hqτ, ← x, ← y, mul_div_cancel_right₀ _ hL.ne']; rfl
      · refine ⟨(1 - τ) * elen e, by nlinarith [hτI.2], by nlinarith [hτI.1], ?_⟩
        rw [hqτ, ← x, ← y, mul_div_cancel_right₀ _ hL.ne']; unfold epar; module
    refine ⟨Z, Z.P + a, by linarith, min a (elen e - a), lt_min ha0 (by linarith),
      fun s hs => ⟨?_, ?_⟩⟩
    · have hs1 := hs.2.trans (min_le_left _ _)
      have hs0 := hs.1
      rw [show Z.P + a - s = Z.P + (a - s) by ring,
        Z.γ_after (by linarith) (by rw [hZe]; linarith), hZe, hZc, hqa]
      exact (qC G he1 hJ ha0 haL s).2
    · have hs2 := hs.2.trans (min_le_right _ _)
      have hs0 := hs.1
      rw [show Z.P + a + s = Z.P + (a + s) by ring,
        Z.γ_after (by linarith [hs.1]) (by rw [hZe]; linarith), hZe, hZc, hqa]
      exact (qC G he1 hJ ha0 haL s).1

end SPFGGeo

-- ===== Geo39 =====


namespace SPFGGeo

open SPFacilityGraph Function

theorem gate_all (N : ℕ) : ∀ {k n : ℕ}, 2 ≤ n → ∀ G : MetricGraph k, G.edges.card = N →
    ∀ M : Profile G n → G.Pt, IsSP G M → Function.Surjective M → Gate G M := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro k n hn G hN M hSP hM
  classical
  by_cases hs : Nonempty (Split G)
  · obtain ⟨S⟩ := hs
    apply gate_split S M hSP hM
    · intro M1 h1 h1'
      exact ih _ (hN ▸ S.card_lt) hn S.G1 rfl M1 h1 h1'
    · intro M2 h2 h2'
      exact ih _ (hN ▸ S.swap.card_lt) hn S.swap.G1 rfl M2 h2 h2'
  · have hns : Split G → False := fun S => hs ⟨S⟩
    have hpos : 0 < G.edges.card := Finset.card_pos.2 G.edges_nonempty
    by_cases h1 : G.edges.card = 1
    · obtain ⟨e, he⟩ := Finset.card_eq_one.1 h1
      exact gate_one_edge G M hSP hM (by omega) e he
    · have hLR := loopRich_of G hns (by omega)
      obtain ⟨j, hj⟩ := dictN G hLR n hn M hSP hM
      exact gate_of_dict G M j hj

end SPFGGeo



open SPFacilityGraph in
theorem solution {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n) (i : Fin n) (y z : G.Pt) :
    G.dist y (M (Function.update x i z)) =
      G.dist y (M (Function.update x i y)) +
        G.dist (M (Function.update x i y)) (M (Function.update x i z)) :=
  SPFGGeo.gate_all _ hn G rfl M hSP hM x i y z
