-- Prove2me | solution 1 for PrivPCP.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:55:42.429341+00:00
-- url     : https://prove2.me/submissions/c53b2807-5d0e-4f11-8ec3-578b7a42375d

import Mathlib
import Definitions.Def_PrivPCP_tensorCode


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]

/-- Hamming weight of a word on a finite type -/
noncomputable def wt {α : Type} [Fintype α] (x : α → F) : ℕ :=
  (Finset.univ.filter fun a => x a ≠ 0).card

lemma wt_eq_supportCard {α : Type} [Fintype α] (x : α → F) : wt x = supportCard x := rfl

/-- two-dimensional tensor code on `Ta × Tb`: columns in `Da`, rows in `Db` -/
def tens2 {Ta Tb : Type} (Da : Submodule F (Ta → F)) (Db : Submodule F (Tb → F)) :
    Submodule F (Ta × Tb → F) where
  carrier := {w | (∀ b, (fun a => w (a, b)) ∈ Da) ∧ ∀ a, (fun b => w (a, b)) ∈ Db}
  add_mem' := by
    intro x y hx hy
    exact ⟨fun b => Da.add_mem (hx.1 b) (hy.1 b), fun a => Db.add_mem (hx.2 a) (hy.2 a)⟩
  zero_mem' := ⟨fun b => Da.zero_mem, fun a => Db.zero_mem⟩
  smul_mem' := by
    intro c x hx
    exact ⟨fun b => Da.smul_mem c (hx.1 b), fun a => Db.smul_mem c (hx.2 a)⟩

/-- three-dimensional tensor code -/
def tens3 {T1 T2 T3 : Type} (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F))
    (D3 : Submodule F (T3 → F)) : Submodule F (T1 × T2 × T3 → F) where
  carrier := {w | (∀ b c, (fun a => w (a, b, c)) ∈ D1) ∧ (∀ a c, (fun b => w (a, b, c)) ∈ D2) ∧
    ∀ a b, (fun c => w (a, b, c)) ∈ D3}
  add_mem' := by
    intro x y hx hy
    exact ⟨fun b c => D1.add_mem (hx.1 b c) (hy.1 b c), fun a c => D2.add_mem (hx.2.1 a c) (hy.2.1 a c),
      fun a b => D3.add_mem (hx.2.2 a b) (hy.2.2 a b)⟩
  zero_mem' := ⟨fun _ _ => D1.zero_mem, fun _ _ => D2.zero_mem, fun _ _ => D3.zero_mem⟩
  smul_mem' := by
    intro s x hx
    exact ⟨fun b c => D1.smul_mem s (hx.1 b c), fun a c => D2.smul_mem s (hx.2.1 a c),
      fun a b => D3.smul_mem s (hx.2.2 a b)⟩

/-- relative distance hypothesis -/
def HasDist {α : Type} [Fintype α] (D : Submodule F (α → F)) (δ : ℝ) : Prop :=
  ∀ c ∈ D, c ≠ 0 → δ * Fintype.card α ≤ wt c

/-- distance of a two-dimensional tensor code -/
theorem tens2_dist {Ta Tb : Type} [Fintype Ta] [Fintype Tb] (Da : Submodule F (Ta → F))
    (Db : Submodule F (Tb → F)) (δa δb : ℝ) (hδa : 0 ≤ δa) (ha : HasDist Da δa) (hb : HasDist Db δb) :
    HasDist (tens2 Da Db) (δa * δb) := by
  intro w hw hw0
  obtain ⟨⟨a0, b0⟩, h0⟩ : ∃ p, w p ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  -- the column through `b0` is a nonzero codeword of `Da`
  have hcol : (fun a => w (a, b0)) ≠ 0 := fun h => h0 (congrFun h a0)
  have hA := ha _ (hw.1 b0) hcol
  -- every row through a nonzero entry of that column is a nonzero codeword of `Db`
  set A := Finset.univ.filter fun a => w (a, b0) ≠ 0 with hA'
  have hrow : ∀ a ∈ A, δb * Fintype.card Tb ≤ wt (fun b => w (a, b)) := by
    intro a haA
    simp only [hA', Finset.mem_filter, Finset.mem_univ, true_and] at haA
    exact hb _ (hw.2 a) (fun h => haA (congrFun h b0))
  have hsplit : (wt w : ℝ) ≥ ∑ a ∈ A, (wt (fun b => w (a, b)) : ℝ) := by
    have : wt w = ∑ a, wt (fun b => w (a, b)) := by
      unfold wt
      rw [← Finset.card_sigma]
      apply Finset.card_bij (fun p _ => ⟨p.1, p.2⟩)
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp; simp [hp]
      · intro p _ q _ h; simp only [Sigma.mk.injEq] at h; exact Prod.ext h.1 (eq_of_heq h.2)
      · intro s hs; simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact ⟨(s.1, s.2), by simpa using hs, rfl⟩
    rw [this]; push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  have hδb : 0 ≤ δb * Fintype.card Tb ∨ δb * Fintype.card Tb < 0 := le_or_gt _ _
  rcases hδb with hδb | hδb
  · calc δa * δb * (Fintype.card (Ta × Tb) : ℝ) = (δa * Fintype.card Ta) * (δb * Fintype.card Tb) := by
          rw [Fintype.card_prod]; push_cast; ring
      _ ≤ (A.card : ℝ) * (δb * Fintype.card Tb) := mul_le_mul_of_nonneg_right hA hδb
      _ = ∑ a ∈ A, δb * (Fintype.card Tb : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ A, (wt (fun b => w (a, b)) : ℝ) := Finset.sum_le_sum hrow
      _ ≤ wt w := hsplit
  · have : δa * δb * (Fintype.card (Ta × Tb) : ℝ) ≤ 0 := by
      rw [Fintype.card_prod]; push_cast
      have : δb * (Fintype.card Tb : ℝ) * (δa * Fintype.card Ta) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hδb.le (by positivity)
      nlinarith
    exact this.trans (by positivity)

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {T1 T2 T3 : Type} [Fintype T1] [Fintype T2] [Fintype T3]
variable (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F)) (D3 : Submodule F (T3 → F))

/-- the disagreement set of a family of plane opinions -/
def Edis (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F)
    (p : T1 × T2 × T3) : Prop :=
  ¬ (r1 p.1 (p.2.1, p.2.2) = r2 p.2.1 (p.1, p.2.2) ∧ r2 p.2.1 (p.1, p.2.2) = r3 p.2.2 (p.1, p.2.1))

/-- number of disagreement points in the plane `x₁ = a` -/
noncomputable def cnt1 (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F)
    (a : T1) : ℕ := (Finset.univ.filter fun q : T2 × T3 => Edis r1 r2 r3 (a, q.1, q.2)).card

noncomputable def cnt2 (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F)
    (b : T2) : ℕ := (Finset.univ.filter fun q : T1 × T3 => Edis r1 r2 r3 (q.1, b, q.2)).card

noncomputable def cnt3 (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F)
    (c : T3) : ℕ := (Finset.univ.filter fun q : T1 × T2 => Edis r1 r2 r3 (q.1, q.2, c)).card

/-- if two codewords of a code with distance `δ` differ somewhere, they differ in `≥ δ n` places -/
lemma diff_card {α : Type} [Fintype α] (D : Submodule F (α → F)) (δ : ℝ) (hD : HasDist D δ)
    (f g : α → F) (hf : f ∈ D) (hg : g ∈ D) (x : α) (hx : f x ≠ g x) :
    δ * Fintype.card α ≤ (Finset.univ.filter fun y => f y ≠ g y).card := by
  have h := hD (f - g) (D.sub_mem hf hg) (fun h => hx (sub_eq_zero.1 (congrFun h x)))
  unfold wt at h
  convert h using 3
  ext y; simp [sub_eq_zero]

/-- counting points of a product set -/
lemma card_prod_ge {α β : Type} [Fintype α] [Fintype β] (P : α × β → Prop) (X : Finset β) (m : ℝ)
    (hm : ∀ c ∈ X, m ≤ (Finset.univ.filter fun b => P (b, c)).card) :
    (X.card : ℝ) * m ≤ (Finset.univ.filter P).card := by
  have : ((Finset.univ.filter P).card : ℝ) ≥
      ∑ c ∈ X, ((Finset.univ.filter fun b => P (b, c)).card : ℝ) := by
    have hdisj : (X.biUnion fun c => (Finset.univ.filter fun b => P (b, c)).map
        ⟨fun b => (b, c), fun b b' h => by simpa using h⟩).card =
        ∑ c ∈ X, (Finset.univ.filter fun b => P (b, c)).card := by
      rw [Finset.card_biUnion]
      · simp
      · intro c _ c' _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro p hp hp'
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk] at hp hp'
        obtain ⟨b, -, rfl⟩ := hp
        obtain ⟨b', -, h⟩ := hp'
        exact hne (Prod.ext_iff.1 h).2.symm
    have hsub : (X.biUnion fun c => (Finset.univ.filter fun b => P (b, c)).map
        ⟨fun b => (b, c), fun b b' h => by simpa using h⟩) ⊆ Finset.univ.filter P := by
      intro p hp
      simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk] at hp ⊢
      obtain ⟨c, -, b, hb, rfl⟩ := hp
      exact hb
    have := Finset.card_le_card hsub
    rw [hdisj] at this
    exact_mod_cast this
  calc (X.card : ℝ) * m = ∑ _c ∈ X, m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ X, ((Finset.univ.filter fun b => P (b, c)).card : ℝ) := Finset.sum_le_sum hm
    _ ≤ _ := this

variable (δ : ℝ) (hδ : 0 ≤ δ) (h1 : HasDist D1 δ) (h2 : HasDist D2 δ) (h3 : HasDist D3 δ)
variable (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F)
variable (hr1 : ∀ a, r1 a ∈ tens2 D2 D3) (hr2 : ∀ b, r2 b ∈ tens2 D1 D3)
  (hr3 : ∀ c, r3 c ∈ tens2 D1 D2)

include hδ h1 h2 h3 hr1 hr2 hr3 in
/-- Viderman's main lemma, planes 1 and 2 -/
lemma main12 (a : T1) (b : T2) (c : T3) (h : r1 a (b, c) ≠ r2 b (a, c)) :
    (1 / 2 : ℝ) * (δ * Fintype.card T2) * (δ * Fintype.card T3) ≤ cnt1 r1 r2 r3 a ∨
    (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T3) ≤ cnt2 r1 r2 r3 b := by
  set Bad := Finset.univ.filter fun c' => r1 a (b, c') ≠ r2 b (a, c') with hBad
  have hB : δ * Fintype.card T3 ≤ Bad.card :=
    diff_card D3 δ h3 _ _ ((hr1 a).2 b) ((hr2 b).2 a) c h
  set X1 := Bad.filter fun c' => r3 c' (a, b) ≠ r1 a (b, c') with hX1
  set X2 := Bad.filter fun c' => r3 c' (a, b) ≠ r2 b (a, c') with hX2
  have hcov : Bad ⊆ X1 ∪ X2 := by
    intro c' hc'
    simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    simp only [hX1, hX2, Finset.mem_union, Finset.mem_filter, hBad, Finset.mem_univ, true_and]
    by_contra hcon
    push Not at hcon
    exact hc' ((hcon.1 hc').symm.trans (hcon.2 hc'))
  have hsum : (Bad.card : ℝ) ≤ X1.card + X2.card := by
    exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have hδ2 : 0 ≤ δ * Fintype.card T2 := by positivity
  have hδ1 : 0 ≤ δ * Fintype.card T1 := by positivity
  by_cases hX : δ * Fintype.card T3 / 2 ≤ X1.card
  · left
    have key := card_prod_ge (fun q : T2 × T3 => Edis r1 r2 r3 (a, q.1, q.2)) X1
      (δ * Fintype.card T2) (by
        intro c' hc'
        simp only [hX1, hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        refine (diff_card D2 δ h2 (fun b' => r1 a (b', c')) (fun b' => r3 c' (a, b'))
          ((hr1 a).1 c') ((hr3 c').2 a) b (fun e => hc'.2 e.symm)).trans ?_
        exact_mod_cast Finset.card_le_card (fun b' hb' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
          intro hE; exact hb' (hE.1.trans hE.2)))
    unfold cnt1
    calc (1 / 2 : ℝ) * (δ * Fintype.card T2) * (δ * Fintype.card T3)
        = (δ * Fintype.card T3 / 2) * (δ * Fintype.card T2) := by ring
      _ ≤ X1.card * (δ * Fintype.card T2) := mul_le_mul_of_nonneg_right hX hδ2
      _ ≤ _ := key
  · right
    push Not at hX
    have hX2c : δ * Fintype.card T3 / 2 ≤ X2.card := by linarith
    have key := card_prod_ge (fun q : T1 × T3 => Edis r1 r2 r3 (q.1, b, q.2)) X2
      (δ * Fintype.card T1) (by
        intro c' hc'
        simp only [hX2, hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        refine (diff_card D1 δ h1 (fun a' => r2 b (a', c')) (fun a' => r3 c' (a', b))
          ((hr2 b).1 c') ((hr3 c').1 b) a (fun e => hc'.2 e.symm)).trans ?_
        exact_mod_cast Finset.card_le_card (fun a' ha' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
          intro hE; exact ha' hE.2))
    unfold cnt2
    calc (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T3)
        = (δ * Fintype.card T3 / 2) * (δ * Fintype.card T1) := by ring
      _ ≤ X2.card * (δ * Fintype.card T1) := mul_le_mul_of_nonneg_right hX2c hδ1
      _ ≤ _ := key

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {T1 T2 T3 : Type} [Fintype T1] [Fintype T2] [Fintype T3]
variable (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F)) (D3 : Submodule F (T3 → F))

lemma card_prod_ge' {α β : Type} [Fintype α] [Fintype β] (P : α × β → Prop) (X : Finset α) (m : ℝ)
    (hm : ∀ a ∈ X, m ≤ (Finset.univ.filter fun b => P (a, b)).card) :
    (X.card : ℝ) * m ≤ (Finset.univ.filter P).card := by
  have h := card_prod_ge (fun q : β × α => P (q.2, q.1)) X m hm
  have : (Finset.univ.filter fun q : β × α => P (q.2, q.1)).card = (Finset.univ.filter P).card := by
    apply Finset.card_bij (fun q _ => (q.2, q.1))
    · intro q hq; simpa using hq
    · intro q _ q' _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro p hp; exact ⟨(p.2, p.1), by simpa using hp, rfl⟩
  rw [this] at h; exact h

variable (δ : ℝ) (hδ : 0 ≤ δ) (h1 : HasDist D1 δ) (h2 : HasDist D2 δ) (h3 : HasDist D3 δ)
variable (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F)
variable (hr1 : ∀ a, r1 a ∈ tens2 D2 D3) (hr2 : ∀ b, r2 b ∈ tens2 D1 D3)
  (hr3 : ∀ c, r3 c ∈ tens2 D1 D2)

include hδ h1 h2 h3 hr1 hr2 hr3 in
lemma main23 (a : T1) (b : T2) (c : T3) (h : r2 b (a, c) ≠ r3 c (a, b)) :
    (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T3) ≤ cnt2 r1 r2 r3 b ∨
    (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T2) ≤ cnt3 r1 r2 r3 c := by
  set Bad := Finset.univ.filter fun a' => r2 b (a', c) ≠ r3 c (a', b) with hBad
  have hB : δ * Fintype.card T1 ≤ Bad.card :=
    diff_card D1 δ h1 _ _ ((hr2 b).1 c) ((hr3 c).1 b) a h
  set X2 := Bad.filter fun a' => r1 a' (b, c) ≠ r2 b (a', c) with hX2
  set X3 := Bad.filter fun a' => r1 a' (b, c) ≠ r3 c (a', b) with hX3
  have hcov : Bad ⊆ X2 ∪ X3 := by
    intro a' ha'
    simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    simp only [hX2, hX3, Finset.mem_union, Finset.mem_filter, hBad, Finset.mem_univ, true_and]
    by_contra hcon
    push Not at hcon
    exact ha' ((hcon.1 ha').symm.trans (hcon.2 ha'))
  have hsum : (Bad.card : ℝ) ≤ X2.card + X3.card := by
    exact_mod_cast (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have hδ3 : 0 ≤ δ * Fintype.card T3 := by positivity
  have hδ2 : 0 ≤ δ * Fintype.card T2 := by positivity
  by_cases hX : δ * Fintype.card T1 / 2 ≤ X2.card
  · left
    have key := card_prod_ge' (fun q : T1 × T3 => Edis r1 r2 r3 (q.1, b, q.2)) X2
      (δ * Fintype.card T3) (by
        intro a' ha'
        simp only [hX2, hBad, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
        refine (diff_card D3 δ h3 (fun c' => r1 a' (b, c')) (fun c' => r2 b (a', c'))
          ((hr1 a').2 b) ((hr2 b).2 a') c ha'.2).trans ?_
        exact_mod_cast Finset.card_le_card (fun c' hc' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢
          intro hE; exact hc' hE.1))
    unfold cnt2
    calc (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T3)
        = (δ * Fintype.card T1 / 2) * (δ * Fintype.card T3) := by ring
      _ ≤ X2.card * (δ * Fintype.card T3) := mul_le_mul_of_nonneg_right hX hδ3
      _ ≤ _ := key
  · right
    push Not at hX
    have hX3c : δ * Fintype.card T1 / 2 ≤ X3.card := by linarith
    have key := card_prod_ge' (fun q : T1 × T2 => Edis r1 r2 r3 (q.1, q.2, c)) X3
      (δ * Fintype.card T2) (by
        intro a' ha'
        simp only [hX3, hBad, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
        refine (diff_card D2 δ h2 (fun b' => r1 a' (b', c)) (fun b' => r3 c (a', b'))
          ((hr1 a').1 c) ((hr3 c).2 a') b ha'.2).trans ?_
        exact_mod_cast Finset.card_le_card (fun b' hb' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb' ⊢
          intro hE; exact hb' (hE.1.trans hE.2)))
    unfold cnt3
    calc (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T2)
        = (δ * Fintype.card T1 / 2) * (δ * Fintype.card T2) := by ring
      _ ≤ X3.card * (δ * Fintype.card T2) := mul_le_mul_of_nonneg_right hX3c hδ2
      _ ≤ _ := key

include hδ h1 h2 h3 hr1 hr2 hr3 in
lemma E_heavy (a : T1) (b : T2) (c : T3) (hE : Edis r1 r2 r3 (a, b, c)) :
    (1 / 2 : ℝ) * (δ * Fintype.card T2) * (δ * Fintype.card T3) ≤ cnt1 r1 r2 r3 a ∨
    (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T3) ≤ cnt2 r1 r2 r3 b ∨
    (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T2) ≤ cnt3 r1 r2 r3 c := by
  unfold Edis at hE
  simp only at hE
  by_cases h12 : r1 a (b, c) = r2 b (a, c)
  · have h23 : r2 b (a, c) ≠ r3 c (a, b) := fun e => hE ⟨h12, e⟩
    rcases main23 D1 D2 D3 δ hδ h1 h2 h3 r1 r2 r3 hr1 hr2 hr3 a b c h23 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases main12 D1 D2 D3 δ hδ h1 h2 h3 r1 r2 r3 hr1 hr2 hr3 a b c h12 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]

/-- an extension operator from a set `S` that determines codewords of `D` -/
lemma ext_op {α : Type} [Fintype α] (D : Submodule F (α → F)) (S : Finset α)
    (hinj : ∀ u ∈ D, (∀ x ∈ S, u x = 0) → u = 0) :
    ∃ E : (α → F) →ₗ[F] (α → F), (∀ v, E v ∈ D) ∧
      (∀ u ∈ D, ∀ v, (∀ x ∈ S, v x = u x) → E v = u) ∧
      (∀ v, E v = ∑ x ∈ S, v x • E (Pi.single x 1)) := by
  let ρ : D →ₗ[F] (↥S → F) :=
    { toFun := fun u x => (u : α → F) x
      map_add' := by intro u u'; funext x; simp
      map_smul' := by intro c u; funext x; simp }
  have hker : LinearMap.ker ρ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    apply Subtype.ext
    apply hinj u u.2
    intro x hx
    have := congrFun hu ⟨x, hx⟩
    simpa [ρ] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective ρ hker
  let R : (α → F) →ₗ[F] (↥S → F) :=
    { toFun := fun v x => v x
      map_add' := by intro u u'; funext x; simp
      map_smul' := by intro c u; funext x; simp }
  refine ⟨D.subtype.comp (L.comp R), fun v => (L (R v)).2, ?_, ?_⟩
  · intro u hu v hv
    have hRv : R v = ρ ⟨u, hu⟩ := by funext x; simp [R, ρ, hv x x.2]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hRv]
    have := congrArg (fun f => f ⟨u, hu⟩) hL
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at this
    rw [this]
  · intro v
    have hRv : R v = R (∑ x ∈ S, v x • Pi.single x 1) := by
      funext y
      simp only [R, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single y.1]
      · simp
      · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
      · intro h; exact absurd y.2 h
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hRv, map_sum, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, map_smul]; rfl

/-- linear combinations of restricted codewords -/
lemma comb_mem {α β : Type} (D : Submodule F (α → F)) (S' : Finset α) (X : Finset β)
    (lam : β → F) (f : β → α → F) (hf : ∀ x ∈ X, ∃ u ∈ D, ∀ y ∈ S', u y = f x y) :
    ∃ u ∈ D, ∀ y ∈ S', u y = ∑ x ∈ X, lam x * f x y := by
  choose u hu hu' using hf
  refine ⟨∑ x ∈ X.attach, lam x • u x.1 x.2, D.sum_mem fun x _ => D.smul_mem _ (hu _ _), ?_⟩
  intro y hy
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_attach X (fun x => lam x * f x y)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hu' _ _ y hy]

lemma comb_mem' {α β : Type} (D : Submodule F (α → F)) (X : Finset β)
    (lam : β → F) (f : β → α → F) (hf : ∀ x ∈ X, f x ∈ D) :
    (fun y => ∑ x ∈ X, lam x * f x y) ∈ D := by
  have : (fun y => ∑ x ∈ X, lam x * f x y) = ∑ x ∈ X, lam x • f x := by
    funext y; simp [Finset.sum_apply, smul_eq_mul]
  rw [this]
  exact D.sum_mem fun x hx => D.smul_mem _ (hf x hx)

variable {T1 T2 T3 : Type} [Fintype T1] [Fintype T2] [Fintype T3]
variable (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F)) (D3 : Submodule F (T3 → F))

theorem extend3 (S1 : Finset T1) (S2 : Finset T2) (S3 : Finset T3)
    (hi1 : ∀ u ∈ D1, (∀ x ∈ S1, u x = 0) → u = 0)
    (hi2 : ∀ u ∈ D2, (∀ x ∈ S2, u x = 0) → u = 0)
    (hi3 : ∀ u ∈ D3, (∀ x ∈ S3, u x = 0) → u = 0)
    (g : T1 × T2 × T3 → F)
    (hg1 : ∀ b ∈ S2, ∀ c ∈ S3, ∃ u ∈ D1, ∀ a ∈ S1, u a = g (a, b, c))
    (hg2 : ∀ a ∈ S1, ∀ c ∈ S3, ∃ u ∈ D2, ∀ b ∈ S2, u b = g (a, b, c))
    (hg3 : ∀ a ∈ S1, ∀ b ∈ S2, ∃ u ∈ D3, ∀ c ∈ S3, u c = g (a, b, c)) :
    ∃ cw ∈ tens3 D1 D2 D3, ∀ a ∈ S1, ∀ b ∈ S2, ∀ c ∈ S3, cw (a, b, c) = g (a, b, c) := by
  obtain ⟨E1, hE1m, hE1u, hE1s⟩ := ext_op D1 S1 hi1
  obtain ⟨E2, hE2m, hE2u, hE2s⟩ := ext_op D2 S2 hi2
  obtain ⟨E3, hE3m, hE3u, hE3s⟩ := ext_op D3 S3 hi3
  -- step 1
  let G1 : T1 × T2 × T3 → F := fun p => E1 (fun a' => g (a', p.2.1, p.2.2)) p.1
  have G1eq : ∀ a b c, G1 (a, b, c) = ∑ x ∈ S1, g (x, b, c) * E1 (Pi.single x 1) a := by
    intro a b c
    simp only [G1]
    rw [hE1s]; simp [Finset.sum_apply, smul_eq_mul]
  have P1a : ∀ b ∈ S2, ∀ c ∈ S3, (fun a => G1 (a, b, c)) ∈ D1 ∧ ∀ a ∈ S1, G1 (a, b, c) = g (a, b, c) := by
    intro b hb c hc
    refine ⟨hE1m (fun a' => g (a', b, c)), fun a ha => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hg1 b hb c hc
    simp only [G1]
    rw [hE1u u hu _ (fun x hx => (hu' x hx).symm)]
    exact hu' a ha
  have P1b : ∀ a, ∀ c ∈ S3, ∃ u ∈ D2, ∀ b ∈ S2, u b = G1 (a, b, c) := by
    intro a c hc
    have := comb_mem D2 S2 S1 (fun x => E1 (Pi.single x 1) a) (fun x b => g (x, b, c))
      (fun x hx => hg2 x hx c hc)
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, hu, fun b hb => by rw [hu' b hb, G1eq]; exact Finset.sum_congr rfl fun x _ => by ring⟩
  have P1c : ∀ a, ∀ b ∈ S2, ∃ u ∈ D3, ∀ c ∈ S3, u c = G1 (a, b, c) := by
    intro a b hb
    have := comb_mem D3 S3 S1 (fun x => E1 (Pi.single x 1) a) (fun x c => g (x, b, c))
      (fun x hx => hg3 x hx b hb)
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, hu, fun c hc => by rw [hu' c hc, G1eq]; exact Finset.sum_congr rfl fun x _ => by ring⟩
  -- step 2
  let G2 : T1 × T2 × T3 → F := fun p => E2 (fun b' => G1 (p.1, b', p.2.2)) p.2.1
  have G2eq : ∀ a b c, G2 (a, b, c) = ∑ y ∈ S2, G1 (a, y, c) * E2 (Pi.single y 1) b := by
    intro a b c
    simp only [G2]
    rw [hE2s]; simp [Finset.sum_apply, smul_eq_mul]
  have P2a : ∀ a, ∀ c ∈ S3, (fun b => G2 (a, b, c)) ∈ D2 ∧ ∀ b ∈ S2, G2 (a, b, c) = G1 (a, b, c) := by
    intro a c hc
    refine ⟨hE2m (fun b' => G1 (a, b', c)), fun b hb => ?_⟩
    obtain ⟨u, hu, hu'⟩ := P1b a c hc
    simp only [G2]
    rw [hE2u u hu _ (fun x hx => (hu' x hx).symm)]
    exact hu' b hb
  have P2b : ∀ b, ∀ c ∈ S3, (fun a => G2 (a, b, c)) ∈ D1 := by
    intro b c hc
    have : (fun a => G2 (a, b, c)) = fun a => ∑ y ∈ S2, E2 (Pi.single y 1) b * G1 (a, y, c) := by
      funext a; rw [G2eq]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [this]
    exact comb_mem' D1 S2 _ (fun y a => G1 (a, y, c)) (fun y hy => (P1a y hy c hc).1)
  have P2c : ∀ a b, ∃ u ∈ D3, ∀ c ∈ S3, u c = G2 (a, b, c) := by
    intro a b
    have := comb_mem D3 S3 S2 (fun y => E2 (Pi.single y 1) b) (fun y c => G1 (a, y, c))
      (fun y hy => P1c a y hy)
    obtain ⟨u, hu, hu'⟩ := this
    exact ⟨u, hu, fun c hc => by rw [hu' c hc, G2eq]; exact Finset.sum_congr rfl fun x _ => by ring⟩
  -- step 3
  let G3 : T1 × T2 × T3 → F := fun p => E3 (fun c' => G2 (p.1, p.2.1, c')) p.2.2
  have G3eq : ∀ a b c, G3 (a, b, c) = ∑ z ∈ S3, G2 (a, b, z) * E3 (Pi.single z 1) c := by
    intro a b c
    simp only [G3]
    rw [hE3s]; simp [Finset.sum_apply, smul_eq_mul]
  have P3a : ∀ a b, ∀ c ∈ S3, G3 (a, b, c) = G2 (a, b, c) := by
    intro a b c hc
    obtain ⟨u, hu, hu'⟩ := P2c a b
    simp only [G3]
    rw [hE3u u hu _ (fun x hx => (hu' x hx).symm)]
    exact hu' c hc
  refine ⟨G3, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro b c
    have : (fun a => G3 (a, b, c)) = fun a => ∑ z ∈ S3, E3 (Pi.single z 1) c * G2 (a, b, z) := by
      funext a; rw [G3eq]; exact Finset.sum_congr rfl fun z _ => by ring
    rw [this]
    exact comb_mem' D1 S3 _ (fun z a => G2 (a, b, z)) (fun z hz => P2b b z hz)
  · intro a c
    have : (fun b => G3 (a, b, c)) = fun b => ∑ z ∈ S3, E3 (Pi.single z 1) c * G2 (a, b, z) := by
      funext b; rw [G3eq]; exact Finset.sum_congr rfl fun z _ => by ring
    rw [this]
    exact comb_mem' D2 S3 _ (fun z b => G2 (a, b, z)) (fun z hz => (P2a a z hz).1)
  · intro a b
    exact hE3m (fun c' => G2 (a, b, c'))
  · intro a ha b hb c hc
    rw [P3a a b c hc, (P2a a c hc).2 b hb, (P1a b hb c hc).2 a ha]

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {T1 T2 T3 : Type} [Fintype T1] [Fintype T2] [Fintype T3]
variable (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F)) (D3 : Submodule F (T3 → F))

lemma exists_nearest {α : Type} [Fintype α] (x : α → F) (E : Submodule F (α → F)) :
    ∃ y ∈ E, supportCard (x - y) = distTo x E :=
  Nat.sInf_mem (s := {d | ∃ y ∈ E, supportCard (x - y) = d}) ⟨_, 0, E.zero_mem, rfl⟩

lemma distTo_le' {α : Type} [Fintype α] (x y : α → F) (E : Submodule F (α → F)) (hy : y ∈ E) :
    distTo x E ≤ supportCard (x - y) := Nat.sInf_le ⟨y, hy, rfl⟩

lemma supportCard_le_card {α : Type} [Fintype α] (x : α → F) : supportCard x ≤ Fintype.card α := by
  unfold supportCard; exact Finset.card_le_univ _

/-- the three slice sums, as point counts -/
lemma slice_sum1 (w : T1 × T2 × T3 → F) (r1 : T1 → T2 × T3 → F) :
    ∑ a, supportCard ((fun q : T2 × T3 => w (a, q.1, q.2)) - r1 a) =
      (Finset.univ.filter fun p : T1 × T2 × T3 => w p ≠ r1 p.1 (p.2.1, p.2.2)).card := by
  unfold supportCard
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun s _ => (s.1, s.2.1, s.2.2))
  · intro s hs; simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.sub_apply, sub_ne_zero] at hs ⊢; exact hs
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨a, q⟩ := s; obtain ⟨b, q'⟩ := t
    simp only at h; obtain ⟨rfl, h2, h3⟩ := h
    have : q = q' := Prod.ext h2 h3
    subst this; rfl
  · intro p hp
    refine ⟨⟨p.1, (p.2.1, p.2.2)⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply,
      sub_ne_zero] at hp ⊢
    exact hp

lemma slice_sum2 (w : T1 × T2 × T3 → F) (r2 : T2 → T1 × T3 → F) :
    ∑ b, supportCard ((fun q : T1 × T3 => w (q.1, b, q.2)) - r2 b) =
      (Finset.univ.filter fun p : T1 × T2 × T3 => w p ≠ r2 p.2.1 (p.1, p.2.2)).card := by
  unfold supportCard
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun s _ => (s.2.1, s.1, s.2.2))
  · intro s hs; simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.sub_apply, sub_ne_zero] at hs ⊢; exact hs
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨a, q⟩ := s; obtain ⟨b, q'⟩ := t
    simp only at h; obtain ⟨h1, rfl, h3⟩ := h
    have : q = q' := Prod.ext h1 h3
    subst this; rfl
  · intro p hp
    refine ⟨⟨p.2.1, (p.1, p.2.2)⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply,
      sub_ne_zero] at hp ⊢
    exact hp

lemma slice_sum3 (w : T1 × T2 × T3 → F) (r3 : T3 → T1 × T2 → F) :
    ∑ c, supportCard ((fun q : T1 × T2 => w (q.1, q.2, c)) - r3 c) =
      (Finset.univ.filter fun p : T1 × T2 × T3 => w p ≠ r3 p.2.2 (p.1, p.2.1)).card := by
  unfold supportCard
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun s _ => (s.2.1, s.2.2, s.1))
  · intro s hs; simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.sub_apply, sub_ne_zero] at hs ⊢; exact hs
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨a, q⟩ := s; obtain ⟨b, q'⟩ := t
    simp only at h; obtain ⟨h1, h2, rfl⟩ := h
    have : q = q' := Prod.ext h1 h2
    subst this; rfl
  · intro p hp
    refine ⟨⟨p.2.2, (p.1, p.2.1)⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply,
      sub_ne_zero] at hp ⊢
    exact hp

lemma sum_cnt1 (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F) :
    ∑ a, cnt1 r1 r2 r3 a = (Finset.univ.filter fun p => Edis r1 r2 r3 p).card := by
  unfold cnt1
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun s _ => (s.1, s.2.1, s.2.2))
  · intro s hs; simpa using hs
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨a, q⟩ := s; obtain ⟨b, q'⟩ := t
    simp only at h; obtain ⟨rfl, h2, h3⟩ := h
    have : q = q' := Prod.ext h2 h3
    subst this; rfl
  · intro p hp; exact ⟨⟨p.1, (p.2.1, p.2.2)⟩, by simpa using hp, rfl⟩

lemma sum_cnt2 (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F) :
    ∑ b, cnt2 r1 r2 r3 b = (Finset.univ.filter fun p => Edis r1 r2 r3 p).card := by
  unfold cnt2
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun s _ => (s.2.1, s.1, s.2.2))
  · intro s hs; simpa using hs
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨a, q⟩ := s; obtain ⟨b, q'⟩ := t
    simp only at h; obtain ⟨h1, rfl, h3⟩ := h
    have : q = q' := Prod.ext h1 h3
    subst this; rfl
  · intro p hp; exact ⟨⟨p.2.1, (p.1, p.2.2)⟩, by simpa using hp, rfl⟩

lemma sum_cnt3 (r1 : T1 → T2 × T3 → F) (r2 : T2 → T1 × T3 → F) (r3 : T3 → T1 × T2 → F) :
    ∑ c, cnt3 r1 r2 r3 c = (Finset.univ.filter fun p => Edis r1 r2 r3 p).card := by
  unfold cnt3
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun s _ => (s.2.1, s.2.2, s.1))
  · intro s hs; simpa using hs
  · intro s _ t _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨a, q⟩ := s; obtain ⟨b, q'⟩ := t
    simp only at h; obtain ⟨h1, h2, rfl⟩ := h
    have : q = q' := Prod.ext h1 h2
    subst this; rfl
  · intro p hp; exact ⟨⟨p.2.2, (p.1, p.2.1)⟩, by simpa using hp, rfl⟩

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {T1 T2 T3 : Type} [Fintype T1] [Fintype T2] [Fintype T3]
variable (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F)) (D3 : Submodule F (T3 → F))

lemma heavy_card {T : Type} [Fintype T] (cnt : T → ℕ) (thr : ℝ) (hthr : 0 < thr) (Etot : ℕ)
    (hsum : ∑ a, cnt a = Etot) :
    ((Finset.univ.filter fun a => thr ≤ cnt a).card : ℝ) ≤ Etot / thr := by
  rw [le_div_iff₀ hthr]
  calc ((Finset.univ.filter fun a => thr ≤ cnt a).card : ℝ) * thr
      = ∑ _a ∈ Finset.univ.filter (fun a => thr ≤ cnt a), thr := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a => thr ≤ cnt a), (cnt a : ℝ) :=
        Finset.sum_le_sum fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑ a, (cnt a : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by positivity)
    _ = Etot := by rw [← hsum]; push_cast; rfl

lemma inj_of_small {α : Type} [Fintype α] (D : Submodule F (α → F)) (δ : ℝ) (hD : HasDist D δ)
    (H : Finset α) (hH : (H.card : ℝ) < δ * Fintype.card α) :
    ∀ u ∈ D, (∀ x ∈ Finset.univ \ H, u x = 0) → u = 0 := by
  intro u hu h0
  by_contra hne
  have := hD u hu hne
  have hsub : (Finset.univ.filter fun x => u x ≠ 0) ⊆ H := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hxH
    exact hx (h0 x (by simp [hxH]))
  have := Finset.card_le_card hsub
  unfold wt at *
  have : ((Finset.univ.filter fun x => u x ≠ 0).card : ℝ) ≤ H.card := by exact_mod_cast this
  linarith

/-- **Viderman's theorem** for three factors (robustness of the plane test). -/
theorem viderman3 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (h1 : HasDist D1 δ) (h2 : HasDist D2 δ)
    (h3 : HasDist D3 δ) (w : T1 × T2 × T3 → F) :
    δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤
      ((∑ a, distTo (fun q : T2 × T3 => w (a, q.1, q.2)) (tens2 D2 D3) +
        ∑ b, distTo (fun q : T1 × T3 => w (q.1, b, q.2)) (tens2 D1 D3) +
        ∑ c, distTo (fun q : T1 × T2 => w (q.1, q.2, c)) (tens2 D1 D2) : ℕ) : ℝ) := by
  -- nearest opinions
  have e1 := fun a => exists_nearest (fun q : T2 × T3 => w (a, q.1, q.2)) (tens2 D2 D3)
  have e2 := fun b => exists_nearest (fun q : T1 × T3 => w (q.1, b, q.2)) (tens2 D1 D3)
  have e3 := fun c => exists_nearest (fun q : T1 × T2 => w (q.1, q.2, c)) (tens2 D1 D2)
  choose r1 hr1 hd1 using e1
  choose r2 hr2 hd2 using e2
  choose r3 hr3 hd3 using e3
  set Etot := (Finset.univ.filter fun p => Edis r1 r2 r3 p).card with hEtot
  set ToFix := (Finset.univ.filter fun p : T1 × T2 × T3 =>
    ¬ Edis r1 r2 r3 p ∧ w p ≠ r1 p.1 (p.2.1, p.2.2)).card with hToFix
  set N := Fintype.card (T1 × T2 × T3) with hN
  -- Proposition 4.1
  have hsum : Etot + 3 * ToFix ≤
      (∑ a, distTo (fun q : T2 × T3 => w (a, q.1, q.2)) (tens2 D2 D3) +
        ∑ b, distTo (fun q : T1 × T3 => w (q.1, b, q.2)) (tens2 D1 D3) +
        ∑ c, distTo (fun q : T1 × T2 => w (q.1, q.2, c)) (tens2 D1 D2)) := by
    simp_rw [← hd1, ← hd2, ← hd3]
    rw [slice_sum1, slice_sum2, slice_sum3, hEtot, hToFix]
    simp only [Finset.card_filter]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hE : Edis r1 r2 r3 p
    · have : ¬ (w p = r1 p.1 (p.2.1, p.2.2) ∧ w p = r2 p.2.1 (p.1, p.2.2) ∧
          w p = r3 p.2.2 (p.1, p.2.1)) := by
        rintro ⟨e1, e2, e3⟩; exact hE ⟨e1.symm.trans e2, e2.symm.trans e3⟩
      simp only [hE, if_true, not_true_eq_false, false_and, if_false]
      by_cases a1 : w p = r1 p.1 (p.2.1, p.2.2) <;> by_cases a2 : w p = r2 p.2.1 (p.1, p.2.2) <;>
        by_cases a3 : w p = r3 p.2.2 (p.1, p.2.1) <;> simp_all
    · unfold Edis at hE; push Not at hE
      have hE' : ¬ Edis r1 r2 r3 p := by unfold Edis; push Not; exact hE
      simp only [hE', if_false, not_false_eq_true, true_and]
      by_cases a1 : w p = r1 p.1 (p.2.1, p.2.2)
      · simp [a1]
      · have a2 : w p ≠ r2 p.2.1 (p.1, p.2.2) := by rw [← hE.1]; exact a1
        have a3 : w p ≠ r3 p.2.2 (p.1, p.2.1) := by rw [← hE.2, ← hE.1]; exact a1
        simp [a1, a2, a3]
  have hdistN : (distTo w (tens3 D1 D2 D3) : ℝ) ≤ N := by
    have := distTo_le' w 0 (tens3 D1 D2 D3) (Submodule.zero_mem _)
    rw [sub_zero] at this
    exact_mod_cast this.trans (supportCard_le_card w)
  have hδ3 : 0 ≤ δ ^ 3 / 6 := by positivity
  by_cases hcase : δ ^ 3 / 6 * N ≤ Etot
  · calc δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤ δ ^ 3 / 6 * N :=
          mul_le_mul_of_nonneg_left hdistN hδ3
      _ ≤ Etot := hcase
      _ ≤ _ := by exact_mod_cast (Nat.le_add_right _ _).trans hsum
  push Not at hcase
  -- heavy planes
  have hT1 : (0 : ℝ) ≤ Fintype.card T1 := by positivity
  have hT2 : (0 : ℝ) ≤ Fintype.card T2 := by positivity
  have hT3 : (0 : ℝ) ≤ Fintype.card T3 := by positivity
  have hNeq : (N : ℝ) = Fintype.card T1 * Fintype.card T2 * Fintype.card T3 := by
    rw [hN, Fintype.card_prod, Fintype.card_prod]; push_cast; ring
  -- if some factor is empty the word is empty
  rcases (eq_or_lt_of_le hT1) with e | hT1p
  · have e' : Fintype.card T1 = 0 := by exact_mod_cast e.symm
    have : N = 0 := by rw [hN, Fintype.card_prod, e', zero_mul]
    have h0 : (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 0 := by rw [this] at hdistN; exact_mod_cast hdistN
    calc δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ3 h0
      _ ≤ _ := by positivity
  rcases (eq_or_lt_of_le hT2) with e | hT2p
  · have e' : Fintype.card T2 = 0 := by exact_mod_cast e.symm
    have : N = 0 := by rw [hN, Fintype.card_prod, Fintype.card_prod, e', zero_mul, mul_zero]
    have h0 : (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 0 := by rw [this] at hdistN; exact_mod_cast hdistN
    calc δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ3 h0
      _ ≤ _ := by positivity
  rcases (eq_or_lt_of_le hT3) with e | hT3p
  · have e' : Fintype.card T3 = 0 := by exact_mod_cast e.symm
    have : N = 0 := by rw [hN, Fintype.card_prod, Fintype.card_prod, e', mul_zero, mul_zero]
    have h0 : (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 0 := by rw [this] at hdistN; exact_mod_cast hdistN
    calc δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ3 h0
      _ ≤ _ := by positivity
  set thr1 := (1 / 2 : ℝ) * (δ * Fintype.card T2) * (δ * Fintype.card T3)
  set thr2 := (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T3)
  set thr3 := (1 / 2 : ℝ) * (δ * Fintype.card T1) * (δ * Fintype.card T2)
  have hthr1 : 0 < thr1 := by positivity
  have hthr2 : 0 < thr2 := by positivity
  have hthr3 : 0 < thr3 := by positivity
  set H1 := Finset.univ.filter fun a => thr1 ≤ cnt1 r1 r2 r3 a
  set H2 := Finset.univ.filter fun b => thr2 ≤ cnt2 r1 r2 r3 b
  set H3 := Finset.univ.filter fun c => thr3 ≤ cnt3 r1 r2 r3 c
  have hH1 : (H1.card : ℝ) ≤ Etot / thr1 := heavy_card _ thr1 hthr1 Etot (sum_cnt1 r1 r2 r3)
  have hH2 : (H2.card : ℝ) ≤ Etot / thr2 := heavy_card _ thr2 hthr2 Etot (sum_cnt2 r1 r2 r3)
  have hH3 : (H3.card : ℝ) ≤ Etot / thr3 := heavy_card _ thr3 hthr3 Etot (sum_cnt3 r1 r2 r3)
  have hsmall1 : (H1.card : ℝ) < δ * Fintype.card T1 := by
    refine lt_of_le_of_lt hH1 ?_
    rw [div_lt_iff₀ hthr1]
    calc (Etot : ℝ) < δ ^ 3 / 6 * N := hcase
      _ = δ * Fintype.card T1 * thr1 / 3 := by rw [hNeq]; ring
      _ ≤ δ * Fintype.card T1 * thr1 := by
          have : 0 ≤ δ * Fintype.card T1 * thr1 := by positivity
          linarith
  have hsmall2 : (H2.card : ℝ) < δ * Fintype.card T2 := by
    refine lt_of_le_of_lt hH2 ?_
    rw [div_lt_iff₀ hthr2]
    calc (Etot : ℝ) < δ ^ 3 / 6 * N := hcase
      _ = δ * Fintype.card T2 * thr2 / 3 := by rw [hNeq]; ring
      _ ≤ δ * Fintype.card T2 * thr2 := by
          have : 0 ≤ δ * Fintype.card T2 * thr2 := by positivity
          linarith
  have hsmall3 : (H3.card : ℝ) < δ * Fintype.card T3 := by
    refine lt_of_le_of_lt hH3 ?_
    rw [div_lt_iff₀ hthr3]
    calc (Etot : ℝ) < δ ^ 3 / 6 * N := hcase
      _ = δ * Fintype.card T3 * thr3 / 3 := by rw [hNeq]; ring
      _ ≤ δ * Fintype.card T3 * thr3 := by
          have : 0 ≤ δ * Fintype.card T3 * thr3 := by positivity
          linarith
  -- consistency off the heavy planes
  have hcons : ∀ a ∉ H1, ∀ b ∉ H2, ∀ c ∉ H3, ¬ Edis r1 r2 r3 (a, b, c) := by
    intro a ha b hb c hc hE
    rcases E_heavy D1 D2 D3 δ hδ0.le h1 h2 h3 r1 r2 r3 hr1 hr2 hr3 a b c hE with h | h | h
    · exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact hb (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact hc (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  set S1 := Finset.univ \ H1
  set S2 := Finset.univ \ H2
  set S3 := Finset.univ \ H3
  obtain ⟨cw, hcw, hcwS⟩ := extend3 D1 D2 D3 S1 S2 S3
    (inj_of_small D1 δ h1 H1 hsmall1) (inj_of_small D2 δ h2 H2 hsmall2)
    (inj_of_small D3 δ h3 H3 hsmall3) (fun p => r1 p.1 (p.2.1, p.2.2))
    (by
      intro b hb c hc
      refine ⟨fun a => r2 b (a, c), (hr2 b).1 c, fun a ha => ?_⟩
      have := hcons a (by simpa [S1] using ha) b (by simpa [S2] using hb) c (by simpa [S3] using hc)
      unfold Edis at this; push Not at this
      exact this.1.symm)
    (by
      intro a _ c _
      exact ⟨fun b => r1 a (b, c), (hr1 a).1 c, fun b _ => rfl⟩)
    (by
      intro a _ b _
      exact ⟨fun c => r1 a (b, c), (hr1 a).2 b, fun c _ => rfl⟩)
  -- the distance bound
  have hdist : (distTo w (tens3 D1 D2 D3) : ℝ) ≤
      H1.card * (Fintype.card T2 * Fintype.card T3) + H2.card * (Fintype.card T1 * Fintype.card T3) +
        H3.card * (Fintype.card T1 * Fintype.card T2) + ToFix := by
    have hle := distTo_le' w cw _ hcw
    have hsub : (Finset.univ.filter fun p => (w - cw) p ≠ 0) ⊆
        ((H1 ×ˢ (Finset.univ : Finset (T2 × T3))) ∪
          ((Finset.univ.filter fun p : T1 × T2 × T3 => p.2.1 ∈ H2) ∪
          (Finset.univ.filter fun p : T1 × T2 × T3 => p.2.2 ∈ H3))) ∪
        (Finset.univ.filter fun p : T1 × T2 × T3 =>
          ¬ Edis r1 r2 r3 p ∧ w p ≠ r1 p.1 (p.2.1, p.2.2)) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at hp
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_univ, and_true,
        Finset.mem_filter, true_and]
      by_cases ha : p.1 ∈ H1
      · exact Or.inl (Or.inl ha)
      by_cases hb : p.2.1 ∈ H2
      · exact Or.inl (Or.inr (Or.inl hb))
      by_cases hc : p.2.2 ∈ H3
      · exact Or.inl (Or.inr (Or.inr hc))
      right
      refine ⟨hcons p.1 ha p.2.1 hb p.2.2 hc, ?_⟩
      have := hcwS p.1 (by simp [S1, ha]) p.2.1 (by simp [S2, hb]) p.2.2 (by simp [S3, hc])
      intro e; apply hp; rw [e]; exact this.symm
    have hc1 : (H1 ×ˢ (Finset.univ : Finset (T2 × T3))).card = H1.card * (Fintype.card T2 * Fintype.card T3) := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_prod]
    have hc2 : (Finset.univ.filter fun p : T1 × T2 × T3 => p.2.1 ∈ H2).card =
        H2.card * (Fintype.card T1 * Fintype.card T3) := by
      have : (Finset.univ.filter fun p : T1 × T2 × T3 => p.2.1 ∈ H2) =
          (Finset.univ : Finset T1) ×ˢ (H2 ×ˢ (Finset.univ : Finset T3)) := by ext p; simp
      rw [this, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ]; ring
    have hc3 : (Finset.univ.filter fun p : T1 × T2 × T3 => p.2.2 ∈ H3).card =
        H3.card * (Fintype.card T1 * Fintype.card T2) := by
      have : (Finset.univ.filter fun p : T1 × T2 × T3 => p.2.2 ∈ H3) =
          (Finset.univ : Finset T1) ×ˢ ((Finset.univ : Finset T2) ×ˢ H3) := by ext p; simp
      rw [this, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ]; ring
    have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _)) _))
    rw [hc1, hc2, hc3] at hcard
    have : (distTo w (tens3 D1 D2 D3) : ℝ) ≤ (supportCard (w - cw) : ℝ) := by exact_mod_cast hle
    unfold supportCard at this
    refine this.trans ?_
    rw [hToFix]
    have hr : (((Finset.univ.filter fun p => (w - cw) p ≠ 0).card : ℕ) : ℝ) ≤
        (H1.card * (Fintype.card T2 * Fintype.card T3) +
          (H2.card * (Fintype.card T1 * Fintype.card T3) + H3.card * (Fintype.card T1 * Fintype.card T2)) +
          (Finset.univ.filter fun p : T1 × T2 × T3 =>
            ¬ Edis r1 r2 r3 p ∧ w p ≠ r1 p.1 (p.2.1, p.2.2)).card : ℕ) := by exact_mod_cast hcard
    push_cast at hr
    linarith
  -- conclude
  have hb1 : (H1.card : ℝ) * (Fintype.card T2 * Fintype.card T3) ≤ 2 * Etot / δ ^ 2 := by
    have hpos : (0 : ℝ) < Fintype.card T2 * Fintype.card T3 := by positivity
    calc (H1.card : ℝ) * (Fintype.card T2 * Fintype.card T3)
        ≤ Etot / thr1 * (Fintype.card T2 * Fintype.card T3) :=
          mul_le_mul_of_nonneg_right hH1 hpos.le
      _ = 2 * Etot / δ ^ 2 := by
          simp only [thr1]
          field_simp
  have hb2 : (H2.card : ℝ) * (Fintype.card T1 * Fintype.card T3) ≤ 2 * Etot / δ ^ 2 := by
    have hpos : (0 : ℝ) < Fintype.card T1 * Fintype.card T3 := by positivity
    calc (H2.card : ℝ) * (Fintype.card T1 * Fintype.card T3)
        ≤ Etot / thr2 * (Fintype.card T1 * Fintype.card T3) :=
          mul_le_mul_of_nonneg_right hH2 hpos.le
      _ = 2 * Etot / δ ^ 2 := by
          simp only [thr2]
          field_simp
  have hb3 : (H3.card : ℝ) * (Fintype.card T1 * Fintype.card T2) ≤ 2 * Etot / δ ^ 2 := by
    have hpos : (0 : ℝ) < Fintype.card T1 * Fintype.card T2 := by positivity
    calc (H3.card : ℝ) * (Fintype.card T1 * Fintype.card T2)
        ≤ Etot / thr3 * (Fintype.card T1 * Fintype.card T2) :=
          mul_le_mul_of_nonneg_right hH3 hpos.le
      _ = 2 * Etot / δ ^ 2 := by
          simp only [thr3]
          field_simp
  have hfinal : δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤ Etot + 3 * ToFix := by
    have hd' : (distTo w (tens3 D1 D2 D3) : ℝ) ≤ 6 * Etot / δ ^ 2 + ToFix := by
      have := hdist
      have e6 : 6 * (Etot : ℝ) / δ ^ 2 = 2 * Etot / δ ^ 2 + 2 * Etot / δ ^ 2 + 2 * Etot / δ ^ 2 := by ring
      rw [e6]; linarith
    have hδ2 : 0 < δ ^ 2 := by positivity
    calc δ ^ 3 / 6 * (distTo w (tens3 D1 D2 D3) : ℝ) ≤ δ ^ 3 / 6 * (6 * Etot / δ ^ 2 + ToFix) :=
          mul_le_mul_of_nonneg_left hd' hδ3
      _ = δ * Etot + δ ^ 3 / 6 * ToFix := by field_simp
      _ ≤ Etot + 3 * ToFix := by
          have hE0 : (0 : ℝ) ≤ Etot := by positivity
          have hT0 : (0 : ℝ) ≤ ToFix := by positivity
          have : δ ^ 3 ≤ 1 := pow_le_one₀ hδ0.le hδ1
          nlinarith
  refine hfinal.trans ?_
  exact_mod_cast hsum

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {T1 T2 : Type} [Fintype T1] [Fintype T2]
variable (D1 : Submodule F (T1 → F)) (D2 : Submodule F (T2 → F))

theorem extend2 (S1 : Finset T1) (S2 : Finset T2)
    (hi1 : ∀ u ∈ D1, (∀ x ∈ S1, u x = 0) → u = 0)
    (hi2 : ∀ u ∈ D2, (∀ x ∈ S2, u x = 0) → u = 0)
    (g : T1 × T2 → F)
    (hg1 : ∀ b ∈ S2, ∃ u ∈ D1, ∀ a ∈ S1, u a = g (a, b))
    (hg2 : ∀ a ∈ S1, ∃ u ∈ D2, ∀ b ∈ S2, u b = g (a, b)) :
    ∃ cw ∈ tens2 D1 D2, ∀ a ∈ S1, ∀ b ∈ S2, cw (a, b) = g (a, b) := by
  obtain ⟨E1, hE1m, hE1u, hE1s⟩ := ext_op D1 S1 hi1
  obtain ⟨E2, hE2m, hE2u, hE2s⟩ := ext_op D2 S2 hi2
  let G1 : T1 × T2 → F := fun p => E1 (fun a' => g (a', p.2)) p.1
  have G1eq : ∀ a b, G1 (a, b) = ∑ x ∈ S1, g (x, b) * E1 (Pi.single x 1) a := by
    intro a b; simp only [G1]; rw [hE1s]; simp [Finset.sum_apply, smul_eq_mul]
  have P1a : ∀ b ∈ S2, (fun a => G1 (a, b)) ∈ D1 ∧ ∀ a ∈ S1, G1 (a, b) = g (a, b) := by
    intro b hb
    refine ⟨hE1m (fun a' => g (a', b)), fun a ha => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hg1 b hb
    simp only [G1]
    rw [hE1u u hu _ (fun x hx => (hu' x hx).symm)]
    exact hu' a ha
  have P1b : ∀ a, ∃ u ∈ D2, ∀ b ∈ S2, u b = G1 (a, b) := by
    intro a
    obtain ⟨u, hu, hu'⟩ := comb_mem D2 S2 S1 (fun x => E1 (Pi.single x 1) a) (fun x b => g (x, b))
      (fun x hx => hg2 x hx)
    exact ⟨u, hu, fun b hb => by rw [hu' b hb, G1eq]; exact Finset.sum_congr rfl fun x _ => by ring⟩
  let G2 : T1 × T2 → F := fun p => E2 (fun b' => G1 (p.1, b')) p.2
  have G2eq : ∀ a b, G2 (a, b) = ∑ y ∈ S2, G1 (a, y) * E2 (Pi.single y 1) b := by
    intro a b; simp only [G2]; rw [hE2s]; simp [Finset.sum_apply, smul_eq_mul]
  have P2a : ∀ a, ∀ b ∈ S2, G2 (a, b) = G1 (a, b) := by
    intro a b hb
    obtain ⟨u, hu, hu'⟩ := P1b a
    simp only [G2]
    rw [hE2u u hu _ (fun x hx => (hu' x hx).symm)]
    exact hu' b hb
  refine ⟨G2, ⟨?_, ?_⟩, ?_⟩
  · intro b
    have : (fun a => G2 (a, b)) = fun a => ∑ y ∈ S2, E2 (Pi.single y 1) b * G1 (a, y) := by
      funext a; rw [G2eq]; exact Finset.sum_congr rfl fun y _ => by ring
    rw [this]
    exact comb_mem' D1 S2 _ (fun y a => G1 (a, y)) (fun y hy => (P1a y hy).1)
  · intro a; exact hE2m (fun b' => G1 (a, b'))
  · intro a ha b hb; rw [P2a a b hb, (P1a b hb).2 a ha]

/-- **Lemma B.3** (two-dimensional line consistency), in point counts: with `δ` a lower bound on
both relative distances, `δ · dist(w, D₁ ⊗ D₂)` is at most the number of points on bad columns plus
the number of points on bad rows. -/
theorem lineB3 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (h1 : HasDist D1 δ) (h2 : HasDist D2 δ)
    (w : T1 × T2 → F) :
    δ * (distTo w (tens2 D1 D2) : ℝ) ≤
      (Finset.univ.filter fun b => (fun a => w (a, b)) ∉ D1).card * (Fintype.card T1 : ℝ) +
      (Finset.univ.filter fun a => (fun b => w (a, b)) ∉ D2).card * (Fintype.card T2 : ℝ) := by
  set Bc := Finset.univ.filter fun b => (fun a => w (a, b)) ∉ D1 with hBc
  set Br := Finset.univ.filter fun a => (fun b => w (a, b)) ∉ D2 with hBr
  have hdN : (distTo w (tens2 D1 D2) : ℝ) ≤ Fintype.card T1 * Fintype.card T2 := by
    have := distTo_le' w 0 (tens2 D1 D2) (Submodule.zero_mem _)
    rw [sub_zero] at this
    have h' := this.trans (supportCard_le_card w)
    rw [Fintype.card_prod] at h'
    exact_mod_cast h'
  have hd0 : (0 : ℝ) ≤ distTo w (tens2 D1 D2) := by positivity
  by_cases hbig : δ * Fintype.card T2 ≤ Bc.card ∨ δ * Fintype.card T1 ≤ Br.card
  · rcases hbig with h | h
    · calc δ * (distTo w (tens2 D1 D2) : ℝ) ≤ δ * (Fintype.card T1 * Fintype.card T2) :=
            mul_le_mul_of_nonneg_left hdN hδ0.le
        _ = (δ * Fintype.card T2) * Fintype.card T1 := by ring
        _ ≤ Bc.card * Fintype.card T1 := mul_le_mul_of_nonneg_right h (by positivity)
        _ ≤ _ := by have : (0 : ℝ) ≤ Br.card * Fintype.card T2 := by positivity
                    linarith
    · calc δ * (distTo w (tens2 D1 D2) : ℝ) ≤ δ * (Fintype.card T1 * Fintype.card T2) :=
            mul_le_mul_of_nonneg_left hdN hδ0.le
        _ = (δ * Fintype.card T1) * Fintype.card T2 := by ring
        _ ≤ Br.card * Fintype.card T2 := mul_le_mul_of_nonneg_right h (by positivity)
        _ ≤ _ := by have : (0 : ℝ) ≤ Bc.card * Fintype.card T1 := by positivity
                    linarith
  push Not at hbig
  obtain ⟨hBcs, hBrs⟩ := hbig
  set G1 := Finset.univ \ Br
  set G2 := Finset.univ \ Bc
  have hi1 := inj_of_small D1 δ h1 Br hBrs
  have hi2 := inj_of_small D2 δ h2 Bc hBcs
  obtain ⟨cw, hcw, hcwG⟩ := extend2 D1 D2 G1 G2 hi1 hi2 w
    (fun b hb => ⟨fun a => w (a, b), by simpa [G2, hBc] using hb, fun a _ => rfl⟩)
    (fun a ha => ⟨fun b => w (a, b), by simpa [G1, hBr] using ha, fun b _ => rfl⟩)
  -- `cw` agrees with `w` on every good row
  have hrow : ∀ a ∈ G1, ∀ b, cw (a, b) = w (a, b) := by
    intro a ha
    have hwa : (fun b => w (a, b)) ∈ D2 := by simpa [G1, hBr] using ha
    have := hi2 ((fun b => cw (a, b)) - fun b => w (a, b)) (D2.sub_mem (hcw.2 a) hwa)
      (fun b hb => by simp [hcwG a ha b hb])
    intro b; exact sub_eq_zero.1 (congrFun this b)
  have hcol : ∀ b ∈ G2, ∀ a, cw (a, b) = w (a, b) := by
    intro b hb
    have hwb : (fun a => w (a, b)) ∈ D1 := by simpa [G2, hBc] using hb
    have := hi1 ((fun a => cw (a, b)) - fun a => w (a, b)) (D1.sub_mem (hcw.1 b) hwb)
      (fun a ha => by simp [hrow a ha b])
    intro a; exact sub_eq_zero.1 (congrFun this a)
  have hsub : (Finset.univ.filter fun p => (w - cw) p ≠ 0) ⊆ Br ×ˢ Bc := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at hp
    rw [Finset.mem_product]
    constructor
    · by_contra h; exact hp (hrow p.1 (by simp [G1, h]) p.2).symm
    · by_contra h; exact hp (hcol p.2 (by simp [G2, h]) p.1).symm
  have hd : (distTo w (tens2 D1 D2) : ℝ) ≤ Br.card * Bc.card := by
    have := (distTo_le' w cw _ hcw).trans (by unfold supportCard; exact Finset.card_le_card hsub)
    rw [Finset.card_product] at this
    exact_mod_cast this
  have hBc1 : (Bc.card : ℝ) ≤ Fintype.card T2 := by exact_mod_cast Finset.card_le_univ Bc
  calc δ * (distTo w (tens2 D1 D2) : ℝ) ≤ δ * (Br.card * Bc.card) := mul_le_mul_of_nonneg_left hd hδ0.le
    _ ≤ 1 * (Br.card * Fintype.card T2) := by
        have : (0 : ℝ) ≤ Br.card := by positivity
        have : (0 : ℝ) ≤ Bc.card := by positivity
        nlinarith
    _ ≤ _ := by have : (0 : ℝ) ≤ Bc.card * Fintype.card T1 := by positivity
                linarith

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

/-- the slice through `β` in the directions `A` -/
noncomputable def Sl (A : Finset ι) (β : ∀ i, S i) : Finset (∀ i, S i) :=
  Finset.univ.filter fun ω => ∀ i, i ∉ A → ω i = β i

lemma mem_Sl {A : Finset ι} {β ω : ∀ i, S i} : ω ∈ Sl A β ↔ ∀ i, i ∉ A → ω i = β i := by
  simp [Sl]

lemma self_mem_Sl (A : Finset ι) (β : ∀ i, S i) : β ∈ Sl A β := mem_Sl.2 fun _ _ => rfl

lemma update_mem_Sl {A : Finset ι} {β ω : ∀ i, S i} (h : ω ∈ Sl A β) {i : ι} (hi : i ∈ A)
    (s : S i) : Function.update ω i s ∈ Sl A β := by
  rw [mem_Sl] at h ⊢
  intro j hj
  have hji : j ≠ i := fun e => hj (e ▸ hi)
  rw [Function.update_of_ne hji, h j hj]

lemma Sl_card (A : Finset ι) (β : ∀ i, S i) : (Sl A β).card = ∏ i ∈ A, Fintype.card (S i) := by
  have : Sl A β = Fintype.piFinset (fun i => if i ∈ A then Finset.univ else {β i}) := by
    ext x
    simp only [mem_Sl, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ A
      · simp [hi]
      · simp [hi, h i hi]
    · intro h j hj
      have := h j
      simpa [hj] using this
  rw [this, Fintype.card_piFinset]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ A)]
  have h1 : ∏ x ∈ Finset.univ.filter (fun i => i ∈ A),
      (if x ∈ A then (Finset.univ : Finset (S x)) else {β x}).card = ∏ i ∈ A, Fintype.card (S i) := by
    rw [Finset.filter_univ_mem]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [hi]
  have h2 : ∏ x ∈ Finset.univ.filter (fun i => ¬ i ∈ A),
      (if x ∈ A then (Finset.univ : Finset (S x)) else {β x}).card = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  rw [h1, h2, mul_one]

/-- the `i`-line of `c` through `ω` lies in `C i` -/
def LOK (i : ι) (c : (∀ i, S i) → F) (ω : ∀ i, S i) : Prop :=
  (fun s => c (Function.update ω i s)) ∈ C i

lemma LOK_update {i : ι} {c : (∀ i, S i) → F} {ω : ∀ i, S i} (s : S i) :
    LOK C i c (Function.update ω i s) ↔ LOK C i c ω := by
  unfold LOK; simp only [Function.update_idem]

/-- the slice code -/
def sliceCode (A : Finset ι) (β : ∀ i, S i) : Submodule F ((∀ i, S i) → F) where
  carrier := {c | ∀ ω ∈ Sl A β, ∀ i ∈ A, LOK C i c ω}
  add_mem' := by
    intro c d hc hd ω hω i hi
    exact (C i).add_mem (hc ω hω i hi) (hd ω hω i hi)
  zero_mem' := by intro ω _ i _; exact (C i).zero_mem
  smul_mem' := by
    intro a c hc ω hω i hi
    exact (C i).smul_mem a (hc ω hω i hi)

lemma mem_sliceCode {A : Finset ι} {β : ∀ i, S i} {c : (∀ i, S i) → F} :
    c ∈ sliceCode C A β ↔ ∀ ω ∈ Sl A β, ∀ i ∈ A, LOK C i c ω := Iff.rfl

/-- number of points of the slice on bad `i`-lines -/
noncomputable def bad (A : Finset ι) (β : ∀ i, S i) (w : (∀ i, S i) → F) (i : ι) : ℕ :=
  ((Sl A β).filter fun ω => ¬ LOK C i w ω).card

/-- distance on the slice -/
noncomputable def sdist (A : Finset ι) (β : ∀ i, S i) (w : (∀ i, S i) → F) : ℕ :=
  sInf {d | ∃ c ∈ sliceCode C A β, ((Sl A β).filter fun ω => w ω ≠ c ω).card = d}

lemma sdist_le (A : Finset ι) (β : ∀ i, S i) (w c : (∀ i, S i) → F) (hc : c ∈ sliceCode C A β) :
    sdist C A β w ≤ ((Sl A β).filter fun ω => w ω ≠ c ω).card := Nat.sInf_le ⟨c, hc, rfl⟩

lemma exists_sdist (A : Finset ι) (β : ∀ i, S i) (w : (∀ i, S i) → F) :
    ∃ c ∈ sliceCode C A β, ((Sl A β).filter fun ω => w ω ≠ c ω).card = sdist C A β w :=
  Nat.sInf_mem (s := {d | ∃ c ∈ sliceCode C A β, ((Sl A β).filter fun ω => w ω ≠ c ω).card = d})
    ⟨_, 0, (sliceCode C A β).zero_mem, rfl⟩

lemma sliceCode_mono {A A' : Finset ι} {β β' : ∀ i, S i} (hA : A' ⊆ A)
    (hS : Sl A' β' ⊆ Sl A β) : sliceCode C A β ≤ sliceCode C A' β' := by
  intro c hc ω hω i hi
  exact hc ω (hS hω) i (hA hi)

/-- **distance of slice codes** -/
theorem slice_dist (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hC : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ wt c) (A : Finset ι) :
    ∀ (β : ∀ i, S i) (c : (∀ i, S i) → F), c ∈ sliceCode C A β → (∃ ω ∈ Sl A β, c ω ≠ 0) →
      Δ ^ A.card * (Sl A β).card ≤ ((Sl A β).filter fun ω => c ω ≠ 0).card := by
  induction A using Finset.induction_on with
  | empty =>
    intro β c _ ⟨ω, hω, hc⟩
    simp only [Finset.card_empty, pow_zero, one_mul]
    have : (Sl ∅ β).card = 1 := by rw [Sl_card]; simp
    rw [this]
    have : 0 < ((Sl ∅ β).filter fun ω => c ω ≠ 0).card :=
      Finset.card_pos.2 ⟨ω, Finset.mem_filter.2 ⟨hω, hc⟩⟩
    exact_mod_cast this
  | @insert i A hiA ih =>
    intro β c hc ⟨ω, hω, hcω⟩
    -- the `i`-line through `ω`
    have hline : (fun s => c (Function.update ω i s)) ∈ C i :=
      hc ω hω i (Finset.mem_insert_self i A)
    have hne : (fun s => c (Function.update ω i s)) ≠ 0 := by
      intro h; apply hcω; have := congrFun h (ω i); simpa using this
    have hcount := hC i _ hline hne
    set Good := Finset.univ.filter fun s => c (Function.update ω i s) ≠ 0 with hGood
    have hGc : Δ * Fintype.card (S i) ≤ Good.card := by
      unfold wt at hcount; exact hcount
    -- each good value gives a sub-slice with many nonzeros
    have hsub : ∀ s ∈ Good, Δ ^ A.card * (Sl A (Function.update β i s)).card ≤
        ((Sl A (Function.update β i s)).filter fun ω => c ω ≠ 0).card := by
      intro s hs
      apply ih
      · apply sliceCode_mono C (Finset.subset_insert i A)
        · intro x hx
          rw [mem_Sl] at hx ⊢
          intro j hj
          have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
          have hji : j ≠ i := fun e => hj (e ▸ Finset.mem_insert_self i A)
          rw [hx j hjA, Function.update_of_ne hji]
        · exact hc
      · refine ⟨Function.update ω i s, ?_, by simpa [hGood] using hs⟩
        rw [mem_Sl] at hω ⊢
        intro j hj
        by_cases hji : j = i
        · subst hji; simp
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
          apply hω j
          intro h
          rcases Finset.mem_insert.1 h with h' | h'
          · exact hji h'
          · exact hj h'
    -- sub-slices are disjoint and lie in the big slice
    have hcardsub : ∀ s, (Sl A (Function.update β i s)).card = ∏ j ∈ A, Fintype.card (S j) := by
      intro s; rw [Sl_card]
    have hdisj : ((Good.biUnion fun s => (Sl A (Function.update β i s)).filter fun ω => c ω ≠ 0)).card =
        ∑ s ∈ Good, ((Sl A (Function.update β i s)).filter fun ω => c ω ≠ 0).card := by
      rw [Finset.card_biUnion]
      intro s _ s' _ hss
      rw [Function.onFun, Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, mem_Sl] at hx hx'
      apply hss
      have h1 := hx.1 i hiA
      have h2 := hx'.1 i hiA
      simp at h1 h2
      rw [← h1, ← h2]
    have hincl : (Good.biUnion fun s => (Sl A (Function.update β i s)).filter fun ω => c ω ≠ 0) ⊆
        (Sl (insert i A) β).filter fun ω => c ω ≠ 0 := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_filter, mem_Sl] at hx ⊢
      obtain ⟨s, -, hx1, hx2⟩ := hx
      refine ⟨fun j hj => ?_, hx2⟩
      have hjA : j ∉ A := fun h => hj (Finset.mem_insert_of_mem h)
      have hji : j ≠ i := fun e => hj (e ▸ Finset.mem_insert_self i A)
      rw [hx1 j hjA, Function.update_of_ne hji]
    have hfin := Finset.card_le_card hincl
    rw [hdisj] at hfin
    have hP : 0 ≤ Δ ^ A.card * (∏ j ∈ A, (Fintype.card (S j) : ℝ)) := by positivity
    calc Δ ^ (insert i A).card * ((Sl (insert i A) β).card : ℝ)
        = (Δ * Fintype.card (S i)) * (Δ ^ A.card * ∏ j ∈ A, (Fintype.card (S j) : ℝ)) := by
          rw [Finset.card_insert_of_notMem hiA, Sl_card, Finset.prod_insert hiA]; push_cast; ring
      _ ≤ Good.card * (Δ ^ A.card * ∏ j ∈ A, (Fintype.card (S j) : ℝ)) :=
          mul_le_mul_of_nonneg_right hGc hP
      _ = ∑ _s ∈ Good, Δ ^ A.card * ∏ j ∈ A, (Fintype.card (S j) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ Good, (((Sl A (Function.update β i s)).filter fun ω => c ω ≠ 0).card : ℝ) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have := hsub s hs
          rw [hcardsub s] at this
          exact_mod_cast this
      _ ≤ _ := by exact_mod_cast hfin

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

def proj (B : Finset ι) (β ω : ∀ i, S i) : ∀ i, S i := fun i => if i ∈ B then ω i else β i

def comb3 (B1 B2 : Finset ι) (t1 t2 t3 : ∀ i, S i) : ∀ i, S i :=
  fun i => if i ∈ B1 then t1 i else if i ∈ B2 then t2 i else t3 i

def comb2 (B1 : Finset ι) (t1 t2 : ∀ i, S i) : ∀ i, S i := fun i => if i ∈ B1 then t1 i else t2 i

lemma proj_mem (B : Finset ι) (β ω : ∀ i, S i) : proj B β ω ∈ Sl B β := by
  rw [mem_Sl]; intro i hi; simp [proj, hi]

lemma proj_update_mem {B : Finset ι} {β ω : ∀ i, S i} {i : ι} (hi : i ∈ B) (s : S i) :
    proj B β (Function.update ω i s) = Function.update (proj B β ω) i s := by
  funext j; by_cases hj : j = i
  · subst hj; simp [proj, hi]
  · simp [proj, Function.update_of_ne hj]

lemma proj_update_not {B : Finset ι} {β ω : ∀ i, S i} {i : ι} (hi : i ∉ B) (s : S i) :
    proj B β (Function.update ω i s) = proj B β ω := by
  funext j; by_cases hj : j = i
  · subst hj; simp [proj, hi]
  · simp [proj, Function.update_of_ne hj]

lemma proj_of_mem {B : Finset ι} {β t : ∀ i, S i} (ht : t ∈ Sl B β) : proj B β t = t := by
  funext j; rw [mem_Sl] at ht
  by_cases hj : j ∈ B
  · simp [proj, hj]
  · simp [proj, hj, ht j hj]

/-- the points of the slice `Sl B β` -/
abbrev T (B : Finset ι) (β : ∀ i, S i) := ↥(Sl B β)

/-- restriction to a slice as a linear map -/
def restrL (B : Finset ι) (β : ∀ i, S i) : ((∀ i, S i) → F) →ₗ[F] (T B β → F) where
  toFun c t := c t.1
  map_add' c d := by funext t; simp
  map_smul' a c := by funext t; simp

/-- restriction of slice codewords -/
def resCode (B : Finset ι) (β : ∀ i, S i) : Submodule F (T B β → F) :=
  (sliceCode C B β).map (restrL B β)

lemma mem_resCode {B : Finset ι} {β : ∀ i, S i} {f : T B β → F} :
    f ∈ resCode C B β ↔ ∃ c ∈ sliceCode C B β, ∀ t, f t = c t.1 := by
  simp only [resCode, Submodule.mem_map, restrL, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, fun t => rfl⟩
  · rintro ⟨c, hc, h⟩; exact ⟨c, hc, funext fun t => (h t).symm⟩

lemma resCode_dist (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hC : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ wt c) (B : Finset ι) (β : ∀ i, S i) :
    HasDist (resCode C B β) (Δ ^ B.card) := by
  intro f hf hf0
  obtain ⟨c, hc, hfc⟩ := (mem_resCode C).1 hf
  obtain ⟨t, ht⟩ : ∃ t, f t ≠ 0 := by by_contra h; push Not at h; exact hf0 (funext h)
  have := slice_dist C Δ hΔ hC B β c hc ⟨t.1, t.2, by rw [← hfc]; exact ht⟩
  have hcardT : Fintype.card (T B β) = (Sl B β).card := by simp
  have hwt : wt f = ((Sl B β).filter fun ω => c ω ≠ 0).card := by
    unfold wt
    apply Finset.card_bij (fun t _ => t.1)
    · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact Finset.mem_filter.2 ⟨t.2, by rw [← hfc]; exact ht⟩
    · intro t _ t' _ h; exact Subtype.ext h
    · intro ω hω
      simp only [Finset.mem_filter] at hω
      exact ⟨⟨ω, hω.1⟩, by simp [hfc, hω.2], rfl⟩
  rw [hcardT, hwt]; exact this

section three
variable {A B1 B2 B3 : Finset ι} (hA : A = B1 ∪ B2 ∪ B3) (h12 : Disjoint B1 B2)
  (h13 : Disjoint B1 B3) (h23 : Disjoint B2 B3)

include hA h12 h13 h23 in
lemma comb3_mem {β t1 t2 t3 : ∀ i, S i} (ht1 : t1 ∈ Sl B1 β) (ht2 : t2 ∈ Sl B2 β)
    (ht3 : t3 ∈ Sl B3 β) : comb3 B1 B2 t1 t2 t3 ∈ Sl A β := by
  rw [mem_Sl] at *
  intro i hi
  rw [hA] at hi
  simp only [Finset.mem_union, not_or] at hi
  simp only [comb3, hi.1.1, hi.1.2, if_false]
  exact ht3 i hi.2

include h12 h13 h23 in
lemma proj_comb3_1 {β t1 t2 t3 : ∀ i, S i} (ht1 : t1 ∈ Sl B1 β) (ht2 : t2 ∈ Sl B2 β)
    (ht3 : t3 ∈ Sl B3 β) : proj B1 β (comb3 B1 B2 t1 t2 t3) = t1 := by
  funext i; rw [mem_Sl] at ht1
  by_cases h1 : i ∈ B1
  · simp [proj, comb3, h1]
  · simp [proj, h1, ht1 i h1]

include h12 h13 h23 in
lemma proj_comb3_2 {β t1 t2 t3 : ∀ i, S i} (ht1 : t1 ∈ Sl B1 β) (ht2 : t2 ∈ Sl B2 β)
    (ht3 : t3 ∈ Sl B3 β) : proj B2 β (comb3 B1 B2 t1 t2 t3) = t2 := by
  funext i; rw [mem_Sl] at ht2
  by_cases h2 : i ∈ B2
  · have h1 : i ∉ B1 := Finset.disjoint_right.1 h12 h2
    simp [proj, comb3, h1, h2]
  · simp [proj, h2, ht2 i h2]

include h12 h13 h23 in
lemma proj_comb3_3 {β t1 t2 t3 : ∀ i, S i} (ht1 : t1 ∈ Sl B1 β) (ht2 : t2 ∈ Sl B2 β)
    (ht3 : t3 ∈ Sl B3 β) : proj B3 β (comb3 B1 B2 t1 t2 t3) = t3 := by
  funext i; rw [mem_Sl] at ht3
  by_cases h3 : i ∈ B3
  · have h1 : i ∉ B1 := Finset.disjoint_right.1 h13 h3
    have h2 : i ∉ B2 := Finset.disjoint_right.1 h23 h3
    simp [proj, comb3, h1, h2, h3]
  · simp [proj, h3, ht3 i h3]

include hA h12 h13 h23 in
lemma comb3_proj {β ω : ∀ i, S i} (hω : ω ∈ Sl A β) :
    comb3 B1 B2 (proj B1 β ω) (proj B2 β ω) (proj B3 β ω) = ω := by
  funext i; rw [mem_Sl] at hω
  by_cases h1 : i ∈ B1
  · simp [comb3, proj, h1]
  by_cases h2 : i ∈ B2
  · simp [comb3, proj, h1, h2]
  by_cases h3 : i ∈ B3
  · simp [comb3, proj, h1, h2, h3]
  · have : i ∉ A := by rw [hA]; simp [h1, h2, h3]
    simp [comb3, proj, h1, h2, h3, hω i this]

lemma comb3_update1 {B1 B2 : Finset ι} {t1 t2 t3 : ∀ i, S i} {i : ι} (hi : i ∈ B1) (s : S i) :
    comb3 B1 B2 (Function.update t1 i s) t2 t3 = Function.update (comb3 B1 B2 t1 t2 t3) i s := by
  funext j; by_cases hj : j = i
  · subst hj; simp [comb3, hi]
  · simp [comb3, Function.update_of_ne hj]

include h12 in
lemma comb3_update2 {t1 t2 t3 : ∀ i, S i} {i : ι} (hi : i ∈ B2) (s : S i) :
    comb3 B1 B2 t1 (Function.update t2 i s) t3 = Function.update (comb3 B1 B2 t1 t2 t3) i s := by
  have h1 : i ∉ B1 := Finset.disjoint_right.1 h12 hi
  funext j; by_cases hj : j = i
  · subst hj; simp [comb3, hi, h1]
  · simp [comb3, Function.update_of_ne hj]

include h13 h23 in
lemma comb3_update3 {t1 t2 t3 : ∀ i, S i} {i : ι} (hi : i ∈ B3) (s : S i) :
    comb3 B1 B2 t1 t2 (Function.update t3 i s) = Function.update (comb3 B1 B2 t1 t2 t3) i s := by
  have h1 : i ∉ B1 := Finset.disjoint_right.1 h13 hi
  have h2 : i ∉ B2 := Finset.disjoint_right.1 h23 hi
  funext j; by_cases hj : j = i
  · subst hj; simp [comb3, h1, h2]
  · simp [comb3, Function.update_of_ne hj]

end three

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

section three
variable {A B1 B2 B3 : Finset ι} (hA : A = B1 ∪ B2 ∪ B3) (h12 : Disjoint B1 B2)
  (h13 : Disjoint B1 B3) (h23 : Disjoint B2 B3)

/-- the block map -/
def Φ3 (B1 B2 : Finset ι) {β : ∀ i, S i} {B3 : Finset ι}
    (t : T B1 β × T B2 β × T B3 β) : ∀ i, S i := comb3 B1 B2 t.1.1 t.2.1.1 t.2.2.1

include hA h12 h13 h23 in
theorem lift3 (β : ∀ i, S i) (u : T B1 β × T B2 β × T B3 β → F)
    (hu : u ∈ tens3 (resCode C B1 β) (resCode C B2 β) (resCode C B3 β)) :
    ∃ c ∈ sliceCode C A β, ∀ t, c (Φ3 B1 B2 t) = u t := by
  let pr : ∀ ω : ∀ i, S i, T B1 β × T B2 β × T B3 β := fun ω =>
    (⟨proj B1 β ω, proj_mem B1 β ω⟩, ⟨proj B2 β ω, proj_mem B2 β ω⟩, ⟨proj B3 β ω, proj_mem B3 β ω⟩)
  let c : (∀ i, S i) → F := fun ω => if ω ∈ Sl A β then u (pr ω) else 0
  refine ⟨c, ?_, ?_⟩
  · intro ω hω i hi
    unfold LOK
    have hupd : ∀ s, Function.update ω i s ∈ Sl A β := fun s => update_mem_Sl hω hi s
    have hiA := hi
    rw [hA] at hiA
    simp only [Finset.mem_union] at hiA
    rcases hiA with (h1 | h2) | h3
    · have hn2 : i ∉ B2 := Finset.disjoint_left.1 h12 h1
      have hn3 : i ∉ B3 := Finset.disjoint_left.1 h13 h1
      obtain ⟨c1, hc1, hc1u⟩ := (mem_resCode C).1 (hu.1 (pr ω).2.1 (pr ω).2.2)
      have key : (fun s => c (Function.update ω i s)) = fun s => c1 (Function.update (proj B1 β ω) i s) := by
        funext s
        simp only [c, if_pos (hupd s)]
        rw [show pr (Function.update ω i s) = (⟨Function.update (proj B1 β ω) i s,
            by rw [← proj_update_mem h1]; exact proj_mem B1 β _⟩, (pr ω).2.1, (pr ω).2.2) from by
          simp only [pr]; congr 1
          · exact Subtype.ext (proj_update_mem h1 s)
          · congr 1
            · exact Subtype.ext (proj_update_not hn2 s)
            · exact Subtype.ext (proj_update_not hn3 s)]
        rw [hc1u]
      rw [key]
      exact hc1 _ (proj_mem B1 β ω) i h1
    · have hn1 : i ∉ B1 := Finset.disjoint_right.1 h12 h2
      have hn3 : i ∉ B3 := Finset.disjoint_left.1 h23 h2
      obtain ⟨c2, hc2, hc2u⟩ := (mem_resCode C).1 (hu.2.1 (pr ω).1 (pr ω).2.2)
      have key : (fun s => c (Function.update ω i s)) = fun s => c2 (Function.update (proj B2 β ω) i s) := by
        funext s
        simp only [c, if_pos (hupd s)]
        rw [show pr (Function.update ω i s) = ((pr ω).1, ⟨Function.update (proj B2 β ω) i s,
            by rw [← proj_update_mem h2]; exact proj_mem B2 β _⟩, (pr ω).2.2) from by
          simp only [pr]; congr 1
          · exact Subtype.ext (proj_update_not hn1 s)
          · congr 1
            · exact Subtype.ext (proj_update_mem h2 s)
            · exact Subtype.ext (proj_update_not hn3 s)]
        rw [hc2u]
      rw [key]
      exact hc2 _ (proj_mem B2 β ω) i h2
    · have hn1 : i ∉ B1 := Finset.disjoint_right.1 h13 h3
      have hn2 : i ∉ B2 := Finset.disjoint_right.1 h23 h3
      obtain ⟨c3, hc3, hc3u⟩ := (mem_resCode C).1 (hu.2.2 (pr ω).1 (pr ω).2.1)
      have key : (fun s => c (Function.update ω i s)) = fun s => c3 (Function.update (proj B3 β ω) i s) := by
        funext s
        simp only [c, if_pos (hupd s)]
        rw [show pr (Function.update ω i s) = ((pr ω).1, (pr ω).2.1, ⟨Function.update (proj B3 β ω) i s,
            by rw [← proj_update_mem h3]; exact proj_mem B3 β _⟩) from by
          simp only [pr]; congr 1
          · exact Subtype.ext (proj_update_not hn1 s)
          · congr 1
            · exact Subtype.ext (proj_update_not hn2 s)
            · exact Subtype.ext (proj_update_mem h3 s)]
        rw [hc3u]
      rw [key]
      exact hc3 _ (proj_mem B3 β ω) i h3
  · intro t
    have hmem := comb3_mem hA h12 h13 h23 t.1.2 t.2.1.2 t.2.2.2
    simp only [c, Φ3, if_pos hmem]
    congr 1
    simp only [pr]
    obtain ⟨t1, t2, t3⟩ := t
    congr 1
    · exact Subtype.ext (proj_comb3_1 h12 h13 h23 t1.2 t2.2 t3.2)
    · congr 1
      · exact Subtype.ext (proj_comb3_2 h12 h13 h23 t1.2 t2.2 t3.2)
      · exact Subtype.ext (proj_comb3_3 h12 h13 h23 t1.2 t2.2 t3.2)

end three

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

section three
variable {B1 B2 B3 : Finset ι} (h12 : Disjoint B1 B2) (h13 : Disjoint B1 B3) (h23 : Disjoint B2 B3)

include h12 h13 h23 in
lemma pl1_mem {β t1 a b : ∀ i, S i} (ht1 : t1 ∈ Sl B1 β) (ha : a ∈ Sl B2 β) (hb : b ∈ Sl B3 β) :
    comb3 B1 B2 t1 a b ∈ Sl (B2 ∪ B3) t1 := by
  rw [mem_Sl] at *
  intro j hj
  simp only [Finset.mem_union, not_or] at hj
  by_cases h1 : j ∈ B1
  · simp [comb3, h1]
  · simp only [comb3, h1, hj.1, if_false]; rw [hb j hj.2, ht1 j h1]

include h12 h13 h23 in
lemma pl2_mem {β a t2 b : ∀ i, S i} (ha : a ∈ Sl B1 β) (ht2 : t2 ∈ Sl B2 β) (hb : b ∈ Sl B3 β) :
    comb3 B1 B2 a t2 b ∈ Sl (B1 ∪ B3) t2 := by
  rw [mem_Sl] at *
  intro j hj
  simp only [Finset.mem_union, not_or] at hj
  by_cases h2 : j ∈ B2
  · simp [comb3, hj.1, h2]
  · simp only [comb3, hj.1, h2, if_false]; rw [hb j hj.2, ht2 j h2]

lemma pl3_mem {a b t3 : ∀ i, S i} :
    comb3 B1 B2 a b t3 ∈ Sl (B1 ∪ B2) t3 := by
  rw [mem_Sl]
  intro j hj
  simp only [Finset.mem_union, not_or] at hj
  simp [comb3, hj.1, hj.2]

include h12 h13 h23 in
lemma plane1 {β : ∀ i, S i} (t1 : T B1 β) (c : (∀ i, S i) → F) (hc : c ∈ sliceCode C (B2 ∪ B3) t1.1) :
    (fun q : T B2 β × T B3 β => c (comb3 B1 B2 t1.1 q.1.1 q.2.1)) ∈
      tens2 (resCode C B2 β) (resCode C B3 β) := by
  refine ⟨fun b => ?_, fun a => ?_⟩
  · refine (mem_resCode C).2 ⟨fun ω => c (comb3 B1 B2 t1.1 ω b.1), ?_, fun a => rfl⟩
    intro ω hω i hi
    unfold LOK
    simp only [comb3_update2 h12 hi]
    exact hc _ (pl1_mem h12 h13 h23 t1.2 hω b.2) i (Finset.mem_union_left _ hi)
  · refine (mem_resCode C).2 ⟨fun ω => c (comb3 B1 B2 t1.1 a.1 ω), ?_, fun b => rfl⟩
    intro ω hω i hi
    unfold LOK
    simp only [comb3_update3 h13 h23 hi]
    exact hc _ (pl1_mem h12 h13 h23 t1.2 a.2 hω) i (Finset.mem_union_right _ hi)

include h12 h13 h23 in
lemma plane2 {β : ∀ i, S i} (t2 : T B2 β) (c : (∀ i, S i) → F) (hc : c ∈ sliceCode C (B1 ∪ B3) t2.1) :
    (fun q : T B1 β × T B3 β => c (comb3 B1 B2 q.1.1 t2.1 q.2.1)) ∈
      tens2 (resCode C B1 β) (resCode C B3 β) := by
  refine ⟨fun b => ?_, fun a => ?_⟩
  · refine (mem_resCode C).2 ⟨fun ω => c (comb3 B1 B2 ω t2.1 b.1), ?_, fun a => rfl⟩
    intro ω hω i hi
    unfold LOK
    simp only [comb3_update1 hi]
    exact hc _ (pl2_mem h12 h13 h23 hω t2.2 b.2) i (Finset.mem_union_left _ hi)
  · refine (mem_resCode C).2 ⟨fun ω => c (comb3 B1 B2 a.1 t2.1 ω), ?_, fun b => rfl⟩
    intro ω hω i hi
    unfold LOK
    simp only [comb3_update3 h13 h23 hi]
    exact hc _ (pl2_mem h12 h13 h23 a.2 t2.2 hω) i (Finset.mem_union_right _ hi)

include h12 h13 h23 in
lemma plane3 {β : ∀ i, S i} (t3 : T B3 β) (c : (∀ i, S i) → F) (hc : c ∈ sliceCode C (B1 ∪ B2) t3.1) :
    (fun q : T B1 β × T B2 β => c (comb3 B1 B2 q.1.1 q.2.1 t3.1)) ∈
      tens2 (resCode C B1 β) (resCode C B2 β) := by
  refine ⟨fun b => ?_, fun a => ?_⟩
  · refine (mem_resCode C).2 ⟨fun ω => c (comb3 B1 B2 ω b.1 t3.1), ?_, fun a => rfl⟩
    intro ω hω i hi
    unfold LOK
    simp only [comb3_update1 hi]
    exact hc _ pl3_mem i (Finset.mem_union_left _ hi)
  · refine (mem_resCode C).2 ⟨fun ω => c (comb3 B1 B2 a.1 ω t3.1), ?_, fun b => rfl⟩
    intro ω hω i hi
    unfold LOK
    simp only [comb3_update2 h12 hi]
    exact hc _ pl3_mem i (Finset.mem_union_right _ hi)

end three

/-- slices of a slice partition it -/
lemma Sl_fiber {A B : Finset ι} (hBA : B ⊆ A) {β t : ∀ i, S i} (ht : t ∈ Sl B β) :
    (Sl A β).filter (fun ω => proj B β ω = t) = Sl (A \ B) t := by
  ext ω
  simp only [Finset.mem_filter, mem_Sl, Finset.mem_sdiff, not_and, not_not]
  rw [mem_Sl] at ht
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjB : j ∈ B
    · rw [← h2]; simp [proj, hjB]
    · have hjA : j ∉ A := fun h => hjB (hj h)
      rw [h1 j hjA, ht j hjB]
  · intro h
    refine ⟨fun j hjA => ?_, ?_⟩
    · have hjB : j ∉ B := fun h' => hjA (hBA h')
      rw [h j (fun h' => absurd h' hjA), ht j hjB]
    · funext j
      by_cases hjB : j ∈ B
      · simp only [proj, hjB, if_true]; exact h j (fun _ => hjB)
      · simp only [proj, hjB, if_false]; exact (ht j hjB).symm

lemma bad_avg {A B : Finset ι} (hBA : B ⊆ A) (β : ∀ i, S i) (w : (∀ i, S i) → F) (i : ι) :
    ∑ t : T B β, bad C (A \ B) t.1 w i = bad C A β w i := by
  unfold bad
  rw [Finset.card_eq_sum_card_fiberwise (f := proj B β) (t := Sl B β)
    (fun ω _ => proj_mem B β ω)]
  rw [← Finset.sum_coe_sort (Sl B β)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.filter_filter]
  have := Sl_fiber hBA t.2
  rw [← this, Finset.filter_filter]
  congr 1; ext ω; simp [and_comm]

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

section three
variable {A B1 B2 B3 : Finset ι} (hA : A = B1 ∪ B2 ∪ B3) (h12 : Disjoint B1 B2)
  (h13 : Disjoint B1 B3) (h23 : Disjoint B2 B3)

include hA h12 h13 h23 in
lemma sdist_le_tens3 (β : ∀ i, S i) (w : (∀ i, S i) → F) :
    sdist C A β w ≤ distTo (fun t : T B1 β × T B2 β × T B3 β => w (Φ3 B1 B2 t))
      (tens3 (resCode C B1 β) (resCode C B2 β) (resCode C B3 β)) := by
  obtain ⟨u, hu, hud⟩ := exists_nearest (fun t : T B1 β × T B2 β × T B3 β => w (Φ3 B1 B2 t))
    (tens3 (resCode C B1 β) (resCode C B2 β) (resCode C B3 β))
  obtain ⟨c, hc, hcu⟩ := lift3 C hA h12 h13 h23 β u hu
  refine (sdist_le C A β w c hc).trans (le_of_eq ?_)
  rw [← hud]
  unfold supportCard
  symm
  apply Finset.card_bij (fun t _ => Φ3 B1 B2 t)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at ht
    refine Finset.mem_filter.2 ⟨comb3_mem hA h12 h13 h23 t.1.2 t.2.1.2 t.2.2.2, ?_⟩
    rw [hcu]; exact ht
  · intro t _ t' _ h
    obtain ⟨t1, t2, t3⟩ := t
    obtain ⟨t1', t2', t3'⟩ := t'
    simp only [Φ3] at h
    have e1 := proj_comb3_1 h12 h13 h23 t1.2 t2.2 t3.2
    have e2 := proj_comb3_2 h12 h13 h23 t1.2 t2.2 t3.2
    have e3 := proj_comb3_3 h12 h13 h23 t1.2 t2.2 t3.2
    rw [h, proj_comb3_1 h12 h13 h23 t1'.2 t2'.2 t3'.2] at e1
    rw [h, proj_comb3_2 h12 h13 h23 t1'.2 t2'.2 t3'.2] at e2
    rw [h, proj_comb3_3 h12 h13 h23 t1'.2 t2'.2 t3'.2] at e3
    simp only [Prod.mk.injEq]
    exact ⟨Subtype.ext e1.symm, Subtype.ext e2.symm, Subtype.ext e3.symm⟩
  · intro ω hω
    simp only [Finset.mem_filter] at hω
    refine ⟨(⟨proj B1 β ω, proj_mem B1 β ω⟩, ⟨proj B2 β ω, proj_mem B2 β ω⟩,
      ⟨proj B3 β ω, proj_mem B3 β ω⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero]
      rw [← hcu]
      simp only [Φ3]
      rw [comb3_proj hA h12 h13 h23 hω.1]
      exact hω.2
    · simp only [Φ3]; exact comb3_proj hA h12 h13 h23 hω.1

include h12 h13 h23 in
lemma plane1_le {β : ∀ i, S i} (t1 : T B1 β) (w : (∀ i, S i) → F) :
    distTo (fun q : T B2 β × T B3 β => w (comb3 B1 B2 t1.1 q.1.1 q.2.1))
      (tens2 (resCode C B2 β) (resCode C B3 β)) ≤ sdist C (B2 ∪ B3) t1.1 w := by
  obtain ⟨c, hc, hcd⟩ := exists_sdist C (B2 ∪ B3) t1.1 w
  refine (distTo_le' _ _ _ (plane1 C h12 h13 h23 t1 c hc)).trans ?_
  rw [← hcd]
  unfold supportCard
  apply Finset.card_le_card_of_injOn (fun q => comb3 B1 B2 t1.1 q.1.1 q.2.1)
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Pi.sub_apply,
      sub_ne_zero] at hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨pl1_mem h12 h13 h23 t1.2 q.1.2 q.2.2, hq⟩
  · intro q _ q' _ h
    have e2 := proj_comb3_2 h12 h13 h23 t1.2 q.1.2 q.2.2
    have e3 := proj_comb3_3 h12 h13 h23 t1.2 q.1.2 q.2.2
    simp only at h
    rw [h, proj_comb3_2 h12 h13 h23 t1.2 q'.1.2 q'.2.2] at e2
    rw [h, proj_comb3_3 h12 h13 h23 t1.2 q'.1.2 q'.2.2] at e3
    exact Prod.ext (Subtype.ext e2.symm) (Subtype.ext e3.symm)

include h12 h13 h23 in
lemma plane2_le {β : ∀ i, S i} (t2 : T B2 β) (w : (∀ i, S i) → F) :
    distTo (fun q : T B1 β × T B3 β => w (comb3 B1 B2 q.1.1 t2.1 q.2.1))
      (tens2 (resCode C B1 β) (resCode C B3 β)) ≤ sdist C (B1 ∪ B3) t2.1 w := by
  obtain ⟨c, hc, hcd⟩ := exists_sdist C (B1 ∪ B3) t2.1 w
  refine (distTo_le' _ _ _ (plane2 C h12 h13 h23 t2 c hc)).trans ?_
  rw [← hcd]
  unfold supportCard
  apply Finset.card_le_card_of_injOn (fun q => comb3 B1 B2 q.1.1 t2.1 q.2.1)
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Pi.sub_apply,
      sub_ne_zero] at hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨pl2_mem h12 h13 h23 q.1.2 t2.2 q.2.2, hq⟩
  · intro q _ q' _ h
    have e1 := proj_comb3_1 h12 h13 h23 q.1.2 t2.2 q.2.2
    have e3 := proj_comb3_3 h12 h13 h23 q.1.2 t2.2 q.2.2
    simp only at h
    rw [h, proj_comb3_1 h12 h13 h23 q'.1.2 t2.2 q'.2.2] at e1
    rw [h, proj_comb3_3 h12 h13 h23 q'.1.2 t2.2 q'.2.2] at e3
    exact Prod.ext (Subtype.ext e1.symm) (Subtype.ext e3.symm)

include h12 h13 h23 in
lemma plane3_le {β : ∀ i, S i} (t3 : T B3 β) (w : (∀ i, S i) → F) :
    distTo (fun q : T B1 β × T B2 β => w (comb3 B1 B2 q.1.1 q.2.1 t3.1))
      (tens2 (resCode C B1 β) (resCode C B2 β)) ≤ sdist C (B1 ∪ B2) t3.1 w := by
  obtain ⟨c, hc, hcd⟩ := exists_sdist C (B1 ∪ B2) t3.1 w
  refine (distTo_le' _ _ _ (plane3 C h12 h13 h23 t3 c hc)).trans ?_
  rw [← hcd]
  unfold supportCard
  apply Finset.card_le_card_of_injOn (fun q => comb3 B1 B2 q.1.1 q.2.1 t3.1)
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Pi.sub_apply,
      sub_ne_zero] at hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨pl3_mem, hq⟩
  · intro q _ q' _ h
    have e1 := proj_comb3_1 h12 h13 h23 q.1.2 q.2.2 t3.2
    have e2 := proj_comb3_2 h12 h13 h23 q.1.2 q.2.2 t3.2
    simp only at h
    rw [h, proj_comb3_1 h12 h13 h23 q'.1.2 q'.2.2 t3.2] at e1
    rw [h, proj_comb3_2 h12 h13 h23 q'.1.2 q'.2.2 t3.2] at e2
    exact Prod.ext (Subtype.ext e1.symm) (Subtype.ext e2.symm)

include hA h12 h13 h23 in
/-- Viderman's theorem on a slice -/
theorem viderman_slice (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (β : ∀ i, S i)
    (hd1 : HasDist (resCode C B1 β) δ) (hd2 : HasDist (resCode C B2 β) δ)
    (hd3 : HasDist (resCode C B3 β) δ) (w : (∀ i, S i) → F) :
    δ ^ 3 / 6 * (sdist C A β w : ℝ) ≤
      ((∑ t : T B1 β, sdist C (B2 ∪ B3) t.1 w + ∑ t : T B2 β, sdist C (B1 ∪ B3) t.1 w +
        ∑ t : T B3 β, sdist C (B1 ∪ B2) t.1 w : ℕ) : ℝ) := by
  have hv := viderman3 (resCode C B1 β) (resCode C B2 β) (resCode C B3 β) δ hδ0 hδ1 hd1 hd2 hd3
    (fun t => w (Φ3 B1 B2 t))
  have hs := sdist_le_tens3 C hA h12 h13 h23 β w
  have h3 : (0 : ℝ) ≤ δ ^ 3 / 6 := by positivity
  calc δ ^ 3 / 6 * (sdist C A β w : ℝ) ≤ δ ^ 3 / 6 * (distTo (fun t : T B1 β × T B2 β × T B3 β =>
        w (Φ3 B1 B2 t)) (tens3 (resCode C B1 β) (resCode C B2 β) (resCode C B3 β)) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hs) h3
    _ ≤ _ := hv
    _ ≤ _ := by
        have e1 : ∀ a : T B1 β, distTo (fun q : T B2 β × T B3 β => (fun t => w (Φ3 B1 B2 t)) (a, q.1, q.2))
            (tens2 (resCode C B2 β) (resCode C B3 β)) ≤ sdist C (B2 ∪ B3) a.1 w :=
          fun a => plane1_le C h12 h13 h23 a w
        have e2 : ∀ b : T B2 β, distTo (fun q : T B1 β × T B3 β => (fun t => w (Φ3 B1 B2 t)) (q.1, b, q.2))
            (tens2 (resCode C B1 β) (resCode C B3 β)) ≤ sdist C (B1 ∪ B3) b.1 w :=
          fun b => plane2_le C h12 h13 h23 b w
        have e3 : ∀ c : T B3 β, distTo (fun q : T B1 β × T B2 β => (fun t => w (Φ3 B1 B2 t)) (q.1, q.2, c))
            (tens2 (resCode C B1 β) (resCode C B2 β)) ≤ sdist C (B1 ∪ B2) c.1 w :=
          fun c => plane3_le C h12 h13 h23 c w
        exact_mod_cast Nat.add_le_add (Nat.add_le_add (Finset.sum_le_sum fun a _ => e1 a)
          (Finset.sum_le_sum fun b _ => e2 b)) (Finset.sum_le_sum fun c _ => e3 c)

end three

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

/-- the soundness constant -/
noncomputable def fC (Δ : ℝ) (n : ℕ) : ℝ := Δ ^ (8 * n) / (10 ^ 6 * (n : ℝ) ^ 16)

lemma fC_nonneg {Δ : ℝ} (hΔ : 0 ≤ Δ) (n : ℕ) : 0 ≤ fC Δ n := by unfold fC; positivity

lemma fC_anti {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    fC Δ b ≤ fC Δ a := by
  unfold fC
  have h1 : Δ ^ (8 * b) ≤ Δ ^ (8 * a) := pow_le_pow_of_le_one hΔ0.le hΔ1 (by omega)
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h2 : (a : ℝ) ^ 16 ≤ (b : ℝ) ^ 16 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    gcongr
  have hpa : (0 : ℝ) < 10 ^ 6 * (a : ℝ) ^ 16 := by positivity
  have hb : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  rw [div_le_div_iff₀ (by positivity) hpa]
  have : (0 : ℝ) ≤ Δ ^ (8 * b) := by positivity
  calc Δ ^ (8 * b) * (10 ^ 6 * (a : ℝ) ^ 16) ≤ Δ ^ (8 * a) * (10 ^ 6 * (a : ℝ) ^ 16) :=
        mul_le_mul_of_nonneg_right h1 hpa.le
    _ ≤ Δ ^ (8 * a) * (10 ^ 6 * (b : ℝ) ^ 16) := by gcongr

lemma nat_key (n : ℕ) (hn : 3 ≤ n) :
    12 * n * (n - n / 3) ^ 16 ≤ (n - (n + 2) / 3) * n ^ 16 := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> norm_num
  · have h5 : 5 * (n - n / 3) ≤ 4 * n := by omega
    have hp : (5 * (n - n / 3)) ^ 16 ≤ (4 * n) ^ 16 := Nat.pow_le_pow_left h5 16
    rw [mul_pow, mul_pow] at hp
    have hm : 12 * 4 ^ 16 * n ≤ 5 ^ 16 * (n - (n + 2) / 3) := by omega
    have key : 5 ^ 16 * (12 * n * (n - n / 3) ^ 16) ≤ 5 ^ 16 * ((n - (n + 2) / 3) * n ^ 16) := by
      calc 5 ^ 16 * (12 * n * (n - n / 3) ^ 16) = 12 * n * (5 ^ 16 * (n - n / 3) ^ 16) := by ring
        _ ≤ 12 * n * (4 ^ 16 * n ^ 16) := Nat.mul_le_mul_left _ hp
        _ = (12 * 4 ^ 16 * n) * n ^ 16 := by ring
        _ ≤ (5 ^ 16 * (n - (n + 2) / 3)) * n ^ 16 := Nat.mul_le_mul_right _ hm
        _ = 5 ^ 16 * ((n - (n + 2) / 3) * n ^ 16) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

lemma real_key (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) * fC Δ n ≤
      ((n - (n + 2) / 3 : ℕ) : ℝ) * fC Δ (n - n / 3) * (Δ ^ ((n + 2) / 3)) ^ 3 / 12 := by
  unfold fC
  set m : ℝ := ((n - (n + 2) / 3 : ℕ) : ℝ)
  set n' : ℝ := ((n - n / 3 : ℕ) : ℝ)
  set N : ℝ := (n : ℝ)
  set X : ℝ := Δ ^ (8 * (n - n / 3)) * (Δ ^ ((n + 2) / 3)) ^ 3
  have hΔp : Δ ^ (8 * n) ≤ X := by
    simp only [X]
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_of_le_one hΔ0.le hΔ1 (by omega)
  have hnk' : (12 : ℝ) * N * n' ^ 16 ≤ m * N ^ 16 := by
    simp only [N, n', m]; exact_mod_cast nat_key n hn
  have hN0 : (0 : ℝ) < N := by simp only [N]; exact_mod_cast (by omega : 0 < n)
  have hn'0 : (0 : ℝ) < n' := by simp only [n']; exact_mod_cast (by omega : 0 < n - n / 3)
  have eL : N * (Δ ^ (8 * n) / (10 ^ 6 * N ^ 16)) = N * Δ ^ (8 * n) / (10 ^ 6 * N ^ 16) := by ring
  have eR : m * (Δ ^ (8 * (n - n / 3)) / (10 ^ 6 * n' ^ 16)) * (Δ ^ ((n + 2) / 3)) ^ 3 / 12 =
      m * X / (12 * 10 ^ 6 * n' ^ 16) := by simp only [X]; ring
  rw [eL, eR, div_le_div_iff₀ (by positivity) (by positivity)]
  have hD : (0 : ℝ) ≤ Δ ^ (8 * n) := by positivity
  have hX0 : 0 ≤ X := le_trans hD hΔp
  calc N * Δ ^ (8 * n) * (12 * 10 ^ 6 * n' ^ 16) = Δ ^ (8 * n) * 10 ^ 6 * (12 * N * n' ^ 16) := by ring
    _ ≤ X * 10 ^ 6 * (12 * N * n' ^ 16) := by gcongr
    _ ≤ X * 10 ^ 6 * (m * N ^ 16) := by gcongr
    _ = m * X * (10 ^ 6 * N ^ 16) := by ring

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

lemma Sl_empty_eq {β t : ∀ i, S i} (ht : t ∈ Sl ∅ β) : t = β := by
  funext k; exact (mem_Sl.1 ht) k (Finset.notMem_empty k)

lemma resCode_empty (β : ∀ i, S i) (f : T (∅ : Finset ι) β → F) : f ∈ resCode C ∅ β := by
  refine (mem_resCode C).2 ⟨fun _ => f ⟨β, self_mem_Sl ∅ β⟩, fun ω _ i hi => absurd hi (Finset.notMem_empty i), ?_⟩
  intro t
  have : t = ⟨β, self_mem_Sl ∅ β⟩ := Subtype.ext (Sl_empty_eq t.2)
  rw [this]

lemma upd_eq_of_Sl {i : ι} {β ω a : ∀ i, S i} (hω : ω ∈ Sl {i} β) (ha : a ∈ Sl {i} β) :
    ω = Function.update a i (ω i) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Function.update_of_ne hk, (mem_Sl.1 hω) k (by simpa using hk), (mem_Sl.1 ha) k (by simpa using hk)]

lemma col_bad {i j : ι} {β : ∀ i, S i} (w : (∀ i, S i) → F) (b : T {j} β)
    (hb : (fun a : T {i} β => w (comb3 {i} {j} a.1 b.1 β)) ∉ resCode C {i} β) (a : T {i} β) :
    ¬ LOK C i w (comb3 {i} {j} a.1 b.1 β) := by
  intro hL
  apply hb
  refine (mem_resCode C).2 ⟨fun ω => w (comb3 {i} {j} ω b.1 β), ?_, fun a' => rfl⟩
  intro ω hω i' hi'
  rw [Finset.mem_singleton] at hi'
  subst hi'
  unfold LOK
  simp only [comb3_update1 (Finset.mem_singleton_self i')]
  rw [upd_eq_of_Sl hω a.2, comb3_update1 (Finset.mem_singleton_self i')]
  have := (LOK_update C (c := w) (ω := comb3 {i'} {j} a.1 b.1 β) (ω i')).2 hL
  unfold LOK at this
  simpa [comb3_update1 (Finset.mem_singleton_self i')] using this

lemma row_bad {i j : ι} (hij : i ≠ j) {β : ∀ i, S i} (w : (∀ i, S i) → F) (a : T {i} β)
    (hb : (fun b : T {j} β => w (comb3 {i} {j} a.1 b.1 β)) ∉ resCode C {j} β) (b : T {j} β) :
    ¬ LOK C j w (comb3 {i} {j} a.1 b.1 β) := by
  have h12 : Disjoint ({i} : Finset ι) {j} := by simpa using hij
  intro hL
  apply hb
  refine (mem_resCode C).2 ⟨fun ω => w (comb3 {i} {j} a.1 ω β), ?_, fun b' => rfl⟩
  intro ω hω j' hj'
  rw [Finset.mem_singleton] at hj'
  subst hj'
  unfold LOK
  simp only [comb3_update2 h12 (Finset.mem_singleton_self j')]
  rw [upd_eq_of_Sl hω b.2, comb3_update2 h12 (Finset.mem_singleton_self j')]
  have := (LOK_update C (c := w) (ω := comb3 {i} {j'} a.1 b.1 β) (ω j')).2 hL
  unfold LOK at this
  simpa [comb3_update2 h12 (Finset.mem_singleton_self j')] using this

theorem base72 (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hC : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ wt c) (i j : ι) (hij : i ≠ j)
    (β : ∀ i, S i) (w : (∀ i, S i) → F) :
    Δ * (sdist C {i, j} β w : ℝ) ≤ bad C {i, j} β w i + bad C {i, j} β w j := by
  have hA : ({i, j} : Finset ι) = {i} ∪ {j} ∪ ∅ := by ext; simp
  have h12 : Disjoint ({i} : Finset ι) {j} := by simpa using hij
  have h13 : Disjoint ({i} : Finset ι) ∅ := Finset.disjoint_empty_right _
  have h23 : Disjoint ({j} : Finset ι) ∅ := Finset.disjoint_empty_right _
  have hs := sdist_le_tens3 C hA h12 h13 h23 β w
  set W2 : T {i} β × T {j} β → F := fun q => w (comb3 {i} {j} q.1.1 q.2.1 β) with hW2
  -- the three-block distance is at most the two-block distance
  have hd32 : distTo (fun t : T {i} β × T {j} β × T (∅ : Finset ι) β => w (Φ3 {i} {j} t))
      (tens3 (resCode C {i} β) (resCode C {j} β) (resCode C ∅ β)) ≤
      distTo W2 (tens2 (resCode C {i} β) (resCode C {j} β)) := by
    obtain ⟨u, hu, hud⟩ := exists_nearest W2 (tens2 (resCode C {i} β) (resCode C {j} β))
    have hu3 : (fun t : T {i} β × T {j} β × T (∅ : Finset ι) β => u (t.1, t.2.1)) ∈
        tens3 (resCode C {i} β) (resCode C {j} β) (resCode C ∅ β) :=
      ⟨fun b c => hu.1 b, fun a c => hu.2 a, fun a b => resCode_empty C β _⟩
    refine (distTo_le' _ _ _ hu3).trans (le_of_eq ?_)
    rw [← hud]
    unfold supportCard
    apply Finset.card_bij (fun t _ => (t.1, t.2.1))
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at ht ⊢
      simp only [Φ3] at ht
      rw [Sl_empty_eq t.2.2.2] at ht
      exact ht
    · intro t _ t' _ h
      simp only [Prod.mk.injEq] at h
      have : t.2.2 = t'.2.2 := Subtype.ext (by rw [Sl_empty_eq t.2.2.2, Sl_empty_eq t'.2.2.2])
      exact Prod.ext h.1 (Prod.ext h.2 this)
    · intro q hq
      refine ⟨(q.1, q.2, ⟨β, self_mem_Sl ∅ β⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at hq ⊢
      exact hq
  have hd1 : HasDist (resCode C {i} β) Δ := by
    have := resCode_dist C Δ hΔ0.le hC {i} β; simpa using this
  have hd2 : HasDist (resCode C {j} β) Δ := by
    have := resCode_dist C Δ hΔ0.le hC {j} β; simpa using this
  have hB3 := lineB3 (resCode C {i} β) (resCode C {j} β) Δ hΔ0 hΔ1 hd1 hd2 W2
  -- counting bad columns and rows
  set Bc := Finset.univ.filter fun b : T {j} β => (fun a => W2 (a, b)) ∉ resCode C {i} β
  set Br := Finset.univ.filter fun a : T {i} β => (fun b => W2 (a, b)) ∉ resCode C {j} β
  have hmemA : ∀ a : T {i} β, ∀ b : T {j} β, comb3 {i} {j} a.1 b.1 β ∈ Sl {i, j} β :=
    fun a b => comb3_mem hA h12 h13 h23 a.2 b.2 (self_mem_Sl ∅ β)
  have hinj : ∀ a a' : T {i} β, ∀ b b' : T {j} β,
      comb3 {i} {j} a.1 b.1 β = comb3 {i} {j} a'.1 b'.1 β → a = a' ∧ b = b' := by
    intro a a' b b' h
    have e1 := proj_comb3_1 h12 h13 h23 a.2 b.2 (self_mem_Sl ∅ β)
    have e2 := proj_comb3_2 h12 h13 h23 a.2 b.2 (self_mem_Sl ∅ β)
    rw [h, proj_comb3_1 h12 h13 h23 a'.2 b'.2 (self_mem_Sl ∅ β)] at e1
    rw [h, proj_comb3_2 h12 h13 h23 a'.2 b'.2 (self_mem_Sl ∅ β)] at e2
    exact ⟨Subtype.ext e1.symm, Subtype.ext e2.symm⟩
  have hcol : (Bc.card : ℝ) * Fintype.card (T {i} β) ≤ bad C {i, j} β w i := by
    have : ((Finset.univ : Finset (T {i} β)) ×ˢ Bc).card ≤ bad C {i, j} β w i := by
      unfold bad
      apply Finset.card_le_card_of_injOn (fun q : T {i} β × T {j} β => comb3 {i} {j} q.1.1 q.2.1 β)
      · intro q hq
        simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
          Finset.mem_coe, Bc, Finset.mem_filter] at hq
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨hmemA q.1 q.2, col_bad C w q.2 hq.2 q.1⟩
      · intro q _ q' _ h
        obtain ⟨e1, e2⟩ := hinj q.1 q'.1 q.2 q'.2 h
        exact Prod.ext e1 e2
    rw [Finset.card_product, Finset.card_univ] at this
    rw [mul_comm]; exact_mod_cast this
  have hrow : (Br.card : ℝ) * Fintype.card (T {j} β) ≤ bad C {i, j} β w j := by
    have : (Br ×ˢ (Finset.univ : Finset (T {j} β))).card ≤ bad C {i, j} β w j := by
      unfold bad
      apply Finset.card_le_card_of_injOn (fun q : T {i} β × T {j} β => comb3 {i} {j} q.1.1 q.2.1 β)
      · intro q hq
        simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, and_true,
          Finset.mem_coe, Br, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨hmemA q.1 q.2, row_bad C hij w q.1 hq q.2⟩
      · intro q _ q' _ h
        obtain ⟨e1, e2⟩ := hinj q.1 q'.1 q.2 q'.2 h
        exact Prod.ext e1 e2
    rw [Finset.card_product, Finset.card_univ] at this
    exact_mod_cast this
  calc Δ * (sdist C {i, j} β w : ℝ) ≤ Δ * (distTo W2 (tens2 (resCode C {i} β) (resCode C {j} β)) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hΔ0.le
        exact_mod_cast hs.trans hd32
    _ ≤ _ := hB3
    _ ≤ _ := by linarith

end PrivPCP.V72


namespace PrivPCP.V72

open GoodQLTC Classical

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (C : ∀ i, Submodule F (S i → F))

lemma hasDist_mono {α : Type} [Fintype α] (D : Submodule F (α → F)) {δ δ' : ℝ} (h : δ ≤ δ')
    (hD : HasDist D δ') : HasDist D δ := by
  intro c hc hc0
  exact le_trans (mul_le_mul_of_nonneg_right h (by positivity)) (hD c hc hc0)

/-- one block contribution -/
lemma block_bound (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) {n : ℕ}
    (ih : ∀ m < n, 2 ≤ m → ∀ A : Finset ι, A.card = m → ∀ β w,
      (m : ℝ) * fC Δ m * sdist C A β w ≤ ∑ k ∈ A, bad C A β w k)
    {A B A' : Finset ι} (hBA : B ⊆ A) (hA' : A \ B = A') (hm2 : 2 ≤ A'.card) (hmn : A'.card < n)
    (mlo nhi : ℕ) (hmlo : mlo ≤ A'.card) (hnhi : A'.card ≤ nhi) (β : ∀ i, S i) (w : (∀ i, S i) → F) :
    (mlo : ℝ) * fC Δ nhi * (∑ t : T B β, (sdist C A' t.1 w : ℝ)) ≤ ∑ k ∈ A', (bad C A β w k : ℝ) := by
  have havg : ∀ k ∈ A', (bad C A β w k : ℝ) = ∑ t : T B β, (bad C A' t.1 w k : ℝ) := by
    intro k _
    rw [← bad_avg C hBA β w k, hA']; push_cast; rfl
  rw [Finset.sum_congr rfl havg, Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have h := ih A'.card hmn hm2 A' rfl t.1 w
  have hf : fC Δ nhi ≤ fC Δ A'.card := fC_anti hΔ0 hΔ1 (by omega) hnhi
  have hs : (0 : ℝ) ≤ sdist C A' t.1 w := by positivity
  have hf0 : 0 ≤ fC Δ nhi := fC_nonneg hΔ0.le _
  calc (mlo : ℝ) * fC Δ nhi * (sdist C A' t.1 w : ℝ)
      ≤ (A'.card : ℝ) * fC Δ A'.card * (sdist C A' t.1 w : ℝ) := by
        gcongr
    _ ≤ _ := by push_cast at h ⊢; exact h

theorem LT72 (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hC : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ wt c) :
    ∀ n, 2 ≤ n → ∀ A : Finset ι, A.card = n → ∀ β w,
      (n : ℝ) * fC Δ n * sdist C A β w ≤ ∑ k ∈ A, bad C A β w k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn A hAc β w
  have ih' : ∀ m < n, 2 ≤ m → ∀ A : Finset ι, A.card = m → ∀ β w,
      (m : ℝ) * fC Δ m * sdist C A β w ≤ ∑ k ∈ A, bad C A β w k :=
    fun m hm h2 => ih m hm h2
  rcases Nat.eq_or_lt_of_le hn with h2 | h3
  · -- the two-dimensional case
    subst h2
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hAc
    rw [Finset.sum_pair hij]
    have hb := base72 C Δ hΔ0 hΔ1 hC i j hij β w
    have hf : (2 : ℝ) * fC Δ 2 ≤ Δ := by
      unfold fC
      have : Δ ^ 16 ≤ Δ := by
        calc Δ ^ 16 ≤ Δ ^ 1 := pow_le_pow_of_le_one hΔ0.le hΔ1 (by norm_num)
          _ = Δ := pow_one Δ
      norm_num
      have : (0 : ℝ) ≤ Δ ^ 16 := by positivity
      nlinarith
    have hs : (0 : ℝ) ≤ sdist C {i, j} β w := by positivity
    push_cast
    nlinarith
  · -- split into three balanced blocks
    have h3' : 3 ≤ n := h3
    obtain ⟨B1, hB1A, hB1c⟩ := Finset.exists_subset_card_eq (s := A) (n := n / 3) (by omega)
    obtain ⟨B2, hB2A, hB2c⟩ := Finset.exists_subset_card_eq (s := A \ B1) (n := (n + 1) / 3)
      (by rw [Finset.card_sdiff_of_subset hB1A]; omega)
    set B3 := (A \ B1) \ B2 with hB3
    have hB3c : B3.card = (n + 2) / 3 := by
      rw [hB3, Finset.card_sdiff_of_subset hB2A, Finset.card_sdiff_of_subset hB1A]; omega
    have h12 : Disjoint B1 B2 := by
      rw [Finset.disjoint_left]; intro x hx hx2
      exact (Finset.mem_sdiff.1 (hB2A hx2)).2 hx
    have h13 : Disjoint B1 B3 := by
      rw [Finset.disjoint_left]; intro x hx hx3
      exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hx3).1).2 hx
    have h23 : Disjoint B2 B3 := by
      rw [Finset.disjoint_left]; intro x hx hx3
      exact (Finset.mem_sdiff.1 hx3).2 hx
    have hA : A = B1 ∪ B2 ∪ B3 := by
      ext x
      simp only [Finset.mem_union, hB3, Finset.mem_sdiff]
      constructor
      · intro hx
        by_cases h1 : x ∈ B1
        · exact Or.inl (Or.inl h1)
        by_cases h2 : x ∈ B2
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨⟨hx, h1⟩, h2⟩
      · rintro ((h | h) | h)
        · exact hB1A h
        · exact (Finset.mem_sdiff.1 (hB2A h)).1
        · exact h.1.1
    have hB2A' : B2 ⊆ A := fun x hx => (Finset.mem_sdiff.1 (hB2A hx)).1
    have hB3A' : B3 ⊆ A := fun x hx => (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hx).1).1
    have e1 : A \ B1 = B2 ∪ B3 := by
      rw [hA]; ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(( h | h) | h), hn⟩
        · exact absurd h hn
        · exact Or.inl h
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl (Or.inr h), Finset.disjoint_right.1 h12 h⟩
        · exact ⟨Or.inr h, Finset.disjoint_right.1 h13 h⟩
    have e2 : A \ B2 = B1 ∪ B3 := by
      rw [hA]; ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(( h | h) | h), hn⟩
        · exact Or.inl h
        · exact absurd h hn
        · exact Or.inr h
      · rintro (h | h)
        · exact ⟨Or.inl (Or.inl h), Finset.disjoint_left.1 h12 h⟩
        · exact ⟨Or.inr h, Finset.disjoint_right.1 h23 h⟩
    have e3 : A \ B3 = B1 ∪ B2 := by
      rw [hA]; ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨(( h | h) | h), hn⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hn
      · rintro (h | h)
        · exact ⟨Or.inl (Or.inl h), Finset.disjoint_left.1 h13 h⟩
        · exact ⟨Or.inl (Or.inr h), Finset.disjoint_left.1 h23 h⟩
    have c23 : (B2 ∪ B3).card = (n + 1) / 3 + (n + 2) / 3 := by
      rw [Finset.card_union_of_disjoint h23, hB2c, hB3c]
    have c13 : (B1 ∪ B3).card = n / 3 + (n + 2) / 3 := by
      rw [Finset.card_union_of_disjoint h13, hB1c, hB3c]
    have c12 : (B1 ∪ B2).card = n / 3 + (n + 1) / 3 := by
      rw [Finset.card_union_of_disjoint h12, hB1c, hB2c]
    set mlo := n - (n + 2) / 3
    set nhi := n - n / 3
    have b1 := block_bound C Δ hΔ0 hΔ1 ih' hB1A e1 (by omega) (by omega) mlo nhi (by omega) (by omega) β w
    have b2 := block_bound C Δ hΔ0 hΔ1 ih' hB2A' e2 (by omega) (by omega) mlo nhi (by omega) (by omega) β w
    have b3 := block_bound C Δ hΔ0 hΔ1 ih' hB3A' e3 (by omega) (by omega) mlo nhi (by omega) (by omega) β w
    -- Viderman on the slice
    set δ := Δ ^ ((n + 2) / 3) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := pow_le_one₀ hΔ0.le hΔ1
    have hdist : ∀ B : Finset ι, B.card ≤ (n + 2) / 3 → HasDist (resCode C B β) δ := by
      intro B hB
      exact hasDist_mono _ (pow_le_pow_of_le_one hΔ0.le hΔ1 hB) (resCode_dist C Δ hΔ0.le hC B β)
    have hv := viderman_slice C hA h12 h13 h23 δ hδ0 hδ1 β (hdist B1 (by omega)) (hdist B2 (by omega))
      (hdist B3 (by omega)) w
    -- the sums over the blocks
    have hsplit : ∑ k ∈ B2 ∪ B3, (bad C A β w k : ℝ) + ∑ k ∈ B1 ∪ B3, (bad C A β w k : ℝ) +
        ∑ k ∈ B1 ∪ B2, (bad C A β w k : ℝ) = 2 * ∑ k ∈ A, (bad C A β w k : ℝ) := by
      rw [Finset.sum_union h23, Finset.sum_union h13, Finset.sum_union h12, hA,
        Finset.sum_union (Finset.disjoint_union_left.2 ⟨h13, h23⟩), Finset.sum_union h12]
      ring
    have hkey := real_key Δ hΔ0 hΔ1 n h3'
    have hsd : (0 : ℝ) ≤ sdist C A β w := by positivity
    have hf0 : 0 ≤ fC Δ nhi := fC_nonneg hΔ0.le _
    have hm0 : (0 : ℝ) ≤ mlo := by positivity
    push_cast at hv b1 b2 b3 ⊢
    set SS := (∑ t : T B1 β, (sdist C (B2 ∪ B3) t.1 w : ℝ)) + (∑ t : T B2 β, (sdist C (B1 ∪ B3) t.1 w : ℝ)) +
      (∑ t : T B3 β, (sdist C (B1 ∪ B2) t.1 w : ℝ))
    have hb : (mlo : ℝ) * fC Δ nhi * SS ≤ 2 * ∑ k ∈ A, (bad C A β w k : ℝ) := by
      rw [← hsplit]
      simp only [SS, mul_add]
      linarith
    have : (n : ℝ) * fC Δ n * (sdist C A β w : ℝ) ≤
        (mlo : ℝ) * fC Δ nhi * (δ ^ 3) / 12 * (sdist C A β w : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hsd
      have := hkey
      simp only [mlo, nhi, δ] at this ⊢
      exact this
    calc (n : ℝ) * fC Δ n * (sdist C A β w : ℝ)
        ≤ (mlo : ℝ) * fC Δ nhi * (δ ^ 3) / 12 * (sdist C A β w : ℝ) := this
      _ = (mlo : ℝ) * fC Δ nhi / 2 * (δ ^ 3 / 6 * (sdist C A β w : ℝ)) := by ring
      _ ≤ (mlo : ℝ) * fC Δ nhi / 2 * SS := by
          apply mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ ∑ k ∈ A, (bad C A β w k : ℝ) := by linarith

end PrivPCP.V72


open PrivPCP PrivPCP.V72 GoodQLTC Classical

theorem solution {F : Type} [Field F] [Fintype F] {r : ℕ} (hr : 2 ≤ r) {S : Fin r → Type}
    [∀ i, Fintype (S i)] (C : ∀ i, Submodule F (S i → F)) (hC : ∀ i, C i ≠ ⊥) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hdist : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ GoodQLTC.supportCard c)
    (w : (∀ i, S i) → F) :
    Δ ^ (8 * r) / (10 ^ 6 * (r : ℝ) ^ 16) * ((distTo w (tensorCode C) : ℝ) / Fintype.card (∀ i, S i)) ≤
      (1 / (r : ℝ)) * ∑ i, lineRejFrac C i w := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hRHS : 0 ≤ (1 / (r : ℝ)) * ∑ i, lineRejFrac C i w := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => by unfold lineRejFrac; positivity
  rcases eq_or_lt_of_le hΔ with h0 | hΔ0
  · rw [← h0, zero_pow (by omega), zero_div, zero_mul]; exact hRHS
  -- `Δ ≤ 1`
  have hΔ1 : Δ ≤ 1 := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hC ⟨0, by omega⟩)
    have h := hdist _ c hc hc0
    have hle : (supportCard c : ℝ) ≤ Fintype.card (S ⟨0, by omega⟩) := by
      unfold supportCard; exact_mod_cast Finset.card_le_univ _
    have hpos : (0 : ℝ) < Fintype.card (S ⟨0, by omega⟩) := by
      obtain ⟨x, hx⟩ : ∃ x, c x ≠ 0 := by by_contra hh; push Not at hh; exact hc0 (funext hh)
      have : Nonempty (S ⟨0, by omega⟩) := ⟨x⟩
      exact_mod_cast Fintype.card_pos
    by_contra hgt; push Not at hgt
    nlinarith
  rcases isEmpty_or_nonempty (∀ i, S i) with hE | hne
  · rw [Fintype.card_eq_zero, Nat.cast_zero, div_zero, mul_zero]; exact hRHS
  obtain ⟨β⟩ := hne
  haveI : Nonempty (∀ i, S i) := ⟨β⟩
  have hC' : ∀ i, ∀ c ∈ C i, c ≠ 0 → Δ * Fintype.card (S i) ≤ wt c := by
    intro i c hc hc0; rw [wt_eq_supportCard]; exact hdist i c hc hc0
  have hLT := LT72 C Δ hΔ0 hΔ1 hC' r hr Finset.univ (by simp) β w
  have hSl : Sl (Finset.univ : Finset (Fin r)) β = Finset.univ := by
    ext x; simp [mem_Sl]
  have hcode : ∀ c, c ∈ sliceCode C Finset.univ β ↔ c ∈ tensorCode C := by
    intro c
    rw [mem_sliceCode, hSl]
    simp only [tensorCode, Submodule.mem_iInf, axisCode, Submodule.mem_comap, LinearMap.funLeft_apply]
    constructor
    · intro h i b; exact h b (Finset.mem_univ _) i (Finset.mem_univ _)
    · intro h ω _ i _; exact h i ω
  have hsd : sdist C Finset.univ β w = distTo w (tensorCode C) := by
    unfold sdist distTo
    congr 1
    ext d
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c, (hcode c).1 hc, ?_⟩
      unfold supportCard; rw [hSl]; congr 1; ext x; simp [sub_eq_zero]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c, (hcode c).2 hc, ?_⟩
      unfold supportCard; rw [hSl]; congr 1; ext x; simp [sub_eq_zero]
  have hbad : ∀ i, (bad C Finset.univ β w i : ℝ) = lineRejFrac C i w * Fintype.card (∀ i, S i) := by
    intro i
    have hN : (0 : ℝ) < Fintype.card (∀ i, S i) := by exact_mod_cast Fintype.card_pos
    unfold bad lineRejFrac
    rw [hSl, div_mul_cancel₀ _ hN.ne']
    congr 2
  have hN : (0 : ℝ) < Fintype.card (∀ i, S i) := by exact_mod_cast Fintype.card_pos
  rw [hsd] at hLT
  push_cast at hLT
  simp only [hbad] at hLT
  rw [← Finset.sum_mul] at hLT
  unfold fC at hLT
  set D := (distTo w (tensorCode C) : ℝ)
  set N := (Fintype.card (∀ i, S i) : ℝ)
  set L := ∑ i, lineRejFrac C i w
  set K := Δ ^ (8 * r) / (10 ^ 6 * (r : ℝ) ^ 16)
  have key : K * (D / N) = ((r : ℝ) * K * D) / ((r : ℝ) * N) := by
    field_simp
  have key2 : (1 / (r : ℝ)) * L = (L * N) / ((r : ℝ) * N) := by
    field_simp
  rw [key, key2]
  exact div_le_div_of_nonneg_right hLT (by positivity)


