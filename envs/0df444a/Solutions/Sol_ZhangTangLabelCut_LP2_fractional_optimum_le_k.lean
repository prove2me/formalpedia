-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.fractional_optimum_le_k
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:05:25.920981+00:00
-- url     : https://prove2.me/submissions/5b8a5034-74d9-45b7-a487-28b01a00f87b

import Mathlib
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

set_option autoImplicit false

namespace ZhangTangLabelCut.LP2

def spos {k h : ℕ} (d : ℕ) : ShutterVertex k d h → ℕ
  | Sum.inl false => 0
  | Sum.inl true => 2 * d
  | Sum.inr (_, Sum.inl j) => 2 * (j.val + 1)
  | Sum.inr (_, Sum.inr (j, _)) => 2 * j.val + 1

lemma spos_junction {k h : ℕ} (d : ℕ) (c : Chain k h) (j : Fin (d + 1)) :
    spos d (junction c j) = 2 * j.val := by
  unfold junction
  split_ifs with h0 hd
  · simp [spos, h0]
  · simp [spos, hd]
  · simp only [spos]; omega

lemma spos_edge {k h : ℕ} (d : ℕ) (e : ShutterEdge k d h) :
    spos d (shutterTail e) + 1 = spos d (shutterHead e) ∨
    spos d (shutterHead e) + 1 = spos d (shutterTail e) := by
  obtain ⟨c, j, b, f⟩ := e
  cases f
  · simp only [shutterTail, shutterHead, if_false, middle, Bool.false_eq_true]
    rw [spos_junction]
    simp [spos] <;> omega
  · simp only [shutterTail, shutterHead, if_true, middle]
    rw [spos_junction]
    simp [spos] <;> omega

lemma ivt_fin (L : ℕ) (g : Fin (L + 1) → ℕ)
    (hstep : ∀ i : Fin L, g i.castSucc + 1 = g i.succ ∨ g i.succ + 1 = g i.castSucc)
    (h0 : g 0 = 0) (M : ℕ) (hL : g (Fin.last L) = M) (m : ℕ) (hm : m ≤ M) :
    ∃ i, g i = m := by
  have hex : ∃ n, ∃ hn : n < L + 1, m ≤ g ⟨n, hn⟩ :=
    ⟨L, by omega, by rw [show (⟨L, by omega⟩ : Fin (L + 1)) = Fin.last L from rfl, hL]; exact hm⟩
  have spec := Nat.find_spec hex
  have hmin : ∀ n, n < Nat.find hex → ¬ ∃ hn : n < L + 1, m ≤ g ⟨n, hn⟩ :=
    fun n hn => Nat.find_min hex hn
  generalize Nat.find hex = n0 at spec hmin
  obtain ⟨hn0, hge⟩ := spec
  rcases n0 with _ | n'
  · refine ⟨0, ?_⟩
    have : g ⟨0, hn0⟩ = 0 := h0
    omega
  · have hn' : n' < L := by omega
    have hlt' : g ⟨n', by omega⟩ < m := by
      by_contra hc
      exact hmin n' (by omega) ⟨by omega, by omega⟩
    rcases hstep ⟨n', hn'⟩ with h1 | h1
    · refine ⟨⟨n' + 1, by omega⟩, ?_⟩
      have e1 : g (⟨n', hn'⟩ : Fin L).castSucc = g ⟨n', by omega⟩ := rfl
      have e2 : g (⟨n', hn'⟩ : Fin L).succ = g ⟨n' + 1, by omega⟩ := rfl
      omega
    · exfalso
      have e1 : g (⟨n', hn'⟩ : Fin L).castSucc = g ⟨n', by omega⟩ := rfl
      have e2 : g (⟨n', hn'⟩ : Fin L).succ = g ⟨n' + 1, by omega⟩ := rfl
      omega

def chn {k d h : ℕ} : ShutterVertex k d h → Option (Chain k h)
  | Sum.inl _ => none
  | Sum.inr x => some x.1

lemma chn_tail {k d h : ℕ} (e : ShutterEdge k d h) :
    chn (shutterTail e) = none ∨ chn (shutterTail e) = some e.1 := by
  obtain ⟨c, j, b, f⟩ := e
  cases f
  · simp only [shutterTail, if_false, Bool.false_eq_true, junction]
    split_ifs <;> simp [chn]
  · simp [shutterTail, middle, chn]

lemma chn_head {k d h : ℕ} (e : ShutterEdge k d h) :
    chn (shutterHead e) = none ∨ chn (shutterHead e) = some e.1 := by
  obtain ⟨c, j, b, f⟩ := e
  cases f
  · simp [shutterHead, middle, chn]
  · simp only [shutterHead, if_true, junction]
    split_ifs <;> simp [chn]

lemma middle_of_edge {k d h : ℕ} (e : ShutterEdge k d h) (c : Chain k h) (j : Fin d) (b : Bool)
    (hm : shutterTail e = middle c j b ∨ shutterHead e = middle c j b) :
    e.1 = c ∧ e.2.1 = j ∧ e.2.2.1 = b := by
  obtain ⟨c', j', b', f⟩ := e
  have jm : ∀ (c1 c2 : Chain k h) (j1 : Fin (d + 1)) (j2 : Fin d) (b2 : Bool),
      junction c1 j1 ≠ middle c2 j2 b2 := by
    intro c1 c2 j1 j2 b2
    unfold junction middle
    split_ifs <;> simp
  cases f
  · rcases hm with hm | hm
    · simp only [shutterTail, if_false, Bool.false_eq_true] at hm
      exact absurd hm (jm _ _ _ _ _)
    · simp only [shutterHead, if_false, Bool.false_eq_true, middle, Sum.inr.injEq,
        Prod.mk.injEq, Sum.inr.injEq] at hm
      simp only [middle] at *
      exact ⟨hm.1, hm.2.1, hm.2.2⟩
  · rcases hm with hm | hm
    · simp only [shutterTail, if_true, middle, Sum.inr.injEq, Prod.mk.injEq] at hm
      exact ⟨hm.1, hm.2.1, hm.2.2⟩
    · simp only [shutterHead, if_true] at hm
      exact absurd hm (jm _ _ _ _ _)

def shLabel {k d h : ℕ} (σ : Sample k d h) (e : ShutterEdge k d h) : Fin k × Fin d :=
  if e.2.2.1 then (e.1.1.val.2, σ e.1 e.2.1) else (e.1.1.val.1, e.2.1)

lemma step_chn {k d h : ℕ} {directed : Bool} (e : ShutterEdge k d h) (u v : ShutterVertex k d h)
    (hs : (shutterGraph k d h directed).Step e u v) (hu : chn u ≠ none) (hv : chn v ≠ none) :
    chn u = chn v := by
  rcases hs with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
  · subst h1 h2
    have hu' : chn (shutterTail e) ≠ none := hu
    have hv' : chn (shutterHead e) ≠ none := hv
    show chn (shutterTail e) = chn (shutterHead e)
    rcases chn_tail e with a | a <;> rcases chn_head e with b | b <;> simp_all
  · subst h1 h2
    have hu' : chn (shutterHead e) ≠ none := hu
    have hv' : chn (shutterTail e) ≠ none := hv
    show chn (shutterHead e) = chn (shutterTail e)
    rcases chn_tail e with a | a <;> rcases chn_head e with b | b <;> simp_all

lemma interior_chn {k d h : ℕ} {directed : Bool}
    (p : Path (shutterGraph k d h directed) (Sum.inl false) (Sum.inl true))
    (m : ℕ) (hm : m < p.length + 1) (h0 : 0 < m) (hL : m < p.length) :
    chn (p.vertex ⟨m, hm⟩) ≠ none := by
  intro hc
  cases hv : p.vertex ⟨m, hm⟩ with
  | inl b =>
    cases b
    · have : p.vertex ⟨m, hm⟩ = p.vertex 0 := by rw [hv, p.start]
      have := p.simple this
      simp [Fin.ext_iff] at this
      omega
    · have : p.vertex ⟨m, hm⟩ = p.vertex (Fin.last p.length) := by rw [hv, p.finish]
      have := p.simple this
      simp [Fin.ext_iff] at this
      omega
  | inr x => simp [chn, hv] at hc

lemma chain_const {k d h : ℕ} {directed : Bool}
    (p : Path (shutterGraph k d h directed) (Sum.inl false) (Sum.inl true))
    (i1 : ℕ) (h1 : 0 < i1) :
    ∀ n (h2 : i1 + n < p.length),
      chn (p.vertex ⟨i1, by omega⟩) = chn (p.vertex ⟨i1 + n, by omega⟩) := by
  intro n
  induction n with
  | zero => intro h2; rfl
  | succ n ih =>
    intro h2
    rw [ih (by omega)]
    have hs := p.step ⟨i1 + n, by omega⟩
    exact step_chn _ _ _ hs (interior_chn p (i1 + n) (by omega) (by omega) (by omega))
      (interior_chn p (i1 + n + 1) (by omega) (by omega) h2)

lemma odd_middle {k d h : ℕ} (x : ShutterVertex k d h) (j : Fin d) (hx : spos d x = 2 * j.val + 1) :
    ∃ c b, x = middle c j b := by
  rcases x with b | ⟨c, (j' | ⟨j', b⟩)⟩
  · cases b <;> simp [spos] at hx <;> omega
  · simp [spos] at hx; omega
  · simp only [spos] at hx
    have : j' = j := Fin.ext (by omega)
    exact ⟨c, b, by rw [this]; rfl⟩

lemma path_label_card {k d h : ℕ} {directed : Bool} (hd : 0 < d) (σ : Sample k d h)
    (p : Path (shutterGraph k d h directed) (Sum.inl false) (Sum.inl true)) :
    d ≤ (Finset.univ.image (fun e : Fin p.length => shLabel σ (p.edge e))).card := by
  classical
  have hex : ∀ j : Fin d, ∃ i : Fin (p.length + 1), spos d (p.vertex i) = 2 * j.val + 1 := by
    intro j
    refine ivt_fin p.length (fun i => spos d (p.vertex i)) ?_ ?_ (2 * d) ?_ (2 * j.val + 1)
      (by omega)
    · intro i
      have hs := p.step i
      have he := spos_edge d (p.edge i)
      rcases hs with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
      · have h1' : shutterTail (p.edge i) = p.vertex i.castSucc := h1
        have h2' : shutterHead (p.edge i) = p.vertex i.succ := h2
        rw [h1', h2'] at he
        exact he
      · have h1' : shutterHead (p.edge i) = p.vertex i.castSucc := h1
        have h2' : shutterTail (p.edge i) = p.vertex i.succ := h2
        rw [h1', h2'] at he
        exact he.symm
    · show spos d (p.vertex 0) = 0
      rw [p.start]; rfl
    · show spos d (p.vertex (Fin.last _)) = 2 * d
      rw [p.finish]; rfl
  choose i hi using hex
  have hmid : ∀ j, ∃ c b, p.vertex (i j) = middle c j b := fun j => odd_middle _ j (hi j)
  choose c b hcb using hmid
  have hint : ∀ j, 0 < (i j).val ∧ (i j).val < p.length := by
    intro j
    constructor
    · by_contra hc
      have : i j = 0 := Fin.ext (by show (i j).val = 0; omega)
      have h1 := hcb j
      rw [this, p.start] at h1
      simp [middle] at h1
    · by_contra hc
      have : i j = Fin.last _ := Fin.ext (by have := (i j).isLt; simp; omega)
      have h1 := hcb j
      rw [this, p.finish] at h1
      simp [middle] at h1
  have key : ∀ j j', (i j).val ≤ (i j').val → c j = c j' := by
    intro j j' hle
    have h1 := chain_const p (i j).val (hint j).1 ((i j').val - (i j).val)
      (by have := (hint j').2; omega)
    have e1 : (⟨(i j).val, by omega⟩ : Fin (p.length + 1)) = i j := Fin.ext rfl
    have e2 : (⟨(i j).val + ((i j').val - (i j).val), by omega⟩ : Fin (p.length + 1)) = i j' :=
      Fin.ext (by simp; omega)
    rw [e1, e2, hcb j, hcb j'] at h1
    simpa [middle, chn] using h1
  have hc : ∀ j j', c j = c j' := by
    intro j j'
    rcases le_total (i j).val (i j').val with hle | hle
    · exact key j j' hle
    · exact (key j' j hle).symm
  have hlab : ∀ j : Fin d, ∃ e : Fin p.length,
      shLabel σ (p.edge e) = if b j then ((c j).1.val.2, σ (c j) j) else ((c j).1.val.1, j) := by
    intro j
    refine ⟨⟨(i j).val, (hint j).2⟩, ?_⟩
    have hs := p.step ⟨(i j).val, (hint j).2⟩
    have e1 : (⟨(i j).val, (hint j).2⟩ : Fin p.length).castSucc = i j := Fin.ext rfl
    rw [e1] at hs
    have hm : shutterTail (p.edge ⟨(i j).val, (hint j).2⟩) = middle (c j) j (b j) ∨
        shutterHead (p.edge ⟨(i j).val, (hint j).2⟩) = middle (c j) j (b j) := by
      rcases hs with ⟨h1, _⟩ | ⟨_, h1, _⟩
      · left; rw [← hcb j]; exact h1
      · right; rw [← hcb j]; exact h1
    obtain ⟨q1, q2, q3⟩ := middle_of_edge _ _ _ _ hm
    generalize p.edge ⟨(i j).val, (hint j).2⟩ = e at q1 q2 q3 ⊢
    unfold shLabel
    rw [q3, q1, q2]
  choose ed hed using hlab
  have hinj : ∀ j j', (if b j then ((c j).1.val.2, σ (c j) j) else ((c j).1.val.1, j)) =
      (if b j' then ((c j').1.val.2, σ (c j') j') else ((c j').1.val.1, j')) → j = j' := by
    intro j j' heq
    have hcc := hc j j'
    have hne : (c j).1.val.1 ≠ (c j).1.val.2 := ne_of_lt (c j).1.property
    rw [← hcc] at heq
    cases hb : b j <;> cases hb' : b j' <;> rw [hb, hb'] at heq <;> simp at heq
    · exact heq
    · exact absurd heq.1 hne
    · exact absurd heq.1.symm hne
    · first | exact heq | exact (σ (c j)).injective heq
  have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin d)))
    (t := Finset.univ.image (fun e : Fin p.length => shLabel σ (p.edge e)))
    (fun j => shLabel σ (p.edge (ed j))) (by
      intro j _
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨ed j, rfl⟩) (by
      intro j _ j' _ hjj
      apply hinj
      rw [← hed j, ← hed j']
      exact hjj)
  simpa using this

lemma frac_le_aux (k d h : ℕ) (hd : 0 < d) (directed : Bool) (σ : Sample k d h) :
    (shutterInstance k d h directed σ).lp.value ≤ (k : EReal) := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hfeas : (shutterInstance k d h directed σ).lp.Feasible (fun _ => 1 / (d : ℝ)) := by
    refine ⟨fun _ => by positivity, ?_⟩
    intro R hR
    have hR2 := (Finset.mem_filter.1 hR).2
    obtain ⟨p, hp⟩ := hR2
    have hc := path_label_card hd σ p
    have hc2 : d ≤ R.card := by
      have hpl : (shutterInstance k d h directed σ).pathLabels p =
          @Finset.image _ _ (fun a b => Classical.propDecidable (a = b))
            (fun e : Fin p.length => shLabel σ (p.edge e)) Finset.univ := by
        ext l
        simp only [LabelCut.pathLabels, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨a, ha⟩
          exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩
        · intro hl
          obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hl
          exact ⟨a, ha⟩
      have hq : @Finset.image _ _ (fun a b => Classical.propDecidable (a = b))
            (fun e : Fin p.length => shLabel σ (p.edge e)) Finset.univ =
          Finset.univ.image (fun e : Fin p.length => shLabel σ (p.edge e)) := by
        have : (fun a b => Classical.propDecidable (a = b) : DecidableEq (Fin k × Fin d)) =
            (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
        rw [this]
      rw [← hp, hpl, hq]
      exact hc
    show (1 : ℝ) ≤ ∑ l ∈ R, 1 / (d : ℝ)
    rw [Finset.sum_const, nsmul_eq_mul]
    have : (d : ℝ) ≤ R.card := by exact_mod_cast hc2
    rw [mul_one_div, le_div_iff₀ hdpos]
    linarith
  have hobj : (shutterInstance k d h directed σ).lp.objective (fun _ => 1 / (d : ℝ)) = k := by
    show ∑ l : Fin k × Fin d, (1 : ℝ) * (1 / (d : ℝ)) = k
    rw [Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    push_cast
    field_simp
  unfold CoveringLP.value
  apply sInf_le
  exact ⟨_, hfeas, by rw [hobj]; norm_cast⟩

theorem fractional_optimum_le_k_aux (k d h : ℕ) (hk : 2 ≤ k) (hd : 0 < d) (hh : 0 < h)
    (directed : Bool) (σ : Sample k d h) :
    (shutterInstance k d h directed σ).frac ≤ (k : ℝ) := by
  have h1 := frac_le_aux k d h hd directed σ
  unfold LabelCut.frac
  by_cases hb : (shutterInstance k d h directed σ).lp.value = ⊥
  · rw [hb]; simp
  · have := EReal.toReal_le_toReal h1 hb (EReal.coe_ne_top _)
    have e : ((k : EReal)).toReal = (k : ℝ) := by
      rw [show ((k : ℕ) : EReal) = (((k : ℝ)) : EReal) from by norm_cast]
      exact EReal.toReal_coe _
    rw [e] at this
    exact this

end ZhangTangLabelCut.LP2

theorem solution (k d h : ℕ) (hk : 2 ≤ k) (hd : 0 < d) (hh : 0 < h)
    (directed : Bool) (σ : ZhangTangLabelCut.LP2.Sample k d h) :
    (ZhangTangLabelCut.LP2.shutterInstance k d h directed σ).frac ≤ (k : ℝ) :=
  ZhangTangLabelCut.LP2.fractional_optimum_le_k_aux k d h hk hd hh directed σ
