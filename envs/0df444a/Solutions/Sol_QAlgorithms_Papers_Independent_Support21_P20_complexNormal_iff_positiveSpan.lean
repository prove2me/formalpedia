-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P20.complexNormal_iff_positiveSpan
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:44:07.051901+00:00
-- url     : https://prove2.me/submissions/73c98866-afec-4b16-ba07-5ffe665031a9

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal Topology

universe u v

section g72gk34
variable {L : Type*} [Order.Frame L]

def g72gk34_Pos (ν : L → ℝ) (a : L) : Prop := ∀ b : L, b ≤ a → 0 ≤ ν b

lemma g72gk34_le_compl {x y : L} (h : x ⊓ y = ⊥) : x ≤ yᶜ :=
  le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h)

lemma g72gk34_bot {ν : L → ℝ} (h : IsNormalValuation ν) : ν ⊥ = 0 := h.1.1.1

lemma g72gk34_disj {ν : L → ℝ} (h : IsNormalValuation ν) {x y : L} (hxy : x ⊓ y = ⊥) :
    ν (x ⊔ y) = ν x + ν y := by
  have := h.1.1.2 x y
  rw [hxy, g72gk34_bot h] at this
  linarith

lemma g72gk34_compl_eq {x b : L} (hx : x ≤ b) : (x ⊔ (b ⊓ xᶜ))ᶜ = bᶜ := by
  apply le_antisymm
  · rw [compl_sup]
    apply g72gk34_le_compl
    apply le_bot_iff.mp
    calc xᶜ ⊓ (b ⊓ xᶜ)ᶜ ⊓ b ≤ (b ⊓ xᶜ) ⊓ (b ⊓ xᶜ)ᶜ :=
          le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
            (inf_le_left.trans inf_le_right)
      _ = ⊥ := inf_compl_self _
  · exact compl_le_compl (sup_le hx inf_le_left)

lemma g72gk34_split {ν : L → ℝ} (h : IsNormalValuation ν) {x b : L} (hx : x ≤ b) :
    ν b = ν x + ν (b ⊓ xᶜ) := by
  have h1 : ν b = ν (x ⊔ (b ⊓ xᶜ)) := by
    rw [← h.2 b, ← g72gk34_compl_eq hx, h.2]
  rw [h1, g72gk34_disj h]
  apply le_bot_iff.mp
  calc x ⊓ (b ⊓ xᶜ) ≤ x ⊓ xᶜ := inf_le_inf_left _ inf_le_right
    _ = ⊥ := inf_compl_self _

lemma g72gk34_pos_bot (ν : L → ℝ) (h : IsNormalValuation ν) : g72gk34_Pos ν ⊥ := by
  intro b hb
  rw [le_bot_iff.mp hb, g72gk34_bot h]

lemma g72gk34_pos_sup {ν : L → ℝ} (h : IsNormalValuation ν) {a1 a2 : L}
    (h1 : g72gk34_Pos ν a1) (h2 : g72gk34_Pos ν a2) : g72gk34_Pos ν (a1 ⊔ a2) := by
  intro b hb
  set x := b ⊓ a1 with hxdef
  set y := b ⊓ xᶜ ⊓ a2 with hydef
  have e1 := g72gk34_split h (x := x) (b := b) inf_le_left
  have e2 := g72gk34_split h (x := y) (b := b ⊓ xᶜ) inf_le_left
  have hw : b ⊓ xᶜ ⊓ yᶜ = ⊥ := by
    apply le_bot_iff.mp
    have hw1 : b ⊓ xᶜ ⊓ yᶜ = (b ⊓ xᶜ ⊓ yᶜ) ⊓ (a1 ⊔ a2) :=
      (inf_eq_left.mpr ((inf_le_left.trans inf_le_left).trans hb)).symm
    rw [hw1, inf_sup_left]
    apply sup_le
    · calc b ⊓ xᶜ ⊓ yᶜ ⊓ a1 ≤ x ⊓ xᶜ :=
            le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right)
              (inf_le_left.trans (inf_le_left.trans inf_le_right))
        _ = ⊥ := inf_compl_self _
    · calc b ⊓ xᶜ ⊓ yᶜ ⊓ a2 ≤ y ⊓ yᶜ :=
            le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (inf_le_left.trans inf_le_right)
        _ = ⊥ := inf_compl_self _
  rw [hw, g72gk34_bot h] at e2
  have p1 : 0 ≤ ν x := h1 x inf_le_right
  have p2 : 0 ≤ ν y := h2 y inf_le_right
  linarith

lemma g72gk34_isDir {s : Set L} (hd : DirectedOn (· ≤ ·) s) : IsDirected s (· ≤ ·) :=
  ⟨fun x y => by
    obtain ⟨z, hz, h1, h2⟩ := hd x x.2 y y.2
    exact ⟨⟨z, hz⟩, h1, h2⟩⟩

lemma g72gk34_lim_ge {ν : L → ℝ} (h : IsNormalValuation ν) {s : Set L} {a : L}
    (hne : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) (hl : IsLUB s a)
    (hp : ∀ b ∈ s, 0 ≤ ν b) : 0 ≤ ν a := by
  haveI : Nonempty s := hne.to_subtype
  haveI := g72gk34_isDir hd
  exact ge_of_tendsto' (h.1.2 s a hne hd hl) (fun b => hp b b.2)

lemma g72gk34_carrier_pos {ν : L → ℝ} (h : IsNormalValuation ν) :
    g72gk34_Pos ν (positiveCarrier ν) := by
  intro b hb
  let s : Set L := {z | ∃ a, g72gk34_Pos ν a ∧ z = b ⊓ a}
  apply g72gk34_lim_ge h (s := s) (a := b)
  · exact ⟨b ⊓ ⊥, ⊥, g72gk34_pos_bot ν h, rfl⟩
  · rintro _ ⟨a1, h1, rfl⟩ _ ⟨a2, h2, rfl⟩
    exact ⟨b ⊓ (a1 ⊔ a2), ⟨a1 ⊔ a2, g72gk34_pos_sup h h1 h2, rfl⟩,
      inf_le_inf_left _ le_sup_left, inf_le_inf_left _ le_sup_right⟩
  · constructor
    · rintro _ ⟨a, _, rfl⟩
      exact inf_le_left
    · intro u hu
      have : b = b ⊓ positiveCarrier ν := (inf_eq_left.mpr hb).symm
      rw [this, positiveCarrier, inf_sSup_eq]
      exact iSup₂_le fun a ha => hu ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha _ inf_le_right

lemma g72gk34_pos_iff {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    g72gk34_Pos ν a ↔ a ≤ positiveCarrier ν :=
  ⟨fun ha => le_sSup ha, fun ha b hb => g72gk34_carrier_pos h b (hb.trans ha)⟩

lemma g72gk34_choose {ν : L → ℝ} (h : IsNormalValuation ν) (r : L) :
    ∃ x ≤ r, ∀ y ≤ r, min 1 (-ν y) ≤ 2 * (-ν x) := by
  let S : Set ℝ := (fun y => min 1 (-ν y)) '' Set.Iic r
  have hS : BddAbove S := ⟨1, by rintro _ ⟨y, _, rfl⟩; exact min_le_left _ _⟩
  have hSn : S.Nonempty := ⟨_, r, le_refl r, rfl⟩
  by_cases hm : sSup S ≤ 0
  · refine ⟨⊥, bot_le, fun y hy => ?_⟩
    rw [g72gk34_bot h, neg_zero, mul_zero]
    exact (le_csSup hS ⟨y, hy, rfl⟩).trans hm
  · push_neg at hm
    obtain ⟨_, ⟨y0, hy0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSn (half_lt_self hm)
    refine ⟨y0, hy0, fun y hy => ?_⟩
    have h1 := le_csSup hS ⟨y, hy, rfl⟩
    have h2 : min 1 (-ν y0) ≤ -ν y0 := min_le_right _ _
    linarith

def g72gk34_seq (f : L → L) (b : L) : ℕ → L
  | 0 => ⊥
  | k + 1 => g72gk34_seq f b k ⊔ f (b ⊓ (g72gk34_seq f b k)ᶜ)

lemma g72gk34_exhaust {ν : L → ℝ} (h : IsNormalValuation ν) (b : L) :
    ∃ d ≤ b, g72gk34_Pos ν d ∧ ν b ≤ ν d := by
  choose f hf1 hf2 using g72gk34_choose h
  set X := g72gk34_seq f b with hXdef
  have hXs : ∀ k, X (k + 1) = X k ⊔ f (b ⊓ (X k)ᶜ) := fun k => rfl
  have hX0 : X 0 = ⊥ := rfl
  have hXb : ∀ k, X k ≤ b := by
    intro k
    induction k with
    | zero => rw [hX0]; exact bot_le
    | succ k ih => rw [hXs]; exact sup_le ih ((hf1 _).trans inf_le_left)
  have hmono : Monotone X := monotone_nat_of_le_succ fun k => by rw [hXs]; exact le_sup_left
  have hstep : ∀ k, ν (X (k + 1)) = ν (X k) + ν (f (b ⊓ (X k)ᶜ)) := by
    intro k
    rw [hXs, g72gk34_disj h]
    apply le_bot_iff.mp
    calc X k ⊓ f (b ⊓ (X k)ᶜ) ≤ X k ⊓ (X k)ᶜ :=
          inf_le_inf_left _ ((hf1 _).trans inf_le_right)
      _ = ⊥ := inf_compl_self _
  have hxneg : ∀ k, ν (f (b ⊓ (X k)ᶜ)) ≤ 0 := by
    intro k
    have := hf2 (b ⊓ (X k)ᶜ) ⊥ bot_le
    rw [g72gk34_bot h, neg_zero, min_eq_right zero_le_one] at this
    linarith
  have hXneg : ∀ k, ν (X k) ≤ 0 := by
    intro k
    induction k with
    | zero => rw [hX0, g72gk34_bot h]
    | succ k ih => rw [hstep]; linarith [hxneg k]
  set Xi := ⨆ k, X k with hXi
  have hXib : Xi ≤ b := iSup_le hXb
  have hdir : DirectedOn (· ≤ ·) (Set.range X) := directedOn_range.mpr (hmono.directed_le)
  have hlub : IsLUB (Set.range X) Xi := isLUB_iSup
  have hT := h.1.2 (Set.range X) Xi (Set.range_nonempty X) hdir hlub
  let g : ℕ → Set.range X := fun k => ⟨X k, k, rfl⟩
  have hg : Tendsto g atTop atTop := by
    rw [tendsto_atTop_atTop]
    rintro ⟨_, j, rfl⟩
    exact ⟨j, fun k hk => hmono hk⟩
  have hTX : Tendsto (fun k => ν (X k)) atTop (𝓝 (ν Xi)) := hT.comp hg
  have hTX1 : Tendsto (fun k => ν (X (k + 1))) atTop (𝓝 (ν Xi)) :=
    hTX.comp (tendsto_add_atTop_nat 1)
  have hx0 : Tendsto (fun k => 2 * (-ν (f (b ⊓ (X k)ᶜ)))) atTop (𝓝 0) := by
    have : Tendsto (fun k => 2 * (-(ν (X (k + 1)) - ν (X k)))) atTop
        (𝓝 (2 * (-(ν Xi - ν Xi)))) := ((hTX1.sub hTX).neg).const_mul 2
    rw [sub_self, neg_zero, mul_zero] at this
    refine this.congr fun k => ?_
    rw [hstep k]; ring
  have hXile : ν Xi ≤ 0 := le_of_tendsto' hTX hXneg
  refine ⟨b ⊓ Xiᶜ, inf_le_left, ?_, ?_⟩
  · intro y hy
    have hk : ∀ k, min 1 (-ν y) ≤ 2 * (-ν (f (b ⊓ (X k)ᶜ))) := fun k =>
      hf2 _ y (hy.trans (inf_le_inf_left _ (compl_le_compl (le_iSup X k))))
    have hle : min 1 (-ν y) ≤ 0 := ge_of_tendsto' hx0 hk
    by_contra hc
    push_neg at hc
    have : 0 < min 1 (-ν y) := lt_min one_pos (by linarith)
    linarith
  · have := g72gk34_split h hXib
    linarith

lemma g72gk34_negative {ν : L → ℝ} (h : IsNormalValuation ν) {c : L}
    (hc : c ⊓ positiveCarrier ν = ⊥) {b : L} (hb : b ≤ c) : ν b ≤ 0 := by
  obtain ⟨d, hdb, hdp, hle⟩ := g72gk34_exhaust h b
  have h1 : d ≤ positiveCarrier ν := le_sSup hdp
  have h2 : d = ⊥ := le_bot_iff.mp (hc ▸ le_inf (hdb.trans hb) h1)
  rw [h2, g72gk34_bot h] at hle
  exact hle

lemma g72gk34_neg {ν : L → ℝ} (h : IsNormalValuation ν) :
    IsNormalValuation (fun a => -ν a) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [g72gk34_bot h]
  · intro a b; have := h.1.1.2 a b; simp only; linarith
  · intro s a hne hd hl
    exact (h.1.2 s a hne hd hl).neg
  · intro a; simp only [h.2]

lemma g72gk34_regular {ν : L → ℝ} (h : IsNormalValuation ν) :
    (positiveCarrier ν)ᶜᶜ = positiveCarrier ν := by
  set P := positiveCarrier ν
  apply le_antisymm _ le_compl_compl
  apply le_sSup
  intro b hb
  have e := g72gk34_split h (x := b ⊓ P) (b := b) inf_le_left
  have hw : b ⊓ (b ⊓ P)ᶜ = ⊥ := by
    apply le_bot_iff.mp
    have hw1 : b ⊓ (b ⊓ P)ᶜ ≤ Pᶜ := by
      apply g72gk34_le_compl
      apply le_bot_iff.mp
      calc b ⊓ (b ⊓ P)ᶜ ⊓ P ≤ (b ⊓ P) ⊓ (b ⊓ P)ᶜ :=
            le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
              (inf_le_left.trans inf_le_right)
        _ = ⊥ := inf_compl_self _
    calc b ⊓ (b ⊓ P)ᶜ ≤ Pᶜ ⊓ Pᶜᶜ := le_inf hw1 (inf_le_left.trans hb)
      _ = ⊥ := inf_compl_self _
  rw [hw, g72gk34_bot h] at e
  have := g72gk34_carrier_pos h (b ⊓ P) inf_le_right
  linarith

lemma g72gk34_hahn {ν : L → ℝ} (h : IsNormalValuation ν) :
    (positiveCarrier ν ⊔ negativeCarrier ν)ᶜ = ⊥ := by
  set P := positiveCarrier ν
  set N := negativeCarrier ν
  set c := (P ⊔ N)ᶜ
  have hcP : c ⊓ P = ⊥ := by
    apply le_bot_iff.mp
    calc c ⊓ P ≤ Pᶜ ⊓ P := inf_le_inf_right _ (compl_le_compl le_sup_left)
      _ = ⊥ := compl_inf_self _
  have hcN : c ≤ N := by
    apply (g72gk34_pos_iff (g72gk34_neg h) c).mp
    intro b hb
    have := g72gk34_negative h hcP hb
    simp only; linarith
  apply le_bot_iff.mp
  calc c ≤ N ⊓ Nᶜ := le_inf hcN (compl_le_compl le_sup_right)
    _ = ⊥ := inf_compl_self _

lemma g72gk34_decomp {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    ν a = ν (positiveCarrier ν ⊓ a) + ν (negativeCarrier ν ⊓ a) := by
  set P := positiveCarrier ν
  set N := negativeCarrier ν
  have hQ := g72gk34_hahn h
  have h1 : ν a = ν ((P ⊔ N) ⊓ a) := by
    rw [← h.2 a, ← h.2 ((P ⊔ N) ⊓ a), compl_compl_inf_distrib, hQ, compl_bot, top_inf_eq]
  have h2 := h.1.1.2 (P ⊓ a) (N ⊓ a)
  rw [← inf_sup_right] at h2
  have hz1 : 0 ≤ ν (P ⊓ a ⊓ (N ⊓ a)) :=
    g72gk34_carrier_pos h _ (inf_le_left.trans inf_le_left)
  have hz2 : 0 ≤ -ν (P ⊓ a ⊓ (N ⊓ a)) :=
    g72gk34_carrier_pos (g72gk34_neg h) _ (inf_le_right.trans inf_le_left)
  linarith

lemma g72gk34_restrict {ν : L → ℝ} (h : IsNormalValuation ν) {Q : L} (hQ : Qᶜᶜ = Q) :
    IsNormalValuation (fun a => ν (Q ⊓ a)) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [inf_bot_eq, g72gk34_bot h]
  · intro a b
    have := h.1.1.2 (Q ⊓ a) (Q ⊓ b)
    simp only
    rw [← inf_sup_left, ← inf_inf_distrib_left] at this
    exact this
  · intro s a hne hd hl
    let s' : Set L := (fun b => Q ⊓ b) '' s
    have hne' : s'.Nonempty := hne.image _
    have hd' : DirectedOn (· ≤ ·) s' := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, h1, h2⟩ := hd x hx y hy
      exact ⟨Q ⊓ z, ⟨z, hz, rfl⟩, inf_le_inf_left _ h1, inf_le_inf_left _ h2⟩
    have hl' : IsLUB s' (Q ⊓ a) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact inf_le_inf_left _ (hl.1 hx)
      · intro u hu
        rw [← hl.sSup_eq, inf_sSup_eq]
        exact iSup₂_le fun b hb => hu ⟨b, hb, rfl⟩
    have hT := h.1.2 s' (Q ⊓ a) hne' hd' hl'
    let g : s → s' := fun b => ⟨Q ⊓ b.1, b.1, b.2, rfl⟩
    haveI : Nonempty s := hne.to_subtype
    haveI := g72gk34_isDir hd
    have hg : Tendsto g atTop atTop := by
      rw [tendsto_atTop_atTop]
      rintro ⟨_, b0, hb0, rfl⟩
      exact ⟨⟨b0, hb0⟩, fun b hb => inf_le_inf_left _ hb⟩
    exact hT.comp hg
  · intro a
    simp only
    rw [← hQ, ← compl_compl_inf_distrib, h.2, hQ]

lemma g72gk34_bool_cc (hB : ∀ a : L, a ⊔ aᶜ = ⊤) (a : L) : aᶜᶜ = a := by
  apply le_antisymm _ le_compl_compl
  calc aᶜᶜ = aᶜᶜ ⊓ (a ⊔ aᶜ) := by rw [hB, inf_top_eq]
    _ = (aᶜᶜ ⊓ a) ⊔ (aᶜᶜ ⊓ aᶜ) := inf_sup_left _ _ _
    _ ≤ a := sup_le inf_le_right (by rw [compl_inf_self]; exact bot_le)

lemma g72gk34_HJ {ν : L → ℝ} (h : IsNormalValuation ν)
    (hPP : positiveCarrier ν ⊔ (positiveCarrier ν)ᶜ = ⊤) : HahnJordanConclusions ν := by
  have hn := g72gk34_neg h
  refine ⟨fun a => g72gk34_pos_iff h a, fun a => g72gk34_pos_iff hn a, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply top_le_iff.mp
    rw [← hPP]
    apply sup_le_sup_left
    apply (g72gk34_pos_iff hn _).mp
    intro b hb
    have := g72gk34_negative h (c := (positiveCarrier ν)ᶜ) (compl_inf_self _) hb
    simp only; linarith
  · intro a
    constructor
    · intro ha
      exact le_inf ((g72gk34_pos_iff h a).mp fun b hb => (ha b hb).ge)
        ((g72gk34_pos_iff hn a).mp fun b hb => by show 0 ≤ -ν b; rw [ha b hb, neg_zero])
    · intro ha b hb
      have h1 := g72gk34_carrier_pos h b (hb.trans (ha.trans inf_le_left))
      have h2 : 0 ≤ -ν b := g72gk34_carrier_pos hn b (hb.trans (ha.trans inf_le_right))
      linarith
  · exact g72gk34_restrict h (g72gk34_regular h)
  · exact g72gk34_restrict hn (g72gk34_regular hn)
  · intro a; exact g72gk34_carrier_pos h _ inf_le_left
  · intro a; exact g72gk34_carrier_pos hn _ inf_le_left
  · intro a
    have := g72gk34_decomp h a
    simp only [jordanPositive, jordanNegative]
    linarith

lemma g72gk34_regime {ν : L → ℝ} (h : IsJordanRegime ν) : HahnJordanConclusions ν := by
  rcases h with ⟨hS, hN⟩ | ⟨hB, hC⟩
  · apply g72gk34_HJ hN
    have := hS.2 (positiveCarrier ν)
    rw [g72gk34_regular hN, sup_comm] at this
    exact this
  · have hN : IsNormalValuation ν := ⟨hC, fun a => by rw [g72gk34_bool_cc hB a]⟩
    exact g72gk34_HJ hN (hB _)

end g72gk34
section g72gk34b
variable {L : Type*} [Order.Frame L]

lemma g72gk34_cmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsContinuousValuation nu) : IsContinuousValuation (fun a => φ (nu a)) :=
  ⟨⟨by simp only [h.1.1, hφ0], fun a b => by simp only; rw [← hadd, ← hadd, h.1.2 a b]⟩,
    fun s a hne hd hl => (hc.tendsto _).comp (h.2 s a hne hd hl)⟩

lemma g72gk34_nmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsNormalValuation nu) : IsNormalValuation (fun a => φ (nu a)) :=
  ⟨g72gk34_cmap φ hφ0 hadd hc h.1, fun a => by simp only [h.2]⟩

lemma g72gk34_rmap {nu : L → ℂ} (φ : ℂ → ℝ) (hφ0 : φ 0 = 0)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hc : Continuous φ)
    (h : IsJordanRegime nu) : IsJordanRegime (fun a => φ (nu a)) := by
  rcases h with ⟨hS, hN⟩ | ⟨hB, hC⟩
  · exact Or.inl ⟨hS, g72gk34_nmap φ hφ0 hadd hc hN⟩
  · exact Or.inr ⟨hB, g72gk34_cmap φ hφ0 hadd hc hC⟩

end g72gk34b


section g72gk34c
variable {L : Type*} [Order.Frame L]

lemma g72gk34_rho_mono {ν : L → ℝ} (h : IsNormalValuation ν) :
    Monotone (fun a => ν (positiveCarrier ν ⊓ a)) := by
  intro a a' hab
  have e := g72gk34_split h (x := positiveCarrier ν ⊓ a) (b := positiveCarrier ν ⊓ a')
    (inf_le_inf_left _ hab)
  have := g72gk34_carrier_pos h (positiveCarrier ν ⊓ a' ⊓ (positiveCarrier ν ⊓ a)ᶜ)
    (inf_le_left.trans inf_le_left)
  simp only
  linarith

lemma g72gk34_posnorm {ρ : L → ℝ} (h : IsNormalValuation ρ) (hnn : ∀ a, 0 ≤ ρ a)
    (hm : Monotone ρ) : IsPositiveNormalValuation (fun a => (ρ a).toNNReal) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp only [g72gk34_bot h, Real.toNNReal_zero]
  · intro a b
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (hnn _)]
    exact h.1.1.2 a b
  · intro a b hab
    exact Real.toNNReal_le_toNNReal (hm hab)
  · intro s a hne hd hl
    constructor
    · rintro _ ⟨b, hb, rfl⟩
      exact Real.toNNReal_le_toNNReal (hm (hl.1 hb))
    · intro u hu
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hnn a)]
      haveI : Nonempty s := hne.to_subtype
      haveI := g72gk34_isDir hd
      refine le_of_tendsto' (h.1.2 s a hne hd hl) (fun b => ?_)
      have := hu ⟨b.1, b.2, rfl⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hnn _)] at this
      exact this
  · intro a
    simp only [h.2]

lemma g72gk34_rho_norm {ν : L → ℝ} (h : IsNormalValuation ν) :
    IsPositiveNormalValuation (fun a => (ν (positiveCarrier ν ⊓ a)).toNNReal) :=
  g72gk34_posnorm (g72gk34_restrict h (g72gk34_regular h))
    (fun a => g72gk34_carrier_pos h _ inf_le_left) (g72gk34_rho_mono h)

lemma g72gk34_real_decomp {ν : L → ℝ} (h : IsNormalValuation ν) (a : L) :
    ν a = ((ν (positiveCarrier ν ⊓ a)).toNNReal : ℝ) -
      (((fun b => -ν b) (positiveCarrier (fun b => -ν b) ⊓ a)).toNNReal : ℝ) := by
  rw [Real.coe_toNNReal _ (g72gk34_carrier_pos h _ inf_le_left),
    Real.coe_toNNReal _ (g72gk34_carrier_pos (g72gk34_neg h) _ inf_le_left)]
  have := g72gk34_decomp h a
  simp only [negativeCarrier] at this
  linarith

lemma g72gk34_posgen {μ : L → ℝ≥0} (hμ : IsPositiveNormalValuation μ) :
    IsNormalValuation (fun a => ((μ a : ℝ) : ℂ)) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [hμ.1.1.1, NNReal.coe_zero, Complex.ofReal_zero]
  · intro a b
    have := congrArg (fun x : ℝ≥0 => ((x : ℝ) : ℂ)) (hμ.1.1.2 a b)
    simp only [NNReal.coe_add, Complex.ofReal_add] at this
    exact this
  · intro s a hne hd hl
    have hlub := hμ.1.2.2 s a hne hd hl
    rw [Set.image_eq_range] at hlub
    have hmono : Monotone (fun b : s => μ b.1) := fun x y hxy => hμ.1.2.1 hxy
    have := tendsto_atTop_isLUB hmono hlub
    exact ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp this
  · intro a
    simp only [hμ.2]

lemma g72gk34_zero : IsNormalValuation (0 : L → ℂ) :=
  ⟨⟨⟨rfl, fun a b => by simp⟩, fun s a _ _ _ => tendsto_const_nhds⟩, fun a => rfl⟩

lemma g72gk34_add {f g : L → ℂ} (hf : IsNormalValuation f) (hg : IsNormalValuation g) :
    IsNormalValuation (f + g) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [hf.1.1.1, hg.1.1.1]
  · intro a b
    have h1 := hf.1.1.2 a b
    have h2 := hg.1.1.2 a b
    simp only [Pi.add_apply]
    linear_combination h1 + h2
  · intro s a hne hd hl
    exact (hf.1.2 s a hne hd hl).add (hg.1.2 s a hne hd hl)
  · intro a
    simp only [Pi.add_apply, hf.2, hg.2]

lemma g72gk34_smul (c : ℂ) {f : L → ℂ} (hf : IsNormalValuation f) :
    IsNormalValuation (c • f) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [hf.1.1.1]
  · intro a b
    have h1 := hf.1.1.2 a b
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * h1
  · intro s a hne hd hl
    exact (hf.1.2 s a hne hd hl).const_mul c
  · intro a
    simp only [Pi.smul_apply, hf.2]

end g72gk34c

theorem solution (L : Type u) [Order.Frame L] (nu : L → ℂ) :
    IsNormalValuation nu ↔ nu ∈ Submodule.span ℂ
      {f : L → ℂ | ∃ mu : L → ℝ≥0, IsPositiveNormalValuation mu ∧
        f = fun a => ((mu a : ℝ) : ℂ)} := by
  constructor
  · intro h
    have hre := g72gk34_nmap Complex.re Complex.zero_re Complex.add_re Complex.continuous_re h
    have him := g72gk34_nmap Complex.im Complex.zero_im Complex.add_im Complex.continuous_im h
    set G := {f : L → ℂ | ∃ mu : L → ℝ≥0, IsPositiveNormalValuation mu ∧
        f = fun a => ((mu a : ℝ) : ℂ)}
    have mem : ∀ {ν : L → ℝ}, IsNormalValuation ν →
        (fun a => (((ν (positiveCarrier ν ⊓ a)).toNNReal : ℝ) : ℂ)) ∈ Submodule.span ℂ G :=
      fun hν => Submodule.subset_span ⟨_, g72gk34_rho_norm hν, rfl⟩
    have key : nu = ((fun a => ((((fun b => (nu b).re) (positiveCarrier (fun b => (nu b).re) ⊓ a)).toNNReal : ℝ) : ℂ)) -
        (fun a => ((((fun b => -(nu b).re) (positiveCarrier (fun b => -(nu b).re) ⊓ a)).toNNReal : ℝ) : ℂ))) +
        Complex.I • ((fun a => ((((fun b => (nu b).im) (positiveCarrier (fun b => (nu b).im) ⊓ a)).toNNReal : ℝ) : ℂ)) -
        (fun a => ((((fun b => -(nu b).im) (positiveCarrier (fun b => -(nu b).im) ⊓ a)).toNNReal : ℝ) : ℂ))) := by
      funext a
      have e1 := g72gk34_real_decomp hre a
      have e2 := g72gk34_real_decomp him a
      apply Complex.ext
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re,
          Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.sub_im, Complex.ofReal_im]
        simp only at e1
        linarith
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
          Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.sub_re, Complex.ofReal_re]
        simp only at e2
        linarith
    rw [key]
    exact Submodule.add_mem _ (Submodule.sub_mem _ (mem hre) (mem (g72gk34_neg hre)))
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ (mem him) (mem (g72gk34_neg him))))
  · intro hmem
    induction hmem using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨mu, hmu, rfl⟩ := hf
      exact g72gk34_posgen hmu
    | zero => exact g72gk34_zero
    | add f g _ _ hf hg => exact g72gk34_add hf hg
    | smul c f _ hf => exact g72gk34_smul c hf
