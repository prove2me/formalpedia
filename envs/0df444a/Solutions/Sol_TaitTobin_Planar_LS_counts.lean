-- Prove2me | solution 1 for TaitTobin.Planar.LS_counts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:00:26.409446+00:00
-- url     : https://prove2.me/submissions/7a06d87b-4fe6-4e46-8783-9a4c837cef3f

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_8
import Theorems.Thm_TaitTobin_Planar_planar_facts

set_option autoImplicit false

section LS

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-- planarity pulls back along an injective map of vertices -/
theorem sb_planar_comap {V W : Type} (G : SimpleGraph W) (g : V → W)
    (hg : Function.Injective g) (hG : IsPlanar G) : IsPlanar (G.comap g) := by
  obtain ⟨D⟩ := hG
  refine ⟨⟨fun v => D.vertex (g v), D.vertex_injective.comp hg,
    fun {v w} h => D.arc h, fun {v w} h => D.arc_injective h,
    fun {v w} h => D.arc_reverse h, ?_, ?_⟩⟩
  · intro v w h t x hx
    rcases D.arc_avoids_vertices h t (g x) hx with h1 | h1
    · exact Or.inl (hg h1)
    · exact Or.inr (hg h1)
  · intro v w x y h k s t hst
    rcases D.arcs_meet_only_at_endpoints h k s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨hg h1, hg h2⟩
    · exact Or.inr (Or.inl ⟨hg h1, hg h2⟩)
    · exact Or.inr (Or.inr h1)

theorem l9_between {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (hd : Disjoint X Y) :
    ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then (1:ℝ) else 0) ≤
      (TaitTobin.Outerplanar.eBetween G X Y : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have key : ((X ×ˢ Y).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      TaitTobin.Outerplanar.eBetween G X Y := by
    unfold TaitTobin.Outerplanar.eBetween
    refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
      simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq,
        SimpleGraph.mem_edgeSet]
      exact ⟨hp.2, p.1, hp.1.1, p.2, hp.1.2, rfl⟩
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.1.1) (Finset.disjoint_left.1 hd |>.mt (not_not.2 hq.1.2))
  exact_mod_cast key

theorem l9_within {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    ∑ i ∈ X, ∑ j ∈ X, (if G.Adj i j then (1:ℝ) else 0) ≤
      2 * (TaitTobin.Outerplanar.eIn G X : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have gen : ∀ E : Finset (Sym2 (Fin n)),
      (∀ e, e ∈ E ↔ (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ X)) →
      ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤ 2 * E.card := by
    intro E hE
    calc ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card
        ≤ (E ×ˢ (Finset.univ : Finset Bool)).card := by
          refine Finset.card_le_card_of_injOn (fun p => (s(p.1, p.2), decide (p.1 < p.2))) ?_ ?_
          · intro p hp
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
            simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hE, Finset.coe_univ,
              Set.mem_univ, and_true]
            refine ⟨hp.2, ?_⟩
            intro v hv
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact hp.1.1
            · exact hp.1.2
          · intro p hp q hq hpq
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
            have hpq' := Prod.mk.inj hpq
            rcases Sym2.eq_iff.1 hpq'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Prod.ext h1 h2
            · exfalso
              have hne : p.1 ≠ p.2 := hp.2.ne
              have h3 := hpq'.2
              rw [← h1, ← h2] at h3
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · simp [hlt, not_lt.2 hlt.le] at h3
              · simp [hgt, not_lt.2 hgt.le] at h3
      _ = 2 * E.card := by rw [Finset.card_product]; simp [mul_comm]
  have key : ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      2 * TaitTobin.Outerplanar.eIn G X := by
    unfold TaitTobin.Outerplanar.eIn
    exact gen _ (fun e => by simp)
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  exact this

theorem l9_eig {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (Z : Finset (Fin n)) :
    l * ∑ z ∈ Z, v z = ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u := by
  have hrow : ∀ i, ∑ j, (if G.Adj i j then v j else 0) = l * v i := by
    intro i
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, ite_mul] using this
  rw [Finset.mul_sum]
  calc ∑ z ∈ Z, l * v z = ∑ z ∈ Z, ∑ j, (if G.Adj z j then v j else 0) :=
        Finset.sum_congr rfl (fun z _ => (hrow z).symm)
    _ = ∑ j, ∑ z ∈ Z, (if G.Adj z j then v j else 0) := Finset.sum_comm
    _ = ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : G.Adj z j
        · have hz' : G.Adj j z := hz.symm
          simp [hz, hz']
        · have hz' : ¬ G.Adj j z := fun h' => hz h'.symm
          simp [hz, hz']


theorem ls_ein_le_sym2 {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    TaitTobin.Outerplanar.eIn G X ≤ X.sym2.card := by
  unfold TaitTobin.Outerplanar.eIn
  refine Finset.card_le_card ?_
  intro e he
  simp only [Finset.mem_filter] at he
  exact Finset.mem_sym2_iff.2 he.2

/-- edges inside any vertex set of a planar graph: at most `3 |X|` -/
theorem ls_ein_planar {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G) (X : Finset (Fin n)) :
    TaitTobin.Outerplanar.eIn G X ≤ 3 * X.card := by
  by_cases hm : 3 ≤ X.card
  · let g : Fin X.card → Fin n := fun i => X.orderEmbOfFin rfl i
    have hg : Function.Injective g := (X.orderEmbOfFin rfl).injective
    have hrange : ∀ y, y ∈ X ↔ ∃ i, g i = y := by
      intro y
      have := Finset.range_orderEmbOfFin X (rfl : X.card = X.card)
      constructor
      · intro hy
        have : y ∈ Set.range (X.orderEmbOfFin rfl) := by rw [this]; exact hy
        exact this
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem X rfl i
    have hplanar := sb_planar_comap G g hg hG
    obtain ⟨-, hE, -⟩ := TaitTobin.Planar.planar_facts hm (G.comap g) hplanar
    have key : TaitTobin.Outerplanar.eIn G X ≤ (G.comap g).edgeFinset.card := by
      unfold TaitTobin.Outerplanar.eIn
      calc _ ≤ ((G.comap g).edgeFinset.image (Sym2.map g)).card := by
              refine Finset.card_le_card ?_
              intro e he
              simp only [Finset.mem_filter] at he
              obtain ⟨he1, he2⟩ := he
              induction e using Sym2.ind with
              | h a b =>
                have ha : a ∈ X := he2 a (Sym2.mem_mk_left a b)
                have hb : b ∈ X := he2 b (Sym2.mem_mk_right a b)
                obtain ⟨i, hi⟩ := (hrange a).1 ha
                obtain ⟨j, hj⟩ := (hrange b).1 hb
                have hab : G.Adj a b := by simpa using he1
                refine Finset.mem_image.2 ⟨s(i, j), ?_, ?_⟩
                · simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
                    SimpleGraph.comap_adj]
                  rw [hi, hj]; exact hab
                · simp [Sym2.map_mk, hi, hj]
        _ ≤ _ := Finset.card_image_le
    have key2 : TaitTobin.Outerplanar.eIn G X ≤ 3 * X.card - 6 :=
      le_trans key (by convert hE; rfl)
    omega
  · have hc : X.card ≤ 2 := by omega
    have h1 := ls_ein_le_sym2 G X
    rw [Finset.card_sym2] at h1
    generalize X.card = m at *
    interval_cases m <;> simp [Nat.choose] at h1 ⊢ <;> omega

theorem ls_between {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (ε : ℝ) (v : Fin n → ℝ) :
    TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) ≤ 2 * n - 4 := by
  let c : Fin n → Fin 2 := fun a => if v a ≤ ε then 0 else 1
  let H : SimpleGraph (Fin n) :=
    { Adj := fun a b => G.Adj a b ∧ c a ≠ c b
      symm := ⟨fun a b h => ⟨h.1.symm, fun hh => h.2 hh.symm⟩⟩
      loopless := ⟨fun a h => h.2 rfl⟩ }
  have hle : H ≤ G := fun a b h => h.1
  have hcol : H.Colorable 2 := ⟨SimpleGraph.Coloring.mk c (fun {a b} h => h.2)⟩
  obtain ⟨-, -, h3⟩ := TaitTobin.Planar.planar_facts hn G hG
  have h4 := h3 H hle hcol
  unfold TaitTobin.Outerplanar.eBetween
  refine le_trans (Finset.card_le_card ?_) h4
  intro e he
  simp only [Finset.mem_filter] at he
  obtain ⟨he1, a, ha, b, hb, rfl⟩ := he
  have hab : G.Adj a b := by simpa using he1
  have hav : v a ≤ ε := by simpa [Sset] using ha
  have hbv : ε < v b := by simpa [Lset] using hb
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  refine ⟨hab, ?_⟩
  simp only [c, if_pos hav, if_neg (not_le.2 hbv)]
  decide

theorem ls_card_bound {n : ℕ} (ε : ℝ) (hε : 0 < ε) (G : SimpleGraph (Fin n)) (v : Fin n → ℝ)
    (l : ℝ) (hl : (G.adjMatrix ℝ).mulVec v = l • v)
    (hle : ∀ i, v i ≤ 1) (s : ℝ) (hs0 : 0 < s) (hss : s * s = 2 * (n:ℝ) - 4) (hlam : s < l)
    (hsε : 9 ≤ s * ε)
    (hSL : (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) ≤ 2 * (n:ℝ) - 4)
    (hLL : (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤ 3 * ((Lset ε v).card : ℝ)) :
    ((Lset ε v).card : ℝ) ≤ 3 * s / ε := by
  have hdisj : Disjoint (Sset ε v) (Lset ε v) := by
    unfold Sset Lset
    rw [Finset.disjoint_filter]
    intro z _ h1 h2; linarith
  set D : Fin n → ℝ := fun u => ∑ z ∈ Lset ε v, if G.Adj u z then (1:ℝ) else 0 with hD
  have hD0 : ∀ u, 0 ≤ D u := fun u =>
    Finset.sum_nonneg (fun z _ => by split_ifs <;> norm_num)
  have h1 := l9_eig G v l hl (Lset ε v)
  have h2 : ∑ u, D u * v u ≤ ∑ u, D u :=
    Finset.sum_le_sum (fun u _ => by nlinarith [hD0 u, hle u])
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
    (fun z => v z ≤ ε) D
  have hL' : (Finset.univ.filter (fun z => ¬ v z ≤ ε)) = Lset ε v := by
    ext z; simp [Lset]
  have hS' : (Finset.univ.filter (fun z => v z ≤ ε)) = Sset ε v := rfl
  rw [hL', hS'] at hsplit
  have hb := l9_between G (Sset ε v) (Lset ε v) hdisj
  have hw := l9_within G (Lset ε v)
  have h3 : ∑ u, D u ≤ (2 * (n:ℝ) - 4) + 2 * (3 * ((Lset ε v).card : ℝ)) := by
    rw [← hsplit]
    have e1 : ∑ u ∈ Sset ε v, D u ≤ 2 * (n:ℝ) - 4 := le_trans hb hSL
    have e2 : ∑ u ∈ Lset ε v, D u ≤ 2 * (3 * ((Lset ε v).card : ℝ)) := by
      have := hw
      linarith
    linarith
  set ℓ : ℝ := ((Lset ε v).card : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  have h4 : ε * ℓ ≤ ∑ z ∈ Lset ε v, v z := by
    have : ∑ z ∈ Lset ε v, ε ≤ ∑ z ∈ Lset ε v, v z :=
      Finset.sum_le_sum (fun z hz => by
        simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hz.le)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have hl0 : 0 < l := hs0.trans hlam
  have h5 : l * (ε * ℓ) ≤ (2 * (n:ℝ) - 4) + 2 * (3 * ℓ) := by
    have := mul_le_mul_of_nonneg_left h4 hl0.le
    linarith
  have h6 : s * (ε * ℓ) ≤ l * (ε * ℓ) :=
    mul_le_mul_of_nonneg_right hlam.le (mul_nonneg hε.le hℓ0)
  have h7 : s * (ε * ℓ) ≤ s * s + 6 * ℓ := by linarith
  have h8 : 0 ≤ (s * ε - 9) * ℓ := mul_nonneg (by linarith) hℓ0
  have h9 : s * (ε * ℓ) ≤ s * (3 * s) := by nlinarith
  have h10 : ε * ℓ ≤ 3 * s := le_of_mul_le_mul_left h9 hs0
  rw [le_div_iff₀ hε]
  linarith

end LS

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ((Lset ε v).card : ℝ) ≤ 3 * Real.sqrt (2 * (n : ℝ) - 4) / ε ∧
          TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) ≤ 2 * n - 4 ∧
          TaitTobin.Outerplanar.eIn G (Sset ε v) ≤ 3 * n - 6 ∧
          (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤ 9 * Real.sqrt (2 * (n : ℝ) - 4) / ε := by
  intro ε hε
  refine ⟨3 + ⌈81 / ε ^ 2⌉₊, fun n hn G hG v hv hpos hle x hx => ?_⟩
  have hn3 : 3 ≤ n := by omega
  have hnr : (3:ℝ) + 81 / ε ^ 2 ≤ n := by
    have h1 := Nat.le_ceil (81 / ε ^ 2)
    have h2 : ((3 + ⌈81 / ε ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn3r : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hpos2 : 0 < 2 * (n:ℝ) - 4 := by linarith
  set s := Real.sqrt (2 * (n : ℝ) - 4) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos2
  have hss : s * s = 2 * (n:ℝ) - 4 := Real.mul_self_sqrt hpos2.le
  have hlam := (TaitTobin.Planar.lemma_8 hn3 G hG).1
  have h81 : 0 < 81 / ε ^ 2 := by positivity
  have hs9 : 9 / ε ≤ s := by
    apply Real.le_sqrt_of_sq_le
    have : (9 / ε) ^ 2 = 81 / ε ^ 2 := by field_simp; norm_num
    rw [this]; linarith
  have hsε : 9 ≤ s * ε := by
    have := mul_le_mul_of_nonneg_right hs9 hε.le
    rwa [div_mul_cancel₀ _ hε.ne'] at this
  obtain ⟨-, hE, -⟩ := TaitTobin.Planar.planar_facts hn3 G hG.1
  have hSL := ls_between hn3 G hG.1 ε v
  have hSLr : (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) ≤ 2 * (n:ℝ) - 4 := by
    have : ((2 * n - 4 : ℕ) : ℝ) = 2 * (n:ℝ) - 4 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast hSL
  have hLL : (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤ 3 * ((Lset ε v).card : ℝ) := by
    exact_mod_cast ls_ein_planar G hG.1 (Lset ε v)
  have hcard := ls_card_bound ε hε G v _ hv hle s hs0 hss hlam hsε hSLr hLL
  refine ⟨hcard, hSL, ?_, ?_⟩
  · refine le_trans ?_ hE
    unfold TaitTobin.Outerplanar.eIn
    refine Finset.card_le_card ?_
    intro e he
    simp only [Finset.mem_filter] at he
    exact he.1
  · have : 3 * ((Lset ε v).card : ℝ) ≤ 9 * s / ε := by
      have h3 : 3 * (3 * s / ε) = 9 * s / ε := by field_simp; ring
      rw [← h3]; linarith
    linarith
