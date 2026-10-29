-- Prove2me | solution 1 for PlanarQueue.Planar.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T05:20:02.040585+00:00
-- url     : https://prove2.me/submissions/286311fd-3461-4f19-8517-cc511d6337e1

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting

set_option autoImplicit false

namespace PQLemma8Aux

theorem lex_lt {a b x y n : ℕ} (hx : x < n) (h : a < b) : a * n + x < b * n + y := by
  have h1 : (a + 1) * n ≤ b * n := Nat.mul_le_mul_right n h
  have h2 : (a + 1) * n = a * n + n := by ring
  omega

/-- Mirsky: a finite strict order whose chains have at most `m` elements is
colourable by `m` antichains (colour = height). -/
theorem mirsky {α : Type} [Fintype α] (r : α → α → Prop) [IsStrictOrder α r] (m : ℕ)
    (h : ∀ S : Finset α, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → r x y ∨ r y x) → S.card ≤ m) :
    ∃ c : α → Fin m, ∀ x y, r x y → c x ≠ c y := by
  classical
  letI : PartialOrder α := partialOrderOfSO r
  have hbound : ∀ x : α, Order.height x < m := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨p, -, hp⟩ := Order.exists_series_of_le_height x hx
    have hinj : Function.Injective p.toFun := p.strictMono.injective
    have hS := h (Finset.univ.image p.toFun) (by
      intro a ha b hb hab
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      rcases lt_trichotomy i j with hij | hij | hij
      · exact Or.inl (p.strictMono hij)
      · exact absurd (congrArg p.toFun hij) hab
      · exact Or.inr (p.strictMono hij))
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hp] at hS
    omega
  have key : ∀ x : α, (((Order.height x).toNat : ℕ) : ℕ∞) = Order.height x :=
    fun x => ENat.natCast_toNat (ne_top_of_lt (hbound x))
  refine ⟨fun x => ⟨(Order.height x).toNat, ?_⟩, ?_⟩
  · have hx := hbound x
    rw [← key x] at hx
    exact_mod_cast hx
  · intro x y hxy hc
    have h1 := Order.height_strictMono (show x < y from hxy) (lt_of_lt_of_le (hbound x) le_top)
    have h2 : (Order.height x).toNat = (Order.height y).toNat := congrArg Fin.val hc
    rw [← key x, ← key y, h2] at h1
    exact lt_irrefl _ h1

/-- Layer-major order: layer, then the `H`-position of the part, then a global index. -/
theorem exists_ord {V W : Type} [Fintype V] (L : V → ℕ) (φ : V → W) (pos : W → ℕ) :
    ∃ ord : V → ℕ, Function.Injective ord ∧ (∀ v w, L v < L w → ord v < ord w) ∧
      (∀ v w, ord v < ord w → L v ≤ L w) ∧
      (∀ v w, ord v < ord w → L v = L w → pos (φ v) ≤ pos (φ w)) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ v, pos (φ v) < M :=
    ⟨Finset.univ.sup (fun v => pos (φ v)) + 1, fun v =>
      Nat.lt_succ_of_le (Finset.le_sup (f := fun v => pos (φ v)) (Finset.mem_univ v))⟩
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have hB : ∀ v w, L v < L w → L v * M + pos (φ v) < L w * M + pos (φ w) :=
    fun v w h => lex_lt (hM v) h
  have hlt : ∀ v w, (L v * M + pos (φ v) < L w * M + pos (φ w)) →
      (L v * M + pos (φ v)) * Fintype.card V + (e v : ℕ) <
        (L w * M + pos (φ w)) * Fintype.card V + (e w : ℕ) :=
    fun v w h => lex_lt (e v).isLt h
  refine ⟨fun v => (L v * M + pos (φ v)) * Fintype.card V + (e v : ℕ), ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only at hvw
    rcases lt_trichotomy (L v * M + pos (φ v)) (L w * M + pos (φ w)) with h | h | h
    · exact absurd hvw (ne_of_lt (hlt v w h))
    · rw [h] at hvw
      have : (e v : ℕ) = e w := by omega
      exact e.injective (Fin.ext this)
    · exact absurd hvw (ne_of_gt (hlt w v h))
  · intro v w h
    exact hlt v w (hB v w h)
  · intro v w h
    by_contra hc
    push Not at hc
    exact absurd h (not_lt.2 (le_of_lt (hlt w v (hB w v hc))))
  · intro v w h hL
    by_contra hc
    push Not at hc
    have : L w * M + pos (φ w) < L v * M + pos (φ v) := by rw [hL]; omega
    exact absurd h (not_lt.2 (le_of_lt (hlt w v this)))

/-- Strict enclosure of edges given by their (lower, upper) endpoints. -/
abbrev Encl {α V : Type} (ord : V → ℕ) (lo hi : α → V) (x y : α) : Prop :=
  ord (lo x) < ord (lo y) ∧ ord (hi y) < ord (hi x)

open PlanarQueue.Planar in
theorem core {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k ℓ : ℕ)
    (pos : W → ℕ) (qH : H.edgeSet → Fin k) (hpos : Function.Injective pos)
    (hqH : ∀ e f : H.edgeSet, qH e = qH f → ¬ Nested pos e f)
    (L : V → ℕ) (hL : IsLayering G L) (φ : V → W) (hφ : IsHPartition G H φ)
    (hw : ∀ x : W, ∀ i : ℕ, (Finset.univ.filter fun v : V => φ v = x ∧ L v = i).card ≤ ℓ)
    (ord : V → ℕ) (hinj : Function.Injective ord)
    (hLo : ∀ v w, ord v < ord w → L v ≤ L w)
    (hpo : ∀ v w, ord v < ord w → L v = L w → pos (φ v) ≤ pos (φ w)) :
    OrderAdmits G (3 * ℓ * k + 3 * ℓ / 2) ord := by
  classical
  have hex : ∀ z : Sym2 V, z ∈ G.edgeSet → ∃ a b : V, z = s(a, b) ∧ ord a < ord b := by
    intro z
    refine Sym2.inductionOn z (fun a b => ?_)
    intro hz
    have hab : G.Adj a b := hz
    have hne : ord a ≠ ord b := fun h => G.ne_of_adj hab (hinj h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a, b, rfl, h⟩
    · exact ⟨b, a, Sym2.eq_swap, h⟩
  have hex2 : ∀ x : G.edgeSet, ∃ a b : V, (x : Sym2 V) = s(a, b) ∧ ord a < ord b :=
    fun x => hex x.1 x.2
  choose lo hi hlh hord using hex2
  have hadj : ∀ x, G.Adj (lo x) (hi x) := by
    intro x
    have := x.2
    rw [hlh x] at this
    exact this
  have huniq : ∀ (x : G.edgeSet) (a d : V), (x : Sym2 V) = s(a, d) → ord a < ord d → a = lo x ∧ d = hi x := by
    intro x a d h1 h2
    rw [hlh x, Sym2.eq_iff] at h1
    rcases h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact ⟨h3.symm, h4.symm⟩
    · have := hord x
      rw [h3, h4] at this
      omega
  have hstrict : IsStrictOrder G.edgeSet (Encl ord lo hi) :=
    { irrefl := fun x h => lt_irrefl _ h.1
      trans := fun x y z h1 h2 => ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩ }
  have hnest : ∀ x y : G.edgeSet, Nested ord x y → Encl ord lo hi x y ∨ Encl ord lo hi y x := by
    rintro x y ⟨a, b, c, d, hor, hab, hbc, hcd⟩
    rcases hor with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · obtain ⟨rfl, rfl⟩ := huniq x a d hx (by omega)
      obtain ⟨rfl, rfl⟩ := huniq y b c hy hbc
      exact Or.inl ⟨hab, hcd⟩
    · obtain ⟨rfl, rfl⟩ := huniq x b c hx hbc
      obtain ⟨rfl, rfl⟩ := huniq y a d hy (by omega)
      exact Or.inr ⟨hab, hcd⟩
  have hLx : ∀ x, L (lo x) ≤ L (hi x) ∧ L (hi x) ≤ L (lo x) + 1 :=
    fun x => ⟨hLo _ _ (hord x), (hL _ _ (hadj x)).2⟩
  -- a family mapped injectively into one part-layer piece has at most `ℓ` members
  have hpc : ∀ {β : Type} (S : Finset β) (f : β → V),
      (∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) → ∀ z i,
      (∀ x ∈ S, φ (f x) = z ∧ L (f x) = i) → S.card ≤ ℓ := by
    intro β S f hf z i hzi
    refine le_trans (Finset.card_le_card_of_injOn f ?_ ?_) (hw z i)
    · intro x hx
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hzi x (Finset.mem_coe.1 hx)⟩)
    · intro x hx y hy h
      exact hf x hx y hy h
  have hchain : ∀ S : Finset G.edgeSet,
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Encl ord lo hi x y ∨ Encl ord lo hi y x) →
      S.card ≤ 3 * ℓ * k + 3 * ℓ / 2 := by
    intro S hS
    have hloinj : ∀ x ∈ S, ∀ y ∈ S, lo x = lo y → x = y := by
      intro x hx y hy h
      by_contra hne
      rcases hS x hx y hy hne with h1 | h1
      · have := h1.1
        rw [h] at this
        exact lt_irrefl _ this
      · have := h1.1
        rw [h] at this
        exact lt_irrefl _ this
    have hhiinj : ∀ x ∈ S, ∀ y ∈ S, hi x = hi y → x = y := by
      intro x hx y hy h
      by_contra hne
      rcases hS x hx y hy hne with h1 | h1
      · have := h1.2
        rw [h] at this
        exact lt_irrefl _ this
      · have := h1.2
        rw [h] at this
        exact lt_irrefl _ this
    have hlohi : ∀ x ∈ S, ∀ y ∈ S, lo x ≠ hi y := by
      intro x hx y hy h
      by_cases hxy : x = y
      · subst hxy
        have := hord x
        rw [h] at this
        exact lt_irrefl _ this
      rcases hS x hx y hy hxy with h1 | h1
      · have := lt_trans h1.1 (hord y)
        rw [h] at this
        exact lt_irrefl _ this
      · have := lt_trans (hord x) h1.2
        rw [h] at this
        exact lt_irrefl _ this
    -- intra-part edges inside one layer: at most ℓ/2 pairwise nested
    set S0 := S.filter (fun x => φ (lo x) = φ (hi x)) with hS0
    set SA := S0.filter (fun x => L (lo x) = L (hi x)) with hSA
    set SB := S0.filter (fun x => ¬ L (lo x) = L (hi x)) with hSB
    set SI := S.filter (fun x => ¬ φ (lo x) = φ (hi x)) with hSI
    have hA : 2 * SA.card ≤ ℓ := by
      rcases SA.eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
      · rw [h0]; simp
      have hmemA : ∀ x ∈ SA, x ∈ S ∧ φ (lo x) = φ (hi x) ∧ L (lo x) = L (hi x) := by
        intro x hx
        rw [hSA, hS0, Finset.mem_filter, Finset.mem_filter] at hx
        exact ⟨hx.1.1, hx.1.2, hx.2⟩
      have hpairA : ∀ x ∈ SA, ∀ y ∈ SA, Encl ord lo hi x y →
          φ (lo x) = φ (lo y) ∧ L (lo x) = L (lo y) := by
        intro x hx y hy hxy
        obtain ⟨-, hx1, hx2⟩ := hmemA x hx
        obtain ⟨-, hy1, hy2⟩ := hmemA y hy
        have e1 := hLo _ _ hxy.1
        have e2 := hLo _ _ (hord y)
        have e3 := hLo _ _ hxy.2
        have hl1 : L (lo x) = L (lo y) := by omega
        have hl2 : L (hi y) = L (hi x) := by omega
        have p1 := hpo _ _ hxy.1 hl1
        have p2 := hpo _ _ (hord y) hy2
        have p3 := hpo _ _ hxy.2 hl2
        have : pos (φ (lo x)) = pos (φ (lo y)) := by
          rw [hx1] at p1 ⊢
          omega
        exact ⟨hpos this, hl1⟩
      have hall : ∀ x ∈ SA, φ (lo x) = φ (lo x0) ∧ L (lo x) = L (lo x0) := by
        intro x hx
        by_cases hxe : x = x0
        · subst hxe
          exact ⟨rfl, rfl⟩
        rcases hS x (hmemA x hx).1 x0 (hmemA x0 hx0).1 hxe with h | h
        · exact hpairA x hx x0 hx0 h
        · exact (hpairA x0 hx0 x hx h).imp Eq.symm Eq.symm
      have h2 := hpc (SA ×ˢ (Finset.univ : Finset Bool))
        (fun p => if p.2 then hi p.1 else lo p.1) (by
          rintro ⟨x, bx⟩ hx ⟨y, bY⟩ hy h
          rw [Finset.mem_product] at hx hy
          have hxS := (hmemA x hx.1).1
          have hyS := (hmemA y hy.1).1
          cases bx <;> cases bY <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
          · rw [hloinj x hxS y hyS h]
          · exact absurd h (hlohi x hxS y hyS)
          · exact absurd h.symm (hlohi y hyS x hxS)
          · rw [hhiinj x hxS y hyS h])
        (φ (lo x0)) (L (lo x0)) (by
          rintro ⟨x, bx⟩ hx
          rw [Finset.mem_product] at hx
          obtain ⟨-, hx1, hx2⟩ := hmemA x hx.1
          have := hall x hx.1
          cases bx
          · simpa using this
          · simp only [↓reduceIte]
            rw [← hx1, ← hx2]
            exact this)
      rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h2
      omega
    have hB : SB.card ≤ ℓ := by
      rcases SB.eq_empty_or_nonempty with h0 | ⟨x0, hx0⟩
      · rw [h0]; simp
      have hmemB : ∀ x ∈ SB, x ∈ S ∧ φ (lo x) = φ (hi x) ∧ ¬ L (lo x) = L (hi x) := by
        intro x hx
        rw [hSB, hS0, Finset.mem_filter, Finset.mem_filter] at hx
        exact ⟨hx.1.1, hx.1.2, hx.2⟩
      have hpairB : ∀ x ∈ SB, ∀ y ∈ SB, Encl ord lo hi x y →
          φ (lo x) = φ (lo y) ∧ L (lo x) = L (lo y) := by
        intro x hx y hy hxy
        obtain ⟨-, hx1, hx2⟩ := hmemB x hx
        obtain ⟨-, hy1, hy2⟩ := hmemB y hy
        have e1 := hLo _ _ hxy.1
        have e3 := hLo _ _ hxy.2
        have f1 := hLx x
        have f2 := hLx y
        have hl1 : L (lo x) = L (lo y) := by omega
        have hl2 : L (hi y) = L (hi x) := by omega
        have p1 := hpo _ _ hxy.1 hl1
        have p3 := hpo _ _ hxy.2 hl2
        have : pos (φ (lo x)) = pos (φ (lo y)) := by
          rw [← hx1, ← hy1] at p3
          omega
        exact ⟨hpos this, hl1⟩
      refine hpc SB lo (fun x hx y hy h => hloinj x (hmemB x hx).1 y (hmemB y hy).1 h)
        (φ (lo x0)) (L (lo x0)) ?_
      intro x hx
      by_cases hxe : x = x0
      · subst hxe
        exact ⟨rfl, rfl⟩
      rcases hS x (hmemB x hx).1 x0 (hmemB x0 hx0).1 hxe with h | h
      · exact hpairB x hx x0 hx0 h
      · exact (hpairB x0 hx0 x hx h).imp Eq.symm Eq.symm
    -- inter-part edges: split by kind (same layer / up-right / up-left) and the H-queue
    obtain ⟨kd, hkd⟩ : ∃ kd : G.edgeSet → ℕ, ∀ x, kd x =
        if L (lo x) = L (hi x) then 0 else if pos (φ (lo x)) < pos (φ (hi x)) then 1 else 2 :=
      ⟨_, fun x => rfl⟩
    obtain ⟨jq, hjq⟩ : ∃ jq : G.edgeSet → ℕ, ∀ x (h : H.Adj (φ (lo x)) (φ (hi x))),
        jq x = (qH ⟨s(φ (lo x), φ (hi x)), (SimpleGraph.mem_edgeSet H).2 h⟩ : ℕ) :=
      ⟨fun x => if h : H.Adj (φ (lo x)) (φ (hi x)) then
          (qH ⟨s(φ (lo x), φ (hi x)), (SimpleGraph.mem_edgeSet H).2 h⟩ : ℕ) else 0,
        fun x h => dif_pos h⟩
    have hmemI : ∀ x ∈ SI, x ∈ S ∧ φ (lo x) ≠ φ (hi x) := by
      intro x hx
      rw [hSI, Finset.mem_filter] at hx
      exact hx
    have hadjH : ∀ x ∈ SI, H.Adj (φ (lo x)) (φ (hi x)) :=
      fun x hx => (hφ _ _ (hadj x)).resolve_left (hmemI x hx).2
    have hpairI : ∀ x ∈ SI, ∀ y ∈ SI, kd x = kd y → jq x = jq y → Encl ord lo hi x y →
        L (lo x) = L (lo y) ∧ L (hi x) = L (hi y) ∧ pos (φ (lo x)) ≤ pos (φ (lo y)) ∧
          pos (φ (hi y)) ≤ pos (φ (hi x)) ∧
          (pos (φ (lo x)) = pos (φ (lo y)) ∨ pos (φ (hi x)) = pos (φ (hi y))) := by
      intro x hx y hy hk hj hxy
      have hxn := (hmemI x hx).2
      have hyn := (hmemI y hy).2
      have hHx := hadjH x hx
      have hHy := hadjH y hy
      have f1 := hLx x
      have f2 := hLx y
      have e1 := hLo _ _ hxy.1
      have e2 := hLo _ _ (hord y)
      have e3 := hLo _ _ hxy.2
      have hLeq : L (lo x) = L (lo y) ∧ L (hi x) = L (hi y) := by
        rw [hkd x, hkd y] at hk
        split_ifs at hk <;> omega
      have p1 := hpo _ _ hxy.1 hLeq.1
      have p3 := hpo _ _ hxy.2 hLeq.2.symm
      refine ⟨hLeq.1, hLeq.2, p1, p3, ?_⟩
      by_contra hne
      push Not at hne
      have hq : qH ⟨s(φ (lo x), φ (hi x)), (SimpleGraph.mem_edgeSet H).2 hHx⟩ =
          qH ⟨s(φ (lo y), φ (hi y)), (SimpleGraph.mem_edgeSet H).2 hHy⟩ :=
        Fin.ext (by rw [← hjq x hHx, ← hjq y hHy]; exact hj)
      refine hqH _ _ hq ?_
      have hpx : pos (φ (lo x)) ≠ pos (φ (hi x)) := fun h => hxn (hpos h)
      have hpy : pos (φ (lo y)) ≠ pos (φ (hi y)) := fun h => hyn (hpos h)
      unfold Nested
      by_cases hor : pos (φ (lo y)) < pos (φ (hi y))
      · exact ⟨φ (lo x), φ (lo y), φ (hi y), φ (hi x), Or.inl ⟨rfl, rfl⟩, by omega, hor, by omega⟩
      · have hky : kd y = 2 := by
          rw [hkd y]
          split_ifs with h1 h2
          all_goals first
            | rfl
            | exact absurd (hpo _ _ (hord y) h1) (by omega)
            | exact absurd h2 hor
        have hkx : kd x = 2 := hk.trans hky
        have hx2 : pos (φ (hi x)) < pos (φ (lo x)) := by
          rw [hkd x] at hkx
          split_ifs at hkx with h1 h2 <;> omega
        exact ⟨φ (hi y), φ (hi x), φ (lo x), φ (lo y), Or.inr ⟨Sym2.eq_swap, Sym2.eq_swap⟩,
          by omega, hx2, by omega⟩
    have hF : ∀ t : ℕ × ℕ, (SI.filter (fun x => (kd x, jq x) = t)).card ≤ ℓ := by
      intro t
      set F := SI.filter (fun x => (kd x, jq x) = t) with hFdef
      rcases F.eq_empty_or_nonempty with h0 | hne
      · rw [h0]; simp
      have hmemF : ∀ x ∈ F, x ∈ SI ∧ (kd x, jq x) = t := fun x hx => Finset.mem_filter.1 hx
      have hFS : ∀ x ∈ F, x ∈ S := fun x hx => (hmemI x (hmemF x hx).1).1
      have hsame : ∀ x ∈ F, ∀ y ∈ F, kd x = kd y ∧ jq x = jq y := by
        intro x hx y hy
        have h1 := (hmemF x hx).2
        have h2 := (hmemF y hy).2
        rw [← h2] at h1
        exact Prod.mk.inj h1
      obtain ⟨xa, hxa, hmin⟩ := F.exists_min_image (fun x => ord (lo x)) hne
      obtain ⟨xb, hxb, hmax⟩ := F.exists_max_image (fun x => ord (lo x)) hne
      have hW : ∀ x ∈ F, ∀ y ∈ F, (x = y ∨ Encl ord lo hi x y) →
          L (lo x) = L (lo y) ∧ L (hi x) = L (hi y) ∧ pos (φ (lo x)) ≤ pos (φ (lo y)) ∧
            pos (φ (hi y)) ≤ pos (φ (hi x)) ∧
            (pos (φ (lo x)) = pos (φ (lo y)) ∨ pos (φ (hi x)) = pos (φ (hi y))) := by
        intro x hx y hy h
        rcases h with rfl | h
        · exact ⟨rfl, rfl, le_rfl, le_rfl, Or.inl rfl⟩
        · exact hpairI x (hmemF x hx).1 y (hmemF y hy).1 (hsame x hx y hy).1
            (hsame x hx y hy).2 h
      have hfromA : ∀ y ∈ F, xa = y ∨ Encl ord lo hi xa y := by
        intro y hy
        by_cases h : xa = y
        · exact Or.inl h
        right
        rcases hS xa (hFS xa hxa) y (hFS y hy) h with h1 | h1
        · exact h1
        · exact absurd (hmin y hy) (not_le.2 h1.1)
      have htoB : ∀ y ∈ F, y = xb ∨ Encl ord lo hi y xb := by
        intro y hy
        by_cases h : y = xb
        · exact Or.inl h
        right
        rcases hS y (hFS y hy) xb (hFS xb hxb) h with h1 | h1
        · exact h1
        · exact absurd (hmax y hy) (not_le.2 h1.1)
      have hab := hW xa hxa xb hxb (htoB xa hxa)
      rcases hab.2.2.2.2 with hl | hr
      · refine hpc F lo (fun x hx y hy h => hloinj x (hFS x hx) y (hFS y hy) h)
          (φ (lo xa)) (L (lo xa)) ?_
        intro y hy
        have h1 := hW xa hxa y hy (hfromA y hy)
        have h2 := hW y hy xb hxb (htoB y hy)
        refine ⟨hpos ?_, h1.1.symm⟩
        omega
      · refine hpc F hi (fun x hx y hy h => hhiinj x (hFS x hx) y (hFS y hy) h)
          (φ (hi xa)) (L (hi xa)) ?_
        intro y hy
        have h1 := hW xa hxa y hy (hfromA y hy)
        have h2 := hW y hy xb hxb (htoB y hy)
        refine ⟨hpos ?_, h1.2.1.symm⟩
        omega
    have hSIc : SI.card ≤ 3 * k * ℓ := by
      have hmaps : ∀ x ∈ SI, (kd x, jq x) ∈ (Finset.range 3 ×ˢ Finset.range k) := by
        intro x hx
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · rw [hkd x]
          split_ifs <;> omega
        · rw [hjq x (hadjH x hx)]
          exact Fin.isLt _
      rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (kd x, jq x))
        (t := Finset.range 3 ×ˢ Finset.range k) (fun x hx => hmaps x hx)]
      calc _ ≤ ∑ _t ∈ Finset.range 3 ×ˢ Finset.range k, ℓ :=
            Finset.sum_le_sum (fun t _ => hF t)
        _ = 3 * k * ℓ := by
            rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range,
              smul_eq_mul]
    have hc1 := Finset.card_filter_add_card_filter_not (s := S) (fun x => φ (lo x) = φ (hi x))
    have hc2 := Finset.card_filter_add_card_filter_not (s := S0) (fun x => L (lo x) = L (hi x))
    rw [← hS0] at hc1
    rw [← hSA, ← hSB] at hc2
    rw [← hSI] at hc1
    have h3 : 3 * k * ℓ = 3 * ℓ * k := by ring
    rw [h3] at hSIc
    generalize 3 * ℓ * k = T at *
    omega
  obtain ⟨c, hc⟩ := mirsky (Encl ord lo hi) _ hchain
  exact ⟨c, hinj, fun x y hq hn =>
    (hnest x y hn).elim (fun h => hc x y h hq) (fun h => hc y x h hq.symm)⟩

end PQLemma8Aux

open PlanarQueue.Planar in
theorem solution {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (k ℓ : ℕ)
    (hH : HasQueueLayout H k)
    (L : V → ℕ) (hL : IsLayering G L)
    (φ : V → W) (hφ : IsHPartition G H φ)
    (hw : ∀ x : W, ∀ i : ℕ,
      (Finset.univ.filter fun v : V => φ v = x ∧ L v = i).card ≤ ℓ) :
    ∃ ord : V → ℕ,
      OrderAdmits G (3 * ℓ * k + 3 * ℓ / 2) ord ∧
        ∀ v w : V, L v < L w → ord v < ord w := by
  obtain ⟨pos, qH, hposinj, hqH⟩ := hH
  obtain ⟨ord, hinj, hmono, hLo, hpo⟩ := PQLemma8Aux.exists_ord L φ pos
  exact ⟨ord, PQLemma8Aux.core G H k ℓ pos qH hposinj hqH L hL φ hφ hw ord hinj hLo hpo, hmono⟩
