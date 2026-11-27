-- Prove2me | solution 1 for PathsTreesFlowers.Duality.Supplement.flowered_tree_4_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:56.434613+00:00
-- url     : https://prove2.me/submissions/967f63e5-e0db-48f0-9e5e-7310fcc80fd1

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees

open PathsTreesFlowers
open PathsTreesFlowers.Duality
open PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V) (e : E) (u v : V)
    (hF : IsFloweredTree G M J r e u v) :
    ∃ bv be b sv se, IsRootPathFlower G M J r e u v bv be b sv se := by
      have idxV : ∀ (l : List V) (a b : ℕ) (ha : a < l.length) (hb : b < l.length), a = b → l[a]'ha = l[b]'hb := by
        intro l a b ha hb h; subst h; rfl
      have idxE : ∀ (l : List E) (a b : ℕ) (ha : a < l.length) (hb : b < l.length), a = b → l[a]'ha = l[b]'hb := by
        intro l a b ha hb h; subst h; rfl
      -- edges of the closed walk
      have genE : ∀ (e : E) (Ae Be : List E) (p q : ℕ), Ae.length = p → Be.length = q →
          (∀ k (h : k < p) (hA : k < Ae.length) (hb : k < (Ae ++ e :: Be.reverse).length), (Ae ++ e :: Be.reverse)[k]'hb = Ae[k]'hA) ∧
          (∀ (hb : p < (Ae ++ e :: Be.reverse).length), (Ae ++ e :: Be.reverse)[p]'hb = e) ∧
          (∀ k c (h : k = p + 1 + c) (hB : q - 1 - c < Be.length) (hb : k < (Ae ++ e :: Be.reverse).length), (Ae ++ e :: Be.reverse)[k]'hb = Be[q - 1 - c]'hB) := by
        intro e Ae Be p q hA hB
        refine ⟨fun k h hA' hb => List.getElem_append_left hA', fun hb => ?_, fun k c h hB' hb => ?_⟩
        · rw [List.getElem_append_right (le_of_eq hA)]
          rw [List.getElem_cons, dif_pos (by rw [hA]; exact Nat.sub_self p)]
        · rw [List.getElem_append_right (by rw [hA, h]; omega), List.getElem_cons, dif_neg (by rw [hA, h]; omega),
            List.getElem_reverse]
          exact idxE Be _ _ _ _ (by rw [hB, hA, h]; omega)
      have genV : ∀ (A B : List V) (p q : ℕ), A.length = p + 1 → B.length = q + 1 →
          (∀ k (h : k ≤ p) (hA : k < A.length) (hb : k < (A ++ (B.drop 1).reverse).length), (A ++ (B.drop 1).reverse)[k]'hb = A[k]'hA) ∧
          (∀ k c (h : k = p + 1 + c) (hc : c < q) (hB : q - c < B.length) (hb : k < (A ++ (B.drop 1).reverse).length), (A ++ (B.drop 1).reverse)[k]'hb = B[q - c]'hB) := by
        intro A B p q hA hB
        refine ⟨fun k h hA' hb => List.getElem_append_left hA', fun k c h hc hB' hb => ?_⟩
        rw [List.getElem_append_right (by rw [hA, h]; omega), List.getElem_reverse, List.getElem_drop]
        exact idxV B _ _ _ _ (by rw [List.length_drop, hB, hA, h]; omega)
      have circ : ∀ (e : E) (A B : List V) (Ae Be : List E) (p q L : ℕ) (bv : List V) (be : List E), bv = A ++ (B.drop 1).reverse → be = Ae ++ e :: Be.reverse → A.length = p + 1 → Ae.length = p →
          B.length = q + 1 → Be.length = q → L = p + q + 1 →
          (∀ k (h1 : k + 1 < A.length) (h0 : k < A.length) (h2 : k < Ae.length), G.ends (Ae[k]'h2) = s(A[k]'h0, A[k+1]'h1)) →
          (∀ k (h1 : k + 1 < B.length) (h0 : k < B.length) (h2 : k < Be.length), G.ends (Be[k]'h2) = s(B[k]'h0, B[k+1]'h1)) →
          (∀ (h1 : p < A.length) (h2 : q < B.length), G.ends e = s(A[p]'h1, B[q]'h2)) →
          (∀ (h1 : 0 < A.length) (h2 : 0 < B.length), A[0]'h1 = B[0]'h2) →
          ∀ k (h : k < L) (hb : k < be.length) (hv : k < bv.length)
            (hv' : (k+1) % L < bv.length),
            G.ends (be[k]'hb) =
              s(bv[k]'hv, bv[(k+1) % L]'hv') := by
        rintro e A B Ae Be p q L _ _ rfl rfl hA hAe hB hBe hL hAends hBends he h0 k hk hb hv hv'
        obtain ⟨E1, E2, E3⟩ := genE e Ae Be p q hAe hBe
        obtain ⟨V1, V2⟩ := genV A B p q hA hB
        have hv0 : ∀ (h : k + 1 < L) (hx : k + 1 < (A ++ (B.drop 1).reverse).length), (A ++ (B.drop 1).reverse)[(k+1) % L]'hv' =
            (A ++ (B.drop 1).reverse)[k+1]'hx := fun h hx => idxV _ _ _ _ _ (Nat.mod_eq_of_lt h)
        have hv1 : ∀ (h : k + 1 = L) (hx : 0 < (A ++ (B.drop 1).reverse).length) , (A ++ (B.drop 1).reverse)[(k+1) % L]'hv' =
            (A ++ (B.drop 1).reverse)[0]'hx := fun h hx => idxV _ _ _ _ _ (by rw [h, Nat.mod_self])
        have hlen : (A ++ (B.drop 1).reverse).length = L := by
          rw [List.length_append, List.length_reverse, List.length_drop, hA, hB, hL]; omega
        rcases Nat.lt_trichotomy k p with hc | hc | hc
        · rw [hv0 (by omega) (by omega), E1 k hc (by omega) hb, V1 k (by omega) (by omega) hv, V1 (k+1) (by omega) (by omega) _]
          exact hAends k (by omega) _ _
        · subst hc
          rw [E2 hb, he (by omega) (by omega), V1 k le_rfl (by omega) hv]
          rcases Nat.eq_zero_or_pos q with hq | hq
          · rw [hv1 (by omega) (by omega), V1 0 (by omega) (by omega) _, h0 (by omega) (by omega)]
            rw [idxV B q 0 _ _ hq]
          · rw [hv0 (by omega) (by omega), V2 (k+1) 0 rfl hq (by omega) _]
            rw [idxV B q (q-0) _ _ rfl]
        · obtain ⟨c, rfl⟩ : ∃ c, k = p + 1 + c := ⟨k - (p+1), by omega⟩
          obtain ⟨d, rfl⟩ : ∃ d, q = c + 1 + d := ⟨q - (c+1), by omega⟩
          rw [E3 _ c rfl (by omega) hb, V2 _ c rfl (by omega) (by omega) hv, hBends _ (by omega) (by omega) _, Sym2.eq_swap]
          rw [idxV B (c + 1 + d - 1 - c + 1) (c + 1 + d - c) _ _ (by omega)]
          rcases Nat.eq_zero_or_pos d with hd | hd
          · rw [hv1 (by omega) (by omega), V1 0 (by omega) (by omega) _, h0 (by omega) (by omega)]
            rw [idxV B (c + 1 + d - 1 - c) 0 _ _ (by omega)]
          · rw [hv0 (by omega) (by omega), V2 (p+1+c+1) (c+1) (by omega) (by omega) (by omega) _]
            rw [idxV B (c + 1 + d - 1 - c) (c + 1 + d - (c + 1)) _ _ (by omega)]
      have circM : ∀ (e : E) (Ae Be : List E) (p q : ℕ) (be : List E), be = Ae ++ e :: Be.reverse → Ae.length = p → Be.length = q → p % 2 = 0 → q % 2 = 0 → e ∉ M →
          (∀ k (h : k < Ae.length), Ae[k]'h ∈ M ↔ k % 2 = 1) → (∀ k (h : k < Be.length), Be[k]'h ∈ M ↔ k % 2 = 1) →
          ∀ k (hb : k < be.length), be[k]'hb ∈ M ↔ k % 2 = 1 := by
        rintro e Ae Be p q _ rfl hA hB hp hq he h1 h2 k hb
        obtain ⟨E1, E2, E3⟩ := genE e Ae Be p q hA hB
        have hlen : k < p + (q + 1) := by
          rw [List.length_append, List.length_cons, List.length_reverse, hA, hB] at hb; exact hb
        rcases Nat.lt_trichotomy k p with hc | hc | hc
        · rw [E1 k hc (by omega) hb]; exact h1 k _
        · subst hc
          rw [E2 hb]; exact ⟨fun h => absurd h he, fun h => by omega⟩
        · rw [E3 k (k - (p+1)) (by omega) (by omega) hb, h2]; omega
      have glue : ∀ (C D : List V) (Ce De : List E) (i q : ℕ), C.length = i + 1 → Ce.length = i → D.length = q + 1 → De.length = q →
          (∀ k (h1 : k + 1 < C.length) (h0 : k < C.length) (h2 : k < Ce.length), G.ends (Ce[k]'h2) = s(C[k]'h0, C[k+1]'h1)) →
          (∀ k (h1 : k + 1 < D.length) (h0 : k < D.length) (h2 : k < De.length), G.ends (De[k]'h2) = s(D[k]'h0, D[k+1]'h1)) →
          (∀ (h1 : i < C.length) (h2 : 0 < D.length), C[i]'h1 = D[0]'h2) →
          (∀ k (h1 : k + 1 < (C ++ D.drop 1).length) (h0 : k < (C ++ D.drop 1).length) (h2 : k < (Ce ++ De).length),
            G.ends ((Ce ++ De)[k]'h2) = s((C ++ D.drop 1)[k]'h0, (C ++ D.drop 1)[k+1]'h1)) ∧
          (C ++ D.drop 1).getLast? = D.getLast? := by
        intro C D Ce De i q hC hCe hD hDe hCends hDends h0
        have V2 : ∀ k c (h : k = i + c) (hk : k < (C ++ D.drop 1).length) (hc : c < D.length), (C ++ D.drop 1)[k]'hk = D[c]'hc := by
          intro k c h hk hc
          rcases Nat.eq_zero_or_pos c with hc0 | hc0
          · subst hc0
            rw [List.getElem_append_left (by omega), ← h0 (by omega) (by omega)]
            exact idxV C _ _ _ _ (by omega)
          · rw [List.getElem_append_right (by omega), List.getElem_drop]
            exact idxV D _ _ _ _ (by omega)
        have hlen : (C ++ D.drop 1).length = i + 1 + q := by
          rw [List.length_append, List.length_drop, hC, hD]; omega
        constructor
        · intro k h1 h2 h3
          rcases Nat.lt_or_ge k i with hk | hk
          · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
            exact hCends k _ _ _
          · obtain ⟨c, rfl⟩ : ∃ c, k = i + c := ⟨k - i, by omega⟩
            rw [List.getElem_append_right (by omega), V2 _ c rfl _ (by omega), V2 (i+c+1) (c+1) (by omega) _ (by omega), ← hDends c (by omega) (by omega) (by omega)]
            exact congrArg G.ends (idxE De _ _ _ _ (by omega))
        · rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
            V2 _ q (by omega) _ (by omega)]
          exact congrArg some (idxV D _ _ _ _ (by omega))
      have fin : ∀ (e : E) (bv : List V) (be : List E) (L : ℕ) (hL3' : 3 ≤ L) (hLodd : L % 2 = 1) (hbvlen : bv.length = L)
          (hbelen : be.length = L) (hbvnd : bv.Nodup)
          (hcends : ∀ k (h : k < L), G.ends (be[k]'(by omega)) =
            s(bv[k]'(by omega), bv[(k+1) % L]'(by rw [hbvlen]; exact Nat.mod_lt _ (by omega))))
          (hbeM : ∀ k (h : k < be.length), be[k]'h ∈ M ↔ k % 2 = 1),
          be.Nodup ∧ IsCircuit G bv be ∧ IsMaxMatchingOn G be.toFinset (M ∩ be.toFinset) ∧
            ∀ f ∈ M ∩ be.toFinset, ∀ h0 : 0 < bv.length, bv[0]'h0 ∉ G.ends f := by
        clear glue circ circM genV genE hF
        intro e bv be L hL3' hLodd hbvlen hbelen hbvnd hcends hbeM
        have hmodL : ∀ x, x < L → (x+1) % L = if x + 1 < L then x+1 else 0 := by
          intro x hx
          split_ifs with h
          · exact Nat.mod_eq_of_lt h
          · rw [show x + 1 = L by omega, Nat.mod_self]
        have hbend : be.Nodup := by
          rw [List.nodup_iff_injective_get]
          intro ⟨a, ha⟩ ⟨b, hb⟩ hab
          simp only [List.get_eq_getElem] at hab
          simp only [Fin.mk.injEq]
          have ha' : a < L := by omega
          have hb' : b < L := by omega
          have e1 : s(bv[a]'(by omega), bv[(a+1) % L]'(by rw [hbvlen]; exact Nat.mod_lt _ (by omega))) =
              s(bv[b]'(by omega), bv[(b+1) % L]'(by rw [hbvlen]; exact Nat.mod_lt _ (by omega))) := by
            rw [← hcends a ha', ← hcends b hb']; exact congrArg G.ends hab
          have hma := hmodL a ha'
          have hmb := hmodL b hb'
          rcases Sym2.eq_iff.mp e1 with ⟨x, y⟩ | ⟨x, y⟩
          · exact hbvnd.getElem_inj_iff.mp x
          · have hx := hbvnd.getElem_inj_iff.mp x
            have hy := hbvnd.getElem_inj_iff.mp y
            rw [hma] at hy; rw [hmb] at hx
            split_ifs at hx hy <;> omega
        have hcirc : IsCircuit G bv be := by
          refine ⟨hbvnd, hbend, by omega, by omega, ?_⟩
          apply List.ext_getElem
          · simp; omega
          · intro k h1 h2
            simp only [List.getElem_map, List.getElem_zipWith, List.getElem_rotate]
            rw [hcends k (by simp at h1; omega)]
            simp [hbvlen]
        have hmaxB : IsMaxMatchingOn G be.toFinset (M ∩ be.toFinset) := by
          classical
          refine ⟨Finset.inter_subset_right, fun f hf g hg hfg x hx1 hx2 =>
            hM f (Finset.mem_inter.mp hf).1 g (Finset.mem_inter.mp hg).1 hfg x hx1 hx2, ?_⟩
          intro M' hM'B hM'm
          have hup : M'.card ≤ (L - 1) / 2 := by
            let S := (Finset.range L).filter (fun k => ∃ h : k < be.length, (be[k]'(by first | assumption | omega)) ∈ M')
            have h1 : M'.card ≤ S.card := by
              have : M' ⊆ S.image (fun k => be.getD k e) := by
                intro f hf
                obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp (hM'B hf))
                exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
                  ⟨Finset.mem_range.mpr (by omega), hk, hf⟩, List.getD_eq_getElem _ _ hk⟩
              exact (Finset.card_le_card this).trans Finset.card_image_le
            have h2 : (S.image (fun k => (k+1) % L)).card = S.card := by
              apply Finset.card_image_of_injOn
              intro a ha b hb hab
              have ha' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1
              have hb' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
              have hab' : (a+1) % L = (b+1) % L := hab
              rw [hmodL a ha', hmodL b hb'] at hab'
              split_ifs at hab' <;> omega
            have h3 : Disjoint S (S.image (fun k => (k+1) % L)) := by
              rw [Finset.disjoint_left]
              intro a ha ha2
              obtain ⟨k, hk, hka⟩ := Finset.mem_image.mp ha2
              obtain ⟨hkr, hkL, hkM⟩ := Finset.mem_filter.mp hk
              obtain ⟨_, haL, haM⟩ := Finset.mem_filter.mp ha
              subst hka
              have hkL' : k < L := Finset.mem_range.mp hkr
              have hmk := hmodL k hkL'
              have hne : (be[k]'(by first | assumption | omega)) ≠ be[(k+1) % L]'haL := by
                intro heq
                have := hbend.getElem_inj_iff.mp heq
                rw [hmk] at this
                split_ifs at this <;> omega
              apply hM'm _ hkM _ haM hne (bv[(k+1) % L]'(by rw [hbvlen]; exact Nat.mod_lt _ (by omega)))
              · rw [hcends k hkL']; exact Sym2.mem_mk_right _ _
              · rw [hcends ((k+1) % L) (Nat.mod_lt _ (by omega))]; exact Sym2.mem_mk_left _ _
            have h4 : S ∪ S.image (fun k => (k+1) % L) ⊆ Finset.range L := by
              intro x hx
              rcases Finset.mem_union.mp hx with hx | hx
              · exact (Finset.mem_filter.mp hx).1
              · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
                exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
            have h5 := Finset.card_le_card h4
            rw [Finset.card_union_of_disjoint h3, h2, Finset.card_range] at h5
            omega
          have hlow : (L - 1) / 2 ≤ (M ∩ be.toFinset).card := by
            have hsub : (Finset.range ((L-1)/2)).image (fun t => be.getD (2*t+1) e) ⊆ M ∩ be.toFinset := by
              intro f hf
              obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
              have ht' := Finset.mem_range.mp ht
              have hb : 2*t+1 < be.length := by omega
              rw [List.getD_eq_getElem _ _ hb]
              exact Finset.mem_inter.mpr ⟨(hbeM _ hb).mpr (by omega), List.mem_toFinset.mpr (List.getElem_mem _)⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_image_of_injOn, Finset.card_range] at this
            · exact this
            · intro a ha b hb hab
              have ha' := Finset.mem_range.mp (Finset.mem_coe.mp ha)
              have hb' := Finset.mem_range.mp (Finset.mem_coe.mp hb)
              have hab' : be.getD (2*a+1) e = be.getD (2*b+1) e := hab
              rw [List.getD_eq_getElem _ _ (by omega : 2*a+1 < be.length),
                List.getD_eq_getElem _ _ (by omega : 2*b+1 < be.length)] at hab'
              have := hbend.getElem_inj_iff.mp hab'
              omega
          omega
        have hbase : ∀ f ∈ M ∩ be.toFinset, ∀ h0 : 0 < bv.length, bv[0]'h0 ∉ G.ends f := by
          intro f hf h00 hb
          obtain ⟨hfM, hfB⟩ := Finset.mem_inter.mp hf
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hfB)
          have hodd := (hbeM k hk).mp hfM
          rw [hcends k (by omega), Sym2.mem_iff] at hb
          rcases hb with hb | hb
          · have := hbvnd.getElem_inj_iff.mp hb; omega
          · have := hbvnd.getElem_inj_iff.mp hb
            rw [hmodL k (by omega)] at this
            split_ifs at this <;> omega
        exact ⟨hbend, hcirc, hmaxB, hbase⟩
      obtain ⟨hPl, hu, hv, he⟩ := hF
      obtain ⟨⟨hMJsub, hMJm, hmax⟩, hrJ, hrJexp, hrexp⟩ := hPl
      -- index form of paths
      have pathIff : ∀ (vs : List V) (es : List E), IsPath G vs es ↔
          (vs.Nodup ∧ vs.length = es.length + 1 ∧
            ∀ k (h1 : k + 1 < vs.length) (h2 : k < es.length),
              G.ends (es[k]'(by first | assumption | omega)) = s((vs[k]'(by first | assumption | omega)), (vs[k+1]'(by first | assumption | omega)))) := by
        intro vs es
        unfold IsPath
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun k hk1 hk2 => ?_⟩
          have := congrArg (fun l => l[k]?) h3
          simp [List.getElem?_zipWith, hk2, hk1] at this
          rw [List.getElem?_eq_getElem (by omega : k < vs.length)] at this
          simpa using this
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, ?_⟩
          apply List.ext_getElem
          · simp; omega
          · intro k hk1 hk2
            simp at hk1 hk2 ⊢
            exact h3 k (by omega) hk1
      have hverts : J.verts = J.inner ∪ J.outer := rfl
      have hdisj : ∀ x, x ∈ J.inner → x ∈ J.outer → False := fun x h1 h2 =>
        Finset.disjoint_left.mp J.disjoint h1 h2
      -- edge types
      have edgeType : ∀ f ∈ J.edges, ∀ a b, G.ends f = s(a, b) →
          (a ∈ J.inner ∧ b ∈ J.outer) ∨ (a ∈ J.outer ∧ b ∈ J.inner) := by
        intro f hf a b hab
        obtain ⟨x, hx, y, hy, hxy⟩ := J.edge_ends f hf
        rw [hab] at hxy
        rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr ⟨hy, hx⟩
      have huv : u ≠ v := by
        intro h; apply G.loopless e; rw [he, h]; exact Sym2.mk_isDiag_iff.mpr rfl
      have heJ : e ∉ J.edges := by
        intro h
        rcases edgeType e h u v he with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hdisj u h1 hu
        · exact hdisj v h2 hv
      -- take of a path
      have pathTake : ∀ (vs : List V) (es : List E) (k : ℕ), IsPath G vs es → k < vs.length →
          IsPath G (vs.take (k+1)) (es.take k) := by
        intro vs es k hp hk
        rw [pathIff] at hp ⊢
        obtain ⟨h1, h2, h3⟩ := hp
        refine ⟨h1.sublist (List.take_sublist _ _), by simp; omega, ?_⟩
        intro m hm1 hm2
        simp only [List.getElem_take]
        simp at hm1 hm2
        exact h3 m (by omega) (by omega)
      -- edges of a path are distinct
      have pathEdgeNodup : ∀ (vs : List V) (es : List E), IsPath G vs es → es.Nodup := by
        intro vs es hp
        rw [pathIff] at hp
        obtain ⟨h1, h2, h3⟩ := hp
        rw [List.nodup_iff_injective_get]
        intro ⟨a, ha⟩ ⟨b, hb⟩ hab
        simp only [List.get_eq_getElem] at hab
        have e1 := h3 a (by omega) ha
        have e2 := h3 b (by omega) hb
        rw [hab, e2] at e1
        rcases Sym2.eq_iff.mp e1 with ⟨x, y⟩ | ⟨x, y⟩
        · have := h1.getElem_inj_iff.mp x
          simp; omega
        · have hx := h1.getElem_inj_iff.mp x
          have hy := h1.getElem_inj_iff.mp y
          omega
      let cov : V → Prop := fun x => ∃ f ∈ M ∩ J.edges, x ∈ G.ends f
      have augment : ∀ (vs : List V) (es : List E), IsPath G vs es → es.toFinset ⊆ J.edges →
          (∀ k (h : k < es.length), ((es[k]'(by first | assumption | omega)) ∈ M ↔ k % 2 = 1)) → es.length % 2 = 1 →
          (∀ x ∈ vs.head?, ¬ cov x) → (∀ x ∈ vs.getLast?, ¬ cov x) → False := by
        clear fin glue circ circM genV genE
        intro vs es hp hesJ halt hodd hhead hlast
        obtain ⟨hnd, hlen, hends⟩ := (pathIff vs es).mp hp
        have hend := pathEdgeNodup vs es hp
        have esJ : ∀ k (h : k < es.length), (es[k]'(by first | assumption | omega)) ∈ J.edges := fun k h =>
          hesJ (List.mem_toFinset.mpr (List.getElem_mem h))
        have hv0 : ¬ cov (vs[0]'(by omega)) := hhead _ (by simp [List.head?_eq_getElem?])
        have hvL : ¬ cov (vs[es.length]'(by omega)) := hlast _ (by
          rw [List.getLast?_eq_getElem?]; simp [hlen])
        have covAt : ∀ f ∈ M ∩ J.edges, f ∉ es → ∀ j (hj : j < vs.length), (vs[j]'(by first | assumption | omega)) ∉ G.ends f := by
          intro f hf hfes j hj hx
          by_cases hj0 : j = 0
          · subst hj0; exact hv0 ⟨f, hf, hx⟩
          by_cases hjL : j = es.length
          · subst hjL; exact hvL ⟨f, hf, hx⟩
          rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
          · have hM1 : (es[j-1]'(by first | assumption | omega)) ∈ M := (halt (j-1) (by omega)).mpr (by omega)
            have hne : f ≠ (es[j-1]'(by first | assumption | omega)) := fun h => hfes (h ▸ List.getElem_mem _)
            have hin : (vs[j]'(by first | assumption | omega)) ∈ G.ends (es[j-1]'(by first | assumption | omega)) := by
              rw [hends (j-1) (by omega) (by omega)]
              have : (vs[j-1+1]'(by first | assumption | omega)) = (vs[j]'(by first | assumption | omega)) := by congr 1; omega
              rw [this]; exact Sym2.mem_mk_right _ _
            exact hM f (Finset.mem_inter.mp hf).1 _ hM1 hne _ hx hin
          · have hM1 : (es[j]'(by first | assumption | omega)) ∈ M := (halt j (by omega)).mpr hpar
            have hne : f ≠ (es[j]'(by first | assumption | omega)) := fun h => hfes (h ▸ List.getElem_mem _)
            have hin : (vs[j]'(by first | assumption | omega)) ∈ G.ends (es[j]'(by first | assumption | omega)) := by
              rw [hends j (by omega) (by omega)]; exact Sym2.mem_mk_left _ _
            exact hM f (Finset.mem_inter.mp hf).1 _ hM1 hne _ hx hin
        set M0 := M ∩ J.edges with hM0
        let M' := (M0 \ es.toFinset) ∪ (es.toFinset.filter (· ∉ M))
        have evenOf : ∀ g ∈ es.toFinset.filter (· ∉ M), ∃ k, ∃ hk : k < es.length,
            (es[k]'(by first | assumption | omega)) = g ∧ k % 2 = 0 := by
          intro g hg
          obtain ⟨hg1, hg2⟩ := Finset.mem_filter.mp hg
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hg1)
          exact ⟨k, hk, rfl, by by_contra hc; exact hg2 ((halt k hk).mpr (by omega))⟩
        have hsub : M' ⊆ J.edges := by
          intro f hf
          rcases Finset.mem_union.mp hf with h | h
          · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
          · exact hesJ (Finset.mem_filter.mp h).1
        have hmatch : IsMatching G M' := by
          intro f hf g hg hfg x hxf hxg
          rcases Finset.mem_union.mp hf with hf' | hf' <;>
            rcases Finset.mem_union.mp hg with hg' | hg'
          · exact hM f (Finset.mem_inter.mp (Finset.mem_sdiff.mp hf').1).1 g
              (Finset.mem_inter.mp (Finset.mem_sdiff.mp hg').1).1 hfg x hxf hxg
          · obtain ⟨k, hk, rfl, _⟩ := evenOf g hg'
            rw [hends k (by omega) hk, Sym2.mem_iff] at hxg
            have hfes : f ∉ es := fun h => (Finset.mem_sdiff.mp hf').2 (List.mem_toFinset.mpr h)
            rcases hxg with rfl | rfl
            · exact covAt f (Finset.mem_sdiff.mp hf').1 hfes k (by omega) hxf
            · exact covAt f (Finset.mem_sdiff.mp hf').1 hfes (k+1) (by omega) hxf
          · obtain ⟨k, hk, rfl, _⟩ := evenOf f hf'
            rw [hends k (by omega) hk, Sym2.mem_iff] at hxf
            have hges : g ∉ es := fun h => (Finset.mem_sdiff.mp hg').2 (List.mem_toFinset.mpr h)
            rcases hxf with rfl | rfl
            · exact covAt g (Finset.mem_sdiff.mp hg').1 hges k (by omega) hxg
            · exact covAt g (Finset.mem_sdiff.mp hg').1 hges (k+1) (by omega) hxg
          · obtain ⟨k, hk, rfl, hkp⟩ := evenOf f hf'
            obtain ⟨l, hl, rfl, hlp⟩ := evenOf g hg'
            have hkl : k ≠ l := fun h => hfg (by subst h; rfl)
            rw [hends k (by omega) hk, Sym2.mem_iff] at hxf
            rw [hends l (by omega) hl, Sym2.mem_iff] at hxg
            rcases hxf with rfl | rfl <;> rcases hxg with h | h
            · exact hkl (hnd.getElem_inj_iff.mp h)
            · have := hnd.getElem_inj_iff.mp h; omega
            · have := hnd.getElem_inj_iff.mp h; omega
            · have := hnd.getElem_inj_iff.mp h; omega
        have hcard := hmax M' hsub hmatch
        obtain ⟨t, ht⟩ : ∃ t, es.length = 2 * t + 1 := ⟨es.length / 2, by omega⟩
        have hodd_le : (es.toFinset.filter (· ∈ M)).card ≤ t := by
          have : es.toFinset.filter (· ∈ M) ⊆
              (Finset.univ : Finset (Fin t)).image (fun k => es[2 * k.1 + 1]'(by omega)) := by
            intro g hg
            obtain ⟨hg1, hg2⟩ := Finset.mem_filter.mp hg
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hg1)
            have hk1 := (halt k hk).mp hg2
            refine Finset.mem_image.mpr ⟨⟨k / 2, by omega⟩, Finset.mem_univ _, ?_⟩
            congr 1; simp; omega
          calc _ ≤ _ := Finset.card_le_card this
            _ ≤ _ := Finset.card_image_le
            _ = t := by simp
        have heven_ge : t + 1 ≤ (es.toFinset.filter (· ∉ M)).card := by
          have hs : (Finset.univ : Finset (Fin (t+1))).image (fun k => es[2 * k.1]'(by omega)) ⊆
              es.toFinset.filter (· ∉ M) := by
            intro g hg
            obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hg
            refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), ?_⟩
            intro hm; have := (halt _ (by omega)).mp hm; omega
          have hinj : Function.Injective (fun k : Fin (t+1) => es[2 * k.1]'(by omega)) := by
            intro a b hab
            have := hend.getElem_inj_iff.mp hab
            ext; omega
          calc t + 1 = _ := by simp
            _ = _ := (Finset.card_image_of_injective _ hinj).symm
            _ ≤ _ := Finset.card_le_card hs
        have hM'card : M'.card = (M0 \ es.toFinset).card + (es.toFinset.filter (· ∉ M)).card := by
          apply Finset.card_union_of_disjoint
          rw [Finset.disjoint_left]
          intro f h1 h2
          exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_filter.mp h2).1
        have hM0card : M0.card ≤ (M0 \ es.toFinset).card + (es.toFinset.filter (· ∈ M)).card := by
          calc M0.card ≤ ((M0 \ es.toFinset) ∪ (es.toFinset.filter (· ∈ M))).card := by
                apply Finset.card_le_card
                intro f hf
                by_cases h : f ∈ es.toFinset
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, (Finset.mem_inter.mp hf).1⟩)
                · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hf, h⟩)
            _ ≤ _ := Finset.card_union_le _ _
        omega
      have alternate : ∀ w0 ∈ J.outer, ¬ cov w0 → ∀ (vs : List V) (es : List E), IsPath G vs es →
          vs.toFinset ⊆ J.verts → es.toFinset ⊆ J.edges → vs.head? = some w0 →
          (∀ k (h : k < vs.length), ((vs[k]'(by first | assumption | omega)) ∈ J.inner ↔ k % 2 = 1)) ∧
          (∀ k (h : k < es.length), ((es[k]'(by first | assumption | omega)) ∈ M ↔ k % 2 = 1)) := by
        clear fin glue circ circM genV genE
        intro w0 hw0 hw0c vs es hp hvsJ hesJ hh
        have hp' := (pathIff vs es).mp hp
        obtain ⟨hnd, hlen, hends⟩ := hp'
        have hend := pathEdgeNodup vs es hp
        have esJ : ∀ k (h : k < es.length), (es[k]'(by first | assumption | omega)) ∈ J.edges := fun k h =>
          hesJ (List.mem_toFinset.mpr (List.getElem_mem h))
        have hv0 : vs[0]'(by omega) = w0 := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
          simpa using hh
        have key : ∀ k, ∀ j ≤ k, (∀ h : j < vs.length, ((vs[j]'(by first | assumption | omega)) ∈ J.inner ↔ j % 2 = 1)) ∧
            (∀ h : j < es.length, ((es[j]'(by first | assumption | omega)) ∈ M ↔ j % 2 = 1)) := by
          intro k
          induction k with
          | zero =>
            intro j hj
            obtain rfl : j = 0 := by omega
            refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [hv0]; simp only [Nat.zero_mod]
              exact ⟨fun hi => (hdisj _ hi hw0).elim, fun h => by omega⟩
            · simp only [Nat.zero_mod]
              refine ⟨fun hm => ?_, fun h => by omega⟩
              exfalso; apply hw0c
              refine ⟨(es[0]'(by first | assumption | omega)), Finset.mem_inter.mpr ⟨hm, esJ 0 h⟩, ?_⟩
              rw [hends 0 (by omega) h, hv0]; exact Sym2.mem_mk_left _ _
          | succ k ih =>
            intro j hj
            rcases Nat.lt_or_ge j (k+1) with hjk | hjk
            · exact ih j (by omega)
            obtain rfl : j = k + 1 := by omega
            have hvert : ∀ h : k + 1 < vs.length, ((vs[k+1]'(by first | assumption | omega)) ∈ J.inner ↔ (k+1) % 2 = 1) := by
              intro h
              have ht := edgeType _ (esJ k (by omega)) _ _ (hends k h (by omega))
              have ihk := (ih k le_rfl).1 (by omega)
              rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have : k % 2 = 1 := ihk.mp h1
                exact ⟨fun hi => absurd (hdisj _ hi h2) id, fun _ => by omega⟩
              · have : ¬ k % 2 = 1 := fun hk => hdisj _ (ihk.mpr hk) h1
                exact ⟨fun _ => by omega, fun _ => h2⟩
            refine ⟨hvert, fun h => ?_⟩
            have hne : (es[k]'(by first | assumption | omega)) ≠ (es[k+1]'(by first | assumption | omega)) := fun heq => by
              have := hend.getElem_inj_iff.mp heq; omega
            have hk_in : (vs[k+1]'(by first | assumption | omega)) ∈ G.ends (es[k]'(by first | assumption | omega)) := by
              rw [hends k (by omega) (by omega)]; exact Sym2.mem_mk_right _ _
            have hk1_in : (vs[k+1]'(by first | assumption | omega)) ∈ G.ends (es[k+1]'(by first | assumption | omega)) := by
              rw [hends (k+1) (by omega) h]; exact Sym2.mem_mk_left _ _
            have ihe := (ih k le_rfl).2 (by omega)
            rcases Nat.mod_two_eq_zero_or_one k with hk | hk
            · -- k+1 odd
              have hinner : (vs[k+1]'(by first | assumption | omega)) ∈ J.inner := (hvert (by omega)).mpr (by omega)
              have hcov : cov (vs[k+1]'(by first | assumption | omega)) := by
                by_contra hc
                have hpt := pathTake vs es (k+1) hp (by omega)
                refine augment _ _ hpt ?_ ?_ ?_ ?_ ?_
                · intro f hf
                  exact hesJ (List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hf)))
                · intro m hm
                  rw [List.length_take] at hm
                  rw [List.getElem_take]
                  exact (ih m (by omega)).2 (by omega)
                · rw [List.length_take]; omega
                · intro y hy
                  rw [List.head?_take] at hy
                  rw [if_neg (Nat.succ_ne_zero _), hh] at hy
                  cases hy; exact hw0c
                · intro y hy
                  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by rw [List.length_take]; omega), List.getElem_take] at hy
                  have : y = (vs[k+1]'(by omega)) :=
                    (Option.some.inj hy).symm.trans (idxV vs _ _ _ _ (by rw [List.length_take]; omega))
                  subst this; exact hc
              obtain ⟨f, hf, hxf⟩ := hcov
              have hfJ := (Finset.mem_inter.mp hf).2
              have hfM := (Finset.mem_inter.mp hf).1
              have hdeg := J.inner_deg _ hinner
              have hsub : ({(es[k]'(by first | assumption | omega)), (es[k+1]'(by first | assumption | omega))} : Finset E) ⊆ J.edges.filter (fun g => (vs[k+1]'(by first | assumption | omega)) ∈ G.ends g) := by
                intro g hg
                simp only [Finset.mem_insert, Finset.mem_singleton] at hg
                rcases hg with rfl | rfl
                · exact Finset.mem_filter.mpr ⟨esJ k (by omega), hk_in⟩
                · exact Finset.mem_filter.mpr ⟨esJ (k+1) h, hk1_in⟩
              have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hdeg, Finset.card_pair hne])
              have hfin : f ∈ ({(es[k]'(by first | assumption | omega)), (es[k+1]'(by first | assumption | omega))} : Finset E) := by
                rw [heq]; exact Finset.mem_filter.mpr ⟨hfJ, hxf⟩
              simp only [Finset.mem_insert, Finset.mem_singleton] at hfin
              rcases hfin with rfl | rfl
              · exact absurd (ihe.mp hfM) (by omega)
              · exact ⟨fun _ => by omega, fun _ => hfM⟩
            · -- k odd, k+1 even
              have hkM : (es[k]'(by first | assumption | omega)) ∈ M := ihe.mpr hk
              refine ⟨fun hm => absurd (hM _ hkM _ hm hne _ hk_in) (fun h' => h' hk1_in), fun h' => by omega⟩
        exact ⟨fun k h => (key k k le_rfl).1 h, fun k h => (key k k le_rfl).2 h⟩
      have pathExists : ∀ a ∈ J.verts, ∀ b ∈ J.verts, ∃ vs es, PathIn G J.toSub a b vs es := by
        intro a ha b hb
        have hrt := J.connected.2 a ha b hb
        induction hrt with
        | refl =>
          refine ⟨[a], [], ?_, ?_, ?_, rfl, rfl⟩
          · rw [pathIff]; simp
          · intro x hx; simp at hx; subst hx; exact ha
          · simp
        | tail hab hbc ih =>
          rename_i c d
          obtain ⟨f, hfJ, hf⟩ := hbc
          have hcd := edgeType f hfJ c d hf
          have hcJ : c ∈ J.verts := by
            rw [hverts]; rcases hcd with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact Finset.mem_union_left _ h1
            · exact Finset.mem_union_right _ h1
          obtain ⟨vs, es, hp, hvsJ, hesJ, hh, hl⟩ := ih hcJ
          obtain ⟨hnd, hlen, hends⟩ := (pathIff vs es).mp hp
          have hlast : (vs[vs.length - 1]'(by first | assumption | omega)) = c := by
            rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl
            simpa using hl
          by_cases hdv : d ∈ vs
          · obtain ⟨i, hi, hvi⟩ := List.getElem_of_mem hdv
            refine ⟨vs.take (i+1), es.take i, pathTake vs es i hp hi, ?_, ?_, ?_, ?_⟩
            · intro x hx; exact hvsJ (List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx)))
            · intro x hx; exact hesJ (List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx)))
            · rw [List.head?_take]; simpa using hh
            · rw [List.getLast?_eq_getElem?]
              rw [List.getElem?_eq_getElem (by rw [List.length_take]; omega), List.getElem_take, ← hvi]
              exact congrArg some (idxV vs _ _ _ _ (by rw [List.length_take]; omega))
          · obtain ⟨g1, g2⟩ := glue vs [c, d] es [f] es.length 1 hlen rfl rfl rfl (fun k h1 h0 h2 => hends k h1 h2)
              (fun k h1 h0 h2 => by
                obtain rfl : k = 0 := Nat.lt_one_iff.mp h2
                exact hf)
              (fun h1 h2 => (idxV vs _ _ _ _ (by omega)).trans hlast)
            refine ⟨vs ++ [d], es ++ [f], ?_, ?_, ?_, ?_, g2⟩
            · rw [pathIff]
              refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton d, fun x hx y hy hxy => hdv ?_⟩, ?_,
                fun k h1 h2 => g1 k h1 (Nat.lt_of_succ_lt h1) h2⟩
              · rw [List.mem_singleton] at hy; rw [← hy, ← hxy]; exact hx
              · rw [List.length_append, List.length_append, hlen]; rfl
            · intro x hx
              rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact hvsJ (List.mem_toFinset.mpr hx)
              · show _ ∈ J.inner ∪ J.outer
                rcases hcd with ⟨_, h1⟩ | ⟨_, h1⟩
                · exact Finset.mem_union_right _ h1
                · exact Finset.mem_union_left _ h1
            · intro x hx
              rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact hesJ (List.mem_toFinset.mpr hx)
              · exact hfJ
            · rw [List.head?_append, hh]; rfl
      have uncovOuter : ∃ w0 ∈ J.outer, ¬ cov w0 := by
        classical
        have hE : J.inner.card * 2 ≤ J.edges.card * 1 := by
          refine Finset.card_mul_le_card_mul (fun x f => x ∈ G.ends f) ?_ ?_
          · intro x hx
            exact (J.inner_deg x hx).ge
          · intro f hf
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.bipartiteBelow, Finset.mem_filter] at ha hb
            obtain ⟨x, hx, y, hy, hxy⟩ := J.edge_ends f hf
            have h1 := ha.2; have h2 := hb.2
            rw [hxy, Sym2.mem_iff] at h1 h2
            rcases h1 with rfl | rfl
            · rcases h2 with rfl | rfl
              · rfl
              · exact (hdisj _ hb.1 hy).elim
            · exact (hdisj _ ha.1 hy).elim
        have hcard : J.inner.card + J.outer.card = J.edges.card + 1 := by
          rw [← Finset.card_union_of_disjoint J.disjoint]; exact J.card_verts
        have hMI : (M ∩ J.edges).card ≤ J.inner.card := by
          refine Finset.card_le_card_of_forall_subsingleton (fun f x => x ∈ G.ends f) ?_ ?_
          · intro f hf
            obtain ⟨x, hx, y, hy, hxy⟩ := J.edge_ends f (Finset.mem_inter.mp hf).2
            exact ⟨x, hx, by rw [hxy]; exact Sym2.mem_mk_left _ _⟩
          · intro x hx f1 hf1 f2 hf2
            by_contra hne
            exact hM f1 (Finset.mem_inter.mp hf1.1).1 f2 (Finset.mem_inter.mp hf2.1).1 hne x hf1.2 hf2.2
        have hC : (J.outer.filter cov).card ≤ (M ∩ J.edges).card := by
          refine Finset.card_le_card_of_forall_subsingleton (fun x f => x ∈ G.ends f) ?_ ?_
          · intro x hx
            exact (Finset.mem_filter.mp hx).2
          · intro f hf x1 hx1 x2 hx2
            obtain ⟨x, hx, y, hy, hxy⟩ := J.edge_ends f (Finset.mem_inter.mp hf).2
            have o1 := (Finset.mem_filter.mp hx1.1).1
            have o2 := (Finset.mem_filter.mp hx2.1).1
            have h1 : x1 ∈ G.ends f := hx1.2
            have h2 : x2 ∈ G.ends f := hx2.2
            rw [hxy, Sym2.mem_iff] at h1 h2
            rcases h1 with rfl | rfl
            · exact (hdisj _ hx o1).elim
            rcases h2 with rfl | rfl
            · exact (hdisj _ hx o2).elim
            rfl
        have hlt : (J.outer.filter cov).card < J.outer.card := by omega
        obtain ⟨w, hw, hwn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        exact ⟨w, hw, fun hc => hwn (Finset.mem_filter.mpr ⟨hw, hc⟩)⟩
      have innerCov : ∀ x ∈ J.inner, cov x := by
        intro x hx
        obtain ⟨w0, hw0, hw0c⟩ := uncovOuter
        have hw0J : w0 ∈ J.verts := by rw [hverts]; exact Finset.mem_union_right _ hw0
        have hxJ : x ∈ J.verts := by rw [hverts]; exact Finset.mem_union_left _ hx
        obtain ⟨vs, es, hp, hvsJ, hesJ, hh, hl⟩ := pathExists w0 hw0J x hxJ
        obtain ⟨a1, a2⟩ := alternate w0 hw0 hw0c vs es hp hvsJ hesJ hh
        have hlen := ((pathIff vs es).mp hp).2.1
        have hlast : (vs[vs.length - 1]'(by first | assumption | omega)) = x := by
          rw [List.getLast?_eq_getElem?] at hl
          rw [List.getElem?_eq_getElem (by omega)] at hl
          simpa using hl
        have hodd : (vs.length - 1) % 2 = 1 := (a1 _ (by omega)).mp (by rw [hlast]; exact hx)
        by_contra hc
        refine augment vs es hp hesJ a2 (by omega) ?_ ?_
        · intro y hy; rw [hh] at hy; cases hy; exact hw0c
        · intro y hy; rw [hl] at hy; cases hy; exact hc
      have hrO : r ∈ J.outer := by
        have : r ∉ J.inner := fun h => by
          obtain ⟨f, hf, hrf⟩ := innerCov r h
          exact hrJexp f hf hrf
        rw [hverts] at hrJ
        rcases Finset.mem_union.mp hrJ with h | h
        · exact absurd h this
        · exact h
      have huJ : u ∈ J.verts := by rw [hverts]; exact Finset.mem_union_right _ hu
      have hvJ : v ∈ J.verts := by rw [hverts]; exact Finset.mem_union_right _ hv
      have hrcov : ¬ cov r := fun ⟨f, hf, hrf⟩ => hrJexp f hf hrf
      obtain ⟨Pv, Pe, hP⟩ := pathExists r hrJ u huJ
      obtain ⟨Qv, Qe, hQ⟩ := pathExists r hrJ v hvJ
      obtain ⟨hPp, hPvs, hPes, hPh, hPl⟩ := hP
      obtain ⟨hQp, hQvs, hQes, hQh, hQl⟩ := hQ
      obtain ⟨Pnd, Plen, Pends⟩ := (pathIff Pv Pe).mp hPp
      obtain ⟨Qnd, Qlen, Qends⟩ := (pathIff Qv Qe).mp hQp
      obtain ⟨Pa1, Pa2⟩ := alternate r hrO hrcov Pv Pe hPp hPvs hPes hPh
      obtain ⟨Qa1, Qa2⟩ := alternate r hrO hrcov Qv Qe hQp hQvs hQes hQh
      have Pend := pathEdgeNodup Pv Pe hPp
      have Qend := pathEdgeNodup Qv Qe hQp
      obtain ⟨m, hm⟩ : ∃ m, m = Pe.length := ⟨_, rfl⟩
      obtain ⟨n, hn⟩ : ∃ n, n = Qe.length := ⟨_, rfl⟩
      have hP0 : Pv[0]'(by omega) = r := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hPh; simpa using hPh
      have hQ0 : Qv[0]'(by omega) = r := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hQh; simpa using hQh
      have hPm : Pv[m]'(by omega) = u := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hPl
        simp at hPl; rw [← hPl]; congr 1; omega
      have hQn : Qv[n]'(by omega) = v := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hQl
        simp at hQl; rw [← hQl]; congr 1; omega
      have hmeven : m % 2 = 0 := by
        have := Pa1 m (by omega); rw [hPm] at this
        by_contra h; exact hdisj u (this.mpr (by omega)) hu
      have hneven : n % 2 = 0 := by
        have := Qa1 n (by omega); rw [hQn] at this
        by_contra h; exact hdisj v (this.mpr (by omega)) hv
      have PeJ : ∀ k (h : k < Pe.length), (Pe[k]'(by first | assumption | omega)) ∈ J.edges := fun k h =>
        hPes (List.mem_toFinset.mpr (List.getElem_mem h))
      have QeJ : ∀ k (h : k < Qe.length), (Qe[k]'(by first | assumption | omega)) ∈ J.edges := fun k h =>
        hQes (List.mem_toFinset.mpr (List.getElem_mem h))
      have heM : e ∉ M := by
        intro heM
        have hue : u ∈ G.ends e := by rw [he]; exact Sym2.mem_mk_left _ _
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · have : u = r := by rw [← hPm, ← hP0]; congr 1
          exact hrexp e heM (this ▸ hue)
        · have hM1 : (Pe[m-1]'(by first | assumption | omega)) ∈ M := (Pa2 (m-1) (by omega)).mpr (by omega)
          have hne : (Pe[m-1]'(by first | assumption | omega)) ≠ e := fun h => heJ (h ▸ PeJ (m-1) (by omega))
          have hin : u ∈ G.ends (Pe[m-1]'(by first | assumption | omega)) := by
            rw [Pends (m-1) (by omega) (by omega)]
            have : Pv[m-1+1]'(by omega) = u := by rw [← hPm]; congr 1; omega
            rw [this]; exact Sym2.mem_mk_right _ _
          exact hM _ hM1 _ heM hne u hin hue
      -- choose j greatest with (Qv[j]'(by first | assumption | omega)) ∈ Pv
      have hj : ∃ j, ∃ hj : j ≤ n, Qv[j]'(by omega) ∈ Pv ∧
          ∀ l (hl : l ≤ n), j < l → Qv[l]'(by omega) ∉ Pv := by
        classical
        let p : ℕ → Prop := fun j => ∃ h : j < Qv.length, (Qv[j]'(by first | assumption | omega)) ∈ Pv
        have h0 : p 0 := ⟨by omega, by rw [hQ0, ← hP0]; exact List.getElem_mem _⟩
        obtain ⟨h1, h2⟩ := Nat.findGreatest_spec (P := p) (Nat.zero_le n) h0
        refine ⟨Nat.findGreatest p n, Nat.findGreatest_le n, h2, ?_⟩
        intro l hl hjl hmem
        exact Nat.findGreatest_is_greatest hjl hl ⟨by omega, hmem⟩
      obtain ⟨j, hjn, hjP, hjmax⟩ := hj
      obtain ⟨i, hi, hPi⟩ := List.getElem_of_mem hjP
      have him : i ≤ m := by omega
      have hparity : i % 2 = j % 2 := by
        have a := Pa1 i hi; have b := Qa1 j (by omega)
        rw [hPi] at a; rw [a] at b; omega
      have hieven : i % 2 = 0 := by
        clear innerCov
        by_contra hodd
        have hinner : Pv[i]'hi ∈ J.inner := (Pa1 i hi).mpr (by omega)
        have hjl : j < Qv.length := by omega
        have hi_m : i < m := lt_of_le_of_ne him (fun h =>
          hdisj u (((idxV Pv i m hi (by omega) h).trans hPm) ▸ hinner) hu)
        have hj_n : j < n := lt_of_le_of_ne hjn (fun h =>
          hdisj v ((hPi.trans ((idxV Qv j n hjl (by omega) h).trans hQn)) ▸ hinner) hv)
        have hi' : i < Pe.length := hm ▸ hi_m
        have hj' : j < Qe.length := hn ▸ hj_n
        have hi1 : i % 2 = 1 := by omega
        have hM1 : Pe[i]'hi' ∈ M := (Pa2 i hi').mpr hi1
        have hM2 : Qe[j]'hj' ∈ M := (Qa2 j hj').mpr (hparity ▸ hi1)
        have e1 := Pends i (by omega) hi'
        have e2 := Qends j (by omega) hj'
        by_cases heq : Pe[i]'hi' = Qe[j]'hj'
        · rw [heq, e2, ← hPi] at e1
          have := Sym2.congr_right.mp e1
          exact hjmax (j+1) hj_n (Nat.lt_succ_self j) (by rw [this]; exact List.getElem_mem _)
        · apply hM _ hM1 _ hM2 heq (Pv[i]'hi)
          · rw [e1]; exact Sym2.mem_mk_left _ _
          · rw [e2, hPi]; exact Sym2.mem_mk_left _ _
      obtain ⟨pp, hpp⟩ : ∃ pp, m = i + pp := ⟨m - i, by omega⟩
      obtain ⟨qq, hqq⟩ : ∃ qq, n = j + qq := ⟨n - j, by omega⟩
      have hbv0 : (Pv[i]'(by first | assumption | omega)) = (Qv[j]'(by first | assumption | omega)) := hPi
      have hL3 : 3 ≤ pp + qq + 1 := by
        by_contra hc
        have h1 : m = i := by omega
        have h2 : n = j := by omega
        exact huv (((idxV Pv i m hi (by omega) h1.symm).trans hPm).symm.trans (hPi.trans ((idxV Qv j n (by omega) (by omega) h2.symm).trans hQn)))
      obtain ⟨L, hL⟩ : ∃ L, L = pp + qq + 1 := ⟨_, rfl⟩
      obtain ⟨bv, hbvdef⟩ : ∃ l, l = Pv.drop i ++ (Qv.drop (j+1)).reverse := ⟨_, rfl⟩
      obtain ⟨be, hbedef⟩ : ∃ l, l = Pe.drop i ++ e :: (Qe.drop j).reverse := ⟨_, rfl⟩
      have hbvlen : bv.length = L := by
        rw [hbvdef, List.length_append, List.length_reverse, List.length_drop, List.length_drop, hL, Plen, Qlen]
        omega
      have hbelen : be.length = L := by
        rw [hbedef, List.length_append, List.length_cons, List.length_reverse, List.length_drop, List.length_drop, hL]
        omega
      have hL3' : 3 ≤ L := by rw [hL]; exact hL3
      have hbv00 : ∀ h : 0 < bv.length, bv[0]'h = Pv[i]'hi := by
        rw [hbvdef]; intro h
        rw [List.getElem_append_left (by rw [List.length_drop]; omega), List.getElem_drop]
        exact idxV Pv _ _ _ _ rfl
      have hbvnd : bv.Nodup := by
        subst hbvdef
        rw [List.nodup_append]
        refine ⟨Pnd.sublist (List.drop_sublist _ _), List.nodup_reverse.mpr (Qnd.sublist (List.drop_sublist _ _)), ?_⟩
        intro x hx y hy hxy
        subst hxy
        rw [List.mem_reverse, List.mem_drop_iff_getElem] at hy
        obtain ⟨c, hc, rfl⟩ := hy
        exact hjmax (j+1+c) (by omega) (by omega) (List.mem_of_mem_drop hx)
      have hcends : ∀ k (h : k < L), G.ends (be[k]'(by omega)) =
          s(bv[k]'(by omega), bv[(k+1) % L]'(by rw [hbvlen]; exact Nat.mod_lt _ (by omega))) := by
        intro k hk
        have hld : ∀ (c : ℕ) (l : List E), (l.drop c).length = l.length - c := fun c l => List.length_drop
        have hlv : ∀ (c : ℕ) (l : List V), (l.drop c).length = l.length - c := fun c l => List.length_drop
        refine circ e (Pv.drop i) (Qv.drop j) (Pe.drop i) (Qe.drop j) (pp) (qq) L bv be
          (by rw [hbvdef, List.drop_drop]) hbedef (by rw [hlv]; omega) (by rw [hld]; omega) (by rw [hlv]; omega) (by rw [hld]; omega)
          (by omega) ?_ ?_ ?_ ?_ k hk _ _ _
        · intro k h1 h0 h2
          rw [hlv] at h1
          simp only [List.getElem_drop]
          exact Pends (i+k) (by omega) (by omega)
        · intro k h1 h0 h2
          rw [hlv] at h1
          simp only [List.getElem_drop]
          exact Qends (j+k) (by omega) (by omega)
        · intro h1 h2
          rw [List.getElem_drop, List.getElem_drop, he, idxV Pv (i+(pp)) m _ (by omega) (by omega), hPm,
            idxV Qv (j+(qq)) n _ (by omega) (by omega), hQn]
        · intro h1 h2
          rw [List.getElem_drop, List.getElem_drop]
          exact hPi
      have hLodd : L % 2 = 1 := by rw [hL]; omega
      have hbeM : ∀ k (h : k < be.length), be[k]'h ∈ M ↔ k % 2 = 1 := by
        try clear hL3'
        try clear hbv00
        try clear hbend
        try clear hLodd
        try clear hmodL
        try clear hcends
        try clear hbvnd
        try clear hbelen
        try clear hbvlen
        try clear hL
        try clear hL3
        try clear hbvdef
        try clear hbv0
        try clear hjmax
        try clear hjP
        refine circM e (Pe.drop i) (Qe.drop j) (pp) (qq) be hbedef (by rw [List.length_drop]; omega)
          (by rw [List.length_drop]; omega) (by omega) (by omega) heM ?_ ?_
        · intro k h
          rw [List.length_drop] at h
          rw [List.getElem_drop, Pa2 (i+k) (by omega)]; omega
        · intro k h
          rw [List.length_drop] at h
          rw [List.getElem_drop, Qa2 (j+k) (by omega)]; omega
      obtain ⟨hbend, hcirc, hmaxB, hbase'⟩ := fin e bv be L hL3' hLodd hbvlen hbelen hbvnd hcends hbeM
      have hbv0l : 0 < bv.length := by omega
      have hbase : ∀ f ∈ M ∩ be.toFinset, Pv[i]'hi ∉ G.ends f := fun f hf =>
        hbv00 hbv0l ▸ hbase' f hf hbv0l
      have hstem : IsStem G M (Pv.take (i+1)) (Pe.take i) := by
        try clear hmaxB
        try clear hcirc
        try clear hbeM
        try clear hLodd
        try clear hparity
        try clear hneven
        try clear hmeven
        try clear hL3
        try clear hbeget
        try clear hbvget
        try clear hbelen
        try clear hbvlen
        try clear hL
        refine ⟨⟨pathTake Pv Pe i hPp hi, ?_⟩, ?_, ?_⟩
        · rw [List.isChain_iff_getElem]
          intro k hk
          simp only [List.length_take] at hk
          simp only [List.getElem_take]
          rw [Pa2 k (by omega), Pa2 (k+1) (by omega)]
          constructor <;> intro h <;> omega
        · intro x hx
          rw [List.head?_take] at hx
          simp only [Nat.add_one_ne_zero, if_false] at hx
          rw [hPh] at hx; cases hx; exact hrexp
        · intro f hf
          rw [List.getLast?_take] at hf
          split at hf
          · cases hf
          · rw [List.getElem?_eq_getElem (by omega)] at hf
            simp at hf
            rw [← hf]
            exact (Pa2 _ (by omega)).mpr (by omega)
      have hsvlast : (Pv.take (i+1)).getLast? = some (Pv[i]'(by first | assumption | omega)) := by
        try clear hmaxB
        try clear hcirc
        try clear hbeM
        try clear hLodd
        try clear hieven
        try clear hparity
        try clear hneven
        try clear hmeven
        try clear hL3
        try clear hbeget
        try clear hbvget
        try clear hbelen
        try clear hbvlen
        try clear hL
        have hl : (Pv.take (i+1)).length = i+1 := by simp; omega
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        simp only [List.getElem_take, Option.some.injEq]
        exact Pnd.getElem_inj_iff.mpr (by omega)
      have hsvbv : ∀ x ∈ Pv.take (i+1), x ∈ bv → x = (Pv[i]'(by first | assumption | omega)) := by
        try clear hmaxB
        try clear hcirc
        try clear hbeM
        try clear hLodd
        try clear hieven
        try clear hparity
        try clear hneven
        try clear hmeven
        try clear hL3
        try clear hbeget
        try clear hbvget
        try clear hbelen
        try clear hbvlen
        try clear hL
        intro x hx hxb
        obtain ⟨a, ha, rfl⟩ := List.mem_take_iff_getElem.mp hx
        rw [hbvdef, List.mem_append, List.mem_reverse] at hxb
        rcases hxb with h | h
        · obtain ⟨c, hc, hcx⟩ := List.mem_drop_iff_getElem.mp h
          have := Pnd.getElem_inj_iff.mp hcx
          exact Pnd.getElem_inj_iff.mpr (by omega)
        · obtain ⟨c, hc, hcx⟩ := List.mem_drop_iff_getElem.mp h
          exact absurd (by rw [hcx]; exact List.getElem_mem _) (hjmax (j+1+c) (by omega) (by omega))
      have hQ' : PathIn G J.toSub r v (Pv.take (i+1) ++ Qv.drop (j+1)) (Pe.take i ++ Qe.drop j) := by
        try clear hEset
        try clear hVset
        try clear hsvbv
        try clear hsvlast
        try clear hstem
        try clear hbase
        try clear hmaxB
        try clear hcirc
        try clear hbeM
        try clear hbend
        try clear hmodL
        try clear hcends
        try clear hbvnd
        try clear hLodd
        try clear hbeget
        try clear hbvget
        try clear hbelen
        try clear hbvlen
        try clear hbedef
        try clear hbvdef
        try clear hL
        try clear hL3
        try clear hbv0
        try clear hieven
        try clear hparity
        try clear heM
        try clear PeJ
        try clear QeJ
        try clear hneven
        try clear hmeven
        try clear hrcov
        try clear innerCov
        try clear uncovOuter
        try clear pathExists
        try clear alternate
        try clear augment
        try clear pathEdgeNodup
        have hQdrop : ∀ x ∈ Qv.drop (j+1), x ∉ Pv := by
          intro x hx
          obtain ⟨c, hc, rfl⟩ := List.mem_drop_iff_getElem.mp hx
          exact hjmax _ (by omega) (by omega)
        obtain ⟨g1, g2⟩ := glue (Pv.take (i+1)) (Qv.drop j) (Pe.take i) (Qe.drop j) i (n-j) (by rw [List.length_take]; omega)
          (by rw [List.length_take]; omega) (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
          (by intro k h1 h0 h2
              rw [List.length_take] at h1 h2
              simp only [List.getElem_take]
              exact Pends k (by omega) (by omega))
          (by intro k h1 h0 h2
              rw [List.length_drop] at h1
              simp only [List.getElem_drop]
              exact Qends (j+k) (by omega) (by omega))
          (by intro h1 h2
              rw [List.getElem_take, List.getElem_drop]
              exact hPi)
        simp only [List.drop_drop] at g1 g2
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [pathIff]
          refine ⟨?_, ?_, fun k h1 h2 => g1 k h1 (Nat.lt_of_succ_lt h1) h2⟩
          · rw [List.nodup_append]
            refine ⟨Pnd.sublist (List.take_sublist _ _), Qnd.sublist (List.drop_sublist _ _), ?_⟩
            intro x hx y hy hxy
            subst hxy
            exact hQdrop x hy (List.mem_of_mem_take hx)
          · rw [List.length_append, List.length_append, List.length_take, List.length_take, List.length_drop, List.length_drop]
            omega
        · intro x hx
          rw [List.mem_toFinset, List.mem_append] at hx
          rcases hx with hx | hx
          · exact hPvs (List.mem_toFinset.mpr (List.mem_of_mem_take hx))
          · exact hQvs (List.mem_toFinset.mpr (List.mem_of_mem_drop hx))
        · intro x hx
          rw [List.mem_toFinset, List.mem_append] at hx
          rcases hx with hx | hx
          · exact hPes (List.mem_toFinset.mpr (List.mem_of_mem_take hx))
          · exact hQes (List.mem_toFinset.mpr (List.mem_of_mem_drop hx))
        · rw [List.head?_append, List.head?_take, if_neg (Nat.succ_ne_zero i), hPh]; rfl
        · rw [g2, List.getLast?_drop, if_neg (by omega)]
          exact hQl
      have hVset : bv.toFinset ∪ (Pv.take (i+1)).toFinset =
          Pv.toFinset ∪ (Pv.take (i+1) ++ Qv.drop (j+1)).toFinset := by
        try clear hsvbv
        try clear hsvlast
        try clear hstem
        try clear hbase
        try clear hmaxB
        try clear hcirc
        try clear hbeM
        try clear hbend
        try clear hmodL
        try clear hcends
        try clear hbvnd
        try clear hLodd
        try clear hbeget
        try clear hbvget
        try clear hbelen
        try clear hbvlen
        try clear hbedef
        try clear hL
        try clear hL3
        try clear hbv0
        try clear hieven
        try clear hparity
        try clear heM
        try clear PeJ
        try clear QeJ
        try clear hneven
        try clear hmeven
        try clear hrcov
        try clear innerCov
        try clear uncovOuter
        try clear pathExists
        try clear alternate
        try clear augment
        try clear pathEdgeNodup
        try clear hQ'
        have h1 : ∀ x, x ∈ Pv ↔ x ∈ Pv.drop i ∨ x ∈ Pv.take (i+1) := by
          intro x; constructor
          · intro hx; obtain ⟨a, ha, hax⟩ := List.getElem_of_mem hx
            rcases Nat.lt_or_ge a (i+1) with h | h
            · right; exact List.mem_take_iff_getElem.mpr ⟨a, by omega, hax⟩
            · left; refine List.mem_drop_iff_getElem.mpr ⟨a - i, by omega, ?_⟩
              rw [← hax]; congr 1; omega
          · rintro (h | h)
            · exact List.mem_of_mem_drop h
            · exact List.mem_of_mem_take h
        ext x
        simp only [Finset.mem_union, List.mem_toFinset, hbvdef, List.mem_append, List.mem_reverse]
        rw [h1 x]
        constructor
        · rintro ((h | h) | h) <;> simp only [h, true_or, or_true]
        · rintro ((h | h) | h | h) <;> simp only [h, true_or, or_true]
      have hEset : be.toFinset ∪ (Pe.take i).toFinset =
          insert e (Pe.toFinset ∪ (Pe.take i ++ Qe.drop j).toFinset) := by
        ext f
        have h2 : f ∈ Pe ↔ f ∈ Pe.take i ∨ f ∈ Pe.drop i := by
          rw [← List.mem_append, List.take_append_drop]
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, hbedef, List.mem_append,
          List.mem_cons, List.mem_reverse]
        rw [h2]
        constructor
        · rintro ((h | h | h) | h) <;> simp only [h, true_or, or_true]
        · rintro (h | (h | h) | h | h) <;> simp only [h, true_or, or_true]
      refine ⟨bv, be, (Pv[i]'(by first | assumption | omega)), Pv.take (i+1), Pe.take i, ⟨⟨hcirc, ?_, hmaxB, ?_, hbase⟩, hstem, hsvlast, hsvbv⟩,
        ?_, ?_, Pv, Pe, _, _, ⟨hPp, hPvs, hPes, hPh, hPl⟩, hQ', hVset, hEset⟩
      · rw [hbvlen, Nat.odd_iff]; exact hLodd
      · rw [hbvdef]; exact List.mem_append_left _ (List.mem_drop_iff_getElem.mpr ⟨0, by omega, by simp⟩)
      · rw [List.head?_take]; simpa using hPh
      · rw [hbedef]; simp
