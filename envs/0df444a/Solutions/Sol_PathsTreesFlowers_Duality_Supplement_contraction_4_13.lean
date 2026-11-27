-- Prove2me | solution 1 for PathsTreesFlowers.Duality.Supplement.contraction_4_13
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:23.945857+00:00
-- url     : https://prove2.me/submissions/381304c2-5d23-4b1e-bbec-a65aa7a4a554

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Trees
import Definitions.Def_PathsTreesFlowers_Duality_Shrink

open PathsTreesFlowers
open PathsTreesFlowers.Duality
open PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V) (e : E) (u v : V)
    (hF : IsFloweredTree G M J r e u v)
    (bv : List V) (be : List E) (b : V) (hB : IsBlossom G M bv be b)
    (hcontained : be.toFinset ⊆ insert e J.edges) :
    let P := blockPartition bv.toFinset
    ∃ K : AltTree (shrink G P),
      K.edges = shrinkMatching G P (insert e J.edges) ∧
      K.verts = J.verts.image (toPart P) ∧
      K.inner = (J.inner \ bv.toFinset).image (toPart P) ∧
      K.outer = insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)) ∧
      toPart P b ∈ K.outer ∧
      IsPlantedTree (shrink G P) (shrinkMatching G P M) K (toPart P r) := by
        intro P
        obtain ⟨⟨hvnd, hend, hlen2, hlen, hmap⟩, hodd, hmax, hbmem, hbexp⟩ := hB
        obtain ⟨hplant, huo, hvo, heuv⟩ := hF
        set m := bv.length with hm
        have hm0 : 0 < m := by omega
        have hends : ∀ f, ∃ x y, G.ends f = s(x, y) ∧ x ≠ y := by
          intro f
          induction h : G.ends f using Sym2.ind with
          | h x y =>
            refine ⟨x, y, rfl, ?_⟩
            intro hxy; apply G.loopless f; rw [h, hxy]; exact Sym2.mk_isDiag_iff.2 rfl
        -- block partition facts
        have hTP : ∀ x y, toPart P x = toPart P y ↔ x = y ∨ (x ∈ bv ∧ y ∈ bv) := by
          intro x y
          have h1 : toPart P x = toPart P y ↔ P.part x = P.part y := Subtype.ext_iff
          rw [h1, eq_comm, P.part_eq_iff_mem (P.part_mem.2 (Finset.mem_univ x))]
          show y ∈ (Finpartition.ofSetoid (blockSetoid bv.toFinset)).part x ↔ _
          rw [Finpartition.mem_part_ofSetoid_iff_rel]
          show x = y ∨ (x ∈ bv.toFinset ∧ y ∈ bv.toFinset) ↔ _
          simp
        have hins : ∀ f x y, G.ends f = s(x, y) → (InsidePart G P f ↔ x ∈ bv ∧ y ∈ bv) := by
          intro f x y hf
          constructor
          · rintro ⟨U, hU, hmem⟩
            rw [hf, Finset.mk_mem_sym2_iff] at hmem
            have h1 : P.part x = U := P.part_eq_of_mem hU hmem.1
            have h2 : P.part y = U := P.part_eq_of_mem hU hmem.2
            have h3 : toPart P x = toPart P y := Subtype.ext (h1.trans h2.symm)
            rcases (hTP x y).1 h3 with h | h
            · exfalso; apply G.loopless f; rw [hf, h]; exact Sym2.mk_isDiag_iff.2 rfl
            · exact h
          · rintro ⟨hx, hy⟩
            refine ⟨P.part x, P.part_mem.2 (Finset.mem_univ x), ?_⟩
            rw [hf, Finset.mk_mem_sym2_iff]
            refine ⟨P.mem_part (Finset.mem_univ x), ?_⟩
            have : toPart P x = toPart P y := (hTP x y).2 (Or.inr ⟨hx, hy⟩)
            have h4 : P.part x = P.part y := congrArg Subtype.val this
            rw [h4]; exact P.mem_part (Finset.mem_univ y)
        -- circuit as periodic sequences
        have hlenE : be.length = m := hlen.symm
        let Vf : ℕ → V := fun i => bv[i % m]'(Nat.mod_lt _ hm0)
        let Ef : ℕ → E := fun i => be[i % m]'(by rw [hlenE]; exact Nat.mod_lt _ hm0)
        have hEf : ∀ i, G.ends (Ef i) = s(Vf i, Vf (i + 1)) := by
          intro i
          have hi : i % m < (be.map G.ends).length := by simp [hlenE]; exact Nat.mod_lt _ hm0
          have := List.getElem_of_eq hmap hi
          simp only [List.getElem_map, List.getElem_zipWith, List.getElem_rotate] at this
          rw [this]
          simp only [Vf]
          congr 2
          show (i % m + 1) % m = (i + 1) % m
          conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < m by omega)]
        have hVf_mem : ∀ i, Vf i ∈ bv := fun i => List.getElem_mem _
        have hEf_mem : ∀ i, Ef i ∈ be := fun i => List.getElem_mem _
        have hVf_surj : ∀ x ∈ bv, ∃ i < m, Vf i = x := by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
          exact ⟨i, hi, by simp only [Vf, Nat.mod_eq_of_lt (show i < m from hi)]⟩
        have hEf_surj : ∀ f ∈ be, ∃ i < m, Ef i = f := by
          intro f hf
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
          exact ⟨i, by omega, by simp [Ef, Nat.mod_eq_of_lt (show i < m by omega)]⟩
        have hVf_inj : ∀ i j, Vf i = Vf j → i % m = j % m := by
          intro i j h
          exact (hvnd.getElem_inj_iff).1 h
        have hEf_inj : ∀ i j, Ef i = Ef j → i % m = j % m := by
          intro i j h
          exact (hend.getElem_inj_iff).1 h
        have hoff : ∀ k s t, s < m → t < m → (k + s) % m = (k + t) % m → s = t := by
          intro k s t hs ht h
          have h1 : s ≡ t [MOD m] := Nat.ModEq.add_left_cancel' k h
          unfold Nat.ModEq at h1
          rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at h1
        have hVf_m : ∀ i, Vf (i + m) = Vf i := by
          intro i; simp only [Vf, Nat.add_mod_right]
        -- J facts
        have hJedge : ∀ f ∈ J.edges, ∀ x y, G.ends f = s(x, y) →
            (x ∈ J.inner ↔ y ∉ J.inner) ∧ x ∈ J.verts ∧ y ∈ J.verts := by
          intro f hf x y hxy
          obtain ⟨p, hp, q, hq, hpq⟩ := J.edge_ends f hf
          have hqi : q ∉ J.inner := fun h => Finset.disjoint_left.1 J.disjoint h hq
          rw [hxy] at hpq
          simp only [AltTree.verts]
          rcases Sym2.eq_iff.1 hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨fun _ => hqi, fun _ => hp⟩, Finset.mem_union_left _ hp, Finset.mem_union_right _ hq⟩
          · exact ⟨⟨fun h => absurd h hqi, fun h => absurd hp h⟩, Finset.mem_union_right _ hq,
              Finset.mem_union_left _ hp⟩
        have hout_ni : ∀ x ∈ J.outer, x ∉ J.inner := fun x hx h => Finset.disjoint_left.1 J.disjoint h hx
        have hJe : e ∉ J.edges := by
          intro he
          have := (hJedge e he u v heuv).1
          have h1 := hout_ni u huo
          have h2 := hout_ni v hvo
          tauto
        have hnot_e : ∀ x ∈ J.inner, x ∉ G.ends e := by
          intro x hx h
          rw [heuv, Sym2.mem_iff] at h
          rcases h with rfl | rfl
          · exact hout_ni _ huo hx
          · exact hout_ni _ hvo hx
        have hwalk : ∀ k d, (∀ i < d, Ef (k + i) ∈ J.edges) →
            (Vf (k + d) ∈ J.inner ↔ (Vf k ∈ J.inner ↔ Even d)) := by
          intro k d
          induction d with
          | zero => intro _; simp
          | succ d ih =>
            intro h
            have h1 := ih (fun i hi => h i (by omega))
            have h2 := (hJedge _ (h d (by omega)) _ _ (hEf (k + d))).1
            rw [Nat.even_add_one, show k + (d + 1) = k + d + 1 by omega]
            tauto
        have hEf_J : ∀ i, Ef i ≠ e → Ef i ∈ J.edges := by
          intro i hi
          have := hcontained (List.mem_toFinset.2 (hEf_mem i))
          rcases Finset.mem_insert.1 this with h | h
          · exact absurd h hi
          · exact h
        have he_be : e ∈ be := by
          by_contra hne
          have h1 := hwalk 0 m (fun i _ => hEf_J _ (fun h => hne (h ▸ hEf_mem _)))
          rw [hVf_m 0] at h1
          have : ¬ Even m := Nat.not_even_iff_odd.2 hodd
          tauto
        have hVoff : ∀ k s t, s < m → t < m → Vf (k + s) = Vf (k + t) → s = t :=
          fun k s t hs ht h => hoff k s t hs ht (hVf_inj _ _ h)
        have hEoff : ∀ k s t, s < m → t < m → Ef (k + s) = Ef (k + t) → s = t :=
          fun k s t hs ht h => hoff k s t hs ht (hEf_inj _ _ h)
        -- inner vertices of the blossom have all their tree edges in the blossom
        have hinnerbv : ∀ x ∈ J.inner, x ∈ bv → ∀ f ∈ J.edges, x ∈ G.ends f → f ∈ be := by
          intro x hx hxb f hf hxf
          obtain ⟨i, hi, rfl⟩ := hVf_surj x hxb
          have hf1 : Vf i ∈ G.ends (Ef i) := by rw [hEf]; exact Sym2.mem_mk_left _ _
          have hf2 : Vf i ∈ G.ends (Ef (i + (m - 1))) := by
            rw [hEf, show i + (m - 1) + 1 = i + m by omega, hVf_m]; exact Sym2.mem_mk_right _ _
          have hne : Ef i ≠ Ef (i + (m - 1)) := by
            intro h
            have := hEoff i 0 (m - 1) hm0 (by omega) (by simpa using h)
            omega
          have hJ1 : Ef i ∈ J.edges := hEf_J _ (fun h => hnot_e _ hx (h ▸ hf1))
          have hJ2 : Ef (i + (m - 1)) ∈ J.edges := hEf_J _ (fun h => hnot_e _ hx (h ▸ hf2))
          have hcard := J.inner_deg _ hx
          have hsub : ({Ef i, Ef (i + (m - 1))} : Finset E) ⊆ J.edges.filter (fun e => Vf i ∈ G.ends e) := by
            intro g hg
            simp only [Finset.mem_insert, Finset.mem_singleton] at hg
            rcases hg with rfl | rfl
            · exact Finset.mem_filter.2 ⟨hJ1, hf1⟩
            · exact Finset.mem_filter.2 ⟨hJ2, hf2⟩
          have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hne])
          have : f ∈ ({Ef i, Ef (i + (m - 1))} : Finset E) := by
            rw [heq]; exact Finset.mem_filter.2 ⟨hf, hxf⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl <;> exact hEf_mem _
        have hbe_ins : ∀ f ∈ be, InsidePart G P f := by
          intro f hf
          obtain ⟨i, _, rfl⟩ := hEf_surj f hf
          exact (hins _ _ _ (hEf i)).2 ⟨hVf_mem _, hVf_mem _⟩
        have hins_iff : ∀ f ∈ insert e J.edges, InsidePart G P f ↔ f ∈ be := by
          intro f hf
          refine ⟨fun h => ?_, hbe_ins f⟩
          rcases Finset.mem_insert.1 hf with rfl | hfJ
          · exact he_be
          · obtain ⟨p, hp, q, _, hpq⟩ := J.edge_ends f hfJ
            have := (hins _ _ _ hpq).1 h
            exact hinnerbv p hp this.1 f hfJ (by rw [hpq]; exact Sym2.mem_mk_left _ _)
        -- counting: a matching with ends in W has at most |W|/2 edges
        have hcount : ∀ F : Finset E, IsMatching G F → ∀ W : Finset V,
            (∀ f ∈ F, ∀ x ∈ G.ends f, x ∈ W) → 2 * F.card ≤ W.card := by
          intro F hFm W hW
          have hdisj : (↑F : Set E).PairwiseDisjoint (fun f => W.filter (fun x => x ∈ G.ends f)) := by
            intro f hf g hg hfg
            simp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro x hx hx'
            exact hFm f hf g hg hfg x (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hx').2
          have h1 := Finset.card_biUnion hdisj
          have h2 : ∀ f ∈ F, (W.filter (fun x => x ∈ G.ends f)).card = 2 := by
            intro f hf
            obtain ⟨x, y, hxy, hne⟩ := hends f
            have : W.filter (fun z => z ∈ G.ends f) = {x, y} := by
              ext z
              simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, hxy, Sym2.mem_iff]
              constructor
              · exact fun h => h.2
              · intro h
                refine ⟨hW f hf z ?_, h⟩
                rw [hxy, Sym2.mem_iff]; exact h
            rw [this, Finset.card_pair hne]
          rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h1
          have h3 : F.biUnion (fun f => W.filter (fun x => x ∈ G.ends f)) ⊆ W := by
            intro x hx
            obtain ⟨f, _, hx⟩ := Finset.mem_biUnion.1 hx
            exact (Finset.mem_filter.1 hx).1
          have := Finset.card_le_card h3
          rw [h1] at this; linarith
        have hbvcard : bv.toFinset.card = m := List.toFinset_card_of_nodup hvnd
        have hends_bv : ∀ f ∈ be, ∀ x ∈ G.ends f, x ∈ bv := by
          intro f hf x hx
          obtain ⟨i, _, rfl⟩ := hEf_surj f hf
          rw [hEf, Sym2.mem_iff] at hx
          rcases hx with rfl | rfl <;> exact hVf_mem _
        -- the rotated matchings of the odd circuit
        let C : ℕ → Finset E := fun k => (Finset.range ((m - 1) / 2)).image (fun j => Ef (k + (1 + 2 * j)))
        have hCsub : ∀ k, C k ⊆ be.toFinset := by
          intro k f hf
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hf
          exact List.mem_toFinset.2 (hEf_mem _)
        have hCcard : ∀ k, (C k).card = (m - 1) / 2 := by
          intro k
          rw [Finset.card_image_of_injOn, Finset.card_range]
          intro j hj j' hj' h
          simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
          have := hEoff k _ _ (by omega) (by omega) h
          omega
        have hCends : ∀ k, ∀ f ∈ C k, ∃ j, j < (m - 1) / 2 ∧ f = Ef (k + (1 + 2 * j)) ∧
            G.ends f = s(Vf (k + (1 + 2 * j)), Vf (k + (2 + 2 * j))) := by
          intro k f hf
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hf
          refine ⟨j, Finset.mem_range.1 hj, rfl, ?_⟩
          rw [hEf, show k + (1 + 2 * j) + 1 = k + (2 + 2 * j) by omega]
        have hCavoid : ∀ k, ∀ f ∈ C k, Vf k ∉ G.ends f := by
          intro k f hf hk
          obtain ⟨j, hj, _, hends'⟩ := hCends k f hf
          rw [hends', Sym2.mem_iff] at hk
          rcases hk with h | h
          · have := hVoff k 0 (1 + 2 * j) hm0 (by omega) (by simpa using h); omega
          · have := hVoff k 0 (2 + 2 * j) hm0 (by omega) (by simpa using h); omega
        have hCmatch : ∀ k, IsMatching G (C k) := by
          intro k f hf g hg hfg x hxf hxg
          obtain ⟨j, hj, rfl, hf'⟩ := hCends k f hf
          obtain ⟨j', hj', rfl, hg'⟩ := hCends k g hg
          have hjj : j ≠ j' := fun h => hfg (by rw [h])
          rw [hf', Sym2.mem_iff] at hxf
          rw [hg', Sym2.mem_iff] at hxg
          rcases hxf with rfl | rfl <;> rcases hxg with h | h
          · have := hVoff k _ _ (by omega) (by omega) h; omega
          · have := hVoff k _ _ (by omega) (by omega) h; omega
          · have := hVoff k _ _ (by omega) (by omega) h; omega
          · have := hVoff k _ _ (by omega) (by omega) h; omega
        have hMbe_match : IsMatching G (M ∩ be.toFinset) :=
          fun f hf g hg => hM f (Finset.mem_inter.1 hf).1 g (Finset.mem_inter.1 hg).1
        obtain ⟨t, ht⟩ := hodd
        have hMbe_le : (M ∩ be.toFinset).card ≤ (m - 1) / 2 := by
          have := hcount _ hMbe_match (bv.toFinset.erase b) (by
            intro f hf x hx
            refine Finset.mem_erase.2 ⟨?_, List.mem_toFinset.2 (hends_bv f (List.mem_toFinset.1 (Finset.mem_inter.1 hf).2) x hx)⟩
            rintro rfl; exact hbexp f hf hx)
          rw [Finset.card_erase_of_mem (List.mem_toFinset.2 hbmem), hbvcard] at this
          omega
        have hcover : ∀ x ∈ bv, x ≠ b → ∃ f ∈ M ∩ be.toFinset, x ∈ G.ends f := by
          intro x hx hxb
          by_contra hno
          push Not at hno
          obtain ⟨kb, _, hkb⟩ := hVf_surj b hbmem
          have h1 := hmax.2.2 (C kb) (hCsub kb) (hCmatch kb)
          rw [hCcard] at h1
          have h2 := hcount _ hMbe_match ((bv.toFinset.erase b).erase x) (by
            intro f hf y hy
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_,
              List.mem_toFinset.2 (hends_bv f (List.mem_toFinset.1 (Finset.mem_inter.1 hf).2) y hy)⟩⟩
            · rintro rfl; exact hno f hf hy
            · rintro rfl; exact hbexp f hf hy)
          rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxb, List.mem_toFinset.2 hx⟩),
            Finset.card_erase_of_mem (List.mem_toFinset.2 hbmem), hbvcard] at h2
          omega
        have hMleave : ∀ f ∈ M, ¬ InsidePart G P f → ∀ a ∈ G.ends f, a ∈ bv → a = b := by
          intro f hfM hfi a ha hab
          by_contra hne
          obtain ⟨g, hg, hag⟩ := hcover a hab hne
          have hgi := hbe_ins g (List.mem_toFinset.1 (Finset.mem_inter.1 hg).2)
          have hfg : f ≠ g := fun h => hfi (h ▸ hgi)
          exact hM f hfM g (Finset.mem_inter.1 hg).1 hfg a ha hag
        have hbv_verts : ∀ x ∈ bv, x ∈ J.verts := by
          intro x hx
          obtain ⟨i, _, rfl⟩ := hVf_surj x hx
          by_cases hie : Ef i = e
          · have h1 : Vf i ∈ G.ends e := by rw [← hie, hEf]; exact Sym2.mem_mk_left _ _
            rw [heuv, Sym2.mem_iff] at h1
            simp only [AltTree.verts]
            rcases h1 with h | h <;> rw [h] <;> exact Finset.mem_union_right _ ‹_›
          · exact ((hJedge _ (hEf_J i hie) _ _ (hEf i)).2.1)
        have hKedge : ∀ f ∈ insert e J.edges, ¬ InsidePart G P f → f ∈ J.edges ∧ f ∉ be := by
          intro f hf hfi
          have hfb : f ∉ be := fun h => hfi (hbe_ins f h)
          refine ⟨?_, hfb⟩
          rcases Finset.mem_insert.1 hf with rfl | h
          · exact absurd he_be hfb
          · exact h
        have hshends : ∀ f' : {f : E // ¬ InsidePart G P f},
            (shrink G P).ends f' = Sym2.map (toPart P) (G.ends f'.1) := fun _ => rfl
        have hmemKE : ∀ f' : {f : E // ¬ InsidePart G P f},
            f' ∈ shrinkMatching G P (insert e J.edges) ↔ f'.1 ∈ insert e J.edges :=
          fun f' => Finset.mem_subtype
        have hTPs : ∀ x y, y ∉ bv → (toPart P x = toPart P y ↔ x = y) := by
          intro x y hy
          rw [hTP]; constructor
          · rintro (h | h); exact h; exact absurd h.2 hy
          · exact Or.inl
        have hverts : (J.inner \ bv.toFinset).image (toPart P) ∪
            insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)) = J.verts.image (toPart P) := by
          ext X
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_sdiff,
            List.mem_toFinset, AltTree.verts]
          constructor
          · rintro ((⟨x, ⟨hx, _⟩, rfl⟩) | rfl | ⟨x, ⟨hx, _⟩, rfl⟩)
            · exact ⟨x, Or.inl hx, rfl⟩
            · have := hbv_verts b hbmem
              simp only [AltTree.verts, Finset.mem_union] at this
              exact ⟨b, this, rfl⟩
            · exact ⟨x, Or.inr hx, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            by_cases hxb : x ∈ bv
            · exact Or.inr (Or.inl ((hTP x b).2 (Or.inr ⟨hxb, hbmem⟩)))
            · rcases hx with hx | hx
              · exact Or.inl ⟨x, ⟨hx, hxb⟩, rfl⟩
              · exact Or.inr (Or.inr ⟨x, ⟨hx, hxb⟩, rfl⟩)
        have hdisj : Disjoint ((J.inner \ bv.toFinset).image (toPart P))
            (insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P))) := by
          rw [Finset.disjoint_left]
          intro X hX hX'
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hX
          rw [Finset.mem_sdiff, List.mem_toFinset] at hx
          rcases Finset.mem_insert.1 hX' with h | h
          · rcases (hTP x b).1 h with h | h
            · exact hx.2 (h ▸ hbmem)
            · exact hx.2 h.1
          · obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 h
            rw [Finset.mem_sdiff, List.mem_toFinset] at hy
            rw [hTPs _ _ hx.2] at hxy
            subst hxy
            exact hout_ni _ hy.1 hx.1
        have hedge_ends : ∀ f' ∈ shrinkMatching G P (insert e J.edges),
            ∃ X ∈ (J.inner \ bv.toFinset).image (toPart P),
            ∃ Y ∈ insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)),
              (shrink G P).ends f' = s(X, Y) := by
          intro f' hf'
          obtain ⟨hfJ, hfb⟩ := hKedge f'.1 ((hmemKE f').1 hf') f'.2
          obtain ⟨p, hp, q, hq, hpq⟩ := J.edge_ends _ hfJ
          have hpb : p ∉ bv := fun h => hfb (hinnerbv p hp h _ hfJ (by rw [hpq]; exact Sym2.mem_mk_left _ _))
          refine ⟨toPart P p, Finset.mem_image.2 ⟨p, by simp [hp, hpb], rfl⟩, toPart P q, ?_, ?_⟩
          · by_cases hqb : q ∈ bv
            · rw [(hTP q b).2 (Or.inr ⟨hqb, hbmem⟩)]; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨q, by simp [hq, hqb], rfl⟩)
          · rw [hshends, hpq, Sym2.map_mk]
        have hinner_deg : ∀ X ∈ (J.inner \ bv.toFinset).image (toPart P),
            ((shrinkMatching G P (insert e J.edges)).filter (fun f' => X ∈ (shrink G P).ends f')).card = 2 := by
          intro X hX
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hX
          rw [Finset.mem_sdiff, List.mem_toFinset] at hx
          rw [← J.inner_deg x hx.1, ← Finset.card_map (Function.Embedding.subtype _)]
          congr 1
          ext f
          simp only [Finset.mem_map, Finset.mem_filter, Function.Embedding.coe_subtype]
          constructor
          · rintro ⟨f', ⟨hf', hX'⟩, rfl⟩
            rw [hshends, Sym2.mem_map] at hX'
            obtain ⟨a, ha, hax⟩ := hX'
            rw [hTPs _ _ hx.2] at hax
            subst hax
            exact ⟨(hKedge _ ((hmemKE f').1 hf') f'.2).1, ha⟩
          · rintro ⟨hfJ, hxf⟩
            have hni : ¬ InsidePart G P f := by
              intro h
              obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.1 hxf
              exact hx.2 ((hins f x y hy).1 h).1
            refine ⟨⟨f, hni⟩, ⟨(hmemKE _).2 (Finset.mem_insert_of_mem hfJ), ?_⟩, rfl⟩
            rw [hshends, Sym2.mem_map]
            exact ⟨x, hxf, rfl⟩
        have hconn : ((J.inner \ bv.toFinset).image (toPart P) ∪
            insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P))).Nonempty ∧
            ∀ X ∈ (J.inner \ bv.toFinset).image (toPart P) ∪
              insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)),
            ∀ Y ∈ (J.inner \ bv.toFinset).image (toPart P) ∪
              insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)),
            Relation.ReflTransGen (fun A B => ∃ f' ∈ shrinkMatching G P (insert e J.edges),
              (shrink G P).ends f' = s(A, B)) X Y := by
          refine ⟨⟨toPart P b, Finset.mem_union_right _ (Finset.mem_insert_self _ _)⟩, ?_⟩
          intro X hX Y hY
          rw [hverts] at hX hY
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hX
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hY
          have hxy := J.connected.2 x hx y hy
          refine (Relation.ReflTransGen.lift' (toPart P) ?_) x y hxy
          intro a c hac
          obtain ⟨f, hf, hfac⟩ := hac
          by_cases hi : InsidePart G P f
          · have := (hins f a c hfac).1 hi
            show Relation.ReflTransGen _ (toPart P a) (toPart P c)
            rw [(hTP a c).2 (Or.inr this)]
          · apply Relation.ReflTransGen.single
            refine ⟨⟨f, hi⟩, (hmemKE _).2 (Finset.mem_insert_of_mem hf), ?_⟩
            rw [hshends]; simp only [hfac, Sym2.map_mk]
        have hbs_sub : bv.toFinset ⊆ J.verts := fun x hx => hbv_verts x (List.mem_toFinset.1 hx)
        have hcardv : ((J.inner \ bv.toFinset).image (toPart P) ∪
            insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P))).card =
            (shrinkMatching G P (insert e J.edges)).card + 1 := by
          rw [hverts]
          have h1 : J.verts.image (toPart P) = insert (toPart P b) ((J.verts \ bv.toFinset).image (toPart P)) := by
            ext X
            rw [Finset.mem_insert, Finset.mem_image, Finset.mem_image]
            constructor
            · rintro ⟨x, hx, rfl⟩
              by_cases hxb : x ∈ bv
              · exact Or.inl ((hTP x b).2 (Or.inr ⟨hxb, hbmem⟩))
              · exact Or.inr ⟨x, Finset.mem_sdiff.2 ⟨hx, fun h => hxb (List.mem_toFinset.1 h)⟩, rfl⟩
            · rintro (rfl | ⟨x, hx, rfl⟩)
              · exact ⟨b, hbv_verts b hbmem, rfl⟩
              · exact ⟨x, (Finset.mem_sdiff.1 hx).1, rfl⟩
          have h2 : toPart P b ∉ (J.verts \ bv.toFinset).image (toPart P) := by
            intro h
            obtain ⟨x, hx, hxb⟩ := Finset.mem_image.1 h
            have hx2 := fun h => (Finset.mem_sdiff.1 hx).2 (List.mem_toFinset.2 h)
            rcases (hTP x b).1 hxb with h | h
            · exact hx2 (h ▸ hbmem)
            · exact hx2 h.1
          have h3 : ((J.verts \ bv.toFinset).image (toPart P)).card = (J.verts \ bv.toFinset).card := by
            apply Finset.card_image_of_injOn
            intro x hx y hy hxy
            have hy2 := fun h => (Finset.mem_sdiff.1 hy).2 (List.mem_toFinset.2 h)
            exact (hTPs x y hy2).1 hxy
          have h4 : (J.verts \ bv.toFinset).card = J.verts.card - bv.toFinset.card :=
            Finset.card_sdiff_of_subset hbs_sub
          have h5 : J.verts.card = J.edges.card + 1 := J.card_verts
          have h6 : (shrinkMatching G P (insert e J.edges)).card = (insert e J.edges \ be.toFinset).card := by
            unfold shrinkMatching
            rw [Finset.card_subtype]
            congr 1
            ext f
            rw [Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset]
            constructor
            · rintro ⟨hf, hi⟩; exact ⟨hf, fun h => hi ((hins_iff f hf).2 h)⟩
            · rintro ⟨hf, hi⟩; exact ⟨hf, fun h => hi ((hins_iff f hf).1 h)⟩
          have h7 : (insert e J.edges \ be.toFinset).card = (insert e J.edges).card - be.toFinset.card :=
            Finset.card_sdiff_of_subset hcontained
          have h8 : (insert e J.edges).card = J.edges.card + 1 := Finset.card_insert_of_notMem hJe
          have h9 : be.toFinset.card = m := by rw [List.toFinset_card_of_nodup hend, hlenE]
          have h10 := Finset.card_le_card hbs_sub
          rw [h1, Finset.card_insert_of_notMem h2, h3, h4, h6, h7, h8, h9, hbvcard]
          rw [hbvcard] at h10
          omega
        let K : AltTree (shrink G P) := ⟨(J.inner \ bv.toFinset).image (toPart P),
          insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P)),
          shrinkMatching G P (insert e J.edges), hdisj, hedge_ends, hinner_deg, hconn, hcardv⟩
        refine ⟨K, rfl, hverts, rfl, rfl, Finset.mem_insert_self _ _, ?_⟩
        have hmemM' : ∀ f' : {f : E // ¬ InsidePart G P f},
            f' ∈ shrinkMatching G P M ↔ f'.1 ∈ M := fun f' => Finset.mem_subtype
        have hrexp : ∀ g ∈ M, r ∉ G.ends g := hplant.2.2.2
        have hexp : ∀ f' ∈ shrinkMatching G P M, toPart P r ∉ (shrink G P).ends f' := by
          intro f' hf' h
          rw [hshends, Sym2.mem_map] at h
          obtain ⟨a, ha, har⟩ := h
          have hfM := (hmemM' f').1 hf'
          rcases (hTP a r).1 har with rfl | ⟨hab, hrb⟩
          · exact hrexp _ hfM ha
          · have hab' := hMleave _ hfM f'.2 a ha hab
            by_cases hrb' : r = b
            · subst hab'; subst hrb'; exact hrexp _ hfM ha
            · obtain ⟨g, hg, hrg⟩ := hcover r hrb hrb'
              exact hrexp g (Finset.mem_inter.1 hg).1 hrg
        have hKE : K.edges = shrinkMatching G P (insert e J.edges) := rfl
        have hunion : ∀ A B : Finset E, IsMatching G A → IsMatching G B →
            (∀ f ∈ A, ∀ g ∈ B, ∀ w ∈ G.ends f, w ∉ G.ends g) → IsMatching G (A ∪ B) := by
          intro A B hA hB hAB f hf g hg hfg w hwf hwg
          rcases Finset.mem_union.1 hf with hf | hf <;> rcases Finset.mem_union.1 hg with hg | hg
          · exact hA f hf g hg hfg w hwf hwg
          · exact hAB f hf g hg w hwf hwg
          · exact hAB g hg f hf w hwg hwf
          · exact hB f hf g hg hfg w hwf hwg
        refine ⟨⟨Finset.inter_subset_right, ?_, ?_⟩, ?_, fun f' hf' => hexp f' (Finset.mem_inter.1 hf').1, hexp⟩
        · -- matching
          intro f' hf' g' hg' hne X hXf hXg
          have hfM := (hmemM' f').1 (Finset.mem_inter.1 hf').1
          have hgM := (hmemM' g').1 (Finset.mem_inter.1 hg').1
          have hfg : f'.1 ≠ g'.1 := fun h => hne (Subtype.ext h)
          rw [hshends, Sym2.mem_map] at hXf hXg
          obtain ⟨a, ha, rfl⟩ := hXf
          obtain ⟨c, hc, hca⟩ := hXg
          rcases (hTP c a).1 hca with rfl | ⟨hcb, hab⟩
          · exact hM _ hfM _ hgM hfg c ha hc
          · have h1 := hMleave _ hfM f'.2 a ha hab
            have h2 := hMleave _ hgM g'.2 c hc hcb
            subst h1; subst h2
            exact hM _ hfM _ hgM hfg _ ha hc
        · -- maximality
          intro N hNsub hNm
          rw [hKE] at hNsub
          set N₀ := N.map (Function.Embedding.subtype _) with hN₀def
          have hN₀ : ∀ f ∈ N₀, ∃ f' ∈ N, f'.1 = f := by
            intro f hf
            obtain ⟨f', hf', rfl⟩ := Finset.mem_map.1 hf
            exact ⟨f', hf', rfl⟩
          have hN₀J : ∀ f ∈ N₀, f ∈ J.edges ∧ f ∉ be ∧ ¬ InsidePart G P f := by
            intro f hf
            obtain ⟨f', hf', rfl⟩ := hN₀ f hf
            have := hKedge _ ((hmemKE f').1 (hNsub hf')) f'.2
            exact ⟨this.1, this.2, f'.2⟩
          have hN₀touch : ∀ f ∈ N₀, ∀ g ∈ N₀, ∀ x ∈ G.ends f, ∀ y ∈ G.ends g,
              toPart P x = toPart P y → f = g := by
            intro f hf g hg x hx y hy hxy
            obtain ⟨f', hf', rfl⟩ := hN₀ f hf
            obtain ⟨g', hg', rfl⟩ := hN₀ g hg
            by_contra hne
            have hne' : f' ≠ g' := fun h => hne (h ▸ rfl)
            apply hNm f' hf' g' hg' hne' (toPart P x)
            · rw [hshends, Sym2.mem_map]; exact ⟨x, hx, rfl⟩
            · rw [hshends, Sym2.mem_map]; exact ⟨y, hy, hxy.symm⟩
          have hN₀m : IsMatching G N₀ := by
            intro f hf g hg hfg w hwf hwg
            exact hfg (hN₀touch f hf g hg w hwf w hwg rfl)
          set Q := (M ∩ J.edges).filter (InsidePart G P) with hQdef
          have hsplit : (M ∩ J.edges).card =
              (shrinkMatching G P M ∩ K.edges).card + Q.card := by
            have h1 := Finset.card_filter_add_card_filter_not (s := M ∩ J.edges) (InsidePart G P)
            have h2 : (shrinkMatching G P M ∩ K.edges).card =
                ((M ∩ J.edges).filter (fun f => ¬ InsidePart G P f)).card := by
              rw [← Finset.card_map (Function.Embedding.subtype _)]
              congr 1
              ext f
              simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_inter,
                Function.Embedding.coe_subtype]
              constructor
              · rintro ⟨f', ⟨hf1, hf2⟩, rfl⟩
                exact ⟨⟨(hmemM' f').1 hf1, (hKedge _ ((hmemKE f').1 hf2) f'.2).1⟩, f'.2⟩
              · rintro ⟨⟨hfM, hfJ⟩, hi⟩
                exact ⟨⟨f, hi⟩, ⟨(hmemM' _).2 hfM, (hmemKE _).2 (Finset.mem_insert_of_mem hfJ)⟩, rfl⟩
            rw [h2, ← h1, add_comm]
          have hQ : ∀ f ∈ Q, f ∈ M ∧ f ∈ J.edges ∧ f ∈ be := by
            intro f hf
            rw [hQdef, Finset.mem_filter, Finset.mem_inter] at hf
            exact ⟨hf.1.1, hf.1.2, (hins_iff f (Finset.mem_insert_of_mem hf.1.2)).1 hf.2⟩
          have hQcard : Q.card ≤ (m - 1) / 2 := by
            refine le_trans (Finset.card_le_card ?_) hMbe_le
            intro f hf
            have := hQ f hf
            exact Finset.mem_inter.2 ⟨this.1, List.mem_toFinset.2 this.2.2⟩
          have hJmax := hplant.1.2.2
          have hfinish : ∀ D : Finset E, D ⊆ J.edges → IsMatching G D → Q.card ≤ D.card →
              (∀ f ∈ N₀, ∀ g ∈ D, ∀ w ∈ G.ends f, w ∉ G.ends g) →
              N.card ≤ (shrinkMatching G P M ∩ K.edges).card := by
            intro D hDJ hDm hQD hcross
            have hU := hunion N₀ D hN₀m hDm hcross
            have hUJ : N₀ ∪ D ⊆ J.edges := by
              intro f hf
              rcases Finset.mem_union.1 hf with hf | hf
              · exact (hN₀J f hf).1
              · exact hDJ hf
            have hle := hJmax _ hUJ hU
            have hdisjND : Disjoint N₀ D := by
              rw [Finset.disjoint_left]
              intro f hf hfD
              obtain ⟨x, y, hxy, _⟩ := hends f
              exact hcross f hf f hfD x (by rw [hxy]; exact Sym2.mem_mk_left _ _)
                (by rw [hxy]; exact Sym2.mem_mk_left _ _)
            rw [Finset.card_union_of_disjoint hdisjND] at hle
            have : N₀.card = N.card := Finset.card_map _
            omega
          by_cases hcase : ∃ f ∈ N₀, ∃ a ∈ G.ends f, a ∈ bv ∧ a ≠ b
          · obtain ⟨f₀, hf₀, a, ha, hab, hane⟩ := hcase
            have hai : a ∉ J.inner := fun h => (hN₀J f₀ hf₀).2.1 (hinnerbv a h hab f₀ (hN₀J f₀ hf₀).1 ha)
            obtain ⟨k, _, rfl⟩ := hVf_surj a hab
            refine hfinish (C k) ?_ (hCmatch k) (by rw [hCcard]; exact hQcard) ?_
            · intro g hg
              obtain ⟨j, hj, rfl, _⟩ := hCends k g hg
              apply hEf_J
              intro hge
              have hw := hwalk k (1 + 2 * j) (by
                intro i hi
                apply hEf_J
                intro hie
                have := hEoff k i (1 + 2 * j) (by omega) (by omega) (hie.trans hge.symm)
                omega)
              have hev : ¬ Even (1 + 2 * j) := by
                rw [Nat.not_even_iff_odd]; exact ⟨j, by ring⟩
              have hin : Vf (k + (1 + 2 * j)) ∈ J.inner := by tauto
              apply hnot_e _ hin
              rw [← hge, hEf]; exact Sym2.mem_mk_left _ _
            · intro f hf g hg w hwf hwg
              have hwb : w ∈ bv := hends_bv g (hCsub k hg |> List.mem_toFinset.1) w hwg
              have hff : f = f₀ := hN₀touch f hf f₀ hf₀ w hwf (Vf k) ha ((hTP _ _).2 (Or.inr ⟨hwb, hab⟩))
              subst hff
              by_cases hwa : w = Vf k
              · subst hwa; exact hCavoid k g hg hwg
              · have := (Sym2.mem_and_mem_iff hwa).1 ⟨hwf, ha⟩
                exact (hN₀J f hf).2.2 ((hins f w (Vf k) this).2 ⟨hwb, hab⟩)
          · push Not at hcase
            refine hfinish Q (fun f hf => (hQ f hf).2.1) ?_ le_rfl ?_
            · intro f hf g hg
              exact hM f (hQ f hf).1 g (hQ g hg).1
            · intro f hf g hg w hwf hwg
              have hwb : w ∈ bv := hends_bv g (hQ g hg).2.2 w hwg
              have := hcase f hf w hwf hwb
              subst this
              exact hbexp g (Finset.mem_inter.2 ⟨(hQ g hg).1, List.mem_toFinset.2 (hQ g hg).2.2⟩) hwg
        · show toPart P r ∈ (J.inner \ bv.toFinset).image (toPart P) ∪
            insert (toPart P b) ((J.outer \ bv.toFinset).image (toPart P))
          rw [hverts]; exact Finset.mem_image_of_mem _ hplant.2.1
