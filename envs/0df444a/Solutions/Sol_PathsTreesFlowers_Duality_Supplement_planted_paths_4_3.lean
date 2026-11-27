-- Prove2me | solution 1 for PathsTreesFlowers.Duality.Supplement.planted_paths_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:44.793704+00:00
-- url     : https://prove2.me/submissions/e8ddd4ce-c6ca-49ae-aa04-a2ad023a9d3e

import Mathlib
import Definitions.Def_PathsTreesFlowers_Duality_Supplement_Paths

open PathsTreesFlowers
open PathsTreesFlowers.Duality
open PathsTreesFlowers.Duality.Supplement

open EdmondsMatching65.Polyhedron (IsMatching)

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (J : AltTree G) (r : V)
    (hJ : IsPlantedTree G M J r) (v : V) (hv : v ∈ J.outer) :
    ∃ rv re, PathIn G J.toSub r v rv re ∧ IsStem G M rv re ∧
      (∀ wv we, PathIn G J.toSub r v wv we → wv = rv ∧ we = re) ∧
      ∀ pv pe, IsAlternatingPath G M pv pe → pv.toFinset ⊆ J.verts →
        pe.toFinset ⊆ J.edges → MatchingEnd M v pv pe → IsSubpath pv pe rv re := by
          classical
          obtain ⟨hmax, hrV, hrN, hrexp⟩ := hJ
          have hVdef : J.verts = J.inner ∪ J.outer := rfl
          have hvV : v ∈ J.verts := Finset.mem_union_right _ hv
          -- walks
          let W : ℕ → V → Prop := fun n x => ∃ f : ℕ → V, f 0 = r ∧ f n = x ∧
            ∀ i < n, ∃ e ∈ J.edges, G.ends e = s(f i, f (i+1))
          have hext : ∀ n b c, W n b → (∃ e ∈ J.edges, G.ends e = s(b, c)) → W (n+1) c := by
            rintro n b c ⟨f, hf0, hfn, hf⟩ hbc
            refine ⟨fun i => if i ≤ n then f i else c, by simp [hf0], by simp, ?_⟩
            intro i hi
            by_cases hin : i < n
            · have := hf i hin
              simpa [show i ≤ n by omega, show i + 1 ≤ n by omega] using this
            · have : i = n := by omega
              subst this
              simpa [hfn] using hbc
          have hreach' : ∀ x, Relation.ReflTransGen (fun a b => ∃ e ∈ J.edges, G.ends e = s(a, b)) r x →
              ∃ n, W n x := by
            intro x h
            induction h with
            | refl => exact ⟨0, fun _ => r, rfl, rfl, by intro i hi; omega⟩
            | tail _ hbc ih =>
              obtain ⟨n, hn⟩ := ih
              exact ⟨n+1, hext n _ _ hn hbc⟩
          have hreach : ∀ x ∈ J.verts, ∃ n, W n x := fun x hx => hreach' x (J.connected.2 r hrV x hx)
          have hedgeV : ∀ e ∈ J.edges, ∀ x ∈ G.ends e, x ∈ J.verts := by
            intro e he x hx
            obtain ⟨a, ha, b, hb, hab⟩ := J.edge_ends e he
            rw [hab, Sym2.mem_iff] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_union_left _ ha
            · exact Finset.mem_union_right _ hb
          obtain ⟨d, hd⟩ : ∃ d : V → ℕ, ∀ x ∈ J.verts, W (d x) x ∧ ∀ n, W n x → d x ≤ n := by
            refine ⟨fun x => if h : ∃ n, W n x then Nat.find h else 0, ?_⟩
            intro x hx
            have h := hreach x hx
            simp only [dif_pos h]
            exact ⟨Nat.find_spec h, fun n hn => Nat.find_min' h hn⟩
          have hdr : d r = 0 := by
            have := (hd r hrV).2 0 ⟨fun _ => r, rfl, rfl, by intro i hi; omega⟩
            omega
          have hd0 : ∀ x ∈ J.verts, d x = 0 → x = r := by
            intro x hx h0
            obtain ⟨f, hf0, hfn, -⟩ := (hd x hx).1
            rw [h0] at hfn
            rw [← hfn, hf0]
          have hkey : ∀ x ∈ J.verts, x ≠ r → ∃ y e, e ∈ J.edges ∧ G.ends e = s(x, y) ∧ y ∈ J.verts ∧
              d y + 1 = d x := by
            intro x hx hxr
            obtain ⟨⟨f, hf0, hfn, hf⟩, hmin⟩ := hd x hx
            obtain ⟨m, hm⟩ : ∃ m, d x = m + 1 := by
              rcases Nat.eq_zero_or_eq_succ_pred (d x) with h | h
              · exact absurd (hd0 x hx h) hxr
              · exact ⟨_, h⟩
            rw [hm] at hfn hf
            obtain ⟨e, he, hee⟩ := hf m (by omega)
            rw [hfn] at hee
            have hyV : f m ∈ J.verts := hedgeV e he (f m) (by rw [hee]; exact Sym2.mem_mk_left _ _)
            have hWm : W m (f m) := ⟨f, hf0, rfl, fun i hi => hf i (by omega)⟩
            have h1 := (hd _ hyV).2 m hWm
            have h2 := hmin _ (hext _ _ _ (hd _ hyV).1 ⟨e, he, hee⟩)
            exact ⟨f m, e, he, by rw [hee, Sym2.eq_swap], hyV, by omega⟩
          by_cases hEn : ¬ Nonempty E
          · have hvr : v = r := by
              by_contra hvr
              obtain ⟨y, e, -⟩ := hkey v hvV hvr
              exact hEn ⟨e⟩
            subst hvr
            have hle : ∀ l : List E, l = [] := by
              intro l; cases l with
              | nil => rfl
              | cons e _ => exact absurd ⟨e⟩ hEn
            refine ⟨[v], [], ⟨⟨by simp, by simp, by simp⟩, by intro x hx; simp at hx; rw [hx]; exact hvV, by simp, rfl, rfl⟩,
              ⟨⟨⟨by simp, by simp, by simp⟩, by simp⟩, by simpa using hrexp, by simp⟩, ?_, ?_⟩
            · rintro wv we ⟨⟨-, hlen, -⟩, -, -, hh, -⟩
              rw [hle we] at hlen ⊢
              refine ⟨?_, rfl⟩
              match wv, hlen, hh with
              | [a], _, hh => simpa using hh
            · rintro pv pe - - - hme
              rw [hle pe] at hme
              simp [MatchingEnd] at hme
          rw [not_not] at hEn
          have hpg : ∀ x, ∃ y e, x ∈ J.verts → x ≠ r → e ∈ J.edges ∧ G.ends e = s(x, y) ∧ y ∈ J.verts ∧
              d y + 1 = d x := by
            intro x
            by_cases hx : x ∈ J.verts ∧ x ≠ r
            · obtain ⟨y, e, h⟩ := hkey x hx.1 hx.2
              exact ⟨y, e, fun _ _ => h⟩
            · exact ⟨x, hEn.some, fun h1 h2 => absurd ⟨h1, h2⟩ hx⟩
          choose p g hpg using hpg
          have hloop : ∀ a b : V, ∀ e, G.ends e = s(a, b) → a ≠ b := by
            intro a b e h hab
            subst hab
            exact G.loopless e (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)
          -- g injective
          have hginj : ∀ x ∈ J.verts, x ≠ r → ∀ x' ∈ J.verts, x' ≠ r → g x = g x' → x = x' := by
            intro x hx hxr x' hx' hxr' h
            have e1 := (hpg x hx hxr).2.1
            have e2 := (hpg x' hx' hxr').2.1
            have d1 := (hpg x hx hxr).2.2.2
            have d2 := (hpg x' hx' hxr').2.2.2
            rw [h, e2, Sym2.eq_iff] at e1
            rcases e1 with ⟨h1, -⟩ | ⟨h1, h2⟩
            · exact h1.symm
            · exfalso; rw [← h1] at d1; rw [h2] at d2; omega
          have hcard : J.verts.card = J.edges.card + 1 := J.card_verts
          have hgsurj : ∀ e ∈ J.edges, ∃ y ∈ J.verts, y ≠ r ∧ g y = e := by
            have himg : (J.verts.erase r).image g = J.edges := by
              apply Finset.eq_of_subset_of_card_le
              · intro e he
                obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
                exact (hpg y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)).1
              · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem hrV]
                · omega
                · intro x hx x' hx' h
                  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hx'
                  exact hginj x hx.1 hx.2 x' hx'.1 hx'.2 h
            intro e he
            rw [← himg] at he
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp he
            exact ⟨y, Finset.mem_of_mem_erase hy, Finset.ne_of_mem_erase hy, rfl⟩
          -- types
          have htype : ∀ x ∈ J.verts, x ≠ r → (x ∈ J.outer → p x ∈ J.inner) ∧ (x ∈ J.inner → p x ∈ J.outer) := by
            intro x hx hxr
            obtain ⟨hge, hends, -, -⟩ := hpg x hx hxr
            obtain ⟨a, ha, b, hb, hab⟩ := J.edge_ends _ hge
            have hne := hloop _ _ _ hends
            rw [hends, Sym2.eq_iff] at hab
            have hdis := J.disjoint
            rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨fun h => absurd (Finset.disjoint_left.mp hdis ha h) id, fun _ => hb⟩
            · exact ⟨fun _ => ha, fun h => absurd (Finset.disjoint_left.mp hdis h hb) id⟩
          have hdis : ∀ x, x ∈ J.inner → x ∈ J.outer → False := fun x h1 h2 =>
            Finset.disjoint_left.mp J.disjoint h1 h2
          have hmemV : ∀ x ∈ J.verts, x ∈ J.inner ∨ x ∈ J.outer := fun x hx => Finset.mem_union.mp hx
          have hinV : ∀ x ∈ J.inner, x ∈ J.verts := fun x hx => Finset.mem_union_left _ hx
          have houtV : ∀ x ∈ J.outer, x ∈ J.verts := fun x hx => Finset.mem_union_right _ hx
          -- incidence: an edge at u is g u or the g of a child
          have hinc : ∀ e ∈ J.edges, ∀ u, u ∈ G.ends e →
              ∃ y ∈ J.verts, y ≠ r ∧ g y = e ∧ (y = u ∨ p y = u) := by
            intro e he u hu
            obtain ⟨y, hy, hyr, rfl⟩ := hgsurj e he
            rw [(hpg y hy hyr).2.1, Sym2.mem_iff] at hu
            exact ⟨y, hy, hyr, rfl, by rcases hu with h | h <;> [left; right] <;> exact h.symm⟩
          have hM1 : ∀ u ∈ J.inner, ∃ c ∈ J.verts, c ≠ r ∧ p c = u := by
            intro u hu
            have h2 := J.inner_deg u hu
            obtain ⟨e, he, hne⟩ := Finset.exists_mem_ne (s := J.edges.filter (fun e => u ∈ G.ends e)) (by omega) (g u)
            rw [Finset.mem_filter] at he
            obtain ⟨y, hy, hyr, rfl, h⟩ := hinc _ he.1 u he.2
            rcases h with rfl | h
            · exact absurd rfl hne
            · exact ⟨y, hy, hyr, h⟩
          have hgu : ∀ x ∈ J.verts, x ≠ r → x ∈ G.ends (g x) := by
            intro x hx hxr; rw [(hpg x hx hxr).2.1]; exact Sym2.mem_mk_left _ _
          have hgp : ∀ x ∈ J.verts, x ≠ r → p x ∈ G.ends (g x) := by
            intro x hx hxr; rw [(hpg x hx hxr).2.1]; exact Sym2.mem_mk_right _ _
          have hM2 : ∀ u ∈ J.inner, u ≠ r → ∀ c ∈ J.verts, c ≠ r → p c = u → ∀ c' ∈ J.verts, c' ≠ r →
              p c' = u → c = c' := by
            intro u hu hur c hc hcr hpc c' hc' hcr' hpc'
            by_contra hcc
            have h2 := J.inner_deg u hu
            have hsub : ({g u, g c, g c'} : Finset E) ⊆ J.edges.filter (fun e => u ∈ G.ends e) := by
              intro e he
              simp only [Finset.mem_insert, Finset.mem_singleton] at he
              rw [Finset.mem_filter]
              rcases he with rfl | rfl | rfl
              · exact ⟨(hpg u (hinV u hu) hur).1, hgu u (hinV u hu) hur⟩
              · exact ⟨(hpg c hc hcr).1, hpc ▸ hgp c hc hcr⟩
              · exact ⟨(hpg c' hc' hcr').1, hpc' ▸ hgp c' hc' hcr'⟩
            have hd1 := (hpg c hc hcr).2.2.2
            have hd2 := (hpg c' hc' hcr').2.2.2
            rw [hpc] at hd1; rw [hpc'] at hd2
            have n1 : g u ≠ g c := fun h => by
              have := hginj u (hinV u hu) hur c hc hcr h; subst this; omega
            have n2 : g u ≠ g c' := fun h => by
              have := hginj u (hinV u hu) hur c' hc' hcr' h; subst this; omega
            have n3 : g c ≠ g c' := fun h => hcc (hginj c hc hcr c' hc' hcr' h)
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp [n1, n2]), Finset.card_pair n3] at this
            omega
          have hch : ∀ u, ∃ c, u ∈ J.inner → c ∈ J.verts ∧ c ≠ r ∧ p c = u := by
            intro u
            by_cases hu : u ∈ J.inner
            · obtain ⟨c, h1, h2, h3⟩ := hM1 u hu; exact ⟨c, fun _ => ⟨h1, h2, h3⟩⟩
            · exact ⟨u, fun h => absurd h hu⟩
          choose ch hch using hch
          have hchout : ∀ u ∈ J.inner, ch u ∈ J.outer := by
            intro u hu
            obtain ⟨h1, h2, h3⟩ := hch u hu
            rcases hmemV _ h1 with h | h
            · have := (htype _ h1 h2).2 h; rw [h3] at this; exact absurd this (hdis u hu)
            · exact h
          have hsurjgen : ∀ (N : Finset E) (A : Finset V) (f : E → V), Set.MapsTo f N A → Set.InjOn f N →
              A.card ≤ N.card → ∀ a ∈ A, ∃ e ∈ N, f e = a := by
            intro N A f hmap hinj hle a ha
            have : N.image f = A := by
              apply Finset.eq_of_subset_of_card_le
              · intro x hx; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx; exact hmap he
              · rw [Finset.card_image_of_injOn hinj]; exact hle
            rw [← this] at ha
            exact Finset.mem_image.mp ha
          have hNmatch : IsMatching G (M ∩ J.edges) := hmax.2.1
          -- a matching of size |inner|
          have hinner_le : J.inner.card ≤ (M ∩ J.edges).card := by
            have hinj : Set.InjOn (fun u => g (ch u)) J.inner := by
              intro u hu u' hu' h
              obtain ⟨h1, h2, h3⟩ := hch u hu
              obtain ⟨h1', h2', h3'⟩ := hch u' hu'
              have := hginj _ h1 h2 _ h1' h2' h
              rw [← h3, ← h3', this]
            have hm : IsMatching G (J.inner.image (fun u => g (ch u))) := by
              intro e he f hf hef w hwe hwf
              obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
              obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hf
              obtain ⟨h1, h2, h3⟩ := hch u hu
              obtain ⟨h1', h2', h3'⟩ := hch u' hu'
              have hc := hchout u hu
              have hc' := hchout u' hu'
              try simp only at hwe hwf
              rw [(hpg _ h1 h2).2.1, h3, Sym2.mem_iff] at hwe
              rw [(hpg _ h1' h2').2.1, h3', Sym2.mem_iff] at hwf
              have hne : u ≠ u' := fun h => hef (by rw [h])
              rcases hwe with rfl | rfl <;> rcases hwf with h | h
              · exact hne (by rw [← h3, ← h3', h])
              · exact hdis _ (h ▸ hu') hc
              · exact hdis _ hu (h ▸ hc')
              · exact hne h
            have := hmax.2.2 _ (by
              intro e he; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
              exact (hpg _ (hch u hu).1 (hch u hu).2.1).1) hm
            rwa [Finset.card_image_of_injOn hinj] at this
          have hio : ∀ e, ∃ a b, e ∈ J.edges → a ∈ J.inner ∧ b ∈ J.outer ∧ G.ends e = s(a, b) := by
            intro e
            by_cases he : e ∈ J.edges
            · obtain ⟨a, ha, b, hb, h⟩ := J.edge_ends e he; exact ⟨a, b, fun _ => ⟨ha, hb, h⟩⟩
            · exact ⟨v, v, fun h => absurd h he⟩
          choose ia ob hio using hio
          have hcovI : ∀ u ∈ J.inner, ∃ e ∈ M ∩ J.edges, ia e = u := by
            apply hsurjgen _ _ ia
            · intro e he; exact (hio e (Finset.mem_inter.mp he).2).1
            · intro e he e' he' h
              by_contra hne
              have he2 := (Finset.mem_inter.mp (Finset.mem_coe.mp he)).2
              have he2' := (Finset.mem_inter.mp (Finset.mem_coe.mp he')).2
              have a1 : ia e ∈ G.ends e := by rw [(hio e he2).2.2]; exact Sym2.mem_mk_left _ _
              have a2 : ia e' ∈ G.ends e' := by rw [(hio e' he2').2.2]; exact Sym2.mem_mk_left _ _
              try simp only at h
              rw [← h] at a2
              exact hNmatch e he e' he' hne _ a1 a2
            · exact hinner_le
          have hrout : r ∈ J.outer := by
            rcases hmemV r hrV with h | h
            · obtain ⟨e, he, hie⟩ := hcovI r h
              have : ia e ∈ G.ends e := by
                rw [(hio e (Finset.mem_inter.mp he).2).2.2]; exact Sym2.mem_mk_left _ _
              rw [hie] at this
              exact absurd this (hrN e he)
            · exact h
          have hrnI : r ∉ J.inner := fun h => hdis r h hrout
          have houter_le : (J.outer.erase r).card ≤ (M ∩ J.edges).card := by
            refine le_trans (Finset.card_le_card_of_injOn p ?_ ?_) hinner_le
            · intro x hx
              have hx' := Finset.mem_coe.mp hx
              exact (htype x (houtV x (Finset.mem_of_mem_erase hx')) (Finset.ne_of_mem_erase hx')).1
                (Finset.mem_of_mem_erase hx')
            · intro x hx x' hx' h
              have hx1 := Finset.mem_coe.mp hx
              have hx2 := Finset.mem_coe.mp hx'
              have hpi := (htype x (houtV x (Finset.mem_of_mem_erase hx1)) (Finset.ne_of_mem_erase hx1)).1
                (Finset.mem_of_mem_erase hx1)
              exact hM2 (p x) hpi (fun h' => hrnI (h' ▸ hpi)) x (houtV x (Finset.mem_of_mem_erase hx1))
                (Finset.ne_of_mem_erase hx1) rfl x' (houtV x' (Finset.mem_of_mem_erase hx2))
                (Finset.ne_of_mem_erase hx2) h.symm
          have hcovO : ∀ x ∈ J.outer.erase r, ∃ e ∈ M ∩ J.edges, ob e = x := by
            apply hsurjgen _ _ ob
            · intro e he
              have he2 := (Finset.mem_inter.mp (Finset.mem_coe.mp he)).2
              have a1 : ob e ∈ G.ends e := by rw [(hio e he2).2.2]; exact Sym2.mem_mk_right _ _
              refine Finset.mem_erase.mpr ⟨fun h => ?_, (hio e he2).2.1⟩
              rw [h] at a1; exact hrN e (Finset.mem_coe.mp he) a1
            · intro e he e' he' h
              by_contra hne
              have he2 := (Finset.mem_inter.mp (Finset.mem_coe.mp he)).2
              have he2' := (Finset.mem_inter.mp (Finset.mem_coe.mp he')).2
              have a1 : ob e ∈ G.ends e := by rw [(hio e he2).2.2]; exact Sym2.mem_mk_right _ _
              have a2 : ob e' ∈ G.ends e' := by rw [(hio e' he2').2.2]; exact Sym2.mem_mk_right _ _
              try simp only at h
              rw [← h] at a2
              exact hNmatch e he e' he' hne _ a1 a2
            · exact houter_le
          have hctype : ∀ y ∈ J.verts, y ≠ r → (p y ∈ J.outer → y ∈ J.inner) ∧ (p y ∈ J.inner → y ∈ J.outer) := by
            intro y hy hyr
            constructor
            · intro h
              rcases hmemV y hy with h' | h'
              · exact h'
              · exact (hdis _ ((htype y hy hyr).1 h') h).elim
            · intro h
              rcases hmemV y hy with h' | h'
              · exact (hdis _ h ((htype y hy hyr).2 h')).elim
              · exact h'
          have hB : ∀ u ∈ J.inner, g u ∉ M := by
            by_contra hcon
            push Not at hcon
            obtain ⟨u, hu', hmaxu⟩ := Finset.exists_max_image (J.inner.filter (fun u => g u ∈ M)) d
              (by obtain ⟨u, hu, h⟩ := hcon; exact ⟨u, Finset.mem_filter.mpr ⟨hu, h⟩⟩)
            rw [Finset.mem_filter] at hu'
            obtain ⟨hu, hgM⟩ := hu'
            have hur : u ≠ r := fun h => hrnI (h ▸ hu)
            obtain ⟨hcV, hcr, hpc⟩ := hch u hu
            have hcout := hchout u hu
            obtain ⟨e, heN, hoe⟩ := hcovO (ch u) (Finset.mem_erase.mpr ⟨hcr, hcout⟩)
            have he2 := (Finset.mem_inter.mp heN).2
            have hcmem : ch u ∈ G.ends e := by
              rw [← hoe, (hio e he2).2.2]; exact Sym2.mem_mk_right _ _
            obtain ⟨y, hy, hyr, rfl, hyc⟩ := hinc _ he2 _ hcmem
            rcases hyc with rfl | hyc
            · have hne : g (ch u) ≠ g u := fun h => by
                have := hginj _ hcV hcr u (hinV u hu) hur h
                rw [this] at hcout; exact hdis u hu hcout
              have h1 : u ∈ G.ends (g (ch u)) := by have := hgp _ hcV hcr; rwa [hpc] at this
              exact hM _ (Finset.mem_inter.mp heN).1 _ hgM hne u h1 (hgu u (hinV u hu) hur)
            · have hyI : y ∈ J.inner := (hctype y hy hyr).1 (hyc ▸ hcout)
              have := hmaxu y (Finset.mem_filter.mpr ⟨hyI, (Finset.mem_inter.mp heN).1⟩)
              have d1 := (hpg y hy hyr).2.2.2
              have d2 := (hpg _ hcV hcr).2.2.2
              rw [hyc] at d1; rw [hpc] at d2
              omega
          have hgM : ∀ x ∈ J.verts, x ≠ r → (g x ∈ M ↔ x ∈ J.outer) := by
            intro x hx hxr
            constructor
            · intro h
              rcases hmemV x hx with h' | h'
              · exact absurd h (hB x h')
              · exact h'
            · intro hxo
              obtain ⟨e, heN, hoe⟩ := hcovO x (Finset.mem_erase.mpr ⟨hxr, hxo⟩)
              have he2 := (Finset.mem_inter.mp heN).2
              have hxmem : x ∈ G.ends e := by
                rw [← hoe, (hio e he2).2.2]; exact Sym2.mem_mk_right _ _
              obtain ⟨y, hy, hyr, rfl, hyc⟩ := hinc _ he2 _ hxmem
              rcases hyc with rfl | hyc
              · exact (Finset.mem_inter.mp heN).1
              · have hyI : y ∈ J.inner := (hctype y hy hyr).1 (hyc ▸ hxo)
                exact absurd (Finset.mem_inter.mp heN).1 (hB y hyI)
          have hPI : ∀ (vs : List V) (es : List E), IsPath G vs es ↔ vs.Nodup ∧ vs.length = es.length + 1 ∧
              ∀ i (h1 : i < es.length) (h2 : i + 1 < vs.length),
                G.ends es[i] = s(vs[i]'(by omega), vs[i+1]) := by
            intro vs es
            unfold IsPath
            constructor
            · rintro ⟨h1, h2, h3⟩
              refine ⟨h1, h2, fun i hi1 hi2 => ?_⟩
              have := congrArg (fun l => l[i]?) h3
              simp only [List.getElem?_map] at this
              rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem (by rw [List.length_zipWith, List.length_tail]; omega)] at this
              simp only [Option.map_some, Option.some.injEq] at this
              rw [this, List.getElem_zipWith, List.getElem_tail]
            · rintro ⟨h1, h2, h3⟩
              refine ⟨h1, h2, ?_⟩
              apply List.ext_getElem
              · simp; omega
              · intro i hi1 hi2
                rw [List.getElem_map, List.getElem_zipWith, List.getElem_tail]
                exact h3 i (by simpa using hi1) (by simp at hi2; omega)
          have hpinv : ∀ x ∈ J.verts, x ≠ r → ∀ a, s(x, p x) = s(a, x) → p x = a := by
            intro x hx hxr a h
            rw [Sym2.eq_iff] at h
            rcases h with ⟨h1, h2⟩ | ⟨-, h2⟩
            · exact absurd h2 (hloop _ _ _ (hpg x hx hxr).2.1).symm
            · exact h2
          set n := d v with hn
          have hit : ∀ k ≤ n, p^[k] v ∈ J.verts ∧ d (p^[k] v) + k = n := by
            intro k
            induction k with
            | zero => intro _; exact ⟨hvV, by simp [hn]⟩
            | succ k ih =>
              intro hk
              obtain ⟨h1, h2⟩ := ih (by omega)
              have hne : p^[k] v ≠ r := fun h => by rw [h, hdr] at h2; omega
              obtain ⟨-, -, h3, h4⟩ := hpg _ h1 hne
              rw [Function.iterate_succ_apply']
              exact ⟨h3, by omega⟩
          have hitne : ∀ k < n, p^[k] v ≠ r := by
            intro k hk h
            have := (hit k hk.le).2
            rw [h, hdr] at this; omega
          have hitr : p^[n] v = r := hd0 _ (hit n le_rfl).1 (by have := (hit n le_rfl).2; omega)
          have hsucc : ∀ k, p^[k+1] v = p (p^[k] v) := fun k => Function.iterate_succ_apply' _ _ _
          have hsame : ∀ x ∈ J.verts, x ≠ r → ∀ y ∈ J.verts, y ≠ r → p x = p y →
              (x ∈ J.outer ↔ y ∈ J.outer) := by
            intro x hx hxr y hy hyr hp
            have hpx : p x ∈ J.verts := (hpg x hx hxr).2.2.1
            rcases hmemV _ hpx with h | h
            · have h1 := (hctype x hx hxr).2 h
              have h2 := (hctype y hy hyr).2 (hp ▸ h)
              exact ⟨fun _ => h2, fun _ => h1⟩
            · have h1 := (hctype x hx hxr).1 h
              have h2 := (hctype y hy hyr).1 (hp ▸ h)
              exact ⟨fun h' => (hdis x h1 h').elim, fun h' => (hdis y h2 h').elim⟩
          have hdown : ∀ (qv : List V) (qe : List E), qv.Nodup → qv.length = qe.length + 1 →
              (∀ i (h1 : i < qe.length) (h2 : i + 1 < qv.length),
                G.ends qe[i] = s(qv[i]'(by omega), qv[i+1])) →
              (∀ i (h : i + 1 < qe.length), (qe[i] ∈ M ↔ qe[i+1] ∉ M)) →
              (∀ e ∈ qe, e ∈ J.edges) → (∀ x ∈ qv, x ∈ J.verts) →
              (∀ h : 0 < qv.length, qv[0] = v) → (∀ h : 0 < qe.length, qe[0] ∈ M) →
              qe.length ≤ n ∧ (∀ i (h : i < qv.length), qv[i] = p^[i] v) ∧
                ∀ i (h : i < qe.length), qe[i] = g (p^[i] v) := by
            intro qv qe hnd hlen hends halt hE hVv h0 hM0
            have claim : ∀ i (h : i < qe.length), qv[i]'(by omega) = p^[i] v ∧ qv[i]'(by omega) ≠ r ∧
                qe[i] = g (qv[i]'(by omega)) ∧ qv[i+1]'(by omega) = p (qv[i]'(by omega)) := by
              intro i
              induction i with
              | zero =>
                intro h
                have hq0 : qv[0] = v := h0 (by omega)
                have he := hE _ (List.getElem_mem h)
                have hmem : qv[0]'(by omega) ∈ G.ends qe[0] := by
                  rw [hends 0 h (by omega)]; exact Sym2.mem_mk_left _ _
                obtain ⟨y, hy, hyr, hgy, hyc⟩ := hinc _ he _ hmem
                have hE0 := hends 0 h (by omega)
                rw [← hgy, (hpg y hy hyr).2.1] at hE0
                rcases hyc with hyc | hyc
                · subst hyc
                  refine ⟨by simpa using hq0, hyr, hgy.symm, ?_⟩
                  rw [Sym2.eq_iff] at hE0
                  rcases hE0 with ⟨-, h2⟩ | ⟨h1, h2⟩
                  · exact h2.symm
                  · exact absurd h1 ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
                · exfalso
                  have hyo : y ∈ J.outer := (hgM y hy hyr).mp (hgy ▸ hM0 h)
                  have := (htype y hy hyr).1 hyo
                  rw [hyc, hq0] at this
                  exact hdis v this hv
              | succ j ih =>
                intro h
                obtain ⟨a1, a2, a3, a4⟩ := ih (by omega)
                have he := hE _ (List.getElem_mem h)
                have hmem : qv[j+1]'(by omega) ∈ G.ends qe[j+1] := by
                  rw [hends (j+1) h (by omega)]; exact Sym2.mem_mk_left _ _
                obtain ⟨y, hy, hyr, hgy, hyc⟩ := hinc _ he _ hmem
                have hE0 := hends (j+1) h (by omega)
                rw [← hgy, (hpg y hy hyr).2.1] at hE0
                rcases hyc with hyc | hyc
                · subst hyc
                  refine ⟨by rw [a4, a1, hsucc], hyr, hgy.symm, ?_⟩
                  rw [Sym2.eq_iff] at hE0
                  rcases hE0 with ⟨-, h2⟩ | ⟨h1, h2⟩
                  · exact h2.symm
                  · exact absurd h1 ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
                · exfalso
                  have hy' : y = qv[j+2]'(by omega) := by
                    rw [hyc, Sym2.eq_iff] at hE0
                    rcases hE0 with ⟨h1, -⟩ | ⟨h1, -⟩
                    · exact absurd (h1.symm) (by rw [← hyc]; exact (hloop _ _ _ (hpg y hy hyr).2.1).symm)
                    · exact h1
                  have hal := halt j (by omega)
                  rw [a3, ← hgy, hgM _ (hVv _ (List.getElem_mem _)) a2, hgM y hy hyr] at hal
                  have := hsame _ (hVv _ (List.getElem_mem _)) a2 y hy hyr (by rw [← a4, hyc])
                  tauto
            have hall : ∀ i (h : i < qv.length), qv[i] = p^[i] v := by
              intro i hi
              rcases Nat.eq_zero_or_eq_succ_pred i with h | h
              · subst h; simpa using h0 hi
              · obtain ⟨a1, -, -, a4⟩ := claim (i - 1) (by omega)
                have : qv[i] = qv[i - 1 + 1]'(by omega) := by congr 1; try omega
                rw [this, a4, a1, ← hsucc]; congr 1; try omega
            refine ⟨?_, hall, fun i hi => by rw [(claim i hi).2.2.1, (claim i hi).1]⟩
            by_contra hlt
            have := (claim n (by omega)).2.1
            rw [hall n (by omega), hitr] at this
            exact this rfl
          have hpit : ∀ k, k < n → p (p^[k] v) = p^[k+1] v := fun k _ => (hsucc k).symm
          set rv : List V := (List.range (n+1)).map (fun i => p^[n-i] v) with hrvdef
          set re : List E := (List.range n).map (fun i => g (p^[n-1-i] v)) with hredef
          have hrvl : rv.length = n + 1 := by simp [rv]
          have hrel : re.length = n := by simp [re]
          have hrv : ∀ i (h : i < rv.length), rv[i] = p^[n-i] v := by intro i h; simp [rv]
          have hre : ∀ i (h : i < re.length), re[i] = g (p^[n-1-i] v) := by intro i h; simp [re]
          have hrePath : IsPath G rv re := by
            rw [hPI]
            refine ⟨?_, by omega, ?_⟩
            · apply List.Nodup.map_on _ List.nodup_range
              intro x hx y hy hxy
              simp only [List.mem_range] at hx hy
              have h1 := (hit (n-x) (by omega)).2
              have h2 := (hit (n-y) (by omega)).2
              try simp only at hxy
              rw [hxy] at h1
              omega
            · intro i h1 h2
              rw [hre, hrv, hrv, (hpg _ (hit _ (by omega)).1 (hitne _ (by omega))).2.1, Sym2.eq_swap]
              rw [hpit _ (by omega)]
              rw [show n - 1 - i + 1 = n - i by omega, show n - (i+1) = n - 1 - i by omega]
          have hrePI : PathIn G J.toSub r v rv re := by
            refine ⟨hrePath, ?_, ?_, ?_, ?_⟩
            · intro x hx
              rw [List.mem_toFinset, List.mem_iff_getElem] at hx
              obtain ⟨i, hi, rfl⟩ := hx
              rw [hrv]; exact (hit _ (by omega)).1
            · intro x hx
              rw [List.mem_toFinset, List.mem_iff_getElem] at hx
              obtain ⟨i, hi, rfl⟩ := hx
              rw [hre]; exact (hpg _ (hit _ (by omega)).1 (hitne _ (by omega))).1
            · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), hrv]; simp [hitr]
            · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), hrv]; simp [hrvl]
          have hpar : ∀ y ∈ J.verts, y ≠ r → (p y ∈ J.outer ↔ y ∉ J.outer) := by
            intro y hy hyr
            rcases hmemV y hy with h | h
            · exact ⟨fun _ hh => hdis y h hh, fun _ => (htype y hy hyr).2 h⟩
            · exact ⟨fun hh => (hdis _ ((htype y hy hyr).1 h) hh).elim, fun hh => (hh h).elim⟩
          have hstem : IsStem G M rv re := by
            refine ⟨⟨hrePath, ?_⟩, ?_, ?_⟩
            · rw [List.isChain_iff_getElem]
              intro i hi
              rw [hre, hre]
              have hy1 := (hit (n-1-(i+1)) (by omega)).1
              have hy2 := hitne (n-1-(i+1)) (by omega)
              have hx1 := (hit (n-1-i) (by omega)).1
              have hx2 := hitne (n-1-i) (by omega)
              rw [hgM _ hx1 hx2, hgM _ hy1 hy2]
              have := hpar _ hy1 hy2
              rw [hpit _ (by omega), show n - 1 - (i + 1) + 1 = n - 1 - i by omega] at this
              rw [this]; try tauto
            · intro r' hr'
              rw [hrePI.2.2.2.1] at hr'
              simp only [Option.mem_def, Option.some.injEq] at hr'
              subst hr'; exact hrexp
            · intro e he
              rw [List.getLast?_eq_getElem?] at he
              rcases Nat.eq_zero_or_pos n with h0 | hpos
              · simp [hrel, h0] at he
              · rw [List.getElem?_eq_getElem (by omega)] at he
                simp only [Option.mem_def, Option.some.injEq] at he
                rw [← he, hre, show n - 1 - (re.length - 1) = 0 by omega]
                exact (hgM v hvV (hitne 0 hpos)).mpr hv
          have huniq : ∀ wv we, PathIn G J.toSub r v wv we → wv = rv ∧ we = re := by
            rintro wv we ⟨hwp, hwV, hwE, hwh, hwl⟩
            rw [hPI] at hwp
            obtain ⟨hnd, hlen, hends⟩ := hwp
            have hVv : ∀ x ∈ wv, x ∈ J.verts := fun x hx => hwV (List.mem_toFinset.mpr hx)
            have hEe : ∀ e ∈ we, e ∈ J.edges := fun e hx => hwE (List.mem_toFinset.mpr hx)
            have hw0 : wv[0]'(by omega) = r := by
              rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hwh
              simpa using hwh
            have hwn : wv[we.length]'(by omega) = v := by
              rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hwl
              simp only [Option.some.injEq] at hwl
              rw [← hwl]; congr 1; try omega
            have U : ∀ i (h : i < we.length), wv[i+1]'(by omega) ≠ r ∧
                p (wv[i+1]'(by omega)) = wv[i]'(by omega) ∧ we[i] = g (wv[i+1]'(by omega)) := by
              intro i
              induction i with
              | zero =>
                intro h
                have he := hEe _ (List.getElem_mem h)
                have hmem : wv[1]'(by omega) ∈ G.ends we[0] := by
                  rw [hends 0 h (by omega)]; exact Sym2.mem_mk_right _ _
                obtain ⟨y, hy, hyr, hgy, hyc⟩ := hinc _ he _ hmem
                have hE0 := hends 0 h (by omega)
                rw [← hgy, (hpg y hy hyr).2.1] at hE0
                rcases hyc with hyc | hyc
                · subst hyc
                  refine ⟨hyr, ?_, hgy.symm⟩
                  rw [Sym2.eq_iff] at hE0
                  rcases hE0 with ⟨h1, -⟩ | ⟨-, h2⟩
                  · exact absurd h1 ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
                  · exact h2
                · exfalso
                  rw [hyc, Sym2.eq_iff] at hE0
                  rcases hE0 with ⟨h1, -⟩ | ⟨h1, h2⟩
                  · rw [h1, hw0] at hyr; exact hyr rfl
                  · exact absurd h2 ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
              | succ j ih =>
                intro h
                obtain ⟨a1, a2, a3⟩ := ih (by omega)
                have he := hEe _ (List.getElem_mem h)
                have hmem : wv[j+2]'(by omega) ∈ G.ends we[j+1] := by
                  rw [hends (j+1) h (by omega)]; exact Sym2.mem_mk_right _ _
                obtain ⟨y, hy, hyr, hgy, hyc⟩ := hinc _ he _ hmem
                have hE0 := hends (j+1) h (by omega)
                rw [← hgy, (hpg y hy hyr).2.1] at hE0
                rcases hyc with hyc | hyc
                · subst hyc
                  refine ⟨hyr, ?_, hgy.symm⟩
                  rw [Sym2.eq_iff] at hE0
                  rcases hE0 with ⟨h1, -⟩ | ⟨-, h2⟩
                  · exact absurd h1 ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
                  · exact h2
                · exfalso
                  rw [hyc, Sym2.eq_iff] at hE0
                  rcases hE0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · rw [h1, a2] at hyc
                    exact absurd hyc ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
                  · exact absurd h2 ((List.Nodup.getElem_inj_iff hnd).not.mpr (by omega))
            have hdep : ∀ i (h : i < wv.length), d (wv[i]) = i := by
              intro i
              induction i with
              | zero => intro h; rw [hw0, hdr]
              | succ j ih =>
                intro h
                obtain ⟨a1, a2, -⟩ := U j (by omega)
                have := (hpg _ (hVv _ (List.getElem_mem _)) a1).2.2.2
                rw [a2, ih (by omega)] at this
                omega
            have hwl' : we.length = n := by
              have := hdep we.length (by omega); rw [hwn] at this; omega
            have hdownw : ∀ k (h : k ≤ n), wv[n-k]'(by omega) = p^[k] v := by
              intro k
              induction k with
              | zero =>
                intro h
                rw [Function.iterate_zero_apply]
                have e : wv[n-0]'(by omega) = wv[we.length]'(by omega) := by congr 1; try omega
                rw [e, hwn]
              | succ k ih =>
                intro h
                obtain ⟨-, a2, -⟩ := U (n - (k+1)) (by omega)
                have e1 : wv[n - (k+1) + 1]'(by omega) = wv[n-k]'(by omega) := by congr 1; try omega
                rw [e1, ih (by omega)] at a2
                rw [← a2, hsucc]
            constructor
            · apply List.ext_getElem (by omega)
              intro i h1 h2
              rw [hrv, ← hdownw (n-i) (by omega)]; congr 1; try omega
            · apply List.ext_getElem (by omega)
              intro i h1 h2
              rw [hre, (U i h1).2.2, ← hdownw (n-1-i) (by omega)]; congr 2; try omega
          refine ⟨rv, re, hrePI, hstem, huniq, ?_⟩
          rintro pv pe ⟨hpp, hpch⟩ hpV hpE hme
          rw [hPI] at hpp
          obtain ⟨hnd, hlen, hends⟩ := hpp
          have hci := List.isChain_iff_getElem.mp hpch
          have hVv : ∀ x ∈ pv, x ∈ J.verts := fun x hx => hpV (List.mem_toFinset.mpr hx)
          have hEe : ∀ e ∈ pe, e ∈ J.edges := fun e hx => hpE (List.mem_toFinset.mpr hx)
          rcases hme with ⟨hh, e, he, heM⟩ | ⟨hl, e, he, heM⟩
          · obtain ⟨hm, hpvi, hpei⟩ := hdown pv pe hnd hlen hends (fun i h => hci i h) hEe hVv
              (fun h => by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h] at hh; simpa using hh)
              (fun h => by
                rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h] at he
                simp only [Option.some.injEq] at he; rw [he]; exact heM)
            refine ⟨n - pe.length, Or.inr ⟨?_, ?_⟩⟩
            · apply List.ext_getElem (by simp; omega)
              intro k h1 h2
              rw [List.getElem_reverse, List.getElem_take, List.getElem_drop, hpvi, hrv]
              congr 1; try omega
            · apply List.ext_getElem (by simp; omega)
              intro k h1 h2
              rw [List.getElem_reverse, List.getElem_take, List.getElem_drop, hpei, hre]
              congr 2; try omega
          · have hlr : pv.reverse.length = pe.reverse.length + 1 := by simp [hlen]
            obtain ⟨hm, hpvi, hpei⟩ := hdown pv.reverse pe.reverse (List.nodup_reverse.mpr hnd) hlr
              (fun i h1 h2 => by
                simp only [List.length_reverse] at h1 h2
                rw [List.getElem_reverse, List.getElem_reverse, List.getElem_reverse,
                  hends (pe.length - 1 - i) (by omega) (by omega), Sym2.eq_swap]
                congr 2 <;> try omega)
              (fun i h => by
                simp only [List.length_reverse] at h
                rw [List.getElem_reverse, List.getElem_reverse]
                have := hci (pe.length - 1 - (i+1)) (by omega)
                have e1 : pe[pe.length - 1 - (i + 1) + 1]'(by omega) = pe[pe.length - 1 - i]'(by omega) := by
                  congr 1; try omega
                rw [e1] at this
                tauto)
              (fun e he => hEe e (List.mem_reverse.mp he)) (fun x hx => hVv x (List.mem_reverse.mp hx))
              (fun h => by
                rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp at h; omega)] at hl
                simp only [Option.some.injEq] at hl
                rw [List.getElem_reverse, ← hl]; congr 1; try omega)
              (fun h => by
                rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp at h; omega)] at he
                simp only [Option.some.injEq] at he
                rw [List.getElem_reverse]
                have e1 : pe[pe.length - 1 - 0]'(by simp at h; omega) = pe[pe.length - 1]'(by simp at h; omega) := by
                  congr 1
                rw [e1, he]; exact heM)
            simp only [List.length_reverse] at hm
            refine ⟨n - pe.length, Or.inl ⟨?_, ?_⟩⟩
            · apply List.ext_getElem (by simp; omega)
              intro k h1 h2
              rw [List.getElem_take, List.getElem_drop, hrv]
              have := hpvi (pv.length - 1 - k) (by simp; omega)
              rw [List.getElem_reverse] at this
              have e1 : pv[pv.length - 1 - (pv.length - 1 - k)]'(by omega) = pv[k] := by congr 1; try omega
              rw [e1] at this
              rw [this]; congr 1; try omega
            · apply List.ext_getElem (by simp; omega)
              intro k h1 h2
              rw [List.getElem_take, List.getElem_drop, hre]
              have := hpei (pe.length - 1 - k) (by simp; omega)
              rw [List.getElem_reverse] at this
              have e1 : pe[pe.length - 1 - (pe.length - 1 - k)]'(by omega) = pe[k] := by congr 1; try omega
              rw [e1] at this
              rw [this]; congr 2; try omega
