-- Prove2me | solution 1 for PathsTreesFlowers.Duality.berge_3_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:50:12.174742+00:00
-- url     : https://prove2.me/submissions/09807fd3-1b42-4d77-a51d-d1b9476c6eaf

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.MinMax
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic

namespace SolPathsTreesFlowersBerge37

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality (IsMaxMatching IsPath IsAlternatingPath)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: Endpoint and Matching Helpers -/

lemma exists_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) :
    ∃ u w : V, u ≠ w ∧ G.ends e = s(u, w) := by
  obtain ⟨u, w, h⟩ : ∃ u w, G.ends e = s(u, w) := by
    induction h' : G.ends e using Sym2.ind with
    | _ u w => exact ⟨u, w, rfl⟩
  refine ⟨u, w, ?_, h⟩
  intro heq
  apply G.loopless e
  rw [h, heq]
  exact Sym2.mk_isDiag_iff.mpr rfl

lemma exists_other_end (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) {u : V}
    (hu : u ∈ G.ends e) :
    ∃ w : V, u ≠ w ∧ G.ends e = s(u, w) := by
  obtain ⟨a, b, hab, h⟩ := exists_ends G e
  rw [h, Sym2.mem_iff] at hu
  rcases hu with rfl | rfl
  · exact ⟨b, hab, h⟩
  · exact ⟨a, hab.symm, by rw [h, Sym2.eq_swap]⟩

lemma not_mem_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    {e : E} {u : V} (hu_end : u ∈ G.ends e) (hu_exp : PathsTreesFlowers.Duality.IsExposed G M u) :
    e ∉ M :=
  fun he => hu_exp e he hu_end

lemma isMatching_erase {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) (e : E) :
    IsMatching G (M.erase e) := by
  intro e₁ he₁ e₂ he₂ hne v hv₁ hv₂
  exact hM e₁ (Finset.mem_erase.mp he₁).2 e₂ (Finset.mem_erase.mp he₂).2 hne v hv₁ hv₂

lemma isExposed_erase_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    {v : V} (hv : PathsTreesFlowers.Duality.IsExposed G M v) (e : E) :
    PathsTreesFlowers.Duality.IsExposed G (M.erase e) v := by
  intro f hf
  exact hv f (Finset.mem_erase.mp hf).2

lemma isExposed_erase_of_mem_ends {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) {e : E} (he : e ∈ M) {v : V} (hv : v ∈ G.ends e) :
    PathsTreesFlowers.Duality.IsExposed G (M.erase e) v := by
  intro f hf hvf
  have hne : f ≠ e := (Finset.mem_erase.mp hf).1
  have hfM : f ∈ M := (Finset.mem_erase.mp hf).2
  exact hM e he f hfM hne.symm v hv hvf

lemma isMatching_insert_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) {e : E} {u v : V} (hends : G.ends e = s(u, v))
    (hu : PathsTreesFlowers.Duality.IsExposed G M u) (hv : PathsTreesFlowers.Duality.IsExposed G M v) :
    e ∉ M ∧ IsMatching G (insert e M) ∧ (insert e M).card = M.card + 1 := by
  have hu_end : u ∈ G.ends e := by rw [hends]; simp
  have he_not : e ∉ M := not_mem_of_isExposed hu_end hu
  refine ⟨he_not, ?_, Finset.card_insert_of_notMem he_not⟩
  intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
  rcases Finset.mem_insert.mp he₁ with rfl | he₁M <;>
    rcases Finset.mem_insert.mp he₂ with rfl | he₂M
  · exact hne rfl
  · rw [hends, Sym2.mem_iff] at hx₁
    rcases hx₁ with rfl | rfl
    · exact hu e₂ he₂M hx₂
    · exact hv e₂ he₂M hx₂
  · rw [hends, Sym2.mem_iff] at hx₂
    rcases hx₂ with rfl | rfl
    · exact hu e₁ he₁M hx₁
    · exact hv e₁ he₁M hx₁
  · exact hM e₁ he₁M e₂ he₂M hne x hx₁ hx₂

lemma isExposed_insert_of_ne {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    {e : E} {u v w : V} (hends : G.ends e = s(u, v))
    (hwu : w ≠ u) (hwv : w ≠ v) (hw : PathsTreesFlowers.Duality.IsExposed G M w) :
    PathsTreesFlowers.Duality.IsExposed G (insert e M) w := by
  intro f hf hwf
  rcases Finset.mem_insert.mp hf with rfl | hfM
  · rw [hends, Sym2.mem_iff] at hwf
    rcases hwf with rfl | rfl
    · exact hwu rfl
    · exact hwv rfl
  · exact hw f hfM hwf

lemma swap_matching {G : EdmondsMatching65.Polyhedron.Graph V E} {K : Finset E}
    (hK : IsMatching G K) {e_rem e_add : E} {x y z : V}
    (he_rem : e_rem ∈ K) (hends_rem : G.ends e_rem = s(x, y))
    (hends_add : G.ends e_add = s(y, z)) (hz : PathsTreesFlowers.Duality.IsExposed G K z) :
    IsMatching G (insert e_add (K.erase e_rem)) ∧
      (insert e_add (K.erase e_rem)).card = K.card ∧
      (x ≠ y → x ≠ z → PathsTreesFlowers.Duality.IsExposed G (insert e_add (K.erase e_rem)) x) ∧
      (∀ w : V, w ≠ y → w ≠ z → PathsTreesFlowers.Duality.IsExposed G K w → PathsTreesFlowers.Duality.IsExposed G (insert e_add (K.erase e_rem)) w) := by
  have hK_er : IsMatching G (K.erase e_rem) := isMatching_erase hK e_rem
  have hy_end : y ∈ G.ends e_rem := by rw [hends_rem]; simp
  have hx_end : x ∈ G.ends e_rem := by rw [hends_rem]; simp
  have hy_exp : PathsTreesFlowers.Duality.IsExposed G (K.erase e_rem) y := isExposed_erase_of_mem_ends hK he_rem hy_end
  have hx_exp : PathsTreesFlowers.Duality.IsExposed G (K.erase e_rem) x := isExposed_erase_of_mem_ends hK he_rem hx_end
  have hz_exp : PathsTreesFlowers.Duality.IsExposed G (K.erase e_rem) z := isExposed_erase_of_isExposed hz e_rem
  obtain ⟨_, hK', hcard'⟩ :=
    isMatching_insert_of_isExposed hK_er hends_add hy_exp hz_exp
  have hcard_er : (K.erase e_rem).card + 1 = K.card := Finset.card_erase_add_one he_rem
  refine ⟨hK', hcard'.trans hcard_er, ?_, ?_⟩
  · intro hxy hxz
    exact isExposed_insert_of_ne hends_add hxy hxz hx_exp
  · intro w hwy hwz hw
    exact isExposed_insert_of_ne hends_add hwy hwz (isExposed_erase_of_isExposed hw e_rem)

/-! ### Part 2: List and Path Helpers -/

lemma exists_getLast?_of_ne_nil {α : Type*} : ∀ (L : List α), L ≠ [] → ∃ x, L.getLast? = some x
  | [], h => False.elim (h rfl)
  | [a], _ => ⟨a, rfl⟩
  | _ :: b :: t, _ => exists_getLast?_of_ne_nil (b :: t) (List.cons_ne_nil b t)

lemma isChain_congr {α : Type*} {R S : α → α → Prop} :
    ∀ (L : List α), (∀ x ∈ L, ∀ y ∈ L, R x y → S x y) → L.IsChain R → L.IsChain S
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.isChain_singleton a
  | a :: b :: t, h, List.IsChain.cons_cons hab hchain =>
    List.IsChain.cons_cons (h a (by simp) b (by simp) hab)
      (isChain_congr (b :: t)
        (fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)) hchain)

lemma mem_zipWith_tail_ends : ∀ (L : List V) (p : Sym2 V),
    p ∈ List.zipWith (fun a b => s(a, b)) L L.tail → ∀ v ∈ p, v ∈ L
  | [], _, hp => by cases hp
  | [_], _, hp => by cases hp
  | a :: b :: t, p, hp => by
    simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hp
    intro v hv
    rcases hp with rfl | hp
    · rw [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem a (mem_zipWith_tail_ends (b :: t) p hp v hv)

lemma ends_mem_verts_of_isPath {G : EdmondsMatching65.Polyhedron.Graph V E} {vs : List V} {es : List E}
    (hpath : IsPath G vs es) {e : E} (he : e ∈ es) {v : V} (hv : v ∈ G.ends e) :
    v ∈ vs := by
  have hmap : G.ends e ∈ List.zipWith (fun a b => s(a, b)) vs vs.tail := by
    rw [← hpath.2.2]
    exact List.mem_map_of_mem he
  exact mem_zipWith_tail_ends vs (G.ends e) hmap v hv

lemma zipWith_tail_append_singleton : ∀ (vs : List V) (b w : V),
    vs.getLast? = some b →
    List.zipWith (fun x y => s(x, y)) (vs ++ [w]) (vs ++ [w]).tail =
      List.zipWith (fun x y => s(x, y)) vs vs.tail ++ [s(b, w)]
  | [], _, _, h => by cases h
  | [x], b, w, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; rfl
  | x :: y :: t, b, w, h => by
    have h' : (y :: t).getLast? = some b := by simpa using h
    exact congrArg (s(x, y) :: ·) (zipWith_tail_append_singleton (y :: t) b w h')

lemma isChain_append_singleton {α : Type*} (R : α → α → Prop) :
    ∀ (es : List α) (e_last f : α),
      es.IsChain R → es.getLast? = some e_last → R e_last f → (es ++ [f]).IsChain R
  | [], _, _, _, h, _ => by cases h
  | [x], e_last, f, _, h, hR => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact List.IsChain.cons_cons hR (List.isChain_singleton f)
  | x :: y :: t, e_last, f, hchain, hlast, hR => by
    cases hchain with
    | cons_cons hxy hchain' =>
      have hlast' : (y :: t).getLast? = some e_last := by simpa using hlast
      exact List.IsChain.cons_cons hxy (isChain_append_singleton R (y :: t) e_last f hchain' hlast' hR)

lemma isPath_append_step {G : EdmondsMatching65.Polyhedron.Graph V E} {vs : List V} {es : List E}
    {b w : V} {f : E} (hpath : IsPath G vs es) (hlast : vs.getLast? = some b)
    (hw : w ∉ vs) (hends : G.ends f = s(b, w)) :
    IsPath G (vs ++ [w]) (es ++ [f]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hpath.1, List.nodup_singleton w, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact fun h => hw (h ▸ hx)
  · simp [hpath.2.1]
  · rw [List.map_append, List.map_singleton, hends, hpath.2.2,
      zipWith_tail_append_singleton vs b w hlast]

/-! ### Part 3: Backward Direction (Augmenting Path implies Not Max Matching) -/

lemma exists_larger_matching_of_aug_path {G : EdmondsMatching65.Polyhedron.Graph V E} :
    ∀ (vs : List V) (es : List E) (M : Finset E),
      IsMatching G M →
      IsAlternatingPath G M vs es →
      es ≠ [] →
      (∀ a ∈ vs.head?, PathsTreesFlowers.Duality.IsExposed G M a) →
      (∀ b ∈ vs.getLast?, PathsTreesFlowers.Duality.IsExposed G M b) →
      ∃ M' : Finset E, IsMatching G M' ∧ M.card < M'.card
  | _, [], _, _, _, hes, _, _ => False.elim (hes rfl)
  | [], _ :: _, _, _, hAlt, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [_], _ :: _, _, _, hAlt, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [v₀, v₁], [e₀], M, hM, hAlt, _, ha, hb => by
    have hends : G.ends e₀ = s(v₀, v₁) := by
      have hmap := hAlt.1.2.2
      simpa using hmap
    have hv₀ : PathsTreesFlowers.Duality.IsExposed G M v₀ := ha v₀ (by simp)
    have hv₁ : PathsTreesFlowers.Duality.IsExposed G M v₁ := hb v₁ (by simp)
    obtain ⟨_, hM', hcard'⟩ := isMatching_insert_of_isExposed hM hends hv₀ hv₁
    exact ⟨insert e₀ M, hM', by omega⟩
  | [_, _], _ :: _ :: _, _, _, hAlt, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | _ :: _ :: _ :: _, [_], _, _, hAlt, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [v₀, v₁, v₂], [e₀, e₁], M, hM, hAlt, _, ha, hb => by
    have hmap := hAlt.1.2.2
    simp only [List.map, List.tail_cons, List.zipWith, List.cons.injEq, and_true] at hmap
    rcases hmap with ⟨hends₀, hends₁⟩
    have hv₀ : PathsTreesFlowers.Duality.IsExposed G M v₀ := ha v₀ (by simp)
    have hv₂ : PathsTreesFlowers.Duality.IsExposed G M v₂ := hb v₂ (by simp)
    have he₀_not : e₀ ∉ M := not_mem_of_isExposed (by rw [hends₀]; simp) hv₀
    have hchain := hAlt.2
    cases hchain with
    | cons_cons h01 _ =>
      have he₁_mem : e₁ ∈ M := by tauto
      have hv₂_end : v₂ ∈ G.ends e₁ := by rw [hends₁]; simp
      exact False.elim (hv₂ e₁ he₁_mem hv₂_end)
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, hAlt, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | v₀ :: v₁ :: v₂ :: vs', e₀ :: e₁ :: e₂ :: es', M, hM, hAlt, _, ha, hb => by
    have hmap := hAlt.1.2.2
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.cons.injEq] at hmap
    rcases hmap with ⟨hends₀, hends₁, hmap'⟩
    have hnodup := hAlt.1.1
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hv0_not, hv1_not, hv2_not, hnodup_vs'⟩
    simp only [List.mem_cons, not_or] at hv0_not hv1_not
    rcases hv0_not with ⟨hv01, hv02, hv0_vs'⟩
    rcases hv1_not with ⟨hv12, hv1_vs'⟩
    have hnodup' : (v₂ :: vs').Nodup := List.nodup_cons.mpr ⟨hv2_not, hnodup_vs'⟩
    have hpath' : IsPath G (v₂ :: vs') (e₂ :: es') := by
      refine ⟨hnodup', ?_, hmap'⟩
      have := hAlt.1.2.1
      simp only [List.length_cons] at this ⊢
      omega
    have hv₀ : PathsTreesFlowers.Duality.IsExposed G M v₀ := ha v₀ (by simp)
    have he₀_not : e₀ ∉ M := not_mem_of_isExposed (by rw [hends₀]; simp) hv₀
    have hchain := hAlt.2
    cases hchain with
    | cons_cons h01 hchain1 =>
      cases hchain1 with
      | cons_cons h12 hchain' =>
        have he₁_mem : e₁ ∈ M := by tauto
        have hends₁_swap : G.ends e₁ = s(v₂, v₁) := by rw [hends₁, Sym2.eq_swap]
        have hends₀_swap : G.ends e₀ = s(v₁, v₀) := by rw [hends₀, Sym2.eq_swap]
        obtain ⟨hM₁, hM₁_card, hv₂_exp, hw_exp⟩ :=
          swap_matching hM he₁_mem hends₁_swap hends₀_swap hv₀
        let M₁ := insert e₀ (M.erase e₁)
        have hmem_iff : ∀ e ∈ e₂ :: es', (e ∈ M₁ ↔ e ∈ M) := by
          intro e he
          have he_ne_e₀ : e ≠ e₀ := by
            rintro rfl
            have hv₁_mem : v₁ ∈ v₂ :: vs' :=
              ends_mem_verts_of_isPath hpath' he (by rw [hends₀]; simp)
            simp only [List.mem_cons] at hv₁_mem
            rcases hv₁_mem with rfl | hv₁_mem
            · exact hv12 rfl
            · exact hv1_vs' hv₁_mem
          have he_ne_e₁ : e ≠ e₁ := by
            rintro rfl
            have hv₁_mem : v₁ ∈ v₂ :: vs' :=
              ends_mem_verts_of_isPath hpath' he (by rw [hends₁]; simp)
            simp only [List.mem_cons] at hv₁_mem
            rcases hv₁_mem with rfl | hv₁_mem
            · exact hv12 rfl
            · exact hv1_vs' hv₁_mem
          simp [M₁, Finset.mem_insert, Finset.mem_erase, he_ne_e₀, he_ne_e₁]
        have hchain_M₁ : (e₂ :: es').IsChain (fun e f => e ∈ M₁ ↔ f ∉ M₁) := by
          refine isChain_congr (e₂ :: es') ?_ hchain'
          intro x hx y hy hxy
          rw [hmem_iff x hx, hmem_iff y hy]
          exact hxy
        have hAlt' : IsAlternatingPath G M₁ (v₂ :: vs') (e₂ :: es') := ⟨hpath', hchain_M₁⟩
        have ha' : ∀ a ∈ (v₂ :: vs').head?, PathsTreesFlowers.Duality.IsExposed G M₁ a := by
          intro a ha_mem
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha_mem
          subst ha_mem
          exact hv₂_exp (Ne.symm hv12) (Ne.symm hv02)
        have hb' : ∀ b ∈ (v₂ :: vs').getLast?, PathsTreesFlowers.Duality.IsExposed G M₁ b := by
          intro b hb_mem
          have hb_vs : b ∈ v₂ :: vs' := List.mem_of_getLast? hb_mem
          have hb_ne_v₁ : b ≠ v₁ := by
            rintro rfl
            rcases List.mem_cons.mp hb_vs with rfl | hmem
            · exact hv12 rfl
            · exact hv1_vs' hmem
          have hb_ne_v₀ : b ≠ v₀ := by
            rintro rfl
            rcases List.mem_cons.mp hb_vs with rfl | hmem
            · exact hv02 rfl
            · exact hv0_vs' hmem
          have hb_last_vs : b ∈ (v₀ :: v₁ :: v₂ :: vs').getLast? := by
            simpa using hb_mem
          exact hw_exp b hb_ne_v₁ hb_ne_v₀ (hb b hb_last_vs)
        obtain ⟨M', hM', hcard'⟩ :=
          exists_larger_matching_of_aug_path (v₂ :: vs') (e₂ :: es') M₁
            hM₁ hAlt' (List.cons_ne_nil _ _) ha' hb'
        exact ⟨M', hM', hM₁_card ▸ hcard'⟩

/-! ### Part 4: Forward Direction (Larger Matching implies Augmenting Path) -/

lemma filter_univ_ends_eq {G : EdmondsMatching65.Polyhedron.Graph V E} {e : E} {u w : V}
    (hends : G.ends e = s(u, w)) :
    (Finset.univ : Finset V).filter (fun v => v ∈ G.ends e) = {u, w} := by
  ext v
  simp [hends, Sym2.mem_iff]

lemma card_filter_univ_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) :
    ((Finset.univ : Finset V).filter (fun v => v ∈ G.ends e)).card = 2 := by
  obtain ⟨u, w, huw, hends⟩ := exists_ends G e
  rw [filter_univ_ends_eq hends, Finset.card_pair huw]

lemma sum_card_filter_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (F : Finset E) :
    ∑ v ∈ (Finset.univ : Finset V), (F.filter (fun e => v ∈ G.ends e)).card = 2 * F.card := by
  have hcomm : ∑ v ∈ (Finset.univ : Finset V), (F.filter (fun e => v ∈ G.ends e)).card =
      ∑ e ∈ F, ((Finset.univ : Finset V).filter (fun v => v ∈ G.ends e)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hcomm]
  calc ∑ e ∈ F, ((Finset.univ : Finset V).filter (fun v => v ∈ G.ends e)).card
      = ∑ _e ∈ F, 2 := Finset.sum_congr rfl fun e _ => card_filter_univ_ends G e
    _ = 2 * F.card := by simp [Nat.mul_comm]

lemma card_filter_ends_le_one_of_isMatching {G : EdmondsMatching65.Polyhedron.Graph V E} {K : Finset E}
    (hK : IsMatching G K) (v : V) :
    (K.filter (fun e => v ∈ G.ends e)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro e₁ he₁ e₂ he₂
  simp only [Finset.mem_filter] at he₁ he₂
  by_contra hne
  exact hK e₁ he₁.1 e₂ he₂.1 hne v he₁.2 he₂.2

lemma exists_exposed_and_edge_of_card_lt {G : EdmondsMatching65.Polyhedron.Graph V E} {M N : Finset E}
    (hN : IsMatching G N) (hcard : M.card < N.card) :
    ∃ a : V, ∃ e₀ ∈ N \ M, PathsTreesFlowers.Duality.IsExposed G M a ∧ a ∈ G.ends e₀ := by
  have hsum_lt : ∑ v ∈ (Finset.univ : Finset V), (M.filter (fun e => v ∈ G.ends e)).card <
      ∑ v ∈ (Finset.univ : Finset V), (N.filter (fun e => v ∈ G.ends e)).card := by
    rw [sum_card_filter_ends G M, sum_card_filter_ends G N]
    omega
  obtain ⟨a, _, ha_lt⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  have ha_le : (N.filter (fun e => a ∈ G.ends e)).card ≤ 1 :=
    card_filter_ends_le_one_of_isMatching hN a
  have ha_M_zero : (M.filter (fun e => a ∈ G.ends e)).card = 0 := by omega
  have ha_N_pos : 0 < (N.filter (fun e => a ∈ G.ends e)).card := by omega
  have ha_exp : PathsTreesFlowers.Duality.IsExposed G M a := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at ha_M_zero
    intro e he
    exact ha_M_zero he
  obtain ⟨e₀, he₀_filt⟩ := Finset.card_pos.mp ha_N_pos
  have he₀_N : e₀ ∈ N := (Finset.mem_filter.mp he₀_filt).1
  have ha_e₀ : a ∈ G.ends e₀ := (Finset.mem_filter.mp he₀_filt).2
  have he₀_not_M : e₀ ∉ M := not_mem_of_isExposed ha_e₀ ha_exp
  exact ⟨a, e₀, Finset.mem_sdiff.mpr ⟨he₀_N, he₀_not_M⟩, ha_exp, ha_e₀⟩

structure IsOddAugPrefix (G : EdmondsMatching65.Polyhedron.Graph V E) (M N : Finset E)
    (vs : List V) (es : List E) : Prop where
  alt : IsAlternatingPath G M vs es
  ne_nil : es ≠ []
  head_exp : ∀ a ∈ vs.head?, PathsTreesFlowers.Duality.IsExposed G M a
  last_edge : ∀ e ∈ es.getLast?, e ∈ N \ M
  last_inc : ∀ e ∈ es.getLast?, ∀ b ∈ vs.getLast?, b ∈ G.ends e
  cov_N : ∀ u ∈ vs, ∃ g ∈ N \ M, u ∈ G.ends g ∧ ∀ x ∈ G.ends g, x ∈ vs
  cov_M : ∀ u ∈ vs, vs.head? ≠ some u → vs.getLast? ≠ some u →
    ∃ g ∈ M \ N, u ∈ G.ends g ∧ ∀ x ∈ G.ends g, x ∈ vs ∧ vs.getLast? ≠ some x

lemma isOddAugPrefix_singleton {G : EdmondsMatching65.Polyhedron.Graph V E} {M N : Finset E}
    {a b₀ : V} {e₀ : E} (hab₀ : a ≠ b₀) (hends₀ : G.ends e₀ = s(a, b₀))
    (he₀ : e₀ ∈ N \ M) (ha : PathsTreesFlowers.Duality.IsExposed G M a) :
    IsOddAugPrefix G M N [a, b₀] [e₀] where
  alt := ⟨⟨by simp [hab₀], rfl, by simp [hends₀]⟩, List.isChain_singleton e₀⟩
  ne_nil := by simp
  head_exp := by
    intro x hx
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx; exact ha
  last_edge := by
    intro e he
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at he
    subst he; exact he₀
  last_inc := by
    intro e he b hb
    simp only [List.getLast?_singleton, List.getLast?_cons_cons, Option.mem_def,
      Option.some.injEq] at he hb
    subst he; subst hb
    rw [hends₀]; simp
  cov_N := by
    intro u hu
    refine ⟨e₀, he₀, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [hends₀, Sym2.mem_iff]
      exact hu
    · intro x hx
      rw [hends₀, Sym2.mem_iff] at hx
      simp [hx]
  cov_M := by
    intro u hu hhead hlast
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact False.elim (hhead rfl)
    · exact False.elim (hlast rfl)

lemma getLast?_append_two {α : Type*} (L : List α) (x y : α) :
    (L ++ [x, y]).getLast? = some y := by
  have h : L ++ [x, y] = (L ++ [x]) ++ [y] := by simp
  rw [h, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil y []), List.getLast?_singleton]

lemma head?_append_of_ne_nil {α : Type*} {L : List α} (hL : L ≠ []) (R : List α) :
    (L ++ R).head? = L.head? := by
  cases L with
  | nil => exact False.elim (hL rfl)
  | cons a t => rfl

lemma isOddAugPrefix_append_two {G : EdmondsMatching65.Polyhedron.Graph V E} {M N : Finset E}
    (hM : IsMatching G M) (hN : IsMatching G N)
    {vs : List V} {es : List E} (hP : IsOddAugPrefix G M N vs es)
    {b w₁ w₂ : V} {e_last f₁ f₂ : E}
    (hb_last : vs.getLast? = some b) (he_last : es.getLast? = some e_last)
    (hf₁ : f₁ ∈ M \ N) (hf₂ : f₂ ∈ N \ M)
    (hbw₁ : b ≠ w₁) (hw₁w₂ : w₁ ≠ w₂)
    (hends₁ : G.ends f₁ = s(b, w₁)) (hends₂ : G.ends f₂ = s(w₁, w₂)) :
    IsOddAugPrefix G M N (vs ++ [w₁, w₂]) (es ++ [f₁, f₂]) := by
  have hvs_ne : vs ≠ [] := by
    intro hnil
    rw [hnil] at hb_last
    cases hb_last
  have hw₁_not_vs : w₁ ∉ vs := by
    intro hw₁_mem
    by_cases hhead : vs.head? = some w₁
    · have hw₁_exp : PathsTreesFlowers.Duality.IsExposed G M w₁ := hP.head_exp w₁ hhead
      have hw₁_f₁ : w₁ ∈ G.ends f₁ := by rw [hends₁]; simp
      exact hw₁_exp f₁ (Finset.mem_sdiff.mp hf₁).1 hw₁_f₁
    · by_cases hlast : vs.getLast? = some w₁
      · rw [hb_last, Option.some.injEq] at hlast
        exact hbw₁ hlast
      · obtain ⟨g, hg, hw₁_g, hg_ends⟩ := hP.cov_M w₁ hw₁_mem hhead hlast
        have hb_not_g : b ∉ G.ends g := by
          intro hb_g
          exact (hg_ends b hb_g).2 hb_last
        have hb_f₁ : b ∈ G.ends f₁ := by rw [hends₁]; simp
        have hf₁_ne_g : f₁ ≠ g := fun h => hb_not_g (h ▸ hb_f₁)
        have hw₁_f₁ : w₁ ∈ G.ends f₁ := by rw [hends₁]; simp
        exact hM f₁ (Finset.mem_sdiff.mp hf₁).1 g (Finset.mem_sdiff.mp hg).1 hf₁_ne_g w₁ hw₁_f₁ hw₁_g
  have hw₂_not_vs : w₂ ∉ vs := by
    intro hw₂_mem
    obtain ⟨g, hg, hw₂_g, hg_ends⟩ := hP.cov_N w₂ hw₂_mem
    have hw₁_not_g : w₁ ∉ G.ends g := fun hw₁_g => hw₁_not_vs (hg_ends w₁ hw₁_g)
    have hw₁_f₂ : w₁ ∈ G.ends f₂ := by rw [hends₂]; simp
    have hf₂_ne_g : f₂ ≠ g := fun h => hw₁_not_g (h ▸ hw₁_f₂)
    have hw₂_f₂ : w₂ ∈ G.ends f₂ := by rw [hends₂]; simp
    exact hN f₂ (Finset.mem_sdiff.mp hf₂).1 g (Finset.mem_sdiff.mp hg).1 hf₂_ne_g w₂ hw₂_f₂ hw₂_g
  have hpath₁ : IsPath G (vs ++ [w₁]) (es ++ [f₁]) :=
    isPath_append_step hP.alt.1 hb_last hw₁_not_vs hends₁
  have hb₁_last : (vs ++ [w₁]).getLast? = some w₁ := by simp
  have hw₂_not_vs₁ : w₂ ∉ vs ++ [w₁] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hw₂_not_vs, hw₁w₂.symm⟩
  have hpath₂ : IsPath G (vs ++ [w₁, w₂]) (es ++ [f₁, f₂]) := by
    have hvs_assoc : vs ++ [w₁, w₂] = (vs ++ [w₁]) ++ [w₂] := by simp
    have hes_assoc : es ++ [f₁, f₂] = (es ++ [f₁]) ++ [f₂] := by simp
    rw [hvs_assoc, hes_assoc]
    exact isPath_append_step hpath₁ hb₁_last hw₂_not_vs₁ hends₂
  have he_last_NM : e_last ∈ N \ M := hP.last_edge e_last he_last
  have he_last_not_M : e_last ∉ M := (Finset.mem_sdiff.mp he_last_NM).2
  have hf₁_M : f₁ ∈ M := (Finset.mem_sdiff.mp hf₁).1
  have hf₂_not_M : f₂ ∉ M := (Finset.mem_sdiff.mp hf₂).2
  have hchain₁ : (es ++ [f₁]).IsChain (fun e f => e ∈ M ↔ f ∉ M) :=
    isChain_append_singleton (fun e f => e ∈ M ↔ f ∉ M) es e_last f₁
      hP.alt.2 he_last (by tauto)
  have he₁_last : (es ++ [f₁]).getLast? = some f₁ := by simp
  have hchain₂ : (es ++ [f₁, f₂]).IsChain (fun e f => e ∈ M ↔ f ∉ M) := by
    have hes_assoc : es ++ [f₁, f₂] = (es ++ [f₁]) ++ [f₂] := by simp
    rw [hes_assoc]
    exact isChain_append_singleton (fun e f => e ∈ M ↔ f ∉ M) (es ++ [f₁]) f₁ f₂
      hchain₁ he₁_last (by tauto)
  refine ⟨⟨hpath₂, hchain₂⟩, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha_mem
    rw [head?_append_of_ne_nil hvs_ne] at ha_mem
    exact hP.head_exp a ha_mem
  · intro e he
    rw [getLast?_append_two, Option.mem_def, Option.some.injEq] at he
    subst he; exact hf₂
  · intro e he x hx
    rw [getLast?_append_two, Option.mem_def, Option.some.injEq] at he
    rw [getLast?_append_two, Option.mem_def, Option.some.injEq] at hx
    subst he; subst hx
    rw [hends₂]; simp
  · intro u hu
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with hu_vs | rfl | rfl
    · obtain ⟨g, hg, hu_g, hg_ends⟩ := hP.cov_N u hu_vs
      refine ⟨g, hg, hu_g, fun x hx => List.mem_append_left _ (hg_ends x hx)⟩
    · refine ⟨f₂, hf₂, by rw [hends₂]; simp, fun x hx => ?_⟩
      rw [hends₂, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp
    · refine ⟨f₂, hf₂, by rw [hends₂]; simp, fun x hx => ?_⟩
      rw [hends₂, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp
  · intro u hu hhead hlast
    rw [head?_append_of_ne_nil hvs_ne] at hhead
    rw [getLast?_append_two] at hlast
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with hu_vs | rfl | rfl
    · by_cases hub : u = b
      · subst hub
        refine ⟨f₁, hf₁, by rw [hends₁]; simp, fun x hx => ?_⟩
        rw [hends₁, Sym2.mem_iff] at hx
        rw [getLast?_append_two]
        rcases hx with rfl | rfl
        · exact ⟨List.mem_append_left _ hu_vs, fun h => hw₂_not_vs (Option.some.inj h ▸ hu_vs)⟩
        · exact ⟨by simp, fun h => hw₁w₂ (Option.some.inj h).symm⟩
      · have hlast_vs : vs.getLast? ≠ some u := by
          rw [hb_last]
          exact fun h => hub (Option.some.inj h).symm
        obtain ⟨g, hg, hu_g, hg_ends⟩ := hP.cov_M u hu_vs hhead hlast_vs
        refine ⟨g, hg, hu_g, fun x hx => ?_⟩
        have hx_vs : x ∈ vs := (hg_ends x hx).1
        rw [getLast?_append_two]
        exact ⟨List.mem_append_left _ hx_vs, fun h => hw₂_not_vs (Option.some.inj h ▸ hx_vs)⟩
    · refine ⟨f₁, hf₁, by rw [hends₁]; simp, fun x hx => ?_⟩
      rw [hends₁, Sym2.mem_iff] at hx
      rw [getLast?_append_two]
      have hb_vs : b ∈ vs := List.mem_of_getLast? hb_last
      rcases hx with rfl | rfl
      · exact ⟨List.mem_append_left _ hb_vs, fun h => hw₂_not_vs (Option.some.inj h ▸ hb_vs)⟩
      · exact ⟨by simp, fun h => hw₁w₂ (Option.some.inj h).symm⟩
    · exact False.elim (hlast rfl)

lemma extend_oddAugPrefix {G : EdmondsMatching65.Polyhedron.Graph V E} {M N : Finset E}
    (hM : IsMatching G M) (hN : IsMatching G N) :
    ∀ (r : ℕ) (vs : List V) (es : List E),
      Fintype.card V - vs.length ≤ r →
      IsOddAugPrefix G M N vs es →
      (∃ (vs' : List V) (es' : List E), IsAlternatingPath G M vs' es' ∧ es' ≠ [] ∧
        (∀ a ∈ vs'.head?, PathsTreesFlowers.Duality.IsExposed G M a) ∧ (∀ b ∈ vs'.getLast?, PathsTreesFlowers.Duality.IsExposed G M b)) ∨
      (∃ N' : Finset E, IsMatching G N' ∧ N'.card = N.card ∧ (N' \ M).card < (N \ M).card) := by
  intro r
  induction r with
  | zero =>
    intro vs es hr hP
    have hvs_ne : vs ≠ [] := by
      intro hnil
      have := hP.alt.1.2.1
      rw [hnil] at this
      simp at this
    obtain ⟨b, hb_last⟩ := exists_getLast?_of_ne_nil vs hvs_ne
    obtain ⟨e_last, he_last⟩ := exists_getLast?_of_ne_nil es hP.ne_nil
    by_cases hb_exp : PathsTreesFlowers.Duality.IsExposed G M b
    · refine Or.inl ⟨vs, es, hP.alt, hP.ne_nil, hP.head_exp, ?_⟩
      intro b' hb'
      rw [Option.mem_def, hb_last, Option.some.injEq] at hb'
      subst hb'
      exact hb_exp
    · simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hb_exp
      rcases hb_exp with ⟨f₁, hf₁_M, hb_f₁⟩
      have he_last_NM : e_last ∈ N \ M := hP.last_edge e_last he_last
      have he_last_N : e_last ∈ N := (Finset.mem_sdiff.mp he_last_NM).1
      have he_last_not_M : e_last ∉ M := (Finset.mem_sdiff.mp he_last_NM).2
      have hb_e_last : b ∈ G.ends e_last := hP.last_inc e_last he_last b hb_last
      have hf₁_ne_e_last : f₁ ≠ e_last := fun h => he_last_not_M (h ▸ hf₁_M)
      have hf₁_not_N : f₁ ∉ N := fun hf₁_N =>
        hN f₁ hf₁_N e_last he_last_N hf₁_ne_e_last b hb_f₁ hb_e_last
      have hf₁_MN : f₁ ∈ M \ N := Finset.mem_sdiff.mpr ⟨hf₁_M, hf₁_not_N⟩
      obtain ⟨w₁, hbw₁, hends₁⟩ := exists_other_end G f₁ hb_f₁
      by_cases hw₁_exp : PathsTreesFlowers.Duality.IsExposed G N w₁
      · obtain ⟨u_last, _, hends_last⟩ := exists_other_end G e_last hb_e_last
        have hends_last_swap : G.ends e_last = s(u_last, b) := by
          rw [hends_last, Sym2.eq_swap]
        obtain ⟨hN', hN'_card, _, _⟩ :=
          swap_matching hN he_last_N hends_last_swap hends₁ hw₁_exp
        let N' := insert f₁ (N.erase e_last)
        have hdiff_eq : N' \ M = (N \ M).erase e_last := by
          ext e
          simp only [N', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨rfl | ⟨hne, heN⟩, heM⟩
            · exact False.elim (heM hf₁_M)
            · exact ⟨hne, heN, heM⟩
          · rintro ⟨hne, heN, heM⟩
            exact ⟨Or.inr ⟨hne, heN⟩, heM⟩
        have hdiff_lt : (N' \ M).card < (N \ M).card := by
          rw [hdiff_eq]
          exact Finset.card_erase_lt_of_mem he_last_NM
        exact Or.inr ⟨N', hN', hN'_card, hdiff_lt⟩
      · simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hw₁_exp
        rcases hw₁_exp with ⟨f₂, hf₂_N, hw₁_f₂⟩
        have hw₁_f₁ : w₁ ∈ G.ends f₁ := by rw [hends₁]; simp
        have hf₂_ne_f₁ : f₂ ≠ f₁ := fun h => hf₁_not_N (h ▸ hf₂_N)
        have hf₂_not_M : f₂ ∉ M := fun hf₂_M =>
          hM f₂ hf₂_M f₁ hf₁_M hf₂_ne_f₁ w₁ hw₁_f₂ hw₁_f₁
        have hf₂_NM : f₂ ∈ N \ M := Finset.mem_sdiff.mpr ⟨hf₂_N, hf₂_not_M⟩
        obtain ⟨w₂, hw₁w₂, hends₂⟩ := exists_other_end G f₂ hw₁_f₂
        have hP' : IsOddAugPrefix G M N (vs ++ [w₁, w₂]) (es ++ [f₁, f₂]) :=
          isOddAugPrefix_append_two hM hN hP hb_last he_last hf₁_MN hf₂_NM
            hbw₁ hw₁w₂ hends₁ hends₂
        have hlen_le : (vs ++ [w₁, w₂]).length ≤ Fintype.card V :=
          hP'.alt.1.1.length_le_card
        have hlen_eq : (vs ++ [w₁, w₂]).length = vs.length + 2 := by simp
        omega
  | succ r' ih =>
    intro vs es hr hP
    have hvs_ne : vs ≠ [] := by
      intro hnil
      have := hP.alt.1.2.1
      rw [hnil] at this
      simp at this
    obtain ⟨b, hb_last⟩ := exists_getLast?_of_ne_nil vs hvs_ne
    obtain ⟨e_last, he_last⟩ := exists_getLast?_of_ne_nil es hP.ne_nil
    by_cases hb_exp : PathsTreesFlowers.Duality.IsExposed G M b
    · refine Or.inl ⟨vs, es, hP.alt, hP.ne_nil, hP.head_exp, ?_⟩
      intro b' hb'
      rw [Option.mem_def, hb_last, Option.some.injEq] at hb'
      subst hb'
      exact hb_exp
    · simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hb_exp
      rcases hb_exp with ⟨f₁, hf₁_M, hb_f₁⟩
      have he_last_NM : e_last ∈ N \ M := hP.last_edge e_last he_last
      have he_last_N : e_last ∈ N := (Finset.mem_sdiff.mp he_last_NM).1
      have he_last_not_M : e_last ∉ M := (Finset.mem_sdiff.mp he_last_NM).2
      have hb_e_last : b ∈ G.ends e_last := hP.last_inc e_last he_last b hb_last
      have hf₁_ne_e_last : f₁ ≠ e_last := fun h => he_last_not_M (h ▸ hf₁_M)
      have hf₁_not_N : f₁ ∉ N := fun hf₁_N =>
        hN f₁ hf₁_N e_last he_last_N hf₁_ne_e_last b hb_f₁ hb_e_last
      have hf₁_MN : f₁ ∈ M \ N := Finset.mem_sdiff.mpr ⟨hf₁_M, hf₁_not_N⟩
      obtain ⟨w₁, hbw₁, hends₁⟩ := exists_other_end G f₁ hb_f₁
      by_cases hw₁_exp : PathsTreesFlowers.Duality.IsExposed G N w₁
      · obtain ⟨u_last, _, hends_last⟩ := exists_other_end G e_last hb_e_last
        have hends_last_swap : G.ends e_last = s(u_last, b) := by
          rw [hends_last, Sym2.eq_swap]
        obtain ⟨hN', hN'_card, _, _⟩ :=
          swap_matching hN he_last_N hends_last_swap hends₁ hw₁_exp
        let N' := insert f₁ (N.erase e_last)
        have hdiff_eq : N' \ M = (N \ M).erase e_last := by
          ext e
          simp only [N', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨rfl | ⟨hne, heN⟩, heM⟩
            · exact False.elim (heM hf₁_M)
            · exact ⟨hne, heN, heM⟩
          · rintro ⟨hne, heN, heM⟩
            exact ⟨Or.inr ⟨hne, heN⟩, heM⟩
        have hdiff_lt : (N' \ M).card < (N \ M).card := by
          rw [hdiff_eq]
          exact Finset.card_erase_lt_of_mem he_last_NM
        exact Or.inr ⟨N', hN', hN'_card, hdiff_lt⟩
      · simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hw₁_exp
        rcases hw₁_exp with ⟨f₂, hf₂_N, hw₁_f₂⟩
        have hw₁_f₁ : w₁ ∈ G.ends f₁ := by rw [hends₁]; simp
        have hf₂_ne_f₁ : f₂ ≠ f₁ := fun h => hf₁_not_N (h ▸ hf₂_N)
        have hf₂_not_M : f₂ ∉ M := fun hf₂_M =>
          hM f₂ hf₂_M f₁ hf₁_M hf₂_ne_f₁ w₁ hw₁_f₂ hw₁_f₁
        have hf₂_NM : f₂ ∈ N \ M := Finset.mem_sdiff.mpr ⟨hf₂_N, hf₂_not_M⟩
        obtain ⟨w₂, hw₁w₂, hends₂⟩ := exists_other_end G f₂ hw₁_f₂
        have hP' : IsOddAugPrefix G M N (vs ++ [w₁, w₂]) (es ++ [f₁, f₂]) :=
          isOddAugPrefix_append_two hM hN hP hb_last he_last hf₁_MN hf₂_NM
            hbw₁ hw₁w₂ hends₁ hends₂
        have hlen_le : (vs ++ [w₁, w₂]).length ≤ Fintype.card V :=
          hP'.alt.1.1.length_le_card
        have hlen_eq : (vs ++ [w₁, w₂]).length = vs.length + 2 := by simp
        have hr' : Fintype.card V - (vs ++ [w₁, w₂]).length ≤ r' := by omega
        exact ih (vs ++ [w₁, w₂]) (es ++ [f₁, f₂]) hr' hP'

lemma exists_aug_path_of_card_lt {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) :
    ∀ (k : ℕ) (N : Finset E),
      (N \ M).card ≤ k →
      IsMatching G N →
      M.card < N.card →
      ∃ (vs : List V) (es : List E), IsAlternatingPath G M vs es ∧ es ≠ [] ∧
        (∀ a ∈ vs.head?, PathsTreesFlowers.Duality.IsExposed G M a) ∧ (∀ b ∈ vs.getLast?, PathsTreesFlowers.Duality.IsExposed G M b) := by
  intro k
  induction k with
  | zero =>
    intro N hk hN hcard
    obtain ⟨_, e₀, he₀, _, _⟩ := exists_exposed_and_edge_of_card_lt hN hcard
    have hpos : 0 < (N \ M).card := Finset.card_pos.mpr ⟨e₀, he₀⟩
    omega
  | succ k' ih =>
    intro N hk hN hcard
    obtain ⟨a, e₀, he₀, ha_exp, ha_e₀⟩ := exists_exposed_and_edge_of_card_lt hN hcard
    obtain ⟨b₀, hab₀, hends₀⟩ := exists_other_end G e₀ ha_e₀
    have hP₀ : IsOddAugPrefix G M N [a, b₀] [e₀] :=
      isOddAugPrefix_singleton hab₀ hends₀ he₀ ha_exp
    rcases extend_oddAugPrefix hM hN (Fintype.card V - [a, b₀].length) [a, b₀] [e₀] le_rfl hP₀ with
      haug | ⟨N', hN', hN'_card, hdiff_lt⟩
    · exact haug
    · exact ih N' (by omega) hN' (hN'_card ▸ hcard)

end SolPathsTreesFlowersBerge37

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality (IsMaxMatching IsPath IsAlternatingPath)
open SolPathsTreesFlowersBerge37

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M) :
    ¬ IsMaxMatching G M ↔
      ∃ (vs : List V) (es : List E), IsAlternatingPath G M vs es ∧ es ≠ [] ∧
        (∀ a ∈ vs.head?, PathsTreesFlowers.Duality.IsExposed G M a) ∧
        (∀ b ∈ vs.getLast?, PathsTreesFlowers.Duality.IsExposed G M b) := by
  constructor
  · intro hNotMax
    simp only [IsMaxMatching, hM, true_and, not_forall, not_le] at hNotMax
    rcases hNotMax with ⟨N, hN, hcard⟩
    exact exists_aug_path_of_card_lt hM (N \ M).card N le_rfl hN hcard
  · rintro ⟨vs, es, hAlt, hes, ha, hb⟩ hMax
    obtain ⟨M', hM', hcard⟩ :=
      exists_larger_matching_of_aug_path vs es M hM hAlt hes ha hb
    have hle := hMax.2 M' hM'
    omega
