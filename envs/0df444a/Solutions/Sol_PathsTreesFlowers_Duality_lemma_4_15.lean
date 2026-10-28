-- Prove2me | solution 1 for PathsTreesFlowers.Duality.lemma_4_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:59:40.545643+00:00
-- url     : https://prove2.me/submissions/353dec78-ee30-450d-bda5-d4cf3652d9f4

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
import Definitions.Def_PathsTreesFlowers_Duality_Shrink
import Theorems.Thm_PathsTreesFlowers_Duality_berge_3_7

namespace SolPathsTreesFlowersLemma415

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: `blockPartition` and matching swap helpers -/

lemma toPart_blockPartition_eq_iff {U : Finset V} {a b : V} :
    toPart (blockPartition U) a = toPart (blockPartition U) b ↔ a = b ∨ (a ∈ U ∧ b ∈ U) := by
  rw [toPart, toPart, Subtype.mk.injEq,
    ← Finpartition.mem_part_iff_part_eq_part _ (Finset.mem_univ a) (Finset.mem_univ b),
    blockPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (b = a ∨ (b ∈ U ∧ a ∈ U)) ↔ (a = b ∨ (a ∈ U ∧ b ∈ U))
  tauto

lemma insidePart_blockPartition_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {e : E} :
    InsidePart G (blockPartition U) e ↔ G.ends e ∈ U.sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have hne : a ≠ b := by
    rintro rfl
    exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  unfold InsidePart
  simp only [hab, Finset.mk_mem_sym2_iff]
  rw [← Finpartition.mem_part_iff_exists, blockPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (b = a ∨ (b ∈ U ∧ a ∈ U)) ↔ (a ∈ U ∧ b ∈ U)
  exact ⟨fun h => (h.resolve_left hne.symm).symm, fun h => Or.inr h.symm⟩

lemma not_insidePart_of_not_mem {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {e : E} {x : V} (hxU : x ∉ U) (hxe : x ∈ G.ends e) :
    ¬ InsidePart G (blockPartition U) e := by
  rw [insidePart_blockPartition_iff, Finset.mem_sym2_iff]
  intro h
  exact hxU (h x hxe)

lemma not_mem_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    {e : E} {u : V} (hu_end : u ∈ G.ends e) (hu_exp : IsExposed G M u) :
    e ∉ M :=
  fun he => hu_exp e he hu_end

lemma isMatching_erase {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) (e : E) :
    IsMatching G (M.erase e) := by
  intro e₁ he₁ e₂ he₂ hne v hv₁ hv₂
  exact hM e₁ (Finset.mem_erase.mp he₁).2 e₂ (Finset.mem_erase.mp he₂).2 hne v hv₁ hv₂

lemma isExposed_erase_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    {v : V} (hv : IsExposed G M v) (e : E) :
    IsExposed G (M.erase e) v := by
  intro f hf
  exact hv f (Finset.mem_erase.mp hf).2

lemma isExposed_erase_of_mem_ends {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) {e : E} (he : e ∈ M) {v : V} (hv : v ∈ G.ends e) :
    IsExposed G (M.erase e) v := by
  intro f hf hvf
  have hne : f ≠ e := (Finset.mem_erase.mp hf).1
  have hfM : f ∈ M := (Finset.mem_erase.mp hf).2
  exact hM e he f hfM hne.symm v hv hvf

lemma isMatching_insert_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (hM : IsMatching G M) {e : E} {u v : V} (hends : G.ends e = s(u, v))
    (hu : IsExposed G M u) (hv : IsExposed G M v) :
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
    (hwu : w ≠ u) (hwv : w ≠ v) (hw : IsExposed G M w) :
    IsExposed G (insert e M) w := by
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
    (hends_add : G.ends e_add = s(y, z)) (hz : IsExposed G K z) :
    IsMatching G (insert e_add (K.erase e_rem)) ∧
      (insert e_add (K.erase e_rem)).card = K.card ∧
      (x ≠ y → x ≠ z → IsExposed G (insert e_add (K.erase e_rem)) x) ∧
      (∀ w : V, w ≠ y → w ≠ z → IsExposed G K w → IsExposed G (insert e_add (K.erase e_rem)) w) := by
  have hK_er : IsMatching G (K.erase e_rem) := isMatching_erase hK e_rem
  have hy_end : y ∈ G.ends e_rem := by rw [hends_rem]; simp
  have hx_end : x ∈ G.ends e_rem := by rw [hends_rem]; simp
  have hy_exp : IsExposed G (K.erase e_rem) y := isExposed_erase_of_mem_ends hK he_rem hy_end
  have hx_exp : IsExposed G (K.erase e_rem) x := isExposed_erase_of_mem_ends hK he_rem hx_end
  have hz_exp : IsExposed G (K.erase e_rem) z := isExposed_erase_of_isExposed hz e_rem
  obtain ⟨_, hK', hcard'⟩ :=
    isMatching_insert_of_isExposed hK_er hends_add hy_exp hz_exp
  have hcard_er : (K.erase e_rem).card + 1 = K.card := Finset.card_erase_add_one he_rem
  refine ⟨hK', hcard'.trans hcard_er, ?_, ?_⟩
  · intro hxy hxz
    exact isExposed_insert_of_ne hends_add hxy hxz hx_exp
  · intro w hwy hwz hw
    exact isExposed_insert_of_ne hends_add hwy hwz (isExposed_erase_of_isExposed hw e_rem)

/-! ### Part 2: Path and reversal helpers -/

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

lemma zipWith_sym2_reverse : ∀ (vs : List V),
    List.zipWith (fun a b => s(a, b)) vs.reverse vs.reverse.tail =
      (List.zipWith (fun a b => s(a, b)) vs vs.tail).reverse
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have hlast : (b :: t).reverse.getLast? = some b := by simp
    calc List.zipWith (fun x y => s(x, y)) (a :: b :: t).reverse (a :: b :: t).reverse.tail
        = List.zipWith (fun x y => s(x, y)) ((b :: t).reverse ++ [a]) ((b :: t).reverse ++ [a]).tail := by
          simp
      _ = List.zipWith (fun x y => s(x, y)) (b :: t).reverse (b :: t).reverse.tail ++ [s(b, a)] :=
          zipWith_tail_append_singleton (b :: t).reverse b a hlast
      _ = (List.zipWith (fun x y => s(x, y)) (b :: t) (b :: t).tail).reverse ++ [s(a, b)] := by
          rw [zipWith_sym2_reverse (b :: t), Sym2.eq_swap]
      _ = (List.zipWith (fun x y => s(x, y)) (a :: b :: t) (a :: b :: t).tail).reverse := by
          simp

lemma isChain_reverse_symm {α : Type*} {R : α → α → Prop} (hsymm : ∀ x y, R x y → R y x) :
    ∀ (es : List α), es.IsChain R → es.reverse.IsChain R
  | [], _ => .nil
  | [a], _ => .singleton a
  | a :: b :: t, .cons_cons hab hchain => by
    have hlast : (b :: t).reverse.getLast? = some b := by simp
    simpa using isChain_append_singleton R (b :: t).reverse b a
      (isChain_reverse_symm hsymm (b :: t) hchain) hlast (hsymm a b hab)

lemma isAlternatingPath_reverse {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {vs : List V} {es : List E} (hAlt : IsAlternatingPath G M vs es) :
    IsAlternatingPath G M vs.reverse es.reverse := by
  refine ⟨⟨List.nodup_reverse.mpr hAlt.1.1, by simp [hAlt.1.2.1], ?_⟩, ?_⟩
  · rw [List.map_reverse, hAlt.1.2.2, zipWith_sym2_reverse]
  · exact isChain_reverse_symm (fun x y h => by tauto) es hAlt.2

/-! ### Part 3: Shrunk exposure and base-case contradiction -/

lemma isExposed_shrink_of_not_mem_U {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {M : Finset E} {x : V} (hxU : x ∉ U) (hx_exp : IsExposed G M x) :
    IsExposed (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M)
      (toPart (blockPartition U) x) := by
  set P := blockPartition U
  intro e he hxe
  have heM : e.1 ∈ M := Finset.mem_subtype.mp he
  change toPart P x ∈ Sym2.map (toPart P) (G.ends e.1) at hxe
  rw [Sym2.mem_map] at hxe
  rcases hxe with ⟨y, hye, hyx⟩
  rcases toPart_blockPartition_eq_iff.mp hyx with rfl | ⟨_, hxU'⟩
  · exact hx_exp e.1 heM hye
  · exact hxU hxU'

lemma shrinkMatching_insert_erase {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {M : Finset E}
    (e_add e_rem : {e : E // ¬ InsidePart G P e}) :
    shrinkMatching G P (insert e_add.1 (M.erase e_rem.1)) =
      insert e_add ((shrinkMatching G P M).erase e_rem) := by
  ext e
  simp [shrinkMatching, Finset.mem_subtype, Subtype.ext_iff]

lemma no_aug_path_from_outside_U {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {u : V} (hu : u ∈ U) :
    ∀ (vs : List V) (es : List E) (M : Finset E),
      IsMatching G M →
      IsAlternatingPath G M vs es →
      es ≠ [] →
      (∀ a ∈ vs.head?, a ∉ U ∧ IsExposed G M a) →
      (∀ b ∈ vs.getLast?, IsExposed G M b) →
      IsMaxMatching (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M) →
      IsExposed (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M)
        (toPart (blockPartition U) u) →
      False
  | _, [], _, _, _, hes, _, _, _, _ => hes rfl
  | [], _ :: _, _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [_], _ :: _, _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [v₀, v₁], [e₀], M, _hM, hAlt, _, ha, hb, hMax_sh, hu_exp => by
    set P := blockPartition U
    have hends : G.ends e₀ = s(v₀, v₁) := by simpa using hAlt.1.2.2
    obtain ⟨hv₀_not_U, hv₀_exp⟩ := ha v₀ (by simp)
    have hv₁_exp : IsExposed G M v₁ := hb v₁ (by simp)
    have he₀_not_in : ¬ InsidePart G P e₀ :=
      not_insidePart_of_not_mem hv₀_not_U (by rw [hends]; simp)
    let e₀' : {e : E // ¬ InsidePart G P e} := ⟨e₀, he₀_not_in⟩
    have hends_sh : (shrink G P).ends e₀' = s(toPart P v₀, toPart P v₁) := by
      change Sym2.map (toPart P) (G.ends e₀) = _
      rw [hends, Sym2.map_mk]
    have hv₀_sh_exp := isExposed_shrink_of_not_mem_U hv₀_not_U hv₀_exp
    have hv₁_sh_exp : IsExposed (shrink G P) (shrinkMatching G P M) (toPart P v₁) := by
      by_cases hv₁U : v₁ ∈ U
      · have h_eq : toPart P v₁ = toPart P u := toPart_blockPartition_eq_iff.mpr (Or.inr ⟨hv₁U, hu⟩)
        exact h_eq ▸ hu_exp
      · exact isExposed_shrink_of_not_mem_U hv₁U hv₁_exp
    obtain ⟨_, hM'_sh, hcard'_sh⟩ :=
      isMatching_insert_of_isExposed hMax_sh.1 hends_sh hv₀_sh_exp hv₁_sh_exp
    have hle := hMax_sh.2 (insert e₀' (shrinkMatching G P M)) hM'_sh
    omega
  | [_, _], _ :: _ :: _, _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | _ :: _ :: _ :: _, [_], _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [v₀, v₁, v₂], [e₀, e₁], M, _hM, hAlt, _, ha, hb, _, _ => by
    have hmap := hAlt.1.2.2
    simp only [List.map, List.tail_cons, List.zipWith, List.cons.injEq, and_true] at hmap
    rcases hmap with ⟨hends₀, hends₁⟩
    obtain ⟨_, hv₀_exp⟩ := ha v₀ (by simp)
    have hv₂_exp : IsExposed G M v₂ := hb v₂ (by simp)
    have he₀_not : e₀ ∉ M := not_mem_of_isExposed (by rw [hends₀]; simp) hv₀_exp
    cases hAlt.2 with
    | cons_cons h01 _ =>
      have he₁_mem : e₁ ∈ M := by tauto
      exact hv₂_exp e₁ he₁_mem (by rw [hends₁]; simp)
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | v₀ :: v₁ :: v₂ :: vs', e₀ :: e₁ :: e₂ :: es', M, hM, hAlt, _, ha, hb, hMax_sh, hu_exp => by
    set P := blockPartition U
    have hmap := hAlt.1.2.2
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.cons.injEq] at hmap
    rcases hmap with ⟨hends₀, hends₁, hmap'⟩
    obtain ⟨hv₀_not_U, hv₀_exp⟩ := ha v₀ (by simp)
    have he₀_not_in : ¬ InsidePart G P e₀ :=
      not_insidePart_of_not_mem hv₀_not_U (by rw [hends₀]; simp)
    let e₀' : {e : E // ¬ InsidePart G P e} := ⟨e₀, he₀_not_in⟩
    have hends₀_sh : (shrink G P).ends e₀' = s(toPart P v₀, toPart P v₁) := by
      change Sym2.map (toPart P) (G.ends e₀) = _
      rw [hends₀, Sym2.map_mk]
    have hv₀_sh_exp := isExposed_shrink_of_not_mem_U hv₀_not_U hv₀_exp
    by_cases hv₁U : v₁ ∈ U
    · have hv₁_sh_exp : IsExposed (shrink G P) (shrinkMatching G P M) (toPart P v₁) := by
        have h_eq : toPart P v₁ = toPart P u := toPart_blockPartition_eq_iff.mpr (Or.inr ⟨hv₁U, hu⟩)
        exact h_eq ▸ hu_exp
      obtain ⟨_, hM'_sh, hcard'_sh⟩ :=
        isMatching_insert_of_isExposed hMax_sh.1 hends₀_sh hv₀_sh_exp hv₁_sh_exp
      have hle := hMax_sh.2 (insert e₀' (shrinkMatching G P M)) hM'_sh
      omega
    · have he₀_not : e₀ ∉ M := not_mem_of_isExposed (by rw [hends₀]; simp) hv₀_exp
      cases hAlt.2 with
      | cons_cons h01 hchain1 =>
        cases hchain1 with
        | cons_cons h12 hchain' =>
          have he₁_mem : e₁ ∈ M := by tauto
          have he₁_not_in : ¬ InsidePart G P e₁ :=
            not_insidePart_of_not_mem hv₁U (by rw [hends₁]; simp)
          let e₁' : {e : E // ¬ InsidePart G P e} := ⟨e₁, he₁_not_in⟩
          have he₁'_mem : e₁' ∈ shrinkMatching G P M := Finset.mem_subtype.mpr he₁_mem
          have hends₁_sh : (shrink G P).ends e₁' = s(toPart P v₁, toPart P v₂) := by
            change Sym2.map (toPart P) (G.ends e₁) = _
            rw [hends₁, Sym2.map_mk]
          have hv₂_not_U : v₂ ∉ U := by
            intro hv₂U
            have h_eq : toPart P v₂ = toPart P u := toPart_blockPartition_eq_iff.mpr (Or.inr ⟨hv₂U, hu⟩)
            exact hu_exp e₁' he₁'_mem (by rw [hends₁_sh, h_eq]; simp)
          have hnodup := hAlt.1.1
          rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnodup
          rcases hnodup with ⟨hv0_not, hv1_not, hv2_not, hnodup_vs'⟩
          simp only [List.mem_cons, not_or] at hv0_not hv1_not
          rcases hv0_not with ⟨hv01, hv02, hv0_vs'⟩
          rcases hv1_not with ⟨hv12, hv1_vs'⟩
          have hpath' : IsPath G (v₂ :: vs') (e₂ :: es') := by
            refine ⟨List.nodup_cons.mpr ⟨hv2_not, hnodup_vs'⟩, ?_, hmap'⟩
            have := hAlt.1.2.1; simp only [List.length_cons] at this ⊢; omega
          have hends₁_swap : G.ends e₁ = s(v₂, v₁) := hends₁.trans Sym2.eq_swap
          have hends₀_swap : G.ends e₀ = s(v₁, v₀) := hends₀.trans Sym2.eq_swap
          obtain ⟨hM₁, _, hv₂_exp_fn, hw_exp_fn⟩ :=
            swap_matching hM he₁_mem hends₁_swap hends₀_swap hv₀_exp
          let M₁ := insert e₀ (M.erase e₁)
          have hv₂_exp : IsExposed G M₁ v₂ := hv₂_exp_fn (Ne.symm hv12) (Ne.symm hv02)
          have hmem_iff : ∀ e ∈ e₂ :: es', (e ∈ M₁ ↔ e ∈ M) := by
            intro e he
            have he_ne_e₀ : e ≠ e₀ := by
              intro h_eq
              have hv₁_mem : v₁ ∈ v₂ :: vs' :=
                ends_mem_verts_of_isPath hpath' (h_eq ▸ he) (by rw [hends₀]; simp)
              rcases List.mem_cons.mp hv₁_mem with rfl | hmem
              · exact hv12 rfl
              · exact hv1_vs' hmem
            have he_ne_e₁ : e ≠ e₁ := by
              intro h_eq
              have hv₁_mem : v₁ ∈ v₂ :: vs' :=
                ends_mem_verts_of_isPath hpath' (h_eq ▸ he) (by rw [hends₁]; simp)
              rcases List.mem_cons.mp hv₁_mem with rfl | hmem
              · exact hv12 rfl
              · exact hv1_vs' hmem
            simp [M₁, Finset.mem_insert, Finset.mem_erase, he_ne_e₀, he_ne_e₁]
          have hAlt' : IsAlternatingPath G M₁ (v₂ :: vs') (e₂ :: es') := by
            refine ⟨hpath', isChain_congr (e₂ :: es') ?_ hchain'⟩
            intro x hx y hy hxy
            rw [hmem_iff x hx, hmem_iff y hy]
            exact hxy
          have hlast_exp' : ∀ b ∈ (v₂ :: vs').getLast?, IsExposed G M₁ b := by
            intro b hb_last
            have hb_orig : b ∈ (v₀ :: v₁ :: v₂ :: vs').getLast? := by simpa using hb_last
            have hb_mem : b ∈ v₂ :: vs' := List.mem_of_mem_getLast? hb_last
            have hbv₁ : b ≠ v₁ := by
              rintro rfl
              rcases List.mem_cons.mp hb_mem with rfl | hmem
              · exact hv12 rfl
              · exact hv1_vs' hmem
            have hbv₀ : b ≠ v₀ := by
              rintro rfl
              rcases List.mem_cons.mp hb_mem with rfl | hmem
              · exact hv02 rfl
              · exact hv0_vs' hmem
            exact hw_exp_fn b hbv₁ hbv₀ (hb b hb_orig)
          have hends₁_sh_swap : (shrink G P).ends e₁' = s(toPart P v₂, toPart P v₁) :=
            hends₁_sh.trans Sym2.eq_swap
          have hends₀_sh_swap : (shrink G P).ends e₀' = s(toPart P v₁, toPart P v₀) :=
            hends₀_sh.trans Sym2.eq_swap
          obtain ⟨hM₁_sh, hM₁_sh_card, _, hw_sh_exp⟩ :=
            swap_matching hMax_sh.1 he₁'_mem hends₁_sh_swap hends₀_sh_swap hv₀_sh_exp
          rw [← shrinkMatching_insert_erase e₀' e₁'] at hM₁_sh hM₁_sh_card hw_sh_exp
          have hMax_sh' : IsMaxMatching (shrink G P) (shrinkMatching G P M₁) :=
            ⟨hM₁_sh, fun M' hM' => hM₁_sh_card.symm ▸ hMax_sh.2 M' hM'⟩
          have hu_ne_v₁ : toPart P u ≠ toPart P v₁ := by
            intro h_eq
            rcases toPart_blockPartition_eq_iff.mp h_eq with rfl | ⟨_, hv₁U'⟩
            · exact hv₁U hu
            · exact hv₁U hv₁U'
          have hu_ne_v₀ : toPart P u ≠ toPart P v₀ := by
            intro h_eq
            rcases toPart_blockPartition_eq_iff.mp h_eq with rfl | ⟨_, hv₀U'⟩
            · exact hv₀_not_U hu
            · exact hv₀_not_U hv₀U'
          have hu_exp' : IsExposed (shrink G P) (shrinkMatching G P M₁) (toPart P u) :=
            hw_sh_exp (toPart P u) hu_ne_v₁ hu_ne_v₀ hu_exp
          exact no_aug_path_from_outside_U hu (v₂ :: vs') (e₂ :: es') M₁ hM₁ hAlt'
            (List.cons_ne_nil _ _)
            (fun a ha' => by
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
              subst ha'
              exact ⟨hv₂_not_U, hv₂_exp⟩)
            hlast_exp' hMax_sh' hu_exp'

lemma lemma_4_15_of_exposed_toPart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V} {u : V} (hu : u ∈ U)
    (h1 : (exposedIn G U M).card = 1)
    (h2 : IsMaxMatching (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M))
    (hu_exp : IsExposed (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M)
      (toPart (blockPartition U) u)) :
    IsMaxMatching G M := by
  by_contra hnot
  rw [berge_3_7 G M hM] at hnot
  rcases hnot with ⟨vs, es, hAlt, hes_ne, hhead, hlast⟩
  have hvs_len : 2 ≤ vs.length := by
    have := List.length_pos_of_ne_nil hes_ne
    have := hAlt.1.2.1; omega
  have hv₀_mem_head : vs[0]'(by omega) ∈ vs.head? := by
    cases vs with
    | nil => simp at hvs_len
    | cons a _ => simp
  have hvm_mem_last : vs[vs.length - 1]'(by omega) ∈ vs.getLast? := by
    rw [Option.mem_def, List.getLast?_eq_getElem?]
    exact List.getElem?_eq_getElem (by omega)
  have hv₀_exp : IsExposed G M (vs[0]'(by omega)) := hhead _ hv₀_mem_head
  have hvm_exp : IsExposed G M (vs[vs.length - 1]'(by omega)) := hlast _ hvm_mem_last
  have hne_0_m : vs[0]'(by omega) ≠ vs[vs.length - 1]'(by omega) := by
    intro h_eq
    have := (List.Nodup.getElem_inj_iff hAlt.1.1).mp h_eq
    omega
  by_cases hv₀U : vs[0]'(by omega) ∈ U
  · have hvm_not_U : vs[vs.length - 1]'(by omega) ∉ U := by
      intro hvmU
      have hv₀_in : vs[0]'(by omega) ∈ exposedIn G U M :=
        Finset.mem_filter.mpr ⟨hv₀U, fun e heM _ => hv₀_exp e heM⟩
      have hvm_in : vs[vs.length - 1]'(by omega) ∈ exposedIn G U M :=
        Finset.mem_filter.mpr ⟨hvmU, fun e heM _ => hvm_exp e heM⟩
      have hle1 : (exposedIn G U M).card ≤ 1 := by omega
      exact hne_0_m (Finset.card_le_one.mp hle1 _ hv₀_in _ hvm_in)
    have hAlt_rev := isAlternatingPath_reverse hAlt
    have hes_rev_ne : es.reverse ≠ [] := by simp [hes_ne]
    exact no_aug_path_from_outside_U hu vs.reverse es.reverse M hM hAlt_rev hes_rev_ne
      (fun a ha_rev => by
        rw [List.head?_reverse] at ha_rev
        have ha_eq : a = vs[vs.length - 1]'(by omega) := by
          rw [Option.mem_def] at ha_rev hvm_mem_last
          exact Option.some.inj (ha_rev.symm.trans hvm_mem_last)
        subst ha_eq
        exact ⟨hvm_not_U, hvm_exp⟩)
      (fun b hb_rev => by
        rw [List.getLast?_reverse] at hb_rev
        exact hhead b hb_rev)
      h2 hu_exp
  · exact no_aug_path_from_outside_U hu vs es M hM hAlt hes_ne
      (fun a ha => by
        have ha_eq : a = vs[0]'(by omega) := by
          rw [Option.mem_def] at ha hv₀_mem_head
          exact Option.some.inj (ha.symm.trans hv₀_mem_head)
        subst ha_eq
        exact ⟨hv₀U, hv₀_exp⟩)
      hlast h2 hu_exp

/-! ### Part 4: Stem reduction by 2-edge induction -/

lemma exposedIn_insert_erase_of_not_insidePart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {M : Finset E} {e_add e_rem : E}
    (hadd : ¬ InsidePart G (blockPartition U) e_add)
    (hrem : ¬ InsidePart G (blockPartition U) e_rem) :
    exposedIn G U (insert e_add (M.erase e_rem)) = exposedIn G U M := by
  rw [insidePart_blockPartition_iff] at hadd hrem
  ext v
  simp only [exposedIn, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  refine and_congr_right fun _ => ⟨fun h e heM heU => ?_, fun h e he_ins heU => ?_⟩
  · have he_ne_rem : e ≠ e_rem := fun h_eq => hrem (h_eq ▸ heU)
    exact h e (Or.inr ⟨he_ne_rem, heM⟩) heU
  · rcases he_ins with rfl | ⟨_, heM⟩
    · exact False.elim (hadd heU)
    · exact h e heM heU

lemma stem_induction {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {u : V} (hu : u ∈ U) :
    ∀ (svs : List {W : Finset V // W ∈ (blockPartition U).parts})
      (ses : List {e : E // ¬ InsidePart G (blockPartition U) e})
      (M : Finset E),
      IsMatching G M →
      (exposedIn G U M).card = 1 →
      IsMaxMatching (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M) →
      IsStem (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M) svs ses →
      svs.getLast? = some (toPart (blockPartition U) u) →
      IsMaxMatching G M
  | [], _, _, _, _, _, _, hlast => by cases hlast
  | [w₀], [], M, hM, h1, h2, hSt, hlast => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    have hu_exp : IsExposed (shrink G (blockPartition U))
        (shrinkMatching G (blockPartition U) M) (toPart (blockPartition U) u) :=
      hSt.2.1 (toPart (blockPartition U) u) (by simp)
    exact lemma_4_15_of_exposed_toPart hM hu h1 h2 hu_exp
  | [_], _ :: _, _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | _ :: _ :: _, [], _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | [w₀, w₁], [e₀], M, _, _, _, hSt, _ => by
    have hends₀ : (shrink G (blockPartition U)).ends e₀ = s(w₀, w₁) := by
      simpa using hSt.1.1.2.2
    have hw₀_exp := hSt.2.1 w₀ (by simp)
    have he₀_mem := hSt.2.2 e₀ (by simp)
    exact False.elim (hw₀_exp e₀ he₀_mem (by rw [hends₀]; simp))
  | [_, _], _ :: _ :: _, _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | _ :: _ :: _ :: _, [_], _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | w₀ :: w₁ :: w₂ :: svs', e₀ :: e₁ :: ses', M, hM, h1, h2, hSt, hlast => by
    let P := blockPartition U
    have hmap := hSt.1.1.2.2
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.cons.injEq] at hmap
    rcases hmap with ⟨hends₀_sh, hends₁_sh, hmap'⟩
    have hnodup := hSt.1.1.1
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hw0_not, hw1_not, hw2_not, hnodup_svs'⟩
    simp only [List.mem_cons, not_or] at hw0_not hw1_not
    rcases hw0_not with ⟨hw01, hw02, hw0_svs'⟩
    rcases hw1_not with ⟨hw12, hw1_svs'⟩
    have hlast' : (w₂ :: svs').getLast? = some (toPart P u) := by simpa using hlast
    have hu_mem_tail : toPart P u ∈ w₂ :: svs' := List.mem_of_mem_getLast? hlast'
    have hw₀_ne_u : w₀ ≠ toPart P u := by
      rintro rfl
      rcases List.mem_cons.mp hu_mem_tail with h | h
      · exact hw02 h
      · exact hw0_svs' h
    have hw₁_ne_u : w₁ ≠ toPart P u := by
      rintro rfl
      rcases List.mem_cons.mp hu_mem_tail with h | h
      · exact hw12 h
      · exact hw1_svs' h
    have hw₀_exp_sh := hSt.2.1 w₀ (by simp)
    have he₀_not_sh : e₀ ∉ shrinkMatching G P M :=
      not_mem_of_isExposed (by rw [hends₀_sh]; simp) hw₀_exp_sh
    cases hSt.1.2 with
    | cons_cons h01 hchain1 =>
      have he₁_mem_sh : e₁ ∈ shrinkMatching G P M := by tauto
      have he₁_mem : e₁.1 ∈ M := Finset.mem_subtype.mp he₁_mem_sh
      rcases Sym2.exists.mp ⟨G.ends e₀.1, rfl⟩ with ⟨a₀, b₀, hab₀⟩
      have hpair₀ : s(toPart P a₀, toPart P b₀) = s(w₀, w₁) := by
        calc s(toPart P a₀, toPart P b₀) = Sym2.map (toPart P) (G.ends e₀.1) := by
              rw [hab₀, Sym2.map_mk]
          _ = s(w₀, w₁) := hends₀_sh
      have h_ends₀ : ∃ v₀ v₁ : V, toPart P v₀ = w₀ ∧ toPart P v₁ = w₁ ∧ G.ends e₀.1 = s(v₀, v₁) := by
        rw [Sym2.eq_iff] at hpair₀
        rcases hpair₀ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨a₀, b₀, ha, hb, hab₀⟩
        · exact ⟨b₀, a₀, hb, ha, hab₀.trans Sym2.eq_swap⟩
      rcases h_ends₀ with ⟨v₀, v₁, hv₀_w₀, hv₁_w₁, hends₀⟩
      have hv₀_not_U : v₀ ∉ U := by
        intro hv₀U
        exact hw₀_ne_u (hv₀_w₀.symm.trans (toPart_blockPartition_eq_iff.mpr (Or.inr ⟨hv₀U, hu⟩)))
      have hv₁_not_U : v₁ ∉ U := by
        intro hv₁U
        exact hw₁_ne_u (hv₁_w₁.symm.trans (toPart_blockPartition_eq_iff.mpr (Or.inr ⟨hv₁U, hu⟩)))
      rcases Sym2.exists.mp ⟨G.ends e₁.1, rfl⟩ with ⟨a₁, b₁, hab₁⟩
      have hpair₁ : s(toPart P a₁, toPart P b₁) = s(w₁, w₂) := by
        calc s(toPart P a₁, toPart P b₁) = Sym2.map (toPart P) (G.ends e₁.1) := by
              rw [hab₁, Sym2.map_mk]
          _ = s(w₁, w₂) := hends₁_sh
      have h_ends₁ : ∃ v₂ : V, toPart P v₂ = w₂ ∧ G.ends e₁.1 = s(v₁, v₂) := by
        rw [Sym2.eq_iff] at hpair₁
        rcases hpair₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have ha_v₁ : a₁ = v₁ := by
            rcases toPart_blockPartition_eq_iff.mp (ha.trans hv₁_w₁.symm) with rfl | ⟨_, hv₁U⟩
            · rfl
            · exact False.elim (hv₁_not_U hv₁U)
          exact ⟨b₁, hb, ha_v₁ ▸ hab₁⟩
        · have hb_v₁ : b₁ = v₁ := by
            rcases toPart_blockPartition_eq_iff.mp (hb.trans hv₁_w₁.symm) with rfl | ⟨_, hv₁U⟩
            · rfl
            · exact False.elim (hv₁_not_U hv₁U)
          exact ⟨a₁, ha, (hb_v₁ ▸ hab₁).trans Sym2.eq_swap⟩
      rcases h_ends₁ with ⟨v₂, hv₂_w₂, hends₁⟩
      have hv₀_exp : IsExposed G M v₀ := by
        intro f hfM hv₀f
        have hf_not_in : ¬ InsidePart G P f := not_insidePart_of_not_mem hv₀_not_U hv₀f
        have hf_sh : (⟨f, hf_not_in⟩ : {e : E // ¬ InsidePart G P e}) ∈ shrinkMatching G P M :=
          Finset.mem_subtype.mpr hfM
        have hw₀_end : w₀ ∈ (shrink G P).ends ⟨f, hf_not_in⟩ :=
          Sym2.mem_map.mpr ⟨v₀, hv₀f, hv₀_w₀⟩
        exact hw₀_exp_sh ⟨f, hf_not_in⟩ hf_sh hw₀_end
      obtain ⟨hM', hM'_card, _, _⟩ :=
        swap_matching hM he₁_mem (hends₁.trans Sym2.eq_swap) (hends₀.trans Sym2.eq_swap) hv₀_exp
      let M' := insert e₀.1 (M.erase e₁.1)
      have h1' : (exposedIn G U M').card = 1 := by
        rw [exposedIn_insert_erase_of_not_insidePart e₀.2 e₁.2, h1]
      obtain ⟨hM'_sh, hM'_sh_card, hw₂_exp_sh_fn, _⟩ :=
        swap_matching h2.1 he₁_mem_sh (hends₁_sh.trans Sym2.eq_swap)
          (hends₀_sh.trans Sym2.eq_swap) hw₀_exp_sh
      rw [← shrinkMatching_insert_erase e₀ e₁] at hM'_sh hM'_sh_card hw₂_exp_sh_fn
      have hw₂_exp_sh : IsExposed (shrink G P) (shrinkMatching G P M') w₂ :=
        hw₂_exp_sh_fn (Ne.symm hw12) (Ne.symm hw02)
      have h2' : IsMaxMatching (shrink G P) (shrinkMatching G P M') :=
        ⟨hM'_sh, fun N hN => hM'_sh_card.symm ▸ h2.2 N hN⟩
      have hpath_sh' : IsPath (shrink G P) (w₂ :: svs') ses' := by
        refine ⟨List.nodup_cons.mpr ⟨hw2_not, hnodup_svs'⟩, ?_, hmap'⟩
        have := hSt.1.1.2.1; simp only [List.length_cons] at this ⊢; omega
      have hmem_sh_iff : ∀ e ∈ ses', (e ∈ shrinkMatching G P M' ↔ e ∈ shrinkMatching G P M) := by
        intro e he
        have he_ne_e₀ : e ≠ e₀ := by
          intro h_eq
          have hw₁_mem : w₁ ∈ w₂ :: svs' :=
            ends_mem_verts_of_isPath hpath_sh' (h_eq ▸ he) (by rw [hends₀_sh]; simp)
          rcases List.mem_cons.mp hw₁_mem with rfl | hmem
          · exact hw12 rfl
          · exact hw1_svs' hmem
        have he_ne_e₁ : e ≠ e₁ := by
          intro h_eq
          have hw₁_mem : w₁ ∈ w₂ :: svs' :=
            ends_mem_verts_of_isPath hpath_sh' (h_eq ▸ he) (by rw [hends₁_sh]; simp)
          rcases List.mem_cons.mp hw₁_mem with rfl | hmem
          · exact hw12 rfl
          · exact hw1_svs' hmem
        change e ∈ shrinkMatching G P (insert e₀.1 (M.erase e₁.1)) ↔ e ∈ shrinkMatching G P M
        rw [shrinkMatching_insert_erase e₀ e₁]
        simp only [Finset.mem_insert, Finset.mem_erase, he_ne_e₀, false_or]
        exact and_iff_right he_ne_e₁
      have hchain_sh' : ses'.IsChain
          (fun e f => e ∈ shrinkMatching G P M' ↔ f ∉ shrinkMatching G P M') := by
        refine isChain_congr ses' ?_ (List.isChain_cons.mp hchain1).2
        intro x hx y hy hxy
        rw [hmem_sh_iff x hx, hmem_sh_iff y hy]
        exact hxy
      have hlast_ses' : ∀ e ∈ ses'.getLast?, e ∈ shrinkMatching G P M' := by
        intro e he_last
        have he_mem : e ∈ ses' := List.mem_of_mem_getLast? he_last
        have he_orig : e ∈ (e₀ :: e₁ :: ses').getLast? := by
          cases ses' with
          | nil => cases he_last
          | cons a t => simpa using he_last
        rw [hmem_sh_iff e he_mem]
        exact hSt.2.2 e he_orig
      have hSt' : IsStem (shrink G P) (shrinkMatching G P M') (w₂ :: svs') ses' :=
        ⟨⟨hpath_sh', hchain_sh'⟩,
          fun r hr => by
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
            exact hr ▸ hw₂_exp_sh,
          hlast_ses'⟩
      have hMax_M' := stem_induction hu (w₂ :: svs') ses' M' hM' h1' h2' hSt' hlast'
      exact ⟨hM, fun N hN => hM'_card.symm ▸ hMax_M'.2 N hN⟩

end SolPathsTreesFlowersLemma415

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality
open SolPathsTreesFlowersLemma415

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M) (U : Finset V)
    (_hconn : IsConnectedSub G (induced G U))
    (h1 : (exposedIn G U M).card = 1)
    (h2 : IsMaxMatching (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M))
    (h3 : ∃ (svs : List {W : Finset V // W ∈ (blockPartition U).parts})
        (ses : List {e : E // ¬ InsidePart G (blockPartition U) e}),
        IsStem (shrink G (blockPartition U)) (shrinkMatching G (blockPartition U) M) svs ses ∧
          ∃ u ∈ U, svs.getLast? = some (toPart (blockPartition U) u)) :
    IsMaxMatching G M := by
  rcases h3 with ⟨svs, ses, hSt, u, hu, hlast⟩
  exact stem_induction hu svs ses M hM h1 h2 hSt hlast
