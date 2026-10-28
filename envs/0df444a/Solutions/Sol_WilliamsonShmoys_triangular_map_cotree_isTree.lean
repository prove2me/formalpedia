-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_cotree_isTree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:34:25.816613+00:00
-- url     : https://prove2.me/submissions/e168876a-d491-4ac7-a596-4bb57fe66d39

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace A3S56CT

open SimpleGraph WilliamsonShmoys

lemma leaf {W : Type} [Finite W] (G : SimpleGraph W) (hG : G.IsAcyclic) {a b : W}
    (hab : G.Adj a b) : ∃ v w, G.Adj v w ∧ ∀ w', G.Adj v w' → w' = w := by
  haveI : Nonempty W := ⟨a⟩
  have : Finite G.edgeSet := inferInstance
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have h1 := hmax _ _ (Walk.cons hab Walk.nil) (by simp [hab.ne])
  have hnil : ¬p.Nil := by
    intro hn
    rw [Walk.nil_iff_length_eq.mp hn] at h1
    simp at h1
  refine ⟨u, p.snd, p.adj_snd hnil, fun w hadj => ?_⟩
  apply hG.eq_snd_of_adj_start hp hadj
  by_contra hw
  have := hmax _ _ _ (hp.cons hw : (Walk.cons hadj.symm p).IsPath)
  simp at this

variable {V F : Type} [Fintype V] [Fintype F] {H : SimpleGraph V}

def rho (M : TriangularMap H F) (a : H.Dart) : H.Dart :=
  M.dart ((M.dart.symm a.symm).1, (M.dart.symm a.symm).2 + 1)

lemma rho_fst (M : TriangularMap H F) (a : H.Dart) : (rho M a).fst = a.fst := by
  unfold rho
  rw [M.dart_tail]
  have h1 : M.dart ((M.dart.symm a.symm).1, (M.dart.symm a.symm).2) = a.symm := by simp
  have := M.dart_head (M.dart.symm a.symm).1 (M.dart.symm a.symm).2
  rw [h1] at this
  simpa using this.symm

lemma face_rho (M : TriangularMap H F) (a : H.Dart) :
    (M.dart.symm (rho M a)).1 = (M.dart.symm a.symm).1 := by
  simp [rho]

lemma iterate_fst (M : TriangularMap H F) (k : ℕ) (a : H.Dart) :
    ((rho M)^[k] a).fst = a.fst := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', rho_fst, ih]

lemma conn (M : TriangularMap H F) (R : SimpleGraph V) (hRH : R ≤ H) (hRac : R.IsAcyclic)
    [hF : Nonempty F] : (M.cotree R).Connected := by
  refine ⟨fun f0 g => ?_⟩
  by_contra hne
  let S : F → Prop := fun f => (M.cotree R).Reachable f0 f
  let s : H.Dart → Prop := fun a => S (M.dart.symm a).1
  let cut : H.Dart → Prop := fun a => ¬ (s a ↔ s a.symm)
  have cut_symm : ∀ a, cut a.symm ↔ cut a := by
    intro a; simp only [cut, Dart.symm_symm]; exact not_congr Iff.comm
  have s_rho : ∀ a, s (rho M a) ↔ s a.symm := by
    intro a; simp only [s, face_rho]
  have cutR : ∀ a, cut a → R.Adj a.fst a.snd := by
    intro a ha
    by_contra hn
    by_cases heq : (M.dart.symm a).1 = (M.dart.symm a.symm).1
    · exact ha (by simp only [s, heq])
    · have hadj : (M.cotree R).Adj (M.dart.symm a).1 (M.dart.symm a.symm).1 :=
        ⟨heq, a, hn, rfl, rfl⟩
      exact ha ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  -- existence of a cut dart
  have hcut : ∃ a, cut a := by
    by_contra hnc
    push Not at hnc
    have hnc' : ∀ a, s a ↔ s a.symm := fun a => by
      have := hnc a; simp only [cut, not_not] at this; exact this
    have hit : ∀ k a, s ((rho M)^[k] a) ↔ s a := by
      intro k
      induction k with
      | zero => intro a; rfl
      | succ k ih =>
        intro a
        rw [Function.iterate_succ_apply', s_rho, ← hnc', ih]
    have hvert : ∀ a b : H.Dart, a.fst = b.fst → (s a ↔ s b) := by
      intro a b hab
      obtain ⟨k, hk⟩ := M.rotation_transitive a b hab
      have := hit k a
      change s ((rho M)^[k] a) ↔ s a at this
      rw [← this]
      change s ((rho M)^[k] a) ↔ s b
      rw [show (rho M)^[k] a = b from hk]
    have hwalk : ∀ u w (p : H.Walk u w) (a b : H.Dart), a.fst = u → b.fst = w → (s a ↔ s b) := by
      intro u w p
      induction p with
      | nil => intro a b ha hb; exact hvert a b (ha.trans hb.symm)
      | @cons u x w h p ih =>
        intro a b ha hb
        let e : H.Dart := ⟨(u, x), h⟩
        exact (hvert a e ha).trans ((hnc' e).trans (ih e.symm b rfl hb))
    have := hwalk _ _ (M.connected.preconnected (M.dart (f0, 0)).fst (M.dart (g, 0)).fst).some
      (M.dart (f0, 0)) (M.dart (g, 0)) rfl rfl
    simp only [s, Equiv.symm_apply_apply] at this
    exact hne (this.mp (Reachable.refl _))
  obtain ⟨a0, ha0⟩ := hcut
  let B : SimpleGraph V := SimpleGraph.fromRel fun u w => ∃ a : H.Dart, cut a ∧ a.fst = u ∧ a.snd = w
  have hBR : B ≤ R := by
    intro u w ⟨_, h⟩
    rcases h with ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
    · exact cutR a ha
    · exact (cutR a ha).symm
  have hBadj : ∀ a, cut a → B.Adj a.fst a.snd := fun a ha =>
    ⟨a.adj.ne, Or.inl ⟨a, ha, rfl, rfl⟩⟩
  obtain ⟨v, w, hvw, huniq⟩ := leaf B (hRac.anti hBR) (hBadj a0 ha0)
  -- a cut dart at v
  obtain ⟨c, hc, hcv⟩ : ∃ c, cut c ∧ c.fst = v := by
    rcases hvw with ⟨_, ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩⟩
    · exact ⟨a, ha, rfl⟩
    · exact ⟨a.symm, (cut_symm a).mpr ha, rfl⟩
  have huc : ∀ a, cut a → a.fst = v → a = c := by
    intro a ha hav
    have h1 := huniq _ (hav ▸ hBadj a ha)
    have h2 := huniq _ (hcv ▸ hBadj c hc)
    ext
    · rw [hav, hcv]
    · rw [h1, h2]
  obtain ⟨k, hk⟩ := M.rotation_transitive (rho M c) c (rho_fst M c)
  have hex : ∃ k, (rho M)^[k] (rho M c) = c := ⟨k, hk⟩
  classical
  have hmain : ∀ j ≤ Nat.find hex, s ((rho M)^[j] (rho M c)) ↔ s (rho M c) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hjc : (rho M)^[j] (rho M c) ≠ c := Nat.find_min hex (by omega)
      have hncut : ¬ cut ((rho M)^[j] (rho M c)) := fun h =>
        hjc (huc _ h (by rw [iterate_fst, rho_fst, hcv]))
      simp only [cut, not_not] at hncut
      rw [Function.iterate_succ_apply', s_rho, ← hncut, ih (by omega)]
  have := hmain _ le_rfl
  rw [Nat.find_spec hex, s_rho] at this
  exact hc this

lemma card_dart_eq {W : Type} [Fintype W] (G : SimpleGraph W) :
    Nat.card G.Dart = 2 * Nat.card G.edgeSet := by
  classical
  rw [Nat.card_eq_fintype_card, dart_card_eq_twice_card_edges, Nat.card_eq_fintype_card,
    edgeFinset_card]

lemma card_le (M : TriangularMap H F) (heuler : 2 * Fintype.card V = Fintype.card F + 4)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree) :
    Nat.card (M.cotree R).edgeSet + 1 ≤ Fintype.card F := by
  classical
  have hRc := (isTree_iff_connected_and_card.mp hR).2
  have h1 : Nat.card (M.cotree R).Dart ≤ Nat.card {d : H.Dart // ¬ R.Adj d.fst d.snd} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨x.adj.2.choose, x.adj.2.choose_spec.1⟩) ?_
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    have hx := x.adj.2.choose_spec
    have hy := y.adj.2.choose_spec
    rw [hxy] at hx
    ext
    · rw [← hx.2.1, hy.2.1]
    · rw [← hx.2.2, hy.2.2]
  have h2 : Nat.card R.Dart ≤ Nat.card {d : H.Dart // R.Adj d.fst d.snd} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨x.toProd, hRH x.adj⟩, x.adj⟩) ?_
    intro x y hxy
    simp only [Subtype.mk.injEq, Dart.mk.injEq] at hxy
    exact Dart.ext _ _ hxy
  have h3 : Nat.card {d : H.Dart // ¬ R.Adj d.fst d.snd} =
      Nat.card H.Dart - Nat.card {d : H.Dart // R.Adj d.fst d.snd} := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have h4 : Nat.card {d : H.Dart // R.Adj d.fst d.snd} ≤ Nat.card H.Dart := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have h5 : Nat.card H.Dart = 3 * Fintype.card F := by
    rw [← Nat.card_congr M.dart, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, mul_comm]
  rw [card_dart_eq] at h1 h2
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  omega

end A3S56CT

theorem solution
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (heuler : 2 * Fintype.card V = Fintype.card F + 4)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree) :
    (M.cotree R).IsTree := by
  have hV : Nonempty V := M.connected.nonempty
  have hF : Nonempty F := by
    obtain ⟨v⟩ := hV
    obtain ⟨f, _, _⟩ := M.vertex_covered v
    exact ⟨f⟩
  have hc := A3S56CT.conn M R hRH hR.isAcyclic
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hc, ?_⟩
  have h1 := hc.card_vert_le_card_edgeSet_add_one
  have h2 := A3S56CT.card_le M heuler R hRH hR
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hF' : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  omega

