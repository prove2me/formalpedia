-- Prove2me | solution 1 for WilliamsonShmoys.triangular_map_one_edge_cut_faces_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:45:54.746991+00:00
-- url     : https://prove2.me/submissions/6907e8c1-7570-43de-a3cd-2f214a58943e

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

namespace A3S56DF2

open SimpleGraph WilliamsonShmoys

lemma pu {W : Type} {G : SimpleGraph W} (hG : G.IsAcyclic) {a b : W} (p q : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath) : p = q :=
  congrArg Subtype.val (hG.path_unique ⟨p, hp⟩ ⟨q, hq⟩)

lemma leafStart {W : Type} (G : SimpleGraph W) (hG : G.IsAcyclic) {u w : W}
    (p : G.Walk u w) (hp : p.IsPath)
    (hmax : ∀ u' w' (q : G.Walk u' w'), q.IsPath → q.length ≤ p.length) :
    ∀ w', G.Adj u w' → w' = p.snd := by
  intro w hadj
  apply hG.eq_snd_of_adj_start hp hadj
  by_contra hw
  have := hmax _ _ _ (hp.cons hw : (Walk.cons hadj.symm p).IsPath)
  simp at this

lemma leaf2 {W : Type} [Finite W] (G : SimpleGraph W) (hG : G.IsAcyclic) {a b : W}
    (hab : G.Adj a b) (x : W) : ∃ v w, v ≠ x ∧ G.Adj v w ∧ ∀ w', G.Adj v w' → w' = w := by
  have : Nonempty W := ⟨a⟩
  have : Finite G.edgeSet := inferInstance
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have h1 := hmax _ _ (Walk.cons hab Walk.nil) (by simp [hab.ne])
  have hnil : ¬p.Nil := by
    intro hn
    rw [Walk.nil_iff_length_eq.mp hn] at h1
    simp at h1
  have hnil' : ¬p.reverse.Nil := by
    intro hn
    rw [Walk.nil_iff_length_eq, Walk.length_reverse] at hn
    rw [hn] at h1
    simp at h1
  have hmax' : ∀ u' w' (q : G.Walk u' w'), q.IsPath → q.length ≤ p.reverse.length := by
    intro u' w' q hq; rw [Walk.length_reverse]; exact hmax _ _ q hq
  have huv : u ≠ v := by
    rintro rfl
    exact hnil (Walk.isPath_iff_nil.mp hp)
  by_cases hux : u = x
  · subst hux
    exact ⟨v, _, Ne.symm huv, p.reverse.adj_snd hnil', leafStart G hG p.reverse hp.reverse hmax'⟩
  · exact ⟨u, _, hux, p.adj_snd hnil, leafStart G hG p hp hmax⟩

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

theorem main (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree)
    (T : Set V) (hne : T.Nonempty) (hconn : (R.induce T).Connected)
    (hcut : ∀ a b c d : V, R.Adj a b → a ∈ T → b ∉ T →
      R.Adj c d → c ∈ T → d ∉ T →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    ((M.cotree R).induce
      {f : F | ∃ i : Fin 3, M.corner f i ∈ T}).Connected := by
  classical
  have hac := hR.isAcyclic
  set S : Set F := {f : F | ∃ i : Fin 3, M.corner f i ∈ T} with hS
  let D : V → Prop := fun x => x ∈ T
  obtain ⟨v0, hDv⟩ := hne
  obtain ⟨x0, hDx0, hx0⟩ : ∃ x0, D x0 ∧ ∀ x y, R.Adj x y → D x → ¬ D y → x = x0 := by
    by_cases hex : ∃ a b, R.Adj a b ∧ D a ∧ ¬ D b
    · obtain ⟨a, b, hab, ha, hb⟩ := hex
      refine ⟨a, ha, fun x y hxy hx hy => ?_⟩
      rcases hcut x y a b hxy hx hy hab ha hb with h | h
      · exact h.1
      · exact absurd (h.1 ▸ hx) hb
    · push Not at hex
      exact ⟨v0, hDv, fun x y hxy hx hy => absurd (hex x y hxy hx) hy⟩
  have parent : ∀ y y', R.Adj x0 y → R.Adj x0 y' → ¬ D y → ¬ D y' → y = y' := by
    intro y y' h h' hy hy'
    rcases hcut x0 y x0 y' h hDx0 hy h' hDx0 hy' with h1 | h1
    · exact h1.2
    · exact h1.2.trans h1.1
  let face : H.Dart → F := fun a => (M.dart.symm a).1
  have memS : ∀ a : H.Dart, D a.fst ∨ D a.snd → face a ∈ S := by
    intro a ha
    have h1 := M.dart_tail (M.dart.symm a).1 (M.dart.symm a).2
    have h2 := M.dart_head (M.dart.symm a).1 (M.dart.symm a).2
    simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h1 h2
    rcases ha with ha | ha
    · exact ⟨(M.dart.symm a).2, by rw [← h1]; exact ha⟩
    · exact ⟨(M.dart.symm a).2 + 1, by rw [← h2]; exact ha⟩
  have memS' : ∀ a : H.Dart, D a.fst ∨ D a.snd → face a.symm ∈ S := fun a ha =>
    memS a.symm ha.symm
  let G' : SimpleGraph F :=
    SimpleGraph.fromRel fun f g => (M.cotree R).Adj f g ∧ f ∈ S ∧ g ∈ S
  obtain ⟨f0, i0, hf0⟩ := M.vertex_covered v0
  let s : H.Dart → Prop := fun a => G'.Reachable f0 (face a)
  have s_rho : ∀ a, s (rho M a) ↔ s a.symm := by
    intro a; simp only [s, face, face_rho]
  have noR : ∀ a : H.Dart, D a.fst → ¬ R.Adj a.fst a.snd → (s a ↔ s a.symm) := by
    intro a ha hn
    by_cases heq : face a = face a.symm
    · show G'.Reachable f0 (face a) ↔ G'.Reachable f0 (face a.symm)
      rw [heq]
    · have hadj : G'.Adj (face a) (face a.symm) := by
        rw [fromRel_adj]
        exact ⟨heq, Or.inl ⟨⟨heq, a, hn, rfl, rfl⟩, memS a (Or.inl ha), memS' a (Or.inl ha)⟩⟩
      exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  let bad : H.Dart → Prop := fun a => ¬ (s a ↔ s a.symm)
  have rot : ∀ c, bad c → (∀ a, bad a → a.fst = c.fst → a = c) → False := by
    intro c hc huc
    obtain ⟨k, hk⟩ := M.rotation_transitive (rho M c) c (rho_fst M c)
    have hex : ∃ k, (rho M)^[k] (rho M c) = c := ⟨k, hk⟩
    have hmain : ∀ j ≤ Nat.find hex, s ((rho M)^[j] (rho M c)) ↔ s (rho M c) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hjc : (rho M)^[j] (rho M c) ≠ c := Nat.find_min hex (by omega)
        have hncut : ¬ bad ((rho M)^[j] (rho M c)) := fun h =>
          hjc (huc _ h (by rw [iterate_fst, rho_fst]))
        simp only [bad, not_not] at hncut
        rw [Function.iterate_succ_apply', s_rho, ← hncut, ih (by omega)]
    have := hmain _ le_rfl
    rw [Nat.find_spec hex, s_rho] at this
    exact hc this
  let cut : H.Dart → Prop := fun a => D a.fst ∧ D a.snd ∧ bad a
  have bad_symm : ∀ a, bad a.symm ↔ bad a := by
    intro a; simp only [bad, Dart.symm_symm]; exact not_congr Iff.comm
  have badR : ∀ a, D a.fst → bad a → R.Adj a.fst a.snd := fun a ha hb => by
    by_contra hn; exact hb (noR a ha hn)
  have hnocut : ¬ ∃ a, cut a := by
    rintro ⟨a0, ha0⟩
    let B : SimpleGraph V :=
      SimpleGraph.fromRel fun u w => ∃ a : H.Dart, cut a ∧ a.fst = u ∧ a.snd = w
    have hBR : B ≤ R := by
      intro u w ⟨_, h⟩
      rcases h with ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩
      · exact badR a ha.1 ha.2.2
      · exact (badR a ha.1 ha.2.2).symm
    have hBadj : ∀ a, cut a → B.Adj a.fst a.snd := fun a ha =>
      ⟨a.adj.ne, Or.inl ⟨a, ha, rfl, rfl⟩⟩
    obtain ⟨w, z, hwv, hwz, huniq⟩ := leaf2 B (hac.anti hBR) (hBadj a0 ha0) x0
    obtain ⟨c, hc, hcw⟩ : ∃ c, cut c ∧ c.fst = w := by
      rcases hwz with ⟨_, ⟨a, ha, rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩⟩
      · exact ⟨a, ha, rfl⟩
      · exact ⟨a.symm, ⟨ha.2.1, ha.1, (bad_symm a).mpr ha.2.2⟩, rfl⟩
    apply rot c hc.2.2
    intro a ha hac'
    have haw : a.fst = w := hac'.trans hcw
    have hDa : D a.fst := by rw [hac']; exact hc.1
    have hRa := badR a hDa ha
    have hDb : D a.snd := by
      by_contra hn
      exact hwv (haw.symm.trans (hx0 _ _ hRa hDa hn))
    have h1 := huniq a.snd (by rw [← haw]; exact hBadj a ⟨hDa, hDb, ha⟩)
    have h2 := huniq c.snd (by rw [← hcw]; exact hBadj c hc)
    ext
    · rw [haw, hcw]
    · rw [h1, h2]
  have nobad : ∀ a, D a.fst → ¬ bad a := by
    intro a ha hb
    have hRa := badR a ha hb
    have hDb : ¬ D a.snd := fun h => hnocut ⟨a, ha, h, hb⟩
    have hav := hx0 _ _ hRa ha hDb
    apply rot a hb
    intro b hb' hba
    have hDb' : D b.fst := by rw [hba]; exact ha
    have hRb := badR b hDb' hb'
    have hDbb : ¬ D b.snd := fun h => hnocut ⟨b, hDb', h, hb'⟩
    have hbv := hx0 _ _ hRb hDb' hDbb
    have hRb' : R.Adj x0 b.snd := by rw [← hbv]; exact hRb
    have hRa' : R.Adj x0 a.snd := by rw [← hav]; exact hRa
    have := parent _ _ hRb' hRa' hDbb hDb
    ext
    · rw [hba]
    · rw [this]
  have hit : ∀ k a, D a.fst → (s ((rho M)^[k] a) ↔ s a) := by
    intro k; induction k with
    | zero => intro a _; rfl
    | succ k ih =>
      intro a ha
      rw [Function.iterate_succ_apply', s_rho]
      have h1 := nobad ((rho M)^[k] a) (by rw [iterate_fst]; exact ha)
      simp only [bad, not_not] at h1
      rw [← h1, ih a ha]
  have hvert : ∀ a b : H.Dart, a.fst = b.fst → D a.fst → (s a ↔ s b) := by
    intro a b hab ha
    obtain ⟨k, hk⟩ := M.rotation_transitive a b hab
    have hk' : (rho M)^[k] a = b := hk
    rw [← hk', hit k a ha]
  have hwalk : ∀ x y (p : R.Walk x y), (∀ z ∈ p.support, D z) →
      ∀ a b : H.Dart, a.fst = x → b.fst = y → (s a ↔ s b) := by
    intro x y p
    induction p with
    | nil =>
      intro hD a b ha hb
      exact hvert a b (ha.trans hb.symm) (by rw [ha]; exact hD _ (Walk.start_mem_support _))
    | @cons x z y h p ih =>
      intro hD a b ha hb
      let e : H.Dart := ⟨(x, z), hRH h⟩
      have hDx : D x := hD x (by simp)
      have h1 := hvert a e ha (by rw [ha]; exact hDx)
      have h2 : s e ↔ s e.symm := by
        by_contra hb'; exact nobad e hDx hb'
      exact h1.trans (h2.trans (ih (fun w hw => hD w (by simp [hw])) e.symm b rfl hb))
  have hreach : ∀ f ∈ S, G'.Reachable f0 f := by
    rintro f ⟨i, hi⟩
    obtain ⟨w0⟩ := hconn.preconnected ⟨v0, hDv⟩ ⟨M.corner f i, hi⟩
    have hqD : ∀ z ∈ (w0.map (Embedding.induce T).toHom).support, D z := by
      intro z hz
      rw [Walk.support_map, List.mem_map] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact w.2
    have hw := hwalk v0 _ _ hqD (M.dart (f0, i0)) (M.dart (f, i)) (by rw [M.dart_tail, hf0])
      (M.dart_tail f i)
    have h0 : s (M.dart (f0, i0)) := by
      show G'.Reachable f0 (M.dart.symm (M.dart (f0, i0))).1
      simp only [Equiv.symm_apply_apply]
      exact Reachable.refl _
    have := hw.mp h0
    simpa [s, face] using this
  have toInd : ∀ x y (w : G'.Walk x y) (hx : x ∈ S),
      ∃ hy : y ∈ S, ((M.cotree R).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y w
    induction w with
    | nil => intro hx; exact ⟨hx, Reachable.refl _⟩
    | @cons x z y h w ih =>
      intro hx
      rw [fromRel_adj] at h
      obtain ⟨_, hh⟩ := h
      have hz : z ∈ S ∧ (M.cotree R).Adj x z := by
        rcases hh with ⟨h1, _, h3⟩ | ⟨h1, h2, _⟩
        · exact ⟨h3, h1⟩
        · exact ⟨h2, h1.symm⟩
      obtain ⟨hy, hr⟩ := ih hz.1
      refine ⟨hy, Reachable.trans ?_ hr⟩
      exact Adj.reachable (by simpa using hz.2)
  have hf0S : f0 ∈ S := ⟨i0, by rw [hf0]; exact hDv⟩
  rw [connected_iff]
  refine ⟨fun x y => ?_, ⟨⟨f0, hf0S⟩⟩⟩
  obtain ⟨w⟩ := (hreach x.1 x.2).symm.trans (hreach y.1 y.2)
  obtain ⟨_, hr⟩ := toInd _ _ w x.2
  exact hr

end A3S56DF2

theorem solution
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree)
    (S : Set V) (hne : S.Nonempty) (hconn : (R.induce S).Connected)
    (hcut : ∀ a b c d : V, R.Adj a b → a ∈ S → b ∉ S →
      R.Adj c d → c ∈ S → d ∉ S →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    ((M.cotree R).induce
      {f : F | ∃ i : Fin 3, M.corner f i ∈ S}).Connected :=
  A3S56DF2.main M R hRH hR S hne hconn hcut

