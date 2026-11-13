-- Prove2me | solution 1 for RepellingPairs.step_1_maximal_switching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:00:52.81345+00:00
-- url     : https://prove2.me/submissions/3506e528-dd39-4054-9f4d-5c44967f8b22

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_PathLength
import Definitions.Def_RepellingPairs_Repel
import Definitions.Def_RepellingPairs_TerminalPath
import Definitions.Def_RepellingPairs_RealFlow
import Definitions.Def_RepellingPairs_Config
import Definitions.Def_RepellingPairs_CyclicallyOrdered
import Definitions.Def_RepellingPairs_IntegralFlow
import Theorems.Thm_RepellingPairs_claim_8_path_switching
universe u v

section
set_option autoImplicit false

namespace RepellingPairs.Dev.Step1


open RepellingPairs


section walks

variable {V : Type u} {E : Type v} {G : Multigraph V E}

theorem edges_append {u w x : V} (p : G.Walk u w) (q : G.Walk w x) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil v => simp [Multigraph.Walk.append, Multigraph.Walk.edges]
  | cons e h p ih => simp [Multigraph.Walk.append, Multigraph.Walk.edges, ih]

theorem edges_reverse {u w : V} (p : G.Walk u w) : p.reverse.edges = p.edges.reverse := by
  induction p with
  | nil v => simp [Multigraph.Walk.reverse, Multigraph.Walk.edges]
  | cons e h p ih => simp [Multigraph.Walk.reverse, Multigraph.Walk.edges, edges_append, ih]

end walks

/-! ### Crossing -/

theorem co_rot1 {k : ℕ} (a b c d : Fin k) : CyclicallyOrdered a b c d ↔ CyclicallyOrdered b c d a := by
  unfold CyclicallyOrdered; tauto

theorem co_rot2 {k : ℕ} (a b c d : Fin k) : CyclicallyOrdered a b c d ↔ CyclicallyOrdered c d a b := by
  exact (co_rot1 a b c d).trans (co_rot1 b c d a)

theorem cc_swap1 {k : ℕ} (x y z w : Fin k) :
    Config.ChordsCross x y z w ↔ Config.ChordsCross y x z w := by
  unfold Config.ChordsCross
  have e1 := co_rot2 y z x w
  have e2 := co_rot2 y w x z
  tauto

theorem cc_symm {k : ℕ} (x y z w : Fin k) :
    Config.ChordsCross x y z w ↔ Config.ChordsCross z w x y := by
  unfold Config.ChordsCross
  have e1 := co_rot1 x w y z
  have e2 := co_rot2 z x w y
  have e3 := co_rot1 x z y w
  tauto

theorem cc_self {k : ℕ} (x y : Fin k) : ¬ Config.ChordsCross x y x y := by
  unfold Config.ChordsCross CyclicallyOrdered; simp only [Fin.lt_def]; omega

/-- inside/outside description of crossing for `p < q`. -/
def X {k : ℕ} (p q x y : Fin k) : Prop :=
  (p < x ∧ x < q ∧ (y < p ∨ q < y)) ∨ (p < y ∧ y < q ∧ (x < p ∨ q < x))

theorem cc_iff_X {k : ℕ} (p q x y : Fin k) (h : p < q) :
    Config.ChordsCross p q x y ↔ X p q x y := by
  unfold Config.ChordsCross CyclicallyOrdered X; simp only [Fin.lt_def] at *; omega

theorem key1 {k : ℕ} (s s' t' t x y : Fin k) (h1 : s < s') (h2 : s' < t') (h3 : t' < t) :
    (X s s' x y ∨ X t' t x y → X s t' x y ∨ X s' t x y) ∧
      (X s s' x y → X t' t x y → X s t' x y ∧ X s' t x y) := by
  simp only [X, Fin.lt_def] at *; constructor <;> omega

theorem key2 {k : ℕ} (s s' t' t x y : Fin k) (h1 : s < s') (h2 : s' < t') (h3 : t' < t) :
    (X s' t' x y ∨ X s t x y → X s t' x y ∨ X s' t x y) ∧
      (X s' t' x y → X s t x y → X s t' x y ∧ X s' t x y) := by
  simp only [X, Fin.lt_def] at *; constructor <;> omega

open Classical in
/-- `0` if the chords of the two units cross, `1` otherwise. -/
noncomputable def ncu {k : ℕ} (a v : Fin k × Fin k) : ℕ :=
  if Config.ChordsCross a.1 a.2 v.1 v.2 then 0 else 1

theorem ncu_symm {k : ℕ} (a v : Fin k × Fin k) : ncu a v = ncu v a := by
  unfold ncu
  by_cases h : Config.ChordsCross a.1 a.2 v.1 v.2
  · have := (cc_symm _ _ _ _).1 h; simp [h, this]
  · have : ¬ Config.ChordsCross v.1 v.2 a.1 a.2 := fun h' => h ((cc_symm _ _ _ _).2 h')
    simp [h, this]

theorem ncu_self {k : ℕ} (a : Fin k × Fin k) : ncu a a = 1 := by
  unfold ncu; simp [cc_self]

theorem ncu_sw {k : ℕ} (x y : Fin k) (u : Fin k × Fin k) : ncu (y, x) u = ncu (x, y) u := by
  unfold ncu
  by_cases h : Config.ChordsCross x y u.1 u.2
  · have := (cc_swap1 _ _ _ _).1 h; simp [h, this]
  · have : ¬ Config.ChordsCross y x u.1 u.2 := fun h' => h ((cc_swap1 _ _ _ _).2 h')
    simp [h, this]

theorem ncu_of_sym2 {k : ℕ} (a v : Fin k × Fin k) (x y : Fin k) (h : s(a.1, a.2) = s(x, y)) :
    ncu a v = ncu (x, y) v := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [show a = (x, y) from Prod.ext h1 h2]
  · rw [show a = (y, x) from Prod.ext h1 h2, ncu_sw]

open Classical in
theorem ncu_X {k : ℕ} (p q : Fin k) (h : p < q) (u : Fin k × Fin k) :
    ncu (p, q) u = if X p q u.1 u.2 then 0 else 1 := by
  unfold ncu
  by_cases hx : X p q u.1 u.2
  · rw [if_pos ((cc_iff_X _ _ _ _ h).2 hx), if_pos hx]
  · rw [if_neg (fun hc => hx ((cc_iff_X _ _ _ _ h).1 hc)), if_neg hx]

open Classical in
theorem nc_abs (P Q R S : Prop) (h1 : R ∨ S → P ∨ Q) (h2 : R → S → P ∧ Q) :
    (if P then 0 else 1) + (if Q then 0 else 1) ≤ (if R then 0 else 1) + (if S then 0 else 1) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;> simp [hP, hQ, hR, hS] <;>
    first | (have := h1 (Or.inl hR); tauto) | (have := h1 (Or.inr hS); tauto) | (have := h2 hR hS; tauto)

theorem key_sorted {k : ℕ} (a b c d : Fin k) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (u : Fin k × Fin k) :
    ncu (a, c) u + ncu (d, b) u ≤ ncu (a, b) u + ncu (d, c) u ∧
    ncu (a, c) u + ncu (d, b) u ≤ ncu (b, c) u + ncu (d, a) u := by
  have hac : a < c := hab.trans hbc
  have hbd : b < d := hbc.trans hcd
  have had : a < d := hac.trans hcd
  constructor
  · rw [ncu_sw b d, ncu_sw c d, ncu_X _ _ hac, ncu_X _ _ hbd, ncu_X _ _ hab, ncu_X _ _ hcd]
    obtain ⟨h1, h2⟩ := key1 a b c d u.1 u.2 hab hbc hcd
    exact nc_abs _ _ _ _ h1 h2
  · rw [ncu_sw b d, ncu_sw a d, ncu_X _ _ hac, ncu_X _ _ hbd, ncu_X _ _ hbc, ncu_X _ _ had]
    obtain ⟨h1, h2⟩ := key2 a b c d u.1 u.2 hab hbc hcd
    exact nc_abs _ _ _ _ h1 h2

theorem key_ineq {k : ℕ} {s s' t' t : Fin k} (hco : CyclicallyOrdered s s' t' t) (u : Fin k × Fin k) :
    ncu (s, t') u + ncu (t, s') u ≤ ncu (s, s') u + ncu (t, t') u := by
  rcases hco with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact (key_sorted s s' t' t h1 h2 h3 u).1
  · have := (key_sorted s' t' t s h1 h2 h3 u).2
    have e1 := ncu_sw t s' u
    have e2 := ncu_sw t' t u
    omega
  · have := (key_sorted t' t s s' h1 h2 h3 u).1
    have e1 := ncu_sw s t' u
    have e2 := ncu_sw s' s u
    have e3 := ncu_sw t' t u
    have e4 := ncu_sw s' t u
    omega
  · have := (key_sorted t s s' t' h1 h2 h3 u).2
    have e1 := ncu_sw t s' u
    have e2 := ncu_sw t' s u
    have e3 := ncu_sw t' t u
    omega

theorem new_pair {k : ℕ} {s s' t' t : Fin k} (hco : CyclicallyOrdered s s' t' t) :
    ncu (s, t') (t, s') = 0 ∧ ncu (s, s') (t, t') = 1 := by
  constructor
  · unfold ncu
    dsimp only
    rw [if_pos (show Config.ChordsCross s t' t s' from Or.inr hco)]
  · unfold ncu
    dsimp only
    rw [if_neg]
    intro h
    simp only [Config.ChordsCross, CyclicallyOrdered, Fin.lt_def] at h hco
    rcases hco with h0 | h0 | h0 | h0 <;> omega

/-! ### Potential -/

noncomputable def pot {k : ℕ} (F : DesignatedFlow k) : ℕ :=
  (F.map fun a => (F.map fun v => ncu a v).sum).sum

theorem pot_cons {k : ℕ} (a : Fin k × Fin k) (F : DesignatedFlow k) :
    pot (a ::ₘ F) = ncu a a + 2 * (F.map fun v => ncu a v).sum + pot F := by
  unfold pot
  simp only [Multiset.map_cons, Multiset.sum_cons]
  rw [Multiset.sum_map_add]
  have : (F.map fun u => ncu u a).sum = (F.map fun v => ncu a v).sum := by
    congr 1; exact Multiset.map_congr rfl fun u _ => ncu_symm _ _
  rw [this]; ring

/-! ### Units equivalences -/

section flow

variable {V : Type u} {E : Type v} {k : ℕ} {G : OSInstance V E k}

def cnt [DecidableEq E] (P : PathStructure G) (a : Fin k × Fin k) (e : E) : ℕ :=
  (P.path a.1 a.2).1.edges.count e

theorem cnt_swap [DecidableEq E] (P : PathStructure G) (x y : Fin k) (e : E) :
    cnt P (y, x) e = cnt P (x, y) e := by
  show (P.path y x).1.edges.count e = (P.path x y).1.edges.count e
  rw [P.path_symm x y, edges_reverse, List.count_reverse]

theorem cnt_of_sym2 [DecidableEq E] (P : PathStructure G) (a : Fin k × Fin k) (x y : Fin k)
    (h : s(a.1, a.2) = s(x, y)) (e : E) : cnt P a e = cnt P (x, y) e := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [show a = (x, y) from Prod.ext h1 h2]
  · rw [show a = (y, x) from Prod.ext h1 h2, cnt_swap]

theorem D_of_sym2 {D : Fin k → Fin k → ℝ} (hD : IsMetric D) (a : Fin k × Fin k) (x y : Fin k)
    (h : s(a.1, a.2) = s(x, y)) : D a.1 a.2 = D x y := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hD.symm]

theorem load_cons [DecidableEq E] (P : PathStructure G) (a : Fin k × Fin k) (F : DesignatedFlow k)
    (e : E) : DesignatedFlow.load P (a ::ₘ F) e = cnt P a e + DesignatedFlow.load P F e := by
  simp [DesignatedFlow.load, cnt]

theorem cost_cons {D : Fin k → Fin k → ℝ} (a : Fin k × Fin k) (F : DesignatedFlow k) :
    DesignatedFlow.cost D (a ::ₘ F) = D a.1 a.2 + DesignatedFlow.cost D F := by
  simp [DesignatedFlow.cost]

theorem deg_cons (c : Sym2 (Fin k)) (C : Config k) (t : Fin k) :
    Config.deg (c ::ₘ C) t = Config.chordDeg t c + Config.deg C t := by
  simp [Config.deg]

theorem chords_cons (a : Fin k × Fin k) (F : DesignatedFlow k) :
    DesignatedFlow.chords (a ::ₘ F) = s(a.1, a.2) ::ₘ DesignatedFlow.chords F := by
  simp [DesignatedFlow.chords]

theorem chordDeg_mk (t x y : Fin k) :
    Config.chordDeg t s(x, y) = (if x = t then 1 else 0) + (if y = t then 1 else 0) := by
  simp [Config.chordDeg]

/-- Edge identity from Claim 8. -/
theorem cnt_identity [Fintype V] [Fintype E] [DecidableEq E] (P : PathStructure G) {a b c d : Fin k}
    (horder : CyclicallyOrdered a b c d)
    (hint : ¬ (P.path a b).1.VertexDisjoint (P.path d c).1) (e : E) :
    cnt P (a, c) e + cnt P (d, b) e = cnt P (a, b) e + cnt P (d, c) e := by
  obtain ⟨x, y, R, Pa, Pb, Qd, Qc, h1, h2, -, h3, h4⟩ := claim_8_path_switching G P horder hint
  unfold cnt
  simp only [h1, h2, h3, h4, edges_append, List.count_append]
  omega

/-- One switching step. -/
theorem step [Fintype V] [Fintype E] [DecidableEq E] {D : Fin k → Fin k → ℝ} (hD : IsMetric D) (P : PathStructure G)
    (hgood : P.IsGood D) {s s' t' t : Fin k} (hco : CyclicallyOrdered s s' t' t)
    (hint : ¬ (P.path s s').1.VertexDisjoint (P.path t t').1)
    (a b : Fin k × Fin k) (rest : DesignatedFlow k)
    (ha : s(a.1, a.2) = s(s, s')) (hb : s(b.1, b.2) = s(t, t')) :
    (∀ e, DesignatedFlow.load P ((s, t') ::ₘ (t, s') ::ₘ rest) e =
        DesignatedFlow.load P (a ::ₘ b ::ₘ rest) e) ∧
    DesignatedFlow.cost D ((s, t') ::ₘ (t, s') ::ₘ rest) ≤ DesignatedFlow.cost D (a ::ₘ b ::ₘ rest) ∧
    (∀ x, Config.deg (DesignatedFlow.chords ((s, t') ::ₘ (t, s') ::ₘ rest)) x =
        Config.deg (DesignatedFlow.chords (a ::ₘ b ::ₘ rest)) x) ∧
    pot ((s, t') ::ₘ (t, s') ::ₘ rest) < pot (a ::ₘ b ::ₘ rest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e
    rw [load_cons, load_cons, load_cons, load_cons, cnt_of_sym2 P a s s' ha,
      cnt_of_sym2 P b t t' hb]
    have := cnt_identity P hco hint e
    omega
  · rw [cost_cons, cost_cons, cost_cons, cost_cons, D_of_sym2 hD a s s' ha,
      D_of_sym2 hD b t t' hb]
    have h1 : ¬ Repel D s s' t t' := fun hr => hint (hgood s s' t t' hr)
    unfold Repel at h1
    have h2 := le_of_not_gt h1
    have h3 : D s t' + D t s' ≤ D s s' + D t t' := le_trans (le_max_right _ _) h2
    simp only
    linarith
  · intro x
    rw [chords_cons, chords_cons, chords_cons, chords_cons, deg_cons, deg_cons, deg_cons, deg_cons,
      ha, hb]
    simp only [chordDeg_mk]
    split_ifs <;> omega
  · rw [pot_cons, pot_cons, pot_cons, pot_cons]
    have hA : ∀ v, ncu a v = ncu (s, s') v := fun v => ncu_of_sym2 a v s s' ha
    have hB : ∀ v, ncu b v = ncu (t, t') v := fun v => ncu_of_sym2 b v t t' hb
    have hS : ((rest.map fun v => ncu (s, t') v).sum + (rest.map fun v => ncu (t, s') v).sum) ≤
        (rest.map fun v => ncu (s, s') v).sum + (rest.map fun v => ncu (t, t') v).sum := by
      rw [← Multiset.sum_map_add, ← Multiset.sum_map_add]
      exact Multiset.sum_map_le_sum_map _ _ fun v _ => key_ineq hco v
    obtain ⟨n1, n2⟩ := new_pair hco
    have hab : ncu a b = 1 := by rw [hA, ncu_symm, hB, ncu_symm]; exact n2
    simp only [Multiset.map_cons, Multiset.sum_cons, ncu_self]
    rw [hab, n1]
    simp only [hA, hB]
    omega

theorem co_ne {k : ℕ} {s s' t' t : Fin k} (hco : CyclicallyOrdered s s' t' t) :
    s ≠ s' ∧ s ≠ t' ∧ s ≠ t ∧ s' ≠ t' ∧ s' ≠ t ∧ t' ≠ t := by
  simp only [CyclicallyOrdered, Fin.lt_def] at hco
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := congrArg Fin.val h <;> omega

theorem main [Fintype V] [Fintype E] [DecidableEq E] {D : Fin k → Fin k → ℝ} (hD : IsMetric D)
    (P : PathStructure G) (hgood : P.IsGood D) (F' : PathFlow G) :
    ∀ n : ℕ, ∀ F : DesignatedFlow k, pot F = n →
      Property2 P F F' → Property3 D F F' → Property4 F F' →
      ∃ F₁ : DesignatedFlow k,
        Property2 P F₁ F' ∧ Property3 D F₁ F' ∧ Property4 F₁ F' ∧ Property5 P F₁ ∧
          (NoTrivialPair F → NoTrivialPair F₁) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hF h2 h3 h4
    by_cases h5 : Property5 P F
    · exact ⟨F, h2, h3, h4, h5, id⟩
    · unfold Property5 at h5
      push_neg at h5
      obtain ⟨s, s', t', t, hco, hm1, hm2, hnd⟩ := h5
      obtain ⟨a, haF, ha⟩ := Multiset.mem_map.1 hm1
      obtain ⟨b, hbF, hb⟩ := Multiset.mem_map.1 hm2
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := co_ne hco
      have hab : b ≠ a := by
        rintro rfl
        rw [ha] at hb
        rcases Sym2.eq_iff.1 hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact n3 h1
        · exact n2 h1
      obtain ⟨F2, rfl⟩ := Multiset.exists_cons_of_mem haF
      have hbF2 : b ∈ F2 := by
        rcases Multiset.mem_cons.1 hbF with h | h
        · exact absurd h hab
        · exact h
      obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hbF2
      obtain ⟨hl, hc, hd, hp⟩ := step hD P hgood hco hnd a b rest ha hb
      obtain ⟨F₂, g2, g3, g4, g5, g6⟩ := ih _ (hF ▸ hp) ((s, t') ::ₘ (t, s') ::ₘ rest) rfl
        (fun e => (h2 e).trans (hl e).symm.le)
        (lt_of_le_of_lt hc h3)
        (fun x => (hd x).trans (h4 x))
      refine ⟨F₂, g2, g3, g4, g5, fun hN => g6 ?_⟩
      intro p hp'
      rcases Multiset.mem_cons.1 hp' with rfl | hp'
      · exact n2
      · rcases Multiset.mem_cons.1 hp' with rfl | hp'
        · exact n5.symm
        · exact hN p (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hp'))

end flow

end RepellingPairs.Dev.Step1

namespace RepellingPairs


theorem chk_step_1_maximal_switching {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : OSInstance V E k) (D : Fin k → Fin k → ℝ) (hD : IsMetric D) (hK : IsKalmanson D)
    (P : PathStructure G) (hgood : P.IsGood D)
    (F : DesignatedFlow k) (F' : PathFlow G)
    (h2 : Property2 P F F') (h3 : Property3 D F F') (h4 : Property4 F F') :
    ∃ F₁ : DesignatedFlow k,
      Property2 P F₁ F' ∧ Property3 D F₁ F' ∧ Property4 F₁ F' ∧ Property5 P F₁ ∧
        (NoTrivialPair F → NoTrivialPair F₁) :=
  Dev.Step1.main hD P hgood F' _ F rfl h2 h3 h4

end RepellingPairs
end

theorem solution : type_of% @RepellingPairs.chk_step_1_maximal_switching := @RepellingPairs.chk_step_1_maximal_switching
