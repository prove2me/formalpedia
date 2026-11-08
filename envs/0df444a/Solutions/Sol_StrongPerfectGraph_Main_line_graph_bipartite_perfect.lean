-- Prove2me | solution 1 for StrongPerfectGraph.Main.line_graph_bipartite_perfect
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:34:38.613073+00:00
-- url     : https://prove2.me/submissions/bfb15670-c6c6-4bb4-9f32-8f8d9cadde2c

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

open StrongPerfectGraph.Main

namespace SPGTKonig

section Walks

variable {W : Type*} (K : SimpleGraph W)

/-- Along a walk in a graph whose edges join different sides, the side flips at each step. -/
lemma side_walk (side : W → Bool) (hK : ∀ x y, K.Adj x y → side x ≠ side y) :
    ∀ {x y : W} (p : K.Walk x y), (side x = side y ↔ Even p.length)
  | _, _, .nil => by simp
  | x, y, .cons (v := z) h q => by
    have ih := side_walk side hK q
    have hxz := hK _ _ h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    cases hx : side x <;> cases hz : side z <;> cases hy : side y <;> simp_all

/-- The swap of two colours. -/
def sw (α β : ℕ) (γ : ℕ) : ℕ := if γ = α then β else if γ = β then α else γ

lemma sw_sw {α β γ : ℕ} (h : γ = α ∨ γ = β) : sw α β (sw α β γ) = γ := by
  unfold sw; rcases h with rfl | rfl <;> split_ifs <;> simp_all

/-- Colours alternate along a path all of whose edges carry colour `α` or `β`, when
distinct edges at a vertex carry distinct colours. -/
lemma alt (col : W → W → ℕ) (α β : ℕ) (hαβ : α ≠ β)
    (hsym : ∀ x y, col x y = col y x)
    (hcol : ∀ x y, K.Adj x y → col x y = α ∨ col x y = β)
    (hprop : ∀ x y y', K.Adj x y → K.Adj x y' → y ≠ y' → col x y ≠ col x y') :
    ∀ {z y : W} (q : K.Walk z y) (w : W), K.Adj w z → w ∉ q.support → q.IsPath →
      ∃ y', K.Adj y' y ∧ col y' y = (if Even q.length then col w z else sw α β (col w z))
  | _, _, .nil, w, hw, _, _ => ⟨w, hw, by simp⟩
  | z, y, .cons (v := z2) h q, w, hw, hws, hq => by
    rw [SimpleGraph.Walk.cons_isPath_iff] at hq
    have hzq : z ∉ q.support := hq.2
    obtain ⟨y', hy', hcy⟩ := alt col α β hαβ hsym hcol hprop q z h hzq hq.1
    refine ⟨y', hy', ?_⟩
    rw [hcy]
    have hwz2 : w ≠ z2 := by
      intro hh; apply hws; subst hh
      simp
    have hne : col z w ≠ col z z2 := hprop z w z2 hw.symm h hwz2
    rw [← hsym w z] at hne
    have h1 := hcol w z hw
    have h2 := hcol z z2 h
    have hswap : col z z2 = sw α β (col w z) := by
      unfold sw
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1] at hne ⊢ <;> rw [h2] at hne ⊢ <;>
        simp_all
    rw [SimpleGraph.Walk.length_cons, hswap]
    by_cases he : Even q.length
    · have he' : ¬ Even (q.length + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
      rw [if_pos he, if_neg he']
    · have he' : Even (q.length + 1) := by rw [Nat.even_add_one]; exact he
      rw [if_neg he, if_pos he']
      exact sw_sw h1

lemma sw_sw' {α β : ℕ} (hαβ : α ≠ β) (γ : ℕ) : sw α β (sw α β γ) = γ := by
  unfold sw
  by_cases h1 : γ = α
  · subst h1; simp [Ne.symm hαβ]
  · by_cases h2 : γ = β
    · subst h2; simp
    · simp [h1, h2]

lemma sw_mem {α β γ : ℕ} (h : γ = α ∨ γ = β) : sw α β γ = α ∨ sw α β γ = β := by
  unfold sw; split_ifs <;> simp_all

lemma sw_lt {α β k γ : ℕ} (hα : α < k) (hβ : β < k) (hγ : γ < k) : sw α β γ < k := by
  unfold sw; split_ifs <;> assumption

end Walks


section Edge

variable {W : Type*} [DecidableEq W]

/-- A proper edge colouring of the edge set `E`. -/
def ProperOn (E : Finset (Sym2 W)) (c : Sym2 W → ℕ) : Prop :=
  ∀ d ∈ E, ∀ f ∈ E, d ≠ f → (∃ w, w ∈ d ∧ w ∈ f) → c d ≠ c f

/-- The Kempe-chain interchange. -/
lemma kempe (side : W → Bool) (E' : Finset (Sym2 W))
    (hside : ∀ d ∈ E', ∀ x y, d = s(x, y) → side x ≠ side y)
    (c : Sym2 W → ℕ) (hcp : ProperOn E' c) (u v : W) (huv : side u ≠ side v)
    (α β : ℕ) (hαβ : α ≠ β) (hu : ∀ f ∈ E', u ∈ f → c f ≠ α)
    (hv : ∀ f ∈ E', v ∈ f → c f ≠ β) :
    ∃ c1 : Sym2 W → ℕ, (∀ f, c1 f = c f ∨ c1 f = sw α β (c f)) ∧ ProperOn E' c1 ∧
      (∀ f ∈ E', u ∈ f → c1 f ≠ α) ∧ (∀ f ∈ E', v ∈ f → c1 f ≠ α) := by
  classical
  let K : SimpleGraph W :=
    { Adj := fun x y => x ≠ y ∧ s(x, y) ∈ E' ∧ (c s(x, y) = α ∨ c s(x, y) = β)
      symm := ⟨fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2.1,
        by rw [Sym2.eq_swap]; exact h.2.2⟩⟩
      loopless := ⟨fun x h => h.1 rfl⟩ }
  have hKadj : ∀ x y, K.Adj x y ↔ x ≠ y ∧ s(x, y) ∈ E' ∧ (c s(x, y) = α ∨ c s(x, y) = β) :=
    fun x y => Iff.rfl
  let swp : Sym2 W → Prop := fun f =>
    f ∈ E' ∧ (c f = α ∨ c f = β) ∧ ∃ w ∈ f, K.Reachable v w
  -- every endpoint of a swapped edge is in the Kempe component
  have hA : ∀ f, swp f → ∀ w ∈ f, K.Reachable v w := by
    intro f hf
    induction f using Sym2.ind with
    | _ x y =>
      obtain ⟨hfE, hfc, w0, hw0, hr⟩ := hf
      have hxy : x ≠ y := by
        intro h; subst h; exact hside _ hfE x x rfl rfl
      have hadj : K.Adj x y := ⟨hxy, hfE, hfc⟩
      intro w hw
      rw [Sym2.mem_iff] at hw hw0
      rcases hw0 with rfl | rfl <;> rcases hw with rfl | rfl
      · exact hr
      · exact hr.trans hadj.reachable
      · exact hr.trans hadj.symm.reachable
      · exact hr
  let c1 : Sym2 W → ℕ := fun f => if swp f then sw α β (c f) else c f
  -- `u` is not in the Kempe component of `v`
  have hnr : ¬ K.Reachable v u := by
    intro hr
    refine hr.elim_path (fun p => ?_)
    obtain ⟨p, hp⟩ := p
    cases p with
    | nil => exact huv rfl
    | cons h q =>
      rename_i z
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      have hsym : ∀ x y, c s(x, y) = c s(y, x) := fun x y => by rw [Sym2.eq_swap]
      have hcol : ∀ x y, K.Adj x y → c s(x, y) = α ∨ c s(x, y) = β := fun x y h => h.2.2
      have hprop : ∀ x y y', K.Adj x y → K.Adj x y' → y ≠ y' → c s(x, y) ≠ c s(x, y') := by
        intro x y y' h1 h2 hyy
        apply hcp _ h1.2.1 _ h2.2.1
        · intro hh; exact hyy (Sym2.congr_right.mp hh)
        · exact ⟨x, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
      obtain ⟨y', hy', hcy⟩ := alt K (fun x y => c s(x, y)) α β hαβ hsym hcol hprop q v h hp.2 hp.1
      have hvz : c s(v, z) = α := by
        rcases h.2.2 with h' | h'
        · exact h'
        · exact absurd h' (hv _ h.2.1 (Sym2.mem_mk_left _ _))
      have hyu : c s(y', u) = β := by
        rcases hy'.2.2 with h' | h'
        · exact absurd h' (hu _ hy'.2.1 (Sym2.mem_mk_right _ _))
        · exact h'

      rw [hvz, hyu] at hcy
      by_cases he : Even q.length
      · rw [if_pos he] at hcy; exact hαβ hcy.symm
      · have hsides := side_walk K side (fun x y h => hside _ h.2.1 x y rfl) (SimpleGraph.Walk.cons h q)
        rw [SimpleGraph.Walk.length_cons, Nat.even_add_one] at hsides
        exact huv (hsides.mpr he).symm
  refine ⟨c1, ?_, ?_, ?_, ?_⟩
  · intro f
    by_cases hf : swp f
    · right; simp only [c1, if_pos hf]
    · left; simp only [c1, if_neg hf]
  · intro d1 h1 d2 h2 hne hsh
    have hc := hcp d1 h1 d2 h2 hne hsh
    obtain ⟨w, hw1, hw2⟩ := hsh
    by_cases s1 : swp d1 <;> by_cases s2 : swp d2
    · simp only [c1, if_pos s1, if_pos s2]
      intro heq
      apply hc
      have := congrArg (sw α β) heq
      rwa [sw_sw' hαβ, sw_sw' hαβ] at this
    · simp only [c1, if_pos s1, if_neg s2]
      have hrw := hA d1 s1 w hw1
      have hn2 : ¬ (c d2 = α ∨ c d2 = β) := fun hh => s2 ⟨h2, hh, w, hw2, hrw⟩
      intro heq
      apply hn2
      rw [← heq]
      exact sw_mem s1.2.1
    · simp only [c1, if_neg s1, if_pos s2]
      have hrw := hA d2 s2 w hw2
      have hn1 : ¬ (c d1 = α ∨ c d1 = β) := fun hh => s1 ⟨h1, hh, w, hw1, hrw⟩
      intro heq
      apply hn1
      rw [heq]
      exact sw_mem s2.2.1
    · simp only [c1, if_neg s1, if_neg s2]
      exact hc
  · intro f hf huf
    by_cases s1 : swp f
    · exact absurd (hA f s1 u huf) hnr
    · simp only [c1, if_neg s1]
      exact hu f hf huf
  · intro f hf hvf
    by_cases s1 : swp f
    · simp only [c1, if_pos s1]
      intro heq
      rcases s1.2.1 with h' | h'
      · rw [h'] at heq; unfold sw at heq; simp at heq; exact hαβ heq.symm
      · exact hv f hf hvf h'
    · simp only [c1, if_neg s1]
      intro heq
      exact s1 ⟨hf, Or.inl heq, v, hvf, SimpleGraph.Reachable.refl v⟩


/-- Number of edges of `E` at `w`. -/
def deg (E : Finset (Sym2 W)) (w : W) : ℕ := (E.filter (fun d => w ∈ d)).card

lemma exists_missing (E : Finset (Sym2 W)) (c : Sym2 W → ℕ) (k : ℕ) (w : W)
    (hdeg : deg E w < k) : ∃ α, α < k ∧ ∀ f ∈ E, w ∈ f → c f ≠ α := by
  classical
  have hcard : ((E.filter (fun d => w ∈ d)).image c).card < (Finset.range k).card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt Finset.card_image_le hdeg
  obtain ⟨α, hα, hαn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨α, Finset.mem_range.mp hα, fun f hf hwf heq => hαn ?_⟩
  exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hwf⟩, heq⟩

/-- König's edge-colouring theorem: a bipartite graph whose degrees are at most `k` has a proper
edge colouring with `k` colours. -/
theorem konig_edge (side : W → Bool) (k : ℕ) (E : Finset (Sym2 W))
    (hside : ∀ d ∈ E, ∀ x y, d = s(x, y) → side x ≠ side y)
    (hdeg : ∀ w, deg E w ≤ k) :
    ∃ c : Sym2 W → ℕ, (∀ d ∈ E, c d < k) ∧ ProperOn E c := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp [ProperOn]⟩
  | insert d E' hd ih =>
    have hside' : ∀ d ∈ E', ∀ x y, d = s(x, y) → side x ≠ side y :=
      fun d' hd' => hside d' (Finset.mem_insert_of_mem hd')
    have hdeg' : ∀ w, deg E' w ≤ k := by
      intro w
      refine le_trans (Finset.card_le_card ?_) (hdeg w)
      intro f hf
      simp only [Finset.mem_filter] at hf ⊢
      exact ⟨Finset.mem_insert_of_mem hf.1, hf.2⟩
    obtain ⟨c, hcb, hcp⟩ := ih hside' hdeg'
    induction d using Sym2.ind with
    | _ u v =>
      have huv : side u ≠ side v := hside _ (Finset.mem_insert_self _ _) u v rfl
      have hdeg_lt : ∀ w, w ∈ s(u, v) → deg E' w < k := by
        intro w hw
        have h1 := hdeg w
        have : deg (insert s(u, v) E') w = deg E' w + 1 := by
          unfold deg
          rw [Finset.filter_insert, if_pos hw, Finset.card_insert_of_notMem]
          simp [hd]
        omega
      obtain ⟨α, hαk, hαu⟩ := exists_missing E' c k u (hdeg_lt u (Sym2.mem_mk_left _ _))
      obtain ⟨β, hβk, hβv⟩ := exists_missing E' c k v (hdeg_lt v (Sym2.mem_mk_right _ _))
      obtain ⟨c1, hc1b, hc1p, hc1u, hc1v⟩ : ∃ c1 : Sym2 W → ℕ, (∀ f ∈ E', c1 f < k) ∧
          ProperOn E' c1 ∧ (∀ f ∈ E', u ∈ f → c1 f ≠ α) ∧ (∀ f ∈ E', v ∈ f → c1 f ≠ α) := by
        by_cases hαβ : α = β
        · subst hαβ
          exact ⟨c, hcb, hcp, hαu, hβv⟩
        · obtain ⟨c1, h1, h2, h3, h4⟩ := kempe side E' hside' c hcp u v huv α β hαβ hαu hβv
          refine ⟨c1, ?_, h2, h3, h4⟩
          intro f hf
          rcases h1 f with h | h <;> rw [h]
          · exact hcb f hf
          · exact sw_lt hαk hβk (hcb f hf)
      refine ⟨fun f => if f = s(u, v) then α else c1 f, ?_, ?_⟩
      · intro f hf
        by_cases hfd : f = s(u, v)
        · simp only [if_pos hfd]; exact hαk
        · simp only [if_neg hfd]
          exact hc1b f ((Finset.mem_insert.mp hf).resolve_left hfd)
      · intro d1 h1 d2 h2 hne hsh
        obtain ⟨w, hw1, hw2⟩ := hsh
        by_cases e1 : d1 = s(u, v) <;> by_cases e2 : d2 = s(u, v)
        · exact absurd (e1.trans e2.symm) hne
        · simp only [if_pos e1, if_neg e2]
          have hd2 := (Finset.mem_insert.mp h2).resolve_left e2
          rw [e1, Sym2.mem_iff] at hw1
          rcases hw1 with rfl | rfl
          · exact (hc1u d2 hd2 hw2).symm
          · exact (hc1v d2 hd2 hw2).symm
        · simp only [if_neg e1, if_pos e2]
          have hd1 := (Finset.mem_insert.mp h1).resolve_left e1
          rw [e2, Sym2.mem_iff] at hw2
          rcases hw2 with rfl | rfl
          · exact hc1u d1 hd1 hw1
          · exact hc1v d1 hd1 hw1
        · simp only [if_neg e1, if_neg e2]
          exact hc1p d1 ((Finset.mem_insert.mp h1).resolve_left e1)
            d2 ((Finset.mem_insert.mp h2).resolve_left e2) hne ⟨w, hw1, hw2⟩

end Edge


lemma chi_le_of_color {U : Type*} (K : SimpleGraph U) {α : Type*} [Fintype α] (f : U → α)
    (hf : ∀ u v, K.Adj u v → f u ≠ f v) : K.chromaticNumber ≤ (Fintype.card α : ℕ∞) :=
  (SimpleGraph.Coloring.mk f (fun {u v} h => hf u v h)).colorable.chromaticNumber_le

lemma card_le_clique {U : Type*} [Finite U] (K : SimpleGraph U) {α : Type*} [Fintype α]
    (g : α → U) (hg : Function.Injective g) (hadj : ∀ a b, a ≠ b → K.Adj (g a) (g b)) :
    Fintype.card α ≤ K.cliqueNum := by
  classical
  have hcl : K.IsClique ((Finset.univ.map ⟨g, hg⟩ : Finset U) : Set U) := by
    intro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact hadj a b (fun h => hxy (by rw [h]))
  have := hcl.card_le_cliqueNum
  simpa using this

end SPGTKonig

open SPGTKonig in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (hH : H.IsBipartite)
    (e : G ≃g H.lineGraph) : IsPerfect G := by
  classical
  intro X
  apply le_antisymm _ (G.induce X).cliqueNum_le_chromaticNumber
  obtain ⟨C⟩ := hH
  let side : Fin n → Bool := fun w => decide (C w = 0)
  have hsideH : ∀ x y, H.Adj x y → side x ≠ side y := by
    intro x y hxy heq
    apply C.valid hxy
    have h1 := (C x).isLt
    have h2 := (C y).isLt
    simp only [side, decide_eq_decide] at heq
    apply Fin.ext
    by_cases hx0 : C x = 0
    · rw [hx0, heq.mp hx0]
    · have hy0 : C y ≠ 0 := fun h => hx0 (heq.mpr h)
      have : (C x).val ≠ 0 := fun h => hx0 (Fin.ext h)
      have : (C y).val ≠ 0 := fun h => hy0 (Fin.ext h)
      omega
  let E : Finset (Sym2 (Fin n)) :=
    (Finset.univ.filter (fun v : V => v ∈ X)).image (fun v => ((e v : H.edgeSet) : Sym2 (Fin n)))
  have hmemE : ∀ d, d ∈ E ↔ ∃ v ∈ X, ((e v : H.edgeSet) : Sym2 (Fin n)) = d := by
    intro d; simp [E]
  have hEedge : ∀ d ∈ E, d ∈ H.edgeSet := by
    intro d hd
    obtain ⟨v, -, rfl⟩ := (hmemE d).mp hd
    exact (e v).2
  have hside : ∀ d ∈ E, ∀ x y, d = s(x, y) → side x ≠ side y := by
    intro d hd x y hxy
    have := hEedge d hd
    rw [hxy, SimpleGraph.mem_edgeSet] at this
    exact hsideH x y this
  let k : ℕ := Finset.univ.sup (deg E)
  have hdeg : ∀ w, deg E w ≤ k := fun w => Finset.le_sup (Finset.mem_univ w)
  obtain ⟨c, hcb, hcp⟩ := konig_edge side k E hside hdeg
  have hvE : ∀ v ∈ X, ((e v : H.edgeSet) : Sym2 (Fin n)) ∈ E :=
    fun v hv => (hmemE _).mpr ⟨v, hv, rfl⟩
  have h1 := chi_le_of_color (G.induce X) (α := Fin k)
    (fun u => ⟨c (e u.1 : H.edgeSet), hcb _ (hvE u.1 u.2)⟩) (by
      intro u v huv heq
      have hG : G.Adj u.1 v.1 := by simpa using huv
      have hL : H.lineGraph.Adj (e u.1) (e v.1) := e.map_adj_iff.mpr hG
      rw [SimpleGraph.lineGraph_adj_iff_exists] at hL
      obtain ⟨hne, w, hw1, hw2⟩ := hL
      have hne' : ((e u.1 : H.edgeSet) : Sym2 (Fin n)) ≠ (e v.1 : H.edgeSet) :=
        fun h => hne (Subtype.ext h)
      apply hcp _ (hvE u.1 u.2) _ (hvE v.1 v.2) hne' ⟨w, hw1, hw2⟩
      exact congrArg Fin.val heq)
  rw [Fintype.card_fin] at h1
  refine h1.trans ?_
  norm_cast
  by_cases hk : k = 0
  · rw [hk]; exact Nat.zero_le _
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hk
    simp only [k, hemp, Finset.sup_empty]
    rfl
  obtain ⟨w0, -, hw0⟩ := Finset.exists_mem_eq_sup _ hne (deg E)
  let D : Finset (Sym2 (Fin n)) := E.filter (fun d => w0 ∈ d)
  have hDcard : D.card = k := hw0.symm
  have hDE : ∀ d ∈ D, d ∈ E := fun d hd => (Finset.mem_filter.mp hd).1
  have hDw : ∀ d ∈ D, w0 ∈ d := fun d hd => (Finset.mem_filter.mp hd).2
  let g : {d // d ∈ D} → X := fun d =>
    ⟨e.symm ⟨d.1, hEedge _ (hDE _ d.2)⟩, by
      obtain ⟨v, hv, hvd⟩ := (hmemE _).mp (hDE _ d.2)
      have : e.symm ⟨d.1, hEedge _ (hDE _ d.2)⟩ = v := by
        apply e.injective
        rw [RelIso.apply_symm_apply]
        exact Subtype.ext hvd.symm
      rw [this]; exact hv⟩
  have h2 := card_le_clique (G.induce X) g (by
      intro a b hab
      have := congrArg (fun x : X => e x.1) hab
      simp only [g, RelIso.apply_symm_apply] at this
      exact Subtype.ext (Subtype.mk.inj this)) (by
      intro a b hab
      show G.Adj (e.symm _) (e.symm _)
      rw [e.symm.map_adj_iff, SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨fun h => hab (Subtype.ext (Subtype.mk.inj h)), w0, hDw _ a.2,
        hDw _ b.2⟩)
  rw [Fintype.card_coe, hDcard] at h2
  exact h2
