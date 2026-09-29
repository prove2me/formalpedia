-- Prove2me | solution 1 for OrdinaryPolygonalDrawingNonempty
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:28:52.436731+00:00
-- url     : https://prove2.me/submissions/03b499b7-cb6b-4f31-85e8-25051ec74acc

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

/-! ### Points on the parabola -/

def aux_OPD_P (t : ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[t, t ^ 2]

@[simp] lemma aux_OPD_P0 (t : ℝ) : aux_OPD_P t 0 = t := rfl
@[simp] lemma aux_OPD_P1 (t : ℝ) : aux_OPD_P t 1 = t ^ 2 := rfl

lemma aux_OPD_P_inj {a b : ℝ} (h : aux_OPD_P a = aux_OPD_P b) : a = b := by
  have := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  simpa using this

lemma aux_OPD_line {a b : ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ segment ℝ (aux_OPD_P a) (aux_OPD_P b)) : p 1 = (a + b) * p 0 - a * b := by
  obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hp
  simp only [PiLp.add_apply, PiLp.smul_apply, aux_OPD_P0, aux_OPD_P1, smul_eq_mul]
  have : β = 1 - α := by linarith
  subst this
  ring

lemma aux_OPD_pair {a b c d : ℝ} (hs : a + b = c + d) (hp : a * b = c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h : (a - c) * (a - d) = 0 := by linear_combination a * hs - hp
  rcases mul_eq_zero.1 h with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

lemma aux_OPD_same {a b c d : ℝ} {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (hp1 : p 1 = (a + b) * p 0 - a * b) (hq1 : q 1 = (a + b) * q 0 - a * b)
    (hp2 : p 1 = (c + d) * p 0 - c * d) (hq2 : q 1 = (c + d) * q 0 - c * d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h0 : p 0 - q 0 ≠ 0 := by
    intro h
    apply hpq
    ext i
    fin_cases i
    · show p 0 = q 0
      linarith
    · show p 1 = q 1
      rw [hp1, hq1]
      have : p 0 = q 0 := by linarith
      rw [this]
  have hs : a + b = c + d := by
    have : (a + b - (c + d)) * (p 0 - q 0) = 0 := by
      linear_combination hp2 - hq2 - hp1 + hq1
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h h0
  have hπ : a * b = c * d := by linear_combination hp1 - hp2 + p 0 * hs
  exact aux_OPD_pair hs hπ

/-! ### Genericity -/

def aux_OPD_conc (a b c d e f : ℝ) : Prop :=
  ∃ X Y : ℝ, Y = (a + b) * X - a * b ∧ Y = (c + d) * X - c * d ∧ Y = (e + f) * X - e * f

def aux_OPD_X (a b c d : ℝ) : ℝ := (a * b - c * d) / (a + b - c - d)

def aux_OPD_bad (a b c d f : ℝ) : ℝ :=
  ((a + b) * aux_OPD_X a b c d - a * b - f * aux_OPD_X a b c d) / (aux_OPD_X a b c d - f)

lemma aux_OPD_bad_spec {a b c d e f : ℝ} (hac : a ≠ c) (had : a ≠ d) (hfa : f ≠ a)
    (hfb : f ≠ b) (h : aux_OPD_conc a b c d e f) : e = aux_OPD_bad a b c d f := by
  obtain ⟨X, Y, h1, h2, h3⟩ := h
  have hden : a + b - c - d ≠ 0 := by
    intro h0
    have hs : a + b = c + d := by linarith
    have hπ : a * b = c * d := by linear_combination h1 - h2 + X * h0
    rcases aux_OPD_pair hs hπ with ⟨h, _⟩ | ⟨h, _⟩
    · exact hac h
    · exact had h
  have hX : X = aux_OPD_X a b c d := by
    unfold aux_OPD_X
    rw [eq_div_iff hden]
    linear_combination h2 - h1
  have hXf : X - f ≠ 0 := by
    intro h0
    have : (f - a) * (f - b) = 0 := by linear_combination h1 - h3 - (e + f - a - b) * h0
    rcases mul_eq_zero.1 this with h | h
    · exact hfa (by linarith)
    · exact hfb (by linarith)
  unfold aux_OPD_bad
  rw [← hX, eq_div_iff hXf]
  linear_combination h1 - h3

def aux_OPD_gen (S : Finset ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ e ∈ S, ∀ f ∈ S,
    [a, b, c, d, e, f].Nodup → ¬ aux_OPD_conc a b c d e f

lemma aux_OPD_step {S : Finset ℝ} {x : ℝ}
    (hxB : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ f ∈ S, x ≠ aux_OPD_bad a b c d f)
    {a b c d f : ℝ} (ha : a ∈ insert x S) (hb : b ∈ insert x S) (hc : c ∈ insert x S)
    (hd : d ∈ insert x S) (hf : f ∈ insert x S)
    (hax : a ≠ x) (hbx : b ≠ x) (hcx : c ≠ x) (hdx : d ≠ x) (hfx : f ≠ x)
    (hac : a ≠ c) (had : a ≠ d) (hfa : f ≠ a) (hfb : f ≠ b)
    (h : aux_OPD_conc a b c d x f) : False := by
  have mem : ∀ y, y ∈ insert x S → y ≠ x → y ∈ S :=
    fun y hy hyx => (Finset.mem_insert.1 hy).resolve_left hyx
  exact hxB a (mem a ha hax) b (mem b hb hbx) c (mem c hc hcx) d (mem d hd hdx) f
    (mem f hf hfx) (aux_OPD_bad_spec hac had hfa hfb h)

lemma aux_OPD_gen_exists (n : ℕ) : ∃ S : Finset ℝ, S.card = n ∧ aux_OPD_gen S := by
  induction n with
  | zero => exact ⟨∅, rfl, by intro a ha; simp at ha⟩
  | succ n ih =>
    obtain ⟨S, hS, hg⟩ := ih
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (S ∪ ((S ×ˢ S ×ˢ S ×ˢ S ×ˢ S).image
      fun q => aux_OPD_bad q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
    have hxB : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, ∀ f ∈ S, x ≠ aux_OPD_bad a b c d f := by
      intro a ha b hb c hc d hd f hf h
      apply hx
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨(a, b, c, d, f), by simp [ha, hb, hc, hd, hf], h.symm⟩
    clear hx
    refine ⟨insert x S, by rw [Finset.card_insert_of_notMem hxS, hS], ?_⟩
    intro a ha b hb c hc d hd e he f hf hnd hconc
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
      not_false_eq_true, and_true, or_false] at hnd'
    obtain ⟨⟨hab, hac, had, hae, haf⟩, ⟨hbc, hbd, hbe, hbf⟩, ⟨hcd, hce, hcf⟩, ⟨hde, hdf⟩,
      hef⟩ := hnd'
    obtain ⟨X, Y, h1, h2, h3⟩ := hconc
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · exact aux_OPD_step hxB he hf hc hd hb (Ne.symm hae) (Ne.symm haf) (Ne.symm hac)
        (Ne.symm had) (Ne.symm hab) (Ne.symm hce) (Ne.symm hde) hbe hbf ⟨X, Y, h3, h2, h1⟩
    rcases Finset.mem_insert.1 hb with rfl | hb'
    · exact aux_OPD_step hxB he hf hc hd ha (Ne.symm hbe) (Ne.symm hbf) (Ne.symm hbc)
        (Ne.symm hbd) hab (Ne.symm hce) (Ne.symm hde) hae haf
        ⟨X, Y, h3, h2, by rw [h1]; ring⟩
    rcases Finset.mem_insert.1 hc with rfl | hc'
    · exact aux_OPD_step hxB ha hb he hf hd hac hbc (Ne.symm hce) (Ne.symm hcf)
        (Ne.symm hcd) hae haf (Ne.symm had) (Ne.symm hbd) ⟨X, Y, h1, h3, h2⟩
    rcases Finset.mem_insert.1 hd with rfl | hd'
    · exact aux_OPD_step hxB ha hb he hf hc had hbd (Ne.symm hde) (Ne.symm hdf)
        hcd hae haf (Ne.symm hac) (Ne.symm hbc) ⟨X, Y, h1, h3, by rw [h2]; ring⟩
    rcases Finset.mem_insert.1 he with rfl | he'
    · exact aux_OPD_step hxB ha hb hc hd hf hae hbe hce hde (Ne.symm hef)
        hac had (Ne.symm haf) (Ne.symm hbf) ⟨X, Y, h1, h2, h3⟩
    rcases Finset.mem_insert.1 hf with rfl | hf'
    · exact aux_OPD_step hxB ha hb hc hd he haf hbf hcf hdf hef
        hac had (Ne.symm hae) (Ne.symm hbe) ⟨X, Y, h1, h2, by rw [h3]; ring⟩
    exact hg a ha' b hb' c hc' d hd' e he' f hf' hnd ⟨X, Y, h1, h2, h3⟩

/-! ### Straight segments as polygonal arcs -/

def aux_OPD_segArc (x y : EuclideanSpace ℝ (Fin 2)) (hxy : x ≠ y) : PolygonalArc where
  vertices := [x, y]
  length_ge_two := by simp
  source := x
  target := y
  source_eq_head := rfl
  target_eq_last := rfl
  carrier := segment ℝ x y
  relativeInterior := segment ℝ x y \ {x, y}
  carrier_eq := by
    ext p
    constructor
    · intro h
      exact ⟨0, by simp, h⟩
    · rintro ⟨i, hi, h⟩
      have : i = 0 := by simp at hi; omega
      subst this
      exact h
  relativeInterior_eq := rfl
  simple_vertices := by simp [hxy]
  segment_intersections := by
    intro i j hi hj hij
    simp at hi hj
    omega
  vertices_avoid_nonincident_interiors := by
    intro i k hi hk h1 h2
    simp at hi hk
    omega

/-! ### The drawing -/

section Drawing

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]

lemma aux_OPD_exists_ends (e : G.edgeFinset) :
    ∃ p : V × V, e.1 = Sym2.mk p.1 p.2 ∧ G.Adj p.1 p.2 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h u v => exact ⟨(u, v), rfl, by simpa using he⟩

def aux_OPD_ends (e : G.edgeFinset) : V × V := Classical.choose (aux_OPD_exists_ends G e)

lemma aux_OPD_ends_spec (e : G.edgeFinset) :
    e.1 = Sym2.mk (aux_OPD_ends G e).1 (aux_OPD_ends G e).2 ∧ G.Adj (aux_OPD_ends G e).1 (aux_OPD_ends G e).2 :=
  Classical.choose_spec (aux_OPD_exists_ends G e)

variable (t : V → ℝ) (ht : Function.Injective t)

def aux_OPD_A (e : G.edgeFinset) : ℝ := t (aux_OPD_ends G e).1
def aux_OPD_B (e : G.edgeFinset) : ℝ := t (aux_OPD_ends G e).2

include ht in
lemma aux_OPD_AB_ne (e : G.edgeFinset) : aux_OPD_A G t e ≠ aux_OPD_B G t e := by
  intro h
  exact (aux_OPD_ends_spec G e).2.ne (ht h)

def aux_OPD_arc (e : G.edgeFinset) : PolygonalArc :=
  aux_OPD_segArc (aux_OPD_P (aux_OPD_A G t e)) (aux_OPD_P (aux_OPD_B G t e))
    (fun h => aux_OPD_AB_ne G t ht e (aux_OPD_P_inj h))

lemma aux_OPD_relint {e : G.edgeFinset} {p : EuclideanSpace ℝ (Fin 2)} :
    p ∈ (aux_OPD_arc G t ht e).relativeInterior ↔
      p ∈ segment ℝ (aux_OPD_P (aux_OPD_A G t e)) (aux_OPD_P (aux_OPD_B G t e)) ∧
        p ≠ aux_OPD_P (aux_OPD_A G t e) ∧ p ≠ aux_OPD_P (aux_OPD_B G t e) := by
  simp [aux_OPD_arc, aux_OPD_segArc, not_or]

include ht in
lemma aux_OPD_edge_eq {e₁ e₂ : G.edgeFinset}
    (h : (aux_OPD_A G t e₁ = aux_OPD_A G t e₂ ∧ aux_OPD_B G t e₁ = aux_OPD_B G t e₂) ∨
      (aux_OPD_A G t e₁ = aux_OPD_B G t e₂ ∧ aux_OPD_B G t e₁ = aux_OPD_A G t e₂)) :
    e₁ = e₂ := by
  apply Subtype.ext
  refine (aux_OPD_ends_spec G e₁).1.trans (Eq.trans ?_ (aux_OPD_ends_spec G e₂).1.symm)
  rw [Sym2.eq_iff]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨ht h1, ht h2⟩
  · exact Or.inr ⟨ht h1, ht h2⟩

include ht in
lemma aux_OPD_two_pts {e₁ e₂ : G.edgeFinset} {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (hp1 : p ∈ segment ℝ (aux_OPD_P (aux_OPD_A G t e₁)) (aux_OPD_P (aux_OPD_B G t e₁)))
    (hq1 : q ∈ segment ℝ (aux_OPD_P (aux_OPD_A G t e₁)) (aux_OPD_P (aux_OPD_B G t e₁)))
    (hp2 : p ∈ segment ℝ (aux_OPD_P (aux_OPD_A G t e₂)) (aux_OPD_P (aux_OPD_B G t e₂)))
    (hq2 : q ∈ segment ℝ (aux_OPD_P (aux_OPD_A G t e₂)) (aux_OPD_P (aux_OPD_B G t e₂))) :
    e₁ = e₂ :=
  aux_OPD_edge_eq G t ht (aux_OPD_same hpq (aux_OPD_line hp1) (aux_OPD_line hq1)
    (aux_OPD_line hp2) (aux_OPD_line hq2))

include ht in
lemma aux_OPD_disj {e₁ e₂ : G.edgeFinset} (hne : e₁ ≠ e₂) {p : EuclideanSpace ℝ (Fin 2)}
    (hp1 : p ∈ (aux_OPD_arc G t ht e₁).relativeInterior)
    (hp2 : p ∈ (aux_OPD_arc G t ht e₂).relativeInterior) :
    aux_OPD_A G t e₁ ≠ aux_OPD_A G t e₂ ∧ aux_OPD_A G t e₁ ≠ aux_OPD_B G t e₂ ∧
      aux_OPD_B G t e₁ ≠ aux_OPD_A G t e₂ ∧ aux_OPD_B G t e₁ ≠ aux_OPD_B G t e₂ := by
  rw [aux_OPD_relint] at hp1 hp2
  obtain ⟨hs1, hpa1, hpb1⟩ := hp1
  obtain ⟨hs2, hpa2, hpb2⟩ := hp2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> apply hne
  · refine aux_OPD_two_pts G t ht hpa1 hs1 (left_mem_segment _ _ _) hs2 ?_
    rw [heq]; exact left_mem_segment _ _ _
  · refine aux_OPD_two_pts G t ht hpa1 hs1 (left_mem_segment _ _ _) hs2 ?_
    rw [heq]; exact right_mem_segment _ _ _
  · refine aux_OPD_two_pts G t ht hpb1 hs1 (right_mem_segment _ _ _) hs2 ?_
    rw [heq]; exact left_mem_segment _ _ _
  · refine aux_OPD_two_pts G t ht hpb1 hs1 (right_mem_segment _ _ _) hs2 ?_
    rw [heq]; exact right_mem_segment _ _ _

include ht in
lemma aux_OPD_cross_finite :
    {p : EuclideanSpace ℝ (Fin 2) | ∃ e₁ e₂ : G.edgeFinset, e₁ ≠ e₂ ∧
      p ∈ (aux_OPD_arc G t ht e₁).relativeInterior ∧
        p ∈ (aux_OPD_arc G t ht e₂).relativeInterior}.Finite := by
  have hEq : {p : EuclideanSpace ℝ (Fin 2) | ∃ e₁ e₂ : G.edgeFinset, e₁ ≠ e₂ ∧
      p ∈ (aux_OPD_arc G t ht e₁).relativeInterior ∧
        p ∈ (aux_OPD_arc G t ht e₂).relativeInterior} =
      ⋃ e₁ : G.edgeFinset, ⋃ e₂ : G.edgeFinset,
        {p | e₁ ≠ e₂ ∧ p ∈ (aux_OPD_arc G t ht e₁).relativeInterior ∧
          p ∈ (aux_OPD_arc G t ht e₂).relativeInterior} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hEq]
  refine Set.finite_iUnion fun e₁ => Set.finite_iUnion fun e₂ => ?_
  apply Set.Subsingleton.finite
  rintro p ⟨hne, hp1, hp2⟩ q ⟨-, hq1, hq2⟩
  by_contra hpq
  apply hne
  rw [aux_OPD_relint] at hp1 hp2 hq1 hq2
  exact aux_OPD_two_pts G t ht hpq hp1.1 hq1.1 hp2.1 hq2.1

include ht in
lemma aux_OPD_main
    (hgen : ∀ a b c d e f : ℝ, a ∈ Set.range t → b ∈ Set.range t → c ∈ Set.range t →
      d ∈ Set.range t → e ∈ Set.range t → f ∈ Set.range t →
      [a, b, c, d, e, f].Nodup → ¬ aux_OPD_conc a b c d e f) :
    Nonempty (OrdinaryPolygonalDrawing G) := by
  refine ⟨{
    vertexPlacement := fun v => aux_OPD_P (t v)
    vertexPlacement_injective := fun u v h => ht (aux_OPD_P_inj h)
    edgeArc := aux_OPD_arc G t ht
    edgeArc_endpoints := fun e => ⟨(aux_OPD_ends G e).1, (aux_OPD_ends G e).2,
      (aux_OPD_ends_spec G e).2, (aux_OPD_ends_spec G e).1, Or.inl ⟨rfl, rfl⟩⟩
    crossingSet := (aux_OPD_cross_finite G t ht).toFinset
    no_vertex_in_edge_interior := ?_
    no_three_edge_interiors_meet := ?_
    transverse_intersections := ?_
    no_shared_nondegenerate_subarc := ?_
    crossingSet_spec := fun p => by simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    adjacentEdgeCrossingCount := _
    adjacentEdgeCrossingCount_eq := rfl }⟩
  · -- no vertex in edge interior
    intro v e hv
    rw [aux_OPD_relint] at hv
    obtain ⟨hs, ha, hb⟩ := hv
    have hl := aux_OPD_line hs
    simp only [aux_OPD_P0, aux_OPD_P1] at hl
    have : (t v - aux_OPD_A G t e) * (t v - aux_OPD_B G t e) = 0 := by
      linear_combination hl
    rcases mul_eq_zero.1 this with h | h
    · exact ha (by rw [show t v = aux_OPD_A G t e by linarith])
    · exact hb (by rw [show t v = aux_OPD_B G t e by linarith])
  · -- no three edge interiors meet
    intro e₁ e₂ e₃ p h12 h13 h23 hp1 hp2 hp3
    obtain ⟨d1, d2, d3, d4⟩ := aux_OPD_disj G t ht h12 hp1 hp2
    obtain ⟨d5, d6, d7, d8⟩ := aux_OPD_disj G t ht h13 hp1 hp3
    obtain ⟨d9, d10, d11, d12⟩ := aux_OPD_disj G t ht h23 hp2 hp3
    have n1 := aux_OPD_AB_ne G t ht e₁
    have n2 := aux_OPD_AB_ne G t ht e₂
    have n3 := aux_OPD_AB_ne G t ht e₃
    rw [aux_OPD_relint] at hp1 hp2 hp3
    refine hgen _ _ _ _ _ _ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ⟨_, rfl⟩ ?_
      ⟨p 0, p 1, aux_OPD_line hp1.1, aux_OPD_line hp2.1, aux_OPD_line hp3.1⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil,
      not_false_eq_true, and_true, or_false]
    exact ⟨⟨n1, d1, d2, d5, d6⟩, ⟨d3, d4, d7, d8⟩, ⟨n2, d9, d10⟩, ⟨d11, d12⟩, n3⟩
  · -- transverse intersections
    intro e₁ e₂ p hne hp1 hp2
    have n2 := aux_OPD_AB_ne G t ht e₂
    rw [aux_OPD_relint] at hp1 hp2
    refine ⟨0, 0, by simp [aux_OPD_arc, aux_OPD_segArc],
      by simp [aux_OPD_arc, aux_OPD_segArc], hp1.1, hp2.1, ?_⟩
    rintro ⟨c, hc⟩
    change aux_OPD_P (aux_OPD_B G t e₂) - aux_OPD_P (aux_OPD_A G t e₂) =
      c • (aux_OPD_P (aux_OPD_B G t e₁) - aux_OPD_P (aux_OPD_A G t e₁)) at hc
    have hc0 := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 0) hc
    have hc1 := congrArg (fun q : EuclideanSpace ℝ (Fin 2) => q 1) hc
    simp only [PiLp.sub_apply, PiLp.smul_apply, aux_OPD_P0, aux_OPD_P1, smul_eq_mul] at hc0 hc1
    have hs : aux_OPD_A G t e₁ + aux_OPD_B G t e₁ = aux_OPD_A G t e₂ + aux_OPD_B G t e₂ := by
      have : (aux_OPD_B G t e₂ - aux_OPD_A G t e₂) *
          (aux_OPD_A G t e₁ + aux_OPD_B G t e₁ - (aux_OPD_A G t e₂ + aux_OPD_B G t e₂)) = 0 := by
        linear_combination (aux_OPD_A G t e₁ + aux_OPD_B G t e₁) * hc0 - hc1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by linarith) n2.symm
      · linarith
    have l1 := aux_OPD_line hp1.1
    have l2 := aux_OPD_line hp2.1
    have hπ : aux_OPD_A G t e₁ * aux_OPD_B G t e₁ = aux_OPD_A G t e₂ * aux_OPD_B G t e₂ := by
      linear_combination l1 - l2 + p 0 * hs
    exact hne (aux_OPD_edge_eq G t ht (aux_OPD_pair hs hπ))
  · -- no shared nondegenerate subarc
    intro e₁ e₂ hne
    rintro ⟨i, j, hi, hj, p, q, hpq, hsub⟩
    have hi0 : i = 0 := by simp [aux_OPD_arc, aux_OPD_segArc] at hi; omega
    have hj0 : j = 0 := by simp [aux_OPD_arc, aux_OPD_segArc] at hj; omega
    subst hi0 hj0
    have hp := hsub (left_mem_segment ℝ p q)
    have hq := hsub (right_mem_segment ℝ p q)
    exact hne (aux_OPD_two_pts G t ht hpq hp.1 hq.1 hp.2 hq.2)

end Drawing

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    Nonempty (OrdinaryPolygonalDrawing G) := by
  obtain ⟨S, hS, hg⟩ := aux_OPD_gen_exists (Fintype.card V)
  let e₁ : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let e₂ : S ≃ Fin (Fintype.card V) := Fintype.equivFinOfCardEq (by simp [hS])
  let t : V → ℝ := fun v => (e₂.symm (e₁ v)).1
  have ht : Function.Injective t := by
    intro u v h
    exact e₁.injective (e₂.symm.injective (Subtype.ext h))
  have hmem : ∀ y ∈ Set.range t, y ∈ S := by
    rintro y ⟨v, rfl⟩
    exact (e₂.symm (e₁ v)).2
  refine aux_OPD_main G t ht ?_
  intro a b c d e f ha hb hc hd he hf hnd
  exact hg a (hmem a ha) b (hmem b hb) c (hmem c hc) d (hmem d hd) e (hmem e he) f (hmem f hf) hnd
