-- Prove2me | solution 1 for PlanarQueue.Planar.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T08:58:19.75644+00:00
-- url     : https://prove2.me/submissions/84258efe-e719-4288-a1f5-a7dad19a95ec

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

set_option autoImplicit false



/-! L1: MacLane-type counting. If the cycle space of a simple graph is spanned by a finite family of
even edge sets covering every edge at most twice, then e ≤ 3n-6 (n ≥ 3), and e ≤ 2n-4 if bipartite. -/

namespace PF12

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the boundary map `ZMod 2 ^ E → ZMod 2 ^ V` -/
noncomputable def bd (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) where
  toFun f v := ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then f e else 0)
  map_add' f g := by
    ext v
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  map_smul' c f := by
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp

omit [DecidableEq V] in
lemma bd_apply (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (f : G.edgeSet → ZMod 2) (v : V) :
    bd G f v = ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then f e else 0) := rfl

lemma zmod2_eq_one {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

lemma sum_mem_pair {a b : V} (hab : a ≠ b) (g : V → ZMod 2) :
    ∑ v, (if v ∈ s(a, b) then g v else 0) = g a + g b := by
  have : ∀ v, (if v ∈ s(a, b) then g v else 0) =
      (if a = v then g v else 0) + (if b = v then g v else 0) := by
    intro v
    by_cases ha : a = v
    · subst ha; simp [hab, Ne.symm hab]
    · by_cases hb : b = v
      · subst hb; simp [hab, Ne.symm hab]
      · have : v ∉ s(a, b) := by
          simp only [Sym2.mem_iff, not_or]; exact ⟨Ne.symm ha, Ne.symm hb⟩
        simp [this, ha, hb]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma sum_bd (G : SimpleGraph V) [DecidableRel G.Adj] (f : G.edgeSet → ZMod 2) :
    ∑ v, bd G f v = 0 := by
  simp only [bd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := G.ne_of_adj he
    have := sum_mem_pair hab (fun _ => f ⟨s(a, b), he⟩)
    have key : ∀ c : ZMod 2, c + c = 0 := by decide
    rw [this]; exact key _

/-- the support of an edge function -/
def supp {G : SimpleGraph V} [DecidableRel G.Adj] (x : G.edgeSet → ZMod 2) : Finset G.edgeSet :=
  univ.filter (fun e => x e ≠ 0)

lemma exists_other {G : SimpleGraph V} [DecidableRel G.Adj] {x : G.edgeSet → ZMod 2}
    (hx : bd G x = 0) (e : G.edgeSet) (he : x e ≠ 0) {a : V} (ha : a ∈ (e : Sym2 V)) :
    ∃ e' : G.edgeSet, e' ≠ e ∧ x e' ≠ 0 ∧ a ∈ (e' : Sym2 V) := by
  by_contra hcon
  push Not at hcon
  have h0 : bd G x a = 0 := by rw [hx]; rfl
  rw [bd_apply] at h0
  rw [Finset.sum_eq_single e] at h0
  · rw [if_pos ha] at h0; exact he h0
  · intro e' _ hne
    by_cases hm : a ∈ (e' : Sym2 V)
    · rw [if_pos hm]
      by_contra hxe
      exact hcon e' hne hxe hm
    · rw [if_neg hm]
  · intro h; exact absurd (Finset.mem_univ e) h

lemma supp_ge_three {G : SimpleGraph V} [DecidableRel G.Adj] {x : G.edgeSet → ZMod 2}
    (hx : bd G x = 0) (hne : x ≠ 0) : 3 ≤ (supp x).card := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hne
  obtain ⟨e0, he0⟩ := e
  induction e0 using Sym2.ind with
  | _ a b =>
    replace he : x ⟨s(a, b), he0⟩ ≠ 0 := he
    have hab : a ≠ b := G.ne_of_adj he0
    obtain ⟨e1, h1ne, h1x, h1a⟩ := exists_other hx ⟨s(a, b), he0⟩ he (Sym2.mem_mk_left a b)
    obtain ⟨e2, h2ne, h2x, h2b⟩ := exists_other hx ⟨s(a, b), he0⟩ he (Sym2.mem_mk_right a b)
    have h12 : e1 ≠ e2 := by
      intro h
      subst h
      apply h1ne
      apply Subtype.ext
      exact (Sym2.mem_and_mem_iff hab).mp ⟨h1a, h2b⟩
    have : 2 < (supp x).card := by
      rw [Finset.two_lt_card_iff]
      refine ⟨⟨s(a, b), he0⟩, e1, e2, ?_, ?_, ?_, Ne.symm h1ne, Ne.symm h2ne, h12⟩ <;>
        simp [supp, he, h1x, h2x]
    omega

lemma supp_even {G : SimpleGraph V} [DecidableRel G.Adj] (C : G.Coloring (Fin 2))
    {x : G.edgeSet → ZMod 2} (hx : bd G x = 0) : Even (supp x).card := by
  have key : ((supp x).card : ZMod 2) = ∑ v ∈ univ.filter (fun v => C v = 0), bd G x v := by
    have h1 : ∑ v ∈ univ.filter (fun v => C v = 0), bd G x v =
        ∑ e : G.edgeSet, x e := by
      simp only [bd_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := G.ne_of_adj he
        have hc : C a ≠ C b := C.valid he
        rw [Finset.sum_filter]
        have := sum_mem_pair hab (fun v => if C v = 0 then x ⟨s(a, b), he⟩ else 0)
        have e1 : ∀ v, (if C v = 0 then (if v ∈ s(a, b) then x ⟨s(a, b), he⟩ else 0) else 0) =
            (if v ∈ s(a, b) then (if C v = 0 then x ⟨s(a, b), he⟩ else 0) else 0) := by
          intro v; split_ifs <;> rfl
        simp only [e1, this]
        have : ∀ i j : Fin 2, i ≠ j → ((if i = 0 then x ⟨s(a, b), he⟩ else 0) +
            (if j = 0 then x ⟨s(a, b), he⟩ else 0) = x ⟨s(a, b), he⟩) := by
          intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
        exact this _ _ hc
    have h2 : ∑ e : G.edgeSet, x e = ((supp x).card : ZMod 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not univ (fun e => x e ≠ 0)]
      rw [Finset.sum_eq_zero (s := univ.filter (fun e => ¬ x e ≠ 0)) (fun e he => by
        simp only [Finset.mem_filter, not_not] at he; exact he.2)]
      rw [add_zero, supp, Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      simp only [Finset.mem_filter] at he
      simp [zmod2_eq_one he.2]
    rw [h1, h2]
  rw [Finset.sum_eq_zero (fun v _ => by rw [hx]; rfl)] at key
  exact (ZMod.natCast_eq_zero_iff_even).mp key

lemma supp_ge_four {G : SimpleGraph V} [DecidableRel G.Adj] (C : G.Coloring (Fin 2))
    {x : G.edgeSet → ZMod 2} (hx : bd G x = 0) (hne : x ≠ 0) : 4 ≤ (supp x).card := by
  have h3 := supp_ge_three hx hne
  obtain ⟨k, hk⟩ := supp_even C hx
  omega

lemma finrank_range_lt (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    Module.finrank (ZMod 2) (LinearMap.range (bd G)) < Fintype.card V := by
  have hlt : LinearMap.range (bd G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨v0⟩ := ‹Nonempty V›
    have hm : (Pi.single v0 (1 : ZMod 2) : V → ZMod 2) ∈ LinearMap.range (bd G) := by
      rw [htop]; exact Submodule.mem_top
    obtain ⟨f, hf⟩ := hm
    have := sum_bd G f
    rw [hf] at this
    simp at this
  have := Submodule.finrank_lt (lt_top_iff_ne_top.mp hlt)
  simpa [Module.finrank_fintype_fun_eq_card] using this

/-- the counting core -/
theorem bound_of_twoSpanned (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V) (s : Finset (G.edgeSet → ZMod 2))
    (hs : ∀ x ∈ s, bd G x = 0)
    (hspan : ∀ z, bd G z = 0 → z ∈ Submodule.span (ZMod 2) (s : Set (G.edgeSet → ZMod 2)))
    (hcov : ∀ e, (s.filter (fun x => x e ≠ 0)).card ≤ 2) :
    Fintype.card G.edgeSet ≤ 3 * Fintype.card V - 6 ∧
      (G.Colorable 2 → Fintype.card G.edgeSet ≤ 2 * Fintype.card V - 4) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨B, hBs, hspanB, hliB⟩ := exists_linearIndependent (ZMod 2) (s : Set (G.edgeSet → ZMod 2))
  set b : Finset (G.edgeSet → ZMod 2) := s.filter (· ∈ B) with hb
  have hbB : (b : Set (G.edgeSet → ZMod 2)) = B := by
    ext x; simp only [hb, Finset.coe_filter, Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hBs h, h⟩
  have hli : LinearIndependent (ZMod 2) (Subtype.val : {x // x ∈ b} → (G.edgeSet → ZMod 2)) := by
    have : LinearIndependent (ZMod 2) (Subtype.val : {x // x ∈ (b : Set (G.edgeSet → ZMod 2))} → (G.edgeSet → ZMod 2)) := by rw [hbB]; exact hliB
    exact this
  have hbs : b ⊆ s := Finset.filter_subset _ _
  -- span b = ker
  have hspan_eq : Submodule.span (ZMod 2) (b : Set (G.edgeSet → ZMod 2)) = LinearMap.ker (bd G) := by
    rw [hbB, hspanB]
    apply le_antisymm
    · rw [Submodule.span_le]; intro x hx; exact hs x hx
    · intro z hz; exact hspan z hz
  have hk : Module.finrank (ZMod 2) (LinearMap.ker (bd G)) = b.card := by
    rw [← hspan_eq]; exact finrank_span_finset_eq_card hli
  have hrn := LinearMap.finrank_range_add_finrank_ker (bd G)
  rw [Module.finrank_fintype_fun_eq_card, hk] at hrn
  have hrl := finrank_range_lt G
  -- members of b are nonzero cycles
  have hbz : ∀ x ∈ b, bd G x = 0 := fun x hx => hs x (hbs hx)
  have hbne : ∀ x ∈ b, x ≠ 0 := by
    intro x hx
    exact hli.ne_zero (i := ⟨x, hx⟩)
  set σ : (G.edgeSet → ZMod 2) := ∑ x ∈ b, x with hσ
  have hσz : bd G σ = 0 := by rw [hσ, map_sum]; exact Finset.sum_eq_zero hbz
  have hσne : b.Nonempty → σ ≠ 0 := by
    intro hne hzero
    have := (Fintype.linearIndependent_iff.mp hli) (fun _ => 1) (by
      simp only [one_smul]
      rw [Finset.sum_coe_sort b (fun x => x)]
      exact hzero)
    obtain ⟨x, hx⟩ := hne
    exact one_ne_zero (this ⟨x, hx⟩)
  -- the double count
  have hcount : ∑ x ∈ b, (supp x).card + (supp σ).card ≤ 2 * Fintype.card G.edgeSet := by
    have e1 : ∑ x ∈ b, (supp x).card = ∑ e : G.edgeSet, (b.filter (fun x => x e ≠ 0)).card := by
      simp only [supp, Finset.card_filter]
      exact Finset.sum_comm
    have e2 : (supp σ).card = ∑ e : G.edgeSet, (if σ e ≠ 0 then 1 else 0) := by
      simp only [supp, Finset.card_filter]
    rw [e1, e2, ← Finset.sum_add_distrib]
    have : ∀ e : G.edgeSet, (b.filter (fun x => x e ≠ 0)).card + (if σ e ≠ 0 then 1 else 0) ≤ 2 := by
      intro e
      have hm : (b.filter (fun x => x e ≠ 0)).card ≤ 2 :=
        le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hbs)) (hcov e)
      have hσe : σ e = ((b.filter (fun x => x e ≠ 0)).card : ZMod 2) := by
        rw [hσ, Finset.sum_apply]
        rw [← Finset.sum_filter_add_sum_filter_not b (fun x => x e ≠ 0)]
        rw [Finset.sum_eq_zero (s := b.filter (fun x => ¬ x e ≠ 0)) (fun x hx => by
          simp only [Finset.mem_filter, not_not] at hx; exact hx.2)]
        rw [add_zero, Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        simp only [Finset.mem_filter] at hx
        simp [zmod2_eq_one hx.2]
      rcases Nat.lt_or_ge (b.filter (fun x => x e ≠ 0)).card 2 with h | h
      · split_ifs <;> omega
      · have h2 : (b.filter (fun x => x e ≠ 0)).card = 2 := le_antisymm hm h
        rw [hσe, h2]
        have : ((2 : ℕ) : ZMod 2) = 0 := by decide
        rw [this]; simp
    calc ∑ e : G.edgeSet, ((b.filter (fun x => x e ≠ 0)).card + (if σ e ≠ 0 then 1 else 0))
        ≤ ∑ _e : G.edgeSet, 2 := Finset.sum_le_sum fun e _ => this e
      _ = 2 * Fintype.card G.edgeSet := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]; ring
  refine ⟨?_, ?_⟩
  · rcases b.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty] at hrn
      omega
    · have h3 : 3 * b.card ≤ ∑ x ∈ b, (supp x).card := by
        rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun x hx => supp_ge_three (hbz x hx) (hbne x hx)
      have h3' := supp_ge_three hσz (hσne hne)
      omega
  · rintro ⟨C⟩
    rcases b.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty] at hrn
      omega
    · have h4 : 4 * b.card ≤ ∑ x ∈ b, (supp x).card := by
        rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun x hx => supp_ge_four C (hbz x hx) (hbne x hx)
      have h4' := supp_ge_four C hσz (hσne hne)
      omega

end PF12



/-! L2: deleting coordinates from a family that covers every coordinate at most twice. -/

namespace PF12

open Finset

section L2
variable {E : Type} [DecidableEq E]

/-- every coordinate is nonzero in at most two members -/
def Cov2 (s : Finset (E → ZMod 2)) : Prop := ∀ e, (s.filter (fun x => x e ≠ 0)).card ≤ 2

lemma zmod2_eq_one' {z : ZMod 2} (h : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl h
  · rfl

omit [DecidableEq E] in
lemma span_coord_zero {s : Finset (E → ZMod 2)} {r : E} (h : ∀ x ∈ s, x r = 0) {z : E → ZMod 2}
    (hz : z ∈ Submodule.span (ZMod 2) (s : Set (E → ZMod 2))) : z r = 0 := by
  have : Submodule.span (ZMod 2) (s : Set (E → ZMod 2)) ≤
      LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : E => ZMod 2) r) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_proj, Function.eval]
    exact h x hx
  have := this hz
  simpa using this

lemma delete_one (s : Finset (E → ZMod 2)) (hs : Cov2 s) (r : E) :
    ∃ s' : Finset (E → ZMod 2),
      (∀ x ∈ s', x ∈ Submodule.span (ZMod 2) (s : Set (E → ZMod 2)) ∧ x r = 0) ∧
      (∀ z ∈ Submodule.span (ZMod 2) (s : Set (E → ZMod 2)), z r = 0 →
        z ∈ Submodule.span (ZMod 2) (s' : Set (E → ZMod 2))) ∧ Cov2 s' := by
  classical
  set T := s.filter (fun x => x r ≠ 0) with hT
  set U := s.filter (fun x => ¬ x r ≠ 0) with hU
  have hsUT : s = U ∪ T := by
    rw [hU, hT, Finset.union_comm, Finset.filter_union_filter_not_eq]
  have hUs : U ⊆ s := Finset.filter_subset _ _
  have hUr : ∀ x ∈ U, x r = 0 := by
    intro x hx; simp only [hU, Finset.mem_filter, not_not] at hx; exact hx.2
  have hTr : ∀ x ∈ T, x r = 1 := by
    intro x hx; simp only [hT, Finset.mem_filter] at hx; exact zmod2_eq_one' hx.2
  have hspanUT : Submodule.span (ZMod 2) (s : Set (E → ZMod 2)) =
      Submodule.span (ZMod 2) (U : Set (E → ZMod 2)) ⊔ Submodule.span (ZMod 2) (T : Set (E → ZMod 2)) := by
    rw [← Submodule.span_union, ← Finset.coe_union, ← hsUT]
  have hTcard : T.card ≤ 2 := hs r
  have hUmem : ∀ x ∈ U, x ∈ Submodule.span (ZMod 2) (s : Set (E → ZMod 2)) ∧ x r = 0 :=
    fun x hx => ⟨Submodule.subset_span (hUs hx), hUr x hx⟩
  have hcovU : Cov2 U := fun e =>
    le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hUs)) (hs e)
  interval_cases hc : T.card
  · -- no member touches r
    refine ⟨U, hUmem, ?_, hcovU⟩
    intro z hz _
    rw [Finset.card_eq_zero] at hc
    rw [hspanUT, hc, Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at hz
    exact hz
  · obtain ⟨x1, hx1⟩ := Finset.card_eq_one.mp hc
    refine ⟨U, hUmem, ?_, hcovU⟩
    intro z hz hzr
    rw [hspanUT, hx1, Finset.coe_singleton, Submodule.mem_sup] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hyr : y r = 0 := span_coord_zero hUr hy
    have h1 : x1 r = 1 := hTr x1 (by rw [hx1]; exact Finset.mem_singleton_self _)
    have hc0 : c = 0 := by
      have := hzr
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyr, h1, zero_add, mul_one] at this
      exact this
    rw [hc0, zero_smul, add_zero]; exact hy
  · obtain ⟨x1, x2, hne, hx12⟩ := Finset.card_eq_two.mp hc
    have h1T : x1 ∈ T := by rw [hx12]; simp
    have h2T : x2 ∈ T := by rw [hx12]; simp
    have h1 : x1 r = 1 := hTr x1 h1T
    have h2 : x2 r = 1 := hTr x2 h2T
    have h1s : x1 ∈ s := (Finset.filter_subset _ _) h1T
    have h2s : x2 ∈ s := (Finset.filter_subset _ _) h2T
    refine ⟨insert (x1 + x2) U, ?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · refine ⟨Submodule.add_mem _ (Submodule.subset_span h1s) (Submodule.subset_span h2s), ?_⟩
        simp only [Pi.add_apply, h1, h2]; decide
      · exact hUmem x hx
    · intro z hz hzr
      rw [hspanUT, hx12, Finset.coe_insert, Finset.coe_singleton, Submodule.mem_sup] at hz
      obtain ⟨y, hy, w, hw, rfl⟩ := hz
      obtain ⟨c1, c2, rfl⟩ := Submodule.mem_span_pair.mp hw
      have hyr : y r = 0 := span_coord_zero hUr hy
      have hcc : c2 = c1 := by
        have := hzr
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyr, h1, h2, zero_add, mul_one] at this
        have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
        exact key c1 c2 this
      rw [hcc, ← smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.span_mono (by intro x hx; simp only [Finset.coe_insert]; exact Set.mem_insert_of_mem _ hx) hy
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · intro e
      rw [Finset.filter_insert]
      split_ifs with hp
      · -- x1+x2 is nonzero at e, so one of x1, x2 is, and it is not in U
        have hor : x1 e ≠ 0 ∨ x2 e ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hp
          simp [hcon.1, hcon.2]
        have hxU : ∀ x ∈ T, x ∉ U := by
          intro x hx hxU
          have := hUr x hxU
          rw [hTr x hx] at this
          exact one_ne_zero this
        rcases hor with h | h
        · calc (insert (x1 + x2) (U.filter fun x => x e ≠ 0)).card
              ≤ (U.filter fun x => x e ≠ 0).card + 1 := Finset.card_insert_le _ _
            _ = (insert x1 (U.filter fun x => x e ≠ 0)).card := by
                rw [Finset.card_insert_of_notMem]
                intro hm; exact hxU x1 h1T (Finset.mem_filter.mp hm).1
            _ ≤ (s.filter fun x => x e ≠ 0).card := by
                apply Finset.card_le_card
                intro x hx
                rw [Finset.mem_insert] at hx
                rcases hx with rfl | hx
                · exact Finset.mem_filter.mpr ⟨h1s, h⟩
                · exact Finset.filter_subset_filter _ hUs hx
            _ ≤ 2 := hs e
        · calc (insert (x1 + x2) (U.filter fun x => x e ≠ 0)).card
              ≤ (U.filter fun x => x e ≠ 0).card + 1 := Finset.card_insert_le _ _
            _ = (insert x2 (U.filter fun x => x e ≠ 0)).card := by
                rw [Finset.card_insert_of_notMem]
                intro hm; exact hxU x2 h2T (Finset.mem_filter.mp hm).1
            _ ≤ (s.filter fun x => x e ≠ 0).card := by
                apply Finset.card_le_card
                intro x hx
                rw [Finset.mem_insert] at hx
                rcases hx with rfl | hx
                · exact Finset.mem_filter.mpr ⟨h2s, h⟩
                · exact Finset.filter_subset_filter _ hUs hx
            _ ≤ 2 := hs e
      · exact hcovU e

lemma delete_set (s₀ : Finset (E → ZMod 2)) (h₀ : Cov2 s₀) (R : Finset E) :
    ∃ s' : Finset (E → ZMod 2),
      (∀ x ∈ s', x ∈ Submodule.span (ZMod 2) (s₀ : Set (E → ZMod 2)) ∧ ∀ r ∈ R, x r = 0) ∧
      (∀ z ∈ Submodule.span (ZMod 2) (s₀ : Set (E → ZMod 2)), (∀ r ∈ R, z r = 0) →
        z ∈ Submodule.span (ZMod 2) (s' : Set (E → ZMod 2))) ∧ Cov2 s' := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    exact ⟨s₀, fun x hx => ⟨Submodule.subset_span hx, by simp⟩, fun z hz _ => hz, h₀⟩
  | insert r R _ ih =>
    obtain ⟨s1, hm1, hsp1, hc1⟩ := ih
    obtain ⟨s2, hm2, hsp2, hc2⟩ := delete_one s1 hc1 r
    have hle : Submodule.span (ZMod 2) (s1 : Set (E → ZMod 2)) ≤
        Submodule.span (ZMod 2) (s₀ : Set (E → ZMod 2)) := by
      rw [Submodule.span_le]; intro x hx; exact (hm1 x hx).1
    refine ⟨s2, ?_, ?_, hc2⟩
    · intro x hx
      refine ⟨hle (hm2 x hx).1, ?_⟩
      intro r' hr'
      rw [Finset.mem_insert] at hr'
      rcases hr' with rfl | hr'
      · exact (hm2 x hx).2
      · exact span_coord_zero (fun y hy => (hm1 y hy).2 r' hr') (hm2 x hx).1
    · intro z hz hzR
      apply hsp2
      · exact hsp1 z hz (fun r' hr' => hzR r' (Finset.mem_insert_of_mem hr'))
      · exact hzR r (Finset.mem_insert_self r R)

end L2

end PF12



/-! L3: an even edge function of the Z^2 grid supported in a box is a sum of unit squares. -/

namespace PF12

open Finset

/-- horizontal grid edge from `p` -/
def gH (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1 + 1, p.2))
/-- vertical grid edge from `p` -/
def gV (p : ℤ × ℤ) : Sym2 (ℤ × ℤ) := s(p, (p.1, p.2 + 1))

lemma gH_inj {p q : ℤ × ℤ} : gH p = gH q ↔ p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [gH, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro (h | h) <;> omega
  · rintro ⟨rfl, rfl⟩; left; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

lemma gV_inj {p q : ℤ × ℤ} : gV p = gV q ↔ p = q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [gV, Sym2.eq_iff, Prod.mk.injEq]
  constructor
  · rintro (h | h) <;> omega
  · rintro ⟨rfl, rfl⟩; left; exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩

lemma gH_ne_gV (p q : ℤ × ℤ) : gH p ≠ gV q := by
  obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
  simp only [gH, gV, ne_eq, Sym2.eq_iff, Prod.mk.injEq]
  omega

/-- mod-2 degree of a grid edge function at a point -/
def gdeg (z : Sym2 (ℤ × ℤ) → ZMod 2) (p : ℤ × ℤ) : ZMod 2 :=
  z (gH p) + z (gH (p.1 - 1, p.2)) + z (gV p) + z (gV (p.1, p.2 - 1))

/-- the boundary of the unit square with lower-left corner `q` -/
def sq (q : ℤ × ℤ) : Sym2 (ℤ × ℤ) → ZMod 2 := fun e =>
  if e = gH q ∨ e = gV q ∨ e = gH (q.1, q.2 + 1) ∨ e = gV (q.1 + 1, q.2) then 1 else 0

/-- the box `[-M, M]^2` -/
def InBox (M : ℤ) (p : ℤ × ℤ) : Prop := -M ≤ p.1 ∧ p.1 ≤ M ∧ -M ≤ p.2 ∧ p.2 ≤ M

/-- grid edge functions supported on edges of the box -/
def BoxSupp (M : ℤ) (z : Sym2 (ℤ × ℤ) → ZMod 2) : Prop :=
  ∀ e, z e ≠ 0 → ∃ p : ℤ × ℤ, (e = gH p ∧ InBox M p ∧ InBox M (p.1 + 1, p.2)) ∨
    (e = gV p ∧ InBox M p ∧ InBox M (p.1, p.2 + 1))

lemma zH_zero {M : ℤ} {z : Sym2 (ℤ × ℤ) → ZMod 2} (hz : BoxSupp M z) (p : ℤ × ℤ)
    (h : ¬ (InBox M p ∧ InBox M (p.1 + 1, p.2))) : z (gH p) = 0 := by
  by_contra hne
  obtain ⟨q, hq | hq⟩ := hz _ hne
  · rw [gH_inj] at hq; obtain ⟨rfl, h1, h2⟩ := hq; exact h ⟨h1, h2⟩
  · exact gH_ne_gV _ _ hq.1

lemma zV_zero {M : ℤ} {z : Sym2 (ℤ × ℤ) → ZMod 2} (hz : BoxSupp M z) (p : ℤ × ℤ)
    (h : ¬ (InBox M p ∧ InBox M (p.1, p.2 + 1))) : z (gV p) = 0 := by
  by_contra hne
  obtain ⟨q, hq | hq⟩ := hz _ hne
  · exact gH_ne_gV _ _ hq.1.symm
  · rw [gV_inj] at hq; obtain ⟨rfl, h1, h2⟩ := hq; exact h ⟨h1, h2⟩

section L3
variable (M : ℤ) (z : Sym2 (ℤ × ℤ) → ZMod 2)

/-- square coefficients: prefix sums of vertical edges along the row -/
noncomputable def coef (q : ℤ × ℤ) : ZMod 2 :=
  ∑ i ∈ Icc (-M) M, if i ≤ q.1 then z (gV (i, q.2)) else 0

variable {M z}

lemma coef_step (hz : BoxSupp M z) (i j : ℤ) :
    coef M z (i, j) = coef M z (i - 1, j) + z (gV (i, j)) := by
  have h : ∀ i' : ℤ, (if i' ≤ i then z (gV (i', j)) else 0) =
      (if i' ≤ i - 1 then z (gV (i', j)) else 0) + (if i' = i then z (gV (i', j)) else 0) := by
    intro i'
    by_cases h1 : i' ≤ i - 1
    · have h2 : i' ≤ i := by omega
      have h3 : i' ≠ i := by omega
      simp [h1, h2, h3]
    · by_cases h3 : i' = i
      · subst h3; simp [h1]
      · have h2 : ¬ i' ≤ i := by omega
        simp [h1, h2, h3]
  simp only [coef]
  rw [Finset.sum_congr rfl (fun i' _ => h i'), Finset.sum_add_distrib, Finset.sum_ite_eq']
  by_cases hi : i ∈ Icc (-M) M
  · rw [if_pos hi]
  · rw [if_neg hi]
    rw [zV_zero hz (i, j) (fun h => hi (Finset.mem_Icc.mpr ⟨h.1.1, h.1.2.1⟩))]

lemma coef_low (i j : ℤ) (hi : i < -M) : coef M z (i, j) = 0 := by
  simp only [coef]
  refine Finset.sum_eq_zero fun i' hi' => ?_
  rw [Finset.mem_Icc] at hi'
  have : ¬ i' ≤ i := by omega
  simp [this]

lemma coef_row (hz : BoxSupp M z) (i j : ℤ) (hj : j < -M ∨ M - 1 < j) : coef M z (i, j) = 0 := by
  simp only [coef]
  refine Finset.sum_eq_zero fun i' _ => ?_
  rw [zV_zero hz (i', j) (by intro h; simp only [InBox] at h; omega)]
  simp

lemma coef_horiz (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) (i j : ℤ) :
    coef M z (i, j) + coef M z (i, j - 1) = z (gH (i, j)) := by
  have base : ∀ i : ℤ, i < -M → coef M z (i, j) + coef M z (i, j - 1) = z (gH (i, j)) := by
    intro i hi
    rw [coef_low i j hi, coef_low i (j - 1) hi, zH_zero hz (i, j) (by
      intro h; simp only [InBox] at h; omega)]
    simp
  have step : ∀ k : ℕ, coef M z (-M - 1 + k, j) + coef M z (-M - 1 + k, j - 1) =
      z (gH (-M - 1 + k, j)) := by
    intro k
    induction k with
    | zero => simpa using base (-M - 1) (by omega)
    | succ k ih =>
      have e1 := coef_step hz (-M - 1 + (k + 1 : ℕ)) j
      have e2 := coef_step hz (-M - 1 + (k + 1 : ℕ)) (j - 1)
      have hd := he (-M - 1 + (k + 1 : ℕ), j)
      simp only [gdeg] at hd
      have r1 : (-M - 1 + ((k + 1 : ℕ) : ℤ) - 1) = -M - 1 + (k : ℤ) := by push_cast; ring
      rw [r1] at e1 e2 hd
      rw [e1, e2]
      have hd' : z (gV (-M - 1 + ((k + 1 : ℕ) : ℤ), j - 1)) =
          z (gV ((-M - 1 + ((k + 1 : ℕ) : ℤ), j).1, (-M - 1 + ((k + 1 : ℕ) : ℤ), j).2 - 1)) := rfl
      rw [hd']
      have key : ∀ a b c d e f : ZMod 2, a + b = c → f + c + d + e = 0 →
          a + d + (b + e) = f := by decide
      exact key _ _ _ _ _ _ ih hd
  by_cases hi : i < -M
  · exact base i hi
  · have := step (i + M + 1).toNat
    have h' : (-M - 1 + ((i + M + 1).toNat : ℤ)) = i := by omega
    rw [h'] at this
    exact this

lemma coef_high (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) (i j : ℤ) (hi : M ≤ i) :
    coef M z (i, j) = 0 := by
  have hM : coef M z (i, j) = coef M z (M, j) := by
    simp only [coef]
    refine Finset.sum_congr rfl fun i' hi' => ?_
    rw [Finset.mem_Icc] at hi'
    have h1 : i' ≤ i := by omega
    have h2 : i' ≤ M := hi'.2
    simp [h1, h2]
  rw [hM]
  -- induction on j
  have hstep : ∀ j : ℤ, coef M z (M, j) = coef M z (M, j - 1) := by
    intro j
    have h := coef_horiz hz he M j
    rw [zH_zero hz (M, j) (by intro h; simp only [InBox] at h; omega)] at h
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact key _ _ h
  have hk : ∀ k : ℕ, coef M z (M, -M - 1 + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using coef_row hz M (-M - 1) (Or.inl (by omega))
    | succ k ih =>
      rw [hstep]
      have : (-M - 1 + ((k + 1 : ℕ) : ℤ) - 1) = -M - 1 + (k : ℤ) := by push_cast; ring
      rw [this]; exact ih
  by_cases hj : j < -M
  · exact coef_row hz M j (Or.inl hj)
  · have := hk (j + M + 1).toNat
    have h' : (-M - 1 + ((j + M + 1).toNat : ℤ)) = j := by omega
    rw [h'] at this
    exact this

/-- the box of squares -/
noncomputable def sqBox (M : ℤ) : Finset (ℤ × ℤ) := Icc (-M) (M - 1) ×ˢ Icc (-M) (M - 1)

lemma coef_out (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) (q : ℤ × ℤ) (hq : q ∉ sqBox M) :
    coef M z q = 0 := by
  obtain ⟨i, j⟩ := q
  simp only [sqBox, Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hq
  rcases hq with (h | h) | (h | h)
  · exact coef_low i j h
  · exact coef_high hz he i j (by omega)
  · exact coef_row hz i j (Or.inl h)
  · exact coef_row hz i j (Or.inr h)

theorem even_mem_span_squares (hz : BoxSupp M z) (he : ∀ p, gdeg z p = 0) :
    z = ∑ q ∈ sqBox M, coef M z q • sq q := by
  funext e
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hV : ∃ p, e = gV p
  · obtain ⟨⟨i, j⟩, rfl⟩ := hV
    rw [Finset.sum_eq_add (i, j) (i - 1, j)]
    · have h1 : sq (i, j) (gV (i, j)) = 1 := by simp [sq]
      have h2 : sq (i - 1, j) (gV (i, j)) = 1 := by
        simp only [sq]; rw [if_pos]; right; right; right; congr 1; ext <;> simp
      rw [h1, h2, mul_one, mul_one, coef_step hz i j]
      have key : ∀ a b : ZMod 2, b = a + b + a := by decide
      exact key _ _
    · intro h; simp only [Prod.mk.injEq] at h; omega
    · intro c _ hc
      obtain ⟨c1, c2⟩ := c
      have : sq (c1, c2) (gV (i, j)) = 0 := by
        simp only [sq]
        rw [if_neg]
        simp only [not_or]
        refine ⟨(gH_ne_gV _ _).symm, ?_, (gH_ne_gV _ _).symm, ?_⟩
        · rw [gV_inj]; exact fun h => hc.1 h.symm
        · rw [gV_inj]; intro h; apply hc.2; simp only [Prod.mk.injEq] at h ⊢; omega
      rw [this, mul_zero]
    · intro h; rw [coef_out hz he _ h, zero_mul]
    · intro h; rw [coef_out hz he _ h, zero_mul]
  by_cases hH : ∃ p, e = gH p
  · obtain ⟨⟨i, j⟩, rfl⟩ := hH
    rw [Finset.sum_eq_add (i, j) (i, j - 1)]
    · have h1 : sq (i, j) (gH (i, j)) = 1 := by simp [sq]
      have h2 : sq (i, j - 1) (gH (i, j)) = 1 := by
        simp only [sq]; rw [if_pos]; right; right; left; congr 1; ext <;> simp
      rw [h1, h2, mul_one, mul_one, coef_horiz hz he i j]
    · intro h; simp only [Prod.mk.injEq] at h; omega
    · intro c _ hc
      obtain ⟨c1, c2⟩ := c
      have : sq (c1, c2) (gH (i, j)) = 0 := by
        simp only [sq]
        rw [if_neg]
        simp only [not_or]
        refine ⟨?_, gH_ne_gV _ _, ?_, gH_ne_gV _ _⟩
        · rw [gH_inj]; exact fun h => hc.1 h.symm
        · rw [gH_inj]; intro h; apply hc.2; simp only [Prod.mk.injEq] at h ⊢; omega
      rw [this, mul_zero]
    · intro h; rw [coef_out hz he _ h, zero_mul]
    · intro h; rw [coef_out hz he _ h, zero_mul]
  · push Not at hV hH
    have hz0 : z e = 0 := by
      by_contra hne
      obtain ⟨p, hp | hp⟩ := hz e hne
      · exact hH p hp.1
      · exact hV p hp.1
    rw [hz0]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    have : sq q e = 0 := by
      simp only [sq]
      rw [if_neg]
      simp only [not_or]
      exact ⟨hH _, hV _, hH _, hV _⟩
    rw [this, mul_zero]

end L3

end PF12



/-! L4: a grid model of `G` gives a family of cycles of `G` spanning its cycle space and covering
every edge at most twice. Needs L1 (bd, sum_mem_pair), L2 (Cov2, delete_set), L3 (gH, gV, sq, gdeg). -/

namespace PF12

open Finset

/-- grid adjacency -/
def gAdj (a b : ℤ × ℤ) : Prop :=
  b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1)

/-- indicator of one grid edge -/
def dlt (g : Sym2 (ℤ × ℤ)) : Sym2 (ℤ × ℤ) → ZMod 2 := fun g' => if g' = g then 1 else 0

/-- indicator of a point -/
def ind (p a : ℤ × ℤ) : ZMod 2 := if p = a then 1 else 0

lemma gV_ne_gH (p q : ℤ × ℤ) : gV p ≠ gH q := fun h => gH_ne_gV q p h.symm

lemma gdeg_add (x y : Sym2 (ℤ × ℤ) → ZMod 2) (p : ℤ × ℤ) :
    gdeg (x + y) p = gdeg x p + gdeg y p := by
  simp only [gdeg, Pi.add_apply]; ring

lemma gdeg_zero (p : ℤ × ℤ) : gdeg 0 p = 0 := by simp [gdeg]

lemma gdeg_sum {ι : Type} (s : Finset ι) (c : ι → ZMod 2) (x : ι → Sym2 (ℤ × ℤ) → ZMod 2)
    (p : ℤ × ℤ) : gdeg (∑ i ∈ s, c i • x i) p = ∑ i ∈ s, c i * gdeg (x i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gdeg_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, gdeg_add, ih]
    congr 1
    simp only [gdeg, Pi.smul_apply, smul_eq_mul]; ring

lemma gdeg_dlt_gH (r p : ℤ × ℤ) : gdeg (dlt (gH r)) p = ind p r + ind p (r.1 + 1, r.2) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨r1, r2⟩ := r
  simp only [gdeg, dlt, ind, gH_inj, gV_ne_gH, if_false, add_zero, Prod.mk.injEq]
  have : (p1 - 1 = r1 ∧ p2 = r2) ↔ (p1 = r1 + 1 ∧ p2 = r2) := by omega
  simp only [this]

lemma gdeg_dlt_gV (r p : ℤ × ℤ) : gdeg (dlt (gV r)) p = ind p r + ind p (r.1, r.2 + 1) := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨r1, r2⟩ := r
  simp only [gdeg, dlt, ind, gV_inj, gH_ne_gV, if_false, zero_add, Prod.mk.injEq]
  have : (p1 = r1 ∧ p2 - 1 = r2) ↔ (p1 = r1 ∧ p2 = r2 + 1) := by omega
  simp only [this]

lemma gAdj_cases {a b : ℤ × ℤ} (h : gAdj a b) :
    (s(a, b) = gH a ∧ b = (a.1 + 1, a.2)) ∨ (s(a, b) = gH b ∧ a = (b.1 + 1, b.2)) ∨
    (s(a, b) = gV a ∧ b = (a.1, a.2 + 1)) ∨ (s(a, b) = gV b ∧ a = (b.1, b.2 + 1)) := by
  rcases h with h | h | h | h
  · left; subst h; exact ⟨rfl, rfl⟩
  · right; left; subst h; exact ⟨Sym2.eq_swap, rfl⟩
  · right; right; left; subst h; exact ⟨rfl, rfl⟩
  · right; right; right; subst h; exact ⟨Sym2.eq_swap, rfl⟩

lemma gdeg_dlt (a b : ℤ × ℤ) (h : gAdj a b) (p : ℤ × ℤ) :
    gdeg (dlt s(a, b)) p = ind p a + ind p b := by
  rcases gAdj_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, gdeg_dlt_gH, ← h2]
  · rw [h1, gdeg_dlt_gH, ← h2, add_comm]
  · rw [h1, gdeg_dlt_gV, ← h2]
  · rw [h1, gdeg_dlt_gV, ← h2, add_comm]

/-- one step inside a blob -/
def BlobRel (B : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) : Prop := a ∈ B ∧ b ∈ B ∧ gAdj a b

/-- a grid edge with both ends in `B` -/
def Internal (B : Finset (ℤ × ℤ)) (g : Sym2 (ℤ × ℤ)) : Prop :=
  ∃ x y, g = s(x, y) ∧ x ∈ B ∧ y ∈ B ∧ gAdj x y

lemma blob_join (B : Finset (ℤ × ℤ)) {a b : ℤ × ℤ} (h : Relation.ReflTransGen (BlobRel B) a b) :
    ∃ J : Sym2 (ℤ × ℤ) → ZMod 2, (∀ g, J g ≠ 0 → Internal B g) ∧
      ∀ p, gdeg J p = ind p a + ind p b := by
  induction h with
  | refl =>
    refine ⟨0, fun g h => absurd rfl h, fun p => ?_⟩
    rw [gdeg_zero]
    have key : ∀ c : ZMod 2, 0 = c + c := by decide
    exact key _
  | @tail b c _ hbc ih =>
    obtain ⟨J, hJ, hd⟩ := ih
    refine ⟨J + dlt s(b, c), ?_, ?_⟩
    · intro g hg
      by_cases hJg : J g = 0
      · have : dlt s(b, c) g ≠ 0 := by simpa [hJg] using hg
        have hgb : g = s(b, c) := by by_contra hne; exact this (by simp [dlt, hne])
        exact ⟨b, c, hgb, hbc.1, hbc.2.1, hbc.2.2⟩
      · exact hJ g hJg
    · intro p
      rw [gdeg_add, hd, gdeg_dlt b c hbc.2.2]
      have key : ∀ x y w : ZMod 2, x + y + (y + w) = x + w := by decide
      exact key _ _ _

lemma internal_boxsupp {M : ℤ} {B : Finset (ℤ × ℤ)} (hB : ∀ p ∈ B, InBox M p)
    {g : Sym2 (ℤ × ℤ)} (h : Internal B g) :
    ∃ p : ℤ × ℤ, (g = gH p ∧ InBox M p ∧ InBox M (p.1 + 1, p.2)) ∨
      (g = gV p ∧ InBox M p ∧ InBox M (p.1, p.2 + 1)) := by
  obtain ⟨x, y, rfl, hx, hy, hxy⟩ := h
  have bx := hB x hx; have by' := hB y hy
  rcases gAdj_cases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨x, Or.inl ⟨h1, bx, h2 ▸ by'⟩⟩
  · exact ⟨y, Or.inl ⟨h1, by', h2 ▸ bx⟩⟩
  · exact ⟨x, Or.inr ⟨h1, bx, h2 ▸ by'⟩⟩
  · exact ⟨y, Or.inr ⟨h1, by', h2 ▸ bx⟩⟩

/-- the edges of the unit square at `q` -/
def sqEdges (q : ℤ × ℤ) : Finset (Sym2 (ℤ × ℤ)) :=
  {gH q, gV q, gH (q.1, q.2 + 1), gV (q.1 + 1, q.2)}

lemma sq_two (g : Sym2 (ℤ × ℤ)) : ∃ q1 q2 : ℤ × ℤ, ∀ q, sq q g ≠ 0 → q = q1 ∨ q = q2 := by
  by_cases hV : ∃ p, g = gV p
  · obtain ⟨⟨i, j⟩, rfl⟩ := hV
    refine ⟨(i, j), (i - 1, j), fun q hq => ?_⟩
    obtain ⟨q1, q2⟩ := q
    simp only [sq, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hq
    rcases hq with h | h | h | h
    · exact absurd h (gV_ne_gH _ _)
    · rw [gV_inj] at h; left; exact h.symm
    · exact absurd h (gV_ne_gH _ _)
    · rw [gV_inj] at h; right; simp only [Prod.mk.injEq] at h ⊢; omega
  by_cases hH : ∃ p, g = gH p
  · obtain ⟨⟨i, j⟩, rfl⟩ := hH
    refine ⟨(i, j), (i, j - 1), fun q hq => ?_⟩
    obtain ⟨q1, q2⟩ := q
    simp only [sq, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hq
    rcases hq with h | h | h | h
    · rw [gH_inj] at h; left; exact h.symm
    · exact absurd h (gH_ne_gV _ _)
    · rw [gH_inj] at h; right; simp only [Prod.mk.injEq] at h ⊢; omega
    · exact absurd h (gH_ne_gV _ _)
  · push Not at hV hH
    refine ⟨0, 0, fun q hq => ?_⟩
    simp only [sq, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hq
    rcases hq with h | h | h | h
    · exact absurd h (hH _)
    · exact absurd h (hV _)
    · exact absurd h (hH _)
    · exact absurd h (hV _)

lemma cov_squares [DecidableEq (Sym2 (ℤ × ℤ) → ZMod 2)] (M : ℤ) : Cov2 ((sqBox M).image sq) := by
  intro g
  obtain ⟨q1, q2, hq⟩ := sq_two g
  calc (((sqBox M).image sq).filter (fun x => x g ≠ 0)).card
      ≤ ({sq q1, sq q2} : Finset (Sym2 (ℤ × ℤ) → ZMod 2)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_image] at hx
        obtain ⟨⟨q, _, rfl⟩, hx⟩ := hx
        rcases hq q hx with rfl | rfl <;> simp
    _ ≤ 2 := Finset.card_le_two

/-- box grid edges -/
noncomputable def boxE (M : ℤ) : Finset (Sym2 (ℤ × ℤ)) :=
  ((Icc (-M) M ×ˢ Icc (-M) M).image gH) ∪ ((Icc (-M) M ×ˢ Icc (-M) M).image gV)

lemma sqEdges_sub (M : ℤ) (q : ℤ × ℤ) (hq : q ∈ sqBox M) : sqEdges q ⊆ boxE M := by
  obtain ⟨i, j⟩ := q
  simp only [sqBox, Finset.mem_product, Finset.mem_Icc] at hq
  intro g hg
  simp only [sqEdges, Finset.mem_insert, Finset.mem_singleton] at hg
  simp only [boxE, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_Icc]
  rcases hg with rfl | rfl | rfl | rfl
  · left; exact ⟨(i, j), ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩
  · right; exact ⟨(i, j), ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩
  · left; exact ⟨(i, j + 1), ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩
  · right; exact ⟨(i + 1, j), ⟨⟨by omega, by omega⟩, by omega, by omega⟩, rfl⟩

/-- parity of the number of ends of an edge in `B` -/
noncomputable def par (B : Finset (ℤ × ℤ)) : Sym2 (ℤ × ℤ) → ZMod 2 :=
  Sym2.lift ⟨fun a b => (if a ∈ B then 1 else 0) + (if b ∈ B then 1 else 0), fun a b => add_comm _ _⟩

lemma par_mk (B : Finset (ℤ × ℤ)) (a b : ℤ × ℤ) :
    par B s(a, b) = (if a ∈ B then 1 else 0) + (if b ∈ B then 1 else 0) := rfl

lemma sq_eq_filter (q : ℤ × ℤ) (g : Sym2 (ℤ × ℤ)) : sq q g = if g ∈ sqEdges q then 1 else 0 := by
  simp only [sq, sqEdges, Finset.mem_insert, Finset.mem_singleton]

lemma par_sq (M : ℤ) (B : Finset (ℤ × ℤ)) (q : ℤ × ℤ) (hq : q ∈ sqBox M) :
    ∑ g ∈ boxE M, sq q g * par B g = 0 := by
  classical
  simp only [sq_eq_filter, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (boxE M).filter (fun g => g ∈ sqEdges q) = sqEdges q := by
    ext g; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨sqEdges_sub M q hq h, h⟩⟩
  rw [hf]
  obtain ⟨i, j⟩ := q
  simp only [sqEdges]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · simp only [gH, gV, par_mk]
    have key : ∀ a b c d : ZMod 2, a + b + ((a + c) + ((c + d) + (b + d))) = 0 := by decide
    convert key (if (i, j) ∈ B then 1 else 0) (if (i + 1, j) ∈ B then 1 else 0)
      (if (i, j + 1) ∈ B then 1 else 0) (if (i + 1, j + 1) ∈ B then 1 else 0) using 3
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    repeat' constructor
    all_goals intro h; simp only [gH, gV, Sym2.eq_iff, Prod.mk.injEq] at h; omega

section Model

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma blob_eq {B : V → Finset (ℤ × ℤ)} (hdisj : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    {v w : V} {p : ℤ × ℤ} (hv : p ∈ B v) (hw : p ∈ B w) : v = w := by
  by_contra h
  exact Finset.disjoint_left.mp (hdisj v w h) hv hw

/-- L4: a grid model gives a two-covering spanning family of cycles -/
theorem family_of_model (G : SimpleGraph V) [DecidableRel G.Adj] (M : ℤ)
    (B : V → Finset (ℤ × ℤ)) (hbox : ∀ v, ∀ p ∈ B v, InBox M p)
    (hdisj : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hconn : ∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (BlobRel (B v)) p q)
    (hne : ∀ v, (B v).Nonempty)
    (hadj : ∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, gAdj p q) :
    ∃ s : Finset (G.edgeSet → ZMod 2), (∀ x ∈ s, bd G x = 0) ∧
      (∀ z, bd G z = 0 → z ∈ Submodule.span (ZMod 2) (s : Set (G.edgeSet → ZMod 2))) ∧
      ∀ e, (s.filter (fun x => x e ≠ 0)).card ≤ 2 := by
  classical
  -- endpoints of each edge
  have hout : ∀ e : G.edgeSet, ∃ vw : V × V, s(vw.1, vw.2) = (e : Sym2 V) := fun e =>
    ⟨(e : Sym2 V).out, Quot.out_eq _⟩
  choose vw hvw using hout
  have hadj' : ∀ e : G.edgeSet, G.Adj (vw e).1 (vw e).2 := by
    intro e; have := e.2; rw [← hvw e] at this; exact this
  have hpick : ∀ e : G.edgeSet, ∃ pq : (ℤ × ℤ) × (ℤ × ℤ),
      pq.1 ∈ B (vw e).1 ∧ pq.2 ∈ B (vw e).2 ∧ gAdj pq.1 pq.2 := by
    intro e
    obtain ⟨p, hp, q, hq, h⟩ := hadj _ _ (hadj' e)
    exact ⟨(p, q), hp, hq, h⟩
  choose pq hpq1 hpq2 hpqa using hpick
  set dE : G.edgeSet → Sym2 (ℤ × ℤ) := fun e => s((pq e).1, (pq e).2) with hdE
  have hvne : ∀ e, (vw e).1 ≠ (vw e).2 := fun e => G.ne_of_adj (hadj' e)
  -- dE is injective
  have hinj : ∀ e e', dE e = dE e' → e = e' := by
    intro e e' h
    simp only [hdE, Sym2.eq_iff] at h
    apply Subtype.ext
    rw [← hvw e, ← hvw e']
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 := blob_eq hdisj (hpq1 e) (h1 ▸ hpq1 e')
      have a2 := blob_eq hdisj (hpq2 e) (h2 ▸ hpq2 e')
      rw [a1, a2]
    · have a1 := blob_eq hdisj (hpq1 e) (h1 ▸ hpq2 e')
      have a2 := blob_eq hdisj (hpq2 e) (h2 ▸ hpq1 e')
      rw [a1, a2, Sym2.eq_swap]
  -- designated edges are not internal
  have hnotint : ∀ e u, ¬ Internal (B u) (dE e) := by
    intro e u ⟨x, y, h, hx, hy, _⟩
    simp only [hdE, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hvne e ((blob_eq hdisj (hpq1 e) (h1 ▸ hx)).trans (blob_eq hdisj (hpq2 e) (h2 ▸ hy)).symm)
    · exact hvne e ((blob_eq hdisj (hpq1 e) (h1 ▸ hy)).trans (blob_eq hdisj (hpq2 e) (h2 ▸ hx)).symm)
  -- allowed edges
  let Allowed : Sym2 (ℤ × ℤ) → Prop := fun g => (∃ u, Internal (B u) g) ∨ ∃ e, g = dE e
  let R : Finset (Sym2 (ℤ × ℤ)) := (boxE M).filter (fun g => ¬ Allowed g)
  let s₀ : Finset (Sym2 (ℤ × ℤ) → ZMod 2) := (sqBox M).image sq
  obtain ⟨s', hm', hsp', hc'⟩ := delete_set s₀ (cov_squares M) R
  let π : (Sym2 (ℤ × ℤ) → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2) :=
    LinearMap.funLeft (ZMod 2) (ZMod 2) dE
  have hπ : ∀ x e, π x e = x (dE e) := fun _ _ => rfl
  refine ⟨s'.image π, ?_, ?_, ?_⟩
  · -- members are cycles
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxspan, hxR⟩ := hm' x hx
    funext v
    -- the parity functional
    let Λ : (Sym2 (ℤ × ℤ) → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => ∑ g ∈ boxE M, x g * par (B v) g
        map_add' := by intro a b; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro c a; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
    have hΛ0 : Λ x = 0 := by
      have : Submodule.span (ZMod 2) (s₀ : Set (Sym2 (ℤ × ℤ) → ZMod 2)) ≤ LinearMap.ker Λ := by
        rw [Submodule.span_le]
        intro w hw
        simp only [s₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        exact par_sq M (B v) q hq
      exact this hxspan
    -- x vanishes off the allowed edges and off the box
    have hxbox : ∀ g, x g ≠ 0 → g ∈ boxE M := by
      have : Submodule.span (ZMod 2) (s₀ : Set (Sym2 (ℤ × ℤ) → ZMod 2)) ≤
          { carrier := {w | ∀ g, g ∉ boxE M → w g = 0}
            add_mem' := by intro a b ha hb g hg; simp [ha g hg, hb g hg]
            zero_mem' := by intro g _; rfl
            smul_mem' := by intro c a ha g hg; simp [ha g hg] } := by
        rw [Submodule.span_le]
        intro w hw g hg
        simp only [s₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [sq_eq_filter, if_neg]
        exact fun h => hg (sqEdges_sub M q hq h)
      intro g hg
      by_contra hgb
      exact hg (this hxspan g hgb)
    have hxA : ∀ g, x g ≠ 0 → Allowed g := by
      intro g hg
      by_contra hna
      exact hg (hxR g (Finset.mem_filter.mpr ⟨hxbox g hg, hna⟩))
    -- pointwise: on the support, par = sum over designated edges
    have hpt : ∀ g, x g * par (B v) g =
        ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then (if g = dE e then x g else 0) else 0) := by
      intro g
      by_cases hg : x g = 0
      · simp [hg]
      · rcases hxA g hg with ⟨u, x', y', rfl, hx', hy', _⟩ | ⟨e0, rfl⟩
        · -- internal edge: parity zero, and it is no designated edge
          have hpz : par (B v) s(x', y') = 0 := by
            rw [par_mk]
            by_cases huv : u = v
            · subst huv; simp [hx', hy']; decide
            · have h1 : x' ∉ B v := fun h => huv (blob_eq hdisj hx' h)
              have h2 : y' ∉ B v := fun h => huv (blob_eq hdisj hy' h)
              simp [h1, h2]
          rw [hpz, mul_zero]
          symm
          refine Finset.sum_eq_zero fun e _ => ?_
          have : s(x', y') ≠ dE e := by
            intro h; apply hnotint e u; rw [← h]; exact ⟨x', y', rfl, hx', hy', by assumption⟩
          simp [this]
        · rw [Finset.sum_eq_single e0]
          · have hmem : v ∈ (e0 : Sym2 V) ↔ v = (vw e0).1 ∨ v = (vw e0).2 := by
              rw [← hvw e0, Sym2.mem_iff]
            have hpe : par (B v) (dE e0) = if v ∈ (e0 : Sym2 V) then 1 else 0 := by
              simp only [hdE, par_mk]
              by_cases h1 : v = (vw e0).1
              · have hm : v ∈ (e0 : Sym2 V) := hmem.mpr (Or.inl h1)
                rw [if_pos hm]
                subst h1
                have : (pq e0).2 ∉ B (vw e0).1 := fun h => hvne e0 (blob_eq hdisj h (hpq2 e0))
                simp [hpq1 e0, this]
              · by_cases h2 : v = (vw e0).2
                · have hm : v ∈ (e0 : Sym2 V) := hmem.mpr (Or.inr h2)
                  rw [if_pos hm]
                  subst h2
                  have : (pq e0).1 ∉ B (vw e0).2 := fun h => hvne e0 (blob_eq hdisj (hpq1 e0) h)
                  simp [hpq2 e0, this]
                · have hm : v ∉ (e0 : Sym2 V) := fun h => (hmem.mp h).elim h1 h2
                  rw [if_neg hm]
                  have a1 : (pq e0).1 ∉ B v := fun h => h1 (blob_eq hdisj h (hpq1 e0))
                  have a2 : (pq e0).2 ∉ B v := fun h => h2 (blob_eq hdisj h (hpq2 e0))
                  simp [a1, a2]
            rw [hpe]
            by_cases hv : v ∈ (e0 : Sym2 V) <;> simp [hv]
          · intro e _ hne'
            have : dE e0 ≠ dE e := fun h => hne' (hinj _ _ h).symm
            simp [this]
          · intro h; exact absurd (Finset.mem_univ e0) h
    have hΛ : Λ x = bd G (π x) v := by
      show ∑ g ∈ boxE M, x g * par (B v) g = _
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_comm, bd_apply]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs with hv
      · rw [Finset.sum_ite_eq' (boxE M) (dE e) (fun g => x g), hπ]
        split_ifs with hm
        · rfl
        · by_contra hne'; exact hm (hxbox _ (Ne.symm hne'))
      · simp
    rw [← hΛ, hΛ0]; rfl
  · -- spanning
    intro z hz
    -- roots and blob paths
    choose r hr using hne
    have hJ1 : ∀ e : G.edgeSet, ∃ J : Sym2 (ℤ × ℤ) → ZMod 2,
        (∀ g, J g ≠ 0 → Internal (B (vw e).1) g) ∧
        ∀ p, gdeg J p = ind p (r (vw e).1) + ind p (pq e).1 := fun e =>
      blob_join _ (hconn _ _ (hr _) _ (hpq1 e))
    have hJ2 : ∀ e : G.edgeSet, ∃ J : Sym2 (ℤ × ℤ) → ZMod 2,
        (∀ g, J g ≠ 0 → Internal (B (vw e).2) g) ∧
        ∀ p, gdeg J p = ind p (pq e).2 + ind p (r (vw e).2) := fun e =>
      blob_join _ (hconn _ _ (hpq2 e) _ (hr _))
    choose J1 hJ1s hJ1d using hJ1
    choose J2 hJ2s hJ2d using hJ2
    let ℓ : G.edgeSet → Sym2 (ℤ × ℤ) → ZMod 2 := fun e => dlt (dE e) + J1 e + J2 e
    have hℓd : ∀ e p, gdeg (ℓ e) p = ind p (r (vw e).1) + ind p (r (vw e).2) := by
      intro e p
      simp only [ℓ, gdeg_add, hJ1d, hJ2d, hdE, gdeg_dlt _ _ (hpqa e)]
      have key : ∀ a b c d : ZMod 2, a + b + (c + a) + (b + d) = c + d := by decide
      exact key _ _ _ _
    have hℓA : ∀ e g, ℓ e g ≠ 0 → Allowed g := by
      intro e g hg
      by_cases h1 : J1 e g = 0
      · by_cases h2 : J2 e g = 0
        · right; refine ⟨e, ?_⟩
          by_contra hne'
          apply hg; simp [ℓ, dlt, hne', h1, h2]
        · left; exact ⟨_, hJ2s e g h2⟩
      · left; exact ⟨_, hJ1s e g h1⟩
    let zt : Sym2 (ℤ × ℤ) → ZMod 2 := ∑ e : G.edgeSet, z e • ℓ e
    have hztA : ∀ g, zt g ≠ 0 → Allowed g := by
      intro g hg
      by_contra hna
      apply hg
      simp only [zt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun e _ => ?_
      by_cases h : ℓ e g = 0
      · rw [h, mul_zero]
      · exact absurd (hℓA e g h) hna
    have hztdeg : ∀ p, gdeg zt p = 0 := by
      intro p
      simp only [zt, gdeg_sum, hℓd]
      have : ∀ e : G.edgeSet, z e * (ind p (r (vw e).1) + ind p (r (vw e).2)) =
          ∑ v, (if v ∈ (e : Sym2 V) then z e * ind p (r v) else 0) := by
        intro e
        rw [← hvw e, sum_mem_pair (hvne e) (fun v => z e * ind p (r v)), mul_add]
      rw [Finset.sum_congr rfl (fun e _ => this e), Finset.sum_comm]
      refine Finset.sum_eq_zero fun v _ => ?_
      have h0 : bd G z v = 0 := by rw [hz]; rfl
      rw [bd_apply] at h0
      calc ∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then z e * ind p (r v) else 0)
          = (∑ e : G.edgeSet, (if v ∈ (e : Sym2 V) then z e else 0)) * ind p (r v) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun e _ => ?_; split_ifs <;> simp
        _ = 0 := by rw [h0, zero_mul]
    have hztbox : BoxSupp M zt := by
      intro g hg
      rcases hztA g hg with ⟨u, hu⟩ | ⟨e, rfl⟩
      · exact internal_boxsupp (hbox u) hu
      · have hI : Internal ({(pq e).1, (pq e).2} : Finset (ℤ × ℤ)) (dE e) :=
          ⟨(pq e).1, (pq e).2, rfl, by simp, by simp, hpqa e⟩
        refine internal_boxsupp ?_ hI
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hbox _ _ (hpq1 e)
        · exact hbox _ _ (hpq2 e)
    have hzt0 : zt ∈ Submodule.span (ZMod 2) (s₀ : Set (Sym2 (ℤ × ℤ) → ZMod 2)) := by
      rw [even_mem_span_squares hztbox hztdeg]
      refine Submodule.sum_mem _ fun q hq => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp only [s₀, Finset.coe_image]
      exact Set.mem_image_of_mem _ hq
    have hztR : ∀ g ∈ R, zt g = 0 := by
      intro g hg
      by_contra hne'
      exact (Finset.mem_filter.mp hg).2 (hztA g hne')
    have hzt' := hsp' zt hzt0 hztR
    have hπz : π zt = z := by
      funext e'
      rw [hπ]
      simp only [zt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have : ∀ e, ℓ e (dE e') = if e = e' then 1 else 0 := by
        intro e
        have a1 : J1 e (dE e') = 0 := by
          by_contra h; exact hnotint e' _ (hJ1s e _ h)
        have a2 : J2 e (dE e') = 0 := by
          by_contra h; exact hnotint e' _ (hJ2s e _ h)
        simp only [ℓ, Pi.add_apply, a1, a2, add_zero, dlt]
        by_cases hee : e = e'
        · subst hee; simp
        · have : dE e' ≠ dE e := fun h => hee (hinj _ _ h).symm
          simp [this, hee]
      simp only [this, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp
    rw [← hπz, Finset.coe_image, Submodule.span_image]
    exact Submodule.mem_map_of_mem hzt'
  · -- covering
    intro e
    calc ((s'.image π).filter (fun y => y e ≠ 0)).card
        ≤ ((s'.filter (fun x => x (dE e) ≠ 0)).image π).card := by
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_image] at hy ⊢
          obtain ⟨⟨x, hx, rfl⟩, hy⟩ := hy
          exact ⟨x, ⟨hx, hy⟩, rfl⟩
      _ ≤ (s'.filter (fun x => x (dE e) ≠ 0)).card := Finset.card_image_le
      _ ≤ 2 := hc' _

end Model

end PF12



/-! L5a: cells of the grid of mesh `h`, the grid graph, walks of cells along an arc,
connectivity of boxes and of chains. Needs gAdj, BlobRel (L4). -/

namespace PF12

open Finset

/-- the grid graph on `ℤ × ℤ` -/
def gridG : SimpleGraph (ℤ × ℤ) where
  Adj a b := gAdj a b
  symm := ⟨by
    intro a b h
    unfold gAdj at *
    rcases h with h | h | h | h
    · right; left; exact h
    · left; exact h
    · right; right; right; exact h
    · right; right; left; exact h⟩
  loopless := ⟨by
    intro a h
    unfold gAdj at h
    obtain ⟨a1, a2⟩ := a
    simp only [Prod.mk.injEq] at h
    omega⟩

lemma gridG_adj {a b : ℤ × ℤ} : gridG.Adj a b ↔ gAdj a b := Iff.rfl

/-- the cell containing `x` -/
noncomputable def cellOf (h : ℝ) (x : ℝ × ℝ) : ℤ × ℤ := (⌊x.1 / h⌋, ⌊x.2 / h⌋)

/-- lower-left corner of a cell -/
def corner (h : ℝ) (c : ℤ × ℤ) : ℝ × ℝ := ((c.1 : ℝ) * h, (c.2 : ℝ) * h)

lemma floor_close {h a : ℝ} (hh : 0 < h) : |(⌊a / h⌋ : ℝ) * h - a| < h := by
  have h1 := Int.floor_le (a / h)
  have h2 := Int.lt_floor_add_one (a / h)
  have e : a / h * h = a := div_mul_cancel₀ a hh.ne'
  rw [abs_lt]
  constructor
  · nlinarith
  · nlinarith

lemma dist_corner_cellOf {h : ℝ} (hh : 0 < h) (x : ℝ × ℝ) : dist (corner h (cellOf h x)) x < h := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨floor_close hh, floor_close hh⟩

lemma floor_step {h a b : ℝ} (hh : 0 < h) (hab : |a - b| < h) : |⌊a / h⌋ - ⌊b / h⌋| ≤ 1 := by
  have h1 := Int.floor_le (a / h)
  have h2 := Int.lt_floor_add_one (a / h)
  have h3 := Int.floor_le (b / h)
  have h4 := Int.lt_floor_add_one (b / h)
  have hd : |a / h - b / h| < 1 := by
    rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh]; exact hab
  rw [abs_lt] at hd
  have k1 : ((⌊a / h⌋ - ⌊b / h⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have k2 : ((⌊b / h⌋ - ⌊a / h⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith
  have k1' : ⌊a / h⌋ - ⌊b / h⌋ < 2 := by exact_mod_cast k1
  have k2' : ⌊b / h⌋ - ⌊a / h⌋ < 2 := by exact_mod_cast k2
  rw [abs_le]; constructor <;> omega

lemma walk_x (c1 c2 a : ℤ) (h : |a - c1| ≤ 1) :
    ∃ w : gridG.Walk (c1, c2) (a, c2), ∀ y ∈ w.support, y = (c1, c2) ∨ y = (a, c2) := by
  rcases (show a = c1 ∨ a = c1 + 1 ∨ a = c1 - 1 by rw [abs_le] at h; omega) with rfl | rfl | rfl
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by left; rfl)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by right; left; simp)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto

lemma walk_y (c1 c2 b : ℤ) (h : |b - c2| ≤ 1) :
    ∃ w : gridG.Walk (c1, c2) (c1, b), ∀ y ∈ w.support, y = (c1, c2) ∨ y = (c1, b) := by
  rcases (show b = c2 ∨ b = c2 + 1 ∨ b = c2 - 1 by rw [abs_le] at h; omega) with rfl | rfl | rfl
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by right; right; left; rfl)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto
  · refine ⟨SimpleGraph.Walk.cons (gridG_adj.mpr (by right; right; right; simp)) SimpleGraph.Walk.nil, ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.mem_singleton] at hy
    tauto

lemma step_walk (c c' : ℤ × ℤ) (h1 : |c'.1 - c.1| ≤ 1) (h2 : |c'.2 - c.2| ≤ 1) :
    ∃ w : gridG.Walk c c', ∀ y ∈ w.support, y = c ∨ y = (c'.1, c.2) ∨ y = c' := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := c'
  obtain ⟨w1, hw1⟩ := walk_x c1 c2 d1 h1
  obtain ⟨w2, hw2⟩ := walk_y d1 c2 d2 h2
  refine ⟨w1.append w2, ?_⟩
  intro y hy
  rw [SimpleGraph.Walk.mem_support_append_iff] at hy
  rcases hy with hy | hy
  · rcases hw1 y hy with h | h
    · left; exact h
    · right; left; exact h
  · rcases hw2 y hy with h | h
    · right; left; exact h
    · right; right; exact h

/-- the walk of cells along an arc -/
theorem arc_walk {x y : ℝ × ℝ} (γ : Path x y) {h : ℝ} (hh : 0 < h) :
    ∃ w : gridG.Walk (cellOf h x) (cellOf h y),
      (∀ c ∈ w.support, ∃ t : unitInterval, dist (corner h c) (γ t) < 2 * h) ∧
      w.support.Pairwise (fun a b => ∃ ta tb : unitInterval, ta ≤ tb ∧
        dist (corner h a) (γ ta) < 2 * h ∧ dist (corner h b) (γ tb) < 2 * h) := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) h hh
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN' : (1 : ℝ) / N < δ := by
    rw [div_lt_iff₀ hNpos]; rw [div_lt_iff₀ hδ] at hN; linarith
  let T : ℕ → unitInterval := fun k => Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)
  have hTval : ∀ k, k ≤ N → (T k : ℝ) = (k : ℝ) / N := by
    intro k hk
    simp only [T]
    rw [Set.projIcc_of_mem]
    constructor
    · positivity
    · rw [div_le_one hNpos]; exact_mod_cast hk
  have hTmono : ∀ k, k + 1 ≤ N → T k ≤ T (k + 1) := by
    intro k hk
    show (T k : ℝ) ≤ T (k + 1)
    rw [hTval k (by omega), hTval (k + 1) hk]
    apply div_le_div_of_nonneg_right _ hNpos.le
    push_cast; linarith
  have hTclose : ∀ k, k + 1 ≤ N → dist (γ (T k)) (γ (T (k + 1))) < h := by
    intro k hk
    apply hU
    rw [Subtype.dist_eq, hTval k (by omega), hTval (k + 1) hk, Real.dist_eq]
    rw [show (k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N = -(1 / N) by push_cast; ring, abs_neg,
      abs_of_pos (by positivity)]
    exact hN'
  -- induction over the samples
  have key : ∀ k, k ≤ N → ∃ w : gridG.Walk (cellOf h (γ 0)) (cellOf h (γ (T k))),
      (∀ c ∈ w.support, ∃ t : unitInterval, t ≤ T k ∧ dist (corner h c) (γ t) < 2 * h) ∧
      w.support.Pairwise (fun a b => ∃ ta tb : unitInterval, ta ≤ tb ∧
        dist (corner h a) (γ ta) < 2 * h ∧ dist (corner h b) (γ tb) < 2 * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hT0 : T 0 = 0 := by
        apply Subtype.ext; rw [hTval 0 (Nat.zero_le _)]; simp
      rw [hT0]
      refine ⟨SimpleGraph.Walk.nil, ?_, by simp⟩
      intro c hc
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hc
      subst hc
      exact ⟨0, le_refl _, lt_trans (dist_corner_cellOf hh _) (by linarith)⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hwn, hwp⟩ := ih (by omega)
      have hcl := hTclose k hk
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hcl
      have hs1 : |(cellOf h (γ (T (k + 1)))).1 - (cellOf h (γ (T k))).1| ≤ 1 := by
        rw [abs_sub_comm]; exact floor_step hh hcl.1
      have hs2 : |(cellOf h (γ (T (k + 1)))).2 - (cellOf h (γ (T k))).2| ≤ 1 := by
        rw [abs_sub_comm]; exact floor_step hh hcl.2
      obtain ⟨w', hw'⟩ := step_walk (cellOf h (γ (T k))) (cellOf h (γ (T (k + 1)))) hs1 hs2
      -- every new cell is near γ (T k)
      have hnear : ∀ y ∈ w'.support, dist (corner h y) (γ (T k)) < 2 * h := by
        intro y hy
        have dc := dist_corner_cellOf hh (γ (T k))
        have dc' := dist_corner_cellOf hh (γ (T (k + 1)))
        have hcl2 := hTclose k hk
        rcases hw' y hy with rfl | rfl | rfl
        · linarith
        · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
          rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at dc dc' hcl2
          simp only [corner] at dc dc' ⊢
          constructor
          · calc |((cellOf h (γ (T (k + 1)))).1 : ℝ) * h - (γ (T k)).1|
                ≤ |((cellOf h (γ (T (k + 1)))).1 : ℝ) * h - (γ (T (k + 1))).1| + |(γ (T k)).1 - (γ (T (k + 1))).1| := by
                  rw [abs_sub_comm (γ (T k)).1]; exact abs_sub_le _ _ _
              _ < h + h := add_lt_add dc'.1 hcl2.1
              _ = 2 * h := by ring
          · linarith [dc.2]
        · calc dist (corner h (cellOf h (γ (T (k + 1))))) (γ (T k))
              ≤ dist (corner h (cellOf h (γ (T (k + 1))))) (γ (T (k + 1))) + dist (γ (T (k + 1))) (γ (T k)) :=
                dist_triangle _ _ _
            _ < h + h := add_lt_add dc' (by rw [dist_comm]; exact hcl2)
            _ = 2 * h := by ring
      refine ⟨w.append w', ?_, ?_⟩
      · intro y hy
        rw [SimpleGraph.Walk.mem_support_append_iff] at hy
        rcases hy with hy | hy
        · obtain ⟨t, ht, hd⟩ := hwn y hy
          exact ⟨t, le_trans ht (hTmono k hk), hd⟩
        · exact ⟨T k, hTmono k hk, hnear y hy⟩
      · rw [SimpleGraph.Walk.support_append, List.pairwise_append]
        refine ⟨hwp, ?_, ?_⟩
        · apply List.Pairwise.imp_of_mem (R := fun _ _ => True)
          · intro a b ha hb _
            exact ⟨T k, T k, le_refl _, hnear a (List.mem_of_mem_tail ha),
              hnear b (List.mem_of_mem_tail hb)⟩
          · exact List.pairwise_of_forall (fun _ _ => trivial)
        · intro a ha b hb
          obtain ⟨t, ht, hd⟩ := hwn a ha
          exact ⟨t, T k, ht, hd, hnear b (List.mem_of_mem_tail hb)⟩
  obtain ⟨w, hwn, hwp⟩ := key N le_rfl
  have hTN : T N = 1 := by
    apply Subtype.ext; rw [hTval N le_rfl]; simp [hNpos.ne']
  refine ⟨w.copy (by rw [Path.source]) (by rw [hTN, Path.target]), ?_, ?_⟩
  · intro c hc
    rw [SimpleGraph.Walk.support_copy] at hc
    obtain ⟨t, _, hd⟩ := hwn c hc
    exact ⟨t, hd⟩
  · rw [SimpleGraph.Walk.support_copy]; exact hwp

/-- monotonicity of blob reachability -/
lemma reach_mono {B B' : Finset (ℤ × ℤ)} (hBB : B ⊆ B') {p q : ℤ × ℤ}
    (h : Relation.ReflTransGen (BlobRel B) p q) : Relation.ReflTransGen (BlobRel B') p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hBB hbc.1, hBB hbc.2.1, hbc.2.2⟩

lemma blobRel_symm (B : Finset (ℤ × ℤ)) {a b : ℤ × ℤ} (h : BlobRel B a b) : BlobRel B b a :=
  ⟨h.2.1, h.1, (show gridG.Adj a b from h.2.2).symm⟩

lemma reach_symm {B : Finset (ℤ × ℤ)} {p q : ℤ × ℤ}
    (h : Relation.ReflTransGen (BlobRel B) p q) : Relation.ReflTransGen (BlobRel B) q p := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (blobRel_symm B hbc) ih

/-- a chain of grid cells inside `B` is connected inside `B` -/
lemma chain_reach (B : Finset (ℤ × ℤ)) : ∀ (a : ℤ × ℤ) (l : List (ℤ × ℤ)),
    List.IsChain gridG.Adj (a :: l) → (∀ x ∈ a :: l, x ∈ B) →
    ∀ x ∈ a :: l, Relation.ReflTransGen (BlobRel B) a x := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ _ x hx
    simp only [List.mem_singleton] at hx
    subst hx; exact Relation.ReflTransGen.refl
  | cons b l ih =>
    intro hc hB x hx
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Relation.ReflTransGen.refl
    · have hab : BlobRel B a b := ⟨hB a (by simp), hB b (by simp), hc.1⟩
      exact Relation.ReflTransGen.head hab
        (ih b hc.2 (fun y hy => hB y (List.mem_cons_of_mem _ hy)) x hx)

/-- a box of cells is connected -/
lemma box_reach (B : Finset (ℤ × ℤ)) (a1 b1 a2 b2 : ℤ)
    (hB : ∀ c : ℤ × ℤ, a1 ≤ c.1 → c.1 ≤ b1 → a2 ≤ c.2 → c.2 ≤ b2 → c ∈ B)
    (p : ℤ × ℤ) (hp : a1 ≤ p.1 ∧ p.1 ≤ b1 ∧ a2 ≤ p.2 ∧ p.2 ≤ b2) :
    Relation.ReflTransGen (BlobRel B) (a1, a2) p := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  -- move along the bottom row, then up
  have hx : ∀ k : ℕ, a1 + k ≤ b1 → Relation.ReflTransGen (BlobRel B) (a1, a2) (a1 + k, a2) := by
    intro k
    induction k with
    | zero => intro _; simp only [Nat.cast_zero, add_zero]; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      refine Relation.ReflTransGen.tail (ih (by push_cast at hk; omega)) ⟨?_, ?_, ?_⟩
      · exact hB _ (by dsimp only; omega) (by dsimp only; push_cast at hk; omega) (le_refl _) (by omega)
      · exact hB _ (by dsimp only; omega) (by dsimp only; push_cast at hk; omega) (le_refl _) (by omega)
      · left; refine Prod.ext ?_ ?_ <;> dsimp only <;> push_cast <;> ring
  have hy : ∀ k : ℕ, a2 + k ≤ b2 →
      Relation.ReflTransGen (BlobRel B) (p1, a2) (p1, a2 + k) := by
    intro k
    induction k with
    | zero => intro _; simp only [Nat.cast_zero, add_zero]; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      refine Relation.ReflTransGen.tail (ih (by push_cast at hk; omega)) ⟨?_, ?_, ?_⟩
      · exact hB _ hp1 hp2 (by dsimp only; omega) (by dsimp only; push_cast at hk; omega)
      · exact hB _ hp1 hp2 (by dsimp only; omega) (by dsimp only; push_cast at hk; omega)
      · right; right; left; refine Prod.ext ?_ ?_ <;> dsimp only <;> push_cast <;> ring
  have h1 := hx (p1 - a1).toNat (by omega)
  have h2 := hy (p2 - a2).toNat (by omega)
  rw [show a1 + ((p1 - a1).toNat : ℤ) = p1 by omega] at h1
  rw [show a2 + ((p2 - a2).toNat : ℤ) = p2 by omega] at h2
  exact h1.trans h2

end PF12



/-! L5b: a crossing-free arc drawing gives a grid model (disjoint connected blobs of cells,
adjacent along every edge). Needs L4 (gAdj, BlobRel) and L5a. -/

namespace PF12

open Finset

lemma pos_bound {X : Type} [TopologicalSpace X] [CompactSpace X] {F : X → ℝ} (hF : Continuous F)
    {S : Set X} (hS : IsClosed S) (hpos : ∀ x ∈ S, 0 < F x) : ∃ c > 0, ∀ x ∈ S, c ≤ F x := by
  rcases S.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, one_pos, by simp [hE]⟩
  · obtain ⟨x0, hx0, hmin⟩ := hS.isCompact.exists_isMinOn hne hF.continuousOn
    exact ⟨F x0, hpos x0 hx0, fun x hx => isMinOn_iff.mp hmin x hx⟩

lemma fin_min {ι : Type} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ c > 0, ∀ i, c ≤ f i := by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  | inr _ =>
    obtain ⟨i0, hi0⟩ := Finite.exists_min f
    exact ⟨f i0, hf i0, hi0⟩

lemma split_exists {α : Type} (p : α → Prop) : ∀ (S : List α), (∃ x ∈ S, p x) →
    ∃ V W : List α, ∃ d : α, S = V ++ W ∧ V.getLast? = some d ∧ p d ∧ ∀ x ∈ W, ¬ p x := by
  intro S
  induction S with
  | nil => intro h; simp at h
  | cons a S ih =>
    intro hex
    by_cases h : ∃ x ∈ S, p x
    · obtain ⟨V, W, d, hS, hl, hd, hW⟩ := ih h
      refine ⟨a :: V, W, d, by rw [hS]; rfl, ?_, hd, hW⟩
      simp [List.getLast?_cons, hl]
    · push Not at h
      have ha : p a := by
        obtain ⟨x, hx, hpx⟩ := hex
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hpx
        · exact absurd hpx (h x hx)
      exact ⟨[a], S, a, rfl, rfl, ha, h⟩

lemma mem_of_head?' {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons b l => simp at h; subst h; simp

lemma mem_of_getLast?' {α : Type} {l : List α} {a : α} (h : l.getLast? = some a) : a ∈ l :=
  List.mem_of_getLast? h

lemma corner_dist_le {h : ℝ} (hh : 0 < h) (c c' : ℤ × ℤ) (k : ℤ) (h1 : |c.1 - c'.1| ≤ k)
    (h2 : |c.2 - c'.2| ≤ k) : dist (corner h c) (corner h c') ≤ k * h := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  simp only [corner]
  rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_pos hh]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hh.le
    have : ((|c.1 - c'.1| : ℤ) : ℝ) ≤ k := by exact_mod_cast h1
    simpa [Int.cast_abs, Int.cast_sub] using this
  · apply mul_le_mul_of_nonneg_right _ hh.le
    have : ((|c.2 - c'.2| : ℤ) : ℝ) ≤ k := by exact_mod_cast h2
    simpa [Int.cast_abs, Int.cast_sub] using this

lemma corner_dist_ge {h : ℝ} (hh : 0 < h) (c c' : ℤ × ℤ) (k : ℤ)
    (hk : k ≤ |c.1 - c'.1| ∨ k ≤ |c.2 - c'.2|) : k * h ≤ dist (corner h c) (corner h c') := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [corner]
  rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_pos hh]
  rcases hk with hk | hk
  · refine le_trans ?_ (le_max_left _ _)
    apply mul_le_mul_of_nonneg_right _ hh.le
    have : (k : ℝ) ≤ ((|c.1 - c'.1| : ℤ) : ℝ) := by exact_mod_cast hk
    simpa [Int.cast_abs, Int.cast_sub] using this
  · refine le_trans ?_ (le_max_right _ _)
    apply mul_le_mul_of_nonneg_right _ hh.le
    have : (k : ℝ) ≤ ((|c.2 - c'.2| : ℤ) : ℝ) := by exact_mod_cast hk
    simpa [Int.cast_abs, Int.cast_sub] using this

open RobertsonSeymour1986.GM5 in
/-- L5: a plane drawing gives a grid model -/
theorem model_of_drawing {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : PlaneDrawing G) :
    ∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (BlobRel (B v)) p q) ∧
      (∀ v, (B v).Nonempty) ∧ (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, gAdj p q) := by
  classical
  -- orientation of the edges
  have hout : ∀ e : G.edgeSet, ∃ vw : V × V, s(vw.1, vw.2) = (e : Sym2 V) := fun e =>
    ⟨(e : Sym2 V).out, Quot.out_eq _⟩
  choose vw hvw using hout
  have hA : ∀ e : G.edgeSet, G.Adj (vw e).1 (vw e).2 := by
    intro e; have := e.2; rw [← hvw e] at this; exact this
  have hab : ∀ e : G.edgeSet, (vw e).1 ≠ (vw e).2 := fun e => G.ne_of_adj (hA e)
  have hPinj : ∀ v w, D.vertex v = D.vertex w → v = w := fun v w h => D.vertex_injective h
  let γ : ∀ e : G.edgeSet, Path (D.vertex (vw e).1) (D.vertex (vw e).2) := fun e => D.arc (hA e)
  have hγ0 : ∀ e, γ e 0 = D.vertex (vw e).1 := fun e => (γ e).source
  have hγ1 : ∀ e, γ e 1 = D.vertex (vw e).2 := fun e => (γ e).target
  have hγinj : ∀ e, Function.Injective (γ e) := fun e => D.arc_injective (hA e)
  have hγcont : ∀ e, Continuous (γ e) := fun e => (γ e).continuous
  have hmeet : ∀ e f s t, e ≠ f → γ e s = γ f t → (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) := by
    intro e f s t hef h
    rcases D.arcs_meet_only_at_endpoints (hA e) (hA f) s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
    · exact absurd (Subtype.ext (by rw [← hvw e, ← hvw f, h1, h2])) hef
    · exact absurd (Subtype.ext (by rw [← hvw e, ← hvw f, h1, h2, Sym2.eq_swap])) hef
    · exact h3
  have havoid : ∀ e t x, γ e t = D.vertex x → x = (vw e).1 ∨ x = (vw e).2 := fun e t x h =>
    D.arc_avoids_vertices (hA e) t x h
  -- vertex separation
  obtain ⟨R0, hR0, hR0b⟩ : ∃ R0 > 0, ∀ v w, v ≠ w → 4 * R0 ≤ dist (D.vertex v) (D.vertex w) := by
    obtain ⟨c, hc, hcb⟩ := fin_min (ι := {p : V × V // p.1 ≠ p.2})
      (fun p => dist (D.vertex p.1.1) (D.vertex p.1.2))
      (fun p => dist_pos.mpr (fun h => p.2 (hPinj _ _ h)))
    exact ⟨c / 4, by positivity, fun v w h => by have := hcb ⟨(v, w), h⟩; simp only at this; linarith⟩
  -- the part of each arc near its tail ends at a parameter τ e < 1
  have hτ : ∀ e, ∃ τ : unitInterval, τ < 1 ∧
      ∀ t, dist (γ e t) (D.vertex (vw e).1) ≤ R0 → t ≤ τ := by
    intro e
    have hTc : IsClosed {t : unitInterval | dist (γ e t) (D.vertex (vw e).1) ≤ R0} :=
      isClosed_le ((hγcont e).dist continuous_const) continuous_const
    have hTne : ({t : unitInterval | dist (γ e t) (D.vertex (vw e).1) ≤ R0}).Nonempty :=
      ⟨0, by simp only [Set.mem_setOf_eq, hγ0, dist_self]; exact hR0.le⟩
    obtain ⟨τ, hτT, hmax⟩ := hTc.isCompact.exists_isMaxOn hTne continuous_id.continuousOn
    refine ⟨τ, ?_, fun t ht => isMaxOn_iff.mp hmax t ht⟩
    refine lt_of_le_of_ne unitInterval.le_one' ?_
    intro h1
    rw [h1] at hτT
    simp only [Set.mem_setOf_eq, hγ1] at hτT
    have := hR0b _ _ (hab e).symm
    linarith
  choose τ hτ1 hτ2 using hτ
  -- ρ: vertices are far from arcs not incident to them, heads are far from tail parts
  have hc2 : ∀ ve : V × G.edgeSet, ∃ c > 0, ve.1 ≠ (vw ve.2).1 → ve.1 ≠ (vw ve.2).2 →
      ∀ t, c ≤ dist (D.vertex ve.1) (γ ve.2 t) := by
    rintro ⟨v, e⟩
    by_cases hv : v ≠ (vw e).1 ∧ v ≠ (vw e).2
    · obtain ⟨c, hc, hb⟩ := pos_bound (F := fun t => dist (D.vertex v) (γ e t))
        (continuous_const.dist (hγcont e)) isClosed_univ (fun t _ => dist_pos.mpr (fun h => by
          rcases havoid e t v h.symm with h' | h'
          · exact hv.1 h'
          · exact hv.2 h'))
      exact ⟨c, hc, fun _ _ t => hb t (Set.mem_univ _)⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
  choose c2 hc2pos hc2 using hc2
  obtain ⟨ρ2, hρ2, hρ2b⟩ := fin_min c2 hc2pos
  have hc3 : ∀ e : G.edgeSet, ∃ c > 0, ∀ t, t ≤ τ e → c ≤ dist (D.vertex (vw e).2) (γ e t) := by
    intro e
    obtain ⟨c, hc, hb⟩ := pos_bound (F := fun t => dist (D.vertex (vw e).2) (γ e t))
      (S := {t | t ≤ τ e}) (continuous_const.dist (hγcont e))
      (isClosed_le continuous_id continuous_const) (fun t ht => dist_pos.mpr (fun h => by
        have h' : γ e 1 = γ e t := (hγ1 e).trans h
        have h1t := hγinj e h'
        simp only [Set.mem_setOf_eq] at ht
        rw [← h1t] at ht
        exact absurd (lt_of_le_of_lt ht (hτ1 e)) (lt_irrefl _)))
    exact ⟨c, hc, fun t ht => hb t ht⟩
  choose c3 hc3pos hc3 using hc3
  obtain ⟨ρ3, hρ3, hρ3b⟩ := fin_min c3 hc3pos
  obtain ⟨ρ, hρ, hρR, hρ2', hρ3'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 4 * ρ ≤ R0 ∧ 2 * ρ ≤ ρ2 ∧ 2 * ρ ≤ ρ3 :=
    ⟨min (R0 / 4) (min ρ2 ρ3 / 2), by positivity,
      by have := min_le_left (R0 / 4) (min ρ2 ρ3 / 2); linarith,
      by have := min_le_right (R0 / 4) (min ρ2 ρ3 / 2); have := min_le_left ρ2 ρ3; linarith,
      by have := min_le_right (R0 / 4) (min ρ2 ρ3 / 2); have := min_le_right ρ2 ρ3; linarith⟩
  -- separation of the pieces of different arcs
  have hsep : ∀ ef : G.edgeSet × G.edgeSet, ∃ c > 0,
      ((vw ef.1).1 ≠ (vw ef.2).1 → ∀ s t, s ≤ τ ef.1 → t ≤ τ ef.2 →
        c ≤ dist (γ ef.1 s) (γ ef.2 t)) ∧
      (ef.1 ≠ ef.2 → (vw ef.1).1 ≠ (vw ef.2).2 → ∀ s t, s ≤ τ ef.1 →
        ρ / 4 ≤ dist (γ ef.2 t) (D.vertex (vw ef.2).1) → c ≤ dist (γ ef.1 s) (γ ef.2 t)) ∧
      ((vw ef.1).2 ≠ (vw ef.2).2 → ∀ s t, ρ / 4 ≤ dist (γ ef.1 s) (D.vertex (vw ef.1).1) →
        ρ / 4 ≤ dist (γ ef.2 t) (D.vertex (vw ef.2).1) → c ≤ dist (γ ef.1 s) (γ ef.2 t)) := by
    rintro ⟨e, f⟩
    have hF : Continuous (fun st : unitInterval × unitInterval => dist (γ e st.1) (γ f st.2)) :=
      ((hγcont e).comp continuous_fst).dist ((hγcont f).comp continuous_snd)
    have s0 : ∀ s : unitInterval, s ≤ τ e → (s = 0 ∨ s = 1) → s = 0 := by
      intro s hs h
      rcases h with h | h
      · exact h
      · rw [h] at hs; exact absurd (lt_of_le_of_lt hs (hτ1 e)) (lt_irrefl _)
    have b4 : ∃ c > 0, (vw e).1 ≠ (vw f).1 → ∀ s t, s ≤ τ e → t ≤ τ f →
        c ≤ dist (γ e s) (γ f t) := by
      by_cases hc : (vw e).1 ≠ (vw f).1
      · obtain ⟨c, hc0, hb⟩ := pos_bound hF
          (S := {st | st.1 ≤ τ e} ∩ {st | st.2 ≤ τ f})
          ((isClosed_le continuous_fst continuous_const).inter
            (isClosed_le continuous_snd continuous_const)) (by
          rintro ⟨s, t⟩ ⟨hs, ht⟩
          apply dist_pos.mpr
          intro h
          simp only [Set.mem_setOf_eq] at hs ht
          by_cases hef : e = f
          · subst hef; exact hc rfl
          · obtain ⟨hs', ht'⟩ := hmeet e f s t hef h
            have ht0 : t = 0 := by
              rcases ht' with h0 | h1
              · exact h0
              · rw [h1] at ht; exact absurd (lt_of_le_of_lt ht (hτ1 f)) (lt_irrefl _)
            rw [s0 s hs hs', ht0, hγ0, hγ0] at h
            exact hc (hPinj _ _ h))
        exact ⟨c, hc0, fun _ s t hs ht => hb (s, t) ⟨hs, ht⟩⟩
      · exact ⟨1, one_pos, fun h => absurd h hc⟩
    have b5 : ∃ c > 0, e ≠ f → (vw e).1 ≠ (vw f).2 → ∀ s t, s ≤ τ e →
        ρ / 4 ≤ dist (γ f t) (D.vertex (vw f).1) → c ≤ dist (γ e s) (γ f t) := by
      by_cases hc : e ≠ f ∧ (vw e).1 ≠ (vw f).2
      · obtain ⟨c, hc0, hb⟩ := pos_bound hF
          (S := {st | st.1 ≤ τ e} ∩ {st | ρ / 4 ≤ dist (γ f st.2) (D.vertex (vw f).1)})
          ((isClosed_le continuous_fst continuous_const).inter
            (isClosed_le continuous_const (((hγcont f).comp continuous_snd).dist continuous_const)))
          (by
          rintro ⟨s, t⟩ ⟨hs, ht⟩
          apply dist_pos.mpr
          intro h
          simp only [Set.mem_setOf_eq] at hs ht
          obtain ⟨hs', ht'⟩ := hmeet e f s t hc.1 h
          rw [s0 s hs hs', hγ0] at h
          rcases ht' with h0 | h1
          · rw [h0, hγ0] at ht; rw [dist_self] at ht; linarith
          · rw [h1, hγ1] at h; exact hc.2 (hPinj _ _ h))
        exact ⟨c, hc0, fun h1 h2 s t hs ht => hb (s, t) ⟨hs, ht⟩⟩
      · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
    have b6 : ∃ c > 0, (vw e).2 ≠ (vw f).2 → ∀ s t,
        ρ / 4 ≤ dist (γ e s) (D.vertex (vw e).1) →
        ρ / 4 ≤ dist (γ f t) (D.vertex (vw f).1) → c ≤ dist (γ e s) (γ f t) := by
      by_cases hc : (vw e).2 ≠ (vw f).2
      · obtain ⟨c, hc0, hb⟩ := pos_bound hF
          (S := {st | ρ / 4 ≤ dist (γ e st.1) (D.vertex (vw e).1)} ∩
            {st | ρ / 4 ≤ dist (γ f st.2) (D.vertex (vw f).1)})
          ((isClosed_le continuous_const (((hγcont e).comp continuous_fst).dist continuous_const)).inter
            (isClosed_le continuous_const (((hγcont f).comp continuous_snd).dist continuous_const)))
          (by
          rintro ⟨s, t⟩ ⟨hs, ht⟩
          apply dist_pos.mpr
          intro h
          simp only [Set.mem_setOf_eq] at hs ht
          have hef : e ≠ f := by intro hef; subst hef; exact hc rfl
          obtain ⟨hs', ht'⟩ := hmeet e f s t hef h
          rcases hs' with hs0 | hs1
          · rw [hs0, hγ0, dist_self] at hs; linarith
          · rcases ht' with ht0 | ht1
            · rw [ht0, hγ0, dist_self] at ht; linarith
            · rw [hs1, ht1, hγ1, hγ1] at h; exact hc (hPinj _ _ h))
        exact ⟨c, hc0, fun _ s t hs ht => hb (s, t) ⟨hs, ht⟩⟩
      · exact ⟨1, one_pos, fun h => absurd h hc⟩
    obtain ⟨c4, h4, h4b⟩ := b4
    obtain ⟨c5, h5, h5b⟩ := b5
    obtain ⟨c6, h6, h6b⟩ := b6
    refine ⟨min c4 (min c5 c6), by positivity, ?_, ?_, ?_⟩
    · intro hne s t hs ht
      exact le_trans (min_le_left _ _) (h4b hne s t hs ht)
    · intro hne hne' s t hs ht
      exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (h5b hne hne' s t hs ht)
    · intro hne s t hs ht
      exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (h6b hne s t hs ht)
  choose csep hcsep hsep4 hsep5 hsep6 using hsep
  obtain ⟨δ, hδ, hδb⟩ := fin_min csep hcsep
  -- the mesh
  obtain ⟨h, hh, hhρ, hhδ⟩ : ∃ h : ℝ, 0 < h ∧ 12 * h ≤ ρ ∧ 8 * h ≤ δ :=
    ⟨min (ρ / 12) (δ / 8), by positivity,
      by have := min_le_left (ρ / 12) (δ / 8); linarith,
      by have := min_le_right (ρ / 12) (δ / 8); linarith⟩
  set m : ℤ := ⌊ρ / (2 * h)⌋ with hm
  have hm1 : (m : ℝ) * h ≤ ρ / 2 := by
    have := Int.floor_le (ρ / (2 * h))
    rw [← hm] at this
    have e : ρ / (2 * h) * h = ρ / 2 := by field_simp
    nlinarith
  have hm2 : ρ / 2 < ((m + 1 : ℤ) : ℝ) * h := by
    have := Int.lt_floor_add_one (ρ / (2 * h))
    rw [← hm] at this
    have e : ρ / (2 * h) * h = ρ / 2 := by field_simp
    push_cast
    nlinarith
  let cv : V → ℤ × ℤ := fun v => cellOf h (D.vertex v)
  let A : V → Finset (ℤ × ℤ) := fun v =>
    Icc ((cv v).1 - m) ((cv v).1 + m) ×ˢ Icc ((cv v).2 - m) ((cv v).2 + m)
  have hm0 : 0 ≤ m := by
    rw [hm]; apply Int.floor_nonneg.mpr; positivity
  have hcvA : ∀ v, cv v ∈ A v := by
    intro v
    simp only [A, Finset.mem_product, Finset.mem_Icc]
    omega
  have FA1 : ∀ v c, c ∈ A v → dist (corner h c) (D.vertex v) < ρ / 2 + h := by
    intro v c hc
    simp only [A, Finset.mem_product, Finset.mem_Icc] at hc
    have h1 := corner_dist_le hh c (cv v) m (by rw [abs_le]; omega) (by rw [abs_le]; omega)
    have h2 : dist (corner h (cv v)) (D.vertex v) < h := dist_corner_cellOf hh _
    calc dist (corner h c) (D.vertex v) ≤ dist (corner h c) (corner h (cv v)) +
          dist (corner h (cv v)) (D.vertex v) := dist_triangle _ _ _
      _ < ρ / 2 + h := by linarith
  have FA2 : ∀ v c, c ∉ A v → ρ / 2 - h < dist (corner h c) (D.vertex v) := by
    intro v c hc
    simp only [A, Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hc
    have h1 := corner_dist_ge hh c (cv v) (m + 1) (by
      rcases hc with (h | h) | (h | h)
      · left; rw [le_abs]; omega
      · left; rw [le_abs]; omega
      · right; rw [le_abs]; omega
      · right; rw [le_abs]; omega)
    have h2 : dist (corner h (cv v)) (D.vertex v) < h := dist_corner_cellOf hh _
    have h3 := dist_triangle (corner h c) (D.vertex v) (corner h (cv v))
    have h4 := dist_comm (D.vertex v) (corner h (cv v))
    linarith
  -- cell paths along the arcs
  have hwalk : ∀ e : G.edgeSet, ∃ S : List (ℤ × ℤ), S.Nodup ∧ List.IsChain gridG.Adj S ∧
      S.head? = some (cv (vw e).1) ∧ S.getLast? = some (cv (vw e).2) ∧
      (∀ c ∈ S, ∃ t, dist (corner h c) (γ e t) < 2 * h) ∧
      S.Pairwise (fun a b => ∃ ta tb : unitInterval, ta ≤ tb ∧
        dist (corner h a) (γ e ta) < 2 * h ∧ dist (corner h b) (γ e tb) < 2 * h) := by
    intro e
    obtain ⟨w, hwn, hwp⟩ := arc_walk (γ e) hh
    refine ⟨w.bypass.support, (w.bypass_isPath).support_nodup, w.bypass.isChain_adj_support,
      ?_, ?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.support_eq_cons]; rfl
    · rw [List.getLast?_eq_getLast (SimpleGraph.Walk.support_ne_nil _),
        SimpleGraph.Walk.getLast_support]
    · intro c hc; exact hwn c (w.support_bypass_subset_support hc)
    · exact hwp.sublist w.support_bypass_sublist_support
  choose S hSnd hSch hSh hSl hSn hSp using hwalk
  have hsplit : ∀ e, ∃ Vp Wp : List (ℤ × ℤ), ∃ d, S e = Vp ++ Wp ∧ Vp.getLast? = some d ∧
      d ∈ A (vw e).1 ∧ ∀ x ∈ Wp, x ∉ A (vw e).1 :=
    fun e => split_exists _ (S e) ⟨cv (vw e).1, mem_of_head?' (hSh e), hcvA _⟩
  choose Vp Wp d hSeq hdl hdA hWA using hsplit
  have hVne : ∀ e, Vp e ≠ [] := by intro e h; have := hdl e; rw [h] at this; simp at this
  -- the head cell is not in the tail box
  have hcvbA : ∀ e, cv (vw e).2 ∉ A (vw e).1 := by
    intro e hc
    have h1 := FA1 _ _ hc
    have h2 : dist (corner h (cv (vw e).2)) (D.vertex (vw e).2) < h := dist_corner_cellOf hh _
    have h3 := hR0b _ _ (hab e)
    have h4 := dist_triangle (D.vertex (vw e).1) (corner h (cv (vw e).2)) (D.vertex (vw e).2)
    have h5 := dist_comm (D.vertex (vw e).1) (corner h (cv (vw e).2))
    linarith
  have hWne : ∀ e, Wp e ≠ [] := by
    intro e h
    have hl := hSl e
    rw [hSeq e, h, List.append_nil, hdl e] at hl
    simp only [Option.some.injEq] at hl
    exact hcvbA e (hl ▸ hdA e)
  have hVhead : ∀ e, (Vp e).head? = some (cv (vw e).1) := by
    intro e
    have := hSh e
    rw [hSeq e, List.head?_append_of_ne_nil _ (hVne e)] at this
    exact this
  have hWlast : ∀ e, (Wp e).getLast? = some (cv (vw e).2) := by
    intro e
    have := hSl e
    rw [hSeq e, List.getLast?_append_of_ne_nil _ (hWne e)] at this
    exact this
  -- witnesses
  have WV : ∀ e c, c ∈ Vp e → ∃ t, t ≤ τ e ∧ dist (corner h c) (γ e t) < 2 * h := by
    intro e c hc
    have hpair := hSp e
    rw [hSeq e, List.pairwise_append] at hpair
    have hVd := List.dropLast_append_getLast? (d e) (hdl e)
    have hdS : d e ∈ S e := by rw [hSeq e]; exact List.mem_append_left _ (mem_of_getLast?' (hdl e))
    have hdτ : ∀ t, dist (corner h (d e)) (γ e t) < 2 * h → t ≤ τ e := by
      intro t ht
      apply hτ2
      have h1 := FA1 _ _ (hdA e)
      have h2 := dist_triangle (γ e t) (corner h (d e)) (D.vertex (vw e).1)
      have h3 := dist_comm (γ e t) (corner h (d e))
      linarith
    by_cases hcd : c = d e
    · obtain ⟨t, ht⟩ := hSn e (d e) hdS
      subst hcd
      exact ⟨t, hdτ t ht, ht⟩
    · have hc' : c ∈ (Vp e).dropLast := by
        rw [← hVd, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · exact hc
        · exact absurd hc hcd
      have hp1 := hpair.1
      rw [← hVd, List.pairwise_append] at hp1
      obtain ⟨tc, td, htcd, hc1, hd1⟩ := hp1.2.2 c hc' (d e) (List.mem_singleton_self _)
      exact ⟨tc, le_trans htcd (hdτ td hd1), hc1⟩
  have WW : ∀ e c, c ∈ Wp e → ∃ t, ρ / 4 ≤ dist (γ e t) (D.vertex (vw e).1) ∧
      dist (corner h c) (γ e t) < 2 * h := by
    intro e c hc
    have hcS : c ∈ S e := by rw [hSeq e]; exact List.mem_append_right _ hc
    obtain ⟨t, ht⟩ := hSn e c hcS
    refine ⟨t, ?_, ht⟩
    have h1 := FA2 _ _ (hWA e c hc)
    have h2 := dist_triangle (corner h c) (γ e t) (D.vertex (vw e).1)
    linarith
  have hVW : ∀ e c, c ∈ Vp e → c ∈ Wp e → False := by
    intro e c h1 h2
    have hnd := hSnd e
    rw [hSeq e] at hnd
    exact List.disjoint_of_nodup_append hnd h1 h2
  -- blobs
  let B : V → Finset (ℤ × ℤ) := fun v =>
    A v ∪ (univ.filter (fun e => (vw e).1 = v)).biUnion (fun e => (Vp e).toFinset) ∪
      (univ.filter (fun e => (vw e).2 = v)).biUnion (fun e => (Wp e).toFinset)
  have hmemB : ∀ v c, c ∈ B v ↔ c ∈ A v ∨ (∃ e, (vw e).1 = v ∧ c ∈ Vp e) ∨
      (∃ e, (vw e).2 = v ∧ c ∈ Wp e) := by
    intro v c
    simp only [B, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, List.mem_toFinset, or_assoc]
  -- separation facts
  have hAA : ∀ v x c, v ≠ x → c ∈ A v → c ∈ A x → False := by
    intro v x c hvx h1 h2
    have a1 := FA1 _ _ h1
    have a2 := FA1 _ _ h2
    have a3 := hR0b _ _ hvx
    have a4 := dist_triangle (D.vertex v) (corner h c) (D.vertex x)
    have a5 := dist_comm (D.vertex v) (corner h c)
    linarith
  have hAarc : ∀ v f c t, c ∈ A v → dist (corner h c) (γ f t) < 2 * h →
      dist (D.vertex v) (γ f t) < ρ := by
    intro v f c t h1 h2
    have a1 := FA1 _ _ h1
    have a4 := dist_triangle (D.vertex v) (corner h c) (γ f t)
    have a5 := dist_comm (D.vertex v) (corner h c)
    linarith
  have hAV : ∀ v f c, c ∈ A v → v ≠ (vw f).1 → c ∈ Vp f → False := by
    intro v f c h1 hv h2
    obtain ⟨t, ht, hd⟩ := WV f c h2
    have a1 := hAarc v f c t h1 hd
    by_cases hv2 : v = (vw f).2
    · have := hc3 f t ht; have := hρ3b f; rw [hv2] at a1; linarith
    · have := hc2 (v, f) hv hv2 t; have := hρ2b (v, f); linarith
  have hAW : ∀ v f c, c ∈ A v → v ≠ (vw f).2 → c ∈ Wp f → False := by
    intro v f c h1 hv h2
    by_cases hv1 : v = (vw f).1
    · subst hv1; exact hWA f c h2 h1
    · obtain ⟨t, _, hd⟩ := WW f c h2
      have a1 := hAarc v f c t h1 hd
      have := hc2 (v, f) hv1 hv t; have := hρ2b (v, f); linarith
  have harcarc : ∀ e f c s t, dist (corner h c) (γ e s) < 2 * h →
      dist (corner h c) (γ f t) < 2 * h → dist (γ e s) (γ f t) < δ := by
    intro e f c s t h1 h2
    have a4 := dist_triangle (γ e s) (corner h c) (γ f t)
    have a5 := dist_comm (γ e s) (corner h c)
    linarith
  have hVV : ∀ e f c, (vw e).1 ≠ (vw f).1 → c ∈ Vp e → c ∈ Vp f → False := by
    intro e f c hne h1 h2
    obtain ⟨s, hs, hd1⟩ := WV e c h1
    obtain ⟨t, ht, hd2⟩ := WV f c h2
    have := hsep4 (e, f) hne s t hs ht
    have := hδb (e, f)
    have := harcarc e f c s t hd1 hd2
    linarith
  have hVW' : ∀ e f c, (vw e).1 ≠ (vw f).2 → c ∈ Vp e → c ∈ Wp f → False := by
    intro e f c hne h1 h2
    by_cases hef : e = f
    · subst hef; exact hVW e c h1 h2
    · obtain ⟨s, hs, hd1⟩ := WV e c h1
      obtain ⟨t, ht, hd2⟩ := WW f c h2
      have := hsep5 (e, f) hef hne s t hs ht
      have := hδb (e, f)
      have := harcarc e f c s t hd1 hd2
      linarith
  have hWW' : ∀ e f c, (vw e).2 ≠ (vw f).2 → c ∈ Wp e → c ∈ Wp f → False := by
    intro e f c hne h1 h2
    obtain ⟨s, hs, hd1⟩ := WW e c h1
    obtain ⟨t, ht, hd2⟩ := WW f c h2
    have := hsep6 (e, f) hne s t hs ht
    have := hδb (e, f)
    have := harcarc e f c s t hd1 hd2
    linarith
  -- connectivity from the centre cell
  have hreach : ∀ v c, c ∈ B v → Relation.ReflTransGen (BlobRel (B v)) (cv v) c := by
    intro v c hc
    have hAB : A v ⊆ B v := fun x hx => (hmemB v x).mpr (Or.inl hx)
    rcases (hmemB v c).mp hc with hc | ⟨e, he, hc⟩ | ⟨e, he, hc⟩
    · -- box
      have hbox : ∀ x : ℤ × ℤ, (cv v).1 - m ≤ x.1 → x.1 ≤ (cv v).1 + m → (cv v).2 - m ≤ x.2 →
          x.2 ≤ (cv v).2 + m → x ∈ A v := by
        intro x h1 h2 h3 h4
        simp only [A, Finset.mem_product, Finset.mem_Icc]; omega
      have r1 := box_reach (A v) _ _ _ _ hbox (cv v) (by omega)
      have r2 := box_reach (A v) _ _ _ _ hbox c (by
        simp only [A, Finset.mem_product, Finset.mem_Icc] at hc; omega)
      exact reach_mono hAB ((reach_symm r1).trans r2)
    · -- tail part of an arc leaving v
      have hch : List.IsChain gridG.Adj (Vp e) := by
        have := hSch e; rw [hSeq e, List.isChain_append] at this; exact this.1
      obtain ⟨hd, tl, htl⟩ : ∃ hd tl, Vp e = hd :: tl := List.exists_cons_of_ne_nil (hVne e)
      have hhd : hd = cv v := by
        have := hVhead e; rw [htl, he] at this; simpa using this
      rw [htl] at hch hc
      have hsub : ∀ x ∈ hd :: tl, x ∈ B v := by
        intro x hx; rw [← htl] at hx; exact (hmemB v x).mpr (Or.inr (Or.inl ⟨e, he, hx⟩))
      rw [← hhd]; exact chain_reach (B v) hd tl hch hsub c hc
    · -- head part of an arc entering v
      have hch : List.IsChain gridG.Adj (Wp e).reverse := by
        have := hSch e; rw [hSeq e, List.isChain_append] at this
        rw [List.isChain_reverse]
        exact this.2.1.imp (fun a b hab => (show gridG.Adj a b from hab).symm)
      obtain ⟨hd, tl, htl⟩ : ∃ hd tl, (Wp e).reverse = hd :: tl :=
        List.exists_cons_of_ne_nil (by simpa using hWne e)
      have hhd : hd = cv v := by
        have := hWlast e
        rw [← List.head?_reverse, htl, he] at this; simpa using this
      have hc' : c ∈ hd :: tl := by rw [← htl, List.mem_reverse]; exact hc
      rw [htl] at hch
      have hsub : ∀ x ∈ hd :: tl, x ∈ B v := by
        intro x hx; rw [← htl, List.mem_reverse] at hx
        exact (hmemB v x).mpr (Or.inr (Or.inr ⟨e, he, hx⟩))
      rw [← hhd]; exact chain_reach (B v) hd tl hch hsub c hc'
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · -- disjointness
    intro v x hvx
    rw [Finset.disjoint_left]
    intro c h1 h2
    rcases (hmemB v c).mp h1 with c1 | ⟨e, he, c1⟩ | ⟨e, he, c1⟩ <;>
      rcases (hmemB x c).mp h2 with c2 | ⟨f, hf, c2⟩ | ⟨f, hf, c2⟩
    · exact hAA v x c hvx c1 c2
    · exact hAV v f c c1 (by rw [hf]; exact hvx) c2
    · exact hAW v f c c1 (by rw [hf]; exact hvx) c2
    · exact hAV x e c c2 (by rw [he]; exact Ne.symm hvx) c1
    · exact hVV e f c (by rw [he, hf]; exact hvx) c1 c2
    · exact hVW' e f c (by rw [he, hf]; exact hvx) c1 c2
    · exact hAW x e c c2 (by rw [he]; exact Ne.symm hvx) c1
    · exact hVW' f e c (by rw [he, hf]; exact Ne.symm hvx) c2 c1
    · exact hWW' e f c (by rw [he, hf]; exact hvx) c1 c2
  · intro v p hp q hq
    exact (reach_symm (hreach v p hp)).trans (hreach v q hq)
  · intro v; exact ⟨cv v, (hmemB v _).mpr (Or.inl (hcvA v))⟩
  · intro v w hvw'
    let e : G.edgeSet := ⟨s(v, w), hvw'⟩
    have hch := hSch e
    rw [hSeq e, List.isChain_append] at hch
    obtain ⟨y, hy⟩ : ∃ y, (Wp e).head? = some y := by
      cases hW : Wp e with
      | nil => exact absurd hW (hWne e)
      | cons y _ => exact ⟨y, rfl⟩
    have hadjdy : gridG.Adj (d e) y := hch.2.2 (d e) (hdl e) y hy
    have hdB : d e ∈ B (vw e).1 :=
      (hmemB _ _).mpr (Or.inr (Or.inl ⟨e, rfl, mem_of_getLast?' (hdl e)⟩))
    have hyB : y ∈ B (vw e).2 :=
      (hmemB _ _).mpr (Or.inr (Or.inr ⟨e, rfl, mem_of_head?' hy⟩))
    have hs := hvw e
    simp only [e, Sym2.eq_iff] at hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hdB; rw [h2] at hyB
      exact ⟨d e, hdB, y, hyB, hadjdy⟩
    · rw [h2] at hyB; rw [h1] at hdB
      exact ⟨y, hyB, d e, hdB, hadjdy.symm⟩

end PF12



/-! L6: assembly. -/

namespace PF12

open Finset

lemma box_bound {V : Type} [Fintype V] (B : V → Finset (ℤ × ℤ)) :
    ∃ M : ℤ, ∀ v, ∀ p ∈ B v, InBox M p := by
  refine ⟨∑ v, ∑ q ∈ B v, (|q.1| + |q.2|), fun v p hp => ?_⟩
  have h1 : |p.1| + |p.2| ≤ ∑ q ∈ B v, (|q.1| + |q.2|) :=
    Finset.single_le_sum (f := fun q : ℤ × ℤ => |q.1| + |q.2|)
      (fun q _ => by positivity) hp
  have h2 : ∑ q ∈ B v, (|q.1| + |q.2|) ≤ ∑ v, ∑ q ∈ B v, (|q.1| + |q.2|) :=
    Finset.single_le_sum (f := fun v => ∑ q ∈ B v, (|q.1| + |q.2|))
      (fun w _ => Finset.sum_nonneg (fun q _ => by positivity)) (Finset.mem_univ v)
  have a1 := abs_nonneg p.1
  have a2 := abs_nonneg p.2
  have b1 := neg_abs_le p.1
  have b2 := le_abs_self p.1
  have b3 := neg_abs_le p.2
  have b4 := le_abs_self p.2
  simp only [InBox]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma bounds_of_model {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (B : V → Finset (ℤ × ℤ))
    (hdisj : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hconn : ∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (BlobRel (B v)) p q)
    (hne : ∀ v, (B v).Nonempty)
    (hadj : ∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, gAdj p q) :
    Fintype.card G.edgeSet ≤ 3 * Fintype.card V - 6 ∧
      (G.Colorable 2 → Fintype.card G.edgeSet ≤ 2 * Fintype.card V - 4) := by
  obtain ⟨M, hM⟩ := box_bound B
  obtain ⟨s, h1, h2, h3⟩ := family_of_model G M B hM hdisj hconn hne hadj
  exact bound_of_twoSpanned G hn s h1 h2 h3

end PF12


/-! PQL5: combinatorial consequences of planarity for lemma_5 (planar treewidth-3 graphs, five queues).
Grid models (PF12.model_of_drawing) are closed under minors, so a planar graph has no K₃,₃ minor and
no K₅ minor. Plus the trivial glue facts used by the reduction of lemma_5. -/

namespace PQL5

open Finset

/-- A grid model of `G` induces a grid model of every minor `H` of `G` (union of the blobs of a
branch set). -/
theorem gridModel_of_minor {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (B : V → Finset (ℤ × ℤ)) (hdisj : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hconn : ∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (PF12.BlobRel (B v)) p q)
    (hne : ∀ v, (B v).Nonempty)
    (hadj : ∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, PF12.gAdj p q)
    (hm : RobertsonSeymour1986.GM5.IsMinor H G) :
    ∃ B' : W → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B' v) (B' w)) ∧
      (∀ v, ∀ p ∈ B' v, ∀ q ∈ B' v, Relation.ReflTransGen (PF12.BlobRel (B' v)) p q) ∧
      (∀ v, (B' v).Nonempty) ∧ (∀ v w, H.Adj v w → ∃ p ∈ B' v, ∃ q ∈ B' w, PF12.gAdj p q) := by
  classical
  obtain ⟨β, hβ, hpw, hβadj⟩ := hm
  obtain ⟨B', hB'⟩ : ∃ B' : W → Finset (ℤ × ℤ), ∀ w p, p ∈ B' w ↔ ∃ x ∈ β w, p ∈ B x :=
    ⟨fun w => (Finset.univ.filter (fun x => x ∈ β w)).biUnion B, fun w p => by
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have memB' : ∀ w x p, x ∈ β w → p ∈ B x → p ∈ B' w := fun w x p hx hp =>
    (hB' w p).2 ⟨x, hx, hp⟩
  refine ⟨B', ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨x, hx, hpx⟩ := (hB' a p).1 hpa
    obtain ⟨y, hy, hpy⟩ := (hB' b p).1 hpb
    have hxy : x ≠ y := by
      rintro rfl
      exact Set.disjoint_left.1 (hpw hab) hx hy
    exact Finset.disjoint_left.1 (hdisj x y hxy) hpx hpy
  · intro w
    have key : ∀ x0 u : β w, (G.induce (β w)).Reachable x0 u →
        ∀ p ∈ B x0.1, ∀ q ∈ B u.1, Relation.ReflTransGen (PF12.BlobRel (B' w)) p q := by
      intro x0 u hr
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      induction hr with
      | refl =>
        intro p hp q hq
        exact PF12.reach_mono (fun c hc => memB' w x0.1 c x0.2 hc) (hconn x0.1 p hp q hq)
      | @tail b c _ hbc ih =>
        intro p hp q hq
        have hbc' : G.Adj b.1 c.1 := by simpa using hbc
        obtain ⟨p1, hp1, q1, hq1, hg⟩ := hadj b.1 c.1 hbc'
        have h1 := ih p hp p1 hp1
        have h2 : PF12.BlobRel (B' w) p1 q1 :=
          ⟨memB' w b.1 p1 b.2 hp1, memB' w c.1 q1 c.2 hq1, hg⟩
        have h3 := PF12.reach_mono (fun d hd => memB' w c.1 d c.2 hd) (hconn c.1 q1 hq1 q hq)
        exact (h1.tail h2).trans h3
    intro p hp q hq
    obtain ⟨x, hx, hpx⟩ := (hB' w p).1 hp
    obtain ⟨y, hy, hqy⟩ := (hB' w q).1 hq
    exact key ⟨x, hx⟩ ⟨y, hy⟩ ((hβ w).2.preconnected _ _) p hpx q hqy
  · intro w
    obtain ⟨x, hx⟩ := (hβ w).1
    obtain ⟨p, hp⟩ := hne x
    exact ⟨p, memB' w x p hx hp⟩
  · intro a b hab
    obtain ⟨x, hx, y, hy, hxy⟩ := hβadj a b hab
    obtain ⟨p, hp, q, hq, hg⟩ := hadj x y hxy
    exact ⟨p, memB' a x p hx hp, q, memB' b y q hy hq, hg⟩

/-- Every minor of a planar graph has a grid model. -/
theorem gridModel_of_planar_minor {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hG : RobertsonSeymour1986.GM5.IsPlanar G)
    (hm : RobertsonSeymour1986.GM5.IsMinor H G) :
    ∃ B' : W → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B' v) (B' w)) ∧
      (∀ v, ∀ p ∈ B' v, ∀ q ∈ B' v, Relation.ReflTransGen (PF12.BlobRel (B' v)) p q) ∧
      (∀ v, (B' v).Nonempty) ∧ (∀ v w, H.Adj v w → ∃ p ∈ B' v, ∃ q ∈ B' w, PF12.gAdj p q) := by
  classical
  obtain ⟨D⟩ := hG
  obtain ⟨B, hdisj, hconn, hne, hadj⟩ := PF12.model_of_drawing G D
  exact gridModel_of_minor G H B hdisj hconn hne hadj hm

/-- A planar graph has no `K₃,₃` minor. -/
theorem planar_no_K33_minor {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RobertsonSeymour1986.GM5.IsPlanar G) :
    ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G := by
  classical
  intro hm
  let K := completeBipartiteGraph (Fin 3) (Fin 3)
  obtain ⟨B, hdisj, hconn, hne, hadj⟩ := gridModel_of_planar_minor G K hG hm
  have hb := PF12.bounds_of_model K (by simp) B hdisj hconn hne hadj
  have hcol : K.Colorable 2 :=
    ⟨SimpleGraph.Coloring.mk (fun u => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) u) (by
      intro u v h
      rcases u with u | u <;> rcases v with v | v <;> simp_all [K, completeBipartiteGraph])⟩
  have h8 := hb.2 hcol
  have h9 : 9 ≤ Fintype.card K.edgeSet := by
    have hinj : Function.Injective (fun ij : Fin 3 × Fin 3 =>
        (⟨s(Sum.inl ij.1, Sum.inr ij.2), by simp [K, completeBipartiteGraph]⟩ : K.edgeSet)) := by
      rintro ⟨i, j⟩ ⟨i', j'⟩ h
      simp only [Subtype.mk.injEq, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        and_false, or_false] at h
      rw [h.1, h.2]
    have := Fintype.card_le_of_injective _ hinj
    simpa using this
  have h6 : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  rw [h6] at h8
  omega

/-- A planar graph has no `K₅` minor. -/
theorem planar_no_K5_minor {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : RobertsonSeymour1986.GM5.IsPlanar G) :
    ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : SimpleGraph (Fin 5)) G := by
  classical
  intro hm
  obtain ⟨B, hdisj, hconn, hne, hadj⟩ := gridModel_of_planar_minor G (⊤ : SimpleGraph (Fin 5)) hG hm
  have hb := (PF12.bounds_of_model (⊤ : SimpleGraph (Fin 5)) (by simp) B hdisj hconn hne hadj).1
  rw [← SimpleGraph.edgeFinset_card, SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hb
  exact absurd hb (by decide)

/-- A copy of `H` inside `G` (injective adjacency-preserving map) is a minor. -/
theorem isMinor_of_embedding {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : H.Copy G) : RobertsonSeymour1986.GM5.IsMinor H G := by
  refine ⟨fun w => {f w}, fun w => ⟨Set.singleton_nonempty _, ?_⟩, ?_, ?_⟩
  · have : Unique ({f w} : Set V) := Set.uniqueSingleton (f w)
    exact ⟨SimpleGraph.Preconnected.of_subsingleton⟩
  · intro a b hab
    simp only [Set.disjoint_singleton]
    exact fun h => hab (f.injective h)
  · intro a b h
    exact ⟨f a, rfl, f b, rfl, f.toHom.map_adj h⟩

/-- Queue layouts restrict to subgraphs. -/
theorem hasQueueLayout_mono {V : Type} {G H : SimpleGraph V} (hle : G ≤ H) {k : ℕ}
    (hH : PlanarQueue.Planar.HasQueueLayout H k) : PlanarQueue.Planar.HasQueueLayout G k := by
  obtain ⟨ord, q, hinj, hq⟩ := hH
  refine ⟨ord, fun e => q ⟨e.1, SimpleGraph.edgeSet_mono hle e.2⟩, hinj, ?_⟩
  intro e f hef
  exact hq ⟨e.1, SimpleGraph.edgeSet_mono hle e.2⟩ ⟨f.1, SimpleGraph.edgeSet_mono hle f.2⟩ hef

/-- A graph on at most three vertices has a one-queue layout (nesting needs four vertices). -/
theorem hasQueueLayout_small {V : Type} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 3) (k : ℕ) (hk : 1 ≤ k) : PlanarQueue.Planar.HasQueueLayout G k := by
  classical
  let e := Fintype.equivFin V
  refine ⟨fun v => (e v : ℕ), fun _ => ⟨0, hk⟩, ?_, ?_⟩
  · intro a b h
    exact e.injective (Fin.ext h)
  · intro x y _ hn
    obtain ⟨a, b, c, d, _, hab, hbc, hcd⟩ := hn
    have h1 : (e a : ℕ) < e b := hab
    have h2 : (e b : ℕ) < e c := hbc
    have h3 : (e c : ℕ) < e d := hcd
    have := (e d).2
    omega

end PQL5

/-! Glue of lemma_5 from its two children (L5-A Kratochvil-Vaner completion, L5-B Alam et al.),
stated as hypotheses so the reduction is checked before the children are posted. -/

namespace PQL5

open PlanarQueue.Planar

/-- `H` is a 3-tree: tree-width at most 3 and edge-maximal with this property (DJMMUW p. 7). -/
def ThreeTreeStmt {V : Type} [DecidableEq V] (H : SimpleGraph V) : Prop :=
  RobertsonSeymour1986.GM5.TreewidthLE H 3 ∧ ∀ x y : V, x ≠ y → ¬ H.Adj x y → ¬ RobertsonSeymour1986.GM5.TreewidthLE (H ⊔ SimpleGraph.edge x y) 3

/-- Child L5-A (Kratochvil-Vaner, arXiv 1210.8113): planar partial 3-trees extend to planar 3-trees. -/
def ChildA : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), IsPlanar G → RobertsonSeymour1986.GM5.TreewidthLE G 3 →
    4 ≤ Fintype.card V → ∃ H : SimpleGraph V, G ≤ H ∧ IsPlanar H ∧ ThreeTreeStmt H

/-- Child L5-B (Alam-Bekos-Gronemann-Kaufmann-Pupyrev, arXiv 1808.10841, Thm 1). -/
def ChildB : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V), IsPlanar H → ThreeTreeStmt H →
    HasQueueLayout H 5

/-- Child L5-B2 (combinatorial core of L5-B): a 3-tree without a K₃,₃ subgraph has 5 queues.
L5-B = L5-B2 + planar_no_K33_minor + isMinor_of_embedding. -/
def ChildB2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V), ThreeTreeStmt H →
    (completeBipartiteGraph (Fin 3) (Fin 3)).Free H → HasQueueLayout H 5

theorem childB_of_childB2 (hB2 : ChildB2) : ChildB := by
  intro V _ _ H hP hT
  refine hB2 H hT ?_
  rintro ⟨f⟩
  exact planar_no_K33_minor H hP (isMinor_of_embedding H _ f)

theorem lemma_5_of_children (hA : ChildA) (hB : ChildB) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3) : HasQueueLayout G 5 := by
  by_cases hc : Fintype.card V ≤ 3
  · exact hasQueueLayout_small G hc 5 (by norm_num)
  · obtain ⟨H, hle, hP, hT⟩ := hA G hplanar htw (by omega)
    exact hasQueueLayout_mono hle (hB H hP hT)

end PQL5
/-! PQL5 / KV-comb lemma YD: a Y-Delta exchange (delete a vertex `v` adjacent to `a, b, c`, add edges
among `a, b, c`) cannot create a minor of a triangle-free graph without isolated vertices (e.g. K₃,₃).
Used in the 3-connected step of the combinatorial Kratochvil-Vaner completion. -/

namespace PQL5

open RobertsonSeymour1986.GM5

/-- `x` is one of `a, b, c`. -/
def In3 {V : Type} (a b c x : V) : Prop := x = a ∨ x = b ∨ x = c

theorem four_of_three {V : Type} {a b c p q r s : V} (hp : In3 a b c p)
    (hq : In3 a b c q) (hr : In3 a b c r) (hs : In3 a b c s)
    (h1 : p ≠ q) (h2 : p ≠ r) (h3 : p ≠ s) (h4 : q ≠ r) (h5 : q ≠ s) (h6 : r ≠ s) : False := by
  unfold In3 at hp hq hr hs
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp_all

/-- A property holding at one vertex of a connected induced set and closed under induced adjacency
holds on the whole set. -/
theorem induce_closed {V : Type} {G : SimpleGraph V} {s : Set V} (hc : (G.induce s).Connected)
    (P : V → Prop) {x0 : V} (hx0 : x0 ∈ s) (h0 : P x0)
    (hstep : ∀ x y, x ∈ s → y ∈ s → G.Adj x y → P x → P y) : ∀ y ∈ s, P y := by
  intro y hy
  have hr := hc.preconnected ⟨x0, hx0⟩ ⟨y, hy⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have key : ∀ u : s, Relation.ReflTransGen (G.induce s).Adj ⟨x0, hx0⟩ u → P u.1 := by
    intro u hu
    induction hu with
    | refl => exact h0
    | @tail b c _ hbc ih =>
      exact hstep b.1 c.1 b.2 c.2 (by simpa using hbc) ih
  exact key ⟨y, hy⟩ hr

/-- Adding a vertex `v` to a set connected in `G''`, where every `G''`-edge of the set is a `G`-edge
or joins two `G`-neighbours of `v`, gives a set connected in `G`. -/
theorem induce_insert_connected {V : Type} {G G'' : SimpleGraph V} {s : Set V} {v : V}
    (hc : (G''.induce s).Connected)
    (hstep : ∀ x y, x ∈ s → y ∈ s → G''.Adj x y → G.Adj x y ∨ (G.Adj v x ∧ G.Adj v y))
    {x0 : V} (hx0 : x0 ∈ s) (hv0 : G.Adj v x0) :
    (G.induce (insert v s)).Connected := by
  have hv : v ∈ insert v s := Set.mem_insert v s
  have hall : ∀ y ∈ s, ∃ hy : y ∈ insert v s,
      (G.induce (insert v s)).Reachable ⟨v, hv⟩ ⟨y, hy⟩ := by
    refine induce_closed hc (fun y => ∃ hy : y ∈ insert v s,
      (G.induce (insert v s)).Reachable ⟨v, hv⟩ ⟨y, hy⟩) hx0 ?_ ?_
    · refine ⟨Set.mem_insert_of_mem v hx0, SimpleGraph.Adj.reachable ?_⟩
      simpa using hv0
    · rintro x y _ hy hxy ⟨_, hr⟩
      refine ⟨Set.mem_insert_of_mem v hy, ?_⟩
      rcases hstep x y ‹_› hy hxy with h | ⟨_, h⟩
      · exact hr.trans (SimpleGraph.Adj.reachable (by simpa using h))
      · exact SimpleGraph.Adj.reachable (by simpa using h)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, hv⟩, ?_⟩
  rintro ⟨y, hy⟩
  rcases Set.mem_insert_iff.1 hy with h | h
  · subst h
    exact SimpleGraph.Reachable.refl _
  · obtain ⟨_, h'⟩ := hall y h
    exact h'

/-- **Lemma YD.** Let `v` be adjacent in `G` to `a, b, c`, and let `G''` have no edge at `v` and only
edges of `G` or edges among `a, b, c`. Then every minor of `G''` that is triangle-free and has no
isolated vertex is a minor of `G`. -/
theorem minor_YDelta {W V : Type} (K : SimpleGraph W)
    (hKtri : ∀ x y z, K.Adj x y → K.Adj y z → ¬ K.Adj x z)
    (hKiso : ∀ w, ∃ w', K.Adj w w')
    (G G'' : SimpleGraph V) (v a b c : V)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hG'' : ∀ x y, G''.Adj x y → x ≠ v ∧ (G.Adj x y ∨ (In3 a b c x ∧ In3 a b c y)))
    (hm : IsMinor K G'') : IsMinor K G := by
  classical
  obtain ⟨β, hβ, hpw, hadj⟩ := hm
  have hvA : ∀ x, In3 a b c x → G.Adj v x := by
    rintro x (rfl | rfl | rfl) <;> assumption
  have hvβ : ∀ w, v ∉ β w := by
    intro w hvw
    obtain ⟨w', hww'⟩ := hKiso w
    obtain ⟨x, hx, y, _, hxy⟩ := hadj w w' hww'
    have hall : ∀ y ∈ β w, y = v :=
      induce_closed (hβ w).2 (fun y => y = v) hvw rfl
        (fun x y _ _ hxy hx => absurd hx (hG'' x y hxy).1)
    exact (hG'' x y hxy).1 (hall x hx)
  have hdis : ∀ p q x, x ∈ β p → x ∈ β q → p = q := by
    intro p q x hp hq
    by_contra hne
    exact Set.disjoint_left.1 (hpw hne) hp hq
  -- the set `D` of branch sets that receive `v` (at most one)
  obtain ⟨D, hD, hDA, hle, hbad⟩ : ∃ D : Set W, D.Subsingleton ∧
      (∀ w ∈ D, ∃ x ∈ β w, In3 a b c x) ∧
      (∀ w ∉ D, ∀ x ∈ β w, ∀ y ∈ β w, In3 a b c x → In3 a b c y → x = y) ∧
      (∀ p q, K.Adj p q → ∀ x ∈ β p, ∀ y ∈ β q, In3 a b c x → In3 a b c y → x ≠ y →
        p ∈ D ∨ q ∈ D) := by
    by_cases h1 : ∃ w, ∃ x ∈ β w, ∃ y ∈ β w, In3 a b c x ∧ In3 a b c y ∧ x ≠ y
    · obtain ⟨w0, x, hx, y, hy, hAx, hAy, hxy⟩ := h1
      refine ⟨{w0}, Set.subsingleton_singleton, ?_, ?_, ?_⟩
      · intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ⟨x, hx, hAx⟩
      · intro w hw x' hx' y' hy' hAx' hAy'
        rw [Set.mem_singleton_iff] at hw
        by_contra hne
        have n1 : x ≠ x' := fun e => hw (hdis _ _ _ hx' (e ▸ hx))
        have n2 : x ≠ y' := fun e => hw (hdis _ _ _ hy' (e ▸ hx))
        have n3 : y ≠ x' := fun e => hw (hdis _ _ _ hx' (e ▸ hy))
        have n4 : y ≠ y' := fun e => hw (hdis _ _ _ hy' (e ▸ hy))
        exact four_of_three hAx hAy hAx' hAy' hxy n1 n2 n3 n4 hne
      · intro p q _ x' hx' y' hy' hAx' hAy' hne
        by_contra hcon
        simp only [Set.mem_singleton_iff, not_or] at hcon
        obtain ⟨hp, hq⟩ := hcon
        have n1 : x ≠ x' := fun e => hp (hdis _ _ _ hx' (e ▸ hx))
        have n2 : x ≠ y' := fun e => hq (hdis _ _ _ hy' (e ▸ hx))
        have n3 : y ≠ x' := fun e => hp (hdis _ _ _ hx' (e ▸ hy))
        have n4 : y ≠ y' := fun e => hq (hdis _ _ _ hy' (e ▸ hy))
        exact four_of_three hAx hAy hAx' hAy' hxy n1 n2 n3 n4 hne
    · push Not at h1
      by_cases h2 : ∃ p q, K.Adj p q ∧ ∃ x ∈ β p, ∃ y ∈ β q,
          In3 a b c x ∧ In3 a b c y ∧ x ≠ y
      · obtain ⟨p0, q0, hpq0, x0, hx0, y0, hy0, hA0, hB0, hne0⟩ := h2
        have through : ∀ (u0 : W) (s0 t0 : V), s0 ∈ β u0 → In3 a b c s0 → In3 a b c t0 →
            s0 ≠ t0 → ∀ (t0w : W), t0 ∈ β t0w →
            ∀ p q, K.Adj p q → ∀ x ∈ β p, ∀ y ∈ β q, In3 a b c x → In3 a b c y → x ≠ y →
              p ≠ u0 → q ≠ u0 → ∃ r, K.Adj t0w r ∧ ∃ z ∈ β r, In3 a b c z ∧ z ≠ s0 ∧ z ≠ t0 := by
          intro u0 s0 t0 hs0 hs0A ht0A hst t0w ht0 p q hpq x hx y hy hAx hAy hne hp hq
          have n1 : x ≠ s0 := fun e => hp (hdis _ _ _ hx (e ▸ hs0))
          have n2 : y ≠ s0 := fun e => hq (hdis _ _ _ hy (e ▸ hs0))
          by_cases e1 : x = t0
          · have hpt : p = t0w := hdis _ _ _ hx (e1 ▸ ht0)
            subst hpt
            exact ⟨q, hpq, y, hy, hAy, n2, fun e => hne (e1.trans e.symm)⟩
          · by_cases e2 : y = t0
            · have hqt : q = t0w := hdis _ _ _ hy (e2 ▸ ht0)
              subst hqt
              exact ⟨p, hpq.symm, x, hx, hAx, n1, e1⟩
            · exact (four_of_three hAx hAy hs0A ht0A hne n1 e1 n2 e2 hst).elim
        by_cases hP : ∀ p q, K.Adj p q → ∀ x ∈ β p, ∀ y ∈ β q, In3 a b c x → In3 a b c y →
            x ≠ y → p = p0 ∨ q = p0
        · refine ⟨{p0}, Set.subsingleton_singleton, ?_, fun w _ => h1 w, ?_⟩
          · intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst hw
            exact ⟨x0, hx0, hA0⟩
          · intro p q hpq x hx y hy hAx hAy hne
            simpa using hP p q hpq x hx y hy hAx hAy hne
        · refine ⟨{q0}, Set.subsingleton_singleton, ?_, fun w _ => h1 w, ?_⟩
          · intro w hw
            rw [Set.mem_singleton_iff] at hw
            subst hw
            exact ⟨y0, hy0, hB0⟩
          · intro p q hpq x hx y hy hAx hAy hne
            by_contra hcon
            simp only [Set.mem_singleton_iff, not_or] at hcon
            obtain ⟨hp, hq⟩ := hcon
            push Not at hP
            obtain ⟨p1, q1, hpq1, x1, hx1, y1, hy1, hAx1, hAy1, hne1, hp1, hq1⟩ := hP
            obtain ⟨r, hr, z, hz, hAz, hz1, hz2⟩ := through p0 x0 y0 hx0 hA0 hB0 hne0 q0 hy0
              p1 q1 hpq1 x1 hx1 y1 hy1 hAx1 hAy1 hne1 hp1 hq1
            obtain ⟨r', hr', z', hz', hAz', hz1', hz2'⟩ := through q0 y0 x0 hy0 hB0 hA0
              hne0.symm p0 hx0 p q hpq x hx y hy hAx hAy hne hp hq
            have hzz : z = z' := by
              by_contra hzz
              exact four_of_three hA0 hB0 hAz hAz' hne0 hz1.symm hz2'.symm hz2.symm
                hz1'.symm hzz
            subst hzz
            have hrr : r = r' := hdis _ _ _ hz hz'
            subst hrr
            exact hKtri p0 q0 r hpq0 hr hr'
      · push Not at h2
        refine ⟨∅, Set.subsingleton_empty, by simp, fun w _ => h1 w, ?_⟩
        intro p q hpq x hx y hy hAx hAy hne
        exact absurd (h2 p q hpq x hx y hy hAx hAy) hne
  -- the new branch sets
  obtain ⟨β', hβ'⟩ : ∃ β' : W → Set V, ∀ w, β' w = if w ∈ D then insert v (β w) else β w :=
    ⟨_, fun w => rfl⟩
  have sub : ∀ w, β w ⊆ β' w := by
    intro w z hz
    rw [hβ' w]
    split_ifs
    · exact Set.mem_insert_of_mem _ hz
    · exact hz
  have memv : ∀ w, w ∈ D → v ∈ β' w := by
    intro w hw
    rw [hβ' w, if_pos hw]
    exact Set.mem_insert _ _
  have mem' : ∀ w x, x ∈ β' w → (x = v ∧ w ∈ D) ∨ x ∈ β w := by
    intro w x hx
    rw [hβ' w] at hx
    split_ifs at hx with hw
    · rcases hx with h | h
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr h
    · exact Or.inr hx
  refine ⟨β', ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ D
    · rw [hβ' w, if_pos hw]
      refine ⟨Set.insert_nonempty _ _, ?_⟩
      obtain ⟨x0, hx0, hAx0⟩ := hDA w hw
      refine induce_insert_connected (hβ w).2 (fun x y _ _ hxy => ?_) hx0 (hvA x0 hAx0)
      rcases (hG'' x y hxy).2 with h | ⟨hx, hy⟩
      · exact Or.inl h
      · exact Or.inr ⟨hvA x hx, hvA y hy⟩
    · rw [hβ' w, if_neg hw]
      refine ⟨(hβ w).1, SimpleGraph.Connected.mono ?_ (hβ w).2⟩
      intro x y hxy
      change G''.Adj x.1 y.1 at hxy
      change G.Adj x.1 y.1
      rcases (hG'' _ _ hxy).2 with h | ⟨hx, hy⟩
      · exact h
      · exact absurd (hle w hw x.1 x.2 y.1 y.2 hx hy) (G''.ne_of_adj hxy)
  · intro p q hpq
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases mem' p x hxp with ⟨hxv, hp⟩ | hp <;> rcases mem' q x hxq with ⟨hxv', hq⟩ | hq
    · exact hpq (hD hp hq)
    · exact hvβ q (hxv ▸ hq)
    · exact hvβ p (hxv' ▸ hp)
    · exact Set.disjoint_left.1 (hpw hpq) hp hq
  · intro p q hpq
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj p q hpq
    rcases (hG'' x y hxy).2 with h | ⟨hAx, hAy⟩
    · exact ⟨x, sub p hx, y, sub q hy, h⟩
    · rcases hbad p q hpq x hx y hy hAx hAy (G''.ne_of_adj hxy) with hp | hq
      · exact ⟨v, memv p hp, y, sub q hy, hvA y hAy⟩
      · exact ⟨x, sub p hx, v, memv q hq, (hvA x hAx).symm⟩

/-- `K₃,₃` is triangle-free. -/
theorem K33_triangle_free : ∀ x y z : Fin 3 ⊕ Fin 3,
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x y →
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj y z →
    ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj x z := by
  intro x y z
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> simp

/-- `K₃,₃` has no isolated vertex. -/
theorem K33_no_isolated : ∀ w : Fin 3 ⊕ Fin 3,
    ∃ w', (completeBipartiteGraph (Fin 3) (Fin 3)).Adj w w' := by
  intro w
  rcases w with w | w
  · exact ⟨Sum.inr 0, by simp⟩
  · exact ⟨Sum.inl 0, by simp⟩

end PQL5

namespace PQL5

/-- the triangle on `x, y, z` -/
def tri {V : Type} (x y z : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {s(x, y), s(y, z), s(x, z)}

/-- the star joining `v` to `x, y, z` -/
def star3 {V : Type} (v x y z : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {s(v, x), s(v, y), s(v, z)}

/-- `H` is a 3-tree on the vertex set `S`, grown from the base triangle `x y z` by stacking
vertices onto triangles (Proskurowski; DJMMUW Sect. 2). -/
inductive TTb {V : Type} [DecidableEq V] : SimpleGraph V → Finset V → V → V → V → Prop
  | base (x y z : V) : x ≠ y → y ≠ z → x ≠ z → TTb (tri x y z) {x, y, z} x y z
  | stack {H : SimpleGraph V} {S : Finset V} {x y z : V} (v p q r : V) : TTb H S x y z → v ∉ S →
      p ∈ S → q ∈ S → r ∈ S → H.Adj p q → H.Adj q r → H.Adj p r →
      TTb (H ⊔ star3 v p q r) (insert v S) x y z

/-- `H` is a 3-tree on `S`. -/
def TT {V : Type} [DecidableEq V] (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ x y z, TTb H S x y z

section TTlemmas

variable {V : Type} [DecidableEq V]

theorem tri_adj {x y z u w : V} : (tri x y z).Adj u w ↔ u ≠ w ∧
    ((u = x ∧ w = y) ∨ (u = y ∧ w = x) ∨ (u = y ∧ w = z) ∨ (u = z ∧ w = y) ∨
      (u = x ∧ w = z) ∨ (u = z ∧ w = x)) := by
  unfold tri
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

theorem star3_adj {v x y z u w : V} : (star3 v x y z).Adj u w ↔ u ≠ w ∧
    ((u = v ∧ w = x) ∨ (u = x ∧ w = v) ∨ (u = v ∧ w = y) ∨ (u = y ∧ w = v) ∨
      (u = v ∧ w = z) ∨ (u = z ∧ w = v)) := by
  unfold star3
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
  tauto

omit [DecidableEq V] in
theorem tri_swap12 (x y z : V) : tri y x z = tri x y z := by
  unfold tri
  rw [show s(y, x) = s(x, y) from Sym2.eq_swap]
  congr 1
  ext e
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  try tauto

omit [DecidableEq V] in
theorem tri_swap23 (x y z : V) : tri x z y = tri x y z := by
  unfold tri
  rw [show s(z, y) = s(y, z) from Sym2.eq_swap]
  congr 1
  ext e
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  try tauto

theorem tri_star3_comm (v b c t : V) : tri b c t ⊔ star3 v b c t = tri v b c ⊔ star3 t v b c := by
  unfold tri star3
  rw [← SimpleGraph.fromEdgeSet_union, ← SimpleGraph.fromEdgeSet_union,
    show s(t, v) = s(v, t) from Sym2.eq_swap, show s(t, b) = s(b, t) from Sym2.eq_swap,
    show s(t, c) = s(c, t) from Sym2.eq_swap]
  congr 1
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  try tauto

theorem TTb.supp {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ u w, H.Adj u w → u ∈ S ∧ w ∈ S := by
  induction h with
  | base x y z _ _ _ =>
    intro u w huw
    rw [tri_adj] at huw
    obtain ⟨_, h⟩ := huw
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp
  | @stack H S x y z v p q r _ _ hp hq hr _ _ _ ih =>
    intro u w huw
    rw [SimpleGraph.sup_adj, star3_adj] at huw
    rcases huw with huw | ⟨_, h⟩
    · obtain ⟨h1, h2⟩ := ih u w huw
      exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [hp, hq, hr]

theorem TTb.base_mem {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ H.Adj x y ∧ H.Adj y z ∧ H.Adj x z := by
  induction h with
  | base x y z hxy hyz hxz =>
    refine ⟨by simp, by simp, by simp, ?_, ?_, ?_⟩
    · rw [tri_adj]; exact ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩
    · rw [tri_adj]; exact ⟨hyz, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rw [tri_adj]; exact ⟨hxz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  | @stack H S x y z v p q r _ _ _ _ _ _ _ _ ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2, Finset.mem_insert_of_mem h3,
      (le_sup_left : H ≤ H ⊔ _) h4, (le_sup_left : H ≤ H ⊔ _) h5, (le_sup_left : H ≤ H ⊔ _) h6⟩

theorem TTb.swap12 {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    TTb H S y x z := by
  induction h with
  | base x y z hxy hyz hxz =>
    have h := TTb.base y x z hxy.symm hxz hyz
    rwa [tri_swap12, Finset.insert_comm] at h
  | @stack H S x y z v p q r _ hv hp hq hr hpq hqr hpr ih =>
    exact TTb.stack v p q r ih hv hp hq hr hpq hqr hpr

theorem TTb.swap23 {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    TTb H S x z y := by
  induction h with
  | base x y z hxy hyz hxz =>
    have h := TTb.base x z y hxz hyz.symm hxy
    rwa [tri_swap23, Finset.pair_comm] at h
  | @stack H S x y z v p q r _ hv hp hq hr hpq hqr hpr ih =>
    exact TTb.stack v p q r ih hv hp hq hr hpq hqr hpr

/-- A vertex stacked on the base triangle can become the first base vertex. -/
theorem TTb.push {H : SimpleGraph V} {S : Finset V} {b c t : V} (h : TTb H S b c t) :
    ∀ v, v ∉ S → TTb (H ⊔ star3 v b c t) (insert v S) v b c := by
  induction h with
  | base b c t hbc hct hbt =>
    intro v hv
    have hvb : v ≠ b := fun e => hv (by simp [e])
    have hvc : v ≠ c := fun e => hv (by simp [e])
    have htv : t ∉ ({v, b, c} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hv (by simp [e]), hbt.symm, hct.symm⟩
    have h0 := TTb.stack t v b c (TTb.base v b c hvb hbc hvc) htv (by simp) (by simp) (by simp)
      (by rw [tri_adj]; exact ⟨hvb, Or.inl ⟨rfl, rfl⟩⟩)
      (by rw [tri_adj]; exact ⟨hbc, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
      (by rw [tri_adj]; exact ⟨hvc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)
    rw [← tri_star3_comm] at h0
    have hS : (insert v {b, c, t} : Finset V) = insert t {v, b, c} := by
      ext u; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [hS]
    exact h0
  | @stack H S b c t u p q r _ hu hp hq hr hpq hqr hpr ih =>
    intro v hv
    have hvS : v ∉ S := fun e => hv (Finset.mem_insert_of_mem e)
    have hvu : u ≠ v := fun e => hv (by rw [← e]; exact Finset.mem_insert_self u S)
    have h1 := TTb.stack u p q r (ih v hvS) (by simp [hvu, hu]) (Finset.mem_insert_of_mem hp)
      (Finset.mem_insert_of_mem hq) (Finset.mem_insert_of_mem hr)
      ((le_sup_left : H ≤ H ⊔ _) hpq) ((le_sup_left : H ≤ H ⊔ _) hqr)
      ((le_sup_left : H ≤ H ⊔ _) hpr)
    rw [sup_right_comm, Finset.insert_comm] at h1
    exact h1

/-- **M1 (re-rooting).** A 3-tree can be grown from any of its triangles (Proskurowski). -/
theorem TTb.reroot {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ a b c, H.Adj a b → H.Adj b c → H.Adj a c → TTb H S a b c := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro a b c hab hbc hac
    have hs := (TTb.base x y z hxy hyz hxz).supp
    have ha := (hs a b hab).1
    have hb := (hs a b hab).2
    have hc := (hs b c hbc).2
    have nab := hab.ne
    have nbc := hbc.ne
    have nac := hac.ne
    have h0 := TTb.base x y z hxy hyz hxz
    have h1 := h0.swap12
    have h2 := h0.swap23
    have h3 := h0.swap12.swap23
    have h4 := h0.swap23.swap12
    have h5 := h0.swap12.swap23.swap12
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;>
      first | exact (nab rfl).elim | exact (nbc rfl).elim | exact (nac rfl).elim | assumption
  | @stack H S x y z v p q r h0 hv hp hq hr hpq hqr hpr ih =>
    have hsupp := h0.supp
    have adjH : ∀ a b, (H ⊔ star3 v p q r).Adj a b → a ≠ v → b ≠ v → H.Adj a b := by
      intro a b hab hav hbv
      rw [SimpleGraph.sup_adj, star3_adj] at hab
      rcases hab with h | ⟨_, h⟩
      · exact h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first | exact hav h1 | exact hbv h2
    have nbrv : ∀ b, (H ⊔ star3 v p q r).Adj v b → b = p ∨ b = q ∨ b = r := by
      intro b hb
      rw [SimpleGraph.sup_adj, star3_adj] at hb
      rcases hb with h | ⟨hne, h⟩
      · exact absurd (hsupp v b h).1 hv
      · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl h2
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inl h2)
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inr h2)
        · exact (hne h2.symm).elim
    have key : ∀ b c t, H.Adj b c → H.Adj c t → H.Adj b t → star3 v b c t = star3 v p q r →
        TTb (H ⊔ star3 v p q r) (insert v S) v b c := by
      intro b c t h1 h2 h3 he
      have := (ih b c t h1 h2 h3).push v hv
      rwa [he] at this
    have case_v : ∀ b c, (H ⊔ star3 v p q r).Adj v b → (H ⊔ star3 v p q r).Adj v c →
        (H ⊔ star3 v p q r).Adj b c → TTb (H ⊔ star3 v p q r) (insert v S) v b c := by
      intro b c hvb hvc hbc
      have nbc := hbc.ne
      rcases nbrv b hvb with rfl | rfl | rfl <;> rcases nbrv c hvc with rfl | rfl | rfl
      · exact (nbc rfl).elim
      · exact key _ _ _ hpq hqr hpr (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hpr hqr.symm hpq (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hpq.symm hpr hqr (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact (nbc rfl).elim
      · exact key _ _ _ hqr hpr.symm hpq.symm (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hpr.symm hpq hqr.symm (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact key _ _ _ hqr.symm hpq.symm hpr.symm (by first | rfl | (unfold star3; congr 1; ext e; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; try tauto))
      · exact (nbc rfl).elim
    intro a b c hab hbc hac
    by_cases ha : a = v
    · subst ha
      exact case_v b c hab hac hbc
    · by_cases hb : b = v
      · subst hb
        exact (case_v a c hab.symm hbc hac).swap12
      · by_cases hc : c = v
        · subst hc
          exact (case_v a b hac.symm hbc.symm hab).swap12.swap23
        · exact TTb.stack v p q r (ih a b c (adjH a b hab ha hb) (adjH b c hbc hb hc)
            (adjH a c hac ha hc)) hv hp hq hr hpq hqr hpr

end TTlemmas

end PQL5

/-! M2: every edge of a 3-tree lies in a face (a triangle with at most one common neighbour). -/

namespace PQL5

section Faces

variable {V : Type} [DecidableEq V]

/-- `x y z` is a triangle of `H` with at most one common neighbour. -/
def Face (H : SimpleGraph V) (x y z : V) : Prop :=
  H.Adj x y ∧ H.Adj y z ∧ H.Adj x z ∧ ∀ p q, p ≠ q → H.Adj p x → H.Adj p y → H.Adj p z →
    H.Adj q x → H.Adj q y → H.Adj q z → False

omit [DecidableEq V] in
theorem Face.swap12 {H : SimpleGraph V} {x y z : V} (h : Face H x y z) : Face H y x z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.symm, h3, h2, fun p q hpq a b c d e f => h4 p q hpq b a c e d f⟩

theorem tri_adj_of_In3 {x y z u w : V} (hu : In3 x y z u) (hw : In3 x y z w) (huw : u ≠ w) :
    (tri x y z).Adj u w := by
  rw [tri_adj]
  refine ⟨huw, ?_⟩
  unfold In3 at hu hw
  rcases hu with h1 | h1 | h1 <;> rcases hw with h2 | h2 | h2 <;> simp_all

theorem tri_In3_of_adj {x y z u w : V} (h : (tri x y z).Adj u w) :
    In3 x y z u ∧ In3 x y z w := by
  rw [tri_adj] at h
  obtain ⟨_, h⟩ := h
  unfold In3
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

theorem face_tri {x y z u w t : V} (hu : In3 x y z u) (hw : In3 x y z w) (ht : In3 x y z t)
    (huw : u ≠ w) (hwt : w ≠ t) (hut : u ≠ t) : Face (tri x y z) u w t := by
  refine ⟨tri_adj_of_In3 hu hw huw, tri_adj_of_In3 hw ht hwt, tri_adj_of_In3 hu ht hut, ?_⟩
  intro p _ _ hpu hpw hpt _ _ _
  exact four_of_three hu hw ht (tri_In3_of_adj hpu).1 huw hut (Ne.symm hpu.ne) hwt
    (Ne.symm hpw.ne) (Ne.symm hpt.ne)

/-- **M2.** Every edge of a 3-tree lies in a face. -/
theorem TTb.edge_face {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ u w, H.Adj u w → ∃ t, Face H u w t := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro u w huw
    have hIn := tri_In3_of_adj huw
    have hne := huw.ne
    have hx : In3 x y z x := Or.inl rfl
    have hy : In3 x y z y := Or.inr (Or.inl rfl)
    have hz : In3 x y z z := Or.inr (Or.inr rfl)
    by_cases hux : u = x
    · by_cases hwy : w = y
      · exact ⟨z, face_tri hIn.1 hIn.2 hz hne (by rw [hwy]; exact hyz) (by rw [hux]; exact hxz)⟩
      · exact ⟨y, face_tri hIn.1 hIn.2 hy hne hwy (by rw [hux]; exact hxy)⟩
    · by_cases hwx : w = x
      · by_cases huy : u = y
        · exact ⟨z, face_tri hIn.1 hIn.2 hz hne (by rw [hwx]; exact hxz) (by rw [huy]; exact hyz)⟩
        · exact ⟨y, face_tri hIn.1 hIn.2 hy hne (by rw [hwx]; exact hxy) huy⟩
      · exact ⟨x, face_tri hIn.1 hIn.2 hx hne hwx hux⟩
  | @stack H S x y z v p q r h0 hv hp hq hr hpq hqr hpr ih =>
    have hsupp := h0.supp
    have hvS : ∀ a, a ∈ S → a ≠ v := fun a ha e => hv (by rw [← e]; exact ha)
    have adjH : ∀ a b, (H ⊔ star3 v p q r).Adj a b → a ≠ v → b ≠ v → H.Adj a b := by
      intro a b hab hav hbv
      rw [SimpleGraph.sup_adj, star3_adj] at hab
      rcases hab with h | ⟨_, h⟩
      · exact h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first | exact hav h1 | exact hbv h2
    have nbrv : ∀ b, (H ⊔ star3 v p q r).Adj v b → In3 p q r b := by
      intro b hb
      rw [SimpleGraph.sup_adj, star3_adj] at hb
      rcases hb with h | ⟨hne, h⟩
      · exact absurd (hsupp v b h).1 hv
      · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inl h2
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inl h2)
        · exact (hne h2.symm).elim
        · exact Or.inr (Or.inr h2)
        · exact (hne h2.symm).elim
    have adjv : ∀ b, In3 p q r b → (H ⊔ star3 v p q r).Adj v b := by
      intro b hb
      rw [SimpleGraph.sup_adj, star3_adj]
      right
      rcases hb with h | h | h
      · rw [h]; exact ⟨fun e => hv (by rw [e]; exact hp), Or.inl ⟨rfl, rfl⟩⟩
      · rw [h]; exact ⟨fun e => hv (by rw [e]; exact hq), Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · rw [h]
        exact ⟨fun e => hv (by rw [e]; exact hr), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    have adj0 : ∀ a b, In3 p q r a → In3 p q r b → a ≠ b → H.Adj a b := by
      intro a b ha hb hab
      rcases ha with h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2 <;> rw [h1, h2] at hab ⊢ <;>
        first | exact (hab rfl).elim | exact hpq | exact hqr | exact hpr | exact hpq.symm |
          exact hqr.symm | exact hpr.symm
    have face_new : ∀ b c, In3 p q r b → In3 p q r c → b ≠ c → Face (H ⊔ star3 v p q r) v b c := by
      intro b c hb hc hbc
      refine ⟨adjv b hb, (le_sup_left : H ≤ H ⊔ _) (adj0 b c hb hc hbc), adjv c hc, ?_⟩
      intro s s' hss' hsv hsb hsc hs'v hs'b hs'c
      exact four_of_three hb hc (nbrv s hsv.symm) (nbrv s' hs'v.symm) hbc (Ne.symm hsb.ne)
        (Ne.symm hs'b.ne) (Ne.symm hsc.ne) (Ne.symm hs'c.ne) hss'
    have other : ∀ b, In3 p q r b → ∃ c, In3 p q r c ∧ b ≠ c := by
      intro b _
      by_cases hbp : b = p
      · exact ⟨q, Or.inr (Or.inl rfl), by rw [hbp]; exact hpq.ne⟩
      · exact ⟨p, Or.inl rfl, hbp⟩
    intro u w huw
    by_cases huv : u = v
    · rw [huv] at huw ⊢
      obtain ⟨c, hc, hwc⟩ := other w (nbrv w huw)
      exact ⟨c, face_new w c (nbrv w huw) hc hwc⟩
    by_cases hwv : w = v
    · rw [hwv] at huw ⊢
      have hu := nbrv u huw.symm
      obtain ⟨c, hc, huc⟩ := other u hu
      exact ⟨c, (face_new u c hu hc huc).swap12⟩
    have h0uw := adjH u w huw huv hwv
    obtain ⟨t, _, ht2, ht3, ht4⟩ := ih u w h0uw
    have htv : t ≠ v := hvS t (hsupp w t ht2).2
    by_cases hall : (H ⊔ star3 v p q r).Adj v u ∧ (H ⊔ star3 v p q r).Adj v w ∧
        (H ⊔ star3 v p q r).Adj v t
    · obtain ⟨a1, a2, _⟩ := hall
      have hu := nbrv u a1
      have hw := nbrv w a2
      refine ⟨v, huw, a2.symm, a1.symm, ?_⟩
      intro s s' hss' hsu hsw hsv hs'u hs'w hs'v
      exact four_of_three hu hw (nbrv s hsv.symm) (nbrv s' hs'v.symm) huw.ne (Ne.symm hsu.ne)
        (Ne.symm hs'u.ne) (Ne.symm hsw.ne) (Ne.symm hs'w.ne) hss'
    · refine ⟨t, huw, (le_sup_left : H ≤ H ⊔ _) ht2, (le_sup_left : H ≤ H ⊔ _) ht3, ?_⟩
      intro s s' hss' hsu hsw hst hs'u hs'w hs't
      have hsv : s ≠ v := fun e => hall (by subst e; exact ⟨hsu, hsw, hst⟩)
      have hs'v : s' ≠ v := fun e => hall (by subst e; exact ⟨hs'u, hs'w, hs't⟩)
      exact ht4 s s' hss' (adjH s u hsu hsv huv) (adjH s w hsw hsv hwv) (adjH s t hst hsv htv)
        (adjH s' u hs'u hs'v huv) (adjH s' w hs'w hs'v hwv) (adjH s' t hs't hs'v htv)

end Faces

end PQL5

/-! Combinatorial interface (session 2): 3-trees grown by stacking (`TT`), the Apollonian condition
`TriCond`, and the reduction of lemma_5 to C2 (combinatorial Kratochvil-Vaner) and C3 (combinatorial
Alam et al.). -/

namespace PQL5

open PlanarQueue.Planar

/-- No triangle of `H` has three distinct common neighbours (planar 3-trees = Apollonian
networks). -/
def TriCond {V : Type} (H : SimpleGraph V) : Prop :=
  ∀ a b c p q r : V, H.Adj a b → H.Adj b c → H.Adj a c → p ≠ q → q ≠ r → p ≠ r →
    H.Adj p a → H.Adj p b → H.Adj p c → H.Adj q a → H.Adj q b → H.Adj q c →
    H.Adj r a → H.Adj r b → H.Adj r c → False

/-- C2 (combinatorial Kratochvil-Vaner, arXiv 1210.8113 Thm 1): a treewidth-3 graph without a
`K₃,₃` minor, supported on `S` with `|S| ≥ 3`, is a spanning subgraph of an Apollonian 3-tree on `S`. -/
def ChildC2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (S : Finset V) (G : SimpleGraph V),
    (∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S) → 3 ≤ S.card →
    RobertsonSeymour1986.GM5.TreewidthLE G 3 →
    ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G →
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H

/-- C3 (combinatorial Alam-Bekos-Gronemann-Kaufmann-Pupyrev, arXiv 1808.10841 Thm 1): an
Apollonian 3-tree has a 5-queue layout. -/
def ChildC3 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V), TT H Finset.univ → TriCond H →
    HasQueueLayout H 5

theorem lemma_5_of_C2_C3 (h2 : ChildC2) (h3 : ChildC3) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3) : HasQueueLayout G 5 := by
  by_cases hc : Fintype.card V ≤ 3
  · exact hasQueueLayout_small G hc 5 (by norm_num)
  · obtain ⟨H, hle, hT, hC⟩ := h2 Finset.univ G
      (fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
      (by rw [Finset.card_univ]; omega) htw (planar_no_K33_minor G hplanar)
    exact hasQueueLayout_mono hle (h3 H hT hC)

end PQL5

/-! C1: a graph of tree-width at most 3 on a support `S` with `|S| ≥ 3` is a spanning subgraph of
a 3-tree on `S` (Proskurowski; the chordal completion of a width-3 tree decomposition). -/

namespace PQL5

section C1

variable {V : Type} [DecidableEq V]

/-- the path (interpolation) property of a tree decomposition -/
def PathProp {T : Type} (t : SimpleGraph T) (X : T → Finset V) : Prop :=
  ∀ (s s' s'' : T) (p : t.Walk s s''), p.IsPath → s' ∈ p.support → X s ∩ X s'' ⊆ X s'

/-- `P` is a union of branches of `t` at `s`. -/
def BrClosed {T : Type} (t : SimpleGraph T) (s : T) (P : Finset T) : Prop :=
  s ∉ P ∧ ∀ u ∈ P, ∀ w, t.Adj u w → w ≠ s → w ∈ P

theorem brClosed_walk_hits {T : Type} {t : SimpleGraph T} {s : T} {P : Finset T}
    (hc : BrClosed t s P) : ∀ {u w : T} (p : t.Walk u w), u ∈ P → w ∉ P → s ∈ p.support := by
  intro u w p
  induction p with
  | nil => intro hu hw; exact absurd hu hw
  | @cons a b c h p ih =>
    intro ha hc'
    by_cases hb : b = s
    · subst hb
      simp
    · have hbP : b ∈ P := hc.2 a ha b h hb
      have := ih hbP hc'
      simp [this]

theorem brClosed_walk_adj {T : Type} {t : SimpleGraph T} {s : T} {P : Finset T}
    (hc : BrClosed t s P) : ∀ {u w : T} (p : t.Walk u w), u ∈ P → w = s → ∃ x ∈ P, t.Adj x s := by
  intro u w p
  induction p with
  | nil => intro hu hw; subst hw; exact absurd hu hc.1
  | @cons a b c h p ih =>
    intro ha hcs
    by_cases hb : b = s
    · subst hb
      exact ⟨a, ha, h⟩
    · exact ih (hc.2 a ha b h hb) hcs

/-- Every tree decomposition has a vertex `v` all of whose bags lie inside one bag containing `v`
(a simplicial vertex of the chordal completion). -/
theorem exists_simplicial {T : Type} [Fintype T] [DecidableEq T] (t : SimpleGraph T)
    (ht : t.Connected) (hac : t.IsAcyclic) (X : T → Finset V) (hp : PathProp t X)
    (hne : ∃ s, (X s).Nonempty) : ∃ v s0, v ∈ X s0 ∧ ∀ s, v ∈ X s → X s ⊆ X s0 := by
  classical
  have key : ∀ m : ℕ, ∀ (s : T) (P : Finset T), P.card = m → BrClosed t s P →
      (∃ w ∈ P, ¬ X w ⊆ X s) → ∃ v s0, v ∈ X s0 ∧ ∀ s, v ∈ X s → X s ⊆ X s0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro s P hPm hc hw
    obtain ⟨w0, hw0P, hw0⟩ := hw
    obtain ⟨p0⟩ := ht.preconnected w0 s
    obtain ⟨s', hs'P, hs's⟩ := brClosed_walk_adj hc p0 hw0P rfl
    have hss' : s ≠ s' := fun h => hc.1 (h ▸ hs'P)
    set P' := P.filter (fun u => u ≠ s' ∧ ∀ p : t.Walk u s, s' ∈ p.support) with hP'
    have hP'sub : P' ⊆ P := Finset.filter_subset _ _
    have hcP' : BrClosed t s' P' := by
      refine ⟨fun h => (Finset.mem_filter.mp h).2.1 rfl, ?_⟩
      intro u hu a hua has'
      rw [hP', Finset.mem_filter] at hu ⊢
      obtain ⟨huP, hus', hall⟩ := hu
      have has : a ≠ s := by
        rintro rfl
        have := hall (SimpleGraph.Walk.cons hua SimpleGraph.Walk.nil)
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at this
        rcases this with h | h
        · exact hus' h.symm
        · exact hss' h.symm
      refine ⟨hc.2 u huP a hua has, has', ?_⟩
      intro q
      have := hall (SimpleGraph.Walk.cons hua q)
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at this
      rcases this with h | h
      · exact absurd h.symm hus'
      · exact h
    have hcard' : P'.card < m := by
      rw [← hPm]
      refine Finset.card_lt_card ⟨hP'sub, fun h => ?_⟩
      exact (Finset.mem_filter.mp (h hs'P)).2.1 rfl
    by_cases hA : ∃ u ∈ P', ¬ X u ⊆ X s'
    · exact ih _ hcard' s' P' rfl hcP' hA
    push_neg at hA
    -- a node of `P` outside `P'` and not `s'` has a walk to `s` avoiding `s'`
    have hout : ∀ u ∈ P, u ≠ s' → u ∉ P' → ∃ q : t.Walk u s, q.IsPath ∧ s' ∉ q.support := by
      intro u huP hus' huP'
      have : ¬ ∀ p : t.Walk u s, s' ∈ p.support := by
        intro h
        exact huP' (Finset.mem_filter.mpr ⟨huP, hus', h⟩)
      push_neg at this
      obtain ⟨q, hq⟩ := this
      exact ⟨q.bypass, q.bypass_isPath,
        fun h => hq (SimpleGraph.Walk.support_bypass_subset_support q h)⟩
    by_cases hB : X s' ⊆ X s
    · -- recurse on the other branches
      have hw0s' : w0 ≠ s' := by rintro rfl; exact hw0 hB
      have hw0P' : w0 ∉ P' := fun h => hw0 ((hA w0 h).trans hB)
      set P2 := (P \ P').erase s' with hP2
      have hc2 : BrClosed t s P2 := by
        refine ⟨fun h => hc.1 (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).1, ?_⟩
        intro u hu a hua has
        rw [hP2, Finset.mem_erase, Finset.mem_sdiff] at hu
        obtain ⟨hus', huP, huP'⟩ := hu
        obtain ⟨q, hqp, hqs'⟩ := hout u huP hus' huP'
        have haP : a ∈ P := hc.2 u huP a hua has
        have has' : a ≠ s' := by
          rintro rfl
          have hpath : (SimpleGraph.Walk.cons hua.symm q).IsPath := by
            rw [SimpleGraph.Walk.cons_isPath_iff]; exact ⟨hqp, hqs'⟩
          have hpath2 : (SimpleGraph.Walk.cons hs's SimpleGraph.Walk.nil : t.Walk a s).IsPath := by
            rw [SimpleGraph.Walk.cons_isPath_iff]
            refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
            simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
            exact fun h => hss' h.symm
          have heq := hac.path_unique ⟨_, hpath⟩ ⟨_, hpath2⟩
          have hsupp := congrArg (fun z : t.Path a s => z.1.support) heq
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.cons.injEq, true_and] at hsupp
          have hu1 : q.support.head? = some u := by
            rw [SimpleGraph.Walk.support_eq_cons]; rfl
          rw [hsupp] at hu1
          simp only [List.head?_cons, Option.some.injEq] at hu1
          exact hc.1 (hu1 ▸ huP)
        have haP' : a ∉ P' := by
          intro h
          obtain ⟨_, _, hall⟩ := (Finset.mem_filter.mp h)
          have := hall (SimpleGraph.Walk.cons hua.symm q)
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at this
          rcases this with h' | h'
          · exact has' h'.symm
          · exact hqs' h'
        rw [hP2, Finset.mem_erase, Finset.mem_sdiff]
        exact ⟨has', haP, haP'⟩
      have hcard2 : P2.card < m := by
        rw [← hPm, hP2]
        exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem
          (Finset.mem_sdiff.mpr ⟨hs'P, fun h => (Finset.mem_filter.mp h).2.1 rfl⟩))
          (Finset.card_le_card Finset.sdiff_subset)
      refine ih _ hcard2 s P2 rfl hc2 ⟨w0, ?_, hw0⟩
      rw [hP2, Finset.mem_erase, Finset.mem_sdiff]
      exact ⟨hw0s', hw0P, hw0P'⟩
    · -- `s'` is the simplicial bag
      rw [Finset.not_subset] at hB
      obtain ⟨v, hvs', hvs⟩ := hB
      refine ⟨v, s', hvs', ?_⟩
      intro u hvu
      by_cases huP' : u ∈ P'
      · exact hA u huP'
      by_cases hus' : u = s'
      · rw [hus']
      exfalso
      apply hvs
      by_cases huP : u ∈ P
      · obtain ⟨q, hqp, hqs'⟩ := hout u huP hus' huP'
        have hpath : (SimpleGraph.Walk.cons hs's q.reverse).IsPath := by
          rw [SimpleGraph.Walk.cons_isPath_iff]
          refine ⟨hqp.reverse, ?_⟩
          rw [SimpleGraph.Walk.support_reverse, List.mem_reverse]
          exact hqs'
        have hs_in : s ∈ (SimpleGraph.Walk.cons hs's q.reverse).support := by
          rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_reverse, List.mem_cons,
            List.mem_reverse]
          exact Or.inr q.end_mem_support
        exact hp s' s u _ hpath hs_in (Finset.mem_inter.mpr ⟨hvs', hvu⟩)
      · obtain ⟨q⟩ := ht.preconnected s' u
        have hsq := brClosed_walk_hits hc q.bypass hs'P huP
        exact hp s' s u q.bypass q.bypass_isPath hsq (Finset.mem_inter.mpr ⟨hvs', hvu⟩)
  obtain ⟨s1, v1, hv1⟩ := hne
  have hc0 : BrClosed t s1 (Finset.univ.erase s1) := by
    refine ⟨Finset.notMem_erase _ _, ?_⟩
    intro u _ w _ hws
    simp [hws]
  by_cases hall : ∃ w ∈ Finset.univ.erase s1, ¬ X w ⊆ X s1
  · exact key _ s1 _ rfl hc0 hall
  push_neg at hall
  refine ⟨v1, s1, hv1, ?_⟩
  intro s _
  by_cases hs : s = s1
  · rw [hs]
  · exact hall s (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ _⟩)

/-- In a 3-tree, every clique of at most three vertices lies in a triangle. -/
theorem TTb.clique_in_tri {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ K : Finset V, K ⊆ S → K.card ≤ 3 → (∀ a ∈ K, ∀ b ∈ K, a ≠ b → H.Adj a b) →
      ∃ p q r, H.Adj p q ∧ H.Adj q r ∧ H.Adj p r ∧ K ⊆ {p, q, r} := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro K hK _ _
    refine ⟨x, y, z, ?_, ?_, ?_, hK⟩
    · rw [tri_adj]; exact ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩
    · rw [tri_adj]; exact ⟨hyz, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rw [tri_adj]; exact ⟨hxz, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
  | @stack H S x y z v p q r hH hv hp hq hr hpq hqr hpr ih =>
    intro K hK hK3 hcl
    have hsupp := hH.supp
    have hle : H ≤ H ⊔ star3 v p q r := le_sup_left
    have hvp : v ≠ p := fun h => hv (h ▸ hp)
    have hvq : v ≠ q := fun h => hv (h ▸ hq)
    have hvr : v ≠ r := fun h => hv (h ▸ hr)
    have hst : ∀ a b, (star3 v p q r).Adj a b → (star3 v p q r ≤ H ⊔ star3 v p q r) →
        (H ⊔ star3 v p q r).Adj a b := fun a b h hs => hs h
    have hS1 : ∀ a b, a ≠ b → (a = v ∧ (b = p ∨ b = q ∨ b = r)) →
        (H ⊔ star3 v p q r).Adj a b := by
      intro a b hab hb
      apply hst a b _ le_sup_right
      rw [star3_adj]
      obtain ⟨rfl, hb⟩ := hb
      refine ⟨hab, ?_⟩
      rcases hb with rfl | rfl | rfl <;> simp
    have hS2 : ∀ a b, a ≠ b → (b = v ∧ (a = p ∨ a = q ∨ a = r)) →
        (H ⊔ star3 v p q r).Adj a b := by
      intro a b hab hb
      exact (hS1 b a (Ne.symm hab) hb).symm
    by_cases hvK : v ∈ K
    · -- every other element of `K` is a neighbour of `v`, hence one of `p, q, r`
      have hKn : ∀ a ∈ K, a ≠ v → a = p ∨ a = q ∨ a = r := by
        intro a ha hav
        have hadj := hcl v hvK a ha (Ne.symm hav)
        rw [SimpleGraph.sup_adj, star3_adj] at hadj
        rcases hadj with hadj | ⟨_, h⟩
        · exact absurd (hsupp v a hadj).1 hv
        · rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
          · exact Or.inl h
          · exact absurd h hav
          · exact Or.inr (Or.inl h)
          · exact absurd h hav
          · exact Or.inr (Or.inr h)
          · exact absurd h hav
      have hpq' : p ≠ q := hpq.ne
      have hqr' : q ≠ r := hqr.ne
      have hpr' : p ≠ r := hpr.ne
      by_cases hpK : p ∈ K
      · by_cases hqK : q ∈ K
        · have hrK : r ∉ K := by
            intro hrK
            have : ({v, p, q, r} : Finset V) ⊆ K := by
              intro a ha
              simp only [Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with rfl | rfl | rfl | rfl <;> assumption
            have h4 := Finset.card_le_card this
            rw [Finset.card_insert_of_notMem (by simp [hvp, hvq, hvr]),
              Finset.card_insert_of_notMem (by simp [hpq', hpr']),
              Finset.card_pair hqr'] at h4
            omega
          refine ⟨v, p, q, hS1 v p hvp ⟨rfl, Or.inl rfl⟩, (hle hpq), hS1 v q hvq ⟨rfl, Or.inr (Or.inl rfl)⟩, ?_⟩
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hav : a = v
          · exact Or.inl hav
          · rcases hKn a ha hav with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
            · exact absurd (h ▸ ha) hrK
        · refine ⟨v, p, r, hS1 v p hvp ⟨rfl, Or.inl rfl⟩, (hle hpr), hS1 v r hvr ⟨rfl, Or.inr (Or.inr rfl)⟩, ?_⟩
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_cases hav : a = v
          · exact Or.inl hav
          · rcases hKn a ha hav with h | h | h
            · exact Or.inr (Or.inl h)
            · exact absurd (h ▸ ha) hqK
            · exact Or.inr (Or.inr h)
      · refine ⟨v, q, r, hS1 v q hvq ⟨rfl, Or.inr (Or.inl rfl)⟩, (hle hqr), hS1 v r hvr ⟨rfl, Or.inr (Or.inr rfl)⟩, ?_⟩
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hav : a = v
        · exact Or.inl hav
        · rcases hKn a ha hav with h | h | h
          · exact absurd (h ▸ ha) hpK
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
    · have hKS : K ⊆ S := by
        intro a ha
        have := hK ha
        rw [Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd (h ▸ ha) hvK
        · exact h
      have hclH : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → H.Adj a b := by
        intro a ha b hb hab
        have hadj := hcl a ha b hb hab
        rw [SimpleGraph.sup_adj, star3_adj] at hadj
        rcases hadj with hadj | ⟨_, h⟩
        · exact hadj
        · exfalso
          rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;>
            exact hvK (h ▸ (by assumption))
      obtain ⟨a, b, c, h1, h2, h3, h4⟩ := ih K hKS hK3 hclH
      exact ⟨a, b, c, hle h1, hle h2, hle h3, h4⟩

/-- C1 core: the chordal completion of a width-3 tree decomposition covering `S` is contained
in a 3-tree on `S`. -/
theorem c1_core {T : Type} [Fintype T] [DecidableEq T] (t : SimpleGraph T) (ht : t.Connected)
    (hac : t.IsAcyclic) : ∀ n : ℕ, ∀ (S : Finset V) (X : T → Finset V), S.card = n → 3 ≤ n →
      (∀ s, X s ⊆ S) → (∀ v ∈ S, ∃ s, v ∈ X s) → (∀ s, (X s).card ≤ 4) → PathProp t X →
      ∃ H, TT H S ∧ ∀ s, ∀ a ∈ X s, ∀ b ∈ X s, a ≠ b → H.Adj a b := by
  intro n
  induction n with
  | zero => intro S X _ h3; omega
  | succ n ih =>
    intro S X hSn h3 hXS hcov h4 hp
    rcases Nat.lt_or_ge n 3 with hn | hn
    · -- `|S| = 3`
      have hS3 : S.card = 3 := by omega
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS3
      refine ⟨tri x y z, ⟨x, y, z, TTb.base x y z hxy hyz hxz⟩, ?_⟩
      intro s a ha b hb hab
      have ha' := hXS s ha
      have hb' := hXS s hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      rw [tri_adj]
      refine ⟨hab, ?_⟩
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;> simp_all
    · obtain ⟨u0, hu0⟩ : S.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨s1, hs1⟩ := hcov u0 hu0
      obtain ⟨v, s0, hvs0, hsimp⟩ := exists_simplicial t ht hac X hp ⟨s1, ⟨u0, hs1⟩⟩
      have hvS : v ∈ S := hXS s0 hvs0
      set X' : T → Finset V := fun s => (X s).erase v with hX'
      have hS'n : (S.erase v).card = n := by
        rw [Finset.card_erase_of_mem hvS]; omega
      have hp' : PathProp t X' := by
        intro s s' s'' p hpth hmem a ha
        simp only [hX', Finset.mem_inter, Finset.mem_erase] at ha ⊢
        exact ⟨ha.1.1, hp s s' s'' p hpth hmem (Finset.mem_inter.mpr ⟨ha.1.2, ha.2.2⟩)⟩
      obtain ⟨H', ⟨x, y, z, hH'⟩, hcl'⟩ := ih (S.erase v) X' hS'n hn
        (fun s => Finset.erase_subset_erase v (hXS s))
        (by
          intro a ha
          obtain ⟨hav, haS⟩ := Finset.mem_erase.mp ha
          obtain ⟨s, hs⟩ := hcov a haS
          exact ⟨s, Finset.mem_erase.mpr ⟨hav, hs⟩⟩)
        (fun s => (Finset.card_erase_le).trans (h4 s)) hp'
      have hK3 : ((X s0).erase v).card ≤ 3 := by
        rw [Finset.card_erase_of_mem hvs0]; have := h4 s0; omega
      obtain ⟨p, q, r, hpq, hqr, hpr, hK⟩ := hH'.clique_in_tri ((X s0).erase v)
        (Finset.erase_subset_erase v (hXS s0)) hK3 (hcl' s0)
      have hpS := (hH'.supp p q hpq).1
      have hqS := (hH'.supp q r hqr).1
      have hrS := (hH'.supp q r hqr).2
      have hvS' : v ∉ S.erase v := Finset.notMem_erase v S
      have hT := TTb.stack v p q r hH' hvS' hpS hqS hrS hpq hqr hpr
      rw [Finset.insert_erase hvS] at hT
      refine ⟨H' ⊔ star3 v p q r, ⟨x, y, z, hT⟩, ?_⟩
      have hvp : v ≠ p := fun h => hvS' (h ▸ hpS)
      have hvq : v ≠ q := fun h => hvS' (h ▸ hqS)
      have hvr : v ≠ r := fun h => hvS' (h ▸ hrS)
      have hstar : ∀ b, b ∈ (X s0).erase v → (H' ⊔ star3 v p q r).Adj v b := by
        intro b hb
        have hb' := hK hb
        have hbv : b ≠ v := (Finset.mem_erase.mp hb).1
        rw [SimpleGraph.sup_adj, star3_adj]
        right
        refine ⟨Ne.symm hbv, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
        rcases hb' with rfl | rfl | rfl <;> simp
      intro s a ha b hb hab
      by_cases hav : a = v
      · subst hav
        exact hstar b (Finset.mem_erase.mpr ⟨Ne.symm hab, hsimp s ha hb⟩)
      by_cases hbv : b = v
      · subst hbv
        exact (hstar a (Finset.mem_erase.mpr ⟨hav, hsimp s hb ha⟩)).symm
      exact (le_sup_left : H' ≤ H' ⊔ star3 v p q r)
        (hcl' s a (Finset.mem_erase.mpr ⟨hav, ha⟩) b (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab)

/-- C1: a graph of tree-width at most 3 supported on `S` with `|S| ≥ 3` is a subgraph of a 3-tree
on `S`. -/
theorem c1_tw {S : Finset V} {G : SimpleGraph V} (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (h3 : 3 ≤ S.card) (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3) :
    ∃ H, G ≤ H ∧ TT H S := by
  classical
  obtain ⟨T, _, t, X, ⟨htree, hcov, hedge, hpath⟩, hw⟩ := htw
  set X2 : T → Finset V := fun s => X s ∩ S with hX2
  have hp2 : PathProp t X2 := by
    intro s s' s'' p hpth hmem a ha
    simp only [hX2, Finset.mem_inter] at ha ⊢
    exact ⟨hpath s s' s'' p hpth hmem (Finset.mem_inter.mpr ⟨ha.1.1, ha.2.1⟩), ha.1.2⟩
  obtain ⟨H, hT, hcl⟩ := c1_core t htree.connected htree.isAcyclic S.card S X2 rfl h3
    (fun s => Finset.inter_subset_right)
    (by
      intro v hv
      obtain ⟨s, hs⟩ := hcov v
      exact ⟨s, Finset.mem_inter.mpr ⟨hs, hv⟩⟩)
    (fun s => (Finset.card_le_card Finset.inter_subset_left).trans (hw s)) hp2
  refine ⟨H, ?_, hT⟩
  intro a b hab
  obtain ⟨s, has, hbs⟩ := hedge a b hab
  obtain ⟨haS, hbS⟩ := hsupp a b hab
  exact hcl s a (Finset.mem_inter.mpr ⟨has, haS⟩) b (Finset.mem_inter.mpr ⟨hbs, hbS⟩) hab.ne

end C1

end PQL5

/-! Apollonian toolkit (session 3): stacking into a face keeps `TriCond`, the new triangles are
faces, gluing two 3-trees along a common triangle, small supports satisfy `TriCond`. -/

namespace PQL5

section Apoll

variable {V : Type} [DecidableEq V]

theorem In3_cover {p q r a b c : V} (ha : In3 p q r a) (hb : In3 p q r b) (hc : In3 p q r c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) : ∀ u, In3 p q r u → In3 a b c u := by
  intro u hu
  unfold In3 at *
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;> simp_all

theorem adj_of_In3 {H : SimpleGraph V} {y a b c u : V} (ha : H.Adj y a) (hb : H.Adj y b)
    (hc : H.Adj y c) (hu : In3 a b c u) : H.Adj y u := by
  rcases hu with rfl | rfl | rfl <;> assumption

theorem star3_adj_of_In3 {v p q r s : V} (hvs : v ≠ s) (hs : In3 p q r s) :
    (star3 v p q r).Adj v s := by
  rw [star3_adj]
  refine ⟨hvs, ?_⟩
  rcases hs with rfl | rfl | rfl <;> simp

/-- neighbours of a freshly stacked vertex -/
theorem stack_nbr {H : SimpleGraph V} {v p q r : V} (hv : ∀ u, ¬ H.Adj v u)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r) :
    ∀ u, (H ⊔ star3 v p q r).Adj v u → In3 p q r u := by
  intro u h
  rw [SimpleGraph.sup_adj, star3_adj] at h
  rcases h with h | ⟨_, h⟩
  · exact absurd h (hv u)
  · unfold In3
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact absurd h hvp
    · exact Or.inr (Or.inl h)
    · exact absurd h hvq
    · exact Or.inr (Or.inr h)
    · exact absurd h hvr

theorem stack_old {H : SimpleGraph V} {v p q r : V} :
    ∀ s t, (H ⊔ star3 v p q r).Adj s t → s ≠ v → t ≠ v → H.Adj s t := by
  intro s t h hs ht
  rw [SimpleGraph.sup_adj, star3_adj] at h
  rcases h with h | ⟨_, h⟩
  · exact h
  · exfalso
    rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;>
      first | exact hs h | exact ht h

/-- Stacking a new vertex into a face keeps the Apollonian condition. -/
theorem triCond_stack {H : SimpleGraph V} {v p q r : V} (hT : TriCond H) (hF : Face H p q r)
    (hv : ∀ u, ¬ H.Adj v u) : TriCond (H ⊔ star3 v p q r) := by
  have hvp : v ≠ p := fun h => hv q (h ▸ hF.1)
  have hvq : v ≠ q := fun h => hv r (h ▸ hF.2.1)
  have hvr : v ≠ r := fun h => hv p (h ▸ hF.2.2.1.symm)
  have hN := stack_nbr hv hvp hvq hvr
  have hN' : ∀ u, (H ⊔ star3 v p q r).Adj u v → In3 p q r u := fun u h => hN u h.symm
  have hH := @stack_old V _ H v p q r
  have hpq : p ≠ q := hF.1.ne
  have hqr : q ≠ r := hF.2.1.ne
  have hpr : p ≠ r := hF.2.2.1.ne
  -- a common neighbour equal to `v`
  have hcom : ∀ a b c w y' z' : V, a ≠ b → b ≠ c → a ≠ c → a ≠ v → b ≠ v → c ≠ v →
      w = v → y' ≠ z' → y' ≠ v → z' ≠ v →
      (H ⊔ star3 v p q r).Adj w a → (H ⊔ star3 v p q r).Adj w b →
      (H ⊔ star3 v p q r).Adj w c →
      (H ⊔ star3 v p q r).Adj y' a → (H ⊔ star3 v p q r).Adj y' b →
      (H ⊔ star3 v p q r).Adj y' c →
      (H ⊔ star3 v p q r).Adj z' a → (H ⊔ star3 v p q r).Adj z' b →
      (H ⊔ star3 v p q r).Adj z' c → False := by
    intro a b c w y' z' hab hbc hac hav hbv hcv hw hyz hyv hzv hwa hwb hwc hya hyb hyc hza hzb hzc
    rw [hw] at hwa hwb hwc
    have hcov := In3_cover (hN a hwa) (hN b hwb) (hN c hwc) hab hbc hac
    have h1 := hH y' a hya hyv hav
    have h2 := hH y' b hyb hyv hbv
    have h3 := hH y' c hyc hyv hcv
    have h4 := hH z' a hza hzv hav
    have h5 := hH z' b hzb hzv hbv
    have h6 := hH z' c hzc hzv hcv
    exact hF.2.2.2 y' z' hyz (adj_of_In3 h1 h2 h3 (hcov p (Or.inl rfl)))
      (adj_of_In3 h1 h2 h3 (hcov q (Or.inr (Or.inl rfl))))
      (adj_of_In3 h1 h2 h3 (hcov r (Or.inr (Or.inr rfl))))
      (adj_of_In3 h4 h5 h6 (hcov p (Or.inl rfl)))
      (adj_of_In3 h4 h5 h6 (hcov q (Or.inr (Or.inl rfl))))
      (adj_of_In3 h4 h5 h6 (hcov r (Or.inr (Or.inr rfl))))
  intro a b c x y z hab hbc hac hxy hyz hxz hxa hxb hxc hya hyb hyc hza hzb hzc
  by_cases ha : a = v
  · rw [ha] at hab hac hxa hya
    exact four_of_three (hN b hab) (hN c hac) (hN' x hxa) (hN' y hya) hbc.ne (Ne.symm hxb.ne)
      (Ne.symm hyb.ne) (Ne.symm hxc.ne) (Ne.symm hyc.ne) hxy
  by_cases hb : b = v
  · rw [hb] at hab hbc hxb hyb
    exact four_of_three (hN a hab.symm) (hN c hbc) (hN' x hxb) (hN' y hyb) hac.ne
      (Ne.symm hxa.ne) (Ne.symm hya.ne) (Ne.symm hxc.ne) (Ne.symm hyc.ne) hxy
  by_cases hc : c = v
  · rw [hc] at hac hbc hxc hyc
    exact four_of_three (hN a hac.symm) (hN b hbc.symm) (hN' x hxc) (hN' y hyc) hab.ne
      (Ne.symm hxa.ne) (Ne.symm hya.ne) (Ne.symm hxb.ne) (Ne.symm hyb.ne) hxy
  by_cases hx : x = v
  · exact hcom a b c x y z hab.ne hbc.ne hac.ne ha hb hc hx hyz (fun h => hxy (hx.trans h.symm))
      (fun h => hxz (hx.trans h.symm)) hxa hxb hxc hya hyb hyc hza hzb hzc
  by_cases hy : y = v
  · exact hcom a b c y x z hab.ne hbc.ne hac.ne ha hb hc hy hxz (fun h => hxy (h.trans hy.symm))
      (fun h => hyz (hy.trans h.symm)) hya hyb hyc hxa hxb hxc hza hzb hzc
  by_cases hz : z = v
  · exact hcom a b c z x y hab.ne hbc.ne hac.ne ha hb hc hz hxy (fun h => hxz (h.trans hz.symm))
      (fun h => hyz (h.trans hz.symm)) hza hzb hzc hxa hxb hxc hya hyb hyc
  exact hT a b c x y z (hH a b hab ha hb) (hH b c hbc hb hc) (hH a c hac ha hc) hxy hyz hxz
    (hH x a hxa hx ha) (hH x b hxb hx hb) (hH x c hxc hx hc) (hH y a hya hy ha)
    (hH y b hyb hy hb) (hH y c hyc hy hc) (hH z a hza hz ha) (hH z b hzb hz hb) (hH z c hzc hz hc)

/-- The triangles through a freshly stacked vertex are faces. -/
theorem face_stack {H : SimpleGraph V} {v p q r s t : V} (hv : ∀ u, ¬ H.Adj v u)
    (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r) (hs : In3 p q r s) (ht : In3 p q r t)
    (hst : H.Adj s t) : Face (H ⊔ star3 v p q r) v s t := by
  have hN := stack_nbr hv hvp hvq hvr
  have hvs : v ≠ s := by rcases hs with rfl | rfl | rfl <;> assumption
  have hvt : v ≠ t := by rcases ht with rfl | rfl | rfl <;> assumption
  have hle : star3 v p q r ≤ H ⊔ star3 v p q r := le_sup_right
  refine ⟨hle (star3_adj_of_In3 hvs hs), (le_sup_left : H ≤ _) hst,
    hle (star3_adj_of_In3 hvt ht), ?_⟩
  intro w w' hww' hwv hws hwt hw'v hw's hw't
  exact four_of_three hs ht (hN w hwv.symm) (hN w' hw'v.symm) hst.ne (Ne.symm hws.ne)
    (Ne.symm hw's.ne) (Ne.symm hwt.ne) (Ne.symm hw't.ne) hww'

/-- Gluing a 3-tree grown from `a b c` onto another 3-tree containing the triangle `a b c`,
the two supports meeting only in `a, b, c`. -/
theorem TTb.glue3 {H1 : SimpleGraph V} {S1 : Finset V} {a b c : V} (h : TTb H1 S1 a b c) :
    ∀ {H2 : SimpleGraph V} {S2 : Finset V}, TT H2 S2 → H2.Adj a b → H2.Adj b c → H2.Adj a c →
      (∀ u ∈ S1, u ∈ S2 → In3 a b c u) → TT (H1 ⊔ H2) (S1 ∪ S2) := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro H2 S2 hT2 h1 h2 h3 _
    obtain ⟨x0, y0, z0, hT2'⟩ := hT2
    have hsupp := hT2'.supp
    have heq : tri x y z ⊔ H2 = H2 := by
      apply sup_eq_right.mpr
      intro u w huw
      obtain ⟨hu, hw⟩ := tri_In3_of_adj huw
      unfold In3 at hu hw
      rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
        first | exact absurd rfl huw.ne | assumption | exact SimpleGraph.Adj.symm (by assumption)
    have hS : ({x, y, z} : Finset V) ∪ S2 = S2 := by
      apply Finset.union_eq_right.mpr
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact (hsupp _ _ h1).1
      · exact (hsupp _ _ h2).1
      · exact (hsupp _ _ h3).2
    rw [heq, hS]
    exact ⟨x0, y0, z0, hT2'⟩
  | @stack H S x y z v p q r hH hvS hp hq hr hpq hqr hpr ih =>
    intro H2 S2 hT2 h1 h2 h3 hint
    obtain ⟨x0, y0, z0, hK⟩ := ih hT2 h1 h2 h3
      (fun u hu hu2 => hint u (Finset.mem_insert_of_mem hu) hu2)
    have hb := hH.base_mem
    have hv : v ∉ S ∪ S2 := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact hvS h
      · have := hint v (Finset.mem_insert_self v S) h
        rcases this with rfl | rfl | rfl
        · exact hvS hb.1
        · exact hvS hb.2.1
        · exact hvS hb.2.2.1
    have hle : H ≤ H ⊔ H2 := le_sup_left
    have hT := TTb.stack v p q r hK hv (Finset.mem_union_left _ hp) (Finset.mem_union_left _ hq)
      (Finset.mem_union_left _ hr) (hle hpq) (hle hqr) (hle hpr)
    refine ⟨x0, y0, z0, ?_⟩
    have e1 : H ⊔ star3 v p q r ⊔ H2 = H ⊔ H2 ⊔ star3 v p q r := sup_right_comm _ _ _
    have e2 : insert v S ∪ S2 = insert v (S ∪ S2) := Finset.insert_union _ _ _
    rw [e1, e2]
    exact hT

/-- Gluing two Apollonian graphs along a triangle that is a face of both keeps `TriCond`. -/
theorem triCond_glue3 {H1 H2 : SimpleGraph V} {S1 S2 : Finset V} {a b c : V}
    (hT1 : TriCond H1) (hT2 : TriCond H2)
    (hs1 : ∀ u w, H1.Adj u w → u ∈ S1 ∧ w ∈ S1) (hs2 : ∀ u w, H2.Adj u w → u ∈ S2 ∧ w ∈ S2)
    (hint : ∀ u ∈ S1, u ∈ S2 → In3 a b c u) (hF1 : Face H1 a b c) (hF2 : Face H2 a b c) :
    TriCond (H1 ⊔ H2) := by
  have hab : a ≠ b := hF1.1.ne
  have hbc : b ≠ c := hF1.2.1.ne
  have hac : a ≠ c := hF1.2.2.1.ne
  have htri1 : ∀ u w, In3 a b c u → In3 a b c w → u ≠ w → H1.Adj u w := by
    intro u w hu hw huw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | exact hF1.1 | exact hF1.2.1 | exact hF1.2.2.1 |
        exact hF1.1.symm | exact hF1.2.1.symm | exact hF1.2.2.1.symm
  have htri2 : ∀ u w, In3 a b c u → In3 a b c w → u ≠ w → H2.Adj u w := by
    intro u w hu hw huw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | exact hF2.1 | exact hF2.2.1 | exact hF2.2.2.1 |
        exact hF2.1.symm | exact hF2.2.1.symm | exact hF2.2.2.1.symm
  -- edges between vertices of one side
  have side1 : ∀ u w, u ∈ S1 → w ∈ S1 → (H1 ⊔ H2).Adj u w → H1.Adj u w := by
    intro u w hu hw h
    rcases h with h | h
    · exact h
    · have := hs2 u w h
      exact htri1 u w (hint u hu this.1) (hint w hw this.2) h.ne
  have side2 : ∀ u w, u ∈ S2 → w ∈ S2 → (H1 ⊔ H2).Adj u w → H2.Adj u w := by
    intro u w hu hw h
    rcases h with h | h
    · have := hs1 u w h
      exact htri2 u w (hint u this.1 hu) (hint w this.2 hw) h.ne
    · exact h
  -- a neighbour of a vertex lying on one side only lies on that side
  have nb1 : ∀ u w, u ∈ S1 → u ∉ S2 → (H1 ⊔ H2).Adj u w → w ∈ S1 := by
    intro u w hu hu2 h
    rcases h with h | h
    · exact (hs1 u w h).2
    · exact absurd (hs2 u w h).1 hu2
  have nb2 : ∀ u w, u ∈ S2 → u ∉ S1 → (H1 ⊔ H2).Adj u w → w ∈ S2 := by
    intro u w hu hu1 h
    rcases h with h | h
    · exact absurd (hs1 u w h).1 hu1
    · exact (hs2 u w h).2
  have mem : ∀ u w, (H1 ⊔ H2).Adj u w → u ∈ S1 ∨ u ∈ S2 := by
    intro u w h
    rcases h with h | h
    · exact Or.inl (hs1 u w h).1
    · exact Or.inr (hs2 u w h).1
  intro u1 u2 u3 x y z h12 h23 h13 hxy hyz hxz hx1 hx2 hx3 hy1 hy2 hy3 hz1 hz2 hz3
  -- all six on side 1
  have all1 : u1 ∈ S1 → u2 ∈ S1 → u3 ∈ S1 → x ∈ S1 → y ∈ S1 → z ∈ S1 → False := by
    intro a1 a2 a3 ax ay az
    exact hT1 u1 u2 u3 x y z (side1 _ _ a1 a2 h12) (side1 _ _ a2 a3 h23) (side1 _ _ a1 a3 h13)
      hxy hyz hxz (side1 _ _ ax a1 hx1) (side1 _ _ ax a2 hx2) (side1 _ _ ax a3 hx3)
      (side1 _ _ ay a1 hy1) (side1 _ _ ay a2 hy2) (side1 _ _ ay a3 hy3)
      (side1 _ _ az a1 hz1) (side1 _ _ az a2 hz2) (side1 _ _ az a3 hz3)
  have all2 : u1 ∈ S2 → u2 ∈ S2 → u3 ∈ S2 → x ∈ S2 → y ∈ S2 → z ∈ S2 → False := by
    intro a1 a2 a3 ax ay az
    exact hT2 u1 u2 u3 x y z (side2 _ _ a1 a2 h12) (side2 _ _ a2 a3 h23) (side2 _ _ a1 a3 h13)
      hxy hyz hxz (side2 _ _ ax a1 hx1) (side2 _ _ ax a2 hx2) (side2 _ _ ax a3 hx3)
      (side2 _ _ ay a1 hy1) (side2 _ _ ay a2 hy2) (side2 _ _ ay a3 hy3)
      (side2 _ _ az a1 hz1) (side2 _ _ az a2 hz2) (side2 _ _ az a3 hz3)
  -- a vertex `u_i` on side 1 only forces everything onto side 1
  have hm1 := mem u1 u2 h12
  have hm2 := mem u2 u3 h23
  have hm3 := mem u3 u1 h13.symm
  by_cases c11 : u1 ∈ S1 ∧ u1 ∉ S2
  · have a2 := nb1 u1 u2 c11.1 c11.2 h12
    have a3 := nb1 u1 u3 c11.1 c11.2 h13
    exact all1 c11.1 a2 a3 (nb1 u1 x c11.1 c11.2 hx1.symm) (nb1 u1 y c11.1 c11.2 hy1.symm)
      (nb1 u1 z c11.1 c11.2 hz1.symm)
  by_cases c12 : u1 ∈ S2 ∧ u1 ∉ S1
  · have a2 := nb2 u1 u2 c12.1 c12.2 h12
    have a3 := nb2 u1 u3 c12.1 c12.2 h13
    exact all2 c12.1 a2 a3 (nb2 u1 x c12.1 c12.2 hx1.symm) (nb2 u1 y c12.1 c12.2 hy1.symm)
      (nb2 u1 z c12.1 c12.2 hz1.symm)
  by_cases c21 : u2 ∈ S1 ∧ u2 ∉ S2
  · have a1 := nb1 u2 u1 c21.1 c21.2 h12.symm
    have a3 := nb1 u2 u3 c21.1 c21.2 h23
    exact all1 a1 c21.1 a3 (nb1 u2 x c21.1 c21.2 hx2.symm) (nb1 u2 y c21.1 c21.2 hy2.symm)
      (nb1 u2 z c21.1 c21.2 hz2.symm)
  by_cases c22 : u2 ∈ S2 ∧ u2 ∉ S1
  · have a1 := nb2 u2 u1 c22.1 c22.2 h12.symm
    have a3 := nb2 u2 u3 c22.1 c22.2 h23
    exact all2 a1 c22.1 a3 (nb2 u2 x c22.1 c22.2 hx2.symm) (nb2 u2 y c22.1 c22.2 hy2.symm)
      (nb2 u2 z c22.1 c22.2 hz2.symm)
  by_cases c31 : u3 ∈ S1 ∧ u3 ∉ S2
  · have a1 := nb1 u3 u1 c31.1 c31.2 h13.symm
    have a2 := nb1 u3 u2 c31.1 c31.2 h23.symm
    exact all1 a1 a2 c31.1 (nb1 u3 x c31.1 c31.2 hx3.symm) (nb1 u3 y c31.1 c31.2 hy3.symm)
      (nb1 u3 z c31.1 c31.2 hz3.symm)
  by_cases c32 : u3 ∈ S2 ∧ u3 ∉ S1
  · have a1 := nb2 u3 u1 c32.1 c32.2 h13.symm
    have a2 := nb2 u3 u2 c32.1 c32.2 h23.symm
    exact all2 a1 a2 c32.1 (nb2 u3 x c32.1 c32.2 hx3.symm) (nb2 u3 y c32.1 c32.2 hy3.symm)
      (nb2 u3 z c32.1 c32.2 hz3.symm)
  -- all of `u1 u2 u3` are shared, hence are `a b c`
  have b1 : u1 ∈ S1 ∧ u1 ∈ S2 := by
    rcases hm1 with h | h
    · exact ⟨h, by_contra fun h' => c11 ⟨h, h'⟩⟩
    · exact ⟨by_contra fun h' => c12 ⟨h, h'⟩, h⟩
  have b2 : u2 ∈ S1 ∧ u2 ∈ S2 := by
    rcases hm2 with h | h
    · exact ⟨h, by_contra fun h' => c21 ⟨h, h'⟩⟩
    · exact ⟨by_contra fun h' => c22 ⟨h, h'⟩, h⟩
  have b3 : u3 ∈ S1 ∧ u3 ∈ S2 := by
    rcases hm3 with h | h
    · exact ⟨h, by_contra fun h' => c31 ⟨h, h'⟩⟩
    · exact ⟨by_contra fun h' => c32 ⟨h, h'⟩, h⟩
  have i1 := hint u1 b1.1 b1.2
  have i2 := hint u2 b2.1 b2.2
  have i3 := hint u3 b3.1 b3.2
  have hcov := In3_cover i1 i2 i3 h12.ne h23.ne h13.ne
  -- each common neighbour is a common neighbour of `a b c` on one side
  have hsidew : ∀ w, (H1 ⊔ H2).Adj w u1 → (H1 ⊔ H2).Adj w u2 → (H1 ⊔ H2).Adj w u3 →
      (H1.Adj w a ∧ H1.Adj w b ∧ H1.Adj w c) ∨ (H2.Adj w a ∧ H2.Adj w b ∧ H2.Adj w c) := by
    intro w hw1 hw2 hw3
    rcases mem w u1 hw1 with hwS | hwS
    · by_cases hw2' : w ∈ S2
      · exfalso
        have hi := hint w hwS hw2'
        have hiu := hcov w hi
        rcases hiu with rfl | rfl | rfl
        · exact hw1.ne rfl
        · exact hw2.ne rfl
        · exact hw3.ne rfl
      · left
        have e1 := side1 w u1 hwS b1.1 hw1
        have e2 := side1 w u2 hwS b2.1 hw2
        have e3 := side1 w u3 hwS b3.1 hw3
        exact ⟨adj_of_In3 e1 e2 e3 (hcov a (Or.inl rfl)),
          adj_of_In3 e1 e2 e3 (hcov b (Or.inr (Or.inl rfl))),
          adj_of_In3 e1 e2 e3 (hcov c (Or.inr (Or.inr rfl)))⟩
    · by_cases hw1' : w ∈ S1
      · exfalso
        have hi := hint w hw1' hwS
        have hiu := hcov w hi
        rcases hiu with rfl | rfl | rfl
        · exact hw1.ne rfl
        · exact hw2.ne rfl
        · exact hw3.ne rfl
      · right
        have e1 := side2 w u1 hwS b1.2 hw1
        have e2 := side2 w u2 hwS b2.2 hw2
        have e3 := side2 w u3 hwS b3.2 hw3
        exact ⟨adj_of_In3 e1 e2 e3 (hcov a (Or.inl rfl)),
          adj_of_In3 e1 e2 e3 (hcov b (Or.inr (Or.inl rfl))),
          adj_of_In3 e1 e2 e3 (hcov c (Or.inr (Or.inr rfl)))⟩
  have sx := hsidew x hx1 hx2 hx3
  have sy := hsidew y hy1 hy2 hy3
  have sz := hsidew z hz1 hz2 hz3
  rcases sx with sx | sx <;> rcases sy with sy | sy <;> rcases sz with sz | sz
  · exact hF1.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2
  · exact hF1.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2
  · exact hF1.2.2.2 x z hxz sx.1 sx.2.1 sx.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF2.2.2.2 y z hyz sy.1 sy.2.1 sy.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF1.2.2.2 y z hyz sy.1 sy.2.1 sy.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF2.2.2.2 x z hxz sx.1 sx.2.1 sx.2.2 sz.1 sz.2.1 sz.2.2
  · exact hF2.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2
  · exact hF2.2.2.2 x y hxy sx.1 sx.2.1 sx.2.2 sy.1 sy.2.1 sy.2.2

/-- A graph supported on at most five vertices satisfies `TriCond` (a violation needs six). -/
theorem triCond_small {H : SimpleGraph V} {S : Finset V} (hs : ∀ u w, H.Adj u w → u ∈ S ∧ w ∈ S)
    (h5 : S.card ≤ 5) : TriCond H := by
  intro a b c x y z hab hbc hac hxy hyz hxz hxa hxb hxc hya hyb hyc hza hzb hzc
  have hsub : ({a, b, c, x, y, z} : Finset V) ⊆ S := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hs _ _ hab).1
    · exact (hs _ _ hbc).1
    · exact (hs _ _ hac).2
    · exact (hs _ _ hxa).1
    · exact (hs _ _ hya).1
    · exact (hs _ _ hza).1
  have h6 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hab.ne, hac.ne, Ne.symm hxa.ne, Ne.symm hya.ne, Ne.symm hza.ne⟩),
    Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hbc.ne, Ne.symm hxb.ne, Ne.symm hyb.ne, Ne.symm hzb.ne⟩),
    Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hxc.ne, Ne.symm hyc.ne, Ne.symm hzc.ne⟩),
    Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxy, hxz⟩),
    Finset.card_pair hyz] at h6
  omega

end Apoll

end PQL5

/-! C2 toolkit A (session 3): face permutations, stacking an Apollonian graph into a face,
gluing two Apollonian graphs along 0, 1 or 2 shared vertices (Kratochvil-Vaner gluing steps,
done by stacking), and tree-width transfer lemmas. -/

namespace PQL5

section C2a

variable {V : Type} [DecidableEq V]

theorem Face.perm {H : SimpleGraph V} {x y z a b c : V} (h : Face H x y z) (ha : In3 x y z a)
    (hb : In3 x y z b) (hc : In3 x y z c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Face H a b c := by
  have hcov := In3_cover ha hb hc hab hbc hac
  have hadj : ∀ u w, In3 x y z u → In3 x y z w → u ≠ w → H.Adj u w := by
    intro u w hu hw huw
    rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
      first | exact absurd rfl huw | exact h.1 | exact h.2.1 | exact h.2.2.1 |
        exact h.1.symm | exact h.2.1.symm | exact h.2.2.1.symm
  refine ⟨hadj a b ha hb hab, hadj b c hb hc hbc, hadj a c ha hc hac, ?_⟩
  intro p q hpq hpa hpb hpc hqa hqb hqc
  exact h.2.2.2 p q hpq (adj_of_In3 hpa hpb hpc (hcov x (Or.inl rfl)))
    (adj_of_In3 hpa hpb hpc (hcov y (Or.inr (Or.inl rfl))))
    (adj_of_In3 hpa hpb hpc (hcov z (Or.inr (Or.inr rfl))))
    (adj_of_In3 hqa hqb hqc (hcov x (Or.inl rfl)))
    (adj_of_In3 hqa hqb hqc (hcov y (Or.inr (Or.inl rfl))))
    (adj_of_In3 hqa hqb hqc (hcov z (Or.inr (Or.inr rfl))))

/-- Stack a new vertex into a face of an Apollonian graph. -/
theorem stack_ap {H : SimpleGraph V} {S : Finset V} {v p q r : V} (hT : TT H S) (hC : TriCond H)
    (hF : Face H p q r) (hv : v ∉ S) :
    TT (H ⊔ star3 v p q r) (insert v S) ∧ TriCond (H ⊔ star3 v p q r) ∧
      (∀ s t, In3 p q r s → In3 p q r t → H.Adj s t → Face (H ⊔ star3 v p q r) v s t) := by
  obtain ⟨x, y, z, hb⟩ := hT
  have hs := hb.supp
  have hp : p ∈ S := (hs p q hF.1).1
  have hq : q ∈ S := (hs p q hF.1).2
  have hr : r ∈ S := (hs q r hF.2.1).2
  have hnv : ∀ u, ¬ H.Adj v u := fun u h => hv (hs v u h).1
  have hvp : v ≠ p := fun h => hv (h ▸ hp)
  have hvq : v ≠ q := fun h => hv (h ▸ hq)
  have hvr : v ≠ r := fun h => hv (h ▸ hr)
  exact ⟨⟨x, y, z, TTb.stack v p q r hb hv hp hq hr hF.1 hF.2.1 hF.2.2.1⟩,
    triCond_stack hC hF hnv, fun s t hs' ht' hst => face_stack hnv hvp hvq hvr hs' ht' hst⟩

theorem glue_face3 {H1 H2 : SimpleGraph V} {A B : Finset V} {a b c : V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (hF1 : Face H1 a b c)
    (hF2 : Face H2 a b c) (hint : ∀ u ∈ A, u ∈ B → In3 a b c u) :
    TT (H1 ⊔ H2) (A ∪ B) ∧ TriCond (H1 ⊔ H2) := by
  obtain ⟨x, y, z, hb1⟩ := hT1
  have hb1' := hb1.reroot a b c hF1.1 hF1.2.1 hF1.2.2.1
  refine ⟨hb1'.glue3 hT2 hF2.1 hF2.2.1 hF2.2.2.1 hint, ?_⟩
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  exact triCond_glue3 hC1 hC2 hb1.supp hb2.supp hint hF1 hF2

theorem TTb.vertex_face {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z)
    (u : V) (hu : u ∈ S) : ∃ w t, Face H u w t := by
  obtain ⟨p, q, r, hpq, hqr, hpr, hK⟩ := h.clique_in_tri {u} (by simpa using hu) (by simp)
    (by
      intro a ha b hb hab
      rw [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab)
  have hu' : u ∈ ({p, q, r} : Finset V) := hK (Finset.mem_singleton_self u)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
  rcases hu' with rfl | rfl | rfl
  · obtain ⟨t, ht⟩ := h.edge_face _ _ hpq
    exact ⟨_, t, ht⟩
  · obtain ⟨t, ht⟩ := h.edge_face _ _ hqr
    exact ⟨_, t, ht⟩
  · obtain ⟨t, ht⟩ := h.edge_face _ _ hpr.symm
    exact ⟨_, t, ht⟩

/-- Glue two Apollonian graphs sharing exactly an edge `a b`. -/
theorem glue_sep2 {H1 H2 : SimpleGraph V} {A B : Finset V} {a b : V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (h1 : H1.Adj a b) (h2 : H2.Adj a b)
    (hint : ∀ u ∈ A, u ∈ B → u = a ∨ u = b) :
    ∃ H, H1 ⊔ H2 ≤ H ∧ TT H (A ∪ B) ∧ TriCond H := by
  obtain ⟨x1, y1, z1, hb1⟩ := hT1
  obtain ⟨c1, hF1⟩ := hb1.edge_face a b h1
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  obtain ⟨x, hF2⟩ := hb2.edge_face a b h2
  have hc1A : c1 ∈ A := (hb1.supp b c1 hF1.2.1).2
  have hbc1 : b ≠ c1 := hF1.2.1.ne
  have hac1 : a ≠ c1 := hF1.2.2.1.ne
  have hc1B : c1 ∉ B := by
    intro h
    rcases hint c1 hc1A h with h' | h'
    · exact hac1 h'.symm
    · exact hbc1 h'.symm
  obtain ⟨hT2', hC2', hfn⟩ := stack_ap ⟨x2, y2, z2, hb2⟩ hC2 hF2 hc1B
  have hF2' := hfn a b (Or.inl rfl) (Or.inr (Or.inl rfl)) h2
  have hF2'' : Face (H2 ⊔ star3 c1 a b x) a b c1 :=
    hF2'.perm (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl) h2.ne hbc1 hac1
  have hint' : ∀ u ∈ A, u ∈ insert c1 B → In3 a b c1 u := by
    intro u hu hu'
    rw [Finset.mem_insert] at hu'
    rcases hu' with h | hu'
    · exact Or.inr (Or.inr h)
    · rcases hint u hu hu' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  obtain ⟨hT, hC⟩ := glue_face3 ⟨x1, y1, z1, hb1⟩ hC1 hT2' hC2' hF1 hF2'' hint'
  refine ⟨H1 ⊔ (H2 ⊔ star3 c1 a b x), sup_le_sup_left le_sup_left _, ?_, hC⟩
  have e : A ∪ insert c1 B = A ∪ B := by
    rw [Finset.union_insert, Finset.insert_eq_of_mem (Finset.mem_union_left _ hc1A)]
  rw [← e]
  exact hT

/-- Glue two Apollonian graphs sharing exactly one vertex `a`. -/
theorem glue_sep1 {H1 H2 : SimpleGraph V} {A B : Finset V} {a : V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (ha1 : a ∈ A) (ha2 : a ∈ B)
    (hint : ∀ u ∈ A, u ∈ B → u = a) :
    ∃ H, H1 ⊔ H2 ≤ H ∧ TT H (A ∪ B) ∧ TriCond H := by
  obtain ⟨x1, y1, z1, hb1⟩ := hT1
  obtain ⟨b1, c1, hF1⟩ := hb1.vertex_face a ha1
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  obtain ⟨x, y, hF2⟩ := hb2.vertex_face a ha2
  have hb1A : b1 ∈ A := (hb1.supp a b1 hF1.1).2
  have hc1A : c1 ∈ A := (hb1.supp b1 c1 hF1.2.1).2
  have hab1 : a ≠ b1 := hF1.1.ne
  have hbc1 : b1 ≠ c1 := hF1.2.1.ne
  have hac1 : a ≠ c1 := hF1.2.2.1.ne
  have hb1B : b1 ∉ B := fun h => hab1 (hint b1 hb1A h).symm
  have hc1B : c1 ∉ B := fun h => hac1 (hint c1 hc1A h).symm
  obtain ⟨hTa, hCa, hfa⟩ := stack_ap ⟨x2, y2, z2, hb2⟩ hC2 hF2 hb1B
  have hFa := hfa a x (Or.inl rfl) (Or.inr (Or.inl rfl)) hF2.1
  have hc1B' : c1 ∉ insert b1 B := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hbc1 h.symm
    · exact hc1B h
  obtain ⟨hTb, hCb, hfb⟩ := stack_ap hTa hCa hFa hc1B'
  have hFb := hfb b1 a (Or.inl rfl) (Or.inr (Or.inl rfl)) hFa.1
  have hFb' := hFb.perm (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) hab1 hbc1 hac1
  have hint' : ∀ u ∈ A, u ∈ insert c1 (insert b1 B) → In3 a b1 c1 u := by
    intro u hu hu'
    rw [Finset.mem_insert, Finset.mem_insert] at hu'
    rcases hu' with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (hint u hu h)
  obtain ⟨hT, hC⟩ := glue_face3 ⟨x1, y1, z1, hb1⟩ hC1 hTb hCb hF1 hFb' hint'
  refine ⟨_, sup_le_sup_left (le_sup_left.trans le_sup_left) _, ?_, hC⟩
  have e : A ∪ insert c1 (insert b1 B) = A ∪ B := by
    rw [Finset.union_insert, Finset.union_insert,
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hb1A),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hc1A)]
  rw [← e]
  exact hT

/-- Glue two Apollonian graphs with disjoint supports. -/
theorem glue_sep0 {H1 H2 : SimpleGraph V} {A B : Finset V} (hT1 : TT H1 A)
    (hC1 : TriCond H1) (hT2 : TT H2 B) (hC2 : TriCond H2) (hint : ∀ u ∈ A, u ∉ B) :
    ∃ H, H1 ⊔ H2 ≤ H ∧ TT H (A ∪ B) ∧ TriCond H := by
  obtain ⟨x1, y1, z1, hb1⟩ := hT1
  obtain ⟨c1, hF1⟩ := hb1.edge_face x1 y1 hb1.base_mem.2.2.2.1
  obtain ⟨x2, y2, z2, hb2⟩ := hT2
  obtain ⟨z, hF2⟩ := hb2.edge_face x2 y2 hb2.base_mem.2.2.2.1
  have ha1A : x1 ∈ A := hb1.base_mem.1
  have hb1A : y1 ∈ A := hb1.base_mem.2.1
  have hc1A : c1 ∈ A := (hb1.supp y1 c1 hF1.2.1).2
  have hab1 : x1 ≠ y1 := hF1.1.ne
  have hbc1 : y1 ≠ c1 := hF1.2.1.ne
  have hac1 : x1 ≠ c1 := hF1.2.2.1.ne
  obtain ⟨hTa, hCa, hfa⟩ := stack_ap ⟨x2, y2, z2, hb2⟩ hC2 hF2 (hint x1 ha1A)
  have hFa := hfa x2 y2 (Or.inl rfl) (Or.inr (Or.inl rfl)) hF2.1
  have hb1B : y1 ∉ insert x1 B := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hab1 h.symm
    · exact hint y1 hb1A h
  obtain ⟨hTb, hCb, hfb⟩ := stack_ap hTa hCa hFa hb1B
  have hFb := hfb x1 x2 (Or.inl rfl) (Or.inr (Or.inl rfl)) hFa.1
  have hc1B : c1 ∉ insert y1 (insert x1 B) := by
    rw [Finset.mem_insert, Finset.mem_insert]
    rintro (h | h | h)
    · exact hbc1 h.symm
    · exact hac1 h.symm
    · exact hint c1 hc1A h
  obtain ⟨hTc, hCc, hfc⟩ := stack_ap hTb hCb hFb hc1B
  have hFc := hfc y1 x1 (Or.inl rfl) (Or.inr (Or.inl rfl)) hFb.1
  have hFc' := hFc.perm (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) hab1 hbc1 hac1
  have hint' : ∀ u ∈ A, u ∈ insert c1 (insert y1 (insert x1 B)) → In3 x1 y1 c1 u := by
    intro u hu hu'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert] at hu'
    rcases hu' with h | h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact absurd h (hint u hu)
  obtain ⟨hT, hC⟩ := glue_face3 ⟨x1, y1, z1, hb1⟩ hC1 hTc hCc hF1 hFc' hint'
  refine ⟨_, sup_le_sup_left ((le_sup_left.trans le_sup_left).trans le_sup_left) _, ?_, hC⟩
  have e : A ∪ insert c1 (insert y1 (insert x1 B)) = A ∪ B := by
    rw [Finset.union_insert, Finset.union_insert, Finset.union_insert,
      Finset.insert_eq_of_mem (Finset.mem_union_left _ ha1A),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hb1A),
      Finset.insert_eq_of_mem (Finset.mem_union_left _ hc1A)]
  rw [← e]
  exact hT

/-- Tree-width transfer: a decomposition of `G` serves any graph whose edges are edges of `G`
or lie in a common bag. -/
theorem tw_transfer {T : Type} [Fintype T] {G G' : SimpleGraph V} {t : SimpleGraph T}
    {X : T → Finset V} (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G t X)
    (hw : ∀ s, (X s).card ≤ 3 + 1)
    (h : ∀ x y, G'.Adj x y → G.Adj x y ∨ ∃ s, x ∈ X s ∧ y ∈ X s) :
    RobertsonSeymour1986.GM5.TreewidthLE G' 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := htd
  refine ⟨T, inferInstance, t, X, ⟨h1, h2, ?_, h4⟩, hw⟩
  intro x y hxy
  rcases h x y hxy with h' | h'
  · exact h3 x y h'
  · exact h'

theorem tw_mono {G G' : SimpleGraph V} (hle : G' ≤ G)
    (h : RobertsonSeymour1986.GM5.TreewidthLE G 3) : RobertsonSeymour1986.GM5.TreewidthLE G' 3 := by
  obtain ⟨T, hT, t, X, htd, hw⟩ := h
  exact tw_transfer htd hw (fun x y hxy => Or.inl (hle hxy))

end C2a

end PQL5

/-! C2 toolkit B (session 3): SEP — in a 3-tree, a triangle with two common neighbours `p, q`
separates `p` from `q` (stated with a closed predicate: no walk from `p` to `q` avoids it). -/

namespace PQL5

section C2b

variable {V : Type} [DecidableEq V]

theorem TTb.sep {H : SimpleGraph V} {S : Finset V} {x y z : V} (h : TTb H S x y z) :
    ∀ a b c p q : V, H.Adj a b → H.Adj b c → H.Adj a c → p ≠ q → H.Adj p a → H.Adj p b →
      H.Adj p c → H.Adj q a → H.Adj q b → H.Adj q c →
      ∃ P : V → Prop, P p ∧ ¬ P q ∧
        ∀ u w, P u → ¬ In3 a b c u → H.Adj u w → ¬ In3 a b c w → P w := by
  induction h with
  | base x y z hxy hyz hxz =>
    intro a b c p q hab hbc hac hpq hpa hpb hpc _ _ _
    exfalso
    exact four_of_three (tri_In3_of_adj hab).1 (tri_In3_of_adj hab).2 (tri_In3_of_adj hbc).2
      (tri_In3_of_adj hpa).1 hab.ne hac.ne (Ne.symm hpa.ne) hbc.ne (Ne.symm hpb.ne)
      (Ne.symm hpc.ne)
  | @stack H S x y z v p0 q0 r0 hH hvS hp0 hq0 hr0 hpq0 hqr0 hpr0 ih =>
    intro a b c p q hab hbc hac hpq hpa hpb hpc hqa hqb hqc
    have hs := hH.supp
    have hnv : ∀ u, ¬ H.Adj v u := fun u h => hvS (hs v u h).1
    have hvp : v ≠ p0 := fun h => hvS (h ▸ hp0)
    have hvq : v ≠ q0 := fun h => hvS (h ▸ hq0)
    have hvr : v ≠ r0 := fun h => hvS (h ▸ hr0)
    have hN := stack_nbr hnv hvp hvq hvr
    have hN' : ∀ u, (H ⊔ star3 v p0 q0 r0).Adj u v → In3 p0 q0 r0 u := fun u h => hN u h.symm
    have hO := @stack_old V _ H v p0 q0 r0
    by_cases ha : a = v
    · exfalso
      rw [ha] at hab hac hpa hqa
      exact four_of_three (hN b hab) (hN c hac) (hN' p hpa) (hN' q hqa) hbc.ne
        (Ne.symm hpb.ne) (Ne.symm hqb.ne) (Ne.symm hpc.ne) (Ne.symm hqc.ne) hpq
    by_cases hb : b = v
    · exfalso
      rw [hb] at hab hbc hpb hqb
      exact four_of_three (hN a hab.symm) (hN c hbc) (hN' p hpb) (hN' q hqb) hac.ne
        (Ne.symm hpa.ne) (Ne.symm hqa.ne) (Ne.symm hpc.ne) (Ne.symm hqc.ne) hpq
    by_cases hc : c = v
    · exfalso
      rw [hc] at hac hbc hpc hqc
      exact four_of_three (hN a hac.symm) (hN b hbc.symm) (hN' p hpc) (hN' q hqc) hab.ne
        (Ne.symm hpa.ne) (Ne.symm hqa.ne) (Ne.symm hpb.ne) (Ne.symm hqb.ne) hpq
    by_cases hp : p = v
    · have hcov := In3_cover (hN a (hp ▸ hpa)) (hN b (hp ▸ hpb)) (hN c (hp ▸ hpc))
        hab.ne hbc.ne hac.ne
      refine ⟨fun u => u = v, hp, fun h => hpq (hp.trans h.symm), ?_⟩
      intro u w hu _ huw hw
      exact (hw (hcov w (hN w (hu ▸ huw)))).elim
    by_cases hq : q = v
    · have hcov := In3_cover (hN a (hq ▸ hqa)) (hN b (hq ▸ hqb)) (hN c (hq ▸ hqc))
        hab.ne hbc.ne hac.ne
      refine ⟨fun u => u ≠ v, hp, fun h => h hq, ?_⟩
      intro u w _ hu' huw _ hwv
      apply hu'
      rw [hwv] at huw
      exact hcov u (hN' u huw)
    obtain ⟨P, hPp, hPq, hPc⟩ := ih a b c p q (hO a b hab ha hb) (hO b c hbc hb hc)
      (hO a c hac ha hc) hpq (hO p a hpa hp ha) (hO p b hpb hp hb) (hO p c hpc hp hc)
      (hO q a hqa hq ha) (hO q b hqb hq hb) (hO q c hqc hq hc)
    have hF : ∀ s t, In3 p0 q0 r0 s → In3 p0 q0 r0 t → s ≠ t → H.Adj s t := by
      intro s t hs' ht' hst
      rcases hs' with rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl <;>
        first | exact absurd rfl hst | exact hpq0 | exact hqr0 | exact hpr0 |
          exact hpq0.symm | exact hqr0.symm | exact hpr0.symm
    refine ⟨fun u => (u ≠ v ∧ P u) ∨ (u = v ∧ ∃ s, In3 p0 q0 r0 s ∧ ¬ In3 a b c s ∧ P s),
      Or.inl ⟨hp, hPp⟩, ?_, ?_⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hPq h
      · exact hq h
    · intro u w hu hu' huw hw
      by_cases hwv : w = v
      · right
        refine ⟨hwv, ?_⟩
        rw [hwv] at huw
        rcases hu with ⟨_, hPu⟩ | ⟨huv, _⟩
        · exact ⟨u, hN' u huw, hu', hPu⟩
        · exact absurd huv huw.ne
      · left
        refine ⟨hwv, ?_⟩
        rcases hu with ⟨huv, hPu⟩ | ⟨huv, s, hsF, hsT, hPs⟩
        · exact hPc u w hPu hu' (hO u w huw huv hwv) hw
        · rw [huv] at huw
          have hwF := hN w huw
          by_cases hsw : s = w
          · rw [← hsw]
            exact hPs
          · exact hPc s w hPs hsT (hF s w hsF hwF hsw) hw

end C2b

end PQL5

/-! C2 toolkit C (session 3): minors of subgraphs. -/

namespace PQL5

theorem minor_of_le {W V : Type} {K : SimpleGraph W} {G G' : SimpleGraph V} (hle : G' ≤ G)
    (hm : RobertsonSeymour1986.GM5.IsMinor K G') : RobertsonSeymour1986.GM5.IsMinor K G := by
  obtain ⟨β, h1, h2, h3⟩ := hm
  refine ⟨β, fun w => ⟨(h1 w).1, (h1 w).2.mono (fun a b h => hle h)⟩, h2, ?_⟩
  intro a b hab
  obtain ⟨x, hx, y, hy, hxy⟩ := h3 a b hab
  exact ⟨x, hx, y, hy, hle hxy⟩

end PQL5

/-! C2 toolkit D (session 4): set contraction, K33 from three sets, components, splits. -/

namespace PQL5

open RobertsonSeymour1986.GM5

abbrev KK33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

theorem connected_of_le_on {V : Type} {G G2 : SimpleGraph V} {s : Set V}
    (hc : (G2.induce s).Connected) (h : ∀ x y, x ∈ s → y ∈ s → G2.Adj x y → G.Adj x y) :
    (G.induce s).Connected := by
  refine hc.mono ?_
  intro u w huw
  have := h u w u.2 w.2 (by simpa using huw)
  simpa using this

theorem induce_singleton_conn {V : Type} (G : SimpleGraph V) (v : V) :
    (G.induce ({v} : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  have : y = v := hy
  subst this
  exact SimpleGraph.Reachable.refl _

/-- **Set contraction.** Contracting a connected set `C` (adjacent to `a`) into `a`. -/
theorem minor_contract {W V : Type} (K : SimpleGraph W) (hKiso : ∀ w, ∃ w', K.Adj w w')
    (G G2 : SimpleGraph V) (C : Set V) (a : V) (hC : (G.induce C).Connected)
    (hac : ∃ c ∈ C, G.Adj a c)
    (hG2 : ∀ x y, G2.Adj x y → x ∉ C ∧ y ∉ C ∧ (G.Adj x y ∨ (x = a ∧ ∃ c ∈ C, G.Adj c y) ∨
      (y = a ∧ ∃ c ∈ C, G.Adj c x)))
    (hm : IsMinor K G2) : IsMinor K G := by
  classical
  obtain ⟨β, hβ, hpw, hadj⟩ := hm
  have hCβ : ∀ w, ∀ x ∈ β w, x ∉ C := by
    intro w x hx hxC
    obtain ⟨w', hww'⟩ := hKiso w
    obtain ⟨x', hx', y, _, hxy⟩ := hadj w w' hww'
    have hall : ∀ y ∈ β w, y = x :=
      induce_closed (hβ w).2 (fun y => y = x) hx rfl
        (fun u y _ _ huy hu => absurd (show u ∈ C by rw [hu]; exact hxC) (hG2 u y huy).1)
    have hx'C : x' ∈ C := by rw [hall x' hx']; exact hxC
    exact (hG2 x' y hxy).1 hx'C
  have hdis : ∀ p q x, x ∈ β p → x ∈ β q → p = q := by
    intro p q x hp hq
    by_contra hne
    exact Set.disjoint_left.1 (hpw hne) hp hq
  obtain ⟨c0, hc0, hac0⟩ := hac
  have hsub : ∀ w, β w ⊆ (if a ∈ β w then β w ∪ C else β w) := by
    intro w
    split_ifs
    · exact Set.subset_union_left
    · exact le_rfl
  refine ⟨fun w => if a ∈ β w then β w ∪ C else β w, ?_, ?_, ?_⟩
  · intro w
    refine ⟨(hβ w).1.mono (hsub w), ?_⟩
    show (G.induce (if a ∈ β w then β w ∪ C else β w)).Connected
    by_cases haw : a ∈ β w
    · rw [if_pos haw]
      have haU : a ∈ β w ∪ C := Or.inl haw
      have hCr : ∀ y ∈ C, ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩ := by
        refine induce_closed hC (fun y => ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩) hc0 ?_ ?_
        · exact ⟨Or.inr hc0, SimpleGraph.Adj.reachable (by simpa using hac0)⟩
        · rintro x y _ hy hxy ⟨_, hr⟩
          exact ⟨Or.inr hy, hr.trans (SimpleGraph.Adj.reachable (by simpa using hxy))⟩
      have hβr : ∀ y ∈ β w, ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩ := by
        refine induce_closed (hβ w).2 (fun y => ∃ hy : y ∈ β w ∪ C,
          (G.induce (β w ∪ C)).Reachable ⟨a, haU⟩ ⟨y, hy⟩) haw
          ⟨haU, SimpleGraph.Reachable.refl _⟩ ?_
        rintro x y _ hy hxy ⟨_, hr⟩
        refine ⟨Or.inl hy, ?_⟩
        rcases (hG2 x y hxy).2.2 with h | ⟨_, c, hc, hcy⟩ | ⟨hya, _⟩
        · exact hr.trans (SimpleGraph.Adj.reachable (by simpa using h))
        · obtain ⟨_, hr'⟩ := hCr c hc
          exact hr'.trans (SimpleGraph.Adj.reachable (by simpa using hcy))
        · subst hya
          exact SimpleGraph.Reachable.refl _
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨a, haU⟩, ?_⟩
      rintro ⟨y, hy⟩
      rcases hy with h | h
      · exact (hβr y h).2
      · exact (hCr y h).2
    · rw [if_neg haw]
      refine connected_of_le_on (hβ w).2 (fun x y hx hy hxy => ?_)
      rcases (hG2 x y hxy).2.2 with h | ⟨hxa, _⟩ | ⟨hya, _⟩
      · exact h
      · exact absurd (hxa ▸ hx) haw
      · exact absurd (hya ▸ hy) haw
  · intro p q hpq
    show Disjoint (if a ∈ β p then β p ∪ C else β p) (if a ∈ β q then β q ∪ C else β q)
    have hpq0 := hpw hpq
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hx1 : x ∈ β p ∨ (a ∈ β p ∧ x ∈ C) := by
      split_ifs at hxp with h
      · rcases hxp with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
      · exact Or.inl hxp
    have hx2 : x ∈ β q ∨ (a ∈ β q ∧ x ∈ C) := by
      split_ifs at hxq with h
      · rcases hxq with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
      · exact Or.inl hxq
    rcases hx1 with h1 | ⟨ha1, hc1⟩ <;> rcases hx2 with h2 | ⟨ha2, hc2⟩
    · exact Set.disjoint_left.1 hpq0 h1 h2
    · exact hCβ p x h1 hc2
    · exact hCβ q x h2 hc1
    · exact hpq (hdis p q a ha1 ha2)
  · intro p q hpq
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj p q hpq
    rcases (hG2 x y hxy).2.2 with h | ⟨hxa, c, hc, hcy⟩ | ⟨hya, c, hc, hcx⟩
    · exact ⟨x, hsub p hx, y, hsub q hy, h⟩
    · have hap : a ∈ β p := hxa ▸ hx
      refine ⟨c, ?_, y, hsub q hy, hcy⟩
      show c ∈ (if a ∈ β p then β p ∪ C else β p)
      rw [if_pos hap]
      exact Or.inr hc
    · have haq : a ∈ β q := hya ▸ hy
      refine ⟨x, hsub p hx, c, ?_, hcx.symm⟩
      show c ∈ (if a ∈ β q then β q ∪ C else β q)
      rw [if_pos haq]
      exact Or.inr hc

/-- Three disjoint connected sets each seeing all of `a, b, c` give a `K₃,₃` minor. -/
theorem K33_of_three {V : Type} (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (D : Fin 3 → Set V) (hD : ∀ i, (D i).Nonempty ∧ (G.induce (D i)).Connected)
    (hDd : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (hDT : ∀ i, a ∉ D i ∧ b ∉ D i ∧ c ∉ D i)
    (hsee : ∀ i, (∃ x ∈ D i, G.Adj a x) ∧ (∃ x ∈ D i, G.Adj b x) ∧ (∃ x ∈ D i, G.Adj c x)) :
    IsMinor KK33 G := by
  let f : Fin 3 → V := ![a, b, c]
  have hf : ∀ i j, f i = f j → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hfD : ∀ i j, f i ∉ D j := by
    intro i j
    fin_cases i <;> simp [f, hDT j]
  have hfs : ∀ i j, ∃ x ∈ D j, G.Adj (f i) x := by
    intro i j
    fin_cases i
    · exact (hsee j).1
    · exact (hsee j).2.1
    · exact (hsee j).2.2
  refine ⟨fun w => Sum.elim (fun i => ({f i} : Set V)) D w, ?_, ?_, ?_⟩
  · rintro (i | j)
    · exact ⟨Set.singleton_nonempty _, induce_singleton_conn G (f i)⟩
    · exact hD j
  · rintro (i | i) (j | j) hij
    · have : i ≠ j := fun h => hij (by rw [h])
      simp only [Sum.elim_inl, Set.disjoint_singleton]
      exact fun h => this (hf i j h)
    · simp only [Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_left]
      exact hfD i j
    · simp only [Sum.elim_inl, Sum.elim_inr, Set.disjoint_singleton_right]
      exact hfD j i
    · exact hDd i j (fun h => hij (by rw [h]))
  · rintro (i | i) (j | j) hij
    · simp at hij
    · obtain ⟨x, hx, hxa⟩ := hfs i j
      exact ⟨f i, rfl, x, hx, hxa⟩
    · obtain ⟨x, hx, hxa⟩ := hfs j i
      exact ⟨x, hx, f j, rfl, hxa.symm⟩
    · simp at hij

/-- reachability inside `R` -/
def reachR {V : Type} (G : SimpleGraph V) (R : Finset V) : V → V → Prop :=
  Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∈ R ∧ y ∈ R)

theorem reachR_symm {V : Type} {G : SimpleGraph V} {R : Finset V} {x y : V}
    (h : reachR G R x y) : reachR G R y x := by
  unfold reachR at *
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.1.symm, hbc.2.2, hbc.2.1⟩ ih

theorem reachR_trans {V : Type} {G : SimpleGraph V} {R : Finset V} {x y z : V}
    (h : reachR G R x y) (h' : reachR G R y z) : reachR G R x z := by
  unfold reachR at *
  exact h.trans h'

open Classical in
/-- the component of `x` in `G[R]` -/
noncomputable def compR {V : Type} (G : SimpleGraph V) (R : Finset V) (x : V) : Finset V :=
  R.filter (fun y => reachR G R x y)

open Classical in
theorem compR_mem {V : Type} {G : SimpleGraph V} {R : Finset V} {x y : V} :
    y ∈ compR G R x ↔ y ∈ R ∧ reachR G R x y := by
  unfold compR
  rw [Finset.mem_filter]

theorem compR_sub {V : Type} {G : SimpleGraph V} {R : Finset V} {x : V} : compR G R x ⊆ R :=
  fun _ h => (compR_mem.1 h).1

theorem compR_self {V : Type} {G : SimpleGraph V} {R : Finset V} {x : V} (hx : x ∈ R) :
    x ∈ compR G R x := compR_mem.2 ⟨hx, Relation.ReflTransGen.refl⟩

theorem compR_closed {V : Type} {G : SimpleGraph V} {R : Finset V} {x y w : V}
    (hy : y ∈ compR G R x) (hw : w ∈ R) (hyw : G.Adj y w) : w ∈ compR G R x := by
  rw [compR_mem] at hy ⊢
  exact ⟨hw, Relation.ReflTransGen.tail hy.2 ⟨hyw, hy.1, hw⟩⟩

theorem compR_conn {V : Type} {G : SimpleGraph V} {R : Finset V} {x : V} (hx : x ∈ R) :
    (G.induce (↑(compR G R x) : Set V)).Connected := by
  have hxm : x ∈ (↑(compR G R x) : Set V) := compR_self hx
  have key : ∀ z, reachR G R x z → ∃ hz : z ∈ (↑(compR G R x) : Set V),
      (G.induce (↑(compR G R x) : Set V)).Reachable ⟨x, hxm⟩ ⟨z, hz⟩ := by
    intro z hz
    unfold reachR at hz
    induction hz with
    | refl => exact ⟨hxm, SimpleGraph.Reachable.refl _⟩
    | @tail b c hb hbc ih =>
      obtain ⟨_, hr⟩ := ih
      have hcm : c ∈ (↑(compR G R x) : Set V) := compR_mem.2 ⟨hbc.2.2, hb.tail hbc⟩
      exact ⟨hcm, hr.trans (SimpleGraph.Adj.reachable (by simpa using hbc.1))⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x, hxm⟩, ?_⟩
  rintro ⟨y, hy⟩
  exact (key y (compR_mem.1 hy).2).2

theorem compR_disj {V : Type} {G : SimpleGraph V} {R : Finset V} {p q w : V} (hq : q ∈ R)
    (hpq : q ∉ compR G R p) (hwp : w ∈ compR G R p) (hwq : w ∈ compR G R q) : False :=
  hpq (compR_mem.2 ⟨hq, reachR_trans (compR_mem.1 hwp).2 (reachR_symm (compR_mem.1 hwq).2)⟩)

/-- `G` restricted to `A` -/
def res {V : Type} (G : SimpleGraph V) (A : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

theorem res_le {V : Type} {G : SimpleGraph V} {A : Finset V} : res G A ≤ G :=
  fun _ _ h => h.1

theorem card_lt_of_out {V : Type} {A S : Finset V} (h : A ⊆ S) {w : V} (hw : w ∈ S)
    (hwA : w ∉ A) : A.card < S.card :=
  Finset.card_lt_card ⟨h, fun h' => hwA (h' hw)⟩

theorem three_le_card {V : Type} {A : Finset V} {x y z : V} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ A.card := by
  have : 2 < A.card := Finset.two_lt_card.2 ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  omega

/-- the induction hypothesis of C2 -/
def C2IH (V : Type) [DecidableEq V] (n : ℕ) : Prop :=
  ∀ (S' : Finset V) (G' : SimpleGraph V), S'.card < n → (∀ x y, G'.Adj x y → x ∈ S' ∧ y ∈ S') →
    3 ≤ S'.card → TreewidthLE G' 3 → ¬ IsMinor KK33 G' → ∃ H, G' ≤ H ∧ TT H S' ∧ TriCond H

end PQL5

/-! C2 toolkit E (session 4): separations and the degree-3 step. -/

namespace PQL5

open RobertsonSeymour1986.GM5

theorem res_adj {V : Type} {G : SimpleGraph V} {A : Finset V} {x y : V} :
    (res G A).Adj x y ↔ G.Adj x y ∧ x ∈ A ∧ y ∈ A := Iff.rfl

theorem K33_of_three' {V : Type} (G : SimpleGraph V) (a b c : V) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (D0 D1 D2 : Set V) (h0 : D0.Nonempty ∧ (G.induce D0).Connected)
    (h1 : D1.Nonempty ∧ (G.induce D1).Connected) (h2 : D2.Nonempty ∧ (G.induce D2).Connected)
    (d01 : Disjoint D0 D1) (d02 : Disjoint D0 D2) (d12 : Disjoint D1 D2)
    (t0 : a ∉ D0 ∧ b ∉ D0 ∧ c ∉ D0) (t1 : a ∉ D1 ∧ b ∉ D1 ∧ c ∉ D1)
    (t2 : a ∉ D2 ∧ b ∉ D2 ∧ c ∉ D2)
    (s0 : (∃ x ∈ D0, G.Adj a x) ∧ (∃ x ∈ D0, G.Adj b x) ∧ (∃ x ∈ D0, G.Adj c x))
    (s1 : (∃ x ∈ D1, G.Adj a x) ∧ (∃ x ∈ D1, G.Adj b x) ∧ (∃ x ∈ D1, G.Adj c x))
    (s2 : (∃ x ∈ D2, G.Adj a x) ∧ (∃ x ∈ D2, G.Adj b x) ∧ (∃ x ∈ D2, G.Adj c x)) :
    IsMinor KK33 G := by
  refine K33_of_three G a b c hab hbc hac ![D0, D1, D2] ?_ ?_ ?_ ?_
  · intro i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact d01 | exact d01.symm | exact d02 | exact d02.symm | exact d12 | exact d12.symm
  · intro i; fin_cases i
    · exact t0
    · exact t1
    · exact t2
  · intro i; fin_cases i
    · exact s0
    · exact s1
    · exact s2

section C2e

variable {V : Type} [DecidableEq V]

theorem c2_split01 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2)
    (htw : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G)
    (C Y : Finset V) (hCne : C.Nonempty) (hCS : C ⊆ S) (hY : Y.card ≤ 1) (hYS : Y ⊆ S)
    (hYC : ∀ u ∈ Y, u ∉ C) (hB3 : 3 ≤ (S \ C).card) (hout : ∃ w ∈ S, w ∉ C ∧ w ∉ Y)
    (hcl : ∀ c ∈ C, ∀ w, G.Adj c w → w ∈ C ∨ w ∈ Y) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hAS : C ∪ Y ⊆ S := Finset.union_subset hCS hYS
  have hAlt : (C ∪ Y).card < S.card := by
    obtain ⟨w, hw, hwC, hwY⟩ := hout
    exact card_lt_of_out hAS hw (by rw [Finset.mem_union]; tauto)
  obtain ⟨c, hc⟩ := hCne
  have hBlt : (S \ C).card < S.card :=
    card_lt_of_out Finset.sdiff_subset (hCS hc) (fun h => (Finset.mem_sdiff.1 h).2 hc)
  have hA3 : 3 ≤ (C ∪ Y).card := by
    obtain ⟨w1, w2, h12, h1, h2⟩ := hdeg c (hCS hc)
    have m1 : w1 ∈ C ∪ Y := Finset.mem_union.2 (hcl c hc w1 h1)
    have m2 : w2 ∈ C ∪ Y := Finset.mem_union.2 (hcl c hc w2 h2)
    exact three_le_card (Finset.mem_union_left _ hc) m1 m2 (G.ne_of_adj h1) (G.ne_of_adj h2) h12
  obtain ⟨H1, h1le, hT1, hC1⟩ := hIH (C ∪ Y) (res G (C ∪ Y)) hAlt
    (fun x y h => ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩)
    hA3 (tw_mono res_le htw) (fun h => hK (minor_of_le res_le h))
  obtain ⟨H2, h2le, hT2, hC2⟩ := hIH (S \ C) (res G (S \ C)) hBlt
    (fun x y h => ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩)
    hB3 (tw_mono res_le htw) (fun h => hK (minor_of_le res_le h))
  have hcover : C ∪ Y ∪ S \ C = S := by
    ext u
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | ⟨h, _⟩)
      · exact hCS h
      · exact hYS h
      · exact h
    · intro h
      by_cases hu : u ∈ C
      · exact Or.inl (Or.inl hu)
      · exact Or.inr ⟨h, hu⟩
  have hGle : G ≤ H1 ⊔ H2 := by
    intro u w huw
    rw [SimpleGraph.sup_adj]
    by_cases hu : u ∈ C
    · exact Or.inl (h1le (res_adj.2 ⟨huw, Finset.mem_union_left _ hu,
        Finset.mem_union.2 (hcl u hu w huw)⟩))
    · by_cases hw : w ∈ C
      · exact Or.inl (h1le (res_adj.2 ⟨huw, Finset.mem_union.2 (hcl w hw u huw.symm),
          Finset.mem_union_left _ hw⟩))
      · exact Or.inr (h2le (res_adj.2 ⟨huw, Finset.mem_sdiff.2 ⟨(hsupp u w huw).1, hu⟩,
          Finset.mem_sdiff.2 ⟨(hsupp u w huw).2, hw⟩⟩))
  have fin : ∀ H, H1 ⊔ H2 ≤ H → TT H (C ∪ Y ∪ S \ C) → TriCond H →
      ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
    intro H hle hT hC
    rw [hcover] at hT
    exact ⟨H, le_trans hGle hle, hT, hC⟩
  by_cases hy : ∃ y, y ∈ Y
  · obtain ⟨y, hyY⟩ := hy
    obtain ⟨H, hle, hT, hC⟩ := glue_sep1 (a := y) hT1 hC1 hT2 hC2 (Finset.mem_union_right _ hyY)
      (Finset.mem_sdiff.2 ⟨hYS hyY, hYC y hyY⟩) (by
        intro u hu1 hu2
        have huC := (Finset.mem_sdiff.1 hu2).2
        rcases Finset.mem_union.1 hu1 with h | h
        · exact absurd h huC
        · exact Finset.card_le_one.1 hY u h y hyY)
    exact fin H hle hT hC
  · push Not at hy
    obtain ⟨H, hle, hT, hC⟩ := glue_sep0 hT1 hC1 hT2 hC2 (by
        intro u hu1 hu2
        have huC := (Finset.mem_sdiff.1 hu2).2
        rcases Finset.mem_union.1 hu1 with h | h
        · exact huC h
        · exact hy u h)
    exact fin H hle hT hC

theorem c2_split2 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hK : ¬ IsMinor KK33 G) (y z v : V) (hyz : y ≠ z)
    (htw : TreewidthLE (G ⊔ tri y z z) 3) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (C : Finset V) (hCS : C ⊆ S) (hvC : v ∉ C) (hyC : y ∉ C) (hzC : z ∉ C)
    (hCconn : (G.induce (↑C : Set V)).Connected)
    (hcl : ∀ c ∈ C, ∀ w, G.Adj c w → w ∈ C ∨ w = y ∨ w = z)
    (hsy : ∃ c ∈ C, G.Adj c y) (hsz : ∃ c ∈ C, G.Adj c z) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hvS := (hsupp v y hvy).1
  have hyS := (hsupp v y hvy).2
  have hzS := (hsupp v z hvz).2
  have hvy' := G.ne_of_adj hvy
  have hvz' := G.ne_of_adj hvz
  obtain ⟨c, hc, hcy⟩ := hsy
  have hmA : ∀ u, u ∈ C ∪ {y, z} ↔ u ∈ C ∨ u = y ∨ u = z := by
    intro u
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  have hAS : C ∪ {y, z} ⊆ S := by
    intro u hu
    rcases (hmA u).1 hu with h | h | h
    · exact hCS h
    · rw [h]; exact hyS
    · rw [h]; exact hzS
  have hAlt : (C ∪ {y, z}).card < S.card := card_lt_of_out hAS hvS (by
    rw [hmA]
    rintro (h | h | h)
    · exact hvC h
    · exact hvy' h
    · exact hvz' h)
  have hBlt : (S \ C).card < S.card :=
    card_lt_of_out Finset.sdiff_subset (hCS hc) (fun h => (Finset.mem_sdiff.1 h).2 hc)
  have hcy' : c ≠ y := fun h => hyC (h ▸ hc)
  have hcz' : c ≠ z := fun h => hzC (h ▸ hc)
  have hA3 : 3 ≤ (C ∪ {y, z}).card :=
    three_le_card ((hmA c).2 (Or.inl hc)) ((hmA y).2 (Or.inr (Or.inl rfl)))
      ((hmA z).2 (Or.inr (Or.inr rfl))) hcy' hcz' hyz
  have hB3 : 3 ≤ (S \ C).card :=
    three_le_card (Finset.mem_sdiff.2 ⟨hvS, hvC⟩) (Finset.mem_sdiff.2 ⟨hyS, hyC⟩)
      (Finset.mem_sdiff.2 ⟨hzS, hzC⟩) hvy' hvz' hyz
  have hyzA : ∀ u, In3 y z z u → u ∈ C ∪ {y, z} := by
    intro u hu
    rcases hu with h | h | h
    · exact (hmA u).2 (Or.inr (Or.inl h))
    · exact (hmA u).2 (Or.inr (Or.inr h))
    · exact (hmA u).2 (Or.inr (Or.inr h))
  have hyzB : ∀ u, In3 y z z u → u ∈ S \ C := by
    intro u hu
    rcases hu with h | h | h
    · rw [h]; exact Finset.mem_sdiff.2 ⟨hyS, hyC⟩
    · rw [h]; exact Finset.mem_sdiff.2 ⟨hzS, hzC⟩
    · rw [h]; exact Finset.mem_sdiff.2 ⟨hzS, hzC⟩
  have hG1K : ¬ IsMinor KK33 (res G (C ∪ {y, z}) ⊔ tri y z z) := by
    intro hm
    refine hK (minor_YDelta KK33 K33_triangle_free K33_no_isolated G _ v y z z hvy hvz hvz ?_ hm)
    intro x w hxw
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · have h' := res_adj.1 h
      refine ⟨?_, Or.inl h'.1⟩
      intro hxv
      rw [hxv] at h'
      rcases (hmA _).1 h'.2.1 with h1 | h1 | h1
      · exact hvC h1
      · exact hvy' h1
      · exact hvz' h1
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      refine ⟨?_, Or.inr ⟨h1, h2⟩⟩
      intro hxv
      rw [hxv] at h1
      rcases h1 with h1 | h1 | h1
      · exact hvy' h1
      · exact hvz' h1
      · exact hvz' h1
  have hG2K : ¬ IsMinor KK33 (res G (S \ C) ⊔ tri y z z) := by
    intro hm
    refine hK (minor_contract KK33 K33_no_isolated G _ (↑C) y hCconn ⟨c, hc, hcy.symm⟩ ?_ hm)
    intro x w hxw
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · have h' := res_adj.1 h
      exact ⟨(Finset.mem_sdiff.1 h'.2.1).2, (Finset.mem_sdiff.1 h'.2.2).2, Or.inl h'.1⟩
    · have hne := (tri y z z).ne_of_adj h
      obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      have hx : x = y ∨ x = z := by rcases h1 with h1 | h1 | h1 <;> tauto
      have hw : w = y ∨ w = z := by rcases h2 with h2 | h2 | h2 <;> tauto
      rcases hx with hx | hx <;> rcases hw with hw | hw
      · exact absurd (hx.trans hw.symm) hne
      · rw [hx, hw]
        exact ⟨hyC, hzC, Or.inr (Or.inl ⟨rfl, hsz⟩)⟩
      · rw [hx, hw]
        exact ⟨hzC, hyC, Or.inr (Or.inr ⟨rfl, hsz⟩)⟩
      · exact absurd (hx.trans hw.symm) hne
  obtain ⟨H1, h1le, hT1, hC1⟩ := hIH (C ∪ {y, z}) (res G (C ∪ {y, z}) ⊔ tri y z z) hAlt
    (by
      intro x w h
      rw [SimpleGraph.sup_adj] at h
      rcases h with h | h
      · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
      · exact ⟨hyzA x (tri_In3_of_adj h).1, hyzA w (tri_In3_of_adj h).2⟩)
    hA3 (tw_mono (sup_le_sup_right res_le _) htw) hG1K
  obtain ⟨H2, h2le, hT2, hC2⟩ := hIH (S \ C) (res G (S \ C) ⊔ tri y z z) hBlt
    (by
      intro x w h
      rw [SimpleGraph.sup_adj] at h
      rcases h with h | h
      · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
      · exact ⟨hyzB x (tri_In3_of_adj h).1, hyzB w (tri_In3_of_adj h).2⟩)
    hB3 (tw_mono (sup_le_sup_right res_le _) htw) hG2K
  have htyz : (tri y z z).Adj y z := tri_adj_of_In3 (Or.inl rfl) (Or.inr (Or.inl rfl)) hyz
  obtain ⟨H, hle, hT, hC⟩ := glue_sep2 (a := y) (b := z) hT1 hC1 hT2 hC2
    (h1le (by rw [SimpleGraph.sup_adj]; exact Or.inr htyz))
    (h2le (by rw [SimpleGraph.sup_adj]; exact Or.inr htyz)) (by
      intro u hu1 hu2
      rcases (hmA u).1 hu1 with h | h | h
      · exact absurd h (Finset.mem_sdiff.1 hu2).2
      · exact Or.inl h
      · exact Or.inr h)
  have hcover : C ∪ {y, z} ∪ S \ C = S := by
    ext u
    rw [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hAS h
      · exact h
    · intro h
      by_cases hu : u ∈ C
      · exact Or.inl ((hmA u).2 (Or.inl hu))
      · exact Or.inr ⟨h, hu⟩
  have hGle : G ≤ H1 ⊔ H2 := by
    intro u w huw
    rw [SimpleGraph.sup_adj]
    by_cases hu : u ∈ C
    · refine Or.inl (h1le ?_)
      rw [SimpleGraph.sup_adj]
      exact Or.inl (res_adj.2 ⟨huw, (hmA u).2 (Or.inl hu), (hmA w).2 (hcl u hu w huw)⟩)
    · by_cases hw : w ∈ C
      · refine Or.inl (h1le ?_)
        rw [SimpleGraph.sup_adj]
        exact Or.inl (res_adj.2 ⟨huw, (hmA u).2 (hcl w hw u huw.symm), (hmA w).2 (Or.inl hw)⟩)
      · refine Or.inr (h2le ?_)
        rw [SimpleGraph.sup_adj]
        exact Or.inl (res_adj.2 ⟨huw, Finset.mem_sdiff.2 ⟨(hsupp u w huw).1, hu⟩,
          Finset.mem_sdiff.2 ⟨(hsupp u w huw).2, hw⟩⟩)
  rw [hcover] at hT
  exact ⟨H, le_trans hGle hle, hT, hC⟩

/-- the separation step: `C` is a union of components of `G - {y, z}` not containing `v`. -/
theorem c2_split {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2)
    (htw0 : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G) (y z v : V) (hyz : y ≠ z)
    (htw : TreewidthLE (G ⊔ tri y z z) 3) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (C : Finset V) (hCne : C.Nonempty) (hCS : C ⊆ S) (hvC : v ∉ C) (hyC : y ∉ C) (hzC : z ∉ C)
    (hCconn : (G.induce (↑C : Set V)).Connected)
    (hcl : ∀ c ∈ C, ∀ w, G.Adj c w → w ∈ C ∨ w = y ∨ w = z) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hvS := (hsupp v y hvy).1
  have hyS := (hsupp v y hvy).2
  have hzS := (hsupp v z hvz).2
  have hvy' := G.ne_of_adj hvy
  have hvz' := G.ne_of_adj hvz
  have hB3 : 3 ≤ (S \ C).card :=
    three_le_card (Finset.mem_sdiff.2 ⟨hvS, hvC⟩) (Finset.mem_sdiff.2 ⟨hyS, hyC⟩)
      (Finset.mem_sdiff.2 ⟨hzS, hzC⟩) hvy' hvz' hyz
  by_cases hsy : ∃ c ∈ C, G.Adj c y
  · by_cases hsz : ∃ c ∈ C, G.Adj c z
    · exact c2_split2 hIH hsupp hK y z v hyz htw hvy hvz C hCS hvC hyC hzC hCconn hcl hsy hsz
    · push Not at hsz
      refine c2_split01 hIH hsupp hdeg htw0 hK C {y} hCne hCS (by simp)
        (Finset.singleton_subset_iff.2 hyS) (fun u hu => by rw [Finset.mem_singleton.1 hu]; exact hyC)
        hB3 ⟨v, hvS, hvC, by rw [Finset.mem_singleton]; exact hvy'⟩ ?_
      intro c hc w hw
      rcases hcl c hc w hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.2 h)
      · exact absurd (h ▸ hw) (hsz c hc)
  · push Not at hsy
    by_cases hsz : ∃ c ∈ C, G.Adj c z
    · refine c2_split01 hIH hsupp hdeg htw0 hK C {z} hCne hCS (by simp)
        (Finset.singleton_subset_iff.2 hzS) (fun u hu => by rw [Finset.mem_singleton.1 hu]; exact hzC)
        hB3 ⟨v, hvS, hvC, by rw [Finset.mem_singleton]; exact hvz'⟩ ?_
      intro c hc w hw
      rcases hcl c hc w hw with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hw) (hsy c hc)
      · exact Or.inr (Finset.mem_singleton.2 h)
    · push Not at hsz
      refine c2_split01 hIH hsupp hdeg htw0 hK C ∅ hCne hCS (by simp) (Finset.empty_subset _)
        (fun u hu => absurd hu (Finset.notMem_empty u)) hB3
        ⟨v, hvS, hvC, Finset.notMem_empty v⟩ ?_
      intro c hc w hw
      rcases hcl c hc w hw with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hw) (hsy c hc)
      · exact absurd (h ▸ hw) (hsz c hc)

end C2e

end PQL5

/-! C2 toolkit F (session 4): the reduction steps and the C2 induction. -/

namespace PQL5

open RobertsonSeymour1986.GM5

section C2f

variable {V : Type} [DecidableEq V]

/-- degree-3 step: `v` simplicial with `N(v) = {a, b, c}`. -/
theorem c2_deg3 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2)
    (htw0 : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G) (h4 : 4 ≤ S.card)
    (v a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hN : ∀ w, G.Adj v w ↔ In3 a b c w)
    (htw : TreewidthLE (G ⊔ tri a b c) 3) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hva : G.Adj v a := (hN a).2 (Or.inl rfl)
  have hvb : G.Adj v b := (hN b).2 (Or.inr (Or.inl rfl))
  have hvc : G.Adj v c := (hN c).2 (Or.inr (Or.inr rfl))
  have hvS := (hsupp v a hva).1
  have haS := (hsupp v a hva).2
  have hbS := (hsupp v b hvb).2
  have hcS := (hsupp v c hvc).2
  have hvT : ∀ x, In3 a b c x → x ≠ v := fun x hx h => G.ne_of_adj ((hN x).2 hx) h.symm
  have hmT : ∀ u, In3 a b c u → u ∈ S.erase v := by
    intro u hu
    refine Finset.mem_erase.2 ⟨hvT u hu, ?_⟩
    rcases hu with h | h | h
    · rw [h]; exact haS
    · rw [h]; exact hbS
    · rw [h]; exact hcS
  have hG''s : ∀ x w, (res G (S.erase v) ⊔ tri a b c).Adj x w →
      x ∈ S.erase v ∧ w ∈ S.erase v := by
    intro x w h
    rw [SimpleGraph.sup_adj] at h
    rcases h with h | h
    · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      exact ⟨hmT x h1, hmT w h2⟩
  have hG''K : ¬ IsMinor KK33 (res G (S.erase v) ⊔ tri a b c) := by
    intro hm
    refine hK (minor_YDelta KK33 K33_triangle_free K33_no_isolated G _ v a b c hva hvb hvc ?_ hm)
    intro x w hxw
    refine ⟨(Finset.mem_erase.1 (hG''s x w hxw).1).1, ?_⟩
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · exact Or.inl (res_adj.1 h).1
    · exact Or.inr (tri_In3_of_adj h)
  have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
  obtain ⟨H'', h''le, hT'', hC''⟩ := hIH (S.erase v) _ (by omega) hG''s (by omega)
    (tw_mono (sup_le_sup_right res_le _) htw) hG''K
  have hT3 : ∀ x w, In3 a b c x → In3 a b c w → x ≠ w → H''.Adj x w := by
    intro x w hx hw hxw
    exact h''le (by rw [SimpleGraph.sup_adj]; exact Or.inr (tri_adj_of_In3 hx hw hxw))
  have hab'' := hT3 a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab
  have hbc'' := hT3 b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc
  have hac'' := hT3 a c (Or.inl rfl) (Or.inr (Or.inr rfl)) hac
  have hGres : ∀ x w, G.Adj x w → x ≠ v → w ≠ v → H''.Adj x w := by
    intro x w h hx hw
    exact h''le (by rw [SimpleGraph.sup_adj]; exact Or.inl (res_adj.2 ⟨h,
      Finset.mem_erase.2 ⟨hx, (hsupp x w h).1⟩, Finset.mem_erase.2 ⟨hw, (hsupp x w h).2⟩⟩))
  by_cases hF : Face H'' a b c
  · obtain ⟨hT, hC, -⟩ := stack_ap hT'' hC'' hF (Finset.notMem_erase v S)
    rw [Finset.insert_erase hvS] at hT
    refine ⟨_, ?_, hT, hC⟩
    intro x w hxw
    rw [SimpleGraph.sup_adj]
    by_cases hx : x = v
    · rw [hx] at hxw ⊢
      exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxw) ((hN w).1 hxw))
    · by_cases hw : w = v
      · rw [hw] at hxw ⊢
        exact Or.inr ((star3_adj_of_In3 (G.ne_of_adj hxw.symm) ((hN x).1 hxw.symm)).symm)
      · exact Or.inl (hGres x w hxw hx hw)
  · have hpq : ∃ p q, p ≠ q ∧ H''.Adj p a ∧ H''.Adj p b ∧ H''.Adj p c ∧
        H''.Adj q a ∧ H''.Adj q b ∧ H''.Adj q c := by
      by_contra hno
      exact hF ⟨hab'', hbc'', hac'', fun p q hpq e1 e2 e3 e4 e5 e6 =>
        hno ⟨p, q, hpq, e1, e2, e3, e4, e5, e6⟩⟩
    obtain ⟨p, q, hpq, hpa, hpb, hpc, hqa, hqb, hqc⟩ := hpq
    obtain ⟨x0, y0, z0, hb⟩ := hT''
    obtain ⟨P, hPp, hPq, hPcl⟩ := hb.sep a b c p q hab'' hbc'' hac'' hpq hpa hpb hpc hqa hqb hqc
    have hsupp'' := hb.supp
    obtain ⟨R, hRdef⟩ : ∃ R : Finset V, R = S \ {v, a, b, c} := ⟨_, rfl⟩
    have hmR : ∀ u, u ∈ R ↔ u ∈ S ∧ u ≠ v ∧ ¬ In3 a b c u := by
      intro u
      rw [hRdef]
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, In3]
      tauto
    have hcommon : ∀ r, H''.Adj r a → H''.Adj r b → H''.Adj r c → r ∈ R := by
      intro r hra hrb hrc
      have hr := (hsupp'' r a hra).1
      refine (hmR r).2 ⟨(Finset.mem_erase.1 hr).2, (Finset.mem_erase.1 hr).1, ?_⟩
      rintro (h | h | h)
      · exact H''.ne_of_adj hra h
      · exact H''.ne_of_adj hrb h
      · exact H''.ne_of_adj hrc h
    have hpR := hcommon p hpa hpb hpc
    have hqR := hcommon q hqa hqb hqc
    have hprop : ∀ w, reachR G R p w → P w := by
      intro w hw
      unfold reachR at hw
      induction hw with
      | refl => exact hPp
      | @tail b' c' _ hst ih =>
        obtain ⟨hadj, hb'R, hc'R⟩ := hst
        have hb' := (hmR b').1 hb'R
        have hc' := (hmR c').1 hc'R
        exact hPcl b' c' ih hb'.2.2 (hGres b' c' hadj hb'.2.1 hc'.2.1) hc'.2.2
    have hqC : q ∉ compR G R p := fun h => hPq (hprop q (compR_mem.1 h).2)
    have key : ∀ r ∈ R, ∀ x y z, (∀ w, In3 a b c w ↔ In3 x y z w) → y ≠ z →
        (∀ u ∈ compR G R r, ¬ G.Adj u x) → ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
      intro r hr x y z hiff hyz hnx
      have hyT : In3 a b c y := (hiff y).2 (Or.inr (Or.inl rfl))
      have hzT : In3 a b c z := (hiff z).2 (Or.inr (Or.inr rfl))
      have htw' : TreewidthLE (G ⊔ tri y z z) 3 := by
        refine tw_mono (sup_le_sup_left ?_ _) htw
        intro u w h
        obtain ⟨h1, h2⟩ := tri_In3_of_adj h
        have m : ∀ t, In3 y z z t → In3 a b c t := by
          rintro t (h | h | h)
          · rw [h]; exact hyT
          · rw [h]; exact hzT
          · rw [h]; exact hzT
        exact tri_adj_of_In3 (m u h1) (m w h2) ((tri y z z).ne_of_adj h)
      have hnot : ∀ u ∈ compR G R r, u ∈ S ∧ u ≠ v ∧ ¬ In3 a b c u :=
        fun u hu => (hmR u).1 (compR_sub hu)
      refine c2_split hIH hsupp hdeg htw0 hK y z v hyz htw' ((hN y).2 hyT) ((hN z).2 hzT)
        (compR G R r) ⟨r, compR_self hr⟩ (fun u hu => (hnot u hu).1) (fun h => (hnot v h).2.1 rfl)
        (fun h => (hnot y h).2.2 hyT) (fun h => (hnot z h).2.2 hzT) (compR_conn hr) ?_
      intro u hu w huw
      have hu' := hnot u hu
      by_cases hwT : In3 a b c w
      · rcases (hiff w).1 hwT with h | h | h
        · rw [h] at huw
          exact absurd huw (hnx u hu)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · by_cases hwv : w = v
        · rw [hwv] at huw
          exact absurd ((hN u).1 huw.symm) hu'.2.2
        · exact Or.inl (compR_closed hu ((hmR w).2 ⟨(hsupp u w huw).2, hwv, hwT⟩) huw)
    have disp : ∀ r ∈ R, ∀ x, In3 a b c x → (∀ u ∈ compR G R r, ¬ G.Adj u x) →
        ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
      intro r hr x hx hnx
      rcases hx with h | h | h
      · rw [h] at hnx
        exact key r hr a b c (fun w => Iff.rfl) hbc hnx
      · rw [h] at hnx
        exact key r hr b a c (fun w => by unfold In3; tauto) hac hnx
      · rw [h] at hnx
        exact key r hr c a b (fun w => by unfold In3; tauto) hab hnx
    by_cases hpall : ∀ x, In3 a b c x → ∃ u ∈ compR G R p, G.Adj u x
    · by_cases hqall : ∀ x, In3 a b c x → ∃ u ∈ compR G R q, G.Adj u x
      · exfalso
        apply hK
        have sees : ∀ r, (∀ x, In3 a b c x → ∃ u ∈ compR G R r, G.Adj u x) →
            (∃ x ∈ (↑(compR G R r) : Set V), G.Adj a x) ∧
            (∃ x ∈ (↑(compR G R r) : Set V), G.Adj b x) ∧
            (∃ x ∈ (↑(compR G R r) : Set V), G.Adj c x) := by
          intro r hr
          obtain ⟨u1, hu1, e1⟩ := hr a (Or.inl rfl)
          obtain ⟨u2, hu2, e2⟩ := hr b (Or.inr (Or.inl rfl))
          obtain ⟨u3, hu3, e3⟩ := hr c (Or.inr (Or.inr rfl))
          exact ⟨⟨u1, hu1, e1.symm⟩, ⟨u2, hu2, e2.symm⟩, ⟨u3, hu3, e3.symm⟩⟩
        have notin : ∀ r, ∀ x, In3 a b c x → x ∉ (↑(compR G R r) : Set V) := by
          intro r x hx h
          exact ((hmR x).1 (compR_sub h)).2.2 hx
        have vnot : ∀ r, v ∉ (↑(compR G R r) : Set V) :=
          fun r h => ((hmR v).1 (compR_sub h)).2.1 rfl
        exact K33_of_three' G a b c hab hbc hac {v} _ _
          ⟨Set.singleton_nonempty v, induce_singleton_conn G v⟩
          ⟨⟨p, compR_self hpR⟩, compR_conn hpR⟩ ⟨⟨q, compR_self hqR⟩, compR_conn hqR⟩
          (Set.disjoint_singleton_left.2 (vnot p)) (Set.disjoint_singleton_left.2 (vnot q))
          (Set.disjoint_left.2 (fun w hwp hwq => compR_disj hqR hqC hwp hwq))
          ⟨fun h => hvT a (Or.inl rfl) h, fun h => hvT b (Or.inr (Or.inl rfl)) h,
            fun h => hvT c (Or.inr (Or.inr rfl)) h⟩
          ⟨notin p a (Or.inl rfl), notin p b (Or.inr (Or.inl rfl)), notin p c (Or.inr (Or.inr rfl))⟩
          ⟨notin q a (Or.inl rfl), notin q b (Or.inr (Or.inl rfl)), notin q c (Or.inr (Or.inr rfl))⟩
          ⟨⟨v, Set.mem_singleton v, hva.symm⟩, ⟨v, Set.mem_singleton v, hvb.symm⟩,
            ⟨v, Set.mem_singleton v, hvc.symm⟩⟩ (sees p hpall) (sees q hqall)
      · push Not at hqall
        obtain ⟨x, hx, hnx⟩ := hqall
        exact disp q hqR x hx hnx
    · push Not at hpall
      obtain ⟨x, hx, hnx⟩ := hpall
      exact disp p hpR x hx hnx

/-- degree-2 step: `v` simplicial with `N(v) = {s, t}`. -/
theorem c2_deg2 {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (hK : ¬ IsMinor KK33 G) (h4 : 4 ≤ S.card)
    (v s t : V) (hst : s ≠ t) (hN : ∀ w, G.Adj v w ↔ w = s ∨ w = t)
    (htw : TreewidthLE (G ⊔ tri s t t) 3) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hvs : G.Adj v s := (hN s).2 (Or.inl rfl)
  have hvt : G.Adj v t := (hN t).2 (Or.inr rfl)
  have hvS := (hsupp v s hvs).1
  have hsS := (hsupp v s hvs).2
  have htS := (hsupp v t hvt).2
  have hmT : ∀ u, In3 s t t u → u ∈ S.erase v := by
    intro u hu
    rcases hu with h | h | h
    · rw [h]; exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvs).symm, hsS⟩
    · rw [h]; exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvt).symm, htS⟩
    · rw [h]; exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvt).symm, htS⟩
  have hG''s : ∀ x w, (res G (S.erase v) ⊔ tri s t t).Adj x w →
      x ∈ S.erase v ∧ w ∈ S.erase v := by
    intro x w h
    rw [SimpleGraph.sup_adj] at h
    rcases h with h | h
    · exact ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      exact ⟨hmT x h1, hmT w h2⟩
  have hG''K : ¬ IsMinor KK33 (res G (S.erase v) ⊔ tri s t t) := by
    intro hm
    refine hK (minor_YDelta KK33 K33_triangle_free K33_no_isolated G _ v s t t hvs hvt hvt ?_ hm)
    intro x w hxw
    refine ⟨(Finset.mem_erase.1 (hG''s x w hxw).1).1, ?_⟩
    rw [SimpleGraph.sup_adj] at hxw
    rcases hxw with h | h
    · exact Or.inl (res_adj.1 h).1
    · exact Or.inr (tri_In3_of_adj h)
  have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
  obtain ⟨H'', h''le, hT'', hC''⟩ := hIH (S.erase v) _ (by omega) hG''s (by omega)
    (tw_mono (sup_le_sup_right res_le _) htw) hG''K
  have hst'' : H''.Adj s t := h''le (by
    rw [SimpleGraph.sup_adj]
    exact Or.inr (tri_adj_of_In3 (Or.inl rfl) (Or.inr (Or.inl rfl)) hst))
  obtain ⟨x0, y0, z0, hb⟩ := hT''
  obtain ⟨r, hF⟩ := hb.edge_face s t hst''
  obtain ⟨hT, hC, -⟩ := stack_ap ⟨x0, y0, z0, hb⟩ hC'' hF (Finset.notMem_erase v S)
  rw [Finset.insert_erase hvS] at hT
  refine ⟨_, ?_, hT, hC⟩
  have hin : ∀ w, G.Adj v w → In3 s t r w := by
    intro w hw
    rcases (hN w).1 hw with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  intro x w hxw
  rw [SimpleGraph.sup_adj]
  by_cases hx : x = v
  · rw [hx] at hxw ⊢
    exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxw) (hin w hxw))
  · by_cases hw : w = v
    · rw [hw] at hxw ⊢
      exact Or.inr ((star3_adj_of_In3 (G.ne_of_adj hxw.symm) (hin x hxw.symm)).symm)
    · exact Or.inl (h''le (by rw [SimpleGraph.sup_adj]; exact Or.inl (res_adj.2 ⟨hxw,
        Finset.mem_erase.2 ⟨hx, (hsupp x w hxw).1⟩, Finset.mem_erase.2 ⟨hw, (hsupp x w hxw).2⟩⟩)))

/-- degree-at-most-1 step at any vertex `u`. -/
theorem c2_low {S : Finset V} {G : SimpleGraph V}
    (hIH : C2IH V S.card) (hsupp : ∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S)
    (htw0 : TreewidthLE G 3) (hK : ¬ IsMinor KK33 G) (h4 : 4 ≤ S.card)
    (u : V) (huS : u ∈ S) (hlow : ∀ w1 w2, G.Adj u w1 → G.Adj u w2 → w1 = w2) :
    ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  have hcard : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem huS
  obtain ⟨H', h'le, hT', hC'⟩ := hIH (S.erase u) (res G (S.erase u)) (by omega)
    (fun x y h => ⟨(res_adj.1 h).2.1, (res_adj.1 h).2.2⟩) (by omega)
    (tw_mono res_le htw0) (fun h => hK (minor_of_le res_le h))
  obtain ⟨s, hs, hsn⟩ : ∃ s ∈ S.erase u, ∀ w, G.Adj u w → w = s := by
    by_cases hn : ∃ w, G.Adj u w
    · obtain ⟨w, hw⟩ := hn
      exact ⟨w, Finset.mem_erase.2 ⟨(G.ne_of_adj hw).symm, (hsupp u w hw).2⟩,
        fun w' hw' => hlow w' w hw' hw⟩
    · push Not at hn
      obtain ⟨s, hs⟩ : (S.erase u).Nonempty := Finset.card_pos.1 (by omega)
      exact ⟨s, hs, fun w hw => absurd hw (hn w)⟩
  obtain ⟨x0, y0, z0, hb⟩ := hT'
  obtain ⟨w, t, hF⟩ := hb.vertex_face s hs
  obtain ⟨hT, hC, -⟩ := stack_ap ⟨x0, y0, z0, hb⟩ hC' hF (Finset.notMem_erase u S)
  rw [Finset.insert_erase huS] at hT
  refine ⟨_, ?_, hT, hC⟩
  intro x y hxy
  rw [SimpleGraph.sup_adj]
  by_cases hx : x = u
  · rw [hx] at hxy ⊢
    have e := hsn y hxy
    rw [e] at hxy ⊢
    exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxy) (Or.inl rfl))
  · by_cases hy : y = u
    · rw [hy] at hxy ⊢
      have e := hsn x hxy.symm
      rw [e] at hxy ⊢
      exact Or.inr (star3_adj_of_In3 (G.ne_of_adj hxy.symm) (Or.inl rfl)).symm
    · exact Or.inl (h'le (res_adj.2 ⟨hxy, Finset.mem_erase.2 ⟨hx, (hsupp x y hxy).1⟩,
        Finset.mem_erase.2 ⟨hy, (hsupp x y hxy).2⟩⟩))

end C2f

/-- **C2** by strong induction on `|S|`. -/
theorem c2_main : ∀ (n : ℕ) {V : Type} [DecidableEq V] (S : Finset V) (G : SimpleGraph V),
    S.card = n → (∀ x y, G.Adj x y → x ∈ S ∧ y ∈ S) → 3 ≤ S.card → TreewidthLE G 3 →
    ¬ IsMinor KK33 G → ∃ H, G ≤ H ∧ TT H S ∧ TriCond H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ S G hn hsupp h3 htw hK
  have hIH : C2IH V S.card := by
    intro S' G' hlt hs' h3' htw' hK'
    exact ih S'.card (hn ▸ hlt) S' G' rfl hs' h3' htw' hK'
  by_cases h5 : S.card ≤ 5
  · obtain ⟨H, hle, hT⟩ := c1_tw hsupp h3 htw
    obtain ⟨x0, y0, z0, hb⟩ := hT
    exact ⟨H, hle, ⟨x0, y0, z0, hb⟩, triCond_small hb.supp h5⟩
  by_cases hlow : ∃ u ∈ S, ∀ w1 w2, G.Adj u w1 → G.Adj u w2 → w1 = w2
  · obtain ⟨u, hu, hl⟩ := hlow
    exact c2_low hIH hsupp htw hK (by omega) u hu hl
  push Not at hlow
  have hdeg : ∀ u ∈ S, ∃ w1 w2, w1 ≠ w2 ∧ G.Adj u w1 ∧ G.Adj u w2 := by
    intro u hu
    obtain ⟨w1, w2, h1, h2, h12⟩ := hlow u hu
    exact ⟨w1, w2, h12, h1, h2⟩
  obtain ⟨T, hTf, t, X, htd, hw⟩ := htw
  have htd0 := htd
  obtain ⟨htree, hcov, hedge, hpath⟩ := htd
  haveI : DecidableEq T := Classical.decEq T
  have hp2 : PathProp t (fun s => X s ∩ S) := by
    intro s s' s'' p hp hs' u hu
    rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_inter] at *
    exact ⟨hpath s s' s'' p hp hs' (Finset.mem_inter.2 ⟨hu.1.1, hu.2.1⟩), hu.1.2⟩
  have hne : ∃ s, (X s ∩ S).Nonempty := by
    obtain ⟨u0, hu0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨s, hs⟩ := hcov u0
    exact ⟨s, u0, Finset.mem_inter.2 ⟨hs, hu0⟩⟩
  obtain ⟨v, s0, hv0, hsimp⟩ := exists_simplicial t htree.isConnected htree.IsAcyclic
    (fun s => X s ∩ S) hp2 hne
  have hvS : v ∈ S := (Finset.mem_inter.1 hv0).2
  have hNB : ∀ w, G.Adj v w → w ∈ (X s0 ∩ S).erase v := by
    intro w hvw
    obtain ⟨s, hvs, hws⟩ := hedge v w hvw
    have hsub := hsimp s (Finset.mem_inter.2 ⟨hvs, hvS⟩)
    exact Finset.mem_erase.2 ⟨(G.ne_of_adj hvw).symm,
      hsub (Finset.mem_inter.2 ⟨hws, (hsupp v w hvw).2⟩)⟩
  have hBX : ∀ w, w ∈ (X s0 ∩ S).erase v → w ∈ X s0 :=
    fun w h => (Finset.mem_inter.1 (Finset.mem_erase.1 h).2).1
  have hB3 : ((X s0 ∩ S).erase v).card ≤ 3 := by
    have h1 := Finset.card_erase_of_mem hv0
    have h2 : (X s0 ∩ S).card ≤ (X s0).card := Finset.card_le_card Finset.inter_subset_left
    have h3 := hw s0
    omega
  have twtri : ∀ a b c, a ∈ X s0 → b ∈ X s0 → c ∈ X s0 → TreewidthLE (G ⊔ tri a b c) 3 := by
    intro a b c ha hb hc
    refine tw_transfer htd0 hw (fun x y h => ?_)
    rw [SimpleGraph.sup_adj] at h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2⟩ := tri_In3_of_adj h
      have m : ∀ u, In3 a b c u → u ∈ X s0 := by
        rintro u (e | e | e)
        · rw [e]; exact ha
        · rw [e]; exact hb
        · rw [e]; exact hc
      exact Or.inr ⟨s0, m x h1, m y h2⟩
  obtain ⟨w1, w2, h12, hv1, hv2⟩ := hdeg v hvS
  have hm1 := hNB w1 hv1
  have hm2 := hNB w2 hv2
  by_cases hall : ∀ w ∈ (X s0 ∩ S).erase v, G.Adj v w
  · have hc2 : 2 ≤ ((X s0 ∩ S).erase v).card := by
      have : 1 < ((X s0 ∩ S).erase v).card := Finset.one_lt_card.2 ⟨w1, hm1, w2, hm2, h12⟩
      omega
    by_cases hc3 : ((X s0 ∩ S).erase v).card = 3
    · obtain ⟨a, b, c, hab, hac, hbc, hE⟩ := Finset.card_eq_three.1 hc3
      have hN : ∀ w, G.Adj v w ↔ In3 a b c w := by
        intro w
        constructor
        · intro h
          have := hNB w h
          rw [hE] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        · intro h
          apply hall
          rw [hE]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact h
      have hmem : ∀ x, In3 a b c x → x ∈ X s0 := by
        intro x hx
        apply hBX
        rw [hE]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hx
      exact c2_deg3 hIH hsupp hdeg ⟨T, hTf, t, X, htd0, hw⟩ hK (by omega) v a b c hab hbc hac hN
        (twtri a b c (hmem a (Or.inl rfl)) (hmem b (Or.inr (Or.inl rfl)))
          (hmem c (Or.inr (Or.inr rfl))))
    · have hc2' : ((X s0 ∩ S).erase v).card = 2 := by omega
      obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.1 hc2'
      have hN : ∀ w, G.Adj v w ↔ w = a ∨ w = b := by
        intro w
        constructor
        · intro h
          have := hNB w h
          rw [hE] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          exact this
        · intro h
          apply hall
          rw [hE]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          exact h
      have ha : a ∈ X s0 := hBX a (by rw [hE]; simp)
      have hb : b ∈ X s0 := hBX b (by rw [hE]; simp)
      exact c2_deg2 hIH hsupp hK (by omega) v a b hab hN (twtri a b b ha hb hb)
  · push Not at hall
    obtain ⟨b0, hb0, hnb0⟩ := hall
    have hN : ∀ w, G.Adj v w ↔ w = w1 ∨ w = w2 := by
      intro w
      constructor
      · intro h
        by_contra hne'
        push Not at hne'
        have m : ∀ x, G.Adj v x → x ∈ ((X s0 ∩ S).erase v).erase b0 := by
          intro x hx
          exact Finset.mem_erase.2 ⟨fun e => hnb0 (e ▸ hx), hNB x hx⟩
        have h3' := three_le_card (m w h) (m w1 hv1) (m w2 hv2) hne'.1 hne'.2 h12
        have := Finset.card_erase_of_mem hb0
        omega
      · rintro (h | h)
        · rw [h]; exact hv1
        · rw [h]; exact hv2
    exact c2_deg2 hIH hsupp hK (by omega) v w1 w2 h12 hN
      (twtri w1 w2 w2 (hBX w1 hm1) (hBX w2 hm2) (hBX w2 hm2))

theorem childC2_holds : ChildC2 := by
  intro V _ _ S G hsupp h3 htw hK
  exact c2_main _ S G rfl hsupp h3 htw hK

end PQL5

/-! C3 part A (session 4): abstract assembly of the 5-queue layout (Alam et al., levels + bags). -/

namespace PQL5

open PlanarQueue.Planar

section C3a

variable {V B : Type}

/-- the queue of the ordered pair `x y`: level edges `q0`, binding edges `2 + role`. -/
noncomputable def asmQ (l : V → ℕ) (bag : V → B) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (x y : V) : ℕ := by
  classical
  exact if bag x = bag y then q0 x y else if l x < l y then 2 + role x y
    else if l y < l x then 2 + role y x else 0

theorem asmQ_symm (l : V → ℕ) (bag : V → B) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (hq0s : ∀ x y, q0 x y = q0 y x) (x y : V) :
    asmQ l bag role q0 x y = asmQ l bag role q0 y x := by
  classical
  unfold asmQ
  by_cases h : bag x = bag y
  · rw [if_pos h, if_pos h.symm, hq0s]
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases h1 : l x < l y
    · rw [if_pos h1, if_neg (show ¬ l y < l x by omega), if_pos h1]
    · by_cases h2 : l y < l x
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

theorem asmQ_le (l : V → ℕ) (bag : V → B) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (hq0 : ∀ x y, q0 x y < 2) (hrole : ∀ x y, role x y < 3) (x y : V) :
    asmQ l bag role q0 x y ≤ 4 := by
  classical
  unfold asmQ
  have := hq0 x y
  have := hrole x y
  have := hrole y x
  split_ifs <;> omega

/-- **Assembly (C3a).** Levels `l`, bags (contiguous, ordered by level), level edges inside a bag
coloured by `q0` without nesting, binding edges from a vertex `y` to vertex `role` of the attachment
triangle `t (bag y)` one level up, and attachment triangles forming a coordinatewise chain in the
order of the bags give a 5-queue layout. -/
theorem assembly5 (H : SimpleGraph V) (ord : V → ℕ) (hinj : Function.Injective ord)
    (l : V → ℕ) (bag : V → B) (t : B → ℕ → V) (role : V → V → ℕ) (q0 : V → V → ℕ)
    (hq0s : ∀ x y, q0 x y = q0 y x) (hq0 : ∀ x y, q0 x y < 2) (hrole : ∀ x y, role x y < 3)
    (hedge : ∀ x y, H.Adj x y → bag x ≠ bag y →
      (l y = l x + 1 ∧ x = t (bag y) (role x y)) ∨ (l x = l y + 1 ∧ y = t (bag x) (role y x)))
    (hlev : ∀ u v, l u < l v → ord u < ord v)
    (hcont : ∀ u u' v v', bag u = bag u' → bag v = bag v' → bag u ≠ bag v → l u = l v →
      ord u < ord v → ord u' < ord v')
    (hbagl : ∀ u v, bag u = bag v → l u = l v)
    (hchain : ∀ u v, l u = l v → bag u ≠ bag v → ord u < ord v → ∀ j,
      ord (t (bag u) j) ≤ ord (t (bag v) j))
    (hin : ∀ a b c d, H.Adj a d → H.Adj b c → bag a = bag d → bag b = bag c → bag a = bag b →
      q0 a d = q0 b c → ord a < ord b → ord b < ord c → ord c < ord d → False) :
    HasQueueLayout H 5 := by
  classical
  set Q := asmQ l bag role q0 with hQdef
  have hQs : ∀ x y, Q x y = Q y x := asmQ_symm l bag role q0 hq0s
  have hQle : ∀ x y, Q x y ≤ 4 := asmQ_le l bag role q0 hq0 hrole
  -- the core: no two edges with equal `Q` nest
  have core : ∀ a b c d, H.Adj a d → H.Adj b c → Q a d = Q b c → ord a < ord b →
      ord b < ord c → ord c < ord d → False := by
    intro a b c d had hbc hQ h1 h2 h3
    have hlv : ∀ u v, ord u < ord v → l u ≤ l v := by
      intro u v h
      by_contra hc
      have := hlev v u (by omega)
      omega
    by_cases had' : bag a = bag d
    · by_cases hbc' : bag b = bag c
      · have e1 : Q a d = q0 a d := by rw [hQdef]; unfold asmQ; rw [if_pos had']
        have e2 : Q b c = q0 b c := by rw [hQdef]; unfold asmQ; rw [if_pos hbc']
        by_cases hab : bag a = bag b
        · exact hin a b c d had hbc had' hbc' hab (by rw [← e1, ← e2]; exact hQ) h1 h2 h3
        · have la := hbagl a d had'
          have lb := hbagl b c hbc'
          have lab := hlv a b h1
          have lcd := hlv c d h3
          have hle : l a = l b := by omega
          have := hcont a d b c had' hbc' hab hle h1
          omega
      · have e1 : Q a d = q0 a d := by rw [hQdef]; unfold asmQ; rw [if_pos had']
        have hb := hq0 a d
        rcases hedge b c hbc hbc' with ⟨hl, _⟩ | ⟨hl, _⟩
        · have e2 : Q b c = 2 + role b c := by
            rw [hQdef]; unfold asmQ; rw [if_neg hbc', if_pos (show l b < l c by omega)]
          omega
        · have := hlev c b (by omega)
          omega
    · rcases hedge a d had had' with ⟨hl1, ht1⟩ | ⟨hl1, _⟩
      · have e1 : Q a d = 2 + role a d := by
          rw [hQdef]; unfold asmQ; rw [if_neg had', if_pos (show l a < l d by omega)]
        by_cases hbc' : bag b = bag c
        · have e2 : Q b c = q0 b c := by rw [hQdef]; unfold asmQ; rw [if_pos hbc']
          have := hq0 b c
          omega
        · rcases hedge b c hbc hbc' with ⟨hl2, ht2⟩ | ⟨hl2, _⟩
          · have e2 : Q b c = 2 + role b c := by
              rw [hQdef]; unfold asmQ; rw [if_neg hbc', if_pos (show l b < l c by omega)]
            have hr : role a d = role b c := by omega
            have lab := hlv a b h1
            have lcd := hlv c d h3
            have hcd : l c = l d := by omega
            by_cases hcd' : bag c = bag d
            · have : a = b := by rw [ht1, ht2, hr, hcd']
              rw [this] at h1
              omega
            · have := hchain c d hcd hcd' h3 (role a d)
              rw [← ht1, hr, ← ht2] at this
              omega
          · have := hlev c b (by omega)
            omega
      · have := hlev d a (by omega)
        omega
  refine ⟨ord, fun e => ⟨min (Sym2.lift ⟨Q, hQs⟩ e.1) 4, by omega⟩, hinj, ?_⟩
  intro e f hq hn
  obtain ⟨a, b, c, d, hcase, h1, h2, h3⟩ := hn
  have hmin : ∀ x y, min (Q x y) 4 = Q x y := fun x y => min_eq_left (hQle x y)
  rcases hcase with ⟨he, hf⟩ | ⟨he, hf⟩
  · have had : H.Adj a d := by
      have := e.2; rw [he, SimpleGraph.mem_edgeSet] at this; exact this
    have hbc : H.Adj b c := by
      have := f.2; rw [hf, SimpleGraph.mem_edgeSet] at this; exact this
    have hq' := congrArg Fin.val hq
    simp only [he, hf, Sym2.lift_mk, hmin, Fin.val_mk] at hq'
    exact core a b c d had hbc hq' h1 h2 h3
  · have had : H.Adj a d := by
      have := f.2; rw [hf, SimpleGraph.mem_edgeSet] at this; exact this
    have hbc : H.Adj b c := by
      have := e.2; rw [he, SimpleGraph.mem_edgeSet] at this; exact this
    have hq' := congrArg Fin.val hq
    simp only [he, hf, Sym2.lift_mk, hmin, Fin.val_mk] at hq'
    exact core a b c d had hbc hq'.symm h1 h2 h3

end C3a

end PQL5

/-! C3 part L (session 5): Apollonian region trees and the bag layout (DPW04 Lemma 22 rows,
in-order x-coordinates). See scratch/decomp/1576ebc4.plan.md "session 5". -/

namespace PQL5

/-- Apollonian region tree: `nd v t1 t2 t3` placed in the region `(a,b,c)` stacks `v` there;
its children live in the regions `(a,b,v)`, `(b,c,v)`, `(c,a,v)`. -/
inductive RT (V : Type) where
  | lf : RT V
  | nd : V → RT V → RT V → RT V → RT V

section RTbasic

variable {V : Type} [DecidableEq V]

/-- the stacked vertices of a region tree -/
def RT.vs : RT V → Finset V
  | .lf => ∅
  | .nd v t1 t2 t3 => insert v (t1.vs ∪ t2.vs ∪ t3.vs)

/-- the edges created inside the region `(a,b,c)` -/
def RT.gr : RT V → V → V → V → SimpleGraph V
  | .lf, _, _, _ => ⊥
  | .nd v t1 t2 t3, a, b, c => star3 v a b c ⊔ t1.gr a b v ⊔ t2.gr b c v ⊔ t3.gr c a v

/-- labels are distinct and avoid the region boundary -/
def RT.wf : RT V → V → V → V → Prop
  | .lf, a, b, c => a ≠ b ∧ b ≠ c ∧ a ≠ c
  | .nd v t1 t2 t3, a, b, c => a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ v ≠ a ∧ v ≠ b ∧ v ≠ c ∧
      t1.wf a b v ∧ t2.wf b c v ∧ t3.wf c a v ∧ c ∉ t1.vs ∧ a ∉ t2.vs ∧ b ∉ t3.vs ∧
      Disjoint t1.vs t2.vs ∧ Disjoint t1.vs t3.vs ∧ Disjoint t2.vs t3.vs

theorem RT.vs_nd {v : V} {t1 t2 t3 : RT V} {z : V} :
    z ∈ (RT.nd v t1 t2 t3).vs ↔ z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs := by
  simp [RT.vs]

theorem RT.wf_ne {T : RT V} {a b c : V} (h : T.wf a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  cases T with
  | lf => exact h
  | nd v t1 t2 t3 => exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem RT.wf_out {T : RT V} {a b c : V} (h : T.wf a b c) :
    a ∉ T.vs ∧ b ∉ T.vs ∧ c ∉ T.vs := by
  induction T generalizing a b c with
  | lf => simp [RT.vs]
  | nd v t1 t2 t3 ih1 ih2 ih3 =>
    obtain ⟨_, _, _, hva, hvb, hvc, h1, h2, h3, hc1, ha2, hb3, _, _, _⟩ := h
    have o1 := ih1 h1
    have o2 := ih2 h2
    have o3 := ih3 h3
    simp only [RT.vs_nd, not_or]
    exact ⟨⟨fun e => hva e.symm, o1.1, ha2, o3.2.1⟩, ⟨fun e => hvb e.symm, o1.2.1, o2.1, hb3⟩,
      ⟨fun e => hvc e.symm, hc1, o2.2.1, o3.1⟩⟩

/-- every edge created in a region has an endpoint inside and the other inside or on the boundary -/
theorem RT.gr_ends {T : RT V} {a b c x y : V} (h : (T.gr a b c).Adj x y) :
    (x ∈ T.vs ∨ x = a ∨ x = b ∨ x = c) ∧ (y ∈ T.vs ∨ y = a ∨ y = b ∨ y = c) ∧
      (x ∈ T.vs ∨ y ∈ T.vs) := by
  induction T generalizing a b c x y with
  | lf => exact absurd h (by simp [RT.gr])
  | nd v t1 t2 t3 ih1 ih2 ih3 =>
    simp only [RT.gr, SimpleGraph.sup_adj] at h
    simp only [RT.vs_nd]
    have hv : v = v ∨ v ∈ t1.vs ∨ v ∈ t2.vs ∨ v ∈ t3.vs := Or.inl rfl
    rcases h with ((h | h) | h) | h
    · rw [star3_adj] at h
      obtain ⟨_, h⟩ := h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        subst h1 h2
      · exact ⟨Or.inl hv, Or.inr (Or.inl rfl), Or.inl hv⟩
      · exact ⟨Or.inr (Or.inl rfl), Or.inl hv, Or.inr hv⟩
      · exact ⟨Or.inl hv, Or.inr (Or.inr (Or.inl rfl)), Or.inl hv⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inl hv, Or.inr hv⟩
      · exact ⟨Or.inl hv, Or.inr (Or.inr (Or.inr rfl)), Or.inl hv⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), Or.inl hv, Or.inr hv⟩
    · obtain ⟨hx, hy, hxy⟩ := ih1 h
      have L : ∀ z, (z ∈ t1.vs ∨ z = a ∨ z = b ∨ z = v) →
          ((z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs) ∨ z = a ∨ z = b ∨ z = c) := by
        intro z hz
        rcases hz with hz | hz | hz | hz
        exacts [Or.inl (Or.inr (Or.inl hz)), Or.inr (Or.inl hz), Or.inr (Or.inr (Or.inl hz)),
          Or.inl (Or.inl hz)]
      refine ⟨L x hx, L y hy, ?_⟩
      rcases hxy with hz | hz
      exacts [Or.inl (Or.inr (Or.inl hz)), Or.inr (Or.inr (Or.inl hz))]
    · obtain ⟨hx, hy, hxy⟩ := ih2 h
      have L : ∀ z, (z ∈ t2.vs ∨ z = b ∨ z = c ∨ z = v) →
          ((z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs) ∨ z = a ∨ z = b ∨ z = c) := by
        intro z hz
        rcases hz with hz | hz | hz | hz
        exacts [Or.inl (Or.inr (Or.inr (Or.inl hz))), Or.inr (Or.inr (Or.inl hz)),
          Or.inr (Or.inr (Or.inr hz)), Or.inl (Or.inl hz)]
      refine ⟨L x hx, L y hy, ?_⟩
      rcases hxy with hz | hz
      exacts [Or.inl (Or.inr (Or.inr (Or.inl hz))), Or.inr (Or.inr (Or.inr (Or.inl hz)))]
    · obtain ⟨hx, hy, hxy⟩ := ih3 h
      have L : ∀ z, (z ∈ t3.vs ∨ z = c ∨ z = a ∨ z = v) →
          ((z = v ∨ z ∈ t1.vs ∨ z ∈ t2.vs ∨ z ∈ t3.vs) ∨ z = a ∨ z = b ∨ z = c) := by
        intro z hz
        rcases hz with hz | hz | hz | hz
        exacts [Or.inl (Or.inr (Or.inr (Or.inr hz))), Or.inr (Or.inr (Or.inr hz)),
          Or.inr (Or.inl hz), Or.inl (Or.inl hz)]
      refine ⟨L x hx, L y hy, ?_⟩
      rcases hxy with hz | hz
      exacts [Or.inl (Or.inr (Or.inr (Or.inr hz))), Or.inr (Or.inr (Or.inr (Or.inr hz)))]

end RTbasic

/-- per-vertex layout data: level, bag root, row, x-coordinate, bag key, attachment triangle
(top, anchor, bottom) of the bag. -/
structure Inf (V : Type) where
  lev : ℕ
  bid : V
  Y : ℤ
  x : ℚ
  bk : List ℚ
  tr : V × V × V

/-- region modes: `m0` new bag, `m1` leg region `(p,q,x)`, `m2 pa dr` polygon region with the
corner at position a (`pa`) or b, in-order direction `dr`. -/
inductive Md
  | m0 : Md
  | m1 : Md
  | m2 : Bool → Bool → Md

section Layout

variable {V : Type} [DecidableEq V]

/-- sort three labelled vertices by row, top first -/
def srt3 (a b c : V × Inf V) : (V × Inf V) × (V × Inf V) × (V × Inf V) :=
  if b.2.Y ≤ a.2.Y then
    (if c.2.Y ≤ b.2.Y then (a, b, c) else if c.2.Y ≤ a.2.Y then (a, c, b) else (c, a, b))
  else
    (if c.2.Y ≤ a.2.Y then (b, a, c) else if c.2.Y ≤ b.2.Y then (b, c, a) else (c, b, a))

/-- the bag key of a new bag attached to the (sorted) triangle `s` of the bag `par` -/
def newbk (enc : V → ℕ) (par : Inf V) (s : (V × Inf V) × (V × Inf V) × (V × Inf V)) : List ℚ :=
  par.bk ++ [(enc par.bid : ℚ), -(s.1.2.Y : ℚ), s.1.2.x, -(s.2.1.2.Y : ℚ), s.2.1.2.x,
    -(s.2.2.2.Y : ℚ), s.2.2.2.x]

/-- the row of the apex stacked on a polygon edge with rows `ys yt` -/
def yapex (ys yt : ℤ) : ℤ :=
  if ys - yt = 1 ∨ yt - ys = 1 then min ys yt - 1 else (ys + yt) / 2

/-- the layout of a region tree: the data of the vertex `z`, given the data `Ia Ib Ic` of the
region boundary and the x-interval `(lo, hi)` reserved for the region. -/
def lay (enc : V → ℕ) : RT V → Md → V → V → V → Inf V → Inf V → Inf V → ℚ → ℚ → V → Inf V
  | .lf, _, _, _, _, _, _, _, _, _, z => ⟨0, z, 0, 0, [], (z, z, z)⟩
  | .nd w t1 t2 t3, .m0, a, b, c, Ia, Ib, Ic, _, _, z =>
      let s := srt3 (a, Ia) (b, Ib) (c, Ic)
      let Iw : Inf V := ⟨Ia.lev + 1, w, 0, 0, newbk enc Ia s, (s.1.1, s.2.1.1, s.2.2.1)⟩
      if z = w then Iw
      else if z ∈ t1.vs then lay enc t1 .m1 a b w Ia Ib Iw 0 1 z
      else if z ∈ t2.vs then lay enc t2 .m1 b c w Ib Ic Iw 1 2 z
      else lay enc t3 .m1 c a w Ic Ia Iw 2 3 z
  | .nd u t1 t2 t3, .m1, a, b, c, Ia, Ib, Ic, lo, hi, z =>
      let d := (hi - lo) / 3
      let Iu : Inf V := ⟨Ic.lev, Ic.bid, Ic.Y - 1, lo + d, Ic.bk, Ic.tr⟩
      if z = u then Iu
      else if z ∈ t3.vs then lay enc t3 (.m2 false true) c a u Ic Ia Iu lo (lo + d) z
      else if z ∈ t1.vs then lay enc t1 .m1 a b u Ia Ib Iu (lo + d) (lo + 2 * d) z
      else lay enc t2 (.m2 true false) b c u Ib Ic Iu (lo + 2 * d) hi z
  | .nd v t1 t2 t3, .m2 pa dr, a, b, c, Ia, Ib, Ic, lo, hi, z =>
      let Is := if pa then Ib else Ia
      let Iv : Inf V := ⟨Is.lev, Is.bid, yapex Is.Y Ic.Y, (lo + hi) / 2, Is.bk, Is.tr⟩
      let mid := (lo + hi) / 2
      let loS := if dr then lo else mid
      let hiS := if dr then mid else hi
      let loT := if dr then mid else lo
      let hiT := if dr then hi else mid
      if z = v then Iv
      else if pa then
        (if z ∈ t1.vs then lay enc t1 (.m2 true dr) a b v Ia Ib Iv loS hiS z
         else if z ∈ t3.vs then lay enc t3 (.m2 false (!dr)) c a v Ic Ia Iv loT hiT z
         else lay enc t2 .m0 b c v Ib Ic Iv 0 0 z)
      else
        (if z ∈ t1.vs then lay enc t1 (.m2 false dr) a b v Ia Ib Iv loS hiS z
         else if z ∈ t2.vs then lay enc t2 (.m2 true (!dr)) b c v Ib Ic Iv loT hiT z
         else lay enc t3 .m0 c a v Ic Ia Iv 0 0 z)

/-- no strip inversion among the bag edges of `G` (edges `ab`, `cd` with `a,c` in one row and
`b,d` in another row of the same bag never cross). -/
def SIF (G : SimpleGraph V) (F : V → Inf V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj c d → (F a).bid = (F b).bid → (F c).bid = (F d).bid →
    (F a).bid = (F c).bid → (F a).Y = (F c).Y → (F b).Y = (F d).Y →
    (F a).x < (F c).x → (F d).x < (F b).x → False

/-- row-wise weak precedence of two vertex sets -/
def RowLe (F : V → Inf V) (P Q : V → Prop) : Prop :=
  ∀ z z', P z → Q z' → (F z).Y = (F z').Y → (F z).x ≤ (F z').x

omit [DecidableEq V] in
/-- PIVOT: edges of `G1` living on `P` never invert with edges of `G2` living on `Q` when `P`
precedes `Q` row-wise. -/
theorem sif_pivot {F : V → Inf V} {G1 G2 : SimpleGraph V} {P Q : V → Prop}
    (h1 : ∀ x y, G1.Adj x y → (F x).bid = (F y).bid → P x ∧ P y)
    (h2 : ∀ x y, G2.Adj x y → (F x).bid = (F y).bid → Q x ∧ Q y) (hPQ : RowLe F P Q) :
    ∀ a b c d, G1.Adj a b → G2.Adj c d → (F a).bid = (F b).bid → (F c).bid = (F d).bid →
      (F a).Y = (F c).Y → (F b).Y = (F d).Y →
      ((F a).x < (F c).x → (F d).x < (F b).x → False) ∧
      ((F c).x < (F a).x → (F b).x < (F d).x → False) := by
  intro a b c d hab hcd hb1 hb2 hy1 hy2
  obtain ⟨pa, pb⟩ := h1 a b hab hb1
  obtain ⟨qc, qd⟩ := h2 c d hcd hb2
  have e1 := hPQ a c pa qc hy1
  have e2 := hPQ b d pb qd hy2
  constructor
  · intro _ h; linarith
  · intro h _; linarith

omit [DecidableEq V] in
/-- SIF of a union from SIF of the parts and a cross condition -/
theorem sif_sup {F : V → Inf V} {G1 G2 : SimpleGraph V} (h1 : SIF G1 F) (h2 : SIF G2 F)
    (h12 : ∀ a b c d, G1.Adj a b → G2.Adj c d → (F a).bid = (F b).bid → (F c).bid = (F d).bid →
      (F a).bid = (F c).bid → (F a).Y = (F c).Y → (F b).Y = (F d).Y →
      ((F a).x < (F c).x → (F d).x < (F b).x → False) ∧
      ((F c).x < (F a).x → (F b).x < (F d).x → False)) :
    SIF (G1 ⊔ G2) F := by
  intro a b c d hab hcd hb1 hb2 hb3 hy1 hy2 hx1 hx2
  simp only [SimpleGraph.sup_adj] at hab hcd
  rcases hab with hab | hab <;> rcases hcd with hcd | hcd
  · exact h1 a b c d hab hcd hb1 hb2 hb3 hy1 hy2 hx1 hx2
  · exact (h12 a b c d hab hcd hb1 hb2 hb3 hy1 hy2).1 hx1 hx2
  · exact (h12 c d a b hcd hab hb2 hb1 (by rw [← hb3]) hy1.symm hy2.symm).2 hx1 hx2
  · exact h2 a b c d hab hcd hb1 hb2 hb3 hy1 hy2 hx1 hx2

end Layout


section LayUnfold

variable {V : Type} [DecidableEq V] (enc : V → ℕ)

theorem lay_m0_w {w : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} :
    lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi w =
      ⟨Ia.lev + 1, w, 0, 0, newbk enc Ia (srt3 (a, Ia) (b, Ib) (c, Ic)),
        ((srt3 (a, Ia) (b, Ib) (c, Ic)).1.1, (srt3 (a, Ia) (b, Ib) (c, Ic)).2.1.1,
          (srt3 (a, Ia) (b, Ib) (c, Ic)).2.2.1)⟩ := by
  simp [lay]

theorem lay_m0_1 {w : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} {z : V}
    (hw : z ≠ w) (h1 : z ∈ t1.vs) :
    lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi z =
      lay enc t1 .m1 a b w Ia Ib (lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi w) 0 1 z := by
  rw [lay_m0_w]; simp [lay, hw, h1]

theorem lay_m0_2 {w : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} {z : V}
    (hw : z ≠ w) (h1 : z ∉ t1.vs) (h2 : z ∈ t2.vs) :
    lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi z =
      lay enc t2 .m1 b c w Ib Ic (lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi w) 1 2 z := by
  rw [lay_m0_w]; simp [lay, hw, h1, h2]

theorem lay_m0_3 {w : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} {z : V}
    (hw : z ≠ w) (h1 : z ∉ t1.vs) (h2 : z ∉ t2.vs) :
    lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi z =
      lay enc t3 .m1 c a w Ic Ia (lay enc (.nd w t1 t2 t3) .m0 a b c Ia Ib Ic lo hi w) 2 3 z := by
  rw [lay_m0_w]; simp [lay, hw, h1, h2]

theorem lay_m1_u {u : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} :
    lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi u =
      ⟨Ic.lev, Ic.bid, Ic.Y - 1, lo + (hi - lo) / 3, Ic.bk, Ic.tr⟩ := by
  simp [lay]

theorem lay_m1_3 {u : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} {z : V}
    (hu : z ≠ u) (h3 : z ∈ t3.vs) :
    lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi z =
      lay enc t3 (.m2 false true) c a u Ic Ia (lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi u)
        lo (lo + (hi - lo) / 3) z := by
  rw [lay_m1_u]; simp [lay, hu, h3]

theorem lay_m1_1 {u : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} {z : V}
    (hu : z ≠ u) (h3 : z ∉ t3.vs) (h1 : z ∈ t1.vs) :
    lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi z =
      lay enc t1 .m1 a b u Ia Ib (lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi u)
        (lo + (hi - lo) / 3) (lo + 2 * ((hi - lo) / 3)) z := by
  rw [lay_m1_u]; simp [lay, hu, h3, h1]

theorem lay_m1_2 {u : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ} {z : V}
    (hu : z ≠ u) (h3 : z ∉ t3.vs) (h1 : z ∉ t1.vs) :
    lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi z =
      lay enc t2 (.m2 true false) b c u Ib Ic (lay enc (.nd u t1 t2 t3) .m1 a b c Ia Ib Ic lo hi u)
        (lo + 2 * ((hi - lo) / 3)) hi z := by
  rw [lay_m1_u]; simp [lay, hu, h3, h1]

theorem lay_m2_v {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {pa dr : Bool} :
    lay enc (.nd v t1 t2 t3) (.m2 pa dr) a b c Ia Ib Ic lo hi v =
      ⟨(if pa then Ib else Ia).lev, (if pa then Ib else Ia).bid,
        yapex (if pa then Ib else Ia).Y Ic.Y, (lo + hi) / 2, (if pa then Ib else Ia).bk,
        (if pa then Ib else Ia).tr⟩ := by
  simp [lay]

theorem lay_mA_1 {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {dr : Bool} {z : V} (hv : z ≠ v) (h1 : z ∈ t1.vs) :
    lay enc (.nd v t1 t2 t3) (.m2 true dr) a b c Ia Ib Ic lo hi z =
      lay enc t1 (.m2 true dr) a b v Ia Ib
        (lay enc (.nd v t1 t2 t3) (.m2 true dr) a b c Ia Ib Ic lo hi v)
        (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi) z := by
  rw [lay_m2_v]; simp [lay, hv, h1]

theorem lay_mA_3 {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {dr : Bool} {z : V} (hv : z ≠ v) (h1 : z ∉ t1.vs) (h3 : z ∈ t3.vs) :
    lay enc (.nd v t1 t2 t3) (.m2 true dr) a b c Ia Ib Ic lo hi z =
      lay enc t3 (.m2 false (!dr)) c a v Ic Ia
        (lay enc (.nd v t1 t2 t3) (.m2 true dr) a b c Ia Ib Ic lo hi v)
        (if dr then (lo + hi) / 2 else lo) (if dr then hi else (lo + hi) / 2) z := by
  rw [lay_m2_v]; simp [lay, hv, h1, h3]

theorem lay_mA_2 {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {dr : Bool} {z : V} (hv : z ≠ v) (h1 : z ∉ t1.vs) (h3 : z ∉ t3.vs) :
    lay enc (.nd v t1 t2 t3) (.m2 true dr) a b c Ia Ib Ic lo hi z =
      lay enc t2 .m0 b c v Ib Ic
        (lay enc (.nd v t1 t2 t3) (.m2 true dr) a b c Ia Ib Ic lo hi v) 0 0 z := by
  rw [lay_m2_v]; simp [lay, hv, h1, h3]

theorem lay_mB_1 {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {dr : Bool} {z : V} (hv : z ≠ v) (h1 : z ∈ t1.vs) :
    lay enc (.nd v t1 t2 t3) (.m2 false dr) a b c Ia Ib Ic lo hi z =
      lay enc t1 (.m2 false dr) a b v Ia Ib
        (lay enc (.nd v t1 t2 t3) (.m2 false dr) a b c Ia Ib Ic lo hi v)
        (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi) z := by
  rw [lay_m2_v]; simp [lay, hv, h1]

theorem lay_mB_2 {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {dr : Bool} {z : V} (hv : z ≠ v) (h1 : z ∉ t1.vs) (h2 : z ∈ t2.vs) :
    lay enc (.nd v t1 t2 t3) (.m2 false dr) a b c Ia Ib Ic lo hi z =
      lay enc t2 (.m2 true (!dr)) b c v Ib Ic
        (lay enc (.nd v t1 t2 t3) (.m2 false dr) a b c Ia Ib Ic lo hi v)
        (if dr then (lo + hi) / 2 else lo) (if dr then hi else (lo + hi) / 2) z := by
  rw [lay_m2_v]; simp [lay, hv, h1, h2]

theorem lay_mB_3 {v : V} {t1 t2 t3 : RT V} {a b c : V} {Ia Ib Ic : Inf V} {lo hi : ℚ}
    {dr : Bool} {z : V} (hv : z ≠ v) (h1 : z ∉ t1.vs) (h2 : z ∉ t2.vs) :
    lay enc (.nd v t1 t2 t3) (.m2 false dr) a b c Ia Ib Ic lo hi z =
      lay enc t3 .m0 c a v Ic Ia
        (lay enc (.nd v t1 t2 t3) (.m2 false dr) a b c Ia Ib Ic lo hi v) 0 0 z := by
  rw [lay_m2_v]; simp [lay, hv, h1, h2]

end LayUnfold


section Inv

variable {V : Type} [DecidableEq V]

/-- `z` is one of the three vertices of the triple `t` -/
def trs (z : V) (t : V × V × V) : Prop := z = t.1 ∨ z = t.2.1 ∨ z = t.2.2

/-- bag-root consistency of the data of `z` -/
def VInv (F : V → Inf V) (z : V) : Prop :=
  (F (F z).bid).bid = (F z).bid ∧ (F (F z).bid).lev = (F z).lev ∧
    (F (F z).bid).bk = (F z).bk ∧ (F (F z).bid).tr = (F z).tr ∧ (F z).bk.length = 7 * (F z).lev

/-- `x y` is a binding edge from the attachment triangle of `y`'s bag -/
def Bind (F : V → Inf V) (x y : V) : Prop :=
  (F y).lev = (F x).lev + 1 ∧ trs x (F y).tr ∧ (F x).bid ≠ (F y).bid

/-- rows differ by one or two -/
def dY12 (y1 y2 : ℤ) : Prop := y1 - y2 = 1 ∨ y2 - y1 = 1 ∨ y1 - y2 = 2 ∨ y2 - y1 = 2

/-- an edge is a bag edge spanning one or two rows, or a binding edge -/
def EInv (F : V → Inf V) (x y : V) : Prop :=
  ((F x).bid = (F y).bid ∧ dY12 (F x).Y (F y).Y) ∨ Bind F x y ∨ Bind F y x

/-- every stacked vertex has level >= 1; a bag root stores its attachment triangle (top, anchor, bottom) and key -/
def RInv (enc : V → ℕ) (H : SimpleGraph V) (F : V → Inf V) (z : V) : Prop :=
  1 ≤ (F z).lev ∧ ((F z).bid = z → 1 ≤ (F z).lev →
    (F (F z).tr.1).bid = (F (F z).tr.2.1).bid ∧ (F (F z).tr.1).bid = (F (F z).tr.2.2).bid ∧
    (F (F z).tr.1).lev + 1 = (F z).lev ∧
    (F (F z).tr.1).Y = (F (F z).tr.2.1).Y + 1 ∧ (F (F z).tr.2.1).Y = (F (F z).tr.2.2).Y + 1 ∧
    H.Adj (F z).tr.1 (F z).tr.2.1 ∧ H.Adj (F z).tr.2.1 (F z).tr.2.2 ∧
    H.Adj (F z).tr.1 (F z).tr.2.2 ∧
    (F z).bk = newbk enc (F (F z).tr.1) (((F z).tr.1, F (F z).tr.1),
      ((F z).tr.2.1, F (F z).tr.2.1), ((F z).tr.2.2, F (F z).tr.2.2)))

/-- same bag, same row, same x -> same vertex -/
def XInj (F : V → Inf V) (z z' : V) : Prop :=
  (F z).bid = (F z').bid → (F z).Y = (F z').Y → (F z).x = (F z').x → z = z'

/-- the common conclusions for a region tree `T` in the region `(a,b,c)` -/
def Good (enc : V → ℕ) (H : SimpleGraph V) (F : V → Inf V) (T : RT V) (a b c : V) : Prop :=
  (∀ z ∈ T.vs, VInv F z ∧ RInv enc H F z) ∧
  (∀ x y, (T.gr a b c).Adj x y → EInv F x y) ∧
  SIF (T.gr a b c) F ∧
  (∀ z ∈ T.vs, ∀ z', (z' ∈ T.vs ∨ z' = a ∨ z' = b ∨ z' = c) → XInj F z z')

/-- bag part of a leg/polygon region: inside the x-interval and below `ymax`; other vertices
belong to bags rooted inside the region. -/
def Rng (F : V → Inf V) (T : RT V) (β : V) (lo hi : ℚ) (ymax : ℤ) : Prop :=
  ∀ z ∈ T.vs, ((F z).bid = β ∧ lo < (F z).x ∧ (F z).x < hi ∧ (F z).Y < ymax) ∨ (F z).bid ∈ T.vs

/-- boundary hypotheses per mode -/
def Hyp (F : V → Inf V) (T : RT V) : Md → V → V → V → ℚ → ℚ → Prop
  | .m0, a, b, c, _, _ => VInv F a ∧ VInv F b ∧ VInv F c ∧ (F a).bid = (F b).bid ∧
      (F a).bid = (F c).bid ∧ (F a).bid ∉ T.vs ∧ (F a).lev = (F b).lev ∧ (F a).lev = (F c).lev ∧
      dY12 (F a).Y (F b).Y ∧ dY12 (F b).Y (F c).Y ∧ dY12 (F a).Y (F c).Y
  | .m1, a, b, c, lo, hi => VInv F c ∧ (F c).bid ∉ T.vs ∧ lo < hi ∧
      (F a).lev + 1 = (F c).lev ∧ trs a (F c).tr ∧ (F a).bid ≠ (F c).bid ∧
      (F b).lev + 1 = (F c).lev ∧ trs b (F c).tr ∧ (F b).bid ≠ (F c).bid ∧
      (F a).bid ∉ T.vs ∧ (F b).bid ∉ T.vs
  | .m2 pa dr, a, b, c, lo, hi =>
      VInv F (if pa then b else a) ∧ VInv F c ∧ (F (if pa then b else a)).bid = (F c).bid ∧
      (F c).bid ∉ T.vs ∧ lo < hi ∧ dY12 (F (if pa then b else a)).Y (F c).Y ∧
      (F (if pa then a else b)).lev + 1 = (F c).lev ∧ trs (if pa then a else b) (F c).tr ∧
      (F (if pa then a else b)).bid ≠ (F c).bid ∧
      ((F (if dr then (if pa then b else a) else c)).Y < max (F (if pa then b else a)).Y (F c).Y →
        (F (if dr then (if pa then b else a) else c)).x ≤ lo) ∧
      ((F (if dr then c else (if pa then b else a))).Y < max (F (if pa then b else a)).Y (F c).Y →
        hi ≤ (F (if dr then c else (if pa then b else a))).x) ∧
      (F (if pa then a else b)).bid ∉ T.vs

/-- mode-specific range conclusion -/
def Cnc (F : V → Inf V) (T : RT V) : Md → V → V → V → ℚ → ℚ → Prop
  | .m0, _, _, _, _, _ => ∀ z ∈ T.vs, (F z).bid ∈ T.vs
  | .m1, _, _, c, lo, hi => Rng F T (F c).bid lo hi (F c).Y
  | .m2 pa _, a, b, c, lo, hi => Rng F T (F c).bid lo hi (max (F (if pa then b else a)).Y (F c).Y)

/-- MAIN LAYOUT THEOREM (to prove by induction on `T`, one step lemma per mode). -/
def MainLay (enc : V → ℕ) : Prop :=
  ∀ (H : SimpleGraph V) (F : V → Inf V) (T : RT V) (md : Md) (a b c : V) (lo hi : ℚ),
    T.wf a b c → T.gr a b c ≤ H → H.Adj a b → H.Adj b c → H.Adj a c →
    (∀ z ∈ T.vs, F z = lay enc T md a b c (F a) (F b) (F c) lo hi z) →
    Hyp F T md a b c lo hi → Good enc H F T a b c ∧ Cnc F T md a b c lo hi

end Inv


section Srt

variable {V : Type}

/-- `srt3` returns a permutation of its input, sorted by row (top first) -/
theorem srt3_spec (a b c : V × Inf V) :
    let s := srt3 a b c
    ((s.1 = a ∧ s.2.1 = b ∧ s.2.2 = c) ∨ (s.1 = a ∧ s.2.1 = c ∧ s.2.2 = b) ∨
      (s.1 = b ∧ s.2.1 = a ∧ s.2.2 = c) ∨ (s.1 = b ∧ s.2.1 = c ∧ s.2.2 = a) ∨
      (s.1 = c ∧ s.2.1 = a ∧ s.2.2 = b) ∨ (s.1 = c ∧ s.2.1 = b ∧ s.2.2 = a)) ∧
    s.2.1.2.Y ≤ s.1.2.Y ∧ s.2.2.2.Y ≤ s.2.1.2.Y := by
  simp only [srt3]
  split_ifs <;> simp_all <;> omega

/-- three rows pairwise one or two apart, sorted top first, are consecutive -/
theorem dY12_consec {y1 y2 y3 : ℤ} (h12 : dY12 y1 y2) (h23 : dY12 y2 y3) (h13 : dY12 y1 y3)
    (s1 : y2 ≤ y1) (s2 : y3 ≤ y2) : y1 = y2 + 1 ∧ y2 = y3 + 1 := by
  unfold dY12 at h12 h23 h13
  omega

end Srt

end PQL5

/-! C3 part C (session 6): proof of `MainLay` (infrastructure: crossing-freeness between edge
sets, pivot / shared-top criteria, node combination). -/

namespace PQL5

section Cross

variable {V : Type} [DecidableEq V]

/-- the two edges `ab`, `cd` (rows matched) are not inverted -/
def NonInv (F : V → Inf V) (a b c d : V) : Prop :=
  ((F a).x ≤ (F c).x ∧ (F b).x ≤ (F d).x) ∨ ((F c).x ≤ (F a).x ∧ (F d).x ≤ (F b).x)

/-- no inversion between an edge of `G1` and an edge of `G2` in one bag -/
def Cross (G1 G2 : SimpleGraph V) (F : V → Inf V) : Prop :=
  ∀ a b c d, G1.Adj a b → G2.Adj c d → (F a).bid = (F b).bid → (F c).bid = (F d).bid →
    (F a).bid = (F c).bid → (F a).Y = (F c).Y → (F b).Y = (F d).Y → NonInv F a b c d

omit [DecidableEq V] in
theorem cross_symm {G1 G2 : SimpleGraph V} {F : V → Inf V} (h : Cross G1 G2 F) :
    Cross G2 G1 F := by
  intro a b c d h1 h2 e1 e2 e3 e4 e5
  rcases h c d a b h2 h1 e2 e1 e3.symm e4.symm e5.symm with h | h
  · exact Or.inr h
  · exact Or.inl h

omit [DecidableEq V] in
theorem cross_supL {G1 G2 G3 : SimpleGraph V} {F : V → Inf V} (h1 : Cross G1 G3 F)
    (h2 : Cross G2 G3 F) : Cross (G1 ⊔ G2) G3 F := by
  intro a b c d hab hcd e1 e2 e3 e4 e5
  rw [SimpleGraph.sup_adj] at hab
  rcases hab with hab | hab
  · exact h1 a b c d hab hcd e1 e2 e3 e4 e5
  · exact h2 a b c d hab hcd e1 e2 e3 e4 e5

omit [DecidableEq V] in
theorem cross_supR {G1 G2 G3 : SimpleGraph V} {F : V → Inf V} (h1 : Cross G1 G2 F)
    (h2 : Cross G1 G3 F) : Cross G1 (G2 ⊔ G3) F :=
  cross_symm (cross_supL (cross_symm h1) (cross_symm h2))

omit [DecidableEq V] in
theorem sif_sup2 {G1 G2 : SimpleGraph V} {F : V → Inf V} (h1 : SIF G1 F) (h2 : SIF G2 F)
    (h12 : Cross G1 G2 F) : SIF (G1 ⊔ G2) F := by
  apply sif_sup h1 h2
  intro a b c d hab hcd e1 e2 e3 e4 e5
  rcases h12 a b c d hab hcd e1 e2 e3 e4 e5 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact ⟨fun _ h => by linarith, fun h _ => by linarith⟩
  · exact ⟨fun h _ => by linarith, fun _ h => by linarith⟩

/-- row-wise weak precedence inside the bag `β` -/
def RowLeB (F : V → Inf V) (β : V) (P Q : V → Prop) : Prop :=
  ∀ z z', P z → Q z' → (F z).bid = β → (F z').bid = β → (F z).Y = (F z').Y → (F z).x ≤ (F z').x

/-- the equal-bag edges of `G` lie in bag `β` on `P`, or in a bag in `S` -/
def EdgeZ (F : V → Inf V) (G : SimpleGraph V) (β : V) (P S : V → Prop) : Prop :=
  ∀ x y, G.Adj x y → (F x).bid = (F y).bid → ((F x).bid = β ∧ P x ∧ P y) ∨ S (F x).bid

omit [DecidableEq V] in
/-- MIXED PIVOT: every equal-bag edge of `G1` lies in bag `β` and either contains the top vertex
`T0` (the only `Q`-vertex of bag `β` in its row) or lies on `P`, with `P`, `Q` row-comparable. -/
theorem cross_mix {G1 G2 : SimpleGraph V} {F : V → Inf V} {β T0 : V} {P Q S2 : V → Prop}
    (h1 : ∀ x y, G1.Adj x y → (F x).bid = (F y).bid →
      (F x).bid = β ∧ ((x = T0 ∨ y = T0) ∨ (P x ∧ P y)))
    (h2 : EdgeZ F G2 β Q S2) (h2β : ¬ S2 β)
    (hQ : ∀ z, Q z → (F z).bid = β → (F z).Y = (F T0).Y → z = T0)
    (hPQ : RowLeB F β P Q ∨ RowLeB F β Q P) : Cross G1 G2 F := by
  intro a b c d hab hcd e1 e2 e3 e4 e5
  obtain ⟨ba, ht⟩ := h1 a b hab e1
  have bc : (F c).bid = β := e3.symm.trans ba
  have bb : (F b).bid = β := e1.symm.trans ba
  rcases h2 c d hcd e2 with ⟨_, qc, qd⟩ | s2
  · have bd : (F d).bid = β := e2.symm.trans bc
    rcases ht with (rfl | rfl) | ⟨pa, pb⟩
    · have := hQ c qc bc e4.symm
      subst this
      rcases le_total (F b).x (F d).x with h | h
      · exact Or.inl ⟨le_rfl, h⟩
      · exact Or.inr ⟨le_rfl, h⟩
    · have := hQ d qd bd e5.symm
      subst this
      rcases le_total (F a).x (F c).x with h | h
      · exact Or.inl ⟨h, le_rfl⟩
      · exact Or.inr ⟨h, le_rfl⟩
    · rcases hPQ with h | h
      · exact Or.inl ⟨h a c pa qc ba bc e4, h b d pb qd bb bd e5⟩
      · exact Or.inr ⟨h c a qc pa bc ba e4.symm, h d b qd pb bd bb e5.symm⟩
  · exact absurd (bc ▸ s2) h2β

omit [DecidableEq V] in
/-- PIVOT between two zoned edge sets -/
theorem cross_pivot {G1 G2 : SimpleGraph V} {F : V → Inf V} {β : V} {P Q S1 S2 : V → Prop}
    (h1 : EdgeZ F G1 β P S1) (h2 : EdgeZ F G2 β Q S2) (hS : ∀ γ, S1 γ → S2 γ → False)
    (h1β : ¬ S1 β) (h2β : ¬ S2 β) (hPQ : RowLeB F β P Q ∨ RowLeB F β Q P) :
    Cross G1 G2 F := by
  intro a b c d hab hcd e1 e2 e3 e4 e5
  rcases h1 a b hab e1 with ⟨ba, pa, pb⟩ | s1
  · have bc : (F c).bid = β := e3.symm.trans ba
    have bb : (F b).bid = β := e1.symm.trans ba
    rcases h2 c d hcd e2 with ⟨_, qc, qd⟩ | s2
    · have bd : (F d).bid = β := e2.symm.trans bc
      rcases hPQ with h | h
      · exact Or.inl ⟨h a c pa qc ba bc e4, h b d pb qd bb bd e5⟩
      · exact Or.inr ⟨h c a qc pa bc ba e4.symm, h d b qd pb bd bb e5.symm⟩
    · exact absurd (bc ▸ s2) h2β
  · rcases h2 c d hcd e2 with ⟨bc, _, _⟩ | s2
    · exact absurd ((e3.trans bc) ▸ s1) h1β
    · exact (hS _ s1 (e3 ▸ s2)).elim

omit [DecidableEq V] in
/-- a graph without equal-bag edges crosses nothing -/
theorem cross_nobag {G1 G2 : SimpleGraph V} {F : V → Inf V}
    (h : ∀ x y, G1.Adj x y → (F x).bid ≠ (F y).bid) : Cross G1 G2 F :=
  fun a b _ _ hab _ e1 => absurd e1 (h a b hab)

omit [DecidableEq V] in
theorem sif_nobag {G : SimpleGraph V} {F : V → Inf V}
    (h : ∀ x y, G.Adj x y → (F x).bid ≠ (F y).bid) : SIF G F :=
  fun a b _ _ hab _ e1 => absurd e1 (h a b hab)

omit [DecidableEq V] in
theorem xinj_symm {F : V → Inf V} {z z' : V} (h : XInj F z z') : XInj F z' z :=
  fun e1 e2 e3 => (h e1.symm e2.symm e3.symm).symm

omit [DecidableEq V] in
theorem xinj_of {F : V → Inf V} {z z' : V}
    (h : (F z).bid ≠ (F z').bid ∨ (F z).Y ≠ (F z').Y ∨ (F z).x ≠ (F z').x) : XInj F z z' := by
  intro e1 e2 e3
  rcases h with h | h | h
  exacts [absurd e1 h, absurd e2 h, absurd e3 h]

/-- the zone of a region: its bag-`β` part (from `Rng`) and its boundary -/
def Zn (F : V → Inf V) (t : RT V) (lo hi : ℚ) (ym : ℤ) (a b c : V) (z : V) : Prop :=
  (z ∈ t.vs ∧ lo < (F z).x ∧ (F z).x < hi ∧ (F z).Y < ym) ∨ z = a ∨ z = b ∨ z = c

theorem rng_mem {F : V → Inf V} {t : RT V} {β : V} {lo hi : ℚ} {ym : ℤ}
    (hR : Rng F t β lo hi ym) {z : V} (hz : z ∈ t.vs) (hb : (F z).bid ∉ t.vs) :
    (F z).bid = β ∧ lo < (F z).x ∧ (F z).x < hi ∧ (F z).Y < ym := by
  rcases hR z hz with h | h
  · exact h
  · exact absurd h hb

theorem edgeZ_rng {F : V → Inf V} {t : RT V} {β : V} {lo hi : ℚ} {ym : ℤ} {a b c : V}
    (hR : Rng F t β lo hi ym) : EdgeZ F (t.gr a b c) β (Zn F t lo hi ym a b c) (· ∈ t.vs) := by
  intro x y hxy e
  obtain ⟨hx, hy, hxy'⟩ := RT.gr_ends hxy
  by_cases hb : (F x).bid ∈ t.vs
  · exact Or.inr hb
  left
  have hb' : (F y).bid ∉ t.vs := e ▸ hb
  have Zx : ((F x).bid = β ∧ Zn F t lo hi ym a b c x) ∨ x = a ∨ x = b ∨ x = c := by
    rcases hx with hx | hx
    · obtain ⟨h1, h2⟩ := rng_mem hR hx hb
      exact Or.inl ⟨h1, Or.inl ⟨hx, h2⟩⟩
    · exact Or.inr hx
  have Zy : ((F y).bid = β ∧ Zn F t lo hi ym a b c y) ∨ y = a ∨ y = b ∨ y = c := by
    rcases hy with hy | hy
    · obtain ⟨h1, h2⟩ := rng_mem hR hy hb'
      exact Or.inl ⟨h1, Or.inl ⟨hy, h2⟩⟩
    · exact Or.inr hy
  have zx : Zn F t lo hi ym a b c x := by
    rcases Zx with ⟨_, h⟩ | h
    · exact h
    · exact Or.inr h
  have zy : Zn F t lo hi ym a b c y := by
    rcases Zy with ⟨_, h⟩ | h
    · exact h
    · exact Or.inr h
  refine ⟨?_, zx, zy⟩
  rcases hxy' with h | h
  · exact (rng_mem hR h hb).1
  · exact e.trans (rng_mem hR h hb').1

theorem edgeZ_m0 {F : V → Inf V} {t : RT V} {β : V} {P : V → Prop} {a b c : V}
    (h : ∀ z ∈ t.vs, (F z).bid ∈ t.vs) : EdgeZ F (t.gr a b c) β P (· ∈ t.vs) := by
  intro x y hxy e
  right
  rcases (RT.gr_ends hxy).2.2 with hx | hy
  · exact h x hx
  · rw [e]; exact h y hy

/-- combination at a node -/
theorem node_good (enc : V → ℕ) {H : SimpleGraph V} {F : V → Inf V} {w : V} {t1 t2 t3 : RT V}
    {a b c : V}
    (hw : VInv F w ∧ RInv enc H F w) (g1 : Good enc H F t1 a b w) (g2 : Good enc H F t2 b c w)
    (g3 : Good enc H F t3 c a w)
    (he : ∀ x y, (star3 w a b c).Adj x y → EInv F x y) (hs : SIF (star3 w a b c) F)
    (c01 : Cross (star3 w a b c) (t1.gr a b w) F) (c02 : Cross (star3 w a b c) (t2.gr b c w) F)
    (c03 : Cross (star3 w a b c) (t3.gr c a w) F) (c12 : Cross (t1.gr a b w) (t2.gr b c w) F)
    (c13 : Cross (t1.gr a b w) (t3.gr c a w) F) (c23 : Cross (t2.gr b c w) (t3.gr c a w) F)
    (xw : ∀ z', (z' ∈ t1.vs ∨ z' ∈ t2.vs ∨ z' ∈ t3.vs ∨ z' = a ∨ z' = b ∨ z' = c) → XInj F w z')
    (x12 : ∀ z ∈ t1.vs, ∀ z' ∈ t2.vs, XInj F z z') (x13 : ∀ z ∈ t1.vs, ∀ z' ∈ t3.vs, XInj F z z')
    (x23 : ∀ z ∈ t2.vs, ∀ z' ∈ t3.vs, XInj F z z')
    (x1c : ∀ z ∈ t1.vs, XInj F z c) (x2a : ∀ z ∈ t2.vs, XInj F z a)
    (x3b : ∀ z ∈ t3.vs, XInj F z b) :
    Good enc H F (RT.nd w t1 t2 t3) a b c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases RT.vs_nd.1 hz with rfl | hz | hz | hz
    exacts [hw, g1.1 z hz, g2.1 z hz, g3.1 z hz]
  · intro x y h
    simp only [RT.gr, SimpleGraph.sup_adj] at h
    rcases h with ((h | h) | h) | h
    exacts [he x y h, g1.2.1 x y h, g2.2.1 x y h, g3.2.1 x y h]
  · simp only [RT.gr]
    exact sif_sup2 (sif_sup2 (sif_sup2 hs g1.2.2.1 c01) g2.2.2.1 (cross_supL c02 c12)) g3.2.2.1
      (cross_supL (cross_supL c03 c13) c23)
  · intro z hz z' hz'
    have hz'' : z' = w ∨ z' ∈ t1.vs ∨ z' ∈ t2.vs ∨ z' ∈ t3.vs ∨ z' = a ∨ z' = b ∨ z' = c := by
      rcases hz' with h | h
      · rcases RT.vs_nd.1 h with h | h | h | h
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
          Or.inr (Or.inr (Or.inr (Or.inl h)))]
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    clear hz'
    rcases RT.vs_nd.1 hz with rfl | hk | hk | hk
    · rcases hz'' with rfl | h
      · exact fun _ _ _ => rfl
      · exact xw z' h
    · rcases hz'' with h | h | h | h | h | h | h
      · subst h; exact xinj_symm (xw z (Or.inl hk))
      · exact g1.2.2.2 z hk z' (Or.inl h)
      · exact x12 z hk z' h
      · exact x13 z hk z' h
      · exact g1.2.2.2 z hk z' (Or.inr (Or.inl h))
      · exact g1.2.2.2 z hk z' (Or.inr (Or.inr (Or.inl h)))
      · subst h; exact x1c z hk
    · rcases hz'' with h | h | h | h | h | h | h
      · subst h; exact xinj_symm (xw z (Or.inr (Or.inl hk)))
      · exact xinj_symm (x12 z' h z hk)
      · exact g2.2.2.2 z hk z' (Or.inl h)
      · exact x23 z hk z' h
      · subst h; exact x2a z hk
      · exact g2.2.2.2 z hk z' (Or.inr (Or.inl h))
      · exact g2.2.2.2 z hk z' (Or.inr (Or.inr (Or.inl h)))
    · rcases hz'' with h | h | h | h | h | h | h
      · subst h; exact xinj_symm (xw z (Or.inr (Or.inr (Or.inl hk))))
      · exact xinj_symm (x13 z' h z hk)
      · exact xinj_symm (x23 z' h z hk)
      · exact g3.2.2.2 z hk z' (Or.inl h)
      · exact g3.2.2.2 z hk z' (Or.inr (Or.inr (Or.inl h)))
      · subst h; exact x3b z hk
      · exact g3.2.2.2 z hk z' (Or.inr (Or.inl h))

/-- the facts of a well-formed node -/
theorem nd_wf {w : V} {t1 t2 t3 : RT V} {a b c : V} (h : (RT.nd w t1 t2 t3).wf a b c) :
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ t1.wf a b w ∧ t2.wf b c w ∧ t3.wf c a w ∧
    (a ∉ t1.vs ∧ b ∉ t1.vs ∧ w ∉ t1.vs ∧ c ∉ t1.vs) ∧ (b ∉ t2.vs ∧ c ∉ t2.vs ∧ w ∉ t2.vs ∧ a ∉ t2.vs) ∧
    (c ∉ t3.vs ∧ a ∉ t3.vs ∧ w ∉ t3.vs ∧ b ∉ t3.vs) ∧
    Disjoint t1.vs t2.vs ∧ Disjoint t1.vs t3.vs ∧ Disjoint t2.vs t3.vs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, w1, w2, w3, hc1, ha2, hb3, d12, d13, d23⟩ := h
  have o1 := RT.wf_out w1
  have o2 := RT.wf_out w2
  have o3 := RT.wf_out w3
  exact ⟨h1, h2, h3, h4, h5, h6, w1, w2, w3, ⟨o1.1, o1.2.1, o1.2.2, hc1⟩, ⟨o2.1, o2.2.1, o2.2.2, ha2⟩,
    ⟨o3.1, o3.2.1, o3.2.2, hb3⟩, d12, d13, d23⟩

/-- the induction statement for one region tree -/
def LayOK (enc : V → ℕ) (H : SimpleGraph V) (F : V → Inf V) (T : RT V) : Prop :=
  ∀ (md : Md) (a b c : V) (lo hi : ℚ),
    T.wf a b c → T.gr a b c ≤ H → H.Adj a b → H.Adj b c → H.Adj a c →
    (∀ z ∈ T.vs, F z = lay enc T md a b c (F a) (F b) (F c) lo hi z) →
    Hyp F T md a b c lo hi → Good enc H F T a b c ∧ Cnc F T md a b c lo hi

theorem layOK_lf (enc : V → ℕ) (H : SimpleGraph V) (F : V → Inf V) : LayOK enc H F .lf := by
  intro md a b c lo hi _ _ _ _ _ _ _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro z hz; simp [RT.vs] at hz
  · intro x y h; simp [RT.gr] at h
  · intro a b c d h; simp [RT.gr] at h
  · intro z hz; simp [RT.vs] at hz
  · cases md <;> simp [Cnc, Rng, RT.vs]

end Cross

end PQL5

/-! C3 part S (session 6): the step lemmas of `MainLay`. -/

namespace PQL5

section Steps

variable {V : Type} [DecidableEq V]

theorem dY12_symm {y1 y2 : ℤ} (h : dY12 y1 y2) : dY12 y2 y1 := by
  unfold dY12 at *; omega

theorem srt3_perm (F : V → Inf V) {a b c : V} {s : (V × Inf V) × (V × Inf V) × (V × Inf V)}
    (hs : s = srt3 (a, F a) (b, F b) (c, F c)) :
    s = ((s.1.1, F s.1.1), (s.2.1.1, F s.2.1.1), (s.2.2.1, F s.2.2.1)) ∧
    (∀ y, (y = a ∨ y = b ∨ y = c) ↔ (y = s.1.1 ∨ y = s.2.1.1 ∨ y = s.2.2.1)) ∧
    (a ≠ b → b ≠ c → a ≠ c → s.1.1 ≠ s.2.1.1 ∧ s.2.1.1 ≠ s.2.2.1 ∧ s.1.1 ≠ s.2.2.1) ∧
    (F s.2.1.1).Y ≤ (F s.1.1).Y ∧ (F s.2.2.1).Y ≤ (F s.2.1.1).Y := by
  have h := srt3_spec (a, F a) (b, F b) (c, F c)
  rw [← hs] at h
  obtain ⟨h, y1, y2⟩ := h
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ <;>
    simp only [h1, h2, h3] at y1 y2 ⊢ <;>
    refine ⟨?_, fun y => by tauto, fun n1 n2 n3 => ⟨?_, ?_, ?_⟩, y1, y2⟩
  all_goals first
    | exact Prod.ext h1 (Prod.ext h2 h3)
    | (intro e; first | exact n1 e | exact n1 e.symm | exact n2 e | exact n2 e.symm | exact n3 e | exact n3 e.symm)

theorem rowle_m0 {F : V → Inf V} {w : V} {t t' : RT V} {x y x' y' : V} {lo1 hi1 lo2 hi2 : ℚ}
    (_hl1 : 0 ≤ lo1) (hl2 : 0 ≤ lo2) (h12 : hi1 ≤ lo2) (hyw : (F w).Y = 0) (hxw : (F w).x = 0)
    (nx : (F x).bid ≠ w) (ny : (F y).bid ≠ w) (nx' : (F x').bid ≠ w) (ny' : (F y').bid ≠ w) :
    RowLeB F w (Zn F t lo1 hi1 0 x y w) (Zn F t' lo2 hi2 0 x' y' w) := by
  intro z z' hz hz' bz bz' e
  rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h'
  all_goals first
    | (subst h; exact absurd bz nx) | (subst h; exact absurd bz ny)
    | (subst h'; exact absurd bz' nx') | (subst h'; exact absurd bz' ny') | skip
  · linarith
  · subst h'; exfalso; omega
  · subst h; linarith
  · subst h h'; exact le_rfl

theorem xinj_rr {F : V → Inf V} {t1 t2 : RT V} {β : V} {lo1 hi1 lo2 hi2 : ℚ} {ym1 ym2 : ℤ}
    (R1 : Rng F t1 β lo1 hi1 ym1) (R2 : Rng F t2 β lo2 hi2 ym2) (hd : Disjoint t1.vs t2.vs)
    (n1 : β ∉ t1.vs) (n2 : β ∉ t2.vs) (hsep : hi1 ≤ lo2 ∨ hi2 ≤ lo1) :
    ∀ z ∈ t1.vs, ∀ z' ∈ t2.vs, XInj F z z' := by
  intro z hz z' hz' e1 _ e3
  rcases R1 z hz with ⟨b1, l1, u1, _⟩ | i1 <;> rcases R2 z' hz' with ⟨b2, l2, u2, _⟩ | i2
  · exfalso; rcases hsep with h | h <;> linarith
  · rw [← e1, b1] at i2; exact absurd i2 n2
  · rw [e1, b2] at i1; exact absurd i1 n1
  · rw [← e1] at i2; exact absurd i2 (Finset.disjoint_left.mp hd i1)

theorem xinj_rb {F : V → Inf V} {t : RT V} {β : V} {lo hi : ℚ} {ym : ℤ}
    (R : Rng F t β lo hi ym) (nβ : β ∉ t.vs) {z' : V}
    (h : ((F z').bid ≠ β ∧ (F z').bid ∉ t.vs) ∨
      ((F z').bid = β ∧ ((F z').x ≤ lo ∨ hi ≤ (F z').x ∨ ym ≤ (F z').Y))) :
    ∀ z ∈ t.vs, XInj F z z' := by
  intro z hz e1 e2 e3
  rcases R z hz with ⟨b1, l1, u1, y1⟩ | i1 <;> rcases h with ⟨n1, n2⟩ | ⟨b2, h⟩
  · exact absurd (e1.symm.trans b1) n1
  · exfalso; rcases h with h | h | h
    · linarith
    · linarith
    · omega
  · rw [e1] at i1; exact absurd i1 n2
  · rw [e1, b2] at i1; exact absurd i1 nβ

theorem rng_of_m0 {F : V → Inf V} {t : RT V} (h : ∀ z ∈ t.vs, (F z).bid ∈ t.vs) (β : V)
    (lo hi : ℚ) (ym : ℤ) : Rng F t β lo hi ym := fun z hz => Or.inr (h z hz)

/-- STEP m0: a new bag stacked in a triangle of a bag. -/
theorem step_m0 (enc : V → ℕ) {H : SimpleGraph V} {F : V → Inf V} {w : V} {t1 t2 t3 : RT V}
    (ih1 : LayOK enc H F t1) (ih2 : LayOK enc H F t2) (ih3 : LayOK enc H F t3)
    {a b c : V} {lo hi : ℚ}
    (hwf : (RT.nd w t1 t2 t3).wf a b c) (hgr : (RT.nd w t1 t2 t3).gr a b c ≤ H)
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c)
    (hF : ∀ z ∈ (RT.nd w t1 t2 t3).vs,
      F z = lay enc (RT.nd w t1 t2 t3) .m0 a b c (F a) (F b) (F c) lo hi z)
    (hH : Hyp F (RT.nd w t1 t2 t3) .m0 a b c lo hi) :
    Good enc H F (RT.nd w t1 t2 t3) a b c ∧ Cnc F (RT.nd w t1 t2 t3) .m0 a b c lo hi := by
  obtain ⟨nab, nbc, nac, nwa, nwb, nwc, w1, w2, w3, ⟨a1, b1, w1o, c1⟩, ⟨b2, c2, w2o, a2⟩,
    ⟨c3, a3, w3o, b3⟩, d12, d13, d23⟩ := nd_wf hwf
  obtain ⟨va, vb, vc, eab, eac, naT, lab, lac, yab, ybc, yac⟩ := hH
  have wT : w ∈ (RT.nd w t1 t2 t3).vs := RT.vs_nd.2 (Or.inl rfl)
  have hFw0 := hF w wT
  have hFw := hFw0
  rw [lay_m0_w] at hFw
  set s := srt3 (a, F a) (b, F b) (c, F c) with hs
  obtain ⟨sp, sall, sne, sy1, sy2⟩ := srt3_perm F hs
  have hbw : (F w).bid = w := by rw [hFw]
  have hlw : (F w).lev = (F a).lev + 1 := by rw [hFw]
  have hyw : (F w).Y = 0 := by rw [hFw]
  have hxw : (F w).x = 0 := by rw [hFw]
  have hkw : (F w).bk = newbk enc (F a) s := by rw [hFw]
  have htw : (F w).tr = (s.1.1, s.2.1.1, s.2.2.1) := by rw [hFw]
  -- the boundary vertices
  have abc : ∀ y, (y = a ∨ y = b ∨ y = c) →
      (F y).bid = (F a).bid ∧ (F y).lev = (F a).lev ∧ (F y).bk = (F a).bk ∧ VInv F y := by
    intro y hy
    have h0 : (F y).bid = (F a).bid ∧ (F y).lev = (F a).lev ∧ VInv F y := by
      rcases hy with rfl | rfl | rfl
      exacts [⟨rfl, rfl, va⟩, ⟨eab.symm, lab.symm, vb⟩, ⟨eac.symm, lac.symm, vc⟩]
    refine ⟨h0.1, h0.2.1, ?_, h0.2.2⟩
    rw [← h0.2.2.2.2.1, ← va.2.2.1, h0.1]
  have nbw : ∀ y, (y = a ∨ y = b ∨ y = c) → (F y).bid ≠ w := by
    intro y hy e
    rw [(abc y hy).1] at e
    exact naT (e ▸ wT)
  have nbt : ∀ y, (y = a ∨ y = b ∨ y = c) → ∀ z ∈ (RT.nd w t1 t2 t3).vs, (F y).bid ≠ z := by
    intro y hy z hz e
    rw [(abc y hy).1] at e
    exact naT (e ▸ hz)
  have pr : ∀ y y', (y = a ∨ y = b ∨ y = c) → (y' = a ∨ y' = b ∨ y' = c) → y ≠ y' →
      H.Adj y y' ∧ dY12 (F y).Y (F y').Y := by
    intro y y' hy hy' n
    rcases hy with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl n
      | exact ⟨hab, yab⟩ | exact ⟨hbc, ybc⟩ | exact ⟨hac, yac⟩
      | exact ⟨hab.symm, dY12_symm yab⟩ | exact ⟨hbc.symm, dY12_symm ybc⟩
      | exact ⟨hac.symm, dY12_symm yac⟩
  have vw : VInv F w := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [hbw]
    · simp only [hbw]
    · simp only [hbw]
    · simp only [hbw]
    rw [hkw, hlw, newbk, List.length_append]
    have := va.2.2.2.2
    simp only [List.length_cons, List.length_nil]
    omega
  have bind : ∀ y, (y = a ∨ y = b ∨ y = c) → Bind F y w := by
    intro y hy
    refine ⟨by rw [hlw, (abc y hy).2.1], ?_, by rw [hbw]; exact nbw y hy⟩
    rw [htw]; exact (sall y).1 hy
  -- children data
  have hF1 : ∀ z ∈ t1.vs, F z = lay enc t1 .m1 a b w (F a) (F b) (F w) 0 1 z := by
    intro z hz
    rw [hF z (RT.vs_nd.2 (Or.inr (Or.inl hz))), lay_m0_1 enc (by rintro rfl; exact w1o hz) hz, ← hFw0]
  have hF2 : ∀ z ∈ t2.vs, F z = lay enc t2 .m1 b c w (F b) (F c) (F w) 1 2 z := by
    intro z hz
    rw [hF z (RT.vs_nd.2 (Or.inr (Or.inr (Or.inl hz)))),
      lay_m0_2 enc (by rintro rfl; exact w2o hz) (fun h => Finset.disjoint_left.mp d12 h hz) hz, ← hFw0]
  have hF3 : ∀ z ∈ t3.vs, F z = lay enc t3 .m1 c a w (F c) (F a) (F w) 2 3 z := by
    intro z hz
    rw [hF z (RT.vs_nd.2 (Or.inr (Or.inr (Or.inr hz)))),
      lay_m0_3 enc (by rintro rfl; exact w3o hz) (fun h => Finset.disjoint_left.mp d13 h hz)
        (fun h => Finset.disjoint_left.mp d23 h hz), ← hFw0]
  have hg : star3 w a b c ⊔ t1.gr a b w ⊔ t2.gr b c w ⊔ t3.gr c a w ≤ H := hgr
  obtain ⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩ := by simpa only [sup_le_iff] using hg
  have hwa : H.Adj a w := (hg0 (star3_adj.2 ⟨nwa, Or.inl ⟨rfl, rfl⟩⟩)).symm
  have hwb : H.Adj b w := (hg0 (star3_adj.2 ⟨nwb, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)).symm
  have hwc : H.Adj c w :=
    (hg0 (star3_adj.2 ⟨nwc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)).symm
  have m1hyp : ∀ (t : RT V) (x y : V) (lo' hi' : ℚ), w ∉ t.vs → lo' < hi' →
      (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) →
      (∀ z ∈ t.vs, z ∈ (RT.nd w t1 t2 t3).vs) → Hyp F t .m1 x y w lo' hi' := by
    intro t x y lo' hi' ht hl hx hy hsub
    obtain ⟨bx1, bx2, bx3⟩ := bind x hx
    obtain ⟨by1, by2, by3⟩ := bind y hy
    exact ⟨vw, by rw [hbw]; exact ht, hl, bx1.symm, bx2, bx3, by1.symm, by2, by3,
      fun h => nbt x hx _ (hsub _ h) rfl, fun h => nbt y hy _ (hsub _ h) rfl⟩
  obtain ⟨g1, r1⟩ := ih1 .m1 a b w 0 1 w1 hg1 hab hwb hwa hF1
    (m1hyp t1 a b 0 1 w1o (by norm_num) (Or.inl rfl) (Or.inr (Or.inl rfl))
      (fun z h => RT.vs_nd.2 (Or.inr (Or.inl h))))
  obtain ⟨g2, r2⟩ := ih2 .m1 b c w 1 2 w2 hg2 hbc hwc hwb hF2
    (m1hyp t2 b c 1 2 w2o (by norm_num) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      (fun z h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inl h)))))
  obtain ⟨g3, r3⟩ := ih3 .m1 c a w 2 3 w3 hg3 hac.symm hwa hwc hF3
    (m1hyp t3 c a 2 3 w3o (by norm_num) (Or.inr (Or.inr rfl)) (Or.inl rfl)
      (fun z h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inr h)))))
  have R1 : Rng F t1 w 0 1 0 := by
    have := r1; simp only [Cnc] at this; rwa [hbw, hyw] at this
  have R2 : Rng F t2 w 1 2 0 := by
    have := r2; simp only [Cnc] at this; rwa [hbw, hyw] at this
  have R3 : Rng F t3 w 2 3 0 := by
    have := r3; simp only [Cnc] at this; rwa [hbw, hyw] at this
  have ha : a = a ∨ a = b ∨ a = c := Or.inl rfl
  have hb : b = a ∨ b = b ∨ b = c := Or.inr (Or.inl rfl)
  have hc : c = a ∨ c = b ∨ c = c := Or.inr (Or.inr rfl)
  -- star edges
  have starnb : ∀ x y, (star3 w a b c).Adj x y → (F x).bid ≠ (F y).bid := by
    intro x y h
    rw [star3_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · rw [hbw]; exact (nbw a ha).symm
    · rw [hbw]; exact nbw a ha
    · rw [hbw]; exact (nbw b hb).symm
    · rw [hbw]; exact nbw b hb
    · rw [hbw]; exact (nbw c hc).symm
    · rw [hbw]; exact nbw c hc
  have he : ∀ x y, (star3 w a b c).Adj x y → EInv F x y := by
    intro x y h
    rw [star3_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact Or.inr (Or.inr (bind a ha))
    · exact Or.inr (Or.inl (bind a ha))
    · exact Or.inr (Or.inr (bind b hb))
    · exact Or.inr (Or.inl (bind b hb))
    · exact Or.inr (Or.inr (bind c hc))
    · exact Or.inr (Or.inl (bind c hc))
  -- RInv of the apex
  have rw0 : RInv enc H F w := by
    refine ⟨by rw [hlw]; omega, fun _ _ => ?_⟩
    have m1 := (sall s.1.1).2 (Or.inl rfl)
    have m2 := (sall s.2.1.1).2 (Or.inr (Or.inl rfl))
    have m3 := (sall s.2.2.1).2 (Or.inr (Or.inr rfl))
    obtain ⟨n12, n23, n13⟩ := sne nab nbc nac
    obtain ⟨p12, y12⟩ := pr _ _ m1 m2 n12
    obtain ⟨p23, y23⟩ := pr _ _ m2 m3 n23
    obtain ⟨p13, y13⟩ := pr _ _ m1 m3 n13
    have cons := dY12_consec y12 y23 y13 sy1 sy2
    rw [htw, hkw, hlw]
    refine ⟨by rw [(abc _ m1).1, (abc _ m2).1], by rw [(abc _ m1).1, (abc _ m3).1],
      by rw [(abc _ m1).2.1], cons.1, cons.2, p12, p23, p13, ?_⟩
    rw [← sp]
    simp only [newbk, (abc _ m1).1, (abc _ m1).2.2.1]
  refine ⟨node_good enc ⟨vw, rw0⟩ g1 g2 g3 he (sif_nobag starnb) (cross_nobag starnb)
    (cross_nobag starnb) (cross_nobag starnb) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · exact cross_pivot (edgeZ_rng R1) (edgeZ_rng R2)
      (fun γ h1 h2 => Finset.disjoint_left.mp d12 h1 h2) w1o w2o
      (Or.inl (rowle_m0 le_rfl (by norm_num) le_rfl hyw hxw (nbw a ha) (nbw b hb) (nbw b hb)
        (nbw c hc)))
  · exact cross_pivot (edgeZ_rng R1) (edgeZ_rng R3)
      (fun γ h1 h2 => Finset.disjoint_left.mp d13 h1 h2) w1o w3o
      (Or.inl (rowle_m0 le_rfl (by norm_num) (by norm_num) hyw hxw (nbw a ha) (nbw b hb)
        (nbw c hc) (nbw a ha)))
  · exact cross_pivot (edgeZ_rng R2) (edgeZ_rng R3)
      (fun γ h1 h2 => Finset.disjoint_left.mp d23 h1 h2) w2o w3o
      (Or.inl (rowle_m0 (by norm_num) (by norm_num) le_rfl hyw hxw (nbw b hb) (nbw c hc)
        (nbw c hc) (nbw a ha)))
  · intro z' hz'
    rcases hz' with h | h | h | h
    · exact xinj_symm (xinj_rb R1 w1o (Or.inr ⟨hbw, Or.inr (Or.inr hyw.ge)⟩) z' h)
    · exact xinj_symm (xinj_rb R2 w2o (Or.inr ⟨hbw, Or.inr (Or.inr hyw.ge)⟩) z' h)
    · exact xinj_symm (xinj_rb R3 w3o (Or.inr ⟨hbw, Or.inr (Or.inr hyw.ge)⟩) z' h)
    · refine xinj_of (Or.inl ?_)
      rw [hbw]; exact fun e => nbw z' h e.symm
  · exact xinj_rr R1 R2 d12 w1o w2o (Or.inl le_rfl)
  · exact xinj_rr R1 R3 d13 w1o w3o (Or.inl (by norm_num))
  · exact xinj_rr R2 R3 d23 w2o w3o (Or.inl le_rfl)
  · exact xinj_rb R1 w1o (Or.inl ⟨nbw c hc, fun h => nbt c hc _ (RT.vs_nd.2 (Or.inr (Or.inl h))) rfl⟩)
  · exact xinj_rb R2 w2o
      (Or.inl ⟨nbw a ha, fun h => nbt a ha _ (RT.vs_nd.2 (Or.inr (Or.inr (Or.inl h)))) rfl⟩)
  · exact xinj_rb R3 w3o
      (Or.inl ⟨nbw b hb, fun h => nbt b hb _ (RT.vs_nd.2 (Or.inr (Or.inr (Or.inr h)))) rfl⟩)
  · intro z hz
    simp only [RT.vs_nd] at hz ⊢
    rcases hz with rfl | hz | hz | hz
    · exact Or.inl hbw
    · rcases R1 z hz with ⟨h, _⟩ | h
      exacts [Or.inl h, Or.inr (Or.inl h)]
    · rcases R2 z hz with ⟨h, _⟩ | h
      exacts [Or.inl h, Or.inr (Or.inr (Or.inl h))]
    · rcases R3 z hz with ⟨h, _⟩ | h
      exacts [Or.inl h, Or.inr (Or.inr (Or.inr h))]

omit [DecidableEq V] in
theorem sif_of_cross {G : SimpleGraph V} {F : V → Inf V} (h : Cross G G F) : SIF G F := by
  intro a b c d hab hcd e1 e2 e3 e4 e5 h1 h2
  rcases h a b c d hab hcd e1 e2 e3 e4 e5 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith

theorem edgeZ_star {F : V → Inf V} {v x y z β : V} (P : V → Prop) (hv : (F v).bid = β)
    (hPv : P v) (hl : ∀ l, (l = x ∨ l = y ∨ l = z) → (F l).bid = β → P l) :
    EdgeZ F (star3 v x y z) β P (fun _ => False) := by
  intro p q h e
  left
  rw [star3_adj] at h
  obtain ⟨_, h⟩ := h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at e ⊢
  · exact ⟨hv, hPv, hl x (Or.inl rfl) (e.symm.trans hv)⟩
  · exact ⟨e.trans hv, hl x (Or.inl rfl) (e.trans hv), hPv⟩
  · exact ⟨hv, hPv, hl y (Or.inr (Or.inl rfl)) (e.symm.trans hv)⟩
  · exact ⟨e.trans hv, hl y (Or.inr (Or.inl rfl)) (e.trans hv), hPv⟩
  · exact ⟨hv, hPv, hl z (Or.inr (Or.inr rfl)) (e.symm.trans hv)⟩
  · exact ⟨e.trans hv, hl z (Or.inr (Or.inr rfl)) (e.trans hv), hPv⟩

theorem rng_mono {F : V → Inf V} {t : RT V} {β : V} {lo hi lo' hi' : ℚ} {ym ym' : ℤ}
    (h : Rng F t β lo hi ym) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (h3 : ym ≤ ym') :
    Rng F t β lo' hi' ym' := by
  intro z hz
  rcases h z hz with ⟨e, l, u, y⟩ | h
  · exact Or.inl ⟨e, by linarith, by linarith, by omega⟩
  · exact Or.inr h

/-- STEP m1: a bag vertex stacked in a leg region `(a,b,c)` (`a b` in the parent bag). -/
theorem step_m1 (enc : V → ℕ) {H : SimpleGraph V} {F : V → Inf V} {u : V} {t1 t2 t3 : RT V}
    (ih1 : LayOK enc H F t1) (ih2 : LayOK enc H F t2) (ih3 : LayOK enc H F t3)
    {a b c : V} {lo hi : ℚ}
    (hwf : (RT.nd u t1 t2 t3).wf a b c) (hgr : (RT.nd u t1 t2 t3).gr a b c ≤ H)
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c)
    (hF : ∀ z ∈ (RT.nd u t1 t2 t3).vs,
      F z = lay enc (RT.nd u t1 t2 t3) .m1 a b c (F a) (F b) (F c) lo hi z)
    (hH : Hyp F (RT.nd u t1 t2 t3) .m1 a b c lo hi) :
    Good enc H F (RT.nd u t1 t2 t3) a b c ∧ Cnc F (RT.nd u t1 t2 t3) .m1 a b c lo hi := by
  obtain ⟨nab, nbc, nac, nua, nub, nuc, w1, w2, w3, ⟨a1, b1, u1o, c1⟩, ⟨b2, c2, u2o, a2⟩,
    ⟨c3, a3, u3o, b3⟩, d12, d13, d23⟩ := nd_wf hwf
  obtain ⟨vc, ncT, hlh, la, ta, nac', lb, tb, nbc', naT, nbT⟩ := hH
  have uT : u ∈ (RT.nd u t1 t2 t3).vs := RT.vs_nd.2 (Or.inl rfl)
  have mem1 : ∀ {z}, z ∈ t1.vs → z ∈ (RT.nd u t1 t2 t3).vs := fun h => RT.vs_nd.2 (Or.inr (Or.inl h))
  have mem2 : ∀ {z}, z ∈ t2.vs → z ∈ (RT.nd u t1 t2 t3).vs :=
    fun h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inl h)))
  have mem3 : ∀ {z}, z ∈ t3.vs → z ∈ (RT.nd u t1 t2 t3).vs :=
    fun h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inr h)))
  have hFu0 := hF u uT
  have hFu := hFu0
  rw [lay_m1_u] at hFu
  have hbu : (F u).bid = (F c).bid := by rw [hFu]
  have hlu : (F u).lev = (F c).lev := by rw [hFu]
  have hyu : (F u).Y = (F c).Y - 1 := by rw [hFu]
  have hxu : (F u).x = lo + (hi - lo) / 3 := by rw [hFu]
  have hku : (F u).bk = (F c).bk := by rw [hFu]
  have htu : (F u).tr = (F c).tr := by rw [hFu]
  have vu : VInv F u := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbu]; exact vc.1
    · rw [hbu, hlu]; exact vc.2.1
    · rw [hbu, hku]; exact vc.2.2.1
    · rw [hbu, htu]; exact vc.2.2.2.1
    · rw [hku, hlu]; exact vc.2.2.2.2
  have ru : RInv enc H F u := by
    refine ⟨by rw [hlu]; omega, fun e _ => ?_⟩
    exfalso
    rw [hbu] at e
    exact ncT (by rw [e]; exact uT)
  have n1 : (F c).bid ∉ t1.vs := fun h => ncT (mem1 h)
  have n2 : (F c).bid ∉ t2.vs := fun h => ncT (mem2 h)
  have n3 : (F c).bid ∉ t3.vs := fun h => ncT (mem3 h)
  have hF3 : ∀ z ∈ t3.vs, F z = lay enc t3 (.m2 false true) c a u (F c) (F a) (F u) lo
      (lo + (hi - lo) / 3) z := by
    intro z hz
    rw [hF z (mem3 hz), lay_m1_3 enc (by rintro rfl; exact u3o hz) hz, ← hFu0]
  have hF1 : ∀ z ∈ t1.vs, F z = lay enc t1 .m1 a b u (F a) (F b) (F u) (lo + (hi - lo) / 3)
      (lo + 2 * ((hi - lo) / 3)) z := by
    intro z hz
    rw [hF z (mem1 hz), lay_m1_1 enc (by rintro rfl; exact u1o hz)
      (fun h => Finset.disjoint_left.mp d13 hz h) hz, ← hFu0]
  have hF2 : ∀ z ∈ t2.vs, F z = lay enc t2 (.m2 true false) b c u (F b) (F c) (F u)
      (lo + 2 * ((hi - lo) / 3)) hi z := by
    intro z hz
    rw [hF z (mem2 hz), lay_m1_2 enc (by rintro rfl; exact u2o hz)
      (fun h => Finset.disjoint_left.mp d23 hz h) (fun h => Finset.disjoint_left.mp d12 h hz),
      ← hFu0]
  have hg : star3 u a b c ⊔ t1.gr a b u ⊔ t2.gr b c u ⊔ t3.gr c a u ≤ H := hgr
  obtain ⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩ := by simpa only [sup_le_iff] using hg
  have hua : H.Adj a u := (hg0 (star3_adj.2 ⟨nua, Or.inl ⟨rfl, rfl⟩⟩)).symm
  have hub : H.Adj b u := (hg0 (star3_adj.2 ⟨nub, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)).symm
  have huc : H.Adj c u :=
    (hg0 (star3_adj.2 ⟨nuc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)).symm
  have hy3 : Hyp F t3 (.m2 false true) c a u lo (lo + (hi - lo) / 3) := by
    simp only [Hyp, Bool.false_eq_true, if_false, if_true, ↓reduceIte]
    refine ⟨vc, vu, hbu.symm, by rw [hbu]; exact n3, by linarith, by unfold dY12; omega,
      by rw [hlu]; exact la, by rw [htu]; exact ta, by rw [hbu]; exact nac', ?_, fun _ => hxu.ge,
      fun h => naT (mem3 h)⟩
    intro h; exfalso; rw [hyu] at h; omega
  have hy1 : Hyp F t1 .m1 a b u (lo + (hi - lo) / 3) (lo + 2 * ((hi - lo) / 3)) := by
    simp only [Hyp]
    exact ⟨vu, by rw [hbu]; exact n1, by linarith, by rw [hlu]; exact la, by rw [htu]; exact ta,
      by rw [hbu]; exact nac', by rw [hlu]; exact lb, by rw [htu]; exact tb, by rw [hbu]; exact nbc',
      fun h => naT (mem1 h), fun h => nbT (mem1 h)⟩
  have hy2 : Hyp F t2 (.m2 true false) b c u (lo + 2 * ((hi - lo) / 3)) hi := by
    simp only [Hyp, Bool.false_eq_true, if_false, if_true, ↓reduceIte]
    refine ⟨vc, vu, hbu.symm, by rw [hbu]; exact n2, by linarith, by unfold dY12; omega,
      by rw [hlu]; exact lb, by rw [htu]; exact tb, by rw [hbu]; exact nbc', ?_, ?_,
      fun h => nbT (mem2 h)⟩
    · intro _; rw [hxu]; linarith
    · intro h; exfalso; rw [hyu] at h; omega
  obtain ⟨g3, r3⟩ := ih3 (.m2 false true) c a u lo (lo + (hi - lo) / 3) w3 hg3 hac.symm hua huc
    hF3 hy3
  obtain ⟨g1, r1⟩ := ih1 .m1 a b u (lo + (hi - lo) / 3) (lo + 2 * ((hi - lo) / 3)) w1 hg1 hab hub
    hua hF1 hy1
  obtain ⟨g2, r2⟩ := ih2 (.m2 true false) b c u (lo + 2 * ((hi - lo) / 3)) hi w2 hg2 hbc huc hub
    hF2 hy2
  have R3 : Rng F t3 (F c).bid lo (lo + (hi - lo) / 3) (F c).Y := by
    have := r3
    simp only [Cnc, Bool.false_eq_true, if_false, if_true, ↓reduceIte] at this
    rw [hbu] at this
    exact rng_mono this le_rfl le_rfl (by rw [hyu]; omega)
  have R1 : Rng F t1 (F c).bid (lo + (hi - lo) / 3) (lo + 2 * ((hi - lo) / 3)) ((F c).Y - 1) := by
    have := r1
    simp only [Cnc] at this
    rwa [hbu, hyu] at this
  have R2 : Rng F t2 (F c).bid (lo + 2 * ((hi - lo) / 3)) hi (F c).Y := by
    have := r2
    simp only [Cnc, Bool.false_eq_true, if_false, if_true, ↓reduceIte] at this
    rw [hbu] at this
    exact rng_mono this le_rfl le_rfl (by rw [hyu]; omega)
  -- the star
  have ezS : EdgeZ F (star3 u a b c) (F c).bid (fun z => z = c ∨ z = u) (fun _ => False) := by
    refine edgeZ_star _ hbu (Or.inr rfl) ?_
    intro l hl e
    rcases hl with h | h | h
    · rw [h] at e; exact absurd e nac'
    · rw [h] at e; exact absurd e nbc'
    · exact Or.inl h
  have he : ∀ x y, (star3 u a b c).Adj x y → EInv F x y := by
    have bA : Bind F a u := ⟨by rw [hlu]; exact la.symm, by rw [htu]; exact ta, by rw [hbu]; exact nac'⟩
    have bB : Bind F b u := ⟨by rw [hlu]; exact lb.symm, by rw [htu]; exact tb, by rw [hbu]; exact nbc'⟩
    intro x y h
    rw [star3_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact Or.inr (Or.inr bA)
    · exact Or.inr (Or.inl bA)
    · exact Or.inr (Or.inr bB)
    · exact Or.inr (Or.inl bB)
    · exact Or.inl ⟨hbu, by unfold dY12; omega⟩
    · exact Or.inl ⟨hbu.symm, by unfold dY12; omega⟩
  have hs : SIF (star3 u a b c) F := by
    refine sif_of_cross (cross_pivot ezS ezS (fun _ h _ => h) (fun h => h) (fun h => h) (Or.inl ?_))
    intro z z' hz hz' _ _ e
    rcases hz with h | h <;> rcases hz' with h' | h' <;> subst h h' <;>
      first | exact le_rfl | (exfalso; omega)
  refine ⟨node_good enc ⟨vu, ru⟩ g1 g2 g3 he hs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · -- star vs t1
    refine cross_pivot ezS (edgeZ_rng R1) (fun _ h _ => h) (fun h => h) n1 (Or.inl ?_)
    intro z z' hz hz' bz bz' e
    rcases hz with h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
      (try subst h) <;> (try subst h')
    all_goals first
      | exact le_rfl
      | (exfalso; omega)
      | exact absurd bz' nac'
      | exact absurd bz' nbc'
  · -- star vs t2
    refine cross_pivot ezS (edgeZ_rng R2) (fun _ h _ => h) (fun h => h) n2 (Or.inl ?_)
    intro z z' hz hz' bz bz' e
    rcases hz with h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
      (try subst h) <;> (try subst h')
    all_goals first
      | exact le_rfl
      | (exfalso; omega)
      | exact absurd bz' nac'
      | exact absurd bz' nbc'
      | linarith
  · -- star vs t3
    refine cross_pivot ezS (edgeZ_rng R3) (fun _ h _ => h) (fun h => h) n3 (Or.inr ?_)
    intro z z' hz hz' bz bz' e
    rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;> rcases hz' with h' | h' <;>
      (try subst h) <;> (try subst h')
    all_goals first
      | exact le_rfl
      | (exfalso; omega)
      | exact absurd bz nac'
      | exact absurd bz nbc'
      | linarith
  · -- t1 vs t2
    refine cross_pivot (edgeZ_rng R1) (edgeZ_rng R2)
      (fun γ h1 h2 => Finset.disjoint_left.mp d12 h1 h2) n1 n2 (Or.inl ?_)
    intro z z' hz hz' bz bz' e
    rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;>
      rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
      (try subst h) <;> (try subst h')
    all_goals first
      | exact le_rfl
      | (exfalso; omega)
      | exact absurd bz nac'
      | exact absurd bz nbc'
      | exact absurd bz' nac'
      | exact absurd bz' nbc'
      | linarith
  · -- t1 vs t3
    refine cross_pivot (edgeZ_rng R1) (edgeZ_rng R3)
      (fun γ h1 h2 => Finset.disjoint_left.mp d13 h1 h2) n1 n3 (Or.inr ?_)
    intro z z' hz hz' bz bz' e
    rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;>
      rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
      (try subst h) <;> (try subst h')
    all_goals first
      | exact le_rfl
      | (exfalso; omega)
      | exact absurd bz nac'
      | exact absurd bz nbc'
      | exact absurd bz' nac'
      | exact absurd bz' nbc'
      | linarith
  · -- t2 vs t3
    refine cross_pivot (edgeZ_rng R2) (edgeZ_rng R3)
      (fun γ h1 h2 => Finset.disjoint_left.mp d23 h1 h2) n2 n3 (Or.inr ?_)
    intro z z' hz hz' bz bz' e
    rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;>
      rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
      (try subst h) <;> (try subst h')
    all_goals first
      | exact le_rfl
      | (exfalso; omega)
      | exact absurd bz nac'
      | exact absurd bz nbc'
      | exact absurd bz' nac'
      | exact absurd bz' nbc'
      | linarith
  · intro z' hz'
    rcases hz' with h | h | h | h | h | h
    · exact xinj_symm (xinj_rb R1 n1 (Or.inr ⟨hbu, Or.inl hxu.le⟩) z' h)
    · exact xinj_symm (xinj_rb R2 n2 (Or.inr ⟨hbu, Or.inl (by rw [hxu]; linarith)⟩) z' h)
    · exact xinj_symm (xinj_rb R3 n3 (Or.inr ⟨hbu, Or.inr (Or.inl hxu.ge)⟩) z' h)
    · subst h; exact xinj_of (Or.inl (by rw [hbu]; exact fun e => nac' e.symm))
    · subst h; exact xinj_of (Or.inl (by rw [hbu]; exact fun e => nbc' e.symm))
    · subst h; exact xinj_of (Or.inr (Or.inl (by rw [hyu]; omega)))
  · exact xinj_rr R1 R2 d12 n1 n2 (Or.inl le_rfl)
  · exact xinj_rr R1 R3 d13 n1 n3 (Or.inr le_rfl)
  · exact xinj_rr R2 R3 d23 n2 n3 (Or.inr (by linarith))
  · exact xinj_rb R1 n1 (Or.inr ⟨rfl, Or.inr (Or.inr (by omega))⟩)
  · exact xinj_rb R2 n2 (Or.inl ⟨nac', fun h => naT (mem2 h)⟩)
  · exact xinj_rb R3 n3 (Or.inl ⟨nbc', fun h => nbT (mem3 h)⟩)
  · intro z hz
    rcases RT.vs_nd.1 hz with rfl | hz | hz | hz
    · exact Or.inl ⟨hbu, by rw [hxu]; linarith, by rw [hxu]; linarith, by rw [hyu]; omega⟩
    · rcases rng_mono (lo' := lo) (hi' := hi) (ym' := (F c).Y) R1 (by linarith) (by linarith) (by omega) z hz with h | h
      exacts [Or.inl h, Or.inr (mem1 h)]
    · rcases rng_mono (lo' := lo) (hi' := hi) (ym' := (F c).Y) R2 (by linarith) le_rfl le_rfl z hz with h | h
      exacts [Or.inl h, Or.inr (mem2 h)]
    · rcases rng_mono (lo' := lo) (hi' := hi) (ym' := (F c).Y) R3 le_rfl (by linarith) le_rfl z hz with h | h
      exacts [Or.inl h, Or.inr (mem3 h)]

end Steps


end PQL5

/-! C3 part M (session 6): the polygon step (mode m2) of `MainLay`. -/

namespace PQL5

section StepM2

variable {V : Type} [DecidableEq V]

theorem yapex_spec {ys yt : ℤ} (h : dY12 ys yt) :
    (yt - ys = 1 ∧ yapex ys yt = ys - 1) ∨ (ys - yt = 1 ∧ yapex ys yt = yt - 1) ∨
      (yt - ys = 2 ∧ yapex ys yt = ys + 1) ∨ (ys - yt = 2 ∧ yapex ys yt = yt + 1) := by
  unfold yapex
  unfold dY12 at h
  split_ifs with h1 <;> omega

set_option maxHeartbeats 4000000 in
/-- the combinatorial core of the polygon step: apex `v` on the bag edge `s t`, corner `p`,
children `S` (region with `p s v`), `T` (with `p t v`) and the new-bag child `M` (`s t v`). -/
theorem m2_core {F : V → Inf V} {p s t v : V} {tS tT tM : RT V} {GS GT GM : SimpleGraph V}
    {lo hi : ℚ} (dr : Bool)
    (hbs : (F s).bid = (F t).bid) (hbv : (F v).bid = (F t).bid) (nbp : (F p).bid ≠ (F t).bid)
    (hY : dY12 (F s).Y (F t).Y) (hyv : (F v).Y = yapex (F s).Y (F t).Y)
    (hxv : (F v).x = (lo + hi) / 2) (hlh : lo < hi)
    (hsx : (if dr then (F s).x ≤ lo else hi ≤ (F s).x) ∨ (F t).Y < (F s).Y)
    (htx : (if dr then hi ≤ (F t).x else (F t).x ≤ lo) ∨ (F s).Y < (F t).Y)
    (nS : (F t).bid ∉ tS.vs) (nT : (F t).bid ∉ tT.vs) (nM : (F t).bid ∉ tM.vs)
    (dST : Disjoint tS.vs tT.vs) (dSM : Disjoint tS.vs tM.vs) (dTM : Disjoint tT.vs tM.vs)
    (RS : Rng F tS (F t).bid (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi)
      (max (F s).Y (F v).Y))
    (RT' : Rng F tT (F t).bid (if dr then (lo + hi) / 2 else lo) (if dr then hi else (lo + hi) / 2)
      (max (F t).Y (F v).Y))
    (hM : ∀ z ∈ tM.vs, (F z).bid ∈ tM.vs)
    (ezS : EdgeZ F GS (F t).bid (fun z => (z ∈ tS.vs ∧ (if dr then lo else (lo + hi) / 2) < (F z).x ∧
      (F z).x < (if dr then (lo + hi) / 2 else hi) ∧ (F z).Y < max (F s).Y (F v).Y) ∨ z = p ∨ z = s ∨
      z = v) (· ∈ tS.vs))
    (ezT : EdgeZ F GT (F t).bid (fun z => (z ∈ tT.vs ∧ (if dr then (lo + hi) / 2 else lo) < (F z).x ∧
      (F z).x < (if dr then hi else (lo + hi) / 2) ∧ (F z).Y < max (F t).Y (F v).Y) ∨ z = p ∨ z = t ∨
      z = v) (· ∈ tT.vs))
    (ezM : EdgeZ F GM (F t).bid (fun _ => False) (· ∈ tM.vs))
    (npM : (F p).bid ∉ tM.vs) (hlp : (F v).lev = (F p).lev + 1) (htp : trs p (F v).tr) :
    (∀ x y, (star3 v p s t).Adj x y → EInv F x y) ∧ SIF (star3 v p s t) F ∧
    Cross (star3 v p s t) GS F ∧ Cross (star3 v p s t) GT F ∧ Cross (star3 v p s t) GM F ∧
    Cross GS GT F ∧ Cross GS GM F ∧ Cross GT GM F ∧
    (∀ z', (z' ∈ tS.vs ∨ z' ∈ tT.vs ∨ z' ∈ tM.vs ∨ z' = p ∨ z' = s ∨ z' = t) → XInj F v z') ∧
    (∀ z ∈ tS.vs, ∀ z' ∈ tT.vs, XInj F z z') ∧ (∀ z ∈ tS.vs, ∀ z' ∈ tM.vs, XInj F z z') ∧
    (∀ z ∈ tT.vs, ∀ z' ∈ tM.vs, XInj F z z') ∧
    (∀ z ∈ tS.vs, XInj F z t) ∧ (∀ z ∈ tT.vs, XInj F z s) ∧ (∀ z ∈ tM.vs, XInj F z p) ∧
    (∀ z, (z = v ∨ z ∈ tS.vs ∨ z ∈ tT.vs ∨ z ∈ tM.vs) →
      ((F z).bid = (F t).bid ∧ lo < (F z).x ∧ (F z).x < hi ∧ (F z).Y < max (F s).Y (F t).Y) ∨
      (F z).bid ∈ tS.vs ∨ (F z).bid ∈ tT.vs ∨ (F z).bid ∈ tM.vs) := by
  have hyp := yapex_spec hY
  rw [← hyv] at hyp
  have hsv : (F v).bid = (F s).bid := hbv.trans hbs.symm
  have ezStar : EdgeZ F (star3 v p s t) (F t).bid (fun z => z = s ∨ z = t ∨ z = v)
      (fun _ => False) := by
    refine edgeZ_star _ hbv (Or.inr (Or.inr rfl)) ?_
    intro l hl e
    rcases hl with h | h | h
    · rw [h] at e; exact absurd e nbp
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have bindP : Bind F p v := ⟨hlp, htp, by rw [hbv]; exact nbp⟩
  have X1 : ∀ x y, (star3 v p s t).Adj x y → EInv F x y := by
    intro x y h
    rw [star3_adj] at h
    obtain ⟨_, h⟩ := h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact Or.inr (Or.inr bindP)
    · exact Or.inr (Or.inl bindP)
    · exact Or.inl ⟨hsv, by unfold dY12; omega⟩
    · exact Or.inl ⟨hsv.symm, by unfold dY12; omega⟩
    · exact Or.inl ⟨hbv, by unfold dY12; omega⟩
    · exact Or.inl ⟨hbv.symm, by unfold dY12; omega⟩
  have X2 : SIF (star3 v p s t) F := by
    refine sif_of_cross (cross_pivot ezStar ezStar (fun _ h _ => h) (fun h => h) (fun h => h)
      (Or.inl ?_))
    intro z z' hz hz' _ _ e
    rcases hz with h | h | h <;> rcases hz' with h' | h' | h' <;> subst h h'
    all_goals first
      | exact le_rfl
      | (exfalso; unfold dY12 at hY; omega)
  have X3 : Cross (star3 v p s t) GS F := by
    have nsv : (F v).Y ≠ (F s).Y := by omega
    rcases lt_or_gt_of_ne nsv with hv | hv
    · refine cross_mix (T0 := s) (P := fun z => z = t ∨ z = v) ?_ ezS nS ?_ ?_
      · intro x y h e
        rw [star3_adj] at h
        obtain ⟨_, h⟩ := h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [h1, h2] at e ⊢
        · exfalso; rw [hbv] at e; exact nbp e.symm
        · exfalso; rw [hbv] at e; exact nbp e
        all_goals refine ⟨by first | exact hbv | exact hbs | rfl, ?_⟩
        all_goals first
          | exact Or.inl (Or.inl rfl)
          | exact Or.inl (Or.inr rfl)
          | exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
      · intro z hz bz ez
        rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h
        · exfalso; omega
        · subst h; exact absurd bz nbp
        · exact h
        · subst h; exfalso; omega
      · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hsx htx ⊢
        · refine Or.inl ?_
          intro z z' hz hz' bz bz' e
          rcases hz with h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz')
            | linarith
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
        · refine Or.inr ?_
          intro z z' hz hz' bz bz' e
          rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;> rcases hz' with h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz)
            | linarith
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
    · refine cross_mix (T0 := v) (P := fun z => z = t ∨ z = v) ?_ ezS nS ?_ ?_
      · intro x y h e
        rw [star3_adj] at h
        obtain ⟨_, h⟩ := h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [h1, h2] at e ⊢
        · exfalso; rw [hbv] at e; exact nbp e.symm
        · exfalso; rw [hbv] at e; exact nbp e
        all_goals refine ⟨by first | exact hbv | exact hbs | rfl, ?_⟩
        all_goals first
          | exact Or.inl (Or.inl rfl)
          | exact Or.inl (Or.inr rfl)
          | exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
      · intro z hz bz ez
        rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h
        · exfalso; omega
        · subst h; exact absurd bz nbp
        · subst h; exfalso; omega
        · exact h
      · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hsx htx ⊢
        · refine Or.inl ?_
          intro z z' hz hz' bz bz' e
          rcases hz with h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz')
            | linarith
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
        · refine Or.inr ?_
          intro z z' hz hz' bz bz' e
          rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;> rcases hz' with h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz)
            | linarith
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
  have X4 : Cross (star3 v p s t) GT F := by
    have ntv : (F v).Y ≠ (F t).Y := by omega
    rcases lt_or_gt_of_ne ntv with hv | hv
    · refine cross_mix (T0 := t) (P := fun z => z = s ∨ z = v) ?_ ezT nT ?_ ?_
      · intro x y h e
        rw [star3_adj] at h
        obtain ⟨_, h⟩ := h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [h1, h2] at e ⊢
        · exfalso; rw [hbv] at e; exact nbp e.symm
        · exfalso; rw [hbv] at e; exact nbp e
        all_goals refine ⟨by first | exact hbv | exact hbs | rfl, ?_⟩
        all_goals first
          | exact Or.inl (Or.inl rfl)
          | exact Or.inl (Or.inr rfl)
          | exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
      · intro z hz bz ez
        rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h
        · exfalso; omega
        · subst h; exact absurd bz nbp
        · exact h
        · subst h; exfalso; omega
      · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hsx htx ⊢
        · refine Or.inr ?_
          intro z z' hz hz' bz bz' e
          rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;> rcases hz' with h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz)
            | (exfalso; exact nbp bz')
            | linarith
            | (rcases hsx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases hsx with q | q <;> rcases htx with q' | q' <;> first | linarith | (exfalso; omega))
        · refine Or.inl ?_
          intro z z' hz hz' bz bz' e
          rcases hz with h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz)
            | (exfalso; exact nbp bz')
            | linarith
            | (rcases hsx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases hsx with q | q <;> rcases htx with q' | q' <;> first | linarith | (exfalso; omega))
    · refine cross_mix (T0 := v) (P := fun z => z = s ∨ z = v) ?_ ezT nT ?_ ?_
      · intro x y h e
        rw [star3_adj] at h
        obtain ⟨_, h⟩ := h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [h1, h2] at e ⊢
        · exfalso; rw [hbv] at e; exact nbp e.symm
        · exfalso; rw [hbv] at e; exact nbp e
        all_goals refine ⟨by first | exact hbv | exact hbs | rfl, ?_⟩
        all_goals first
          | exact Or.inl (Or.inl rfl)
          | exact Or.inl (Or.inr rfl)
          | exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
          | exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
      · intro z hz bz ez
        rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h
        · exfalso; omega
        · subst h; exact absurd bz nbp
        · subst h; exfalso; omega
        · exact h
      · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hsx htx ⊢
        · refine Or.inr ?_
          intro z z' hz hz' bz bz' e
          rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;> rcases hz' with h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz)
            | (exfalso; exact nbp bz')
            | linarith
            | (rcases hsx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases hsx with q | q <;> rcases htx with q' | q' <;> first | linarith | (exfalso; omega))
        · refine Or.inl ?_
          intro z z' hz hz' bz bz' e
          rcases hz with h | h <;> rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
            (try subst h) <;> (try subst h')
          all_goals first
            | exact le_rfl
            | (exfalso; omega)
            | (exfalso; exact nbp bz)
            | (exfalso; exact nbp bz')
            | linarith
            | (rcases hsx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
            | (rcases hsx with q | q <;> rcases htx with q' | q' <;> first | linarith | (exfalso; omega))
  have X5 : Cross (star3 v p s t) GM F :=
    cross_pivot ezStar ezM (fun _ h _ => h) (fun h => h) nM (Or.inl (fun _ _ _ h => h.elim))
  have X6 : Cross GS GT F := by
    refine cross_pivot ezS ezT (fun γ h1 h2 => Finset.disjoint_left.mp dST h1 h2) nS nT ?_
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hsx htx ⊢
    · refine Or.inr ?_
      intro z z' hz hz' bz bz' e
      rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;>
        rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
        (try subst h) <;> (try subst h')
      all_goals first
        | exact le_rfl
        | (exfalso; omega)
        | (exfalso; exact nbp bz)
        | (exfalso; exact nbp bz')
        | linarith
        | (rcases hsx with q | q <;> first | linarith | (exfalso; omega))
        | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
        | (rcases hsx with q | q <;> rcases htx with q' | q' <;> first | linarith | (exfalso; omega))
    · refine Or.inl ?_
      intro z z' hz hz' bz bz' e
      rcases hz with ⟨_, h1, h2, h3⟩ | h | h | h <;>
        rcases hz' with ⟨_, h1', h2', h3'⟩ | h' | h' | h' <;>
        (try subst h) <;> (try subst h')
      all_goals first
        | exact le_rfl
        | (exfalso; omega)
        | (exfalso; exact nbp bz)
        | (exfalso; exact nbp bz')
        | linarith
        | (rcases hsx with q | q <;> first | linarith | (exfalso; omega))
        | (rcases htx with q | q <;> first | linarith | (exfalso; omega))
        | (rcases hsx with q | q <;> rcases htx with q' | q' <;> first | linarith | (exfalso; omega))
  have X7 : Cross GS GM F :=
    cross_pivot ezS ezM (fun γ h1 h2 => Finset.disjoint_left.mp dSM h1 h2) nS nM
      (Or.inl (fun _ _ _ h => h.elim))
  have X8 : Cross GT GM F :=
    cross_pivot ezT ezM (fun γ h1 h2 => Finset.disjoint_left.mp dTM h1 h2) nT nM
      (Or.inl (fun _ _ _ h => h.elim))
  have X9 : ∀ z', (z' ∈ tS.vs ∨ z' ∈ tT.vs ∨ z' ∈ tM.vs ∨ z' = p ∨ z' = s ∨ z' = t) →
      XInj F v z' := by
    intro z' hz'
    rcases hz' with h | h | h | h | h | h
    · refine xinj_symm (xinj_rb RS nS (Or.inr ⟨hbv, ?_⟩) z' h)
      rw [hxv]; cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte]
      · exact Or.inl le_rfl
      · exact Or.inr (Or.inl le_rfl)
    · refine xinj_symm (xinj_rb RT' nT (Or.inr ⟨hbv, ?_⟩) z' h)
      rw [hxv]; cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte]
      · exact Or.inr (Or.inl le_rfl)
      · exact Or.inl le_rfl
    · exact xinj_symm (xinj_rb (rng_of_m0 hM (F t).bid (F v).x (F v).x 0) nM
        (Or.inr ⟨hbv, Or.inl le_rfl⟩) z' h)
    · subst h; exact xinj_of (Or.inl (by rw [hbv]; exact fun e => nbp e.symm))
    · subst h; exact xinj_of (Or.inr (Or.inl (by omega)))
    · subst h; exact xinj_of (Or.inr (Or.inl (by omega)))
  have X10 : ∀ z ∈ tS.vs, ∀ z' ∈ tT.vs, XInj F z z' := by
    refine xinj_rr RS RT' dST nS nT ?_
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte]
    · exact Or.inr le_rfl
    · exact Or.inl le_rfl
  have X11 : ∀ z ∈ tS.vs, ∀ z' ∈ tM.vs, XInj F z z' :=
    xinj_rr RS (rng_of_m0 hM (F t).bid _ 0 0) dSM nS nM (Or.inl le_rfl)
  have X12 : ∀ z ∈ tT.vs, ∀ z' ∈ tM.vs, XInj F z z' :=
    xinj_rr RT' (rng_of_m0 hM (F t).bid _ 0 0) dTM nT nM (Or.inl le_rfl)
  have X13 : ∀ z ∈ tS.vs, XInj F z t := by
    refine xinj_rb RS nS (Or.inr ⟨rfl, ?_⟩)
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at htx ⊢ <;> rcases htx with q | q
    all_goals first
      | exact Or.inl (by linarith)
      | exact Or.inr (Or.inl (by linarith))
      | exact Or.inr (Or.inr (by omega))
  have X14 : ∀ z ∈ tT.vs, XInj F z s := by
    refine xinj_rb RT' nT (Or.inr ⟨hbs, ?_⟩)
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at hsx ⊢ <;> rcases hsx with q | q
    all_goals first
      | exact Or.inl (by linarith)
      | exact Or.inr (Or.inl (by linarith))
      | exact Or.inr (Or.inr (by omega))
  have X15 : ∀ z ∈ tM.vs, XInj F z p :=
    xinj_rb (rng_of_m0 hM (F t).bid 0 0 0) nM (Or.inl ⟨nbp, npM⟩)
  have X16 : ∀ z, (z = v ∨ z ∈ tS.vs ∨ z ∈ tT.vs ∨ z ∈ tM.vs) →
      ((F z).bid = (F t).bid ∧ lo < (F z).x ∧ (F z).x < hi ∧ (F z).Y < max (F s).Y (F t).Y) ∨
      (F z).bid ∈ tS.vs ∨ (F z).bid ∈ tT.vs ∨ (F z).bid ∈ tM.vs := by
    intro z hz
    rcases hz with h | h | h | h
    · subst h
      exact Or.inl ⟨hbv, by rw [hxv]; linarith, by rw [hxv]; linarith, by omega⟩
    · rcases RS z h with ⟨b, l, u, y⟩ | i
      · refine Or.inl ⟨b, ?_, ?_, by omega⟩ <;> cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at l u <;> linarith
      · exact Or.inr (Or.inl i)
    · rcases RT' z h with ⟨b, l, u, y⟩ | i
      · refine Or.inl ⟨b, ?_, ?_, by omega⟩ <;> cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, ↓reduceIte] at l u <;> linarith
      · exact Or.inr (Or.inr (Or.inl i))
    · exact Or.inr (Or.inr (Or.inr (hM z h)))
  exact ⟨X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16⟩

omit [DecidableEq V] in
theorem edgeZ_mono {F : V → Inf V} {G : SimpleGraph V} {β : V} {P P' S : V → Prop}
    (h : EdgeZ F G β P S) (hP : ∀ z, P z → P' z) : EdgeZ F G β P' S := by
  intro x y hxy e
  rcases h x y hxy e with ⟨b, px, py⟩ | h
  · exact Or.inl ⟨b, hP x px, hP y py⟩
  · exact Or.inr h

theorem star3_swap (v x y z : V) : star3 v x y z = star3 v y x z := by
  ext p q
  simp only [star3_adj]
  tauto

omit [DecidableEq V] in
theorem vinv_eq {F : V → Inf V} {x y : V} (vx : VInv F x) (vy : VInv F y)
    (e : (F x).bid = (F y).bid) :
    (F x).lev = (F y).lev ∧ (F x).bk = (F y).bk ∧ (F x).tr = (F y).tr := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← vx.2.1, ← vy.2.1, e]
  · rw [← vx.2.2.1, ← vy.2.2.1, e]
  · rw [← vx.2.2.2.1, ← vy.2.2.2.1, e]

/-- STEP m2, corner at position a (`pa = true`): region `(p,s,t) = (a,b,c)`. -/
theorem step_m2A (enc : V → ℕ) {H : SimpleGraph V} {F : V → Inf V} {v : V} {t1 t2 t3 : RT V}
    (ih1 : LayOK enc H F t1) (ih2 : LayOK enc H F t2) (ih3 : LayOK enc H F t3)
    {a b c : V} {lo hi : ℚ} (dr : Bool)
    (hwf : (RT.nd v t1 t2 t3).wf a b c) (hgr : (RT.nd v t1 t2 t3).gr a b c ≤ H)
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c)
    (hF : ∀ z ∈ (RT.nd v t1 t2 t3).vs,
      F z = lay enc (RT.nd v t1 t2 t3) (.m2 true dr) a b c (F a) (F b) (F c) lo hi z)
    (hH : Hyp F (RT.nd v t1 t2 t3) (.m2 true dr) a b c lo hi) :
    Good enc H F (RT.nd v t1 t2 t3) a b c ∧ Cnc F (RT.nd v t1 t2 t3) (.m2 true dr) a b c lo hi := by
  obtain ⟨nab, nbc, nac, nva, nvb, nvc, w1, w2, w3, ⟨a1, b1, v1o, c1⟩, ⟨b2, c2, v2o, a2⟩,
    ⟨c3, a3, v3o, b3⟩, d12, d13, d23⟩ := nd_wf hwf
  simp only [Hyp, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at hH
  obtain ⟨vb, vc, ebc, ncT, hlh, ybc, la, ta, nac', o1, o2, naT⟩ := hH
  have vT : v ∈ (RT.nd v t1 t2 t3).vs := RT.vs_nd.2 (Or.inl rfl)
  have mem1 : ∀ {z}, z ∈ t1.vs → z ∈ (RT.nd v t1 t2 t3).vs := fun h => RT.vs_nd.2 (Or.inr (Or.inl h))
  have mem2 : ∀ {z}, z ∈ t2.vs → z ∈ (RT.nd v t1 t2 t3).vs :=
    fun h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inl h)))
  have mem3 : ∀ {z}, z ∈ t3.vs → z ∈ (RT.nd v t1 t2 t3).vs :=
    fun h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inr h)))
  have hFv0 := hF v vT
  have hFv := hFv0
  rw [lay_m2_v] at hFv
  have hbv : (F v).bid = (F b).bid := by rw [hFv] <;> rfl
  have hlv : (F v).lev = (F b).lev := by rw [hFv] <;> rfl
  have hyv : (F v).Y = yapex (F b).Y (F c).Y := by rw [hFv] <;> rfl
  have hxv : (F v).x = (lo + hi) / 2 := by rw [hFv]
  have hkv : (F v).bk = (F b).bk := by rw [hFv] <;> rfl
  have htv : (F v).tr = (F b).tr := by rw [hFv] <;> rfl
  have hbv' : (F v).bid = (F c).bid := hbv.trans ebc
  obtain ⟨lbc, _, tbc⟩ := vinv_eq vb vc ebc
  have hyp := yapex_spec ybc
  rw [← hyv] at hyp
  have vv : VInv F v := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbv]; exact vb.1
    · rw [hbv, hlv]; exact vb.2.1
    · rw [hbv, hkv]; exact vb.2.2.1
    · rw [hbv, htv]; exact vb.2.2.2.1
    · rw [hkv, hlv]; exact vb.2.2.2.2
  have rv : RInv enc H F v := by
    refine ⟨by rw [hlv, lbc]; omega, fun e _ => ?_⟩
    exfalso
    rw [hbv'] at e
    exact ncT (by rw [e]; exact vT)
  have hlp : (F v).lev = (F a).lev + 1 := by rw [hlv, lbc]; exact la.symm
  have htp : trs a (F v).tr := by rw [htv, tbc]; exact ta
  have hF1 : ∀ z ∈ t1.vs, F z = lay enc t1 (.m2 true dr) a b v (F a) (F b) (F v)
      (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi) z := by
    intro z hz
    rw [hF z (mem1 hz), lay_mA_1 enc (by rintro rfl; exact v1o hz) hz, ← hFv0]
  have hF3 : ∀ z ∈ t3.vs, F z = lay enc t3 (.m2 false (!dr)) c a v (F c) (F a) (F v)
      (if dr then (lo + hi) / 2 else lo) (if dr then hi else (lo + hi) / 2) z := by
    intro z hz
    rw [hF z (mem3 hz), lay_mA_3 enc (by rintro rfl; exact v3o hz)
      (fun h => Finset.disjoint_left.mp d13 h hz) hz, ← hFv0]
  have hF2 : ∀ z ∈ t2.vs, F z = lay enc t2 .m0 b c v (F b) (F c) (F v) 0 0 z := by
    intro z hz
    rw [hF z (mem2 hz), lay_mA_2 enc (by rintro rfl; exact v2o hz)
      (fun h => Finset.disjoint_left.mp d12 h hz) (fun h => Finset.disjoint_left.mp d23 hz h),
      ← hFv0]
  have hg : star3 v a b c ⊔ t1.gr a b v ⊔ t2.gr b c v ⊔ t3.gr c a v ≤ H := hgr
  obtain ⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩ := by simpa only [sup_le_iff] using hg
  have hav : H.Adj a v := (hg0 (star3_adj.2 ⟨nva, Or.inl ⟨rfl, rfl⟩⟩)).symm
  have hbv2 : H.Adj b v := (hg0 (star3_adj.2 ⟨nvb, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)).symm
  have hcv : H.Adj c v :=
    (hg0 (star3_adj.2 ⟨nvc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)).symm
  have hy1 : Hyp F t1 (.m2 true dr) a b v (if dr then lo else (lo + hi) / 2)
      (if dr then (lo + hi) / 2 else hi) := by
    simp only [Hyp, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte]
    refine ⟨vb, vv, hbv.symm, by rw [hbv']; exact fun h => ncT (mem1 h), ?_,
      by unfold dY12; omega, hlp.symm, htp, by rw [hbv']; exact nac', ?_, ?_,
      fun h => naT (mem1 h)⟩
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;> linarith
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact hxv.le
      · exact o1 (by omega)
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact o2 (by omega)
      · exact hxv.ge
  have hy3 : Hyp F t3 (.m2 false (!dr)) c a v (if dr then (lo + hi) / 2 else lo)
      (if dr then hi else (lo + hi) / 2) := by
    simp only [Hyp, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte]
    refine ⟨vc, vv, hbv'.symm, by rw [hbv']; exact fun h => ncT (mem3 h), ?_,
      by unfold dY12; omega, hlp.symm, htp, by rw [hbv']; exact nac', ?_, ?_,
      fun h => naT (mem3 h)⟩
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;> linarith
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact o1 (by omega)
      · exact hxv.le
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact hxv.ge
      · exact o2 (by omega)
  have hy2 : Hyp F t2 .m0 b c v 0 0 := by
    simp only [Hyp]
    exact ⟨vb, vc, vv, ebc, hbv.symm, by rw [ebc]; exact fun h => ncT (mem2 h), lbc, hlv.symm,
      ybc, by unfold dY12; omega, by unfold dY12; omega⟩
  obtain ⟨g1, r1⟩ := ih1 (.m2 true dr) a b v _ _ w1 hg1 hab hbv2 hav hF1 hy1
  obtain ⟨g3, r3⟩ := ih3 (.m2 false (!dr)) c a v _ _ w3 hg3 hac.symm hav hcv hF3 hy3
  obtain ⟨g2, r2⟩ := ih2 .m0 b c v 0 0 w2 hg2 hbc hcv hbv2 hF2 hy2
  have RS : Rng F t1 (F c).bid (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi)
      (max (F b).Y (F v).Y) := by
    have := r1
    simp only [Cnc, if_true, ↓reduceIte] at this
    rwa [hbv'] at this
  have RT' : Rng F t3 (F c).bid (if dr then (lo + hi) / 2 else lo)
      (if dr then hi else (lo + hi) / 2) (max (F c).Y (F v).Y) := by
    have := r3
    simp only [Cnc, if_false, Bool.false_eq_true, ↓reduceIte] at this
    rwa [hbv'] at this
  have hM : ∀ z ∈ t2.vs, (F z).bid ∈ t2.vs := by simpa only [Cnc] using r2
  have hne : (F b).Y ≠ (F c).Y := by unfold dY12 at ybc; omega
  have hsx : (if dr then (F b).x ≤ lo else hi ≤ (F b).x) ∨ (F c).Y < (F b).Y := by
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (o2 (by omega))
    · exact Or.inr h
    · exact Or.inl (o1 (by omega))
    · exact Or.inr h
  have htx : (if dr then hi ≤ (F c).x else (F c).x ≤ lo) ∨ (F b).Y < (F c).Y := by
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl (o1 (by omega))
    · exact Or.inr h
    · exact Or.inl (o2 (by omega))
  obtain ⟨X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16⟩ :=
    m2_core (p := a) (s := b) (t := c) (v := v) (tS := t1) (tT := t3) (tM := t2)
      (GS := t1.gr a b v) (GT := t3.gr c a v) (GM := t2.gr b c v) dr ebc hbv' nac' ybc hyv hxv hlh
      hsx htx (fun h => ncT (mem1 h)) (fun h => ncT (mem3 h)) (fun h => ncT (mem2 h)) d13 d12
      (Disjoint.symm d23) RS RT' hM (edgeZ_rng RS)
      (edgeZ_mono (edgeZ_rng RT') (fun z hz => by
        rcases hz with h | h | h | h
        exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h))]))
      (edgeZ_m0 hM) (fun h => naT (mem2 h)) hlp htp
  refine ⟨node_good enc ⟨vv, rv⟩ g1 g2 g3 X1 X2 X3 X5 X4 X7 X6 (cross_symm X8) ?_ X11 X10
    (fun z hz z' hz' => xinj_symm (X12 z' hz' z hz)) X13 X15 X14, ?_⟩
  · intro z' h
    refine X9 z' ?_
    rcases h with h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h))]
  · simp only [Cnc, if_true, ↓reduceIte]
    intro z hz
    have hz' : z = v ∨ z ∈ t1.vs ∨ z ∈ t3.vs ∨ z ∈ t2.vs := by
      rcases RT.vs_nd.1 hz with h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h)), Or.inr (Or.inr (Or.inl h))]
    rcases X16 z hz' with h | h | h | h
    exacts [Or.inl h, Or.inr (mem1 h), Or.inr (mem3 h), Or.inr (mem2 h)]

/-- STEP m2, corner at position b (`pa = false`): region `(s,p,t) = (a,b,c)`. -/
theorem step_m2B (enc : V → ℕ) {H : SimpleGraph V} {F : V → Inf V} {v : V} {t1 t2 t3 : RT V}
    (ih1 : LayOK enc H F t1) (ih2 : LayOK enc H F t2) (ih3 : LayOK enc H F t3)
    {a b c : V} {lo hi : ℚ} (dr : Bool)
    (hwf : (RT.nd v t1 t2 t3).wf a b c) (hgr : (RT.nd v t1 t2 t3).gr a b c ≤ H)
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c)
    (hF : ∀ z ∈ (RT.nd v t1 t2 t3).vs,
      F z = lay enc (RT.nd v t1 t2 t3) (.m2 false dr) a b c (F a) (F b) (F c) lo hi z)
    (hH : Hyp F (RT.nd v t1 t2 t3) (.m2 false dr) a b c lo hi) :
    Good enc H F (RT.nd v t1 t2 t3) a b c ∧ Cnc F (RT.nd v t1 t2 t3) (.m2 false dr) a b c lo hi := by
  obtain ⟨nab, nbc, nac, nva, nvb, nvc, w1, w2, w3, ⟨a1, b1, v1o, c1⟩, ⟨b2, c2, v2o, a2⟩,
    ⟨c3, a3, v3o, b3⟩, d12, d13, d23⟩ := nd_wf hwf
  simp only [Hyp, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at hH
  obtain ⟨va, vc, eac, ncT, hlh, yac, lb, tb, nbc', o1, o2, nbT⟩ := hH
  have vT : v ∈ (RT.nd v t1 t2 t3).vs := RT.vs_nd.2 (Or.inl rfl)
  have mem1 : ∀ {z}, z ∈ t1.vs → z ∈ (RT.nd v t1 t2 t3).vs := fun h => RT.vs_nd.2 (Or.inr (Or.inl h))
  have mem2 : ∀ {z}, z ∈ t2.vs → z ∈ (RT.nd v t1 t2 t3).vs :=
    fun h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inl h)))
  have mem3 : ∀ {z}, z ∈ t3.vs → z ∈ (RT.nd v t1 t2 t3).vs :=
    fun h => RT.vs_nd.2 (Or.inr (Or.inr (Or.inr h)))
  have hFv0 := hF v vT
  have hFv := hFv0
  rw [lay_m2_v] at hFv
  have hav0 : (F v).bid = (F a).bid := by rw [hFv] <;> rfl
  have hlv : (F v).lev = (F a).lev := by rw [hFv] <;> rfl
  have hyv : (F v).Y = yapex (F a).Y (F c).Y := by rw [hFv] <;> rfl
  have hxv : (F v).x = (lo + hi) / 2 := by rw [hFv]
  have hkv : (F v).bk = (F a).bk := by rw [hFv] <;> rfl
  have htv : (F v).tr = (F a).tr := by rw [hFv] <;> rfl
  have hbv' : (F v).bid = (F c).bid := hav0.trans eac
  obtain ⟨lac, _, tac⟩ := vinv_eq va vc eac
  have hyp := yapex_spec yac
  rw [← hyv] at hyp
  have vv : VInv F v := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hav0]; exact va.1
    · rw [hav0, hlv]; exact va.2.1
    · rw [hav0, hkv]; exact va.2.2.1
    · rw [hav0, htv]; exact va.2.2.2.1
    · rw [hkv, hlv]; exact va.2.2.2.2
  have rv : RInv enc H F v := by
    refine ⟨by rw [hlv, lac]; omega, fun e _ => ?_⟩
    exfalso
    rw [hbv'] at e
    exact ncT (by rw [e]; exact vT)
  have hlp : (F v).lev = (F b).lev + 1 := by rw [hlv, lac]; exact lb.symm
  have htp : trs b (F v).tr := by rw [htv, tac]; exact tb
  have hF1 : ∀ z ∈ t1.vs, F z = lay enc t1 (.m2 false dr) a b v (F a) (F b) (F v)
      (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi) z := by
    intro z hz
    rw [hF z (mem1 hz), lay_mB_1 enc (by rintro rfl; exact v1o hz) hz, ← hFv0]
  have hF2 : ∀ z ∈ t2.vs, F z = lay enc t2 (.m2 true (!dr)) b c v (F b) (F c) (F v)
      (if dr then (lo + hi) / 2 else lo) (if dr then hi else (lo + hi) / 2) z := by
    intro z hz
    rw [hF z (mem2 hz), lay_mB_2 enc (by rintro rfl; exact v2o hz)
      (fun h => Finset.disjoint_left.mp d12 h hz) hz, ← hFv0]
  have hF3 : ∀ z ∈ t3.vs, F z = lay enc t3 .m0 c a v (F c) (F a) (F v) 0 0 z := by
    intro z hz
    rw [hF z (mem3 hz), lay_mB_3 enc (by rintro rfl; exact v3o hz)
      (fun h => Finset.disjoint_left.mp d13 h hz) (fun h => Finset.disjoint_left.mp d23 h hz),
      ← hFv0]
  have hg : star3 v a b c ⊔ t1.gr a b v ⊔ t2.gr b c v ⊔ t3.gr c a v ≤ H := hgr
  obtain ⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩ := by simpa only [sup_le_iff] using hg
  have hav : H.Adj a v := (hg0 (star3_adj.2 ⟨nva, Or.inl ⟨rfl, rfl⟩⟩)).symm
  have hbv2 : H.Adj b v := (hg0 (star3_adj.2 ⟨nvb, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)).symm
  have hcv : H.Adj c v :=
    (hg0 (star3_adj.2 ⟨nvc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)).symm
  have hy1 : Hyp F t1 (.m2 false dr) a b v (if dr then lo else (lo + hi) / 2)
      (if dr then (lo + hi) / 2 else hi) := by
    simp only [Hyp, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte]
    refine ⟨va, vv, hav0.symm, by rw [hbv']; exact fun h => ncT (mem1 h), ?_,
      by unfold dY12; omega, hlp.symm, htp, by rw [hbv']; exact nbc', ?_, ?_,
      fun h => nbT (mem1 h)⟩
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;> linarith
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact hxv.le
      · exact o1 (by omega)
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact o2 (by omega)
      · exact hxv.ge
  have hy2 : Hyp F t2 (.m2 true (!dr)) b c v (if dr then (lo + hi) / 2 else lo)
      (if dr then hi else (lo + hi) / 2) := by
    simp only [Hyp, if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte]
    refine ⟨vc, vv, hbv'.symm, by rw [hbv']; exact fun h => ncT (mem2 h), ?_,
      by unfold dY12; omega, hlp.symm, htp, by rw [hbv']; exact nbc', ?_, ?_,
      fun h => nbT (mem2 h)⟩
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;> linarith
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact o1 (by omega)
      · exact hxv.le
    · cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> intro h
      · exact hxv.ge
      · exact o2 (by omega)
  have hy3 : Hyp F t3 .m0 c a v 0 0 := by
    simp only [Hyp]
    exact ⟨vc, va, vv, eac.symm, hbv'.symm, by exact fun h => ncT (mem3 h), lac.symm,
      by rw [hlv, lac], by unfold dY12 at yac ⊢; omega, by unfold dY12; omega,
      by unfold dY12; omega⟩
  obtain ⟨g1, r1⟩ := ih1 (.m2 false dr) a b v _ _ w1 hg1 hab hbv2 hav hF1 hy1
  obtain ⟨g2, r2⟩ := ih2 (.m2 true (!dr)) b c v _ _ w2 hg2 hbc hcv hbv2 hF2 hy2
  obtain ⟨g3, r3⟩ := ih3 .m0 c a v 0 0 w3 hg3 hac.symm hav hcv hF3 hy3
  have RS : Rng F t1 (F c).bid (if dr then lo else (lo + hi) / 2) (if dr then (lo + hi) / 2 else hi)
      (max (F a).Y (F v).Y) := by
    have := r1
    simp only [Cnc, if_false, Bool.false_eq_true, ↓reduceIte] at this
    rwa [hbv'] at this
  have RT' : Rng F t2 (F c).bid (if dr then (lo + hi) / 2 else lo)
      (if dr then hi else (lo + hi) / 2) (max (F c).Y (F v).Y) := by
    have := r2
    simp only [Cnc, if_true, ↓reduceIte] at this
    rwa [hbv'] at this
  have hM : ∀ z ∈ t3.vs, (F z).bid ∈ t3.vs := by simpa only [Cnc] using r3
  have hne : (F a).Y ≠ (F c).Y := by unfold dY12 at yac; omega
  have hsx : (if dr then (F a).x ≤ lo else hi ≤ (F a).x) ∨ (F c).Y < (F a).Y := by
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (o2 (by omega))
    · exact Or.inr h
    · exact Or.inl (o1 (by omega))
    · exact Or.inr h
  have htx : (if dr then hi ≤ (F c).x else (F c).x ≤ lo) ∨ (F a).Y < (F c).Y := by
    cases dr <;> simp only [if_true, if_false, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] at o1 o2 ⊢ <;> rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl (o1 (by omega))
    · exact Or.inr h
    · exact Or.inl (o2 (by omega))
  obtain ⟨X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16⟩ :=
    m2_core (p := b) (s := a) (t := c) (v := v) (tS := t1) (tT := t2) (tM := t3)
      (GS := t1.gr a b v) (GT := t2.gr b c v) (GM := t3.gr c a v) dr eac hbv' nbc' yac hyv hxv hlh
      hsx htx (fun h => ncT (mem1 h)) (fun h => ncT (mem2 h)) (fun h => ncT (mem3 h)) d12 d13
      d23 RS RT' hM
      (edgeZ_mono (edgeZ_rng RS) (fun z hz => by
        rcases hz with h | h | h | h
        exacts [Or.inl h, Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h))]))
      (edgeZ_rng RT') (edgeZ_m0 hM) (fun h => nbT (mem3 h)) hlp htp
  rw [star3_swap v b a c] at X1 X2 X3 X4 X5
  refine ⟨node_good enc ⟨vv, rv⟩ g1 g2 g3 X1 X2 X3 X4 X5 X6 X7 X8 ?_ X10 X11 X12 X13 X14 X15, ?_⟩
  · intro z' h
    refine X9 z' ?_
    rcases h with h | h | h | h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))), Or.inr (Or.inr (Or.inr (Or.inl h))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))]
  · simp only [Cnc, if_false, Bool.false_eq_true, ↓reduceIte]
    intro z hz
    rcases X16 z (RT.vs_nd.1 hz) with h | h | h | h
    exacts [Or.inl h, Or.inr (mem1 h), Or.inr (mem2 h), Or.inr (mem3 h)]

theorem layOK_all (enc : V → ℕ) (H : SimpleGraph V) (F : V → Inf V) :
    ∀ T, LayOK enc H F T := by
  intro T
  induction T with
  | lf => exact layOK_lf enc H F
  | nd w t1 t2 t3 ih1 ih2 ih3 =>
    intro md a b c lo hi hwf hgr hab hbc hac hF hH
    cases md with
    | m0 => exact step_m0 enc ih1 ih2 ih3 hwf hgr hab hbc hac hF hH
    | m1 => exact step_m1 enc ih1 ih2 ih3 hwf hgr hab hbc hac hF hH
    | m2 pa dr =>
      cases pa
      · exact step_m2B enc ih1 ih2 ih3 dr hwf hgr hab hbc hac hF hH
      · exact step_m2A enc ih1 ih2 ih3 dr hwf hgr hab hbc hac hF hH

/-- MAIN LAYOUT THEOREM -/
theorem mainLay_holds (enc : V → ℕ) : MainLay enc :=
  fun H F T => layOK_all enc H F T

end StepM2

end PQL5

/-! C3b: an Apollonian 3-tree is the graph of a region tree over one of its faces. -/

namespace PQL5

section C3b

variable {V : Type} [DecidableEq V]

/-- the graph of a region tree together with its boundary triangle -/
def GT (T : RT V) (a b c : V) : SimpleGraph V := tri a b c ⊔ T.gr a b c

theorem star3_adj' {v p q r u w : V} : (star3 v p q r).Adj u w ↔ u ≠ w ∧
    ((u = v ∧ In3 p q r w) ∨ (w = v ∧ In3 p q r u)) := by
  rw [star3_adj]; unfold In3; tauto

theorem star3_eq_of_cover {v p q r a b c : V} (h : ∀ u, In3 p q r u ↔ In3 a b c u) :
    star3 v p q r = star3 v a b c := by
  ext u w
  simp only [star3_adj', h]

theorem GT_ends {T : RT V} {a b c u u' : V} (h : (GT T a b c).Adj u u') :
    u ∈ T.vs ∨ In3 a b c u := by
  unfold GT at h
  rw [SimpleGraph.sup_adj] at h
  rcases h with h | h
  · exact Or.inr (tri_In3_of_adj h).1
  · rcases (RT.gr_ends h).1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

theorem gt_nd_adj {w : V} {t1 t2 t3 : RT V} {a b c u u' : V} :
    (GT (.nd w t1 t2 t3) a b c).Adj u u' ↔ (tri a b c).Adj u u' ∨ (star3 w a b c).Adj u u' ∨
      (t1.gr a b w).Adj u u' ∨ (t2.gr b c w).Adj u u' ∨ (t3.gr c a w).Adj u u' := by
  simp only [GT, RT.gr, SimpleGraph.sup_adj]
  tauto

theorem vs_ins1 (v w : V) (A B C : Finset V) :
    insert w (insert v A ∪ B ∪ C) = insert v (insert w (A ∪ B ∪ C)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto

theorem vs_ins2 (v w : V) (A B C : Finset V) :
    insert w (A ∪ insert v B ∪ C) = insert v (insert w (A ∪ B ∪ C)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto

theorem vs_ins3 (v w : V) (A B C : Finset V) :
    insert w (A ∪ B ∪ insert v C) = insert v (insert w (A ∪ B ∪ C)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_union]; tauto

omit [DecidableEq V] in
theorem gr_ins1 (A B C D X : SimpleGraph V) : A ⊔ (B ⊔ X) ⊔ C ⊔ D = A ⊔ B ⊔ C ⊔ D ⊔ X := by
  ext u w; simp only [SimpleGraph.sup_adj]; tauto

omit [DecidableEq V] in
theorem gr_ins2 (A B C D X : SimpleGraph V) : A ⊔ B ⊔ (C ⊔ X) ⊔ D = A ⊔ B ⊔ C ⊔ D ⊔ X := by
  ext u w; simp only [SimpleGraph.sup_adj]; tauto

omit [DecidableEq V] in
theorem gr_ins3 (A B C D X : SimpleGraph V) : A ⊔ B ⊔ C ⊔ (D ⊔ X) = A ⊔ B ⊔ C ⊔ D ⊔ X := by
  ext u w; simp only [SimpleGraph.sup_adj]; tauto

/-- the conclusion of the triangle-region lemma -/
def TRC (T : RT V) (a b c p q r : V) : Prop :=
  (∀ v, v ∉ T.vs → v ≠ a → v ≠ b → v ≠ c → ∃ T' : RT V, T'.wf a b c ∧
      T'.vs = insert v T.vs ∧ T'.gr a b c = T.gr a b c ⊔ star3 v p q r) ∨
  (∃ w ∈ T.vs, In3 a b c p ∧ In3 a b c q ∧ In3 a b c r ∧ (GT T a b c).Adj w p ∧
      (GT T a b c).Adj w q ∧ (GT T a b c).Adj w r) ∨
  (∃ w1 w2, w1 ≠ w2 ∧ (w1 ∈ T.vs ∨ In3 a b c w1) ∧ (w2 ∈ T.vs ∨ In3 a b c w2) ∧
      (GT T a b c).Adj w1 p ∧ (GT T a b c).Adj w1 q ∧ (GT T a b c).Adj w1 r ∧
      (GT T a b c).Adj w2 p ∧ (GT T a b c).Adj w2 q ∧ (GT T a b c).Adj w2 r)

/-- every triangle of a region-tree graph is a leaf region, or has two common neighbours -/
def TR (T : RT V) : Prop :=
  ∀ a b c p q r, T.wf a b c → (GT T a b c).Adj p q → (GT T a b c).Adj q r →
    (GT T a b c).Adj p r → TRC T a b c p q r

/-- the generic child step of the triangle-region lemma -/
theorem child_case {G : SimpleGraph V} {T t : RT V} {a b c a' b' w c' p q r : V}
    (ih : TR t) (hwf : t.wf a' b' w) (hle : GT t a' b' w ≤ G)
    (hP : ∀ u u', (u ∈ t.vs ∨ In3 a' b' w u) → (u' ∈ t.vs ∨ In3 a' b' w u') → G.Adj u u' →
      (GT t a' b' w).Adj u u')
    (hp : p ∈ t.vs ∨ In3 a' b' w p) (hq : q ∈ t.vs ∨ In3 a' b' w q)
    (hr : r ∈ t.vs ∨ In3 a' b' w r)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hpr : G.Adj p r)
    (hca : G.Adj c' a') (hcb : G.Adj c' b') (hcw : G.Adj c' w) (hct : c' ∉ t.vs)
    (hM : ∀ z, (z ∈ t.vs ∨ In3 a' b' w z) → z ∈ T.vs ∨ In3 a b c z)
    (hMc : c' ∈ T.vs ∨ In3 a b c c') (hGT : G = GT T a b c)
    (hreb : ∀ v, v ∉ T.vs → v ≠ a → v ≠ b → v ≠ c → v ∉ t.vs ∧ v ≠ a' ∧ v ≠ b' ∧ v ≠ w ∧
      ∀ t' : RT V, t'.wf a' b' w → t'.vs = insert v t.vs →
        t'.gr a' b' w = t.gr a' b' w ⊔ star3 v p q r →
        ∃ T' : RT V, T'.wf a b c ∧ T'.vs = insert v T.vs ∧
          T'.gr a b c = T.gr a b c ⊔ star3 v p q r) :
    TRC T a b c p q r := by
  have h := ih a' b' w p q r hwf (hP p q hp hq hpq) (hP q r hq hr hqr) (hP p r hp hr hpr)
  rcases h with h1 | ⟨w', hw', ip, iq, ir, ap, aq, ar⟩ | ⟨w1, w2, hne, m1, m2, a1p, a1q, a1r,
    a2p, a2q, a2r⟩
  · left
    intro v hv ha hb hc
    obtain ⟨hvt, hva, hvb, hvw, hreb'⟩ := hreb v hv ha hb hc
    obtain ⟨t', e1, e2, e3⟩ := h1 v hvt hva hvb hvw
    exact hreb' t' e1 e2 e3
  · right; right
    rw [← hGT]
    refine ⟨w', c', fun e => hct (e ▸ hw'), hM w' (Or.inl hw'), hMc, hle ap, hle aq, hle ar,
      adj_of_In3 hca hcb hcw ip, adj_of_In3 hca hcb hcw iq, adj_of_In3 hca hcb hcw ir⟩
  · right; right
    rw [← hGT]
    exact ⟨w1, w2, hne, hM w1 m1, hM w2 m2, hle a1p, hle a1q, hle a1r, hle a2p, hle a2q, hle a2r⟩

theorem four_split {a b c w p q r : V} (hp : p = w ∨ In3 a b c p) (hq : q = w ∨ In3 a b c q)
    (hr : r = w ∨ In3 a b c r) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (h1 : ¬ (In3 a b w p ∧ In3 a b w q ∧ In3 a b w r))
    (h2 : ¬ (In3 b c w p ∧ In3 b c w q ∧ In3 b c w r))
    (h3 : ¬ (In3 c a w p ∧ In3 c a w q ∧ In3 c a w r)) :
    In3 a b c p ∧ In3 a b c q ∧ In3 a b c r := by
  unfold In3 at *
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl | rfl <;> simp_all

set_option maxHeartbeats 1000000 in
/-- **Triangle-region lemma** (C3b core). -/
theorem tri_region (T : RT V) : TR T := by
  induction T with
  | lf =>
    intro a b c p q r hwf hpq hqr hpr
    have e : ∀ u u', (GT (RT.lf : RT V) a b c).Adj u u' → (tri a b c).Adj u u' := by
      intro u u' h
      simpa [GT, RT.gr] using h
    have ip := (tri_In3_of_adj (e _ _ hpq)).1
    have iq := (tri_In3_of_adj (e _ _ hqr)).1
    have ir := (tri_In3_of_adj (e _ _ hpr)).2
    have hcov := In3_cover ip iq ir hpq.ne hqr.ne hpr.ne
    have hcov' : ∀ u, In3 p q r u ↔ In3 a b c u := by
      intro u
      refine ⟨fun hu => ?_, hcov u⟩
      rcases hu with rfl | rfl | rfl
      exacts [ip, iq, ir]
    obtain ⟨hab, hbc, hac⟩ := hwf
    left
    intro v _ hva hvb hvc
    refine ⟨.nd v .lf .lf .lf, ?_, ?_, ?_⟩
    · refine ⟨hab, hbc, hac, hva, hvb, hvc, ⟨hab, fun e => hvb e.symm, fun e => hva e.symm⟩,
        ⟨hbc, fun e => hvc e.symm, fun e => hvb e.symm⟩,
        ⟨fun e => hac e.symm, fun e => hva e.symm, fun e => hvc e.symm⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [RT.vs]
    · simp [RT.vs]
    · simp only [RT.gr, sup_bot_eq, bot_sup_eq]
      exact (star3_eq_of_cover hcov').symm
  | nd w t1 t2 t3 ih1 ih2 ih3 =>
    intro a b c p q r hwf hpq hqr hpr
    have hwf0 := hwf
    obtain ⟨hab, hbc, hac, hwa, hwb, hwc, h1, h2, h3, hc1, ha2, hb3, d12, d13, d23⟩ := hwf
    have o1 := RT.wf_out h1
    have o2 := RT.wf_out h2
    have o3 := RT.wf_out h3
    set G := GT (.nd w t1 t2 t3) a b c with hG
    have hwT : w ∈ (RT.nd w t1 t2 t3).vs := by simp [RT.vs]
    have s1 : ∀ z, z ∈ t1.vs → z ∈ (RT.nd w t1 t2 t3).vs := by intro z hz; simp [RT.vs, hz]
    have s2 : ∀ z, z ∈ t2.vs → z ∈ (RT.nd w t1 t2 t3).vs := by intro z hz; simp [RT.vs, hz]
    have s3 : ∀ z, z ∈ t3.vs → z ∈ (RT.nd w t1 t2 t3).vs := by intro z hz; simp [RT.vs, hz]
    -- the K4 on a b c w
    have k4 : ∀ u u', (u = w ∨ In3 a b c u) → (u' = w ∨ In3 a b c u') → u ≠ u' → G.Adj u u' := by
      intro u u' hu hu' hne
      rw [hG, gt_nd_adj]
      rcases hu with rfl | hu
      · rcases hu' with rfl | hu'
        · exact absurd rfl hne
        · exact Or.inr (Or.inl (star3_adj'.2 ⟨hne, Or.inl ⟨rfl, hu'⟩⟩))
      · rcases hu' with rfl | hu'
        · exact Or.inr (Or.inl (star3_adj'.2 ⟨hne, Or.inr ⟨rfl, hu⟩⟩))
        · exact Or.inl (tri_adj_of_In3 hu hu' hne)
    -- locality of the three children
    have loc1 : ∀ u u', u ∈ t1.vs → G.Adj u u' → (t1.gr a b w).Adj u u' := by
      intro u u' hu h
      rw [hG, gt_nd_adj] at h
      rcases h with h | h | h | h | h
      · rcases (tri_In3_of_adj h).1 with e | e | e <;> subst e
        exacts [absurd hu o1.1, absurd hu o1.2.1, absurd hu hc1]
      · rcases (star3_adj'.1 h).2 with ⟨e, _⟩ | ⟨_, e⟩
        · subst e; exact absurd hu o1.2.2
        · rcases e with e | e | e <;> subst e
          exacts [absurd hu o1.1, absurd hu o1.2.1, absurd hu hc1]
      · exact h
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd e (Finset.disjoint_left.mp d12 hu)
        all_goals (subst e; first | exact absurd hu o1.2.1 | exact absurd hu hc1 |
          exact absurd hu o1.2.2)
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd e (Finset.disjoint_left.mp d13 hu)
        all_goals (subst e; first | exact absurd hu hc1 | exact absurd hu o1.1 |
          exact absurd hu o1.2.2)
    have loc2 : ∀ u u', u ∈ t2.vs → G.Adj u u' → (t2.gr b c w).Adj u u' := by
      intro u u' hu h
      rw [hG, gt_nd_adj] at h
      rcases h with h | h | h | h | h
      · rcases (tri_In3_of_adj h).1 with e | e | e <;> subst e
        exacts [absurd hu ha2, absurd hu o2.1, absurd hu o2.2.1]
      · rcases (star3_adj'.1 h).2 with ⟨e, _⟩ | ⟨_, e⟩
        · subst e; exact absurd hu o2.2.2
        · rcases e with e | e | e <;> subst e
          exacts [absurd hu ha2, absurd hu o2.1, absurd hu o2.2.1]
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd hu (Finset.disjoint_left.mp d12 e)
        all_goals (subst e; first | exact absurd hu ha2 | exact absurd hu o2.1 |
          exact absurd hu o2.2.2)
      · exact h
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd e (Finset.disjoint_left.mp d23 hu)
        all_goals (subst e; first | exact absurd hu o2.2.1 | exact absurd hu ha2 |
          exact absurd hu o2.2.2)
    have loc3 : ∀ u u', u ∈ t3.vs → G.Adj u u' → (t3.gr c a w).Adj u u' := by
      intro u u' hu h
      rw [hG, gt_nd_adj] at h
      rcases h with h | h | h | h | h
      · rcases (tri_In3_of_adj h).1 with e | e | e <;> subst e
        exacts [absurd hu o3.2.1, absurd hu hb3, absurd hu o3.1]
      · rcases (star3_adj'.1 h).2 with ⟨e, _⟩ | ⟨_, e⟩
        · subst e; exact absurd hu o3.2.2
        · rcases e with e | e | e <;> subst e
          exacts [absurd hu o3.2.1, absurd hu hb3, absurd hu o3.1]
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd hu (Finset.disjoint_left.mp d13 e)
        all_goals (subst e; first | exact absurd hu o3.2.1 | exact absurd hu hb3 |
          exact absurd hu o3.2.2)
      · rcases (RT.gr_ends h).1 with e | e | e | e
        · exact absurd hu (Finset.disjoint_left.mp d23 e)
        all_goals (subst e; first | exact absurd hu hb3 | exact absurd hu o3.1 |
          exact absurd hu o3.2.2)
      · exact h
    -- the neighbour of a child vertex lies in the child's closed region
    have side1 : ∀ u u', u ∈ t1.vs → G.Adj u u' → (u' ∈ t1.vs ∨ In3 a b w u') :=
      fun u u' hu h => (RT.gr_ends (loc1 u u' hu h)).2.1
    have side2 : ∀ u u', u ∈ t2.vs → G.Adj u u' → (u' ∈ t2.vs ∨ In3 b c w u') :=
      fun u u' hu h => (RT.gr_ends (loc2 u u' hu h)).2.1
    have side3 : ∀ u u', u ∈ t3.vs → G.Adj u u' → (u' ∈ t3.vs ∨ In3 c a w u') :=
      fun u u' hu h => (RT.gr_ends (loc3 u u' hu h)).2.1
    -- the closed child graphs embed
    have le1 : GT t1 a b w ≤ G := by
      intro u u' h
      rw [GT, SimpleGraph.sup_adj] at h
      rcases h with h | h
      · have hi := tri_In3_of_adj h
        have L : ∀ z, In3 a b w z → z = w ∨ In3 a b c z := by
          intro z hz; rcases hz with e | e | e
          exacts [Or.inr (Or.inl e), Or.inr (Or.inr (Or.inl e)), Or.inl e]
        exact k4 u u' (L u hi.1) (L u' hi.2) h.ne
      · rw [hG, gt_nd_adj]; exact Or.inr (Or.inr (Or.inl h))
    have le2 : GT t2 b c w ≤ G := by
      intro u u' h
      rw [GT, SimpleGraph.sup_adj] at h
      rcases h with h | h
      · have hi := tri_In3_of_adj h
        have L : ∀ z, In3 b c w z → z = w ∨ In3 a b c z := by
          intro z hz; rcases hz with e | e | e
          exacts [Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inr e)), Or.inl e]
        exact k4 u u' (L u hi.1) (L u' hi.2) h.ne
      · rw [hG, gt_nd_adj]; exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    have le3 : GT t3 c a w ≤ G := by
      intro u u' h
      rw [GT, SimpleGraph.sup_adj] at h
      rcases h with h | h
      · have hi := tri_In3_of_adj h
        have L : ∀ z, In3 c a w z → z = w ∨ In3 a b c z := by
          intro z hz; rcases hz with e | e | e
          exacts [Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inl e), Or.inl e]
        exact k4 u u' (L u hi.1) (L u' hi.2) h.ne
      · rw [hG, gt_nd_adj]; exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have P1 : ∀ u u', (u ∈ t1.vs ∨ In3 a b w u) → (u' ∈ t1.vs ∨ In3 a b w u') → G.Adj u u' →
        (GT t1 a b w).Adj u u' := by
      intro u u' hu hu' h
      by_cases m : u ∈ t1.vs
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc1 u u' m h))
      by_cases m' : u' ∈ t1.vs
      · exact ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc1 u' u m' h.symm))).symm
      exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 (hu.resolve_left m)
        (hu'.resolve_left m') h.ne))
    have P2 : ∀ u u', (u ∈ t2.vs ∨ In3 b c w u) → (u' ∈ t2.vs ∨ In3 b c w u') → G.Adj u u' →
        (GT t2 b c w).Adj u u' := by
      intro u u' hu hu' h
      by_cases m : u ∈ t2.vs
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc2 u u' m h))
      by_cases m' : u' ∈ t2.vs
      · exact ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc2 u' u m' h.symm))).symm
      exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 (hu.resolve_left m)
        (hu'.resolve_left m') h.ne))
    have P3 : ∀ u u', (u ∈ t3.vs ∨ In3 c a w u) → (u' ∈ t3.vs ∨ In3 c a w u') → G.Adj u u' →
        (GT t3 c a w).Adj u u' := by
      intro u u' hu hu' h
      by_cases m : u ∈ t3.vs
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc3 u u' m h))
      by_cases m' : u' ∈ t3.vs
      · exact ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (loc3 u' u m' h.symm))).symm
      exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 (hu.resolve_left m)
        (hu'.resolve_left m') h.ne))
    have ia : In3 a b c a := Or.inl rfl
    have ib : In3 a b c b := Or.inr (Or.inl rfl)
    have ic : In3 a b c c := Or.inr (Or.inr rfl)
    by_cases A1 : (p ∈ t1.vs ∨ In3 a b w p) ∧ (q ∈ t1.vs ∨ In3 a b w q) ∧
        (r ∈ t1.vs ∨ In3 a b w r)
    · refine child_case (c' := c) ih1 h1 le1 P1 A1.1 A1.2.1 A1.2.2 hpq hqr hpr
        (k4 c a (Or.inr ic) (Or.inr ia) hac.symm) (k4 c b (Or.inr ic) (Or.inr ib) hbc.symm)
        (k4 c w (Or.inr ic) (Or.inl rfl) hwc.symm) hc1 ?_ (Or.inr ic) rfl ?_
      · intro z hz
        rcases hz with hz | e | e | e
        exacts [Or.inl (s1 z hz), Or.inr (Or.inl e), Or.inr (Or.inr (Or.inl e)),
          Or.inl (e ▸ hwT)]
      · intro v hv hva hvb hvc
        have hvw : v ≠ w := fun e => hv (e ▸ hwT)
        refine ⟨fun h => hv (s1 v h), hva, hvb, hvw, ?_⟩
        intro t' e1 e2 e3
        refine ⟨.nd w t' t2 t3, ⟨hab, hbc, hac, hwa, hwb, hwc, e1, h2, h3, ?_, ha2, hb3, ?_, ?_,
          d23⟩, ?_, ?_⟩
        · rw [e2, Finset.mem_insert]; rintro (e | e); exact hvc e.symm; exact hc1 e
        · rw [e2, Finset.disjoint_insert_left]
          exact ⟨fun h => hv (s2 v h), d12⟩
        · rw [e2, Finset.disjoint_insert_left]
          exact ⟨fun h => hv (s3 v h), d13⟩
        · simp only [RT.vs, e2]; exact vs_ins1 _ _ _ _ _
        · simp only [RT.gr, e3]; exact gr_ins1 _ _ _ _ _
    by_cases A2 : (p ∈ t2.vs ∨ In3 b c w p) ∧ (q ∈ t2.vs ∨ In3 b c w q) ∧
        (r ∈ t2.vs ∨ In3 b c w r)
    · refine child_case (c' := a) ih2 h2 le2 P2 A2.1 A2.2.1 A2.2.2 hpq hqr hpr
        (k4 a b (Or.inr ia) (Or.inr ib) hab) (k4 a c (Or.inr ia) (Or.inr ic) hac)
        (k4 a w (Or.inr ia) (Or.inl rfl) hwa.symm) ha2 ?_ (Or.inr ia) rfl ?_
      · intro z hz
        rcases hz with hz | e | e | e
        exacts [Or.inl (s2 z hz), Or.inr (Or.inr (Or.inl e)), Or.inr (Or.inr (Or.inr e)),
          Or.inl (e ▸ hwT)]
      · intro v hv hva hvb hvc
        have hvw : v ≠ w := fun e => hv (e ▸ hwT)
        refine ⟨fun h => hv (s2 v h), hvb, hvc, hvw, ?_⟩
        intro t' e1 e2 e3
        refine ⟨.nd w t1 t' t3, ⟨hab, hbc, hac, hwa, hwb, hwc, h1, e1, h3, hc1, ?_, hb3, ?_, d13,
          ?_⟩, ?_, ?_⟩
        · rw [e2, Finset.mem_insert]; rintro (e | e); exact hva e.symm; exact ha2 e
        · rw [e2, Finset.disjoint_insert_right]
          exact ⟨fun h => hv (s1 v h), d12⟩
        · rw [e2, Finset.disjoint_insert_left]
          exact ⟨fun h => hv (s3 v h), d23⟩
        · simp only [RT.vs, e2]; exact vs_ins2 _ _ _ _ _
        · simp only [RT.gr, e3]; exact gr_ins2 _ _ _ _ _
    by_cases A3 : (p ∈ t3.vs ∨ In3 c a w p) ∧ (q ∈ t3.vs ∨ In3 c a w q) ∧
        (r ∈ t3.vs ∨ In3 c a w r)
    · refine child_case (c' := b) ih3 h3 le3 P3 A3.1 A3.2.1 A3.2.2 hpq hqr hpr
        (k4 b c (Or.inr ib) (Or.inr ic) hbc) (k4 b a (Or.inr ib) (Or.inr ia) hab.symm)
        (k4 b w (Or.inr ib) (Or.inl rfl) hwb.symm) hb3 ?_ (Or.inr ib) rfl ?_
      · intro z hz
        rcases hz with hz | e | e | e
        exacts [Or.inl (s3 z hz), Or.inr (Or.inr (Or.inr e)), Or.inr (Or.inl e),
          Or.inl (e ▸ hwT)]
      · intro v hv hva hvb hvc
        have hvw : v ≠ w := fun e => hv (e ▸ hwT)
        refine ⟨fun h => hv (s3 v h), hvc, hva, hvw, ?_⟩
        intro t' e1 e2 e3
        refine ⟨.nd w t1 t2 t', ⟨hab, hbc, hac, hwa, hwb, hwc, h1, h2, e1, hc1, ha2, ?_, d12, ?_,
          ?_⟩, ?_, ?_⟩
        · rw [e2, Finset.mem_insert]; rintro (e | e); exact hvb e.symm; exact hb3 e
        · rw [e2, Finset.disjoint_insert_right]
          exact ⟨fun h => hv (s1 v h), d13⟩
        · rw [e2, Finset.disjoint_insert_right]
          exact ⟨fun h => hv (s2 v h), d23⟩
        · simp only [RT.vs, e2]; exact vs_ins3 _ _ _ _ _
        · simp only [RT.gr, e3]; exact gr_ins3 _ _ _ _ _
    -- the triangle is the boundary triangle itself
    have key : ∀ z z', G.Adj z z' → (z = p ∨ z = q ∨ z = r) → z = w ∨ In3 a b c z := by
      intro z z' hz hzm
      have all1 : z ∈ t1.vs → False := by
        intro m; apply A1
        rcases hzm with rfl | rfl | rfl
        · exact ⟨Or.inl m, side1 _ _ m hpq, side1 _ _ m hpr⟩
        · exact ⟨side1 _ _ m hpq.symm, Or.inl m, side1 _ _ m hqr⟩
        · exact ⟨side1 _ _ m hpr.symm, side1 _ _ m hqr.symm, Or.inl m⟩
      have all2 : z ∈ t2.vs → False := by
        intro m; apply A2
        rcases hzm with rfl | rfl | rfl
        · exact ⟨Or.inl m, side2 _ _ m hpq, side2 _ _ m hpr⟩
        · exact ⟨side2 _ _ m hpq.symm, Or.inl m, side2 _ _ m hqr⟩
        · exact ⟨side2 _ _ m hpr.symm, side2 _ _ m hqr.symm, Or.inl m⟩
      have all3 : z ∈ t3.vs → False := by
        intro m; apply A3
        rcases hzm with rfl | rfl | rfl
        · exact ⟨Or.inl m, side3 _ _ m hpq, side3 _ _ m hpr⟩
        · exact ⟨side3 _ _ m hpq.symm, Or.inl m, side3 _ _ m hqr⟩
        · exact ⟨side3 _ _ m hpr.symm, side3 _ _ m hqr.symm, Or.inl m⟩
      rcases GT_ends hz with m | m
      · rcases RT.vs_nd.1 m with e | m | m | m
        · exact Or.inl e
        · exact (all1 m).elim
        · exact (all2 m).elim
        · exact (all3 m).elim
      · exact Or.inr m
    have N1 : ¬ (In3 a b w p ∧ In3 a b w q ∧ In3 a b w r) :=
      fun h => A1 ⟨Or.inr h.1, Or.inr h.2.1, Or.inr h.2.2⟩
    have N2 : ¬ (In3 b c w p ∧ In3 b c w q ∧ In3 b c w r) :=
      fun h => A2 ⟨Or.inr h.1, Or.inr h.2.1, Or.inr h.2.2⟩
    have N3 : ¬ (In3 c a w p ∧ In3 c a w q ∧ In3 c a w r) :=
      fun h => A3 ⟨Or.inr h.1, Or.inr h.2.1, Or.inr h.2.2⟩
    obtain ⟨ip, iq, ir⟩ := four_split (key p q hpq (Or.inl rfl)) (key q r hqr (Or.inr (Or.inl rfl)))
      (key r p hpr.symm (Or.inr (Or.inr rfl))) hpq.ne hqr.ne hpr.ne N1 N2 N3
    have hwn : ∀ z, In3 a b c z → w ≠ z := by
      intro z hz e; subst e
      rcases hz with e | e | e
      exacts [hwa e, hwb e, hwc e]
    right; left
    exact ⟨w, hwT, ip, iq, ir, k4 w p (Or.inl rfl) (Or.inr ip) (hwn p ip),
      k4 w q (Or.inl rfl) (Or.inr iq) (hwn q iq), k4 w r (Or.inl rfl) (Or.inr ir) (hwn r ir)⟩

set_option maxHeartbeats 1000000 in
/-- **Extraction (C3b).** A 3-tree inside an Apollonian graph `Hf`, grown from a face of `Hf`,
is the graph of a region tree over that face. -/
theorem extract_rt {Hf : SimpleGraph V} (hT : TriCond Hf) {H : SimpleGraph V} {S : Finset V}
    {x y z : V} (h : TTb H S x y z) (hle : H ≤ Hf) (hF : Face Hf x y z) :
    ∃ T : RT V, T.wf x y z ∧ H = GT T x y z ∧ ∀ u, u ∈ S ↔ u ∈ T.vs ∨ In3 x y z u := by
  induction h with
  | base x y z hxy hyz hxz =>
    refine ⟨.lf, ⟨hxy, hyz, hxz⟩, by simp [GT, RT.gr], ?_⟩
    intro u; simp [RT.vs, In3]
  | @stack H S x y z v p q r h hv hp hq hr hpq hqr hpr ih =>
    obtain ⟨T, hwf, hH, hS⟩ := ih (le_trans le_sup_left hle) hF
    have hH' : ∀ s t, (GT T x y z).Adj s t → Hf.Adj s t := by
      intro s t hst; rw [← hH] at hst; exact hle ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hst))
    have hvS : ∀ u, u ∈ T.vs ∨ In3 x y z u → v ≠ u := by
      intro u hu e; subst e; exact hv ((hS _).2 hu)
    have hstar : ∀ s, In3 p q r s → Hf.Adj v s := by
      intro s hs
      have hs' : s ∈ S := by
        rcases hs with rfl | rfl | rfl
        exacts [hp, hq, hr]
      exact hle ((SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (star3_adj_of_In3 (hvS s ((hS s).1 hs')) hs)))
    rw [hH] at hpq hqr hpr
    have hvT : v ∉ T.vs := fun m => hvS v (Or.inl m) rfl
    rcases tri_region T x y z p q r hwf hpq hqr hpr with h1 | ⟨w, hw, ip, iq, ir, ap, aq, ar⟩ |
      ⟨w1, w2, hne, m1, m2, a1p, a1q, a1r, a2p, a2q, a2r⟩
    · obtain ⟨T', e1, e2, e3⟩ := h1 v hvT (hvS _ (Or.inr (Or.inl rfl)))
        (hvS _ (Or.inr (Or.inr (Or.inl rfl)))) (hvS _ (Or.inr (Or.inr (Or.inr rfl))))
      refine ⟨T', e1, ?_, ?_⟩
      · rw [hH]; simp only [GT, e3, sup_assoc]
      · intro u; rw [e2, Finset.mem_insert, Finset.mem_insert, hS]; tauto
    · exfalso
      have cov := In3_cover ip iq ir hpq.ne hqr.ne hpr.ne
      have hw' : ∀ s, In3 p q r s → Hf.Adj w s := fun s hs =>
        adj_of_In3 (hH' _ _ ap) (hH' _ _ aq) (hH' _ _ ar) hs
      exact hF.2.2.2 w v (fun e => hvT (e ▸ hw)) (hw' _ (cov _ (Or.inl rfl)))
        (hw' _ (cov _ (Or.inr (Or.inl rfl)))) (hw' _ (cov _ (Or.inr (Or.inr rfl))))
        (hstar _ (cov _ (Or.inl rfl))) (hstar _ (cov _ (Or.inr (Or.inl rfl))))
        (hstar _ (cov _ (Or.inr (Or.inr rfl))))
    · exfalso
      exact hT p q r w1 w2 v (hH' _ _ hpq) (hH' _ _ hqr) (hH' _ _ hpr) hne
        (fun e => hvS w2 m2 e.symm) (fun e => hvS w1 m1 e.symm)
        (hH' _ _ a1p) (hH' _ _ a1q) (hH' _ _ a1r) (hH' _ _ a2p) (hH' _ _ a2q) (hH' _ _ a2r)
        (hstar p (Or.inl rfl)) (hstar q (Or.inr (Or.inl rfl))) (hstar r (Or.inr (Or.inr rfl)))

/-- **C3b.** An Apollonian 3-tree on all of `V` is the graph of a region tree over a face. -/
theorem rt_of_TT {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    (hT : TT H Finset.univ) (hC : TriCond H) :
    ∃ (x y z : V) (T : RT V), T.wf x y z ∧ H = GT T x y z ∧ ∀ u, u ∈ T.vs ∨ In3 x y z u := by
  obtain ⟨x, y, z, h⟩ := hT
  have hb := h.base_mem
  obtain ⟨t, hF⟩ := h.edge_face x y hb.2.2.2.1
  have h' := h.reroot x y t hF.1 hF.2.1 hF.2.2.1
  obtain ⟨T, hw, hH, hS⟩ := extract_rt hC h' le_rfl hF
  exact ⟨x, y, t, T, hw, hH, fun u => (hS u).1 (Finset.mem_univ u)⟩

end C3b

end PQL5

/-! C3d: the global layout of an Apollonian 3-tree and the 5-queue assembly. -/

namespace PQL5

open PlanarQueue.Planar

section C3dList

theorem lt_app_left (P s t : List ℚ) : P ++ s < P ++ t ↔ s < t := by
  induction P with
  | nil => simp
  | cons a P ih => simp only [List.cons_append, List.cons_lt_cons_iff, lt_self_iff_false,
      false_or, true_and, ih]

theorem le_app_left (P s t : List ℚ) : P ++ s ≤ P ++ t ↔ s ≤ t := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lt_app_left, List.append_cancel_left_eq]

theorem lt_app_ne (A A' s t : List ℚ) (hl : A.length = A'.length) (hne : A ≠ A') :
    A ++ s < A' ++ t ↔ A < A' := by
  induction A generalizing A' with
  | nil =>
    cases A' with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hl
  | cons a A ih =>
    cases A' with
    | nil => simp at hl
    | cons a' A' =>
      simp only [List.cons_append, List.cons_lt_cons_iff]
      by_cases h : a = a'
      · subst h
        have hne' : A ≠ A' := fun e => hne (by rw [e])
        rw [ih A' (by simpa using hl) hne']
      · simp [h]

theorem pair_lt {p p' : ℤ} {q q' : ℚ} :
    ([-(p : ℚ), q] : List ℚ) < [-(p' : ℚ), q'] ↔ p' < p ∨ (p = p' ∧ q < q') := by
  simp only [List.cons_lt_cons_iff, neg_lt_neg_iff, Int.cast_lt, neg_inj, Int.cast_inj,
    lt_self_iff_false, and_false, or_false]

theorem pair_le_of {p p' : ℤ} {q q' : ℚ} (hp : p = p') (hq : q ≤ q') :
    ([-(p : ℚ), q] : List ℚ) ≤ [-(p' : ℚ), q'] := by
  rcases hq.lt_or_eq with h | h
  · exact (pair_lt.2 (Or.inr ⟨hp, h⟩)).le
  · rw [hp, h]

theorem pair_le_of_lt {p p' : ℤ} {q q' : ℚ} (hp : p' < p) :
    ([-(p : ℚ), q] : List ℚ) ≤ [-(p' : ℚ), q'] :=
  (pair_lt.2 (Or.inl hp)).le

end C3dList

section C3dOrd

variable {V : Type} [Fintype V] [DecidableEq V]

/-- the position of `u` in the order given by a key -/
def ordK (key : V → List ℚ) (u : V) : ℕ :=
  (Finset.univ.filter (fun w => key w < key u)).card

theorem ordK_lt {key : V → List ℚ} {u v : V} (h : key u < key v) : ordK key u < ordK key v := by
  unfold ordK
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, by simp [h], by simp⟩
  · intro w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hw
    exact lt_trans hw h

theorem ordK_eq {key : V → List ℚ} {u v : V} (h : key u = key v) : ordK key u = ordK key v := by
  unfold ordK
  rw [h]

theorem ordK_le {key : V → List ℚ} {u v : V} (h : key u ≤ key v) : ordK key u ≤ ordK key v := by
  rcases h.lt_or_eq with h | h
  · exact (ordK_lt h).le
  · exact (ordK_eq h).le

theorem ordK_lt_iff {key : V → List ℚ} {u v : V} : ordK key u < ordK key v ↔ key u < key v := by
  constructor
  · intro h
    by_contra hc
    have := ordK_le (not_lt.1 hc)
    omega
  · exact ordK_lt

end C3dOrd

section C3dAsm

variable {V : Type} [DecidableEq V]

/-- vertex `j` of the attachment triangle of the bag `β` -/
def tselF (F : V → Inf V) (β : V) (j : ℕ) : V :=
  if j = 0 then (F β).tr.1 else if j = 1 then (F β).tr.2.1 else (F β).tr.2.2

/-- the index of `a` in the attachment triangle of `b`'s bag -/
def roleF (F : V → Inf V) (a b : V) : ℕ :=
  if a = (F b).tr.1 then 0 else if a = (F b).tr.2.1 then 1 else 2

/-- level-edge queue: rows two apart use queue 1 -/
def q0F (F : V → Inf V) (a b : V) : ℕ :=
  if (F a).Y - (F b).Y = 2 ∨ (F b).Y - (F a).Y = 2 then 1 else 0

theorem tselF_role {F : V → Inf V} {a b : V} (hV : VInv F b) (h : trs a (F b).tr) :
    tselF F (F b).bid (roleF F a b) = a := by
  have htr := hV.2.2.2.1
  unfold tselF roleF
  rw [htr]
  by_cases h1 : a = (F b).tr.1
  · simp [h1]
  by_cases h2 : a = (F b).tr.2.1
  · rw [if_neg h1, if_pos h2, if_neg one_ne_zero, if_pos rfl]; exact h2.symm
  simp only [h1, h2, if_false]
  simp only [show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false]
  rcases h with h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact h.symm

/-- two attachment triangles in one bag, rows `k+1,k,k-1`, compare coordinatewise when their
`(-row, x)` sextuples compare lexicographically. -/
theorem chain_core {H : SimpleGraph V} {F : V → Inf V} (hS : SIF H F) {s1 s2 s3 r1 r2 r3 : V}
    (hb : (F s1).bid = (F s2).bid ∧ (F s1).bid = (F s3).bid)
    (hb' : (F r1).bid = (F r2).bid ∧ (F r1).bid = (F r3).bid) (hbb : (F s1).bid = (F r1).bid)
    (hy : (F s1).Y = (F s2).Y + 1 ∧ (F s2).Y = (F s3).Y + 1)
    (hy' : (F r1).Y = (F r2).Y + 1 ∧ (F r2).Y = (F r3).Y + 1)
    (ha : H.Adj s1 s2 ∧ H.Adj s2 s3 ∧ H.Adj s1 s3) (ha' : H.Adj r1 r2 ∧ H.Adj r2 r3 ∧ H.Adj r1 r3)
    (hlt : ([-((F s1).Y : ℚ), (F s1).x, -((F s2).Y : ℚ), (F s2).x, -((F s3).Y : ℚ), (F s3).x] :
      List ℚ) ≤ [-((F r1).Y : ℚ), (F r1).x, -((F r2).Y : ℚ), (F r2).x, -((F r3).Y : ℚ), (F r3).x]) :
    ([-((F s1).Y : ℚ), (F s1).x] : List ℚ) ≤ [-((F r1).Y : ℚ), (F r1).x] ∧
    ([-((F s2).Y : ℚ), (F s2).x] : List ℚ) ≤ [-((F r2).Y : ℚ), (F r2).x] ∧
    ([-((F s3).Y : ℚ), (F s3).x] : List ℚ) ≤ [-((F r3).Y : ℚ), (F r3).x] := by
  rcases hlt.lt_or_eq with hlt | heq
  · have h1 : (F r1).Y ≤ (F s1).Y := by
      rcases List.cons_lt_cons_iff.1 hlt with h | ⟨h, _⟩
      · have := neg_lt_neg_iff.1 h
        exact_mod_cast this.le
      · have := neg_inj.1 h
        exact_mod_cast this.symm.le
    by_cases hY : (F s1).Y = (F r1).Y
    · have hY2 : (F s2).Y = (F r2).Y := by omega
      have hY3 : (F s3).Y = (F r3).Y := by omega
      simp only [hY, hY2, hY3, List.cons_lt_cons_iff, lt_self_iff_false, false_or, true_and,
        or_false, and_false] at hlt
      have s12 := hS s1 s2 r1 r2 ha.1 ha'.1 hb.1 hb'.1 hbb hY hY2
      have s13 := hS s1 s3 r1 r3 ha.2.2 ha'.2.2 hb.2 hb'.2 hbb hY hY3
      have s23 := hS s2 s3 r2 r3 ha.2.1 ha'.2.1 (hb.1.symm.trans hb.2) (hb'.1.symm.trans hb'.2)
        (by rw [← hb.1, ← hb'.1]; exact hbb) hY2 hY3
      rcases hlt with h | ⟨e1, h | ⟨e2, h⟩⟩
      · refine ⟨pair_le_of hY h.le, pair_le_of hY2 ?_, pair_le_of hY3 ?_⟩
        · exact not_lt.1 (fun h' => s12 h h')
        · exact not_lt.1 (fun h' => s13 h h')
      · refine ⟨pair_le_of hY e1.le, pair_le_of hY2 h.le, pair_le_of hY3 ?_⟩
        exact not_lt.1 (fun h' => s23 h h')
      · exact ⟨pair_le_of hY e1.le, pair_le_of hY2 e2.le, pair_le_of hY3 h.le⟩
    · have hlt1 : (F r1).Y < (F s1).Y := lt_of_le_of_ne h1 (Ne.symm hY)
      exact ⟨pair_le_of_lt hlt1, pair_le_of_lt (by omega), pair_le_of_lt (by omega)⟩
  · simp only [List.cons.injEq] at heq
    obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := heq
    refine ⟨le_of_eq ?_, le_of_eq ?_, le_of_eq ?_⟩
    · rw [e1, e2]
    · rw [e3, e4]
    · rw [e5, e6]

set_option maxHeartbeats 1000000 in
/-- **Assembly of the global layout (C3d).** -/
theorem c3_assemble [Fintype V] (H : SimpleGraph V) (F : V → Inf V) (enc : V → ℕ)
    (henc : Function.Injective enc) (hV : ∀ u, VInv F u)
    (hR : ∀ u, 1 ≤ (F u).lev → RInv enc H F (F u).bid)
    (hE : ∀ a b, H.Adj a b → EInv F a b) (hS : SIF H F) (hX : ∀ u u', XInj F u u')
    (h0 : ∀ u v, (F u).lev = 0 → (F v).lev = 0 → (F u).bid = (F v).bid) :
    HasQueueLayout H 5 := by
  obtain ⟨pre, hpre⟩ : ∃ pre : V → List ℚ,
      pre = fun u => ((F u).lev : ℚ) :: ((F u).bk ++ [(enc (F u).bid : ℚ)]) := ⟨_, rfl⟩
  obtain ⟨key, hkey⟩ : ∃ key : V → List ℚ,
      key = fun u => pre u ++ [-((F u).Y : ℚ), (F u).x] := ⟨_, rfl⟩
  have keyE : ∀ u, key u = pre u ++ [-((F u).Y : ℚ), (F u).x] := by intro u; rw [hkey]
  have preE : ∀ u, pre u = ((F u).lev : ℚ) :: ((F u).bk ++ [(enc (F u).bid : ℚ)]) := by
    intro u; rw [hpre]
  have lev_bag : ∀ u u', (F u).bid = (F u').bid → (F u).lev = (F u').lev := by
    intro u u' h
    rw [← (hV u).2.1, ← (hV u').2.1, h]
  have bk_bag : ∀ u u', (F u).bid = (F u').bid → (F u).bk = (F u').bk := by
    intro u u' h
    rw [← (hV u).2.2.1, ← (hV u').2.2.1, h]
  have pre_len : ∀ u, (pre u).length = 7 * (F u).lev + 2 := by
    intro u
    rw [preE]
    simp [(hV u).2.2.2.2]
  have pre_bag : ∀ u u', (F u).bid = (F u').bid → pre u = pre u' := by
    intro u u' h
    rw [preE, preE, lev_bag u u' h, bk_bag u u' h, h]
  have bag_of_pre : ∀ u u', pre u = pre u' → (F u).bid = (F u').bid := by
    intro u u' h
    rw [preE, preE, List.cons.injEq] at h
    have := List.append_inj_right' h.2 rfl
    simp only [List.cons.injEq, and_true, Nat.cast_inj] at this
    exact henc this
  have key_inj : ∀ u u', key u = key u' → u = u' := by
    intro u u' h
    rw [keyE, keyE] at h
    have hp := List.append_inj_left' h rfl
    have hs := List.append_inj_right' h rfl
    simp only [List.cons.injEq, neg_inj, Int.cast_inj, and_true] at hs
    exact hX u u' (bag_of_pre u u' hp) hs.1 hs.2
  have key_lt_of : ∀ u v, (F u).bid ≠ (F v).bid → (F u).lev = (F v).lev →
      (key u < key v ↔ pre u < pre v) := by
    intro u v hne hl
    rw [keyE, keyE]
    exact lt_app_ne _ _ _ _ (by rw [pre_len, pre_len, hl]) (fun e => hne (bag_of_pre u v e))
  have key_same : ∀ u v, (F u).bid = (F v).bid →
      (key u < key v ↔ ([-((F u).Y : ℚ), (F u).x] : List ℚ) < [-((F v).Y : ℚ), (F v).x]) := by
    intro u v h
    rw [keyE, keyE, pre_bag u v h]
    exact lt_app_left _ _ _
  refine assembly5 H (ordK key) ?_ (fun u => (F u).lev) (fun u => (F u).bid) (tselF F) (roleF F)
    (q0F F) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- injectivity
    intro u v h
    rcases lt_trichotomy (key u) (key v) with h' | h' | h'
    · have := ordK_lt h'; omega
    · exact key_inj u v h'
    · have := ordK_lt h'; omega
  · intro a b; unfold q0F; simp only [or_comm]
  · intro a b; unfold q0F; split_ifs <;> norm_num
  · intro a b; unfold roleF; split_ifs <;> norm_num
  · -- binding edges
    intro a b hab hne
    beta_reduce at hne ⊢
    rcases hE a b hab with ⟨he, _⟩ | hB | hB
    · exact absurd he hne
    · exact Or.inl ⟨hB.1, (tselF_role (hV b) hB.2.1).symm⟩
    · exact Or.inr ⟨hB.1, (tselF_role (hV a) hB.2.1).symm⟩
  · -- levels first
    intro u v h
    beta_reduce at h
    apply ordK_lt
    rw [keyE, keyE, preE, preE, List.cons_append, List.cons_append]
    exact List.cons_lt_cons_iff.2 (Or.inl (by exact_mod_cast h))
  · -- bags contiguous
    intro u u' v v' hu hv hne hl h
    beta_reduce at hu hv hne hl
    rw [ordK_lt_iff] at h ⊢
    have hl' : (F u').lev = (F v').lev := by
      rw [← lev_bag u u' hu, ← lev_bag v v' hv]; exact hl
    rw [key_lt_of u v hne hl] at h
    rw [key_lt_of u' v' (by rw [← hu, ← hv]; exact hne) hl', ← pre_bag u u' hu,
      ← pre_bag v v' hv]
    exact h
  · exact fun u v h => lev_bag u v h
  · -- the chain condition
    intro u v hl hne h j
    beta_reduce at hl hne ⊢
    rw [ordK_lt_iff] at h
    have hl' : (F u).lev = (F v).lev := hl
    by_cases L0 : (F u).lev = 0
    · exact absurd (h0 u v L0 (hl' ▸ L0)) hne
    have Lu : 1 ≤ (F u).lev := by omega
    have Lv : 1 ≤ (F v).lev := by omega
    have ru := (hR u Lu).2 (hV u).1 (by rw [(hV u).2.1]; exact Lu)
    have rv := (hR v Lv).2 (hV v).1 (by rw [(hV v).2.1]; exact Lv)
    set s1 := (F (F u).bid).tr.1
    set s2 := (F (F u).bid).tr.2.1
    set s3 := (F (F u).bid).tr.2.2
    set r1 := (F (F v).bid).tr.1
    set r2 := (F (F v).bid).tr.2.1
    set r3 := (F (F v).bid).tr.2.2
    obtain ⟨ub12, ub13, ulev, uy12, uy23, ua12, ua23, ua13, ubk⟩ := ru
    obtain ⟨vb12, vb13, vlev, vy12, vy23, va12, va23, va13, vbk⟩ := rv
    have levu : (F (F u).bid).lev = (F u).lev := (hV u).2.1
    have levv : (F (F v).bid).lev = (F v).lev := (hV v).2.1
    have hsr : (F s1).lev = (F r1).lev := by omega
    -- the key prefixes
    have Qs := pre_len s1
    have Qr := pre_len r1
    have preU : pre u = ((F u).lev : ℚ) :: (((F s1).bk ++ [(enc (F s1).bid : ℚ)]) ++
        ([-((F s1).Y : ℚ), (F s1).x, -((F s2).Y : ℚ), (F s2).x, -((F s3).Y : ℚ), (F s3).x] ++
          [(enc (F u).bid : ℚ)])) := by
      rw [preE, ← (hV u).2.2.1, ubk]
      simp [newbk, List.append_assoc]
    have preV : pre v = ((F v).lev : ℚ) :: (((F r1).bk ++ [(enc (F r1).bid : ℚ)]) ++
        ([-((F r1).Y : ℚ), (F r1).x, -((F r2).Y : ℚ), (F r2).x, -((F r3).Y : ℚ), (F r3).x] ++
          [(enc (F v).bid : ℚ)])) := by
      rw [preE, ← (hV v).2.2.1, vbk]
      simp [newbk, List.append_assoc]
    have hpuv : pre u < pre v := (key_lt_of u v hne hl').1 h
    rw [preU, preV, hl', List.cons_lt_cons_iff] at hpuv
    simp only [lt_self_iff_false, false_or, true_and] at hpuv
    have lenQ : ((F s1).bk ++ [(enc (F s1).bid : ℚ)]).length =
        ((F r1).bk ++ [(enc (F r1).bid : ℚ)]).length := by
      simp [(hV s1).2.2.2.2, (hV r1).2.2.2.2, hsr]
    -- the three vertices of each triangle share the key prefix of their bag
    have pS : ∀ w, (F w).bid = (F s1).bid → pre w = pre s1 := fun w hw => pre_bag w s1 hw
    have pR : ∀ w, (F w).bid = (F r1).bid → pre w = pre r1 := fun w hw => pre_bag w r1 hw
    -- reduce to the three vertex comparisons
    suffices H3 : key s1 ≤ key r1 ∧ key s2 ≤ key r2 ∧ key s3 ≤ key r3 by
      unfold tselF
      split_ifs
      · exact ordK_le H3.1
      · exact ordK_le H3.2.1
      · exact ordK_le H3.2.2
    by_cases hQ : ((F s1).bk ++ [(enc (F s1).bid : ℚ)]) = ((F r1).bk ++ [(enc (F r1).bid : ℚ)])
    · -- same parent bag: compare the sextuples
      have hbb : (F s1).bid = (F r1).bid := by
        have := List.append_inj_right' hQ rfl
        simp only [List.cons.injEq, and_true, Nat.cast_inj] at this
        exact henc this
      rw [hQ, lt_app_left] at hpuv
      have h6 : ([-((F s1).Y : ℚ), (F s1).x, -((F s2).Y : ℚ), (F s2).x, -((F s3).Y : ℚ),
          (F s3).x] : List ℚ) ≤
          [-((F r1).Y : ℚ), (F r1).x, -((F r2).Y : ℚ), (F r2).x, -((F r3).Y : ℚ), (F r3).x] := by
        by_cases e6 : ([-((F s1).Y : ℚ), (F s1).x, -((F s2).Y : ℚ), (F s2).x, -((F s3).Y : ℚ),
            (F s3).x] : List ℚ) =
            [-((F r1).Y : ℚ), (F r1).x, -((F r2).Y : ℚ), (F r2).x, -((F r3).Y : ℚ), (F r3).x]
        · exact le_of_eq e6
        · exact ((lt_app_ne _ _ _ _ (by simp) e6).1 hpuv).le
      obtain ⟨c1, c2, c3⟩ := chain_core hS ⟨ub12, ub13⟩ ⟨vb12, vb13⟩ hbb ⟨uy12, uy23⟩ ⟨vy12, vy23⟩
        ⟨ua12, ua23, ua13⟩ ⟨va12, va23, va13⟩ h6
      have e1 : pre s1 = pre r1 := pre_bag s1 r1 hbb
      refine ⟨?_, ?_, ?_⟩
      · rw [keyE, keyE, e1, le_app_left]; exact c1
      · rw [keyE, keyE, pS s2 ub12.symm, pR r2 vb12.symm, e1, le_app_left]; exact c2
      · rw [keyE, keyE, pS s3 ub13.symm, pR r3 vb13.symm, e1, le_app_left]; exact c3
    · -- different parent prefixes: the whole triangles compare
      have hQlt := (lt_app_ne _ _ _ _ lenQ hQ).1 hpuv
      have hpre : pre s1 < pre r1 := by
        rw [preE, preE, hsr]
        exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, hQlt⟩)
      have hpne : pre s1 ≠ pre r1 := ne_of_lt hpre
      have hlen : (pre s1).length = (pre r1).length := by rw [pre_len, pre_len, hsr]
      have K : ∀ w w', pre w = pre s1 → pre w' = pre r1 → key w ≤ key w' := by
        intro w w' hw hw'
        rw [keyE, keyE, hw, hw']
        exact ((lt_app_ne _ _ _ _ hlen hpne).2 hpre).le
      exact ⟨K s1 r1 rfl rfl, K s2 r2 (pS s2 ub12.symm) (pR r2 vb12.symm),
        K s3 r3 (pS s3 ub13.symm) (pR r3 vb13.symm)⟩
  · -- no nesting inside a bag
    intro a b c d had hbc hbad hbbc hbab hq h1 h2 h3
    beta_reduce at hbad hbbc hbab
    rw [ordK_lt_iff] at h1 h2 h3
    rw [key_same a b hbab, pair_lt] at h1
    rw [key_same b c hbbc, pair_lt] at h2
    rw [key_same c d (by rw [← hbbc, ← hbab]; exact hbad), pair_lt] at h3
    have ead : dY12 (F a).Y (F d).Y := by
      rcases hE a d had with ⟨_, h⟩ | hB | hB
      · exact h
      · exact absurd hbad hB.2.2
      · exact absurd hbad.symm hB.2.2
    have ebc : dY12 (F b).Y (F c).Y := by
      rcases hE b c hbc with ⟨_, h⟩ | hB | hB
      · exact h
      · exact absurd hbbc hB.2.2
      · exact absurd hbbc.symm hB.2.2
    have y1 : (F b).Y ≤ (F a).Y := by rcases h1 with h | ⟨h, _⟩ <;> omega
    have y2 : (F c).Y ≤ (F b).Y := by rcases h2 with h | ⟨h, _⟩ <;> omega
    have y3 : (F d).Y ≤ (F c).Y := by rcases h3 with h | ⟨h, _⟩ <;> omega
    unfold q0F at hq
    unfold dY12 at ead ebc
    have hab : (F a).Y = (F b).Y ∧ (F c).Y = (F d).Y := by
      split_ifs at hq <;> omega
    have xab : (F a).x < (F b).x := by
      rcases h1 with h | ⟨_, h⟩
      · omega
      · exact h
    have xcd : (F c).x < (F d).x := by
      rcases h3 with h | ⟨_, h⟩
      · omega
      · exact h
    exact hS a d b c had hbc hbad hbbc hbab hab.1 hab.2.symm xab xcd

end C3dAsm

section C3dMain

set_option maxHeartbeats 1000000 in
/-- **C3** (Alam-Bekos-Gronemann-Kaufmann-Pupyrev, combinatorial form). -/
theorem childC3_holds : ChildC3 := by
  intro V _ _ H hT hC
  obtain ⟨x, y, z, T, hwf, hH, hcov⟩ := rt_of_TT hT hC
  obtain ⟨enc, henc⟩ : ∃ enc : V → ℕ, Function.Injective enc :=
    ⟨fun v => ((Fintype.equivFin V v : Fin _) : ℕ),
      fun a b h => (Fintype.equivFin V).injective (Fin.ext h)⟩
  obtain ⟨hxy, hyz, hxz⟩ := RT.wf_ne hwf
  obtain ⟨ox, oy, oz⟩ := RT.wf_out hwf
  obtain ⟨R, hR⟩ : ∃ R : ℤ → Inf V, R = fun k => ⟨0, x, k, 0, [], (x, x, x)⟩ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : V → Inf V, F = fun u => if u ∈ T.vs then
      lay enc T .m0 x y z (R 0) (R (-1)) (R (-2)) 0 0 u
      else if u = x then R 0 else if u = y then R (-1) else R (-2) := ⟨_, rfl⟩
  have Fx : F x = R 0 := by rw [hF]; simp [ox]
  have Fy : F y = R (-1) := by rw [hF]; simp [oy, hxy.symm]
  have Fz : F z = R (-2) := by rw [hF]; simp [oz, hxz.symm, hyz.symm]
  have Rf : ∀ k, (R k).lev = 0 ∧ (R k).bid = x ∧ (R k).Y = k ∧ (R k).x = 0 ∧ (R k).bk = [] ∧
      (R k).tr = (x, x, x) := by
    intro k; rw [hR]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hFT : ∀ u ∈ T.vs, F u = lay enc T .m0 x y z (F x) (F y) (F z) 0 0 u := by
    intro u hu; rw [Fx, Fy, Fz, hF]; simp [hu]
  have hle : T.gr x y z ≤ H := by rw [hH, GT]; exact le_sup_right
  have hadj : ∀ a b, In3 x y z a → In3 x y z b → a ≠ b → H.Adj a b := by
    intro a b ha hb hab
    rw [hH, GT]
    exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (tri_adj_of_In3 ha hb hab))
  have ix : In3 x y z x := Or.inl rfl
  have iy : In3 x y z y := Or.inr (Or.inl rfl)
  have iz : In3 x y z z := Or.inr (Or.inr rfl)
  -- root data
  have root : ∀ u, In3 x y z u → (F u).lev = 0 ∧ (F u).bid = x ∧ (F u).bk = [] ∧
      (F u).tr = (x, x, x) := by
    intro u hu
    rcases hu with e | e | e <;> rw [e]
    · rw [Fx]; exact ⟨(Rf 0).1, (Rf 0).2.1, (Rf 0).2.2.2.2.1, (Rf 0).2.2.2.2.2⟩
    · rw [Fy]; exact ⟨(Rf _).1, (Rf _).2.1, (Rf _).2.2.2.2.1, (Rf _).2.2.2.2.2⟩
    · rw [Fz]; exact ⟨(Rf _).1, (Rf _).2.1, (Rf _).2.2.2.2.1, (Rf _).2.2.2.2.2⟩
  have rootV : ∀ u, In3 x y z u → VInv F u := by
    intro u hu
    obtain ⟨l1, b1, k1, t1⟩ := root u hu
    obtain ⟨l2, b2, k2, t2⟩ := root x ix
    rw [VInv, b1, l1, b2, l2, k1, k2, t1, t2]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have rY : (F x).Y = 0 ∧ (F y).Y = -1 ∧ (F z).Y = -2 := by
    rw [Fx, Fy, Fz]; exact ⟨(Rf _).2.2.1, (Rf _).2.2.1, (Rf _).2.2.1⟩
  have rX : (F x).x = 0 ∧ (F y).x = 0 ∧ (F z).x = 0 := by
    rw [Fx, Fy, Fz]; exact ⟨(Rf _).2.2.2.1, (Rf _).2.2.2.1, (Rf _).2.2.2.1⟩
  have rowinj : ∀ a c, In3 x y z a → In3 x y z c → (F a).Y = (F c).Y → a = c := by
    intro a c ha hc h
    rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;> first | rfl |
      (exfalso; simp [rY.1, rY.2.1, rY.2.2] at h)
  have hyp : Hyp F T .m0 x y z 0 0 := by
    unfold Hyp
    refine ⟨rootV x ix, rootV y iy, rootV z iz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(root x ix).2.1, (root y iy).2.1]
    · rw [(root x ix).2.1, (root z iz).2.1]
    · rw [(root x ix).2.1]; exact ox
    · rw [(root x ix).1, (root y iy).1]
    · rw [(root x ix).1, (root z iz).1]
    · rw [rY.1, rY.2.1]; unfold dY12; omega
    · rw [rY.2.1, rY.2.2]; unfold dY12; omega
    · rw [rY.1, rY.2.2]; unfold dY12; omega
  obtain ⟨good, cnc⟩ := mainLay_holds enc H F T .m0 x y z 0 0 hwf hle (hadj x y ix iy hxy)
    (hadj y z iy iz hyz) (hadj x z ix iz hxz) hFT hyp
  have cnc' : ∀ u ∈ T.vs, (F u).bid ∈ T.vs := cnc
  obtain ⟨gI, gE, gS, gX⟩ := good
  have hV : ∀ u, VInv F u := by
    intro u
    rcases hcov u with hu | hu
    · exact (gI u hu).1
    · exact rootV u hu
  have lev0 : ∀ u, (F u).lev = 0 → In3 x y z u := by
    intro u hu
    rcases hcov u with h | h
    · have := (gI u h).2.1; omega
    · exact h
  refine c3_assemble H F enc henc hV ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rcases hcov u with h | h
    · exact (gI _ (cnc' u h)).2
    · have := (root u h).1; omega
  · intro a b hab
    rw [hH, GT, SimpleGraph.sup_adj] at hab
    rcases hab with hab | hab
    · have hi := tri_In3_of_adj hab
      left
      refine ⟨by rw [(root a hi.1).2.1, (root b hi.2).2.1], ?_⟩
      have hne := hab.ne
      unfold dY12
      rcases hi.1 with rfl | rfl | rfl <;> rcases hi.2 with rfl | rfl | rfl <;>
        first | exact absurd rfl hne | simp [rY.1, rY.2.1, rY.2.2]
    · exact gE a b hab
  · rw [hH, GT]
    apply sif_sup
    · intro a b c d hab hcd _ _ _ hy1 _ hx1 _
      have := rowinj a c (tri_In3_of_adj hab).1 (tri_In3_of_adj hcd).1 hy1
      subst this
      exact lt_irrefl _ hx1
    · exact gS
    · intro a b c d hab hcd _ hcd' hac _ _
      exfalso
      have ba : (F a).bid = x := (root a (tri_In3_of_adj hab).1).2.1
      rcases (RT.gr_ends hcd).2.2 with h | h
      · have := cnc' c h
        rw [← hac, ba] at this
        exact ox this
      · have := cnc' d h
        rw [← hcd', ← hac, ba] at this
        exact ox this
  · intro u u'
    rcases hcov u with hu | hu
    · exact gX u hu u' (hcov u')
    rcases hcov u' with hu' | hu'
    · intro h1 h2 h3
      exact (gX u' hu' u (Or.inr hu) h1.symm h2.symm h3.symm).symm
    · intro _ h2 _
      exact rowinj u u' hu hu' h2
  · intro u v hu hv
    rw [(root u (lev0 u hu)).2.1, (root v (lev0 v hv)).2.1]

end C3dMain

end PQL5

open PlanarQueue.Planar in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hplanar : IsPlanar G)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3) :
    HasQueueLayout G 5 := by
  exact PQL5.lemma_5_of_C2_C3 PQL5.childC2_holds PQL5.childC3_holds G hplanar htw
