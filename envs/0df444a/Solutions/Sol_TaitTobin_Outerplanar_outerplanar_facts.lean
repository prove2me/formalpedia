-- Prove2me | solution 1 for TaitTobin.Outerplanar.outerplanar_facts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T15:55:19.245801+00:00
-- url     : https://prove2.me/submissions/659bbd36-4cd6-4536-899a-a857680b0746

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

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

/-! Outer-face topology. -/

namespace PF12

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar

lemma img_compact {W : Type} [Finite W] {H : SimpleGraph W} (D : PlaneDrawing H) :
    IsCompact (drawingImage D) := by
  unfold drawingImage
  refine (Set.finite_range D.vertex).isCompact.union ?_
  refine isCompact_iUnion (fun a => isCompact_iUnion (fun b => isCompact_iUnion (fun h => ?_)))
  exact isCompact_range (D.arc h).continuous

lemma comp_absorb {K S : Set (ℝ × ℝ)} {x a : ℝ × ℝ} (hS : IsPreconnected S) (hSK : S ⊆ Kᶜ)
    (ha : a ∈ S) (hax : a ∈ connectedComponentIn Kᶜ x) : S ⊆ connectedComponentIn Kᶜ x := by
  rw [connectedComponentIn_eq hax]
  exact hS.subset_connectedComponentIn ha hSK

lemma far_compl {K S : Set (ℝ × ℝ)} {R : ℝ} (hK : ∀ z ∈ K, ‖z‖ ≤ R)
    (hS : ∀ y ∈ S, R < |y.1| ∨ R < |y.2|) : S ⊆ Kᶜ := by
  intro y hy hyK
  have h1 := hK y hyK
  have h2 : |y.1| ≤ ‖y‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have h3 : |y.2| ≤ ‖y‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  rcases hS y hy with h | h <;> linarith

/-- every point far from a bounded set lies in the component of `(R+1, 0)` in its complement -/
lemma far_in_comp {K : Set (ℝ × ℝ)} {R : ℝ} (hR : 0 ≤ R) (hK : ∀ z ∈ K, ‖z‖ ≤ R) (z : ℝ × ℝ)
    (hz : R < |z.1| ∨ R < |z.2|) :
    z ∈ connectedComponentIn Kᶜ ((R + 1, 0) : ℝ × ℝ) := by
  let H1 : Set (ℝ × ℝ) := Set.Ioi R ×ˢ Set.univ
  let H2 : Set (ℝ × ℝ) := Set.Iio (-R) ×ˢ Set.univ
  let H3 : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioi R
  let H4 : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Iio (-R)
  have c1 : IsPreconnected H1 := ((convex_Ioi R).prod convex_univ).isPreconnected
  have c2 : IsPreconnected H2 := ((convex_Iio (-R)).prod convex_univ).isPreconnected
  have c3 : IsPreconnected H3 := (convex_univ.prod (convex_Ioi R)).isPreconnected
  have c4 : IsPreconnected H4 := (convex_univ.prod (convex_Iio (-R))).isPreconnected
  have s1 : H1 ⊆ Kᶜ := far_compl hK (fun y hy => Or.inl (lt_of_lt_of_le hy.1 (le_abs_self _)))
  have s2 : H2 ⊆ Kᶜ := far_compl hK (fun y hy => Or.inl (by
    have : y.1 < -R := hy.1
    rw [abs_of_neg (by linarith)]; linarith))
  have s3 : H3 ⊆ Kᶜ := far_compl hK (fun y hy => Or.inr (lt_of_lt_of_le hy.2 (le_abs_self _)))
  have s4 : H4 ⊆ Kᶜ := far_compl hK (fun y hy => Or.inr (by
    have : y.2 < -R := hy.2
    rw [abs_of_neg (by linarith)]; linarith))
  have q1 : ((R + 1, 0) : ℝ × ℝ) ∈ H1 := ⟨show R < R + 1 by linarith, Set.mem_univ _⟩
  have i1 : H1 ⊆ connectedComponentIn Kᶜ ((R + 1, 0) : ℝ × ℝ) :=
    c1.subset_connectedComponentIn q1 s1
  have i3 : H3 ⊆ connectedComponentIn Kᶜ ((R + 1, 0) : ℝ × ℝ) :=
    comp_absorb c3 s3 (a := (R + 1, R + 1)) ⟨Set.mem_univ _, show R < R + 1 by linarith⟩
      (i1 ⟨show R < R + 1 by linarith, Set.mem_univ _⟩)
  have i4 : H4 ⊆ connectedComponentIn Kᶜ ((R + 1, 0) : ℝ × ℝ) :=
    comp_absorb c4 s4 (a := (R + 1, -R - 1)) ⟨Set.mem_univ _, show -R - 1 < -R by linarith⟩
      (i1 ⟨show R < R + 1 by linarith, Set.mem_univ _⟩)
  have i2 : H2 ⊆ connectedComponentIn Kᶜ ((R + 1, 0) : ℝ × ℝ) :=
    comp_absorb c2 s2 (a := (-R - 1, R + 1)) ⟨show -R - 1 < -R by linarith, Set.mem_univ _⟩
      (i3 ⟨Set.mem_univ _, show R < R + 1 by linarith⟩)
  rcases hz with h | h
  · rcases le_or_gt 0 z.1 with h0 | h0
    · rw [abs_of_nonneg h0] at h; exact i1 ⟨h, Set.mem_univ _⟩
    · rw [abs_of_neg h0] at h; exact i2 ⟨show z.1 < -R by linarith, Set.mem_univ _⟩
  · rcases le_or_gt 0 z.2 with h0 | h0
    · rw [abs_of_nonneg h0] at h; exact i3 ⟨Set.mem_univ _, h⟩
    · rw [abs_of_neg h0] at h; exact i4 ⟨Set.mem_univ _, show z.2 < -R by linarith⟩

/-- routes from every vertex to one far point; the part of a route at distance `≥ r` from its
vertex avoids the drawing -/
theorem outer_route {V : Type} [Finite V] {G : SimpleGraph V} (D : PlaneDrawing G)
    (hD : ∀ v, D.vertex v ∈ closure (outerFace D)) (r : ℝ) (hr : 0 < r) :
    ∃ q : ℝ × ℝ, (∀ v, r ≤ dist q (D.vertex v)) ∧ ∀ v, ∃ P : Path (D.vertex v) q,
      ∀ s, r ≤ dist (P s) (D.vertex v) → P s ∉ drawingImage D := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (img_compact D).isBounded
  set R : ℝ := |C| + r with hRdef
  have hR0 : 0 ≤ R := by have := abs_nonneg C; linarith
  have hK : ∀ z ∈ drawingImage D, ‖z‖ ≤ R := by
    intro z hz; have := hC z hz; have := le_abs_self C; linarith
  have hopen : IsOpen (drawingImage D)ᶜ := (img_compact D).isClosed.isOpen_compl
  refine ⟨(R + 1, 0), ?_, ?_⟩
  · intro v
    have hv := hK _ (Or.inl ⟨v, rfl⟩)
    have h1 : |(D.vertex v).1| ≤ ‖D.vertex v‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have h2 : |(R + 1) - (D.vertex v).1| ≤ dist ((R + 1, (0:ℝ)) : ℝ × ℝ) (D.vertex v) := by
      rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
    have h3 := le_abs_self (D.vertex v).1
    have hvC : ‖D.vertex v‖ ≤ C := hC _ (Or.inl ⟨v, rfl⟩)
    have h4 : (R + 1) - (D.vertex v).1 ≤ |(R + 1) - (D.vertex v).1| := le_abs_self _
    have h5 := le_abs_self C
    linarith
  · intro v
    obtain ⟨p, ⟨hp1, hp2⟩, hdp⟩ := Metric.mem_closure_iff.1 (hD v) r hr
    -- the component of p contains a far point
    obtain ⟨z, hzC, hz⟩ : ∃ z ∈ connectedComponentIn (drawingImage D)ᶜ p, R < |z.1| ∨ R < |z.2| := by
      by_contra hcon
      push Not at hcon
      apply hp2
      refine isBounded_iff_forall_norm_le.2 ⟨R, fun y hy => ?_⟩
      obtain ⟨a1, a2⟩ := hcon y hy
      rw [Prod.norm_def]
      exact max_le (by simpa using a1) (by simpa using a2)
    have hzq := far_in_comp hR0 hK z hz
    have hqC : ((R + 1, 0) : ℝ × ℝ) ∈ connectedComponentIn (drawingImage D)ᶜ p := by
      rw [connectedComponentIn_eq hzC, ← connectedComponentIn_eq hzq]
      refine mem_connectedComponentIn ?_
      refine far_compl hK (S := {((R + 1, 0) : ℝ × ℝ)}) ?_ rfl
      intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
      left; simp only; rw [abs_of_pos (by linarith)]; linarith
    have hCpc : IsPathConnected (connectedComponentIn (drawingImage D)ᶜ p) :=
      hopen.connectedComponentIn.isConnected_iff_isPathConnected.mp
        (isConnected_connectedComponentIn_iff.mpr hp1)
    have J2 := hCpc.joinedIn p (mem_connectedComponentIn hp1) _ hqC
    have hball : IsPathConnected (Metric.ball (D.vertex v) r) :=
      (convex_ball (D.vertex v) r).isPathConnected ⟨D.vertex v, Metric.mem_ball_self hr⟩
    have J1 := hball.joinedIn (D.vertex v) (Metric.mem_ball_self hr) p
      (by rw [Metric.mem_ball, dist_comm]; exact hdp)
    refine ⟨J1.somePath.trans J2.somePath, fun s hs => ?_⟩
    have hmem : (J1.somePath.trans J2.somePath) s ∈ Set.range (J1.somePath.trans J2.somePath) :=
      Set.mem_range_self s
    rw [Path.trans_range] at hmem
    rcases hmem with ⟨t, ht⟩ | ⟨t, ht⟩
    · have := J1.somePath_mem t
      rw [ht, Metric.mem_ball] at this
      linarith
    · have := J2.somePath_mem t
      rw [ht] at this
      exact connectedComponentIn_subset _ _ this

end PF12

/-! L5-outer: an outerplanar drawing gives a grid model with an outer blob. -/


namespace PF12

open Finset

open RobertsonSeymour1986.GM5 TaitTobin.Outerplanar in
/-- an outerplanar drawing gives a grid model of the graph plus an outer blob adjacent to every
vertex blob -/
theorem model_of_outer {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : PlaneDrawing G) (hD : ∀ v, D.vertex v ∈ closure (outerFace D)) :
    ∃ B : V → Finset (ℤ × ℤ), ∃ O : Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (BlobRel (B v)) p q) ∧
      (∀ v, (B v).Nonempty) ∧ (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w, gAdj p q) ∧
      (∀ v, Disjoint O (B v)) ∧ (∀ p ∈ O, ∀ q ∈ O, Relation.ReflTransGen (BlobRel O) p q) ∧
      O.Nonempty ∧ (∀ v, ∃ p ∈ O, ∃ q ∈ B v, gAdj p q) := by
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
  -- routes to the outside
  obtain ⟨qf, hqf, hroute⟩ := outer_route D hD (ρ / 8) (by positivity)
  choose P hP using hroute
  have himg : ∀ e t, γ e t ∈ drawingImage D := by
    intro e t
    exact Or.inr (Set.mem_iUnion.2 ⟨(vw e).1, Set.mem_iUnion.2 ⟨(vw e).2,
      Set.mem_iUnion.2 ⟨hA e, ⟨t, rfl⟩⟩⟩⟩)
  have himgv : ∀ x, D.vertex x ∈ drawingImage D := fun x => Or.inl ⟨x, rfl⟩
  have hcl1 : ∀ ve : V × G.edgeSet, ∃ c > 0, ∀ s t, ρ / 8 ≤ dist (P ve.1 s) (D.vertex ve.1) →
      c ≤ dist (P ve.1 s) (γ ve.2 t) := by
    rintro ⟨v, e⟩
    obtain ⟨c, hc, hb⟩ := pos_bound
      (F := fun st : unitInterval × unitInterval => dist (P v st.1) (γ e st.2))
      (((P v).continuous.comp continuous_fst).dist ((hγcont e).comp continuous_snd))
      (S := {st | ρ / 8 ≤ dist (P v st.1) (D.vertex v)})
      (isClosed_le continuous_const (((P v).continuous.comp continuous_fst).dist continuous_const))
      (by
        rintro ⟨s, t⟩ hs
        apply dist_pos.mpr
        intro heq
        exact hP v s hs (heq ▸ himg e t))
    exact ⟨c, hc, fun s t hs => hb (s, t) hs⟩
  have hcl2 : ∀ vx : V × V, ∃ c > 0, ∀ s, ρ / 8 ≤ dist (P vx.1 s) (D.vertex vx.1) →
      c ≤ dist (P vx.1 s) (D.vertex vx.2) := by
    rintro ⟨v, x⟩
    obtain ⟨c, hc, hb⟩ := pos_bound
      (F := fun s : unitInterval => dist (P v s) (D.vertex x))
      ((P v).continuous.dist continuous_const)
      (S := {s | ρ / 8 ≤ dist (P v s) (D.vertex v)})
      (isClosed_le continuous_const ((P v).continuous.dist continuous_const))
      (by
        intro s hs
        apply dist_pos.mpr
        intro heq
        exact hP v s hs (heq ▸ himgv x))
    exact ⟨c, hc, fun s hs => hb s hs⟩
  choose c1 hc1pos hc1 using hcl1
  choose c2' hc2'pos hc2' using hcl2
  obtain ⟨ε1, hε1, hε1b⟩ := fin_min c1 hc1pos
  obtain ⟨ε2, hε2, hε2b⟩ := fin_min c2' hc2'pos
  -- the mesh
  obtain ⟨h, hh, hhρ, hhδ, hhε1, hhε2⟩ : ∃ h : ℝ, 0 < h ∧ 12 * h ≤ ρ ∧ 8 * h ≤ δ ∧
      4 * h ≤ ε1 ∧ 4 * h ≤ ε2 :=
    ⟨min (min (ρ / 12) (δ / 8)) (min (ε1 / 4) (ε2 / 4)), by positivity,
      by have := min_le_left (min (ρ / 12) (δ / 8)) (min (ε1 / 4) (ε2 / 4))
         have := min_le_left (ρ / 12) (δ / 8); linarith,
      by have := min_le_left (min (ρ / 12) (δ / 8)) (min (ε1 / 4) (ε2 / 4))
         have := min_le_right (ρ / 12) (δ / 8); linarith,
      by have := min_le_right (min (ρ / 12) (δ / 8)) (min (ε1 / 4) (ε2 / 4))
         have := min_le_left (ε1 / 4) (ε2 / 4); linarith,
      by have := min_le_right (min (ρ / 12) (δ / 8)) (min (ε1 / 4) (ε2 / 4))
         have := min_le_right (ε1 / 4) (ε2 / 4); linarith⟩
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
    {cv v} ∪ (univ.filter (fun e => (vw e).1 = v)).biUnion (fun e => (Vp e).toFinset) ∪
      (univ.filter (fun e => (vw e).2 = v)).biUnion (fun e => (Wp e).toFinset)
  have hmemB : ∀ v c, c ∈ B v ↔ c = cv v ∨ (∃ e, (vw e).1 = v ∧ c ∈ Vp e) ∨
      (∃ e, (vw e).2 = v ∧ c ∈ Wp e) := by
    intro v c
    simp only [B, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, List.mem_toFinset, or_assoc]
  have hcvA' : ∀ v c, c = cv v → c ∈ A v := by
    intro v c hc; rw [hc]; exact hcvA v
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
    rcases (hmemB v c).mp hc with hc | ⟨e, he, hc⟩ | ⟨e, he, hc⟩
    · -- centre cell
      rw [hc]
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
  -- blob cells lie near the drawing
  have hBnear : ∀ x c, c ∈ B x → dist (corner h c) (D.vertex x) < h ∨
      ∃ f t, dist (corner h c) (γ f t) < 2 * h := by
    intro x c hc
    rcases (hmemB x c).mp hc with hc | ⟨e, _, hc⟩ | ⟨e, _, hc⟩
    · left; rw [hc]; exact dist_corner_cellOf hh _
    · obtain ⟨t, _, ht⟩ := WV e c hc; exact Or.inr ⟨e, t, ht⟩
    · obtain ⟨t, _, ht⟩ := WW e c hc; exact Or.inr ⟨e, t, ht⟩
  -- cells near the far part of a route are in no blob
  have hfar : ∀ v c s, dist (corner h c) (P v s) < 2 * h → ρ / 8 ≤ dist (P v s) (D.vertex v) →
      ∀ x, c ∉ B x := by
    intro v c s h1 h2 x hc
    rcases hBnear x c hc with h3 | ⟨f, t, h3⟩
    · have a1 := hc2' (v, x) s h2
      have a2 := hε2b (v, x)
      have a3 := dist_triangle (P v s) (corner h c) (D.vertex x)
      have a4 := dist_comm (P v s) (corner h c)
      linarith
    · have a1 := hc1 (v, f) s t h2
      have a2 := hε1b (v, f)
      have a3 := dist_triangle (P v s) (corner h c) (γ f t)
      have a4 := dist_comm (P v s) (corner h c)
      linarith
  -- cells near the near part of a route lie in the box of the vertex
  have hnear : ∀ v c s, dist (corner h c) (P v s) < 2 * h → dist (P v s) (D.vertex v) < ρ / 8 →
      c ∈ A v := by
    intro v c s h1 h2
    by_contra hc
    have a1 := FA2 v c hc
    have a3 := dist_triangle (corner h c) (P v s) (D.vertex v)
    linarith
  -- a box cell lies in no other blob
  have hAB' : ∀ v x c, c ∈ A v → c ∈ B x → x = v := by
    intro v x c hcA hcB
    by_contra hxv
    rcases (hmemB x c).mp hcB with hc | ⟨f, hf, hc⟩ | ⟨f, hf, hc⟩
    · exact hAA v x c (Ne.symm hxv) hcA (hcvA' x c hc)
    · exact hAV v f c hcA (by rw [hf]; exact Ne.symm hxv) hc
    · exact hAW v f c hcA (by rw [hf]; exact Ne.symm hxv) hc
  -- the walk of cells along each route
  have hOwalk : ∀ v, ∃ T : List (ℤ × ℤ), List.IsChain gridG.Adj T ∧ T.head? = some (cv v) ∧
      T.getLast? = some (cellOf h qf) ∧ ∀ c ∈ T, ∃ s, dist (corner h c) (P v s) < 2 * h := by
    intro v
    obtain ⟨w, hwn, -⟩ := arc_walk (P v) hh
    refine ⟨w.support, w.isChain_adj_support, ?_, ?_, hwn⟩
    · rw [SimpleGraph.Walk.support_eq_cons]; rfl
    · rw [List.getLast?_eq_getLast (SimpleGraph.Walk.support_ne_nil _),
        SimpleGraph.Walk.getLast_support]
  choose T hTch hTh hTl hTn using hOwalk
  -- cut each walk after its last blob cell
  have hsplitO : ∀ v, ∃ X Y : List (ℤ × ℤ), ∃ dd, T v = X ++ Y ∧ X.getLast? = some dd ∧
      (∃ x, dd ∈ B x) ∧ ∀ y ∈ Y, ¬ ∃ x, y ∈ B x :=
    fun v => split_exists _ (T v) ⟨cv v, mem_of_head?' (hTh v), v, (hmemB v _).mpr (Or.inl rfl)⟩
  choose X Y dd hTeq hXl hdd hY using hsplitO
  have hddB : ∀ v, dd v ∈ B v := by
    intro v
    obtain ⟨x, hx⟩ := hdd v
    have hmem : dd v ∈ T v := by
      rw [hTeq v]; exact List.mem_append_left _ (mem_of_getLast?' (hXl v))
    obtain ⟨s, hs⟩ := hTn v (dd v) hmem
    by_cases h8 : ρ / 8 ≤ dist (P v s) (D.vertex v)
    · exact absurd hx (hfar v (dd v) s hs h8 x)
    · have hA' := hnear v (dd v) s hs (lt_of_not_ge h8)
      have hxv := hAB' v x (dd v) hA' hx
      rw [hxv] at hx; exact hx
  have hYne : ∀ v, Y v ≠ [] := by
    intro v hY0
    have hl := hTl v
    rw [hTeq v, hY0, List.append_nil, hXl v] at hl
    simp only [Option.some.injEq] at hl
    obtain ⟨x, hx⟩ := hdd v
    rw [hl] at hx
    have hq1 : dist (corner h (cellOf h qf)) (P v 1) < 2 * h := by
      rw [(P v).target]
      have := dist_corner_cellOf hh qf
      linarith
    exact hfar v _ 1 hq1 (by rw [(P v).target]; exact hqf v) x hx
  have hYlast : ∀ v, (Y v).getLast? = some (cellOf h qf) := by
    intro v
    have := hTl v
    rw [hTeq v, List.getLast?_append_of_ne_nil _ (hYne v)] at this
    exact this
  have hYch : ∀ v, List.IsChain gridG.Adj (Y v) := by
    intro v; have := hTch v; rw [hTeq v, List.isChain_append] at this; exact this.2.1
  -- the outer blob
  let O : Finset (ℤ × ℤ) := univ.biUnion (fun v => (Y v).toFinset)
  have hmemO : ∀ c, c ∈ O ↔ ∃ v, c ∈ Y v := by
    intro c; simp only [O, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset]
  have hOreach : ∀ c ∈ O, Relation.ReflTransGen (BlobRel O) (cellOf h qf) c := by
    intro c hc
    obtain ⟨v, hv⟩ := (hmemO c).mp hc
    have hch : List.IsChain gridG.Adj (Y v).reverse := by
      rw [List.isChain_reverse]
      exact (hYch v).imp (fun a b hab => (show gridG.Adj a b from hab).symm)
    obtain ⟨hd, tl, htl⟩ : ∃ hd tl, (Y v).reverse = hd :: tl :=
      List.exists_cons_of_ne_nil (by simpa using hYne v)
    have hhd : hd = cellOf h qf := by
      have := hYlast v
      rw [← List.head?_reverse, htl] at this; simpa using this
    have hc' : c ∈ hd :: tl := by rw [← htl, List.mem_reverse]; exact hv
    rw [htl] at hch
    have hsub : ∀ x ∈ hd :: tl, x ∈ O := by
      intro x hx; rw [← htl, List.mem_reverse] at hx
      exact (hmemO x).mpr ⟨v, hx⟩
    rw [← hhd]; exact chain_reach O hd tl hch hsub c hc'
  obtain ⟨v0⟩ := ‹Nonempty V›
  refine ⟨B, O, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- disjointness
    intro v x hvx
    rw [Finset.disjoint_left]
    intro c h1 h2
    rcases (hmemB v c).mp h1 with c1 | ⟨e, he, c1⟩ | ⟨e, he, c1⟩ <;>
      rcases (hmemB x c).mp h2 with c2 | ⟨f, hf, c2⟩ | ⟨f, hf, c2⟩
    · exact hAA v x c hvx (hcvA' v c c1) (hcvA' x c c2)
    · exact hAV v f c (hcvA' v c c1) (by rw [hf]; exact hvx) c2
    · exact hAW v f c (hcvA' v c c1) (by rw [hf]; exact hvx) c2
    · exact hAV x e c (hcvA' x c c2) (by rw [he]; exact Ne.symm hvx) c1
    · exact hVV e f c (by rw [he, hf]; exact hvx) c1 c2
    · exact hVW' e f c (by rw [he, hf]; exact hvx) c1 c2
    · exact hAW x e c (hcvA' x c c2) (by rw [he]; exact Ne.symm hvx) c1
    · exact hVW' f e c (by rw [he, hf]; exact Ne.symm hvx) c2 c1
    · exact hWW' e f c (by rw [he, hf]; exact hvx) c1 c2
  · intro v p hp q hq
    exact (reach_symm (hreach v p hp)).trans (hreach v q hq)
  · intro v; exact ⟨cv v, (hmemB v _).mpr (Or.inl rfl)⟩
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
  · intro v
    rw [Finset.disjoint_left]
    intro c hcO hcB
    obtain ⟨u, hu⟩ := (hmemO c).mp hcO
    exact hY u c hu ⟨v, hcB⟩
  · intro p hp q hq
    exact (reach_symm (hOreach p hp)).trans (hOreach q hq)
  · obtain ⟨y, hy⟩ : ∃ y, y ∈ Y v0 := by
      cases hW : Y v0 with
      | nil => exact absurd hW (hYne v0)
      | cons y _ => exact ⟨y, by simp⟩
    exact ⟨y, (hmemO y).mpr ⟨v0, hy⟩⟩
  · intro v
    have hch := hTch v
    rw [hTeq v, List.isChain_append] at hch
    obtain ⟨y, hy⟩ : ∃ y, (Y v).head? = some y := by
      cases hW : Y v with
      | nil => exact absurd hW (hYne v)
      | cons y _ => exact ⟨y, rfl⟩
    have hadj : gridG.Adj (dd v) y := hch.2.2 (dd v) (hXl v) y hy
    exact ⟨y, (hmemO y).mpr ⟨v, mem_of_head?' hy⟩, dd v, hddB v, hadj.symm⟩


end PF12

/-! L7: apex count, K33 contradiction, solution. -/


namespace PF12

open Finset

/-- the edges of `G` and the apex edges inject into the edges of `G + K₁` -/
lemma apex_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype (TaitTobin.Outerplanar.join G (⊥ : SimpleGraph Unit)).edgeSet] :
    Fintype.card G.edgeSet + Fintype.card V ≤
      Fintype.card (TaitTobin.Outerplanar.join G (⊥ : SimpleGraph Unit)).edgeSet := by
  have hmem : ∀ e : G.edgeSet, Sym2.map Sum.inl (e : Sym2 V) ∈
      (TaitTobin.Outerplanar.join G (⊥ : SimpleGraph Unit)).edgeSet := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact (SimpleGraph.mem_edgeSet G).mp he
  let F : G.edgeSet ⊕ V → (TaitTobin.Outerplanar.join G (⊥ : SimpleGraph Unit)).edgeSet :=
    Sum.elim (fun e => ⟨Sym2.map Sum.inl (e : Sym2 V), hmem e⟩)
      (fun v => ⟨s(Sum.inl v, Sum.inr ()), (SimpleGraph.mem_edgeSet _).mpr trivial⟩)
  have hnot : ∀ (e : G.edgeSet) (v : V), Sym2.map Sum.inl (e : Sym2 V) ≠ s(Sum.inl v, Sum.inr ()) := by
    intro e v h
    have : (Sum.inr () : V ⊕ Unit) ∈ Sym2.map Sum.inl (e : Sym2 V) := by
      rw [h]; exact Sym2.mem_mk_right _ _
    rw [Sym2.mem_map] at this
    obtain ⟨a, -, ha⟩ := this
    exact Sum.inl_ne_inr ha
  have hF : Function.Injective F := by
    rintro (e | v) (e' | v') h
    · simp only [F, Sum.elim_inl, Subtype.mk.injEq] at h
      exact congrArg Sum.inl (Subtype.ext (Sym2.map.injective Sum.inl_injective h))
    · simp only [F, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      exact absurd h (hnot e v')
    · simp only [F, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
      exact absurd h.symm (hnot e' v)
    · simp only [F, Sum.elim_inr, Subtype.mk.injEq, Sym2.eq_iff, Sum.inl.injEq] at h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
      · exact absurd h1 Sum.inl_ne_inr
  have := Fintype.card_le_of_injective F hF
  simpa [Fintype.card_sum] using this

/-- a grid model admits no `K₃,₃` -/
lemma k33_contra {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (Bs : W → Finset (ℤ × ℤ))
    (hdisj : ∀ a b, a ≠ b → Disjoint (Bs a) (Bs b))
    (hconn : ∀ a, ∀ p ∈ Bs a, ∀ q ∈ Bs a, Relation.ReflTransGen (BlobRel (Bs a)) p q)
    (hne : ∀ a, (Bs a).Nonempty)
    (hadj : ∀ a b, H.Adj a b → ∃ p ∈ Bs a, ∃ q ∈ Bs b, gAdj p q)
    (g : Fin 3 ⊕ Fin 3 → W) (hg : Function.Injective g)
    (hgadj : ∀ i j, H.Adj (g (Sum.inl i)) (g (Sum.inr j))) : False := by
  classical
  let K := completeBipartiteGraph (Fin 3) (Fin 3)
  have hKadj : ∀ u u', K.Adj u u' → H.Adj (g u) (g u') := by
    rintro (i | i) (j | j) h
    · simp [K, completeBipartiteGraph] at h
    · exact hgadj i j
    · exact (hgadj j i).symm
    · simp [K, completeBipartiteGraph] at h
  have hb := bounds_of_model K (by simp) (fun u => Bs (g u))
    (fun u u' huu => hdisj _ _ (fun h => huu (hg h)))
    (fun u => hconn (g u)) (fun u => hne (g u))
    (fun u u' h => hadj _ _ (hKadj u u' h))
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

end PF12

open Classical WangKangXue.SpectralTuran TaitTobin.Outerplanar RobertsonSeymour1986.GM5 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsOuterplanar G) :
    G.edgeFinset.card ≤ 2 * n - 3 ∧ (completeBipartiteGraph (Fin 2) (Fin 3)).Free G := by
  obtain ⟨D, hD⟩ := hG
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨B, O, hdisj, hconn, hne, hadj, hOd, hOc, hOn, hOa⟩ := PF12.model_of_outer G D hD
  let Bs : Fin n ⊕ Unit → Finset (ℤ × ℤ) := Sum.elim B (fun _ => O)
  have sdisj : ∀ a b, a ≠ b → Disjoint (Bs a) (Bs b) := by
    rintro (a | a) (b | b) hab
    · exact hdisj a b (fun h => hab (congrArg Sum.inl h))
    · exact (hOd a).symm
    · exact hOd b
    · exact absurd (by cases a; cases b; rfl) hab
  have sconn : ∀ a, ∀ p ∈ Bs a, ∀ q ∈ Bs a, Relation.ReflTransGen (PF12.BlobRel (Bs a)) p q := by
    rintro (a | a)
    · exact hconn a
    · exact hOc
  have sne : ∀ a, (Bs a).Nonempty := by
    rintro (a | a)
    · exact hne a
    · exact hOn
  have sadj : ∀ a b, (join G (⊥ : SimpleGraph Unit)).Adj a b →
      ∃ p ∈ Bs a, ∃ q ∈ Bs b, PF12.gAdj p q := by
    rintro (a | a) (b | b) hab
    · exact hadj a b hab
    · obtain ⟨p, hp, q, hq, hpq⟩ := hOa a
      exact ⟨q, hq, p, hp, (show PF12.gridG.Adj p q from hpq).symm⟩
    · exact hOa b
    · exact ((SimpleGraph.bot_adj a b).mp hab).elim
  have hcardJ : 3 ≤ Fintype.card (Fin n ⊕ Unit) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega
  refine ⟨?_, ?_⟩
  · have hb := (PF12.bounds_of_model (join G (⊥ : SimpleGraph Unit)) hcardJ Bs sdisj sconn sne
      sadj).1
    have hcount := PF12.apex_card G
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hb
    rw [Fintype.card_fin] at hcount
    rw [SimpleGraph.edgeFinset_card]
    omega
  · rintro ⟨f⟩
    let g : Fin 3 ⊕ Fin 3 → Fin n ⊕ Unit :=
      Sum.elim ![Sum.inr (), Sum.inl (f (Sum.inl 0)), Sum.inl (f (Sum.inl 1))]
        (fun j => Sum.inl (f (Sum.inr j)))
    have hfi : ∀ a b, f a = f b ↔ a = b := fun a b => ⟨fun h => f.injective h, fun h => h ▸ rfl⟩
    have hg : Function.Injective g := by
      rintro (i | i) (j | j) h <;> (try fin_cases i) <;> (try fin_cases j) <;>
        simp [g, hfi] at h ⊢
    have hgadj : ∀ i j, (join G (⊥ : SimpleGraph Unit)).Adj (g (Sum.inl i)) (g (Sum.inr j)) := by
      intro i j
      fin_cases i
      · exact trivial
      · exact f.toHom.map_adj (by simp [completeBipartiteGraph])
      · exact f.toHom.map_adj (by simp [completeBipartiteGraph])
    exact PF12.k33_contra (join G (⊥ : SimpleGraph Unit)) Bs sdisj sconn sne sadj g hg hgadj
