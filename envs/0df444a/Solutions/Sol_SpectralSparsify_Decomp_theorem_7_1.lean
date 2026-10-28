-- Prove2me | solution 1 for SpectralSparsify.Decomp.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T07:10:07.558993+00:00
-- url     : https://prove2.me/submissions/277df272-ff35-4b88-8c00-1f98b6d04c8a

import Definitions.Def_SpectralSparsify_Decomp_cond
import Definitions.Def_SpectralSparsify_Decomp_decompBoundary
set_option autoImplicit false


open Finset SpectralSparsify.Decomp
namespace SDProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma vol_nonneg (S : Finset V) : 0 ≤ vol G S := by
  exact sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma vol_add_sdiff {B S : Finset V} (hSB : S ⊆ B) :
    vol G S + vol G (B \ S) = vol G B := by
  unfold vol
  rw [← sum_union (disjoint_sdiff_self_right), union_sdiff_of_subset hSB]

omit [DecidableEq V] in
lemma one_le_vol (hdeg : ∀ v, 0 < G.degree v) {S : Finset V} (hS : S.Nonempty) :
    1 ≤ vol G S := by
  obtain ⟨v, hv⟩ := hS
  calc
    1 ≤ (G.degree v : ℝ) := by exact_mod_cast hdeg v
    _ ≤ vol G S := by
      unfold vol
      exact single_le_sum (f := fun v => (G.degree v : ℝ)) (fun _ _ => Nat.cast_nonneg _) hv

omit [DecidableEq V] in
lemma vol_univ : vol G univ = 2 * (G.edgeFinset.card : ℝ) := by
  unfold vol
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

omit [DecidableEq V] in
lemma two_le_total [Nonempty V] (hdeg : ∀ v, 0 < G.degree v) :
    2 ≤ vol G univ := by
  have h := one_le_vol G hdeg (univ_nonempty : (univ : Finset V).Nonempty)
  rw [vol_univ] at h ⊢
  have hm : 0 < G.edgeFinset.card := by
    have : (0 : ℝ) < G.edgeFinset.card := by linarith
    exact_mod_cast this
  have : (1 : ℝ) ≤ G.edgeFinset.card := by exact_mod_cast hm
  linarith

noncomputable def entropy (P : Finpartition (univ : Finset V)) : ℝ :=
  ∑ B ∈ P.parts, vol G B * Real.log (vol G B)

noncomputable def potential (P : Finpartition (univ : Finset V)) : ℝ :=
  6 * Real.log (vol G univ) * (decompBoundary G P).card + entropy G P

lemma entropy_nonneg (hdeg : ∀ v, 0 < G.degree v)
    (P : Finpartition (univ : Finset V)) : 0 ≤ entropy G P := by
  apply sum_nonneg
  intro B hB
  exact mul_nonneg (vol_nonneg G B)
    (Real.log_nonneg (one_le_vol G hdeg (P.nonempty_of_mem_parts hB)))

lemma boundary_indiscrete (h : (univ : Finset V) ≠ ⊥) :
    decompBoundary G (Finpartition.indiscrete h) = ∅ := by
  ext e
  simp [decompBoundary]

lemma entropy_indiscrete (h : (univ : Finset V) ≠ ⊥) :
    entropy G (Finpartition.indiscrete h) = vol G univ * Real.log (vol G univ) := by
  simp [entropy]

end SDProof


open Finset SpectralSparsify.Decomp
namespace SDProof
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def refinePart (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) :
    Finpartition (univ : Finset V) := by
  classical
  let parts := insert S (insert (B \ S) (P.parts.erase B))
  have hT : (B \ S).Nonempty := sdiff_nonempty.mpr (fun h => hSB.ne (Subset.antisymm hSB.subset h))
  refine Finpartition.ofExistsUnique parts (by simp) ?_ ?_
  · intro v _
    obtain ⟨A, hA, hvA⟩ := P.exists_mem (mem_univ v)
    have old_unique : ∀ C ∈ P.parts, v ∈ C → C = A := fun C hC hvC =>
      P.eq_of_mem_parts hC hA hvC hvA
    by_cases hvS : v ∈ S
    · refine ⟨S, ⟨by simp [parts], hvS⟩, ?_⟩
      intro C hC
      simp only [parts, mem_insert, mem_erase] at hC
      have hAB : A = B := (old_unique B hB (hSB.subset hvS)).symm
      rcases hC with ⟨rfl | rfl | ⟨hne, hC⟩, hvC⟩
      · rfl
      · exact False.elim ((mem_sdiff.mp hvC).2 hvS)
      · exact False.elim (hne ((old_unique C hC hvC).trans hAB))
    · by_cases hvB : v ∈ B
      · refine ⟨B \ S, ⟨by simp [parts], mem_sdiff.mpr ⟨hvB, hvS⟩⟩, ?_⟩
        intro C hC
        simp only [parts, mem_insert, mem_erase] at hC
        rcases hC with ⟨rfl | rfl | ⟨hne, hC⟩, hvC⟩
        · exact False.elim (hvS hvC)
        · rfl
        · exact False.elim (hne (P.eq_of_mem_parts hC hB hvC hvB))
      · have hAB : A ≠ B := by rintro rfl; exact hvB hvA
        refine ⟨A, ⟨by simp [parts, hAB, hA], hvA⟩, ?_⟩
        intro C hC
        simp only [parts, mem_insert, mem_erase] at hC
        rcases hC with ⟨rfl | rfl | ⟨_, hC⟩, hvC⟩
        · exact False.elim (hvS hvC)
        · exact False.elim (hvB (mem_sdiff.mp hvC).1)
        · exact old_unique C hC hvC
  · simp [parts, hS.ne_empty.symm, hT.ne_empty.symm, P.empty_notMem_parts]

@[simp] lemma refinePart_parts (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) :
    (refinePart P B S hB hS hSB).parts = insert S (insert (B \ S) (P.parts.erase B)) := rfl

lemma refinePart_part (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) (v : V) :
    (refinePart P B S hB hS hSB).part v =
      if v ∈ S then S else if v ∈ B then B \ S else P.part v := by
  classical
  split_ifs with hs hb
  · apply Finpartition.part_eq_of_mem <;> simp [hs]
  · apply Finpartition.part_eq_of_mem <;> simp [hs, hb]
  · apply Finpartition.part_eq_of_mem
    · have : P.part v ≠ B := by intro h; have := P.mem_part (mem_univ v); exact hb (h ▸ this)
      simp [this]
    · simp

variable (G : SimpleGraph V) [DecidableRel G.Adj]
lemma boundary_mem (P : Finpartition (univ : Finset V)) (u v : V) :
    s(u,v) ∈ decompBoundary G P ↔ G.Adj u v ∧ P.part u ≠ P.part v := by
  classical
  simp only [decompBoundary, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨hadj, A, hA, C, hC, hne, x, hx, y, hy, heq⟩
    refine ⟨hadj, ?_⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [P.part_eq_of_mem hA hx, P.part_eq_of_mem hC hy] using hne
    · simpa [P.part_eq_of_mem hA hx, P.part_eq_of_mem hC hy] using hne.symm
  · rintro ⟨hadj, hne⟩
    exact ⟨hadj, P.part u, by simp, P.part v, by simp, hne, u, by simp, v, by simp, rfl⟩

noncomputable def crossingEdges (S T : Finset V) : Finset (Sym2 V) :=
  ((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).image (fun p => s(p.1,p.2))

omit [Fintype V] in
lemma crossingEdges_mem (S T : Finset V) (u v : V) :
    s(u,v) ∈ crossingEdges G S T ↔ G.Adj u v ∧
      ((u ∈ S ∧ v ∈ T) ∨ (v ∈ S ∧ u ∈ T)) := by
  classical
  simp only [crossingEdges, mem_image, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨x,y⟩, ⟨⟨hx,hy⟩, hadj⟩, heq⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hadj, Or.inl ⟨hx,hy⟩⟩
    · exact ⟨hadj.symm, Or.inr ⟨hx,hy⟩⟩
  · rintro ⟨hadj, ⟨hu,hv⟩ | ⟨hv,hu⟩⟩
    · exact ⟨(u,v), ⟨⟨hu,hv⟩,hadj⟩,rfl⟩
    · exact ⟨(v,u), ⟨⟨hv,hu⟩,hadj.symm⟩,Sym2.eq_swap⟩

omit [Fintype V] in
lemma crossingEdges_card (S T : Finset V) (hd : Disjoint S T) :
    (crossingEdges G S T).card = cutEdges G S T := by
  classical
  apply card_image_of_injOn
  intro p hp q hq heq
  have hp' := (mem_product.mp (mem_filter.mp hp).1)
  have hq' := (mem_product.mp (mem_filter.mp hq).1)
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,_⟩
  · exact Prod.ext h1 h2
  · exact False.elim (disjoint_left.mp hd hp'.1 (h1 ▸ hq'.2))

lemma refinePart_old (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B)
    {A : Finset V} (hA : A ∈ (refinePart P B S hB hS hSB).parts) :
    ∃ C ∈ P.parts, A ⊆ C := by
  simp only [refinePart_parts, mem_insert, mem_erase] at hA
  rcases hA with rfl | rfl | ⟨_,hA⟩
  · exact ⟨B,hB,hSB.subset⟩
  · exact ⟨B,hB,sdiff_subset⟩
  · exact ⟨A,hA,Subset.rfl⟩

lemma refinePart_boundary_union (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) :
    decompBoundary G (refinePart P B S hB hS hSB) =
      decompBoundary G P ∪ crossingEdges G S (B \ S) := by
  classical
  let Q := refinePart P B S hB hS hSB
  have hST : S ≠ B \ S := by
    intro heq
    obtain ⟨x,hx⟩ := hS
    exact (mem_sdiff.mp (heq ▸ hx)).2 hx
  ext e
  induction e using Sym2.ind with | _ u v => ?_
  rw [mem_union, boundary_mem, boundary_mem, crossingEdges_mem]
  constructor
  · rintro ⟨hadj,hnew⟩
    by_cases hold : P.part u = P.part v
    · right
      have huB : u ∈ B := by
        by_contra huB
        have hvB : v ∉ B := by
          intro hvB
          have := P.part_eq_of_mem hB hvB
          exact huB ((hold.trans this) ▸ (P.mem_part (mem_univ u)))
        have huS : u ∉ S := fun h => huB (hSB.subset h)
        have hvS : v ∉ S := fun h => hvB (hSB.subset h)
        exact hnew (by simpa [refinePart_part,huB,hvB,huS,hvS] using hold)
      have hvB : v ∈ B := by
        have hu := P.part_eq_of_mem hB huB
        exact (hold.symm.trans hu) ▸ (P.mem_part (mem_univ v))
      refine ⟨hadj, ?_⟩
      by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
      · exact False.elim (hnew (by simp [refinePart_part,huS,hvS]))
      · exact Or.inl ⟨huS,mem_sdiff.mpr ⟨hvB,hvS⟩⟩
      · exact Or.inr ⟨hvS,mem_sdiff.mpr ⟨huB,huS⟩⟩
      · exact False.elim (hnew (by simp [refinePart_part,huS,hvS,huB,hvB]))
    · exact Or.inl ⟨hadj,hold⟩
  · rintro (⟨hadj,hold⟩ | ⟨hadj,hcross⟩)
    · refine ⟨hadj, ?_⟩
      intro heq
      obtain ⟨C,hC,hsub⟩ := refinePart_old P B S hB hS hSB (Q.part_mem.mpr (mem_univ u))
      have huC := hsub (Q.mem_part (mem_univ u))
      have hvC := hsub (heq ▸ Q.mem_part (mem_univ v))
      exact hold ((P.part_eq_of_mem hC huC).trans (P.part_eq_of_mem hC hvC).symm)
    · refine ⟨hadj, ?_⟩
      rcases hcross with ⟨hu,hv⟩ | ⟨hv,hu⟩
      · simpa [refinePart_part,hu,(mem_sdiff.mp hv).1,(mem_sdiff.mp hv).2] using hST
      · simpa [refinePart_part,hv,(mem_sdiff.mp hu).1,(mem_sdiff.mp hu).2] using hST.symm

lemma refinePart_boundary (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) :
    (decompBoundary G (refinePart P B S hB hS hSB)).card =
      (decompBoundary G P).card + cutEdges G S (B \ S) := by
  classical
  rw [refinePart_boundary_union]
  have hd : Disjoint (decompBoundary G P) (crossingEdges G S (B \ S)) := by
    apply disjoint_left.mpr
    intro e he hc
    induction e using Sym2.ind with | _ u v => ?_
    obtain ⟨_,hn⟩ := (boundary_mem G P u v).mp he
    obtain ⟨_,h⟩ := (crossingEdges_mem G S (B \ S) u v).mp hc
    rcases h with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact hn ((P.part_eq_of_mem hB (hSB.subset hu)).trans
        (P.part_eq_of_mem hB (mem_sdiff.mp hv).1).symm)
    · exact hn ((P.part_eq_of_mem hB (mem_sdiff.mp hu).1).trans
        (P.part_eq_of_mem hB (hSB.subset hv)).symm)
  rw [card_union_of_disjoint hd, crossingEdges_card G S (B \ S) disjoint_sdiff_self_right]

lemma refinePart_entropy (P : Finpartition (univ : Finset V)) (B S : Finset V)
    (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) :
    entropy G (refinePart P B S hB hS hSB) + vol G B * Real.log (vol G B) =
      entropy G P + vol G S * Real.log (vol G S) + vol G (B \ S) * Real.log (vol G (B \ S)) := by
  classical
  have hT : (B \ S).Nonempty := sdiff_nonempty.mpr (fun h => hSB.ne (Subset.antisymm hSB.subset h))
  have hsold : S ∉ P.parts := by
    intro hs
    obtain ⟨x,hx⟩ := hS
    exact hSB.ne (P.eq_of_mem_parts hs hB hx (hSB.subset hx))
  have htold : B \ S ∉ P.parts := by
    intro ht
    obtain ⟨x,hx⟩ := hT
    have heq := P.eq_of_mem_parts ht hB hx (mem_sdiff.mp hx).1
    obtain ⟨y,hy⟩ := hS
    exact (mem_sdiff.mp (heq.symm ▸ hSB.subset hy)).2 hy
  have hST : S ≠ B \ S := by
    intro heq
    obtain ⟨x,hx⟩ := hS
    exact (mem_sdiff.mp (heq ▸ hx)).2 hx
  have hs : S ∉ insert (B \ S) (P.parts.erase B) := by simp [hST,hsold]
  have ht : B \ S ∉ P.parts.erase B := by simp [htold]
  unfold entropy
  rw [refinePart_parts, sum_insert hs, sum_insert ht]
  have he := sum_erase_add P.parts (fun C => vol G C * Real.log (vol G C)) hB
  linarith

end SDProof

set_option autoImplicit false
namespace SDProof

theorem xlogx_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * Real.log x :=
  mul_nonneg (by linarith) (Real.log_nonneg hx)

theorem entropy_split_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min a b * Real.log (4/3) ≤
      (a+b)*Real.log (a+b)-a*Real.log a-b*Real.log b := by
  have hbase : Real.log (4/3) ≤ Real.log (2:ℝ) := Real.log_le_log (by norm_num) (by norm_num)
  have hstep : ∀ x y : ℝ, 0 < x → 0 < y → x ≤ y →
      x * Real.log (2:ℝ) ≤ (x+y)*Real.log (x+y)-x*Real.log x-y*Real.log y := by
    intro x y hx hy hxy
    have h1 := Real.log_le_log (by positivity : 0 < 2*x) (show 2*x ≤ x+y by linarith)
    rw [Real.log_mul (by norm_num) hx.ne'] at h1
    have h2 := Real.log_le_log hy (show y ≤ x+y by linarith)
    nlinarith [mul_nonneg hx.le (show 0 ≤ Real.log (x+y)-Real.log x-Real.log 2 by linarith),
      mul_nonneg hy.le (show 0 ≤ Real.log (x+y)-Real.log y by linarith)]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact (mul_le_mul_of_nonneg_left hbase ha.le).trans (hstep a b ha hb hab)
  · rw [min_eq_right hba]
    have h := (mul_le_mul_of_nonneg_left hbase hb.le).trans (hstep b a hb ha hba)
    rw [add_comm b a] at h
    nlinarith

theorem target_eq {W : ℝ} (hW : 2 ≤ W) :
    (6*Real.logb (4/3) W)⁻¹ = Real.log (4/3)/(6*Real.log W) := by
  have hw : Real.log W ≠ 0 := (Real.log_pos (by linarith : 1 < W)).ne'
  have hb : Real.log (4/3:ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<4/3)).ne'
  unfold Real.logb
  field_simp

theorem target_le_one {W : ℝ} (hW : 2 ≤ W) :
    (6*Real.logb (4/3) W)⁻¹ ≤ 1 := by
  rw [target_eq hW]
  have hw : 0 < Real.log W := Real.log_pos (by linarith)
  apply (div_le_iff₀ (by positivity : 0 < 6*Real.log W)).2
  have hb := Real.log_le_log (by norm_num : (0:ℝ)<4/3) (show (4/3:ℝ)≤W by linarith)
  linarith

theorem split_ratio_bound {a b W d : ℝ} (ha : 0 < a) (hb : 0 < b) (hW : 2 ≤ W)
    (hdrop : (a+b)*Real.log (a+b)-a*Real.log a-b*Real.log b ≤ 6*Real.log W*d) :
    (6*Real.logb (4/3) W)⁻¹ ≤ d/min a b := by
  rw [target_eq hW]
  have hw : 0 < 6*Real.log W := mul_pos (by norm_num) (Real.log_pos (by linarith))
  have hm : 0 < min a b := lt_min ha hb
  apply (div_le_div_iff₀ hw hm).2
  have h := (entropy_split_lower ha hb).trans hdrop
  nlinarith

theorem boundary_scalar {W H d : ℝ} (hW : 2 ≤ W) (hH : 0 ≤ H)
    (h : 6*Real.log W*d+H ≤ W*Real.log W) : d ≤ W/6 := by
  have hw : 0 < Real.log W := Real.log_pos (by linarith)
  nlinarith
end SDProof

set_option autoImplicit false
open Finset SpectralSparsify.Decomp
namespace SDProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_minimizer [Nonempty V] :
    ∃ P : Finpartition (univ : Finset V), ∀ Q, potential G P ≤ potential G Q := by
  classical
  let P₀ : Finpartition (univ : Finset V) :=
    Finpartition.indiscrete (Finset.univ_nonempty.ne_empty)
  obtain ⟨P, _, hP⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Finpartition (univ : Finset V)))
    (potential G) (by exact ⟨P₀, Finset.mem_univ P₀⟩)
  exact ⟨P, fun Q => hP Q (Finset.mem_univ Q)⟩

theorem minimizer_boundary_third [Nonempty V] (hdeg : ∀ v, 0 < G.degree v)
    (P : Finpartition (univ : Finset V))
    (hP : ∀ Q, potential G P ≤ potential G Q) :
    ((decompBoundary G P).card : ℝ) ≤ (G.edgeFinset.card : ℝ)/3 := by
  have hn : (univ : Finset V) ≠ ⊥ := Finset.univ_nonempty.ne_empty
  have h := hP (Finpartition.indiscrete hn)
  simp only [potential, boundary_indiscrete, Finset.card_empty, Nat.cast_zero,
    mul_zero, zero_add, entropy_indiscrete] at h
  have hd := boundary_scalar (two_le_total G hdeg) (entropy_nonneg G hdeg P) h
  rw [vol_univ G] at hd
  linarith
theorem minimizer_cut_ratio [Nonempty V] (hdeg : ∀ v, 0 < G.degree v)
    (P : Finpartition (univ : Finset V))
    (hP : ∀ Q, potential G P ≤ potential G Q)
    (B S : Finset V) (hB : B ∈ P.parts) (hS : S.Nonempty) (hSB : S ⊂ B) :
    (6*Real.logb (4/3) (2*(G.edgeFinset.card:ℝ)))⁻¹ ≤
      (cutEdges G S (B\S):ℝ)/min (vol G S) (vol G (B\S)) := by
  have hT : (B\S).Nonempty := Finset.sdiff_nonempty.mpr
    (fun h => hSB.ne (Finset.Subset.antisymm hSB.subset h))
  have ha : 0 < vol G S := lt_of_lt_of_le (by norm_num) (one_le_vol G hdeg hS)
  have hb : 0 < vol G (B\S) := lt_of_lt_of_le (by norm_num) (one_le_vol G hdeg hT)
  have hc := refinePart_boundary G P B S hB hS hSB
  have he := refinePart_entropy G P B S hB hS hSB
  have hp := hP (refinePart P B S hB hS hSB)
  unfold potential at hp
  rw [hc, Nat.cast_add] at hp
  have hv := vol_add_sdiff G hSB.subset
  have hd :
      (vol G S+vol G (B\S))*Real.log (vol G S+vol G (B\S))-
        vol G S*Real.log (vol G S)-vol G (B\S)*Real.log (vol G (B\S)) ≤
      6*Real.log (vol G univ)*(cutEdges G S (B\S):ℝ) := by
    rw [hv]
    nlinarith
  have h := split_ratio_bound ha hb (two_le_total G hdeg) hd
  rwa [vol_univ G] at h

theorem exists_good_cuts [Nonempty V] (hdeg : ∀ v, 0 < G.degree v) :
    ∃ P : Finpartition (univ : Finset V),
      (∀ B ∈ P.parts, ∀ S, S.Nonempty → S ⊂ B →
        (6*Real.logb (4/3) (2*(G.edgeFinset.card:ℝ)))⁻¹ ≤
          (cutEdges G S (B\S):ℝ)/min (vol G S) (vol G (B\S))) ∧
      ((decompBoundary G P).card:ℝ) ≤ (G.edgeFinset.card:ℝ)/3 := by
  obtain ⟨P,hP⟩ := exists_minimizer G
  exact ⟨P, fun B hB S hS hSB => minimizer_cut_ratio G hdeg P hP B S hB hS hSB,
    minimizer_boundary_third G hdeg P hP⟩
end SDProof


open Finset SpectralSparsify.Decomp
namespace SDProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma cond_lower {q : ℝ} (B : Finset V) (hq : q ≤ 1)
    (hcut : ∀ S, S.Nonempty → S ⊂ B →
      q ≤ (cutEdges G S (B \ S) : ℝ) / min (vol G S) (vol G (B \ S))) :
    q ≤ cond G B := by
  classical
  unfold SpectralSparsify.Decomp.cond
  split_ifs with hb
  · exact hq
  · apply le_inf'
    intro S hS
    have hsB := (mem_filter.mp hS).2
    by_cases hs : S = ∅
    · simpa [condRel,hs] using hq
    · simpa [condRel,hs] using hcut S (nonempty_iff_ne_empty.mpr hs) hsB

lemma decomposition (hdeg : ∀ v, 0 < G.degree v) :
    ∃ P : Finpartition (univ : Finset V),
      (∀ B ∈ P.parts, (6*Real.logb (4/3) (2*(G.edgeFinset.card:ℝ)))⁻¹ ≤ cond G B) ∧
      ((decompBoundary G P).card:ℝ) ≤ (G.edgeFinset.card:ℝ)/2 := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
    let := hV
    refine ⟨⊥, ?_, ?_⟩
    · intro B hB
      have he : B = ∅ := by ext v; exact isEmptyElim v
      exact False.elim ((⊥ : Finpartition (univ : Finset V)).ne_empty hB he)
    · have he : G.edgeFinset = ∅ := by
        ext e
        induction e using Sym2.ind with | _ u v => exact isEmptyElim u
      simp [decompBoundary,he]
  | inr hV =>
    let := hV
    obtain ⟨P,hcuts,hbound⟩ := exists_good_cuts G hdeg
    refine ⟨P, ?_, ?_⟩
    · intro B hB
      apply cond_lower G B
      · have h := target_le_one (two_le_total G hdeg)
        rwa [vol_univ] at h
      · exact hcuts B hB
    · have hm : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
      linarith
end SDProof


namespace SpectralSparsify.Decomp

/-- Theorem 7.1 (arXiv:0808.4134v3, p. 17). Let `G = (V, E)` be a graph without isolated
vertices and `m = |E|`. Then `G` has a `(6 log_{4/3} 2m)⁻¹`-decomposition `(A₁, …, A_k)`,
i.e. a partition of `V` with `Φ^G_{Aᵢ} ≥ (6 log_{4/3} 2m)⁻¹` for all `i`, whose boundary
satisfies `|∂(A₁, …, A_k)| ≤ |E|/2`. -/
theorem theorem_7_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ A ∈ P.parts,
        (6 * Real.logb (4 / 3) (2 * (G.edgeFinset.card : ℝ)))⁻¹ ≤ cond G A) ∧
      ((decompBoundary G P).card : ℝ) ≤ (G.edgeFinset.card : ℝ) / 2 := by
  exact SDProof.decomposition G hdeg

end SpectralSparsify.Decomp

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ A ∈ P.parts,
        (6 * Real.logb (4 / 3) (2 * (G.edgeFinset.card : ℝ)))⁻¹ ≤ SpectralSparsify.Decomp.cond G A) ∧
      ((SpectralSparsify.Decomp.decompBoundary G P).card : ℝ) ≤ (G.edgeFinset.card : ℝ) / 2 := by
  exact SDProof.decomposition G hdeg

