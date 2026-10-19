-- Prove2me | solution 1 for OAI.WeakPinned.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:03:07.617649+00:00
-- url     : https://prove2.me/submissions/f1cf46d5-de27-40ab-aa93-ac9b8d8baf0c

import Mathlib
import Definitions.Def_PinnedDistances
import Definitions.Def_OAIQWWP000
import Theorems.Thm_OAI_WeakPinned_arithmetic_sequence_impossible

section
-- module Solutions.OAIQW_WeakPinned.ExtremalFractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned
open Filter
open scoped Topology

lemma richPairs_subset_offDiag (P : Finset Plane) (s : ℝ) : richPairs P s ⊆ P.offDiag := by
  intro xy h
  obtain ⟨hP,hh,_⟩ := Finset.mem_filter.mp h
  exact Finset.mem_offDiag.mpr ⟨(Finset.mem_product.mp hP).1,(Finset.mem_product.mp hP).2,hh⟩

lemma richPairs_card_le (P : Finset Plane) (s : ℝ) : (richPairs P s).card ≤ P.card*(P.card-1) := by
  calc
    _ ≤ P.offDiag.card := Finset.card_le_card (richPairs_subset_offDiag P s)
    _ = _ := by rw [Finset.offDiag_card,Nat.mul_sub_one]

lemma pairFraction_nonneg (P : Finset Plane) (s : ℝ) : 0 ≤ pairFraction P s := by
  by_cases hn : 1 ≤ P.card
  · exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hn)))
  · have hz : P.card=0 := by omega
    simp [pairFraction,hz]

lemma pairFraction_le_one (P : Finset Plane) (s : ℝ) : pairFraction P s ≤ 1 := by
  by_cases hn : 2 ≤ P.card
  · have hd : 0 < (P.card : ℝ)*((P.card : ℝ)-1) := by
      have : (2:ℝ) ≤ P.card := by exact_mod_cast hn
      nlinarith
    rw [pairFraction,div_le_one hd]
    have hh := richPairs_card_le P s
    have h1 : 1 ≤ P.card := by omega
    exact_mod_cast (show (richPairs P s).card ≤ P.card*(P.card-1) from hh)
  · have hc : P.card=0 ∨ P.card=1 := by omega
    rcases hc with hc | hc <;> simp [pairFraction,hc]

lemma fraction_values_nonempty (n : ℕ) (s : ℝ) :
    ({a : ℝ | ∃ P : Finset Plane, P.card=n ∧ a=pairFraction P s}).Nonempty := by
  obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
  exact ⟨_,P,hP,rfl⟩

lemma fraction_values_bddAbove (n : ℕ) (s : ℝ) :
    BddAbove {a : ℝ | ∃ P : Finset Plane, P.card=n ∧ a=pairFraction P s} := by
  refine ⟨1,?_⟩
  rintro a ⟨P,_,rfl⟩
  exact pairFraction_le_one P s

lemma fraction_le_F (P : Finset Plane) (s : ℝ) (hn : 2 ≤ P.card) : pairFraction P s ≤ F P.card s := by
  rw [F,ite_eq_left hn]
  exact le_csSup (fraction_values_bddAbove _ _) ⟨P,rfl,rfl⟩

lemma F_nonneg (n : ℕ) (s : ℝ) : 0 ≤ F n s := by
  by_cases hn : 2 ≤ n
  · obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
    rw [← hP] at hn ⊢
    exact (pairFraction_nonneg P s).trans (fraction_le_F P s hn)
  · simp [F,hn]

lemma F_le_one (n : ℕ) (s : ℝ) : F n s ≤ 1 := by
  unfold F
  split_ifs
  · exact csSup_le (fraction_values_nonempty _ _) (by rintro a ⟨P,_,rfl⟩; exact pairFraction_le_one P s)
  · norm_num

lemma F_attained (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    ∃ P : Finset Plane, P.card=n ∧ F n s=pairFraction P s := by
  classical
  let A : Finset ℕ := (Finset.range (n*(n-1)+1)).filter (fun k => ∃ P : Finset Plane, P.card=n ∧ (richPairs P s).card=k)
  obtain ⟨P,hP⟩ := Finset.exists_card_eq (α:=Plane) n
  have hA : (richPairs P s).card ∈ A := by
    simp only [A,Finset.mem_filter,Finset.mem_range]
    refine ⟨?_,P,hP,rfl⟩
    have hh := richPairs_card_le P s
    rw [hP] at hh
    omega
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image A id ⟨_,hA⟩
  obtain ⟨Q,hQ,hkQ⟩ := (Finset.mem_filter.mp hk).2
  refine ⟨Q,hQ,le_antisymm ?_ ?_⟩
  · rw [F,ite_eq_left hn]
    apply csSup_le (fraction_values_nonempty _ _)
    rintro a ⟨R,hR,rfl⟩
    have hm : (richPairs R s).card ∈ A := by
      simp only [A,Finset.mem_filter,Finset.mem_range]
      refine ⟨?_,R,hR,rfl⟩
      have hh := richPairs_card_le R s
      rw [hR] at hh
      omega
    have hh := hmax _ hm
    change (richPairs R s).card ≤ k at hh
    simp only [pairFraction,hR,hQ]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (hkQ ▸ hh)) (by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
  · rw [← hQ]
    exact fraction_le_F Q s (hQ ▸ hn)

lemma k_lt_card {P : Finset Plane} {x y : Plane} (hx : x ∈ P) : k P x y < P.card := by
  calc
    _ ≤ (P.erase x).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ < P.card := Finset.card_erase_lt_of_mem hx

lemma richPairs_antitone {P : Finset Plane} (hn : 1 ≤ P.card) {s t : ℝ} (hst : s ≤ t) :
    richPairs P t ⊆ richPairs P s := by
  intro xy h
  obtain ⟨hP,hne,hk⟩ := Finset.mem_filter.mp h
  apply Finset.mem_filter.mpr
  refine ⟨hP,hne,?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hst).trans hk

lemma fraction_antitone {P : Finset Plane} (hn : 2 ≤ P.card) : Antitone (pairFraction P) := by
  intro s t hst
  unfold pairFraction
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (richPairs_antitone (by omega) hst)
  · have : (2:ℝ) ≤ P.card := by exact_mod_cast hn
    nlinarith

lemma F_antitone (n : ℕ) : Antitone (F n) := by
  intro s t hst
  by_cases hn : 2 ≤ n
  · obtain ⟨P,hP,hF⟩ := F_attained n hn t
    rw [hF]
    have hPn : 2 ≤ P.card := hP ▸ hn
    calc
      _ ≤ pairFraction P s := fraction_antitone hPn hst
      _ ≤ F n s := by simpa [hP] using fraction_le_F P s hPn
  · simp [F,hn]

lemma F_eq_zero_of_one_le (n : ℕ) {s : ℝ} (hs : 1 ≤ s) : F n s=0 := by
  by_cases hn : 2 ≤ n
  · obtain ⟨P,hP,hF⟩ := F_attained n hn s
    have hz : richPairs P s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro xy hh
      obtain ⟨hxy,_,hk⟩ := Finset.mem_filter.mp hh
      have hlt := k_lt_card (x:=xy.1) (y:=xy.2) (Finset.mem_product.mp hxy).1
      have h1 : (1:ℝ) ≤ P.card := by rw [hP]; exact_mod_cast (show 1 ≤ n by omega)
      have hr := Real.rpow_le_rpow_of_exponent_le h1 hs
      rw [Real.rpow_one] at hr
      have hlt' : (k P xy.1 xy.2 : ℝ) < P.card := by exact_mod_cast hlt
      linarith
    rw [hF,pairFraction,hz]
    simp
  · simp [F,hn]

end WeakPinned

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ExtremalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

/- Finite extremal core construction. The truncated-fiber score gives the same
   core as pruning while avoiding an arbitrary pruning order. It uses the
   original fibers without a generic-position hypothesis. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Core
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]

namespace Fibers
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma size_erase (C : Finset V) (v : V) (e : I) :
    G.size (C.erase v) e = G.size C e - if v ∈ G.targets e ∩ C then 1 else 0 := by
  have he : G.targets e ∩ C.erase v=(G.targets e ∩ C).erase v := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_erase]
    tauto
  change (G.targets e ∩ C.erase v).card=_
  rw [he]
  by_cases hv : v ∈ G.targets e ∩ C
  · simp [size,hv,Finset.card_erase_of_mem hv]
  · simp [size,hv]

omit [Fintype V] [Fintype I] in
lemma contribution_nonneg (K : ℝ) (C : Finset V) (e : I) : 0 ≤ G.contribution K C e := by
  unfold contribution
  split_ifs <;> positivity

omit [Fintype V] [Fintype I] in
lemma contribution_erase_loss (K : ℝ) (hK : 0 ≤ K) (C : Finset V) (v : V) (e : I) :
    G.contribution K C e-G.contribution K (C.erase v) e ≤ G.fiberDegree K C v e := by
  by_cases ha : G.active K C e
  · obtain ⟨hs,hk⟩ := ha
    rw [fiberDegree,ite_eq_left ⟨hs,hk⟩]
    by_cases hv : G.source e=v
    · have hno : v ∉ G.targets e ∩ C := by
        intro hh
        exact G.no_loop e (hv ▸ (Finset.mem_inter.mp hh).1)
      have he1 : G.contribution K C e=(G.size C e : ℝ)-K := by
        simp [contribution,hs,max_eq_left (le_of_lt (sub_pos.mpr hk))]
      have he0 : G.contribution K (C.erase v) e=0 := by simp [contribution,hv]
      rw [he1,he0,ite_eq_left hv,ite_eq_right hno]
      linarith
    · have hse : G.source e ∈ C.erase v := Finset.mem_erase.mpr ⟨hv,hs⟩
      simp only [contribution,ite_eq_left hs,ite_eq_left hse,ite_eq_right hv,zero_add,
        max_eq_left (le_of_lt (sub_pos.mpr hk))]
      by_cases hm : v ∈ G.targets e ∩ C
      · rw [ite_eq_left hm,G.size_erase,ite_eq_left hm]
        have hpos : 1 ≤ G.size C e := Finset.one_le_card.mpr ⟨v,hm⟩
        rw [Nat.cast_sub hpos]
        have hh := le_max_left ((G.size C e : ℝ)-1-K) 0
        norm_num only [Nat.cast_one]
        linarith
      · rw [ite_eq_right hm,G.size_erase,ite_eq_right hm,Nat.sub_zero,max_eq_left (le_of_lt (sub_pos.mpr hk))]
        simp
  · have hz : G.contribution K C e=0 := by
      unfold contribution
      by_cases hs : G.source e ∈ C
      · rw [ite_eq_left hs,max_eq_right]
        exact sub_nonpos.mpr (le_of_not_gt (fun hk => ha ⟨hs,hk⟩))
      · rw [ite_eq_right hs]
    rw [hz,fiberDegree,ite_eq_right ha,zero_sub]
    exact neg_nonpos.mpr (G.contribution_nonneg K _ e)

lemma sum_fiberDegree (K : ℝ) (C : Finset V) (v : V) :
    (∑ e, G.fiberDegree K C v e)=G.degree K C v := by
  classical
  have hout (e : I) : (if G.active K C e then (if G.source e=v then (G.size C e : ℝ) else 0) else 0)=
      ∑ y : V, if G.active K C e ∧ G.source e=v ∧ y ∈ G.targets e ∩ C then (1:ℝ) else 0 := by
    by_cases ha : G.active K C e <;> by_cases hs : G.source e=v <;>
      simp [ha,hs,size]
    congr 1
    ext y
    simp
  have hin (e : I) : (if G.active K C e then (if v ∈ G.targets e ∩ C then (1:ℝ) else 0) else 0)=
      ∑ x : V, if G.active K C e ∧ G.source e=x ∧ v ∈ G.targets e ∩ C then (1:ℝ) else 0 := by
    by_cases ha : G.active K C e <;> by_cases hv : v ∈ G.targets e ∩ C <;> simp [ha,hv]
  have hone (x y : V) : (∑ e, if G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C then (1:ℝ) else 0)=
      if G.edge K C x y then 1 else 0 := by
    by_cases hh : G.edge K C x y
    · obtain ⟨e,he,hs,hy⟩ := hh
      rw [ite_eq_left ⟨e,he,hs,hy⟩]
      rw [Finset.sum_eq_single e]
      · simp [he,hs,hy]
      · intro f _ hfe
        rw [ite_eq_right]
        rintro ⟨_,hfs,hfy⟩
        exact hfe (G.edge_unique K C x y hfs hs (Finset.mem_inter.mp hfy).1 (Finset.mem_inter.mp hy).1)
      · simp
    · have hn : ∀ e, ¬(G.active K C e ∧ G.source e=x ∧ y ∈ G.targets e ∩ C) :=
        fun e he => hh ⟨e,he⟩
      simp only [ite_eq_right (hn _),Finset.sum_const_zero,ite_eq_right hh]
  have hs (e : I) : G.fiberDegree K C v e =
      (if G.active K C e then (if G.source e=v then (G.size C e : ℝ) else 0) else 0)+
      (if G.active K C e then (if v ∈ G.targets e ∩ C then (1:ℝ) else 0) else 0) := by
    unfold fiberDegree
    split_ifs <;> ring
  simp_rw [hs,hout,hin]
  rw [Finset.sum_add_distrib,Finset.sum_comm,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun e x => if G.active K C e ∧ G.source e=x ∧ v ∈ G.targets e ∩ C then (1:ℝ) else 0)]
  simp only [hone,degree,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

lemma score_erase_loss (K : ℝ) (hK : 0 ≤ K) (C : Finset V) (v : V) :
    G.score K C-G.score K (C.erase v) ≤ G.degree K C v := by
  rw [score,score,← Finset.sum_sub_distrib,← G.sum_fiberDegree K C v]
  exact Finset.sum_le_sum (fun e _ => G.contribution_erase_loss K hK C v e)

/-- Constants here are finite numeric bounds on the original extremal scores.
    The proof is a maximization on subsets, not an assumption of a core. -/
theorem exists_core (K a U : ℝ) (hK : 0 ≤ K) (m₀ : ℕ) (hm : m₀ < Fintype.card V)
    (hboundary : ∀ C : Finset V, C.card=m₀ → G.score K C ≤ U*(m₀ : ℝ)*((m₀ : ℝ)-1))
    (hgap : (U-a)*(m₀ : ℝ)*((m₀ : ℝ)-1) < G.objective K a Finset.univ) :
    ∃ C : Finset V, m₀ < C.card ∧ G.objective K a Finset.univ ≤ G.objective K a C ∧
      ∀ v ∈ C, 2*a*((C.card : ℝ)-1) ≤ G.degree K C v := by
  classical
  let S : Finset (Finset V) := Finset.univ.filter (fun C => m₀ ≤ C.card)
  have hu : (Finset.univ : Finset V) ∈ S := by simp [S,le_of_lt hm]
  obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image S (G.objective K a) ⟨_,hu⟩
  have hmc : m₀ ≤ C.card := (Finset.mem_filter.mp hC).2
  have hge := hmax _ hu
  have hlt : m₀ < C.card := by
    by_contra hh
    have he : C.card=m₀ := le_antisymm (le_of_not_gt hh) hmc
    have hb := hboundary C he
    unfold objective penalty at hge hgap
    rw [he] at hge
    nlinarith
  refine ⟨C,hlt,hge,?_⟩
  intro v hv
  have hce : C.erase v ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.card_erase_of_mem hv]
    omega
  have hh := hmax _ hce
  have hl := G.score_erase_loss K hK C v
  have hn : 1 ≤ C.card := Finset.one_le_card.mpr ⟨v,hv⟩
  unfold objective penalty at hh
  rw [Finset.card_erase_of_mem hv,Nat.cast_sub hn] at hh
  norm_num at hh
  nlinarith

end Fibers
end WeakPinned.Core

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma contribution_formula (K : ℝ) (C : Finset V) (e : I) :
    G.contribution K C e = if G.active K C e then (G.size C e : ℝ)-K else 0 := by
  unfold contribution active
  by_cases hs : G.source e ∈ C
  · by_cases hk : K < (G.size C e : ℝ)
    · simp [hs,hk,max_eq_left (le_of_lt (sub_pos.mpr hk))]
    · simp [hs,hk,max_eq_right (sub_nonpos.mpr (le_of_not_gt hk))]
  · simp [hs]

lemma score_le_edgeSet (K : ℝ) (hK : 0 ≤ K) (C : Finset V) :
    G.score K C ≤ (G.edgeSet K C).card := by
  rw [score,G.edgeSet_card]
  apply Finset.sum_le_sum
  intro e _
  rw [G.contribution_formula]
  split_ifs <;> linarith

lemma score_univ_lower (K : ℝ) :
    (∑ e, (G.targets e).card : ℝ)-K*(Fintype.card I : ℝ) ≤ G.score K Finset.univ := by
  have hh : ∀ e, (G.targets e).card-K ≤ G.contribution K Finset.univ e := by
    intro e
    simp [contribution,size]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun e _ => hh e)
  simpa [Finset.sum_sub_distrib,score,mul_comm] using hs

lemma sum_sizes_le_edgeSet_univ (K : ℝ) (h : ∀ e, K < ((G.targets e).card : ℝ)) :
    (∑ e, ((G.targets e).card : ℝ))=(G.edgeSet K Finset.univ).card := by
  rw [G.edgeSet_card]
  apply Finset.sum_congr rfl
  intro e _
  have ha : G.active K Finset.univ e := by simp [active,size,h e]
  simp [ha,size]

lemma number_fibers (L K : ℝ) (hKL : K < L)
    (hL : ∀ e, L ≤ ((G.targets e).card : ℝ)) :
    (Fintype.card I : ℝ)*L ≤ (G.edgeSet K Finset.univ).card := by
  rw [← G.sum_sizes_le_edgeSet_univ K (fun e => hKL.trans_le (hL e))]
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun e _ => hL e)

end WeakPinned.Core.Fibers

namespace WeakPinned
open WeakPinned.Core

lemma planar_target_iff (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) (y : P) :
    y ∈ (planarFibers P s).targets e ↔ dist y.val e.val.1=e.val.2 := by
  simp [planarFibers]

lemma planar_fiber_card (P : Finset Plane) (s : ℝ) (e : fiberIndices P s) :
    (P.card : ℝ)^s ≤ ((planarFibers P s).targets e).card := by
  obtain ⟨xy,hxy,he⟩ := Finset.mem_image.mp e.property
  obtain ⟨hP,hne,hk⟩ := Finset.mem_filter.mp hxy
  have hsrc : e.val.1=xy.1 := (congrArg Prod.fst he).symm
  have hrad : e.val.2=dist xy.2 xy.1 := (congrArg Prod.snd he).symm
  have hi : Function.Injective (fun y : P => y.val) := Subtype.val_injective
  have heq : ((planarFibers P s).targets e).image (fun y : P => y.val)=distanceFiber P xy.1 xy.2 := by
    ext y
    simp only [Finset.mem_image,distanceFiber,Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hz' := (planar_target_iff P s e z).mp hz
      rw [hsrc,hrad] at hz'
      refine ⟨⟨?_,z.property⟩,hz'⟩
      intro hh
      rw [hh,dist_self] at hz'
      exact (dist_pos.mpr hne.symm).ne hz'
    · rintro ⟨⟨_,hy⟩,hd⟩
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      apply (planar_target_iff _ _ _ _).mpr
      simpa [hsrc,hrad] using hd
  have hc : ((planarFibers P s).targets e).card = k P xy.1 xy.2 := by
    rw [← Finset.card_image_of_injective _ hi,heq]
    rfl
  rw [hc]
  exact hk

lemma planeSubset_card (P : Finset Plane) (C : Finset P) : (planeSubset P C).card=C.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

lemma restricted_targets_subset (P : Finset Plane) (s : ℝ) (C : Finset P)
    (e : fiberIndices P s) (y : P) (hy : y ∈ (planarFibers P s).targets e) :
    (((planarFibers P s).targets e ∩ C).image Subtype.val) ⊆
      distanceFiber (planeSubset P C) e.val.1 y.val := by
  intro z hz
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hz
  subst z
  obtain ⟨hzt,hzC⟩ := Finset.mem_inter.mp hw
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_image.mpr ⟨w,hzC,rfl⟩⟩,?_⟩
  · intro hh
    have hd := (planar_target_iff P s e w).mp hzt
    rw [hh,dist_self] at hd
    exact (index_radius_pos P s e).ne hd
  · rw [(planar_target_iff _ _ _ _).mp hzt,(planar_target_iff _ _ _ _).mp hy]

lemma core_edge_rich (P : Finset Plane) (s K r : ℝ) (C : Finset P)
    (hK : (C.card : ℝ)^r ≤ K) (x y : P)
    (hxy : (planarFibers P s).edge K C x y) :
    (x.val,y.val) ∈ richPairs (planeSubset P C) r := by
  obtain ⟨e,⟨hs,hsize⟩,hsrc,hy⟩ := hxy
  have hxC : x ∈ C := hsrc ▸ hs
  have hyC := (Finset.mem_inter.mp hy).2
  have hyT := (Finset.mem_inter.mp hy).1
  have hne : x ≠ y := by
    intro hh
    exact (planarFibers P s).no_loop e (hsrc ▸ hh ▸ hyT)
  have hsrc' : e.val.1=x.val := congrArg Subtype.val hsrc
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hxC,rfl⟩,
    Finset.mem_image.mpr ⟨y,hyC,rfl⟩⟩,?_,?_⟩
  · exact fun hh => hne (Subtype.ext hh)
  · rw [planeSubset_card]
    have hc := Finset.card_le_card (restricted_targets_subset P s C e y hyT)
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hsrc'] at hc
    have hc' : ((planarFibers P s).size C e : ℝ) ≤ k (planeSubset P C) x.val y.val := by
      exact_mod_cast hc
    exact hK.trans ((le_of_lt hsize).trans hc')

end WeakPinned

namespace WeakPinned
open scoped BigOperators

lemma subtype_pair_injective (P : Finset Plane) :
    Function.Injective (fun xy : P × P => (xy.1.val,xy.2.val)) := by
  intro x y h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma core_edge_card (P : Finset Plane) (s K r : ℝ) (C : Finset P)
    (hK : (C.card : ℝ)^r ≤ K) :
    ((planarFibers P s).edgeSet K C).card ≤ (richPairs (planeSubset P C) r).card := by
  rw [← Finset.card_image_of_injective _ (subtype_pair_injective P)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨xy,he,hval⟩ := Finset.mem_image.mp hz
  subst z
  exact core_edge_rich P s K r C hK xy.1 xy.2 (Finset.mem_filter.mp he).2

lemma core_score_bound (P : Finset Plane) (s K r : ℝ) (C : Finset P)
    (hK0 : 0 ≤ K) (hK : (C.card : ℝ)^r ≤ K) (hn : 2 ≤ C.card) :
    (planarFibers P s).score K C ≤ F C.card r*(C.card : ℝ)*((C.card : ℝ)-1) := by
  have hQ := fraction_le_F (planeSubset P C) r (by simpa [planeSubset_card] using hn)
  have hpos : 0 < (C.card : ℝ)*((C.card : ℝ)-1) := by
    have hh : (2:ℝ) ≤ C.card := by exact_mod_cast hn
    nlinarith
  rw [pairFraction,planeSubset_card,div_le_iff₀ hpos] at hQ
  calc
    _ ≤ (((planarFibers P s).edgeSet K C).card : ℝ) := (planarFibers P s).score_le_edgeSet K hK0 C
    _ ≤ ((richPairs (planeSubset P C) r).card : ℝ) := by exact_mod_cast core_edge_card P s K r C hK
    _ ≤ _ := by simpa only [mul_assoc] using hQ

lemma initial_edge_image (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    ((planarFibers P s).edgeSet K Finset.univ).image (fun xy : P × P => (xy.1.val,xy.2.val)) =
      richPairs P s := by
  ext xy
  constructor
  · intro h
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨e,_,hsrc,hy⟩ := (Finset.mem_filter.mp hxy).2
    have hyT := (Finset.mem_inter.mp hy).1
    have hsrc' : e.val.1=x.val := congrArg Subtype.val hsrc
    have hr : dist y.val e.val.1=e.val.2 := (planar_target_iff P s e y).mp hyT
    have hne : x.val ≠ y.val := by
      intro hh
      rw [hsrc',hh,dist_self] at hr
      exact (index_radius_pos P s e).ne hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨x.property,y.property⟩,hne,?_⟩
    have hc := planar_fiber_card P s e
    have heq : ((planarFibers P s).targets e).image Subtype.val=distanceFiber P x.val y.val := by
      ext z
      constructor
      · intro hz
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        have hd := (planar_target_iff P s e w).mp hw
        rw [hsrc'] at hd hr
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_erase.mpr ⟨?_,w.property⟩,hd.trans hr.symm⟩
        intro hh
        rw [hh,dist_self] at hd
        exact (index_radius_pos P s e).ne hd
      · intro hz
        obtain ⟨hz,hd⟩ := Finset.mem_filter.mp hz
        have hzP := (Finset.mem_erase.mp hz).2
        refine Finset.mem_image.mpr ⟨⟨z,hzP⟩,?_,rfl⟩
        apply (planar_target_iff P s e _).mpr
        simpa [hsrc'] using hd.trans (by simpa [hsrc'] using hr)
    have hcard : ((planarFibers P s).targets e).card=k P x.val y.val := by
      rw [← Finset.card_image_of_injective _ Subtype.val_injective,heq]
      rfl
    simpa only [hcard] using hc
  · intro hxy
    obtain ⟨hP,hne,hk⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hP
    let x : P := ⟨xy.1,hx⟩
    let y : P := ⟨xy.2,hy⟩
    let e : fiberIndices P s := ⟨(xy.1,dist xy.2 xy.1),Finset.mem_image.mpr ⟨xy,hxy,rfl⟩⟩
    refine Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    refine ⟨e,⟨Finset.mem_univ _,?_⟩,rfl,Finset.mem_inter.mpr ⟨?_,Finset.mem_univ _⟩⟩
    · simpa only [Core.Fibers.size,Finset.inter_univ] using hK.trans_le (planar_fiber_card P s e)
    · exact (planar_target_iff P s e y).mpr rfl

lemma initial_edge_card (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    ((planarFibers P s).edgeSet K Finset.univ).card=(richPairs P s).card := by
  rw [← Finset.card_image_of_injective _ (subtype_pair_injective P),initial_edge_image P s K hK]

lemma initial_score_lower (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    (richPairs P s).card-K*(Fintype.card (fiberIndices P s) : ℝ) ≤
      (planarFibers P s).score K Finset.univ := by
  have hh := (planarFibers P s).score_univ_lower K
  rw [(planarFibers P s).sum_sizes_le_edgeSet_univ K (fun e => hK.trans_le (planar_fiber_card P s e)),
    initial_edge_card P s K hK] at hh
  exact hh

lemma index_card_bound (P : Finset Plane) (s K : ℝ) (hK : K < (P.card : ℝ)^s) :
    (Fintype.card (fiberIndices P s) : ℝ)*(P.card : ℝ)^s ≤ (richPairs P s).card := by
  have hh := (planarFibers P s).number_fibers ((P.card : ℝ)^s) K hK (planar_fiber_card P s)
  simpa only [initial_edge_card P s K hK] using hh

end WeakPinned

namespace WeakPinned
open scoped BigOperators

lemma initial_score_rate (P : Finset Plane) (s K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hK : K < (P.card : ℝ)^s) (hKL : K ≤ ρ*(P.card : ℝ)^s) :
    (richPairs P s).card-ρ*((P.card : ℝ)*((P.card : ℝ)-1)) ≤
      (planarFibers P s).score K Finset.univ := by
  have hf := index_card_bound P s K hK
  have hc : ((richPairs P s).card : ℝ) ≤ (P.card : ℝ)*((P.card : ℝ)-1) := by
    by_cases hn : 1 ≤ P.card
    · have hh := richPairs_card_le P s
      have hc' : ((richPairs P s).card : ℝ) ≤ (P.card*(P.card-1) : ℕ) := by exact_mod_cast hh
      simpa only [Nat.cast_mul,Nat.cast_sub hn,Nat.cast_one] using hc'
    · have hz : P.card=0 := by omega
      have hzero : (richPairs P s).card=0 := by
        have hh := richPairs_card_le P s
        rw [hz] at hh
        simpa using hh
      simp [hz,hzero]
  have hi0 : 0 ≤ (Fintype.card (fiberIndices P s) : ℝ) := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hKL hi0
  have h2 := mul_le_mul_of_nonneg_left hf hρ
  have h3 := mul_le_mul_of_nonneg_left hc hρ
  have h4 := initial_score_lower P s K hK
  nlinarith

/-- A finite actual planar core. All hypotheses before the conclusion are
    scalar extremal bounds; the graph, degrees and surviving fibers are
    constructed, not postulated. -/
theorem finite_extremal_core (P : Finset Plane) (s r K θ η : ℝ) (m₀ : ℕ)
    (hn : 2 ≤ P.card) (hm0 : 2 ≤ m₀) (hm : m₀ < P.card)
    (hη : 0 < η) (hK0 : 0 ≤ K) (hK : K < (P.card : ℝ)^s)
    (hloss : K ≤ (η/8)*(P.card : ℝ)^s)
    (hinit : θ-η/8 ≤ pairFraction P s)
    (hboundary : (m₀ : ℝ)*((m₀ : ℝ)-1) ≤ (P.card : ℝ)*((P.card : ℝ)-1)/2)
    (hthreshold : ∀ m : ℕ, m₀ ≤ m → m ≤ P.card → (m : ℝ)^r ≤ K)
    (hext : ∀ m : ℕ, m₀ ≤ m → m ≤ P.card → F m r ≤ θ+η/8) :
    ∃ C : Finset P, m₀ < C.card ∧
      (θ-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤ ((planarFibers P s).edgeSet K C).card ∧
      (((planarFibers P s).edgeSet K C).card : ℝ) ≤ (θ+η/8)*(C.card : ℝ)*((C.card : ℝ)-1) ∧
      (∀ x ∈ C, 2*(θ-η)*((C.card : ℝ)-1) ≤ (planarFibers P s).degree K C x) := by
  let G := planarFibers P s
  let A : ℝ := (P.card : ℝ)*((P.card : ℝ)-1)
  have hA : 0 < A := by
    have hh : (2:ℝ) ≤ P.card := by exact_mod_cast hn
    dsimp [A]
    nlinarith
  have hinit' : (θ-η/8)*A ≤ (richPairs P s).card := by
    simpa only [pairFraction,A,le_div_iff₀ hA] using hinit
  have hscore := initial_score_rate P s K (η/8) (by positivity) hK hloss
  have hscore' : (θ-η/4)*A ≤ G.score K Finset.univ := by
    change (richPairs P s).card-η/8*A ≤ G.score K Finset.univ at hscore
    nlinarith
  have hobj : 3*η/4*A ≤ G.objective K (θ-η) Finset.univ := by
    simp only [Core.Fibers.objective,Core.Fibers.penalty,Finset.card_univ,Fintype.card_coe]
    unfold A at hscore' ⊢
    nlinarith
  obtain ⟨C,hC,hge,hdeg⟩ := G.exists_core K (θ-η) (θ+η/8) hK0 m₀
    (by simpa using hm) (fun C hCm => by
      have hc := core_score_bound P s K r C hK0 (hCm ▸ hthreshold m₀ le_rfl (le_of_lt hm)) (by omega)
      rw [hCm] at hc
      have hmR : (1:ℝ) ≤ m₀ := by exact_mod_cast (show 1 ≤ m₀ by omega)
      have he := mul_le_mul_of_nonneg_right (hext m₀ le_rfl (le_of_lt hm))
        (mul_nonneg (Nat.cast_nonneg m₀) (sub_nonneg.mpr hmR))
      dsimp [G]
      nlinarith) (by
      have hh := mul_le_mul_of_nonneg_left hboundary (show 0 ≤ 9*η/8 by positivity)
      change _ < G.objective K (θ-η) Finset.univ
      unfold A at hobj
      have hηA := mul_pos hη hA
      unfold A at hηA
      nlinarith)
  have hCn : C.card ≤ P.card := by simpa using Finset.card_le_univ C
  have hCm : m₀ ≤ C.card := le_of_lt hC
  have hC1 : (1:ℝ) ≤ C.card := by exact_mod_cast (show 1 ≤ C.card by omega)
  have hprod : 0 ≤ (C.card : ℝ)*((C.card : ℝ)-1) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hC1)
  have hscore0 : (θ-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤ G.score K C := by
    have hh : 0 ≤ G.objective K (θ-η) Finset.univ := (le_of_lt (by positivity : 0 < 3*η/4*A)).trans hobj
    unfold Core.Fibers.objective Core.Fibers.penalty at hge hh
    linarith
  have hedge := core_edge_card P s K r C (hthreshold C.card hCm hCn)
  have hQ := fraction_le_F (planeSubset P C) r (by simpa [planeSubset_card] using (show 2 ≤ C.card by omega))
  rw [pairFraction,planeSubset_card] at hQ
  have hp : 0 < (C.card : ℝ)*((C.card : ℝ)-1) := by
    have h2 : (2:ℝ) ≤ C.card := by exact_mod_cast (show 2 ≤ C.card by omega)
    nlinarith
  rw [div_le_iff₀ hp] at hQ
  have he := mul_le_mul_of_nonneg_right (hext C.card hCm hCn) hprod
  refine ⟨C,hC,hscore0.trans (G.score_le_edgeSet K hK0 C),?_,hdeg⟩
  have he' : (((planarFibers P s).edgeSet K C).card : ℝ) ≤ (richPairs (planeSubset P C) r).card := by exact_mod_cast hedge
  nlinarith

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.UniformCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

lemma retained_card (D : Finset V) (Q : I → Prop) [DecidablePred Q] :
    (((G.retained D Q).edgeSet (-1) D).card : ℝ) =
      ∑ e, if Q e ∧ G.source e ∈ D then (G.size D e : ℝ) else 0 := by
  rw [edgeSet_card]
  apply Finset.sum_congr rfl
  intro e _
  have hsize : (G.retained D Q).size D e = if Q e then G.size D e else 0 := by
    by_cases hq : Q e <;> simp [size,retained,hq]
  have ha : (G.retained D Q).active (-1) D e ↔ G.source e ∈ D := by
    change (G.source e ∈ D ∧ (-1:ℝ)<((G.retained D Q).size D e : ℝ)) ↔ _
    have hh : (-1:ℝ)<((G.retained D Q).size D e : ℝ) := by have hh := Nat.cast_nonneg (α:=ℝ) ((G.retained D Q).size D e); linarith
    simp [hh]
  simp only [ha,hsize]
  by_cases hq : Q e <;> by_cases hs : G.source e ∈ D <;> simp [hq,hs]

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators

lemma heavySubset_edge_rich (P : Finset Plane) (s K lam r : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hK : (D.card : ℝ)^r ≤ lam*K) (x y : P)
    (hxy : ((planarFibers P s).retained D (heavyFiber P s K lam C D)).edge (-1) D x y) :
    (x.val,y.val) ∈ richPairs (planeSubset P D) r := by
  obtain ⟨e,ha,hsrc,hy⟩ := hxy
  have hxD : x ∈ D := hsrc ▸ ha.1
  have hyD := (Finset.mem_inter.mp hy).2
  have hyT := (Finset.mem_inter.mp hy).1
  change y ∈ (if heavyFiber P s K lam C D e then (planarFibers P s).targets e ∩ D else ∅) at hyT
  split_ifs at hyT with he
  · obtain ⟨hactive,hheavy⟩ := he
    have hsz : (D.card : ℝ)^r ≤ ((planarFibers P s).size D e : ℝ) :=
      hK.trans ((mul_le_mul_of_nonneg_left (le_of_lt hactive.2) hlam).trans hheavy)
    have hyT' := (Finset.mem_inter.mp hyT).1
    have hsrc' : e.val.1=x.val := congrArg Subtype.val hsrc
    have hne : x.val ≠ y.val := by
      intro hh
      have hd := (planar_target_iff P s e y).mp hyT'
      rw [hsrc',hh,dist_self] at hd
      exact (index_radius_pos P s e).ne hd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hxD,rfl⟩,
      Finset.mem_image.mpr ⟨y,hyD,rfl⟩⟩,hne,?_⟩
    rw [planeSubset_card]
    have hc := Finset.card_le_card (restricted_targets_subset P s D e y hyT')
    rw [Finset.card_image_of_injective _ Subtype.val_injective,hsrc'] at hc
    exact hsz.trans (by exact_mod_cast hc)
  · simp at hyT

/-- The exact finite counting step underlying both uniform subset estimates
    for the rich-pair graph. Each ordered pair is counted only once. -/
theorem heavySubset_count (P : Finset Plane) (s K lam r : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hK : (D.card : ℝ)^r ≤ lam*K) :
    (∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
      then ((planarFibers P s).size D e : ℝ) else 0) ≤
      (richPairs (planeSubset P D) r).card := by
  rw [← (planarFibers P s).retained_card]
  suffices h : (((planarFibers P s).retained D (heavyFiber P s K lam C D)).edgeSet (-1) D).card ≤
      (richPairs (planeSubset P D) r).card by exact_mod_cast h
  rw [← Finset.card_image_of_injective _ (subtype_pair_injective P)]
  apply Finset.card_le_card
  intro z hz
  obtain ⟨xy,he,rfl⟩ := Finset.mem_image.mp hz
  exact heavySubset_edge_rich P s K lam r C D hlam hK xy.1 xy.2 (Finset.mem_filter.mp he).2

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

lemma F_bdd (s : ℝ) : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => F n s) :=
  isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => F_le_one n s))
lemma F_cobdd (s : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => F n s) :=
  isCoboundedUnder_le_of_le atTop (fun n => F_nonneg n s)

lemma Theta_nonneg (s : ℝ) : 0 ≤ Theta s := by
  have hh := limsup_le_limsup (f:=atTop) (u:=fun _ : ℕ => (0:ℝ)) (v:=fun n => F n s)
    (Eventually.of_forall (fun n => F_nonneg n s)) (isCoboundedUnder_le_of_le atTop (fun _ => le_refl (0:ℝ))) (F_bdd s)
  change 0 ≤ limsup (fun n : ℕ => F n s) atTop
  simpa only [limsup_const] using hh

lemma Theta_antitone : Antitone Theta := by
  intro s t hst
  exact limsup_le_limsup (Eventually.of_forall (fun n => F_antitone n hst)) (F_cobdd t) (F_bdd s)

lemma Theta_eq_zero_of_one_le {s : ℝ} (hs : 1 ≤ s) : Theta s=0 := by
  simp [Theta,F_eq_zero_of_one_le _ hs]

lemma tendsto_F_of_Theta_zero {s : ℝ} (hs : Theta s=0) : Tendsto (fun n : ℕ => F n s) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (F_nonneg n s))
  · intro a ha
    exact eventually_lt_of_limsup_lt (by change Theta s < a; simpa [hs] using ha) (F_bdd s)

lemma positive_exponents_bdd : BddAbove {s : ℝ | 0 < s ∧ 0 < Theta s} := by
  refine ⟨1,?_⟩
  intro s hs
  by_contra hn
  have hz := Theta_eq_zero_of_one_le (le_of_lt (lt_of_not_ge hn))
  linarith [hs.2]

lemma failed_main_nonempty (h : ¬ MainStatement) : {s : ℝ | 0 < s ∧ 0 < Theta s}.Nonempty := by
  by_contra hn
  apply h
  intro s hs
  apply tendsto_F_of_Theta_zero
  have hnp : ¬0 < Theta s := fun hp => hn ⟨s,hs,hp⟩
  exact le_antisymm (le_of_not_gt hnp) (Theta_nonneg s)

lemma critical_pos (h : ¬ MainStatement) : 0 < criticalExponent := by
  obtain ⟨s,hs,hθ⟩ := failed_main_nonempty h
  exact hs.trans_le (le_csSup positive_exponents_bdd ⟨hs,hθ⟩)

lemma critical_le_one (h : ¬ MainStatement) : criticalExponent ≤ 1 :=
  csSup_le (failed_main_nonempty h) (fun s hs => by
    by_contra hn
    have hz := Theta_eq_zero_of_one_le (le_of_lt (lt_of_not_ge hn))
    linarith [hs.2])

lemma Theta_pos_below_critical (h : ¬ MainStatement) {s : ℝ} (hs : s < criticalExponent) : 0 < Theta s := by
  obtain ⟨t,ht,hst⟩ := exists_lt_of_lt_csSup (failed_main_nonempty h) hs
  exact ht.2.trans_le (Theta_antitone (le_of_lt hst))

lemma Theta_zero_above_critical (h : ¬ MainStatement) {s : ℝ} (hs : criticalExponent < s) : Theta s=0 := by
  apply le_antisymm _ (Theta_nonneg s)
  by_contra hn
  have hp : 0 < Theta s := lt_of_not_ge hn
  have hs0 := (critical_pos h).trans hs
  have hh : s ≤ criticalExponent := le_csSup positive_exponents_bdd ⟨hs0,hp⟩
  linarith

/-- A fixed exponent regime obtained from failure of the uniform multiplicity limit. -/

theorem extremal_parameters (h : ¬ MainStatement) :
    ∃ c s γ : ℝ, 0 < c ∧ c < criticalExponent/3 ∧
      max c ((1-c)*criticalExponent) < s ∧ s < criticalExponent ∧
      c < γ ∧ γ < s ∧ ContinuousAt Theta s ∧ 0 < Theta s := by
  let c := criticalExponent/4
  have hp := critical_pos h
  have h1 := critical_le_one h
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hc3 : c < criticalExponent/3 := by dsimp [c]; linarith
  have hcm : c < criticalExponent := by dsimp [c]; linarith
  have hm : (1-c)*criticalExponent < criticalExponent := by nlinarith
  have hmax : max c ((1-c)*criticalExponent) < criticalExponent := max_lt hcm hm
  have hd := (Theta_antitone.countable_not_continuousAt).dense_compl ℝ
  obtain ⟨s,hs,hr⟩ := hd.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hmax)
  have hcs : c < s := (le_max_left _ _).trans_lt hr.1
  refine ⟨c,s,(c+s)/2,hc0,hc3,hr.1,hr.2,?_,?_,?_,Theta_pos_below_critical h hr.2⟩
  · linarith
  · linarith
  · simpa only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_not] using hs

lemma extremal_subsequence (s : ℝ) :
    ∃ N : ℕ → ℕ, Tendsto N atTop atTop ∧ Tendsto (fun i => F (N i) s) atTop (𝓝 (Theta s)) := by
  obtain ⟨N,hN,hT⟩ := exists_seq_tendsto_limsup (F_cobdd s) (F_bdd s)
  exact ⟨N,hT,hN⟩

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

lemma eventual_power_below_cutoff {s r : ℝ} (hrs : r < s) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)^r ≤ cutoff s N := by
  have ho := (isLittleO_log_rpow_atTop (sub_pos.mpr hrs)).bound (show (0:ℝ)<1 by norm_num)
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually ho,hn.eventually (eventually_gt_atTop 1)] with N hN hp
  have hlog : 0 < Real.log N := Real.log_pos hp
  have hpow : 0 ≤ (N : ℝ)^(s-r) := Real.rpow_nonneg (by linarith) _
  simp only [Real.norm_eq_abs,abs_of_nonneg hlog.le,abs_of_nonneg hpow,one_mul] at hN
  unfold cutoff
  apply (le_div_iff₀ hlog).mpr
  calc
    (N : ℝ)^r*Real.log N ≤ (N : ℝ)^r*(N : ℝ)^(s-r) :=
      mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg (by linarith) _)
    _ = (N : ℝ)^s := by rw [← Real.rpow_add (by linarith : (0:ℝ)<N)]; congr 1; ring

lemma eventual_cutoff_loss (s η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, 0 ≤ cutoff s N ∧ cutoff s N < (N : ℝ)^s ∧
      cutoff s N ≤ (η/8)*(N : ℝ)^s := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  filter_upwards [hl.eventually (eventually_gt_atTop (max 1 (8/η))),
    hn.eventually (eventually_gt_atTop 1)] with N hlog hN
  have hlog1 : 1 < Real.log N := (le_max_left _ _).trans_lt hlog
  have hlogη : 8/η < Real.log N := (le_max_right _ _).trans_lt hlog
  have hp : 0 < (N : ℝ)^s := Real.rpow_pos_of_pos (by linarith) _
  have hi : (1:ℝ)/Real.log N ≤ η/8 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log N)).mpr
    have hh : 8 < Real.log N*η := (div_lt_iff₀ hη).mp hlogη
    nlinarith
  refine ⟨div_nonneg hp.le (by linarith),?_,?_⟩
  · exact (div_lt_iff₀ (by linarith : 0 < Real.log N)).mpr (by nlinarith)
  · unfold cutoff
    calc
      (N : ℝ)^s/Real.log N = (1/Real.log N)*(N : ℝ)^s := by ring
      _ ≤ (η/8)*(N : ℝ)^s := mul_le_mul_of_nonneg_right hi hp.le

lemma continuous_left_tail {s γ ε : ℝ} (hγ : γ < s) (hε : 0 < ε)
    (hs : ContinuousAt Theta s) :
    ∃ r : ℝ, γ < r ∧ r < s ∧ ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m → F m r ≤ Theta s+ε := by
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hs (ε/2) (by linarith)
  obtain ⟨r,hrlo,hrhi⟩ := exists_between (show max γ (s-δ) < s by exact max_lt hγ (by linarith))
  have hγr : γ < r := (le_max_left _ _).trans_lt hrlo
  have hdist : dist r s < δ := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hrhi)]
    have hh := (le_max_right γ (s-δ)).trans_lt hrlo
    linarith
  have ht : Theta r < Theta s+ε := by
    have hh := (abs_lt.mp (show |Theta r-Theta s| < ε/2 from by simpa only [Real.dist_eq] using hcont hdist)).2
    linarith
  obtain ⟨m₁,hm⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt ht (F_bdd r))
  exact ⟨r,hγr,hrhi,m₁,fun m hm₁ => (hm m hm₁).le⟩

lemma half_boundary (N : ℕ) (hN : 4 ≤ N) :
    let m₀ := (N+1)/2
    2 ≤ m₀ ∧ m₀ < N ∧
      (m₀ : ℝ)*((m₀ : ℝ)-1) ≤ (N : ℝ)*((N : ℝ)-1)/2 := by
  dsimp
  have hm : 2 ≤ (N+1)/2 := by omega
  have hlt : (N+1)/2 < N := by omega
  refine ⟨hm,hlt,?_⟩
  have h2 : 2*((N+1)/2) ≤ N+1 := by omega
  have h2R : (2:ℝ)*((N+1)/2 : ℕ) ≤ (N : ℝ)+1 := by exact_mod_cast h2
  have hNR : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hmR : (2:ℝ) ≤ ((N+1)/2 : ℕ) := by exact_mod_cast hm
  nlinarith

/-- Actual core configurations at arbitrarily small density error and arbitrarily
    large cardinality. No field or position assumptions are introduced. -/
theorem arbitrarily_large_core {s γ : ℝ} (hγ : 0 < γ) (hγs : γ < s)
    (hs : ContinuousAt Theta s) (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∃ (P : Finset Plane) (C : Finset P), M < C.card ∧
      (P.card+1)/2 < C.card ∧ (C.card : ℝ)^γ ≤ cutoff s P.card ∧
      (Theta s-η)*(C.card : ℝ)*((C.card : ℝ)-1) ≤ ((planarFibers P s).edgeSet (cutoff s P.card) C).card ∧
      (((planarFibers P s).edgeSet (cutoff s P.card) C).card : ℝ) ≤
        (Theta s+η/8)*(C.card : ℝ)*((C.card : ℝ)-1) ∧
      (∀ x ∈ C, 2*(Theta s-η)*((C.card : ℝ)-1) ≤
        (planarFibers P s).degree (cutoff s P.card) C x) := by
  obtain ⟨r,hγr,hrs,m₁,hm₁⟩ := continuous_left_tail hγs (show 0 < η/8 by positivity) hs
  obtain ⟨N,hN,hF⟩ := extremal_subsequence s
  have hlarge : ∀ᶠ i in atTop, 4+2*M+2*m₁ ≤ N i := hN.eventually (eventually_ge_atTop _)
  have happrox : ∀ᶠ i in atTop, Theta s-η/8 ≤ F (N i) s :=
    (hF.eventually_const_lt (by linarith : Theta s-η/8 < Theta s)).mono (fun _ h => h.le)
  obtain ⟨i,hi,hcut,hpow,hinit⟩ := (hlarge.and ((hN.eventually (eventual_cutoff_loss s η hη)).and
    ((hN.eventually (eventual_power_below_cutoff hrs)).and happrox))).exists
  obtain ⟨P,hP,hPF⟩ := F_attained (N i) (by omega) s
  have hn : 4 ≤ P.card := by omega
  obtain ⟨hm0,hm,hbd⟩ := half_boundary P.card hn
  have hm1 : m₁ ≤ (P.card+1)/2 := by omega
  have hη8 := hcut.2.2
  have hpowP : (P.card : ℝ)^r ≤ cutoff s P.card := by simpa [hP] using hpow
  have hthreshold : ∀ m : ℕ, (P.card+1)/2 ≤ m → m ≤ P.card → (m : ℝ)^r ≤ cutoff s P.card := by
    intro m _ hmP
    exact (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmP) (by linarith)).trans hpowP
  obtain ⟨C,hC,hlo,hhi,hdeg⟩ := finite_extremal_core P s r (cutoff s P.card) (Theta s) η ((P.card+1)/2)
    (by omega) hm0 hm hη (by simpa [hP] using hcut.1) (by simpa [hP] using hcut.2.1)
    (by simpa [hP] using hη8) (by simpa [hPF] using hinit) hbd hthreshold
    (fun m hm _ => hm₁ m (hm1.trans hm))
  have hCn : C.card ≤ P.card := by simpa using Finset.card_le_univ C
  have hCpos : (1:ℝ) ≤ C.card := by exact_mod_cast (show 1 ≤ C.card by omega)
  refine ⟨P,C,by omega,hC,?_,hlo,hhi,hdeg⟩
  exact (Real.rpow_le_rpow_of_exponent_le hCpos hγr.le).trans
    (hthreshold C.card hC.le hCn)

end WeakPinned

namespace WeakPinned
open scoped BigOperators

lemma restricted_size_lt_card (P : Finset Plane) (s : ℝ) (D : Finset P)
    (e : fiberIndices P s) (hs : (planarFibers P s).source e ∈ D) :
    (planarFibers P s).size D e < D.card := by
  have hh : (planarFibers P s).targets e ∩ D ⊆ D.erase ((planarFibers P s).source e) := by
    intro y hy
    obtain ⟨hyT,hyD⟩ := Finset.mem_inter.mp hy
    refine Finset.mem_erase.mpr ⟨?_,hyD⟩
    intro he
    subst y
    exact (planarFibers P s).no_loop e hyT
  have hc := Finset.card_le_card hh
  rw [Finset.card_erase_of_mem hs] at hc
  have hp := Finset.card_pos.mpr ⟨_,hs⟩
  change (planarFibers P s).size D e ≤ D.card-1 at hc
  omega

lemma heavySubset_zero (P : Finset Plane) (s K lam : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hsmall : (D.card : ℝ) ≤ lam*K) :
    (∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
      then ((planarFibers P s).size D e : ℝ) else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro e _
  rw [ite_eq_right]
  rintro ⟨⟨ha,hh⟩,hs⟩
  have hk := mul_le_mul_of_nonneg_left (le_of_lt ha.2) hlam
  have hm : ((planarFibers P s).size D e : ℝ) < D.card := by
    exact_mod_cast restricted_size_lt_card P s D e hs
  linarith

/-- A uniform extremal bound valid even for tiny subsets: their contribution
    is zero, rather than an uncontrolled diagonal error. -/
theorem heavySubset_uniform (P : Finset Plane) (s K lam r B : ℝ) (C D : Finset P)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (m₁ : ℕ) (hm1 : 2 ≤ m₁)
    (hT : (m₁ : ℝ) ≤ lam*K)
    (hthreshold : (D.card : ℝ)^r ≤ lam*K)
    (hext : ∀ m : ℕ, m₁ ≤ m → m ≤ P.card → F m r ≤ B) :
    (∑ e, if heavyFiber P s K lam C D e ∧ (planarFibers P s).source e ∈ D
      then ((planarFibers P s).size D e : ℝ) else 0) ≤
      B*(D.card : ℝ)*((D.card : ℝ)-1) := by
  by_cases hm : D.card < m₁
  · have hDm : (D.card : ℝ) ≤ m₁ := by exact_mod_cast hm.le
    rw [heavySubset_zero P s K lam C D hlam (hDm.trans hT)]
    by_cases hzero : D.card=0
    · simp [hzero]
    · have hh : (1:ℝ) ≤ D.card := by exact_mod_cast (show 1 ≤ D.card by omega)
      positivity
  · have hmge : m₁ ≤ D.card := by omega
    have hDn : D.card ≤ P.card := by simpa using Finset.card_le_univ D
    have hh : (2:ℝ) ≤ D.card := by exact_mod_cast hm1.trans hmge
    have hp : 0 < (D.card : ℝ)*((D.card : ℝ)-1) := by nlinarith
    have hf := fraction_le_F (planeSubset P D) r (by simpa [planeSubset_card] using hm1.trans hmge)
    rw [pairFraction,planeSubset_card,div_le_iff₀ hp] at hf
    have hc := heavySubset_count P s K lam r C D hlam hthreshold
    have he := mul_le_mul_of_nonneg_right (hext D.card hmge hDn) hp.le
    nlinarith

lemma eventual_power_below_logsquare {s r : ℝ} (hrs : r < s) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ)^r ≤ cutoff s N / Real.log N := by
  have ho := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (sub_pos.mpr hrs)).bound (show (0:ℝ)<1 by norm_num)
  have hn : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually ho,hn.eventually (Filter.eventually_gt_atTop 1)] with N hN hp
  have hlog : 0 < Real.log N := Real.log_pos hp
  have hpow : 0 ≤ (N : ℝ)^(s-r) := Real.rpow_nonneg (by linarith) _
  simp only [Real.norm_eq_abs,Real.rpow_two,one_mul,abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),abs_of_nonneg hpow] at hN
  unfold cutoff
  rw [div_div]
  apply (le_div_iff₀ (mul_pos hlog hlog)).mpr
  calc
    (N : ℝ)^r*(Real.log N*Real.log N) ≤ (N : ℝ)^r*(N : ℝ)^(s-r) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
      nlinarith
    _ = (N : ℝ)^s := by rw [← Real.rpow_add (by linarith : (0:ℝ)<N)]; congr 1; ring

end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology BigOperators

lemma choose_above_critical (hfail : ¬ MainStatement) {s c : ℝ}
    (hc : c < 1) (hsc : (1-c)*criticalExponent < s) :
    ∃ t : ℝ, criticalExponent < t ∧ (1-c)*t < s ∧ 0 < t := by
  have hp : 0 < 1-c := by linarith
  have hb : criticalExponent < s/(1-c) := (lt_div_iff₀ hp).mpr (by nlinarith)
  obtain ⟨t,ht,hst⟩ := exists_between hb
  refine ⟨t,ht,?_,(critical_pos hfail).trans ht⟩
  have hh := (lt_div_iff₀ hp).mp hst
  nlinarith

lemma log_cutoff_comparison {N n : ℕ} {s : ℝ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    cutoff s N / Real.log N ≤ (1/Real.log n)*cutoff s N := by
  have hnr : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hlog := Real.log_pos hnr
  have hlogs : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) (by exact_mod_cast hnN)
  calc
    cutoff s N / Real.log N ≤ cutoff s N / Real.log n := by
      apply div_le_div_of_nonneg_left _ hlog hlogs
      exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hlog.le.trans hlogs)
    _ = (1/Real.log n)*cutoff s N := by ring

/-- Uniformity of both subset estimates is obtained before passing to any
    arithmetic model. Tiny subsets are treated exactly, with no diagonal error. -/
theorem arbitrarily_large_prepared (hfail : ¬ MainStatement) {s γ c : ℝ}
    (hγ : 0 < γ) (hγs : γ < s) (_hc : 0 < c) (hc1 : c < 1)
    (hsc : (1-c)*criticalExponent < s) (hs : ContinuousAt Theta s)
    (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∃ (P : Finset Plane) (C : Finset P), M < C.card ∧ PreparedCore s γ c η P C := by
  obtain ⟨r,hγr,hrs,m₁,hm₁⟩ := continuous_left_tail hγs hη hs
  obtain ⟨t,ht,hst,ht0⟩ := choose_above_critical hfail hc1 hsc
  obtain ⟨m₂,hm₂⟩ := eventually_atTop.mp
    ((tendsto_F_of_Theta_zero (Theta_zero_above_critical hfail ht)).eventually_lt_const hη)
  let m := max 2 (max m₁ m₂)
  have hm2 : 2 ≤ m := le_max_left _ _
  have hmr : m₁ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmt : m₂ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hr0 : 0 < r := hγ.trans hγr
  have hbig : ∀ᶠ N : ℕ in atTop, (m : ℝ) ≤ (N : ℝ)^r :=
    ((tendsto_rpow_atTop hr0).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (hbig.and ((eventual_power_below_logsquare hrs).and (eventual_power_below_logsquare hst)))
  obtain ⟨P,C,hC,hhalf,hpow,hlo,hhi,hdeg⟩ :=
    arbitrarily_large_core hγ hγs hs η hη (max (max M N₀) 2)
  have hn : 2 ≤ C.card := by omega
  have hCn : C.card ≤ P.card := by simpa using Finset.card_le_univ C
  have hg : N₀ ≤ P.card := by omega
  obtain ⟨hbigP,hpr,hpt⟩ := hN₀ P.card hg
  have hcomp := log_cutoff_comparison (s:=s) hn hCn
  have hlam : 0 ≤ 1/Real.log (C.card : ℝ) := by
    have hh := Real.log_pos (show (1:ℝ)<C.card by exact_mod_cast (show 1<C.card by omega))
    positivity
  have hT : (m : ℝ) ≤ (1/Real.log (C.card : ℝ))*cutoff s P.card := hbigP.trans (hpr.trans hcomp)
  refine ⟨P,C,by omega,hn,hhalf,hpow,hlo,hhi,hdeg,?_,?_⟩
  · intro D
    have hDn : D.card ≤ P.card := by simpa using Finset.card_le_univ D
    have hDP : (D.card : ℝ)^r ≤ (P.card : ℝ)^r :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hDn) hr0.le
    exact heavySubset_uniform P s (cutoff s P.card) (1/Real.log C.card) r (Theta s+η) C D hlam
      (by linarith [Theta_nonneg s]) m hm2 hT (hDP.trans (hpr.trans hcomp))
      (fun j hj _ => hm₁ j (hmr.trans hj))
  · intro D hD
    have hDP : (D.card : ℝ)^t ≤ (P.card : ℝ)^((1-c)*t) := by
      calc
        (D.card : ℝ)^t ≤ ((C.card : ℝ)^(1-c))^t :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hD ht0.le
        _ = (C.card : ℝ)^((1-c)*t) := (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm
        _ ≤ (P.card : ℝ)^((1-c)*t) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hCn) (by positivity)
    exact heavySubset_uniform P s (cutoff s P.card) (1/Real.log C.card) t η C D hlam hη.le
      m hm2 hT (hDP.trans (hpt.trans hcomp)) (fun j hj _ => (hm₂ j (hmt.trans hj)).le)

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.IncomingFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma onCore_targets (K : ℝ) (C : Finset V) (e : G.Active K C) :
    ((G.onCore K C).targets e).image Subtype.val=G.targets e.val ∩ C := by
  ext y
  simp only [onCore,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter]
  constructor
  · rintro ⟨z,hz,rfl⟩; exact ⟨hz,z.property⟩
  · rintro ⟨hy,hC⟩; exact ⟨⟨y,hC⟩,hy,rfl⟩

omit [Fintype V] [Fintype I] in
lemma onCore_size (K : ℝ) (C : Finset V) (e : G.Active K C) :
    ((G.onCore K C).targets e).card=G.size C e.val := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,G.onCore_targets,size]

omit [Fintype I] in
omit [Fintype V] in
lemma onCore_edge (K : ℝ) (C : Finset V) (x y : C) :
    (G.onCore K C).edge (-1) Finset.univ x y ↔ G.edge K C x.val y.val := by
  simp only [edge,active_univ_neg_one,true_and,Finset.mem_inter,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨e,hs,hy⟩
    refine ⟨e.val,e.property,congrArg Subtype.val hs,?_⟩
    exact ⟨(Finset.mem_filter.mp hy).2,y.property⟩
  · rintro ⟨e,ha,hs,hy⟩
    exact ⟨⟨e,ha⟩,Subtype.ext hs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy.1⟩⟩

omit [Fintype I] in
lemma onCore_edges_image (K : ℝ) (C : Finset V) :
    ((G.onCore K C).edges).image (fun xy : C × C => (xy.1.val,xy.2.val))=G.edgeSet K C := by
  ext xy
  simp only [edges,edgeSet,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨x,y⟩,hxy,rfl⟩
    exact (G.onCore_edge K C x y).mp hxy
  · intro hxy
    obtain ⟨e,ha,hs,hy⟩ := hxy
    have hxC : xy.1 ∈ C := hs ▸ ha.1
    have hyC : xy.2 ∈ C := (Finset.mem_inter.mp hy).2
    refine ⟨(⟨xy.1,hxC⟩,⟨xy.2,hyC⟩),?_,rfl⟩
    exact (G.onCore_edge K C _ _).mpr ⟨e,ha,hs,hy⟩

omit [Fintype I] in
lemma onCore_card (K : ℝ) (C : Finset V) :
    ((G.onCore K C).edges).card=(G.edgeSet K C).card := by
  rw [← G.onCore_edges_image]
  apply (Finset.card_image_of_injective _ _).symm
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

omit [Fintype I] in
lemma onCore_degree (K : ℝ) (C : Finset V) (x : C) :
    (G.onCore K C).degree (-1) Finset.univ x=G.degree K C x.val := by
  simp only [degree,G.onCore_edge]
  have hsum (f : V → ℝ) (hf : ∀ y, y ∉ C → f y=0) : (∑ y : C, f y.val)=∑ y, f y := by
    rw [Finset.sum_coe_sort]
    apply Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => hf y hy)
  simp only [← Finset.sum_boole,← Finset.sum_add_distrib]
  apply hsum (fun y => (if G.edge K C x.val y then 1 else 0)+(if G.edge K C y x.val then 1 else 0))
  intro y hy
  have h1 : ¬ G.edge K C x.val y := by
    rintro ⟨e,ha,hs,he⟩
    exact hy (Finset.mem_inter.mp he).2
  have h2 : ¬ G.edge K C y x.val := by
    rintro ⟨e,ha,hs,he⟩
    exact hy (hs ▸ ha.1)
  simp [h1,h2]

end WeakPinned.Core.Fibers

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma onCore_size_subset (K : ℝ) (C : Finset V) (D : Finset C) (e : G.Active K C) :
    (G.onCore K C).size D e=G.size (D.image Subtype.val) e.val := by
  unfold size
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext y
  simp only [Finset.mem_image,Finset.mem_inter]
  constructor
  · rintro ⟨z,⟨hz,hd⟩,rfl⟩
    exact ⟨(Finset.mem_filter.mp hz).2,⟨z,hd,rfl⟩⟩
  · rintro ⟨hy,z,hz,rfl⟩
    exact ⟨z,⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,hz⟩,rfl⟩

omit [Fintype V] in
lemma onCore_heavyCount (K lam : ℝ) (C : Finset V) (D : Finset C) :
    (G.onCore K C).heavyCount lam D =
      ∑ e, if G.active K C e ∧ lam*(G.size C e : ℝ) ≤ (G.size (D.image Subtype.val) e : ℝ) ∧
        G.source e ∈ D.image Subtype.val then (G.size (D.image Subtype.val) e : ℝ) else 0 := by
  classical
  unfold heavyCount
  simp_rw [G.onCore_size_subset,G.onCore_size]
  have hs (e : G.Active K C) : (G.onCore K C).source e ∈ D ↔ G.source e.val ∈ D.image Subtype.val := by
    constructor
    · intro h; exact Finset.mem_image.mpr ⟨_,h,rfl⟩
    · intro h
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
      have hh : y=(G.onCore K C).source e := Subtype.ext he
      simpa only [hh] using hy
  simp_rw [hs]
  rw [← Finset.sum_subtype (p:=G.active K C) (Finset.univ.filter (G.active K C)) (by simp)
    (fun e => if lam*(G.size C e : ℝ) ≤ (G.size (D.image Subtype.val) e : ℝ) ∧
      G.source e ∈ D.image Subtype.val then (G.size (D.image Subtype.val) e : ℝ) else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.active K C e <;> simp [he]

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators
open WeakPinned.Core

lemma coreGraph_heavy (P : Finset Plane) (s lam : ℝ) (C : Finset P) (D : Finset C) :
    (coreGraph P s C).heavyCount lam D = heavyCount P s (cutoff s P.card) lam C (D.image Subtype.val) := by
  rw [(planarFibers P s).onCore_heavyCount]
  unfold heavyCount heavyFiber
  apply Finset.sum_congr rfl
  intro e _
  simp only [and_assoc]

lemma PreparedCore.graph {s γ c η : ℝ} {P : Finset Plane} {C : Finset P}
    (h : PreparedCore s γ c η P C) :
    PreparedGraph C ((planarFibers P s).Active (cutoff s P.card) C) (coreGraph P s C) (Theta s) γ c η := by
  have hn : Fintype.card C=C.card := Fintype.card_coe C
  have he : (coreGraph P s C).edgeCount = ((planarFibers P s).edgeSet (cutoff s P.card) C).card := by
    unfold Core.Fibers.edgeCount
    rw [(planarFibers P s).onCore_card]
  refine ⟨by simpa only [hn] using h.card_two,?_,?_,?_,?_,?_,?_⟩
  · simpa only [he,hn] using h.lower
  · simpa only [he,hn] using h.upper
  · intro x
    simpa only [hn,(planarFibers P s).onCore_degree] using h.degree x.val x.property
  · intro e
    rw [(planarFibers P s).onCore_size,hn]
    exact h.large_fiber.trans_lt e.property.2
  · intro D
    rw [hn,coreGraph_heavy]
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h.subset (D.image Subtype.val)
  · intro D hD
    rw [hn,coreGraph_heavy]
    have hc : (D.image Subtype.val).card=D.card := Finset.card_image_of_injective _ Subtype.val_injective
    simpa only [hc] using h.small (D.image Subtype.val) (by simpa only [hc,hn] using hD)

/-- Actual arbitrarily large real planar graphs, with all uniform subset
bounds simultaneously. No graph condition is added to the main hypothesis. -/
theorem arbitrarily_large_graph (hfail : ¬ MainStatement) {s γ c : ℝ}
    (hγ : 0<γ) (hγs : γ<s) (hc : 0<c) (hc1 : c<1)
    (hsc : (1-c)*criticalExponent<s) (hs : ContinuousAt Theta s)
    (η : ℝ) (hη : 0<η) (M : ℕ) :
    ∃ (P : Finset Plane) (C : Finset P), M<C.card ∧
      PreparedGraph C ((planarFibers P s).Active (cutoff s P.card) C) (coreGraph P s C) (Theta s) γ c η := by
  obtain ⟨P,C,hM,hC⟩ := arbitrarily_large_prepared hfail hγ hγs hc hc1 hsc hs η hη M
  exact ⟨P,C,hM,hC.graph⟩

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
noncomputable section
namespace WeakPinned
open Filter
open scoped Topology BigOperators

/-- Diagonalized extraction of genuine configurations. The errors tend to zero
and vertex numbers tend to infinity. -/
theorem graph_sequence_of_failure (hfail : ¬ MainStatement) :
    ∃ c s γ : ℝ, 0<c ∧ c<γ ∧ γ<s ∧ s<1 ∧ 0<Theta s ∧
      ∃ (P : ℕ → Finset Plane) (C : ∀ j, Finset (P j)),
        (∀ j, j<(C j).card) ∧
        ∀ j, PreparedGraph (C j) ((planarFibers (P j) s).Active (cutoff s (P j).card) (C j))
          (coreGraph (P j) s (C j)) (Theta s) γ c (Theta s/(j+2)) := by
  classical
  obtain ⟨c,s,γ,hc,hc3,hcs,hs,hcγ,hγs,hct,hθ⟩ := extremal_parameters hfail
  have hcrit := critical_le_one hfail
  have hsc : (1-c)*criticalExponent<s := (le_max_right _ _).trans_lt hcs
  have hc1 : c<1 := by linarith
  have hγ0 : 0<γ := hc.trans hcγ
  have hex (j : ℕ) := arbitrarily_large_graph hfail hγ0 hγs hc hc1 hsc hct
    (Theta s/(j+2)) (div_pos hθ (by positivity)) j
  choose P C hC hG using hex
  exact ⟨c,s,γ,hc,hcγ,hγs,hs.trans_le hcrit,hθ,P,C,hC,hG⟩

lemma graph_card_tendsto {P : ℕ → Finset Plane} {C : ∀ j, Finset (P j)}
    (hC : ∀ j, j<(C j).card) : Tendsto (fun j => (C j).card) atTop atTop :=
  tendsto_atTop_mono (fun j => (hC j).le) tendsto_id

lemma graph_error_tendsto (θ : ℝ) : Tendsto (fun j : ℕ => θ/((j:ℝ)+2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun j : ℕ => (j:ℝ)+2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop ht

end WeakPinned

/- Algebraic representation of the finite rational polynomial pattern of a
   real configuration in a number field. -/

noncomputable section

namespace WeakPinned.Transfer
open MvPolynomial

/-- A system of rational polynomial equations with a complex solution has an
    algebraic solution. No finite set assumption on the equations is needed. -/
theorem equations {ι : Type u1} [Finite ι]
    (S : Set (MvPolynomial ι ℚ)) (x : ι → ℂ)
    (hx : ∀ p ∈ S, aeval x p = 0) :
    ∃ y : ι → AlgebraicClosure ℚ, ∀ p ∈ S, aeval y p = 0 := by
  let I : Ideal (MvPolynomial ι ℚ) := vanishingIdeal ℚ {x}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial ι ℚ) ∈ I := by rw [h]; trivial
    have hz := (mem_vanishingIdeal_singleton_iff x 1).mp h1
    simp at hz
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨y, hy⟩ := eq_vanishingIdeal_singleton_of_isMaximal (AlgebraicClosure ℚ) hM
  refine ⟨y, fun p hp => ?_⟩
  apply (mem_vanishingIdeal_singleton_iff y p).mp
  rw [← hy]
  exact hIM ((mem_vanishingIdeal_singleton_iff x p).mpr (hx p hp))

/-- Simultaneous equations and finitely many inequations transfer to algebraic
    coordinates. The inverse-variable equation enforces every inequation. -/
theorem equations_and_inequations {ι : Type u2} [Finite ι]
    (S : Set (MvPolynomial ι ℚ)) (T : Finset (MvPolynomial ι ℚ)) (x : ι → ℂ)
    (hx : ∀ p ∈ S, aeval x p = 0) (hT : ∀ p ∈ T, aeval x p ≠ 0) :
    ∃ y : ι → AlgebraicClosure ℚ,
      (∀ p ∈ S, aeval y p = 0) ∧ (∀ p ∈ T, aeval y p ≠ 0) := by
  let q : MvPolynomial ι ℚ := ∏ p ∈ T, p
  let r : MvPolynomial (Option ι) ℚ := X none * rename some q - 1
  let S' : Set (MvPolynomial (Option ι) ℚ) := (rename some) '' S ∪ {r}
  let x' : Option ι → ℂ := fun j => j.elim (aeval x q)⁻¹ x
  have hq : aeval x q ≠ 0 := by
    simpa [q] using Finset.prod_ne_zero_iff.mpr hT
  have hl (p : MvPolynomial ι ℚ) : aeval x' (rename some p) = aeval x p := by
    simp [aeval_rename, Function.comp_def, x']
  have hx' : ∀ p ∈ S', aeval x' p = 0 := by
    intro p hp
    rcases hp with ⟨p, hp, rfl⟩ | rfl
    · rw [hl]
      exact hx p hp
    · simp [r, hl, x', hq]
  obtain ⟨y', hy'⟩ := equations S' x' hx'
  let y : ι → AlgebraicClosure ℚ := fun i => y' (some i)
  have hl' (p : MvPolynomial ι ℚ) : aeval y' (rename some p) = aeval y p := by
    simp [aeval_rename, Function.comp_def, y]
  refine ⟨y, ?_, ?_⟩
  · intro p hp
    rw [← hl']
    exact hy' _ (Or.inl ⟨p, hp, rfl⟩)
  · have hr := hy' r (Or.inr rfl)
    have hq' : aeval y q ≠ 0 := by
      intro hz
      simp [r, hl', hz] at hr
    have hprod : (∏ p ∈ T, aeval y p) ≠ 0 := by simpa [q] using hq'
    exact Finset.prod_ne_zero_iff.mp hprod

/-- The algebraic realization lies in a single number field generated by its
    finitely many coordinates. The field is not fixed in advance. -/
theorem numberField_pattern {ι : Type u3} [Finite ι]
    (S : Set (MvPolynomial ι ℚ)) (T : Finset (MvPolynomial ι ℚ)) (x : ι → ℂ)
    (hx : ∀ p ∈ S, aeval x p = 0) (hT : ∀ p ∈ T, aeval x p ≠ 0) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
      ∃ y : ι → K, (∀ p ∈ S, aeval y p = 0) ∧ (∀ p ∈ T, aeval y p ≠ 0) := by
  obtain ⟨y, hy, hTy⟩ := equations_and_inequations S T x hx hT
  let K := IntermediateField.adjoin ℚ (Set.range y)
  have : Finite (Set.range y) := (Set.finite_range y).to_subtype
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isIntegral
  have hfd : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  have hnf : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  let z : ι → K := fun i => ⟨y i, IntermediateField.subset_adjoin ℚ (Set.range y) ⟨i, rfl⟩⟩
  have he (p : MvPolynomial ι ℚ) : K.val (aeval z p) = aeval y p :=
    comp_aeval_apply z K.val p
  refine ⟨K, hnf, z, ?_, ?_⟩
  · intro p hp
    apply K.val.injective
    change K.val (aeval z p) = K.val 0
    rw [he, map_zero, hy p hp]
  · intro p hp hz
    apply hTy p hp
    rw [← he, hz, map_zero]

/-- Preservation of an arbitrary finite zero-pattern, simultaneously, in one
    number field. In particular this preserves all selected equalities exactly. -/
theorem numberField_zero_pattern {ι : Type u4} [Finite ι]
    (T : Finset (MvPolynomial ι ℚ)) (x : ι → ℂ) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
      ∃ y : ι → K, ∀ p ∈ T, aeval y p = 0 ↔ aeval x p = 0 := by
  classical
  let S : Set (MvPolynomial ι ℚ) := {p | p ∈ T ∧ aeval x p = 0}
  let U := T.filter (fun p => aeval x p ≠ 0)
  obtain ⟨K, hK, y, hy, hUy⟩ := numberField_pattern S U x
    (fun _ hp => hp.2) (fun p hp => (Finset.mem_filter.mp hp).2)
  refine ⟨K, hK, y, fun p hp => ⟨?_, ?_⟩⟩
  · intro h
    by_contra h'
    exact hUy p (Finset.mem_filter.mpr ⟨hp, h'⟩) h
  · intro h
    exact hy p ⟨hp, h⟩

lemma eval_distancePoly {ι : Type u8} (x : ι → Plane) (a b : ι) :
    aeval (complexAssignment x) (distancePoly a b) = ((dist (x a) (x b)) ^ 2 : ℝ) := by
  simp only [distancePoly, map_mul, map_sub, aeval_X, complexAssignment,
    Option.elim_some, secondCoord, Bool.false_eq_true, reduceIte]
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  apply Complex.ext <;> simp [-Complex.ofReal_pow] <;> ring

/-- Every finite real planar configuration has a faithful number-field model
    for BOTH distance factors. The real configuration is not restricted or
    replaced: the exact equality pattern of ALL its distances is retained.
    The factorization at every place does not require conjugacy in the new field. -/
theorem planar_factor_model {ι : Type u9} [Finite ι]
    (x : ι → Plane) (hx : Function.Injective x) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
      ∃ (ii : K) (Z₁ Z₂ : ι → K), ii ^ 2 = -1 ∧
        Function.Injective Z₁ ∧ Function.Injective Z₂ ∧
        ∀ a b c d, (Z₁ a - Z₁ b) * (Z₂ a - Z₂ b) =
          (Z₁ c - Z₁ d) * (Z₂ c - Z₂ d) ↔ dist (x a) (x b) = dist (x c) (x d) := by
  classical
  let := Fintype.ofFinite ι
  let D := @distancePoly ι
  let root : MvPolynomial (Variables ι) ℚ := X none ^ 2 + 1
  let pairs := Finset.univ.image (fun t : ι × ι => D t.1 t.2)
  let quadruples := Finset.univ.image (fun t : (ι × ι) × (ι × ι) =>
    D t.1.1 t.1.2 - D t.2.1 t.2.2)
  let T := pairs ∪ quadruples ∪ {root}
  obtain ⟨K, hK, y, hy⟩ := numberField_zero_pattern T (complexAssignment x)
  let Z₁ : ι → K := fun a => y (some (false, a))
  let Z₂ : ι → K := fun a => y (some (true, a))
  have he (a b : ι) : aeval y (D a b) = (Z₁ a - Z₁ b) * (Z₂ a - Z₂ b) := by
    simp [D, distancePoly, Z₁, Z₂]
  have hp (a b : ι) : D a b ∈ T := by
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_univ _, rfl⟩
  have h0 (a b : ι) : (Z₁ a - Z₁ b) * (Z₂ a - Z₂ b) = 0 ↔ a = b := by
    rw [← he, hy _ (hp a b), eval_distancePoly]
    simp [hx.eq_iff]
  have hdist (a b c d : ι) : D a b - D c d ∈ T := by
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨((a,b),(c,d)), Finset.mem_univ _, rfl⟩
  have hroot : y none ^ 2 + 1 = 0 := by
    have hm : root ∈ T := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))
    have hc : aeval (complexAssignment x) root = 0 := by
      simp [root, complexAssignment, Complex.I_sq]
    simpa [root] using (hy root hm).mpr hc
  refine ⟨K, hK, y none, Z₁, Z₂, eq_neg_of_add_eq_zero_left hroot, ?_, ?_, ?_⟩
  · intro a b hab
    apply (h0 a b).mp
    rw [hab, sub_self, zero_mul]
  · intro a b hab
    apply (h0 a b).mp
    rw [hab, sub_self, mul_zero]
  · intro a b c d
    rw [← he, ← he]
    have h := hy _ (hdist a b c d)
    rw [map_sub, sub_eq_zero, map_sub, sub_eq_zero, eval_distancePoly,
      eval_distancePoly, Complex.ofReal_inj] at h
    exact h.trans (sq_eq_sq₀ dist_nonneg dist_nonneg)

end WeakPinned.Transfer

namespace WeakPinned
open scoped BigOperators

/-- The exact arithmetic model for each extracted real graph. No point is
assumed algebraic; the original graph's complete distance-equality pattern
is preserved by the proved finite specialization theorem. -/
theorem core_arithmetic_model (P : Finset Plane) (s : ℝ) (C : Finset P)
    (hne : ∀ e, ((coreGraph P s C).targets e).Nonempty) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
      ∃ (ii : K) (Z₁ Z₂ : C → K) (t : (planarFibers P s).Active (cutoff s P.card) C → K),
        ii^2 = -1 ∧ Function.Injective Z₁ ∧ Function.Injective Z₂ ∧
        (∀ e, t e ≠ 0) ∧
        (∀ e y, y ∈ (coreGraph P s C).targets e →
          (Z₁ ((coreGraph P s C).source e)-Z₁ y)*(Z₂ ((coreGraph P s C).source e)-Z₂ y)=t e) ∧
        (∀ a b c d : C, (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=(Z₁ c-Z₁ d)*(Z₂ c-Z₂ d) ↔
          dist a.val.val b.val.val=dist c.val.val d.val.val) := by
  classical
  let x : C → Plane := fun a => a.val.val
  have hx : Function.Injective x := Subtype.val_injective.comp Subtype.val_injective
  obtain ⟨K,hK,ii,Z₁,Z₂,hii,h₁,h₂,hpat⟩ := Transfer.planar_factor_model x hx
  choose y hy using hne
  let G := coreGraph P s C
  let t := fun e => (Z₁ (G.source e)-Z₁ (y e))*(Z₂ (G.source e)-Z₂ (y e))
  refine ⟨K,hK,ii,Z₁,Z₂,t,hii,h₁,h₂,?_,?_,hpat⟩
  · intro e
    have hxy : G.source e ≠ y e := by intro he; exact G.no_loop e (he ▸ hy e)
    exact mul_ne_zero (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
  · intro e z hz
    apply (hpat _ _ _ _).mpr
    have hz' := (Finset.mem_filter.mp hz).2
    have hy' := (Finset.mem_filter.mp (hy e)).2
    have hzdist := (planar_target_iff P s e.val z.val).mp hz'
    have hydist := (planar_target_iff P s e.val (y e).val).mp hy'
    change dist e.val.val.1 z.val.val=dist e.val.val.1 (y e).val.val
    rw [dist_comm,dist_comm e.val.val.1,hzdist,hydist]

lemma PreparedGraph.targets_nonempty {V : Type u10} {I : Type u11} [Fintype V] [Fintype I] [DecidableEq V]
    {G : Core.Fibers V I} {θ γ c η : ℝ} (h : PreparedGraph V I G θ γ c η) :
    ∀ e, (G.targets e).Nonempty := by
  intro e
  have hn : (0:ℝ)<Fintype.card V := by exact_mod_cast (show 0<Fintype.card V by have := h.card_ge; omega)
  have hh : (0:ℝ)<(G.targets e).card := (Real.rpow_pos_of_pos hn γ).trans (h.fiber e)
  exact Finset.card_pos.mp (by exact_mod_cast hh)

/-- Specialization is available independently for EVERY graph in the genuine
counterexample sequence, over number fields of unrestricted degree. -/
theorem sequence_arithmetic_model (hfail : ¬ MainStatement) :
    ∃ c s γ : ℝ, 0<c ∧ c<γ ∧ γ<s ∧ s<1 ∧ 0<Theta s ∧
      ∃ (P : ℕ → Finset Plane) (C : ∀ j, Finset (P j)),
        (∀ j, j<(C j).card) ∧
        (∀ j, PreparedGraph (C j) ((planarFibers (P j) s).Active (cutoff s (P j).card) (C j))
          (coreGraph (P j) s (C j)) (Theta s) γ c (Theta s/(j+2))) ∧
        ∀ j, ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), NumberField K ∧
          ∃ (ii : K) (Z₁ Z₂ : C j → K) (t : (planarFibers (P j) s).Active (cutoff s (P j).card) (C j) → K),
            ii^2 = -1 ∧ Function.Injective Z₁ ∧ Function.Injective Z₂ ∧
            (∀ e, t e ≠ 0) ∧
            (∀ e y, y ∈ (coreGraph (P j) s (C j)).targets e →
              (Z₁ ((coreGraph (P j) s (C j)).source e)-Z₁ y)*(Z₂ ((coreGraph (P j) s (C j)).source e)-Z₂ y)=t e) := by
  obtain ⟨c,s,γ,hc,hcγ,hγs,hs,hθ,P,C,hC,hG⟩ := graph_sequence_of_failure hfail
  refine ⟨c,s,γ,hc,hcγ,hγs,hs,hθ,P,C,hC,hG,?_⟩
  intro j
  obtain ⟨K,hK,ii,Z₁,Z₂,t,hii,h₁,h₂,ht,hfiber,_⟩ :=
    core_arithmetic_model (P j) s (C j) (hG j).targets_nonempty
  exact ⟨K,hK,ii,Z₁,Z₂,t,hii,h₁,h₂,ht,hfiber⟩

end WeakPinned

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned

/-- Uniform weak pinned planar distances for arbitrary real configurations. -/
theorem mainStatement : MainStatement := by
  classical
  by_contra hfail
  obtain ⟨c,s,γ,hc,hcγ,hγs,hs,hθ,P,C,hcard,hG,hmodels⟩ := sequence_arithmetic_model hfail
  choose L hL ii Z₁ Z₂ t hii h₁ h₂ ht0 ht using hmodels
  let K := fun j => L j
  let (j : ℕ) : NumberField (K j) := hL j
  have hn : Tendsto (fun j => (Fintype.card (C j):ℝ)) atTop atTop := by
    simpa only [Fintype.card_coe, Function.comp_def] using tendsto_natCast_atTop_atTop.comp (graph_card_tendsto hcard)
  apply arithmetic_sequence_impossible (fun j => coreGraph (P j) s (C j)) (Theta s) γ c
    (fun j => Theta s/((j:ℝ)+2)) Z₁ Z₂ h₁ h₂ hθ (hc.trans hcγ) (hγs.trans hs) hc hcγ hn
    (graph_error_tendsto (Theta s)) (fun j => by positivity) _ hG t ht
  intro j
  apply div_le_div_of_nonneg_left hθ.le (by norm_num : (0:ℝ)<2)
  have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

theorem main_oai (s : ℝ) (hs : 0<s) : Tendsto (fun n : ℕ => F n s) atTop (𝓝 0) :=
  mainStatement s hs

end WeakPinned

end
end

end OAI
end

theorem solution : type_of% @OAI.WeakPinned.main_oai := @OAI.WeakPinned.main_oai
