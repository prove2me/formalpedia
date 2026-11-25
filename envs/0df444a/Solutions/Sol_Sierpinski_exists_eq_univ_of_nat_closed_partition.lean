-- Prove2me | solution 1 for Sierpinski.exists_eq_univ_of_nat_closed_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:12:57.27851+00:00
-- url     : https://prove2.me/submissions/d0624e39-eb94-4d01-b054-b5852c913e6f

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_Sierpinski_Solution
public import Theorems.Thm_BoundaryBumping_exists_subcontinuum_meeting_frontier
section
@[expose] public section
open Set
namespace BoundaryBumping
variable {X : Type*} [TopologicalSpace X]
end BoundaryBumping
universe u v w
namespace Sierpinski
variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]
private theorem shrink_continuum (F : ℕ → Set X)
    (hclosed : ∀ n, IsClosed (F n))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ n, F n = univ)
    {C : Set X} (hcompact : IsCompact C) (hconnected : IsConnected C)
    (htwo : ∃ i j, i ≠ j ∧ (C ∩ F i).Nonempty ∧ (C ∩ F j).Nonempty)
    (n : ℕ) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ D ⊆ C ∧
      Disjoint D (F n) ∧
      ∃ i j, i ≠ j ∧ (D ∩ F i).Nonempty ∧ (D ∩ F j).Nonempty := by
  classical
  by_cases hmiss : Disjoint C (F n)
  · exact ⟨C, hcompact, hconnected, subset_rfl, hmiss, htwo⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace C := Subtype.connectedSpace hconnected
  let G : ℕ → Set C := fun k => Subtype.val ⁻¹' F k
  have hGclosed (k : ℕ) : IsClosed (G k) :=
    (hclosed k).preimage continuous_subtype_val
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  have hm : ∃ m, m ≠ n ∧ (C ∩ F m).Nonempty := by
    by_cases hin : i = n
    · exact ⟨j, fun hjn => hij (hin.trans hjn.symm), hj⟩
    · exact ⟨i, hin, hi⟩
  obtain ⟨m, hmn, p, hpC, hpF⟩ := hm
  let q : C := ⟨p, hpC⟩
  have hsep : Disjoint (G n) (G m) := (hdisjoint hmn.symm).preimage Subtype.val
  obtain ⟨U, V, hU, hV, hnU, hmV, hUV⟩ :=
    normal_separation (hGclosed n) (hGclosed m) hsep
  have hclV : Disjoint (closure V) U := hUV.symm.closure_left hU
  have hproper : closure V ≠ univ := by
    intro heq
    obtain ⟨z, hzC, hzF⟩ := not_disjoint_iff_nonempty_inter.mp hmiss
    exact disjoint_left.mp hclV (heq ▸ mem_univ (⟨z, hzC⟩ : C)) (hnU hzF)
  have hqV : q ∈ V := hmV hpF
  obtain ⟨K, hKcompact, hKconnected, hqK, hKsub, y, hyK, hyfront⟩ :=
    BoundaryBumping.exists_subcontinuum_meeting_frontier isClosed_closure hproper
      (subset_closure hqV)
  have hyNotM : (y : X) ∉ F m := by
    intro hyM
    exact hyfront.2 (hV.subset_interior_closure (hmV hyM))
  have hKavoid : Disjoint (Subtype.val '' K) (F n) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨w, hwK, rfl⟩ hzN
    exact disjoint_left.mp hclV (hKsub hwK) (hnU hzN)
  have hycover : (y : X) ∈ ⋃ k, F k := hcover ▸ mem_univ _
  obtain ⟨k, hyF⟩ := mem_iUnion.mp hycover
  have hmk : m ≠ k := by
    intro hmk
    exact hyNotM (hmk ▸ hyF)
  refine ⟨Subtype.val '' K, hKcompact.image continuous_subtype_val,
    hKconnected.image _ continuous_subtype_val.continuousOn, ?_, hKavoid,
    m, k, hmk, ⟨p, ⟨q, hqK, rfl⟩, hpF⟩, ⟨y, ⟨y, hyK, rfl⟩, hyF⟩⟩
  rintro z ⟨w, _, rfl⟩
  exact w.2
end Sierpinski
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set
universe u v w
open Sierpinski
variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]
namespace Sierpinski
theorem _root_.solution
    [cX : CompactSpace X] [connX : ConnectedSpace X]
    (F : ℕ → Set X) (hclosed : ∀ n, IsClosed (F n))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ n, F n = univ) : ∃ n, F n = univ := by
  classical
  by_contra hwhole
  have hproper : ∀ n, F n ≠ univ := by simpa using hwhole
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
  have hiProper : ¬ univ ⊆ F i := by
    intro hsub
    exact hproper i (Subset.antisymm (subset_univ _) hsub)
  obtain ⟨y, _, hyi⟩ := not_subset.mp hiProper
  obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover ▸ mem_univ y)
  have hij : i ≠ j := by
    intro hij
    exact hyi (hij ▸ hyj)
  let P : Set X → Prop := fun C => IsCompact C ∧ IsConnected C ∧
    ∃ a b, a ≠ b ∧ (C ∩ F a).Nonempty ∧ (C ∩ F b).Nonempty
  have hstart : P univ := ⟨isCompact_univ, isConnected_univ,
    i, j, hij, ⟨x, mem_univ x, hxi⟩, ⟨y, mem_univ y, hyj⟩⟩
  have hstep (C : {C : Set X // P C}) (n : ℕ) :
      ∃ D : {C : Set X // P C}, D.val ⊆ C.val ∧ Disjoint D.val (F n) := by
    obtain ⟨D, hDc, hDconn, hDC, hDn, hDtwo⟩ :=
      shrink_continuum F hclosed hdisjoint hcover C.2.1 C.2.2.1 C.2.2.2 n
    exact ⟨⟨D, hDc, hDconn, hDtwo⟩, hDC, hDn⟩
  choose next hnextSub hnextAvoid using hstep
  let seq : ℕ → {C : Set X // P C} := Nat.rec ⟨univ, hstart⟩ (fun n C => next C n)
  have hsub (n : ℕ) : (seq (n + 1)).val ⊆ (seq n).val := hnextSub (seq n) n
  have havoid (n : ℕ) : Disjoint (seq (n + 1)).val (F n) := hnextAvoid (seq n) n
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (seq n).val) hsub (fun n => (seq n).2.2.1.nonempty)
    (seq 0).2.1 (fun n => (seq n).2.1.isClosed)
  obtain ⟨n, hzn⟩ := mem_iUnion.mp (hcover ▸ mem_univ z)
  exact disjoint_left.mp (havoid n) (mem_iInter.mp hz (n + 1)) hzn
end Sierpinski
