-- Prove2me | solution 1 for VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:26:46.122511+00:00
-- url     : https://prove2.me/submissions/aea84170-7045-4b9e-bc71-1c517a701d8a

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_VectorSublattice_generated_le
public import Theorems.Thm_VectorSublattice_generated_submodule_eq_supClosure_infClosure
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval


attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] VectorSublattice.mem_bot
section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace PointedCone
end PointedCone
namespace VectorSublattice
variable (Y : VectorSublattice X)
end VectorSublattice
namespace LLexpr
variable {n : ℕ}
section Combinations
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Combinations
end LLexpr
section Normed
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
namespace VectorSublattice
variable (Y : VectorSublattice X)
omit [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [NormedVectorLattice X] in
/-- Finite subsets of a countable set form a countable set of finsets. -/
private lemma countable_finsets_subset {D : Set X} (hD : D.Countable) :
    {t : Finset X | ↑t ⊆ D}.Countable := by
  classical
  have h_fin : {u : Set X | u.Finite ∧ u ⊆ D}.Countable :=
    Set.countable_ofPred_finite_subset hD
  apply Set.Countable.mono ?_ (h_fin.image
    (fun (u : Set X) => if h : u.Finite then h.toFinset else ∅))
  intro t ht
  refine ⟨↑t, ⟨Finset.finite_toSet t, ht⟩, ?_⟩
  simp
omit [IsOrderedAddMonoid X] [NormedVectorLattice X] in
/-- If `D` is countable, then so is its sup-closure. -/
private lemma countable_supClosure {D : Set X} (hD : D.Countable) :
    (_root_.supClosure D).Countable := by
  classical
  set FD := {t : Finset X | ↑t ⊆ D} with hFD_def
  have hFD : FD.Countable := countable_finsets_subset hD
  apply Set.Countable.mono ?_
    (hFD.image (fun t : Finset X => if h : t.Nonempty then t.sup' h id else (0 : X)))
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  refine ⟨t, hsub, ?_⟩
  simp [dif_pos ht]
omit [IsOrderedAddMonoid X] [NormedVectorLattice X] in
/-- If `D` is countable, then so is its inf-closure. -/
private lemma countable_infClosure {D : Set X} (hD : D.Countable) :
    (_root_.infClosure D).Countable := by
  classical
  set FD := {t : Finset X | ↑t ⊆ D} with hFD_def
  have hFD : FD.Countable := countable_finsets_subset hD
  apply Set.Countable.mono ?_
    (hFD.image (fun t : Finset X => if h : t.Nonempty then t.inf' h id else (0 : X)))
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  refine ⟨t, hsub, ?_⟩
  simp [dif_pos ht]
private lemma supClosure_subset_closure_supClosure {s D : Set X}
    (h : s ⊆ closure D) :
    _root_.supClosure s ⊆ closure (_root_.supClosure D) := by
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  classical
  have ht_attach : t.attach.Nonempty := Finset.attach_nonempty_iff.mpr ht
  choose f hf_mem hf_tendsto using fun (y : {a // a ∈ t}) =>
    (mem_closure_iff_seq_limit.mp (h (hsub y.property)) :
      ∃ seq, (∀ n, seq n ∈ D) ∧ Filter.Tendsto seq Filter.atTop (nhds y.val))
  set xn : ℕ → X := fun n => t.attach.sup' ht_attach (fun y => f y n)
  have h_sum_mem : ∀ n, xn n ∈ _root_.supClosure D := by
    intro n
    refine ⟨t.attach.image (fun y => f y n), ht_attach.image _, ?_, ?_⟩
    · rintro z hz
      simp only [Finset.coe_image, Set.mem_image] at hz
      obtain ⟨y, _, rfl⟩ := hz
      exact hf_mem y n
    · rw [Finset.sup'_image]
      rfl
  have h_eq : t.attach.sup' ht_attach (Subtype.val : {a // a ∈ t} → X) = t.sup' ht id := by
    refine le_antisymm ?_ ?_
    · exact Finset.sup'_le _ _ fun y _ => Finset.le_sup' (f := id) y.2
    · refine Finset.sup'_le _ _ fun a ha => ?_
      exact Finset.le_sup' (f := Subtype.val) (Finset.mem_attach t ⟨a, ha⟩)
  have h_tendsto : Filter.Tendsto xn Filter.atTop
      (nhds (t.attach.sup' ht_attach (Subtype.val : {a // a ∈ t} → X))) :=
    Filter.Tendsto.finset_sup'_nhds_apply ht_attach (fun y _ => hf_tendsto y)
  rw [← h_eq]
  exact mem_closure_of_tendsto h_tendsto (Filter.Eventually.of_forall h_sum_mem)
private lemma infClosure_subset_closure_infClosure {s D : Set X}
    (h : s ⊆ closure D) :
    _root_.infClosure s ⊆ closure (_root_.infClosure D) := by
  intro x hx
  obtain ⟨t, ht, hsub, rfl⟩ := hx
  classical
  have ht_attach : t.attach.Nonempty := Finset.attach_nonempty_iff.mpr ht
  choose f hf_mem hf_tendsto using fun (y : {a // a ∈ t}) =>
    (mem_closure_iff_seq_limit.mp (h (hsub y.property)) :
      ∃ seq, (∀ n, seq n ∈ D) ∧ Filter.Tendsto seq Filter.atTop (nhds y.val))
  set xn : ℕ → X := fun n => t.attach.inf' ht_attach (fun y => f y n)
  have h_sum_mem : ∀ n, xn n ∈ _root_.infClosure D := by
    intro n
    refine ⟨t.attach.image (fun y => f y n), ht_attach.image _, ?_, ?_⟩
    · rintro z hz
      simp only [Finset.coe_image, Set.mem_image] at hz
      obtain ⟨y, _, rfl⟩ := hz
      exact hf_mem y n
    · rw [Finset.inf'_image]
      rfl
  have h_eq : t.attach.inf' ht_attach (Subtype.val : {a // a ∈ t} → X) = t.inf' ht id := by
    refine le_antisymm ?_ ?_
    · refine Finset.le_inf' _ _ fun a ha => ?_
      exact Finset.inf'_le (f := Subtype.val) (Finset.mem_attach t ⟨a, ha⟩)
    · exact Finset.le_inf' _ _ fun y _ => Finset.inf'_le (f := id) y.2
  have h_tendsto : Filter.Tendsto xn Filter.atTop
      (nhds (t.attach.inf' ht_attach (Subtype.val : {a // a ∈ t} → X))) :=
    Filter.Tendsto.finset_inf'_nhds_apply ht_attach (fun y _ => hf_tendsto y)
  rw [← h_eq]
  exact mem_closure_of_tendsto h_tendsto (Filter.Eventually.of_forall h_sum_mem)
private lemma isSeparable_supClosure {s : Set X}
    (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (_root_.supClosure s) := by
  obtain ⟨D, hD_ctble, hs_sub⟩ := hs
  exact ⟨_root_.supClosure D, countable_supClosure hD_ctble,
    supClosure_subset_closure_supClosure hs_sub⟩
private lemma isSeparable_infClosure {s : Set X}
    (hs : TopologicalSpace.IsSeparable s) :
    TopologicalSpace.IsSeparable (_root_.infClosure s) := by
  obtain ⟨D, hD_ctble, hs_sub⟩ := hs
  exact ⟨_root_.infClosure D, countable_infClosure hD_ctble,
    infClosure_subset_closure_infClosure hs_sub⟩
end VectorSublattice
end Normed
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)
namespace VectorSublattice
theorem _root_.solution
    {A : Set X} (hA : A.Countable) :
    TopologicalSpace.SeparableSpace
      ↥(topologicalClosure (generated A)).toSubmodule := by
  have h_span_eq : (generated A : Set X) =
      (generated (Submodule.span ℝ A : Set X) : Set X) := by
    refine Set.Subset.antisymm ?_ ?_
    · exact generated_le (Set.Subset.trans Submodule.subset_span (subset_generated _))
    · exact generated_le
        (Submodule.span_le.mpr (subset_generated A))
  have h_gen : (generated A : Set X) =
      _root_.supClosure (_root_.infClosure (Submodule.span ℝ A : Set X)) := by
    rw [h_span_eq]; exact generated_submodule_eq_supClosure_infClosure _
  have h_span_sep : TopologicalSpace.IsSeparable (Submodule.span ℝ A : Set X) :=
    (hA.isSeparable).span
  have h_gen_sep : TopologicalSpace.IsSeparable (generated A : Set X) := by
    rw [h_gen]
    exact isSeparable_supClosure (isSeparable_infClosure h_span_sep)
  have h_closure_sep : TopologicalSpace.IsSeparable
      ((topologicalClosure (generated A)).toSubmodule : Set X) := by
    have : ((topologicalClosure (generated A)).toSubmodule : Set X) =
        closure (generated A : Set X) := Submodule.topologicalClosure_coe _
    rw [this]
    exact h_gen_sep.closure
  exact h_closure_sep.separableSpace
end VectorSublattice
