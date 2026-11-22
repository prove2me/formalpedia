-- Prove2me | solution 1 for OrderClosures.orderAdherence_subset_uoAdherence_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:05.253836+00:00
-- url     : https://prove2.me/submissions/b5215c29-0725-4de9-92dc-701feca42605

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Pi
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LatticeSeminorm
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Tactic_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Examples_CofK_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Theorems.Thm_OrderClosures_OrderConvergesTo_uoConvergesTo
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
public import Theorems.Thm_OrderConvergesTo_add
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_abs_mem
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_const
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
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom


section
@[expose] public section
open Set
namespace OrderClosures
universe u v
section Convergence
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [IsOrderedAddMonoid X] [VectorLattice X] in
/-- Converts domination by an order-null net into order convergence to zero;
used to pass from uo-convergence to convergence of lattice clamps. -/
private theorem orderConvergesTo_zero_of_abs_le {ι : Type v} [Preorder ι]
    {f g : ι → X} (hg : OrderConvergesTo g 0) (hfg : ∀ i, |f i| ≤ |g i|) :
    OrderConvergesTo f 0 := by
  rcases hg with ⟨κ, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, hbound⟩
  refine ⟨κ, hpre, hdir, hne, r, hranti, hrnonneg, hrglb, ?_⟩
  intro k
  exact (hbound k).mono fun i hi ↦ by
    simpa using (hfg i).trans (by simpa using hi)
omit [VectorLattice X] in
/-- Bounds the change of a lattice clamp by the clamped difference; used by
`UOConvergesTo.clamp` to obtain its controlling order-null net. -/
private theorem abs_clamp_le (x a : X) (ha : 0 ≤ a) :
    |(x ⊓ a) ⊔ (-a)| ≤ a := by
  apply (abs_le').2
  exact ⟨sup_le inf_le_right ((neg_nonpos.mpr ha).trans ha),
    by simpa using neg_le_neg (show -a ≤ (x ⊓ a) ⊔ (-a) from le_sup_right)⟩
omit [VectorLattice X] in
/-- Shows that clamping a uo-convergent net to a fixed order interval gives
order convergence; this is the key reduction in the adherence comparison. -/
private theorem UOConvergesTo.clamp {ι : Type v} [Preorder ι]
      {f : ι → X} {x : X}
    (h : UOConvergesTo f x) (a : X) (ha : 0 ≤ a) :
    OrderConvergesTo (fun i ↦ (f i ⊓ a) ⊔ (-a)) ((x ⊓ a) ⊔ (-a)) := by
  let c : X := (x ⊓ a) ⊔ (-a)
  let d : ι → X := fun i ↦ ((f i ⊓ a) ⊔ (-a)) - c
  have ht := h (a + a) (add_nonneg ha ha)
  have hd_bound : ∀ i, |d i| ≤ |(|f i - x| ⊓ (a + a))| := by
    intro i
    have hfirst : |d i| ≤ |f i - x| := by
      exact (abs_sup_sub_sup_le_abs (f i ⊓ a) (x ⊓ a) (-a)).trans
        (abs_inf_sub_inf_le_abs (f i) x a)
    have hsecond : |d i| ≤ a + a := by
      calc
        |d i| = |((f i ⊓ a) ⊔ (-a)) + -((x ⊓ a) ⊔ (-a))| := by
          simp [d, c, sub_eq_add_neg]
        _ ≤ |(f i ⊓ a) ⊔ (-a)| + |(x ⊓ a) ⊔ (-a)| := by
          simpa using abs_add_le ((f i ⊓ a) ⊔ (-a)) (-((x ⊓ a) ⊔ (-a)))
        _ ≤ a + a := add_le_add (abs_clamp_le _ _ ha) (abs_clamp_le _ _ ha)
    have ht_nonneg : 0 ≤ |f i - x| ⊓ (a + a) :=
      le_inf (abs_nonneg _) (add_nonneg ha ha)
    simpa [abs_of_nonneg ht_nonneg] using (le_inf hfirst hsecond)
  have hd : OrderConvergesTo d 0 := orderConvergesTo_zero_of_abs_le ht hd_bound
  have hsum := hd.add (orderConvergesTo_const (ι := ι) c)
  simpa [d, c] using hsum
end Convergence
section Solidity
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
end Solidity
section CompletenessAndNorms
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [Module ℝ X]
end CompletenessAndNorms
end OrderClosures
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set
open OrderClosures
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution {Y : VectorSublattice X} :
    orderAdherence (Y : Set X) ⊆ uoAdherence (Y : Set X) ∧
      uoAdherence (Y : Set X) ⊆ orderAdherence (orderAdherence (Y : Set X)) := by
  constructor
  · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    exact ⟨ι, inferInstance, inferInstance, inferInstance, f, hf,
      OrderConvergesTo.uoConvergesTo hfx⟩
  · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    let g : ι → X := fun i ↦ (x ⊓ |f i|) ⊔ (-|f i|)
    have hg_mem : ∀ i, g i ∈ orderAdherence (Y : Set X) := by
      intro i
      have hai : |f i| ∈ Y := Y.abs_mem (hf i)
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun j ↦ (f j ⊓ |f i|) ⊔ (-|f i|), ?_, ?_⟩
      · intro j
        exact Y.sup_mem (Y.inf_mem (hf j) hai) (Y.toSubmodule.neg_mem hai)
      · exact hfx.clamp |f i| (abs_nonneg _)
    have ht := hfx |x| (abs_nonneg x)
    have hdiff : OrderConvergesTo (fun i ↦ g i - x) 0 := by
      apply orderConvergesTo_zero_of_abs_le ht
      intro i
      dsimp [g]
      have clamp_bound_test (x a r : X) (hr : 0 ≤ r) (h : |x| - a ≤ r) :
          |((x ⊓ a) ⊔ -a) - x| ≤ r := by
        have hxa : x - a ≤ r := (sub_le_sub_right (le_abs_self x) a).trans h
        have hnxa : -x - a ≤ r := (sub_le_sub_right (neg_le_abs x) a).trans h
        rw [abs_le', and_comm, neg_le]
        constructor
        · have hxr : x - r ≤ a := by
            apply sub_le_iff_le_add.mpr
            simpa [add_comm] using (sub_le_iff_le_add.mp hxa)
          have hc : x - r ≤ (x ⊓ a) ⊔ -a :=
            (le_inf (sub_le_self x hr) hxr).trans le_sup_left
          apply le_sub_iff_add_le.mpr
          simpa [sub_eq_add_neg, add_comm] using hc
        · apply sub_le_iff_le_add.mpr
          refine sup_le (inf_le_left.trans ?_) ?_
          · exact le_add_of_nonneg_left hr
          · have hh : -a - x ≤ r := by
              simpa [sub_eq_add_neg, add_comm] using hnxa
            exact sub_le_iff_le_add.mp hh
      apply clamp_bound_test _ _ _ (abs_nonneg _)
      apply le_trans (le_inf ?_ ?_) (le_abs_self _)
      · simpa only [abs_sub_comm] using ((le_abs_self (|x| - |f i|)).trans (abs_abs_sub_abs_le x (f i)))
      · exact sub_le_self _ (abs_nonneg _)
    have hg_order := hdiff.add (orderConvergesTo_const (ι := ι) x)
    refine ⟨ι, inferInstance, inferInstance, inferInstance, g, hg_mem, ?_⟩
    simpa [g] using hg_order
end OrderClosures
