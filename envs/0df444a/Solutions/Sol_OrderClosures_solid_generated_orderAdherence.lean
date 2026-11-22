-- Prove2me | solution 1 for OrderClosures.solid_generated_orderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:52.449507+00:00
-- url     : https://prove2.me/submissions/ef03e29a-63ff-4ba4-af9c-6c91cadc1c02

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_orderConvergesTo_zero_of_abs_le_gao
public import Theorems.Thm_ClosedOrderIdeal_inf_toSubmodule
public import Theorems.Thm_ClosedOrderIdeal_mem_sInf
public import Theorems.Thm_ClosedOrderIdeal_sup_toSubmodule
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
public import Theorems.Thm_OrderClosures_CNFListLT_trans
public import Theorems.Thm_OrderClosures_CNFStep_trans
public import Theorems.Thm_OrderConvergesTo_abs
public import Theorems.Thm_OrderConvergesTo_add
public import Theorems.Thm_OrderConvergesTo_sub
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
public import Theorems.Thm_orderConvergesTo_const
public import Theorems.Thm_orderConvergesTo_of_monotone_isLUB
attribute [local simp] ClosedOrderIdeal.inf_toSubmodule
attribute [local simp] ClosedOrderIdeal.mem_sInf
attribute [local simp] ClosedOrderIdeal.sup_toSubmodule
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



set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {G : Set X} (hG : G ⊆ Ici 0) :
    orderAdherence (solidHull G) =
      {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (a : ι → X),
        (∀ i, a i ∈ G) ∧
          OrderConvergesTo (fun i ↦ |x| ⊓ a i) |x| ∧
          IsLUB (Set.range fun i ↦ |x| ⊓ a i) |x|} := by
  ext x
  constructor
  · rintro ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    rcases hfx with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrnonneg, hrglb, hbound⟩
    let : Preorder κ := hκpre
    let : IsDirected κ (· ≤ ·) := hκdir
    let : Nonempty κ := hκne
    let y : κ → X := fun k ↦ (|x| - r k)⁺
    have hy_mono : Monotone y := fun _ _ hkl ↦
      posPart_mono (sub_le_sub_left (hranti hkl) |x|)
    have hy_lub : IsLUB (Set.range y) |x| := by
      constructor
      · rintro _ ⟨k, rfl⟩
        exact show (|x| - r k) ⊔ 0 ≤ |x| from
          sup_le (sub_le_self _ (hrnonneg k)) (abs_nonneg _)
      · intro c hc
        have hlow : |x| - c ∈ lowerBounds (Set.range r) := by
          rintro _ ⟨k, rfl⟩
          have hraw : |x| - r k ≤ c := (le_posPart _).trans (hc ⟨k, rfl⟩)
          exact sub_le_iff_le_add.mpr (by
            simpa [add_comm] using (sub_le_iff_le_add.mp hraw))
        exact sub_nonpos.mp (hrglb.2 hlow)
    have hyG : ∀ k, ∃ a ∈ G, y k ≤ a := by
      intro k
      obtain ⟨i, hi⟩ := (hbound k).exists
      rcases hf i with ⟨a, haG, hfa⟩
      have hx_le : |x| ≤ |f i| + r k := by
        calc
          |x| = |(x - f i) + f i| := by congr 1; abel
          _ ≤ |x - f i| + |f i| := abs_add_le _ _
          _ = |f i| + |x - f i| := add_comm _ _
          _ ≤ |f i| + r k := add_le_add_right (by
            simpa [abs_sub_comm] using hi) _
      have hsub : |x| - r k ≤ |f i| := sub_le_iff_le_add.mpr hx_le
      have hyf : y k ≤ |f i| :=
        show (|x| - r k) ⊔ 0 ≤ |f i| from sup_le hsub (abs_nonneg _)
      exact ⟨a, haG, hyf.trans (by simpa [abs_of_nonneg (hG haG)] using hfa)⟩
    choose a haG hya using hyG
    let q : κ → X := fun k ↦ |x| ⊓ a k
    have hy_order : OrderConvergesTo y |x| :=
      orderConvergesTo_of_monotone_isLUB hy_mono hy_lub
    have hq_order : OrderConvergesTo q |x| := by
      have hzero : OrderConvergesTo (fun k ↦ q k - |x|) 0 := by
        have hbase : OrderConvergesTo (fun k ↦ y k - |x|) 0 := by
          simpa using hy_order.sub (orderConvergesTo_const |x|)
        apply orderConvergesTo_zero_of_abs_le_gao hbase
        intro k
        dsimp [q]
        have hyx : y k ≤ |x| := hy_lub.1 ⟨k, rfl⟩
        have hyq : y k ≤ |x| ⊓ a k := le_inf hyx (hya k)
        rw [abs_of_nonpos (sub_nonpos.mpr inf_le_left),
          abs_of_nonpos (sub_nonpos.mpr hyx)]
        exact neg_le_neg (sub_le_sub_right hyq |x|)
      have := hzero.add (orderConvergesTo_const (ι := κ) |x|)
      simpa [q] using this
    have hq_lub : IsLUB (Set.range q) |x| := by
      constructor
      · rintro _ ⟨k, rfl⟩
        exact inf_le_left
      · intro c hc
        apply hy_lub.2
        rintro _ ⟨k, rfl⟩
        exact (le_inf (hy_lub.1 ⟨k, rfl⟩) (hya k)).trans (hc ⟨k, rfl⟩)
    exact ⟨κ, inferInstance, inferInstance, inferInstance, a, haG, hq_order, hq_lub⟩
  · rintro ⟨ι, hpre, hdir, hne, a, haG, hq_order, _hq_lub⟩
    let : Preorder ι := hpre
    let : IsDirected ι (· ≤ ·) := hdir
    let : Nonempty ι := hne
    let c : ι → X := fun i ↦ (x ⊓ a i) ⊔ (-a i)
    have hc_mem : ∀ i, c i ∈ solidHull G := by
      intro i
      refine ⟨a i, haG i, ?_⟩
      dsimp [c]
      have hai : 0 ≤ a i := hG (haG i)
      change |(x ⊓ a i) ⊔ -a i| ≤ |a i|
      rw [abs_of_nonneg hai, abs_le', and_comm, neg_le]
      exact ⟨le_sup_right, sup_le inf_le_right ((neg_nonpos.mpr hai).trans hai)⟩
    have hc_order : OrderConvergesTo c x := by
      have hzero : OrderConvergesTo (fun i ↦ c i - x) 0 := by
        have hbase : OrderConvergesTo (fun i ↦ (|x| ⊓ a i) - |x|) 0 := by
          simpa using hq_order.sub (orderConvergesTo_const |x|)
        apply orderConvergesTo_zero_of_abs_le_gao hbase
        intro i
        dsimp [c]
        have hai : 0 ≤ a i := hG (haG i)
        change |((x ⊓ a i) ⊔ (-a i)) - x| ≤ abs ((|x| ⊓ a i) - |x|)
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
        exact (sub_le_sub_left inf_le_right |x|).trans (by
          simpa only [neg_sub] using (neg_le_abs ((|x| ⊓ a i) - |x|)))
      have := hzero.add (orderConvergesTo_const (ι := ι) x)
      simpa [c] using this
    exact ⟨ι, inferInstance, inferInstance, inferInstance, c, hc_mem, hc_order⟩
end OrderClosures
