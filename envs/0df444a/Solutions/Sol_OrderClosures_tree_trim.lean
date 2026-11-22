-- Prove2me | solution 1 for OrderClosures.tree_trim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:36.702994+00:00
-- url     : https://prove2.me/submissions/43021031-08f2-4090-9663-cd18a26611a8

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_treeBandOfNode_eq_of_mem
public import Theorems.Thm_OrderClosures_treeBandProjection_support_nonempty_iff
public import Theorems.Thm_OrderClosures_mem_bandsAt_iff
public import Theorems.Thm_OrderClosures_finiteBandProjection_apply
public import Theorems.Thm_OrderClosures_finiteBandProjection_nonneg
public import Theorems.Thm_OrderClosures_finiteBandProjection_le
public import Theorems.Thm_OrderClosures_treeRho_finiteBandProjection
public import Theorems.Thm_OrderClosures_sum_treeRho_bandProjection_le
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
public import Theorems.Thm_OrderClosures_treeOperator_le_root_of_nonneg
public import Theorems.Thm_OrderClosures_treeRho_mono_of_nonneg
public import Theorems.Thm_OrderConvergesTo_le
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
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
namespace OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
private theorem exists_positive_finite_sum_budget {ι : Type*} [Countable ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ι → ℝ, (∀ i, 0 < δ i) ∧ ∀ F : Finset ι, ∑ i ∈ F, δ i ≤ ε := by
  classical
  let : Encodable ι := Encodable.ofCountable _
  let a := ε / 2
  have ha : 0 < a := div_pos hε (by norm_num)
  let δ : ι → ℝ := fun i ↦ a * (1 / 2 : ℝ) ^ Encodable.encode i
  have hδpos (i : ι) : 0 < δ i := mul_pos ha (pow_pos (by norm_num) _)
  have hgeom : Summable (fun i : ι ↦ (1 / 2 : ℝ) ^ Encodable.encode i) := by
    simpa [Function.comp_def] using
      summable_geometric_two.comp_injective Encodable.encode_injective
  have hgeom_tsum_le : ∑' i : ι, (1 / 2 : ℝ) ^ Encodable.encode i ≤ 2 := by
    calc
      ∑' i : ι, (1 / 2 : ℝ) ^ Encodable.encode i ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
        hgeom.tsum_le_tsum_of_inj Encodable.encode Encodable.encode_injective
          (fun k _ ↦ by positivity) (fun _ ↦ le_rfl) summable_geometric_two
      _ = 2 := tsum_geometric_two
  have hδsummable : Summable δ := hgeom.mul_left a
  refine ⟨δ, hδpos, fun F ↦ ?_⟩
  calc
    ∑ i ∈ F, δ i ≤ ∑' i, δ i :=
      Summable.sum_le_tsum F (fun i _ ↦ (hδpos i).le) hδsummable
    _ = a * ∑' i : ι, (1 / 2 : ℝ) ^ Encodable.encode i := tsum_mul_left
    _ ≤ a * 2 := mul_le_mul_of_nonneg_left hgeom_tsum_le ha.le
    _ = ε := by dsimp [a]; ring
end OrderClosures
end
end

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution
    (n : ℕ) (x : ℕ → TreeComponent n) (w : ℕ → TreeCoefficients n)
    {ε : ℝ} (hε : 0 < ε)
    (hw : ∀ m, 0 ≤ w m)
    (hdom : ∀ m, (x m).1 ≤ treeOperator n (w m))
    (hrho : ∀ m, treeRho n (w m) < 1 + ε / 4)
    (hsharp : ∀ B : TreeBandIndex n, ∃ l : ℝ,
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds l)) :
    ∃ w' : ℕ → TreeCoefficients n,
      (∀ m, 0 ≤ w' m ∧ (x m).1 ≤ treeOperator n (w' m) ∧
        treeRho n (w' m) < 1 + ε / 2) ∧
      (recurrentBands n w').Finite := by
  classical
  let M : ℝ := (2 : ℝ) ^ n
  have hM : 0 < M := pow_pos (by norm_num) n
  let lam : TreeBandIndex n → ℝ := fun B ↦ Classical.choose (hsharp B)
  have hlamlim (B : TreeBandIndex n) :
      Tendsto (fun m ↦ treeRho n (treeBandProjection n B (w m)))
        atTop (nhds (lam B)) := Classical.choose_spec (hsharp B)
  have hlamnonneg (B : TreeBandIndex n) : 0 ≤ lam B := by
    apply ge_of_tendsto (hlamlim B)
    exact Filter.Eventually.of_forall fun m ↦ treeRho_nonneg n _
  have hlamfinite (S : Finset (TreeBandIndex n)) :
      ∑ B ∈ S, lam B ≤ 1 + ε / 4 := by
    have hlim : Tendsto
        (fun m ↦ ∑ B ∈ S, treeRho n (treeBandProjection n B (w m)))
        atTop (nhds (∑ B ∈ S, lam B)) :=
      tendsto_finsetSum S fun B _ ↦ hlamlim B
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun m ↦
      (sum_treeRho_bandProjection_le n S (w m)).trans (hrho m).le
  have hlamsummable : Summable lam :=
    summable_of_sum_le (fun B ↦ hlamnonneg B) hlamfinite
  let tailBudget : ℝ := ε / (8 * M)
  have htailBudget : 0 < tailBudget := div_pos hε (mul_pos (by norm_num) hM)
  obtain ⟨Λ₀, hΛ₀⟩ :=
    (Metric.tendsto_atTop.mp hlamsummable.hasSum) tailBudget htailBudget
  let Λ : Finset (TreeBandIndex n) := insert none Λ₀
  have hnoneΛ : none ∈ Λ := by simp [Λ]
  have hΛapprox : dist (∑ B ∈ Λ, lam B) (∑' B, lam B) < tailBudget :=
    hΛ₀ Λ (Finset.subset_insert none Λ₀)
  have hΛsum_le : ∑ B ∈ Λ, lam B ≤ ∑' B, lam B :=
    Summable.sum_le_tsum Λ (fun B _ ↦ hlamnonneg B) hlamsummable
  have htail (F : Finset (TreeBandIndex n))
      (hF : ∀ B ∈ F, B ∉ Λ) : ∑ B ∈ F, lam B < tailBudget := by
    have hdis : Disjoint Λ F := Finset.disjoint_left.mpr fun B hBΛ hBF ↦
      (hF B hBF) hBΛ
    have hunion : (∑ B ∈ Λ, lam B) + ∑ B ∈ F, lam B =
        ∑ B ∈ Λ ∪ F, lam B := by
      exact (Finset.sum_union hdis).symm
    have hle : ∑ B ∈ Λ ∪ F, lam B ≤ ∑' B, lam B :=
      Summable.sum_le_tsum (Λ ∪ F) (fun B _ ↦ hlamnonneg B) hlamsummable
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hΛsum_le)] at hΛapprox
    linarith
  obtain ⟨δ, hδpos, hδfinite⟩ :=
    exists_positive_finite_sum_budget (ι := TreeBandIndex n) htailBudget
  have hcutoff (B : TreeBandIndex n) : ∃ N : ℕ, ∀ m ≥ N,
      treeRho n (treeBandProjection n B (w m)) < lam B + δ B := by
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.mp (hlamlim B)) (δ B) (hδpos B)
    refine ⟨N, fun m hm ↦ ?_⟩
    have habs := hN m hm
    rw [Real.dist_eq] at habs
    have hsub : treeRho n (treeBandProjection n B (w m)) - lam B < δ B :=
      (le_abs_self _).trans_lt habs
    linarith
  let N : TreeBandIndex n → ℕ := fun B ↦ Classical.choose (hcutoff B)
  have hN (B : TreeBandIndex n) (m : ℕ) (hm : N B ≤ m) :
      treeRho n (treeBandProjection n B (w m)) < lam B + δ B :=
    Classical.choose_spec (hcutoff B) m hm
  let removedBands : ℕ → Finset (TreeBandIndex n) := fun m ↦
    (bandsAt n (w m)).filter fun B ↦ B ∉ Λ ∧ N B ≤ m
  let r : ℕ → TreeCoefficients n := fun m ↦
    finiteBandProjection n (removedBands m) (w m)
  let w' : ℕ → TreeCoefficients n := fun m ↦
    w m - r m + (M * treeRho n (r m)) • treeBasis (TreeNode.root n)
  have hr_nonneg (m : ℕ) : 0 ≤ r m :=
    finiteBandProjection_nonneg n (removedBands m) (hw m)
  have hkeep_nonneg (m : ℕ) : 0 ≤ w m - r m :=
    sub_nonneg.mpr (finiteBandProjection_le n (removedBands m) (hw m))
  have hrho_r (m : ℕ) : treeRho n (r m) < ε / (4 * M) := by
    have hRB (B : TreeBandIndex n) (hB : B ∈ removedBands m) :
        treeRho n (treeBandProjection n B (w m)) < lam B + δ B := by
      exact hN B m (Finset.mem_filter.mp hB).2.2
    have houtside (B : TreeBandIndex n) (hB : B ∈ removedBands m) : B ∉ Λ :=
      (Finset.mem_filter.mp hB).2.1
    change treeRho n (finiteBandProjection n (removedBands m) (w m)) < _
    rw [treeRho_finiteBandProjection]
    calc
      ∑ B ∈ removedBands m, treeRho n (treeBandProjection n B (w m)) ≤
          ∑ B ∈ removedBands m, (lam B + δ B) := by
        apply Finset.sum_le_sum
        intro B hB
        exact (hRB B hB).le
      _ = (∑ B ∈ removedBands m, lam B) + ∑ B ∈ removedBands m, δ B := by
        rw [← Finset.sum_add_distrib]
      _ < tailBudget + tailBudget :=
        add_lt_add_of_lt_of_le (htail (removedBands m) houtside)
          (hδfinite (removedBands m))
      _ = ε / (4 * M) := by
        dsimp [tailBudget]
        field_simp
        ring
  refine ⟨w', ?_, ?_⟩
  · intro m
    have hroot_nonneg : 0 ≤
        (M * treeRho n (r m)) • treeBasis (TreeNode.root n) := by
      intro t
      change 0 ≤ (M * treeRho n (r m)) * treeBasis (TreeNode.root n) t
      apply mul_nonneg (mul_nonneg hM.le (treeRho_nonneg n (r m)))
      by_cases ht : t = TreeNode.root n <;> simp [treeBasis, ht]
    refine ⟨add_nonneg (hkeep_nonneg m) hroot_nonneg, ?_, ?_⟩
    · calc
        (x m).1 ≤ treeOperator n (w m) := hdom m
        _ = treeOperator n (w m - r m) + treeOperator n (r m) := by
          rw [← treeOperator_add]
          congr 1
          abel
        _ ≤ treeOperator n (w m - r m) +
            (M * treeRho n (r m)) • treeFunction n (TreeNode.root n) := by
          exact add_le_add le_rfl
            (treeOperator_le_root_of_nonneg n (r m) (hr_nonneg m))
        _ = treeOperator n (w' m) := by
          change _ = treeOperator n
            (w m - r m + (M * treeRho n (r m)) • treeBasis (TreeNode.root n))
          rw [treeOperator_add, treeOperator_smul, treeBasis,
            treeOperator_single, one_smul]
    · have hkeep_le : w m - r m ≤ w m := by
        exact sub_le_self _ (hr_nonneg m)
      calc
        treeRho n (w' m) ≤ treeRho n (w m - r m) +
            treeRho n ((M * treeRho n (r m)) • treeBasis (TreeNode.root n)) :=
          treeRho_add_le n _ _
        _ ≤ treeRho n (w m) + M * treeRho n (r m) := by
          apply add_le_add
          · exact treeRho_mono_of_nonneg n (hkeep_nonneg m) hkeep_le
          · rw [treeRho_smul, abs_of_nonneg
              (mul_nonneg hM.le (treeRho_nonneg n (r m)))]
            simp [treeBasis, treeRho, TreeNode.root, TreeNode.level]
        _ < 1 + ε / 2 := by
          have hMr : M * treeRho n (r m) < ε / 4 := by
            calc
              M * treeRho n (r m) < M * (ε / (4 * M)) :=
                mul_lt_mul_of_pos_left (hrho_r m) hM
              _ = ε / 4 := by field_simp
          linarith [hrho m]
  · apply Set.Finite.subset Λ.finite_toSet
    intro B hBrec
    by_contra hBΛ
    have hoccFinite :
        {m | (treeBandProjection n B (w' m)).support.Nonempty}.Finite := by
      apply (Finset.finite_toSet (Finset.range (N B))).subset
      intro m hm
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hmN
      have hNm : N B ≤ m := Nat.le_of_not_gt hmN
      rcases hm with ⟨t, ht⟩
      have htw' : t ∈ (w' m).support ∧ t ∈ treeBandSupport n B := by
        simpa [treeBandProjection] using ht
      have htBand : treeBandOfNode n t = B :=
        treeBandOfNode_eq_of_mem n t B htw'.2
      have htroot : t ≠ TreeNode.root n := by
        intro htr
        have : B = none := by
          rw [← htBand, htr]
          simp [treeBandOfNode]
        exact hBΛ (this ▸ hnoneΛ)
      have hwt_ne : w m t ≠ 0 := by
        intro hzero
        have hrzero : r m t = 0 := by
          by_cases htR : treeBandOfNode n t ∈ removedBands m
          · change finiteBandProjection n (removedBands m) (w m) t = 0
            rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1 htR,
              hzero]
          · change finiteBandProjection n (removedBands m) (w m) t = 0
            rw [(finiteBandProjection_apply n (removedBands m) (w m) t).2 htR]
        have hrootzero : treeBasis (TreeNode.root n) t = 0 := by
          simp [treeBasis, htroot]
        have htne := Finsupp.mem_support_iff.mp htw'.1
        change (w m - r m +
          (M * treeRho n (r m)) • treeBasis (TreeNode.root n)) t ≠ 0 at htne
        simp [Finsupp.add_apply, Finsupp.sub_apply, hzero, hrzero,
          Finsupp.smul_apply, hrootzero, smul_eq_mul] at htne
      have hBbands : B ∈ bandsAt n (w m) := by
        rw [mem_bandsAt_iff, treeBandProjection_support_nonempty_iff]
        exact ⟨t, Finsupp.mem_support_iff.mpr hwt_ne, htBand⟩
      have hBR : B ∈ removedBands m := by
        apply Finset.mem_filter.mpr
        exact ⟨hBbands, hBΛ, hNm⟩
      have hrval : r m t = w m t := by
        change finiteBandProjection n (removedBands m) (w m) t = w m t
        rw [(finiteBandProjection_apply n (removedBands m) (w m) t).1]
        exact htBand ▸ hBR
      have hrootzero : treeBasis (TreeNode.root n) t = 0 := by
        simp [treeBasis, htroot]
      have htne := Finsupp.mem_support_iff.mp htw'.1
      change (w m - r m +
        (M * treeRho n (r m)) • treeBasis (TreeNode.root n)) t ≠ 0 at htne
      simp [Finsupp.add_apply, Finsupp.sub_apply, hrval,
        Finsupp.smul_apply, hrootzero, smul_eq_mul] at htne
    exact hBrec hoccFinite
end OrderClosures
