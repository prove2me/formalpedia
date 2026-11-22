-- Prove2me | solution 1 for OrderClosures.component_moderated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:19.550914+00:00
-- url     : https://prove2.me/submissions/8ca901e6-ac3b-460b-b91b-f475b587639f

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Theorems.Thm_OrderClosures_tree_thinning
public import Theorems.Thm_OrderClosures_tree_transient
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
public import Theorems.Thm_OrderClosures_finiteBandProjection_le
public import Theorems.Thm_OrderClosures_finiteBandProjection_nonneg
public import Theorems.Thm_OrderClosures_treeRho_finiteBandProjection_le
public import Theorems.Thm_OrderClosures_treeUpshift_basic
public import Theorems.Thm_OrderClosures_treeUpshift_support_subset_bandParents
public import Theorems.Thm_OrderClosures_tree_sharp_subsequence
public import Theorems.Thm_OrderClosures_tree_trim
public import Theorems.Thm_OrderConvergesTo_abs
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
private theorem exists_thinned_treeMajorants
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Λ : Finset (TreeBandIndex n)) (W : ℕ → TreeCoefficients n),
      none ∈ Λ ∧ (∀ m, 0 ≤ W m) ∧ (∀ m, (x m).1 ≤ treeOperator n (W m)) ∧
      (∀ m, treeRho n (W m) < 1 + ε / 2) ∧
      ∀ B ∉ Λ, {m | (treeBandProjection n B (W m)).support.Nonempty}.Subsingleton := by
  classical
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  choose w hw hmajor hrho using fun m ↦
    exists_treeMajorant_lt n (x m).1 hquarter
  have hdom (m : ℕ) : (x m).1 ≤ treeOperator n (w m) := by
    have hxpos' : 0 ≤ (x m).1 := hxpos m
    simpa [abs_of_nonneg hxpos'] using hmajor m
  have hrho' (m : ℕ) : treeRho n (w m) < 1 + ε / 4 := by
    have hn := hxnorm m
    change treeSeminorm n (x m).1 ≤ 1 at hn
    linarith [hrho m]
  obtain ⟨φ, hφ, hsharp⟩ :=
    tree_sharp_subsequence n w (1 + ε / 4) (fun m ↦ (hrho' m).le)
  have hφid (m : ℕ) : m ≤ φ m := hφ.id_le m
  have hdomφ (m : ℕ) : (x m).1 ≤ treeOperator n (w (φ m)) := by
    have hxm := hxmono (hφid m)
    change (x m).1 ≤ (x (φ m)).1 at hxm
    exact hxm.trans (hdom (φ m))
  obtain ⟨wt, hwt, hrec⟩ := tree_trim n x (fun m ↦ w (φ m)) hε
    (fun m ↦ hw (φ m)) hdomφ (fun m ↦ hrho' (φ m)) hsharp
  let Λ : Finset (TreeBandIndex n) := insert none hrec.toFinset
  have hnoneΛ : none ∈ Λ := by simp [Λ]
  have hrecΛ : recurrentBands n wt ⊆ (Λ : Set (TreeBandIndex n)) := by
    intro B hB
    simp only [Λ, Finset.mem_coe, Finset.mem_insert]
    exact Or.inr (hrec.mem_toFinset.mpr hB)
  obtain ⟨ψ, hψ, hthin⟩ := tree_thinning n wt Λ hrecΛ
  have hψid (m : ℕ) : m ≤ ψ m := hψ.id_le m
  let W : ℕ → TreeCoefficients n := fun m ↦ wt (ψ m)
  have hWpos (m : ℕ) : 0 ≤ W m := (hwt (ψ m)).1
  have hWdom (m : ℕ) : (x m).1 ≤ treeOperator n (W m) := by
    have hxm := hxmono (hψid m)
    change (x m).1 ≤ (x (ψ m)).1 at hxm
    exact hxm.trans (hwt (ψ m)).2.1
  have hWrho (m : ℕ) : treeRho n (W m) < 1 + ε / 2 :=
    (hwt (ψ m)).2.2
  have hthinW : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (W m)).support.Nonempty}.Subsingleton :=
    hthin
  exact ⟨Λ, W, hnoneΛ, hWpos, hWdom, hWrho, hthinW⟩
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
    (n : ℕ) (x : ℕ → TreeComponent n) (hxmono : Monotone x)
    (hxpos : ∀ m, 0 ≤ x m) (hxnorm : ∀ m, componentLatticeNorm n (x m) ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TreeCoefficients n, 0 ≤ w ∧
      (∀ m, (x m).1 ≤ treeOperator n w) ∧ treeRho n w ≤ 2 + ε := by
  classical
  obtain ⟨Λ, W, hnoneΛ, hWpos, hWdom, hWrho, hthinW⟩ :=
    exists_thinned_treeMajorants n x hxmono hxpos hxnorm hε
  let U₀ : ℕ → TreeCoefficients n := fun m ↦ finiteBandProjection n Λ (W m)
  let V : ℕ → TreeCoefficients n := fun m ↦ W m - U₀ m
  let U : ℕ → TreeCoefficients n := fun m ↦ treeUpshift n (U₀ m)
  have hU₀pos (m : ℕ) : 0 ≤ U₀ m := finiteBandProjection_nonneg n Λ (hWpos m)
  have hVpos (m : ℕ) : 0 ≤ V m := sub_nonneg.mpr (finiteBandProjection_le n Λ (hWpos m))
  have hUpos (m : ℕ) : 0 ≤ U m :=
    Finsupp.mapDomain_nonneg (hU₀pos m)
  let P : Finset (TreeNode n) := treeBandParents n Λ
  have hUsupport (m : ℕ) : (U m).support ⊆ P :=
    treeUpshift_support_subset_bandParents n Λ (W m)
  have hUrho (m : ℕ) : treeRho n (U m) < 2 + ε := by
    calc
      treeRho n (U m) ≤ 2 * treeRho n (U₀ m) :=
        (treeUpshift_basic n (U₀ m) (hU₀pos m)).1
      _ ≤ 2 * treeRho n (W m) :=
        mul_le_mul_of_nonneg_left (treeRho_finiteBandProjection_le n Λ (W m))
          (by norm_num)
      _ < 2 * (1 + ε / 2) := mul_lt_mul_of_pos_left (hWrho m) (by norm_num)
      _ = 2 + ε := by ring
  let M : ℝ := (2 : ℝ) ^ n
  have hM : 0 < M := pow_pos (by norm_num) n
  let D : ℝ := M * (2 + ε)
  have htwoeps : 0 < 2 + ε := by linarith
  have hD : 0 < D := mul_pos hM htwoeps
  have hUcoord (m : ℕ) (t : TreeNode n) : |U m t| ≤ D := by
    have hone : |U m t| ≤ ∑ q ∈ (U m).support, |U m q| := by
      by_cases ht : U m t = 0
      · rw [ht, abs_zero]
        exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      · exact Finset.single_le_sum (fun q _ ↦ abs_nonneg (U m q))
          (Finsupp.mem_support_iff.mpr ht)
    calc
      |U m t| ≤ ∑ q ∈ (U m).support, |U m q| := hone
      _ ≤ M * treeRho n (U m) := treeRho_controls_sum n (U m)
      _ ≤ M * (2 + ε) := mul_le_mul_of_nonneg_left (hUrho m).le hM.le
      _ = D := rfl
  let y : ℕ → ↥P → Set.Icc (-D) D := fun m t ↦
    ⟨U m t.1, by
      have habs := hUcoord m t.1
      exact ⟨(neg_le_neg habs).trans (neg_abs_le _), (le_abs_self _).trans habs⟩⟩
  let : SeqCompactSpace (↥P → Set.Icc (-D) D) := inferInstance
  obtain ⟨l, _, θ, hθ, hlim⟩ :=
    (SeqCompactSpace.isSeqCompact_univ (X := ↥P → Set.Icc (-D) D))
      (x := y) (fun _ ↦ Set.mem_univ _)
  let coeff : TreeNode n → ℝ := fun t ↦
    if ht : t ∈ P then (l ⟨t, ht⟩).1 else 0
  let u : TreeCoefficients n := Finsupp.onFinset P coeff (by
    intro t ht
    by_contra htP
    simp [coeff, htP] at ht)
  have hcoordlim (t : TreeNode n) :
      Tendsto (fun m ↦ U (θ m) t) atTop (nhds (u t)) := by
    by_cases ht : t ∈ P
    · have htend := tendsto_pi_nhds.mp hlim ⟨t, ht⟩
      have htend' := tendsto_subtype_rng.mp htend
      simpa [y, u, coeff, ht, Function.comp_def] using htend'
    · have hzero (m : ℕ) : U (θ m) t = 0 := by
        by_contra hne
        exact ht (hUsupport (θ m) (Finsupp.mem_support_iff.mpr hne))
      have huzero : u t = 0 := by simp [u, coeff, ht]
      simp only [hzero, huzero]
      exact tendsto_const_nhds
  have hupos : 0 ≤ u := by
    intro t
    apply ge_of_tendsto (hcoordlim t)
    exact Filter.Eventually.of_forall fun m ↦ hUpos (θ m) t
  have huSupport : u.support ⊆ P := Finsupp.support_onFinset_subset
  have hTop_repr (q : TreeCoefficients n) (hq : q.support ⊆ P) :
      treeOperator n q = ∑ t ∈ P, q t • treeFunction n t := by
    rw [treeOperator]
    apply Finsupp.sum_of_support_subset q hq
    intro t _
    simp
  have hRho_repr (q : TreeCoefficients n) (hq : q.support ⊆ P) :
      treeRho n q = ∑ t ∈ P,
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |q t| := by
    rw [treeRho]
    apply Finsupp.sum_of_support_subset q hq
    intro t _
    simp
  have hToplim : Tendsto (fun m ↦ treeOperator n (U (θ m))) atTop
      (nhds (treeOperator n u)) := by
    have hsum : Tendsto
        (fun m ↦ ∑ t ∈ P, U (θ m) t • treeFunction n t) atTop
        (nhds (∑ t ∈ P, u t • treeFunction n t)) :=
      tendsto_finsetSum P fun t _ ↦ (hcoordlim t).smul_const (treeFunction n t)
    rw [hTop_repr u huSupport]
    apply tendsto_congr' _ |>.mpr hsum
    exact Filter.Eventually.of_forall fun m ↦ hTop_repr (U (θ m)) (hUsupport (θ m))
  have hRholim : Tendsto (fun m ↦ treeRho n (U (θ m))) atTop
      (nhds (treeRho n u)) := by
    have hsum : Tendsto
        (fun m ↦ ∑ t ∈ P,
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |U (θ m) t|) atTop
        (nhds (∑ t ∈ P,
          (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |u t|)) :=
      tendsto_finsetSum P fun t _ ↦ tendsto_const_nhds.mul (hcoordlim t).abs
    rw [hRho_repr u huSupport]
    apply tendsto_congr' _ |>.mpr hsum
    exact Filter.Eventually.of_forall fun m ↦ hRho_repr (U (θ m)) (hUsupport (θ m))
  have hurho : treeRho n u ≤ 2 + ε := by
    apply le_of_tendsto hRholim
    exact Filter.Eventually.of_forall fun m ↦ (hUrho (θ m)).le
  have htransient_subseq (χ : ℕ → ℕ) (hχ : Function.Injective χ)
      (z : BoundedContinuousFunction (TreeProduct n) ℝ) (hz : 0 ≤ z)
      (hzlower : ∀ k, z ≤ treeOperator n (V (χ k))) : z = 0 := by
    have hsub : ∀ B ∉ Λ,
        {k | (treeBandProjection n B (W (χ k))).support.Nonempty}.Subsingleton := by
      intro B hB i hi j hj
      exact hχ (hthinW B hB hi hj)
    have htr := (tree_transient n (fun k ↦ W (χ k)) Λ hnoneΛ hsub).2
    apply htr z hz
    intro k
    change z ≤ treeOperator n
      (W (χ k) - finiteBandProjection n Λ (W (χ k)))
    exact hzlower k
  refine ⟨u, hupos, ?_, hurho⟩
  intro j α
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp hToplim) η hη
  let K : ℕ := max j m₀
  let χ : ℕ → ℕ := fun k ↦ θ (k + K)
  have hχ : Function.Injective χ := hθ.injective.comp fun a b hab ↦ by
    omega
  have hclose (k : ℕ) :
      ‖treeOperator n (U (χ k)) - treeOperator n u‖ < η := by
    have hk : m₀ ≤ k + K := le_trans (le_max_right j m₀) (Nat.le_add_left K k)
    have := hm₀ (k + K) hk
    rw [dist_eq_norm_sub] at this
    exact this
  have happrox (k : ℕ) :
      treeOperator n (U (χ k)) ≤ treeOperator n u +
        η • treeFunction n (TreeNode.root n) := by
    let d := treeOperator n (U (χ k)) - treeOperator n u
    have habs : |d| ≤ η • treeFunction n (TreeNode.root n) := by
      calc
        |d| ≤ ‖d‖ • treeFunction n (TreeNode.root n) :=
          abs_le_norm_smul_root n d
        _ ≤ η • treeFunction n (TreeNode.root n) := by
          intro β
          simpa [treeFunction_root] using (hclose k).le
    calc
      treeOperator n (U (χ k)) = d + treeOperator n u := by
        dsimp [d]
        abel
      _ ≤ |d| + treeOperator n u := add_le_add (le_abs_self d) le_rfl
      _ ≤ η • treeFunction n (TreeNode.root n) + treeOperator n u :=
        add_le_add habs le_rfl
      _ = treeOperator n u + η • treeFunction n (TreeNode.root n) := add_comm _ _
  let b : BoundedContinuousFunction (TreeProduct n) ℝ :=
    treeOperator n u + η • treeFunction n (TreeNode.root n)
  let z : BoundedContinuousFunction (TreeProduct n) ℝ := ((x j).1 - b)⁺
  have hzpos : 0 ≤ z := posPart_nonneg _
  have hzlower (k : ℕ) : z ≤ treeOperator n (V (χ k)) := by
    have hjχ : j ≤ χ k := by
      have hK : j ≤ k + K := le_trans (le_max_left j m₀) (Nat.le_add_left K k)
      exact hK.trans (hθ.id_le (k + K))
    have hxjχ := hxmono hjχ
    change (x j).1 ≤ (x (χ k)).1 at hxjχ
    have hxW : (x j).1 ≤ treeOperator n (W (χ k)) :=
      hxjχ.trans (hWdom (χ k))
    have hdecomp : treeOperator n (W (χ k)) =
        treeOperator n (U₀ (χ k)) + treeOperator n (V (χ k)) := by
      rw [← treeOperator_add]
      congr 1
      dsimp [V]
      abel
    have hup := (treeUpshift_basic n (U₀ (χ k)) (hU₀pos (χ k))).2
    have hmain : (x j).1 ≤ b + treeOperator n (V (χ k)) := by
      calc
        (x j).1 ≤ treeOperator n (W (χ k)) := hxW
        _ = treeOperator n (U₀ (χ k)) + treeOperator n (V (χ k)) := hdecomp
        _ ≤ treeOperator n (U (χ k)) + treeOperator n (V (χ k)) :=
          add_le_add hup le_rfl
        _ ≤ b + treeOperator n (V (χ k)) :=
          add_le_add (happrox k) le_rfl
    have hdiff : (x j).1 - b ≤ treeOperator n (V (χ k)) := by
      rw [sub_le_iff_le_add]
      simpa [add_comm] using hmain
    change ((x j).1 - b) ⊔ 0 ≤ treeOperator n (V (χ k))
    exact sup_le hdiff (treeOperator_nonneg n (V (χ k)) (hVpos (χ k)))
  have hz0 := htransient_subseq χ hχ z hzpos hzlower
  have hxb : (x j).1 ≤ b := by
    rw [← sub_nonpos]
    exact (le_posPart ((x j).1 - b)).trans_eq hz0
  have hpoint := hxb α
  simpa [b, treeFunction_root] using hpoint
end OrderClosures
