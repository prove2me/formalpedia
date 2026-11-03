-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P18.generalizedRelativeEntropy_swapCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-02T20:57:24.075051+00:00
-- url     : https://prove2.me/submissions/e9897fe6-f0da-4292-88f1-dae9214f6c58

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

open Matrix

/-- Reindexing a square matrix as a real star-algebra equivalence. -/
def grs_reindexStar {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℝ] Matrix n n ℂ :=
  { reindexAlgEquiv ℝ ℂ e with
    map_smul' := fun r M => map_smul (reindexAlgEquiv ℝ ℂ e) r M
    map_star' := fun M => by
      simp [reindexAlgEquiv, reindexRingEquiv, star_eq_conjTranspose] }

theorem grs_reindexStar_apply {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m ℂ) : grs_reindexStar e M = reindex e e M := rfl

theorem grs_cfc_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (f : ℝ → ℝ) (M : Matrix m m ℂ) :
    cfc f (reindex e e M) = reindex e e (cfc f M) := by
  set φ := grs_reindexStar e
  have hφ : ∀ N, reindex e e N = φ N := fun N => rfl
  rw [hφ, hφ]
  have hsp : spectrum ℝ (φ M) = spectrum ℝ M := AlgEquiv.spectrum_eq φ M
  by_cases ha : IsSelfAdjoint M
  · have ha' : IsSelfAdjoint (φ M) := ha.map φ
    by_cases hf : ContinuousOn f (spectrum ℝ M)
    · have hcont : Continuous φ := by
        change Continuous (fun N : Matrix m m ℂ => reindex e e N)
        exact continuous_id.matrix_reindex e e
      exact (StarAlgHomClass.map_cfc (S := ℝ) φ f M hf hcont ha ha').symm
    · rw [cfc_apply_of_not_continuousOn _ hf, cfc_apply_of_not_continuousOn _ (hsp ▸ hf), map_zero]
  · have ha' : ¬ IsSelfAdjoint (φ M) := by
      intro h; apply ha
      have := h.map φ.symm
      simpa using this
    rw [cfc_apply_of_not_predicate _ ha, cfc_apply_of_not_predicate _ ha', map_zero]

theorem grs_trace_reindex {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (M : Matrix m m ℂ) :
    (reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, reindex_apply, submatrix_apply, diag_apply]
  exact e.symm.sum_comp (fun j => M j j)

theorem grs_ker_reindex {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (X Y : Matrix m m ℂ) :
    LinearMap.ker (reindex e e Y).mulVecLin ≤ LinearMap.ker (reindex e e X).mulVecLin ↔
      LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin := by
  have key : ∀ (M : Matrix m m ℂ) (v : n → ℂ),
      reindex e e M *ᵥ v = 0 ↔ M *ᵥ (v ∘ e) = 0 := by
    intro M v
    rw [reindex_apply, submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm]
    constructor
    · intro h; funext j
      have := congrFun h (e j); simpa using this
    · intro h; rw [h]; rfl
  constructor
  · intro h w hw
    simp only [LinearMap.mem_ker, mulVecLin_apply] at hw ⊢
    have h1 : reindex e e Y *ᵥ (w ∘ e.symm) = 0 := by
      rw [key]; simpa [Function.comp_def] using hw
    have h2 := h (show w ∘ e.symm ∈ LinearMap.ker (reindex e e Y).mulVecLin from h1)
    rw [LinearMap.mem_ker, mulVecLin_apply, key] at h2
    simpa [Function.comp_def] using h2
  · intro h v hv
    simp only [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
    rw [key] at hv ⊢
    exact h hv

/-- The finite-dimensional relative entropy is invariant under reindexing. -/
theorem grs_finiteRelativeEntropy_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (X Y : Matrix m m ℂ) :
    finiteRelativeEntropy (reindex e e X) (reindex e e Y) = finiteRelativeEntropy X Y := by
  unfold finiteRelativeEntropy
  by_cases hc : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin
  · rw [if_pos ((grs_ker_reindex e X Y).2 hc), if_pos hc, grs_cfc_reindex, grs_cfc_reindex]
    rw [← grs_trace_reindex e (cfc (fun x : ℝ => x * Real.log x) X - X * cfc Real.log Y + Y - X)]
    congr 3
    simp only [← grs_reindexStar_apply, map_sub, map_add, map_mul]
  · rw [if_neg (fun h => hc ((grs_ker_reindex e X Y).1 h)), if_neg hc]

theorem grs_main {I J : Type} (X Y : Matrix (I × J) (I × J) ℂ) :
    generalizedRelativeEntropy (swapCoeff X) (swapCoeff Y) = generalizedRelativeEntropy X Y := by
  unfold generalizedRelativeEntropy
  rw [← (Equiv.finsetCongr (Equiv.prodComm I J)).iSup_comp]
  refine iSup_congr fun t => ?_
  set s := Equiv.finsetCongr (Equiv.prodComm I J) t
  have hmem : ∀ a : I × J, a ∈ t ↔ Equiv.prodComm I J a ∈ s := by
    intro a; simp [s, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
  let e : t ≃ s := (Equiv.prodComm I J).subtypeEquiv hmem
  have hc : ∀ Z : Matrix (I × J) (I × J) ℂ,
      coordinateCompression s (swapCoeff Z) = reindex e e (coordinateCompression t Z) := by
    intro Z; ext i j
    rfl
  rw [hc, hc]
  convert grs_finiteRelativeEntropy_reindex e (coordinateCompression t X) (coordinateCompression t Y)

end QAlgorithms.Papers.Independent.Claimed50.P18

open QAlgorithms.Papers.Independent.Claimed50.P18 in
theorem solution {I J : Type} (X Y : Matrix (I × J) (I × J) ℂ) :
    generalizedRelativeEntropy (swapCoeff X) (swapCoeff Y) = generalizedRelativeEntropy X Y :=
  grs_main X Y
