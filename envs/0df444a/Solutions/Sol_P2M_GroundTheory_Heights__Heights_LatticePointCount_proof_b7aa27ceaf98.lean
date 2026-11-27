-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePointCount_proof_b7aa27ceaf98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:01.475319+00:00
-- url     : https://prove2.me/submissions/3a669489-eb42-4116-ae05-3022baf3e034

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_closedBall_le_45191c17be59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_card_mul_volume_le_d74be91004af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_fundamentalDomain_eq_9e5c19851b44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_det_gram_eq_sq_b3d628168b4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_exists_near_9e6247090531

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount
namespace GroundTheory.Heights₂.Heights.LatticePointCount
theorem _root_.solution : LatticePointCount.Statement := by
  intro V _ _ r b hb S C hC hS hspan
  classical
  set W := span ℝ (Set.range b) with hWdef
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  let bW : Basis (Fin r) ℝ W := Basis.span hb
  have hrank : finrank ℝ W = r := by rw [finrank_span_eq_card hb, Fintype.card_fin]
  let e : OrthonormalBasis (Fin r) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hrank)
  let φ : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) := e.repr
  let c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)) := bW.map φ.toLinearEquiv
  let g : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] V := W.subtype ∘ₗ φ.symm.toLinearEquiv.toLinearMap
  have hgc : ∀ i, g (c i) = b i := by
    intro i
    simp [g, c, bW]
    exact Basis.coe_span_apply hb i
  have hgnorm : ∀ y, ‖g y‖ = ‖y‖ := by
    intro y
    exact φ.symm.norm_map y
  have hginj : Function.Injective g := by
    intro y z h
    have : ‖y - z‖ = 0 := by rw [← hgnorm, map_sub, h, sub_self, norm_zero]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hgspan : span ℤ (Set.range b) = (span ℤ (Set.range c)).map (g.restrictScalars ℤ) := by
    have hcomp : (⇑(g.restrictScalars ℤ) ∘ ⇑c) = b := funext hgc
    rw [Submodule.map_span, ← Set.range_comp, hcomp]
  have hset : {x : V | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ 1} =
      g '' {y | y ∈ span ℤ (Set.range c) ∧ ‖y‖ ≤ 1} := by
    ext x
    rw [hgspan]
    constructor
    · rintro ⟨hx, hx1⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
      exact ⟨y, ⟨hy, by rw [← hgnorm]; exact hx1⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
      exact ⟨Submodule.mem_map.2 ⟨y, hy, rfl⟩, by rw [hgnorm]; exact hy1⟩
  have hcov : ∀ y, ∃ l ∈ span ℤ (Set.range c), ‖y - l‖ ≤ r * C := by
    intro y
    obtain ⟨l, hl, hly⟩ := exists_near b hb S C hS hspan (g y) (φ.symm y).2
    rw [hgspan] at hl
    obtain ⟨l', hl', rfl⟩ := Submodule.mem_map.1 hl
    refine ⟨l', hl', ?_⟩
    rw [← hgnorm, map_sub]
    exact hly
  have hgram : (Matrix.of fun i j ↦ @inner ℝ V _ (b i) (b j)) =
      Matrix.of fun i j ↦ @inner ℝ _ _ (c i) (c j) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [← hgc i, ← hgc j]
    exact φ.symm.inner_map_map (c i) (c j)
  set d := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det c with hd
  have hd0 : 0 < |d| := abs_pos.2 ((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.isUnit_det c).ne_zero
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  have hR : 0 ≤ 1 + r * C := by linarith
  have hK : 0 < (2 * (1 + r * C)) ^ r := pow_pos (by linarith) r
  have hbound : ∀ X : Finset (EuclideanSpace ℝ (Fin r)),
      (∀ x ∈ X, x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ 1) → (X.card : ℝ) * |d| ≤ (2 * (1 + r * C)) ^ r := by
    intro X hX
    have h := (card_mul_volume_le c hcov X hX).trans (volume_closedBall_le r hR)
    rw [volume_fundamentalDomain_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_pow (by linarith)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hK.le).1 h
  have hfin : {y | y ∈ span ℤ (Set.range c) ∧ ‖y‖ ≤ 1}.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈(2 * (1 + r * C)) ^ r / |d|⌉₊ + 1)
    have h := hbound t (fun x hx => ht hx)
    rw [htc] at h
    have h2 : (2 * (1 + r * C)) ^ r / |d| < ((⌈(2 * (1 + r * C)) ^ r / |d|⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    rw [div_lt_iff₀ hd0] at h2
    linarith
  refine ⟨hset ▸ hfin.image g, ?_⟩
  rw [hset, Set.ncard_image_of_injective _ hginj, hgram, det_gram_eq_sq, Set.ncard_eq_toFinset_card _ hfin]
  have hN := hbound hfin.toFinset (fun x hx => (Set.Finite.mem_toFinset hfin).1 hx)
  have hNpos : (0 : ℝ) < hfin.toFinset.card := by
    have h0 : (0 : EuclideanSpace ℝ (Fin r)) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨zero_mem _, by simp⟩
    exact_mod_cast Finset.card_pos.2 ⟨0, h0⟩
  have hlog : Real.log hfin.toFinset.card ≤ Real.log ((2 * (1 + r * C)) ^ r / |d|) :=
    Real.log_le_log hNpos ((le_div_iff₀ hd0).2 hN)
  rw [Real.log_div hK.ne' hd0.ne', Real.log_pow, Real.log_abs] at hlog
  rw [Real.log_pow]
  push_cast at hlog ⊢
  linarith
end GroundTheory.Heights₂.Heights.LatticePointCount
