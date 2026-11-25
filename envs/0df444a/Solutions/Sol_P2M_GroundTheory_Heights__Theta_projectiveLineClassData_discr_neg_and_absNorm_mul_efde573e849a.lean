-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_projectiveLineClassData_discr_neg_and_absNorm_mul_efde573e849a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:48.071862+00:00
-- url     : https://prove2.me/submissions/40edc733-0960-4330-87f0-1c4a633c9889

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_normSq_mul_det_2844130a5510
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
open EtaPeriodLatticeClass
namespace GroundTheory.Heights₂.Theta.projectiveLineClassData
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : FractionalIdeal (𝓞 K)⁰ K) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' (I : Set K)) = latticeOf (τ : ℂ)) :
    (discr K : ℝ) < 0 ∧
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2 = 2 * τ.im / Real.sqrt |(discr K : ℝ)| := by
  classical
  have hmem : ∀ x : K, x ∈ I → c * σ x ∈ latticeOf (τ : ℂ) := fun x hx => by
    rw [← himg]; exact ⟨σ x, ⟨x, hx, rfl⟩, rfl⟩
  have hpre : ∀ z ∈ latticeOf (τ : ℂ), ∃ x ∈ I, c * σ x = z := by
    intro z hz
    rw [← himg] at hz
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  obtain ⟨α, hαI, hα⟩ := hpre 1 (mem_latticeOf.mpr ⟨1, 0, by simp⟩)
  obtain ⟨β, hβI, hβ⟩ := hpre τ (mem_latticeOf.mpr ⟨0, 1, by simp⟩)
  have hcoord : ∀ x ∈ I, ∃ m n : ℤ, x = m * α + n * β := by
    intro x hx
    obtain ⟨m, n, hmn⟩ := mem_latticeOf.mp (hmem x hx)
    refine ⟨m, n, σ.injective (mul_left_cancel₀ hc ?_)⟩
    rw [hmn, map_add, map_mul, map_mul, map_intCast, map_intCast]
    linear_combination (-(m : ℂ)) * hα - (n : ℂ) * hβ
  have hind : ∀ m n : ℤ, (m : K) * α + n * β = 0 → m = 0 ∧ n = 0 := by
    intro m n h
    have h2 := congrArg (fun x => c * σ x) h
    simp only [map_add, map_mul, map_intCast, map_zero, mul_zero] at h2
    have h3 : (m : ℂ) + n * (τ : ℂ) = ((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * (τ : ℂ) := by
      push_cast
      linear_combination h2 - (m : ℂ) * hα - (n : ℂ) * hβ
    exact coord_unique h3
  let v : Fin 2 → (I : Submodule (𝓞 K) K) := ![⟨α, hαI⟩, ⟨β, hβI⟩]
  have hli : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    apply hind s t
    have := congrArg (fun y : (I : Submodule (𝓞 K) K) => (y : K)) hst
    simpa [zsmul_eq_mul] using this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨m, n, hxmn⟩ := hcoord x hx
    have h0 : v 0 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
    have h1 : v 1 ∈ Submodule.span ℤ (Set.range v) := Submodule.subset_span ⟨1, rfl⟩
    have := Submodule.add_mem _ (Submodule.smul_mem _ m h0) (Submodule.smul_mem _ n h1)
    convert this using 1
    ext
    simp [v, zsmul_eq_mul, hxmn]
  let bJ : Module.Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K) := Module.Basis.mk hli hsp
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, hK]
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) :=
    (RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq hcard)
  have habs := FractionalIdeal.abs_det_basis_change b I bJ
  set b₀ := b.localizationLocalization ℚ ℤ⁰ K
  set w : Fin 2 → K := (↑) ∘ bJ with hw
  have hw0 : w 0 = α := by simp [hw, bJ, v]
  have hw1 : w 1 = β := by simp [hw, bJ, v]
  have hdisc := Algebra.discr_of_matrix_vecMul (⇑b₀) (b₀.toMatrix w)
  rw [Module.Basis.toMatrix_map_vecMul, ← Module.Basis.det_apply, Algebra.discr_localizationLocalization ℤ ℤ⁰ K b,
    NumberField.discr_eq_discr K b] at hdisc
  have hemb := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ w (embEquiv hK σ hσ)
  rw [Matrix.det_fin_two] at hemb
  simp only [Algebra.embeddingsMatrixReindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, Algebra.embeddingsMatrix_apply, embEquiv,
    Equiv.ofBijective_apply, embPair, Matrix.cons_val_zero, Matrix.cons_val_one,
    RingHom.toRatAlgHom_apply, hw0, hw1, conjugate_coe_eq] at hemb
  have hX := normSq_mul_det c (σ α) (σ β) τ hα hβ
  rw [UpperHalfPlane.coe_im] at hX
  have hq : Algebra.discr ℚ w = (FractionalIdeal.absNorm I) ^ 2 * (discr K : ℚ) := by
    rw [hdisc, ← sq_abs, habs]
    simp
  have hC : ((‖c‖ ^ 2 : ℝ) : ℂ) ^ 2 *
      ((((FractionalIdeal.absNorm I : ℚ) : ℝ) : ℂ) ^ 2 * (((discr K : ℤ) : ℝ) : ℂ)) =
        ((-(4 * τ.im ^ 2) : ℝ) : ℂ) := by
    have h1 : ((‖c‖ ^ 2 : ℝ) : ℂ) ^ 2 *
        (σ α * (starRingEnd ℂ) (σ β) - (starRingEnd ℂ) (σ α) * σ β) ^ 2 =
          ((-(4 * τ.im ^ 2) : ℝ) : ℂ) := by
      rw [← mul_pow, hX]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [← h1, ← hemb, hq]
    simp only [map_mul, map_pow, eq_ratCast, Rat.cast_intCast]
    push_cast
    ring
  have hR : (‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) =
      -(4 * τ.im ^ 2) := by
    have := Complex.ofReal_injective (by push_cast at hC ⊢; exact hC :
      (((‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) : ℝ) : ℂ) =
        ((-(4 * τ.im ^ 2) : ℝ) : ℂ))
    exact this
  have hy := τ.im_pos
  have hN : 0 ≤ ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg I
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hD : (discr K : ℝ) < 0 := by
    by_contra h
    replace h := not_lt.mp h
    have : 0 ≤ (‖c‖ ^ 2) ^ 2 * (((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ 2 * (discr K : ℝ)) := by
      positivity
    nlinarith
  refine ⟨hD, ?_⟩
  have hsq : Real.sqrt |(discr K : ℝ)| ^ 2 = -(discr K : ℝ) := by
    rw [Real.sq_sqrt (abs_nonneg _), abs_of_neg hD]
  have hspos : 0 < Real.sqrt |(discr K : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr hD.ne)
  have key : Real.sqrt |(discr K : ℝ)| * (((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2) =
      2 * τ.im := by
    have h1 : (Real.sqrt |(discr K : ℝ)| * (((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2)) ^ 2 =
        (2 * τ.im) ^ 2 := by
      rw [mul_pow, hsq]
      linear_combination (-1 : ℝ) * hR
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  rw [eq_div_iff hspos.ne']
  linarith [key]
end GroundTheory.Heights₂.Theta.projectiveLineClassData
