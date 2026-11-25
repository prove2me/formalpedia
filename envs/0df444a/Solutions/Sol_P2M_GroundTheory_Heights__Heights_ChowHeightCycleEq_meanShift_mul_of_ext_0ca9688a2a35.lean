-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_meanShift_mul_of_ext_0ca9688a2a35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:07:30.361631+00:00
-- url     : https://prove2.me/submissions/fe7e2157-cadf-4456-bbb2-c599b3542c6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_chowHt_sub_57687e4dc03a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_formNorm_one_star_7a2447a07dfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution (hA : ChowHeightMul.Statement) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] (j : K →+* L) (τ : L →+* ℂ) (hτ : ¬ ComplexEmbedding.IsReal τ)
    (σ : K →+* ℂ) (hσ : ComplexEmbedding.IsReal σ) (hτj : τ.comp j = σ)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    meanShift S σ (f * g) = meanShift S σ f + meanShift S σ g := by
  classical
  set w' := InfinitePlace.mk τ with hw'
  have hw'c : ¬ w'.IsReal := fun h => hτ (InfinitePlace.isReal_mk_iff.mp h)
  let T : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ := fun w => if w = w' then S else 1
  have hT : ∀ w, IsUnit (T w) := by
    intro w
    by_cases h : w = w'
    · simp only [T, if_pos h]; exact hS
    · simp only [T, if_neg h]; exact isUnit_one
  have hTr : ∀ w : InfinitePlace L, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u := by
    intro w hw u
    have : w ≠ w' := fun h => hw'c (h ▸ hw)
    simp only [T, if_neg this]
    exact formNorm_one_star u
  have h1 : ∀ w : InfinitePlace L, IsUnit ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w) :=
    fun _ => isUnit_one
  have h1r : ∀ w : InfinitePlace L, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w) (star u) =
        IndefiniteRowSideFullHecke.ArithBezout.formNorm ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w) u :=
    fun _ _ u => formNorm_one_star u
  have hconj : (ComplexEmbedding.conjugate τ).comp j = σ := by
    ext x
    have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hσ) x
    rw [ComplexEmbedding.conjugate_coe_eq] at h2
    rw [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, ← RingHom.comp_apply τ j, hτj, h2]
  have hmap : ∀ P : MvPolynomial (Fin (e + 1) × Fin n) K,
      map w'.embedding (map j P) = map σ P := by
    intro P
    rw [map_map]
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [hw', h, hτj]
    · rw [hw', h, hconj]
  have hdiff : ∀ (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ),
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) (map j P) δ -
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt
          (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w)
            (e + 1)) (map j P) δ =
        (w'.mult : ℝ) * meanShift S σ P / Height.totalWeight L := by
    intro P δ
    rw [chowHt_sub, Finset.sum_eq_single w']
    · simp only [T, if_pos rfl, hmap]
      rfl
    · intro w _ hw
      simp only [T, if_neg hw, sub_self, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hinj : Function.Injective (map j : MvPolynomial (Fin (e + 1) × Fin n) K → _) :=
    map_injective j j.injective
  have hF : map j f ≠ 0 := fun h => hf (hinj (by rw [h, map_zero]))
  have hG : map j g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have addT := additive_of_conjInv hA T hT hTr (map j f) (map j g) 0 0 hF hG
  have add1 := additive_of_conjInv hA _ h1 h1r (map j f) (map j g) 0 0 hF hG
  have hd1 := hdiff (f * g) 0
  have hd2 := hdiff f 0
  have hd3 := hdiff g 0
  rw [map_mul] at hd1
  simp only [add_zero] at addT add1
  have htw : (Height.totalWeight L : ℝ) ≠ 0 := by
    rw [NumberField.totalWeight_eq_finrank]
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hc : (w'.mult : ℝ) / Height.totalWeight L ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr InfinitePlace.mult_pos.ne') htw
  apply mul_left_cancel₀ hc
  have e1 : ∀ x : ℝ, (w'.mult : ℝ) / Height.totalWeight L * x =
      (w'.mult : ℝ) * x / Height.totalWeight L := fun x => by ring
  rw [mul_add, e1, e1, e1, ← hd1, ← hd2, ← hd3, addT, add1]
  ring
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
