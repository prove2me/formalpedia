-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.exists_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:51.978814+00:00
-- url     : https://prove2.me/submissions/6f76bf5e-d411-4658-9a9a-c25e85fc776c

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
import Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_infinite_residueField
import Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_v_eq_one_of_residue_ne_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_eval_det_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
theorem _root_.solution [IsAlgClosed C] {ι σ T : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [Fintype T] (Q : T → Matrix ι σ C) (hQ : ∀ t i r, v (Q t i r) ≤ 1)
    (hsec : ∀ t, ∃ d : Matrix σ ι C, (∀ r i, v (d r i) ≤ 1) ∧ Q t * d = 1) :
    ∃ c : Matrix σ ι C, (∀ r i, v (c r i) ≤ 1) ∧ ∀ t, v (Q t * c).det = 1 := by
  classical
  haveI : Infinite (IsLocalRing.ResidueField v.valuationSubring) := infinite_residueField
  let QO : T → Matrix ι σ v.valuationSubring :=
    fun t i r => ⟨Q t i r, (v.mem_valuationSubring_iff _).mpr (hQ t i r)⟩
  let Qk : T → Matrix ι σ (IsLocalRing.ResidueField v.valuationSubring) :=
    fun t i r => IsLocalRing.residue v.valuationSubring (QO t i r)
  let p : T → MvPolynomial (σ × ι) (IsLocalRing.ResidueField v.valuationSubring) := fun t =>
    Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (Qk t i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) _))
  have hp : ∀ t, p t ≠ 0 := by
    intro t hzero
    obtain ⟨d, hd, hQd⟩ := hsec t
    let dO : Matrix σ ι v.valuationSubring :=
      fun r i => ⟨d r i, (v.mem_valuationSubring_iff _).mpr (hd r i)⟩
    have h1 := eval_det_gen (Qk t) (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))
    have h1' : MvPolynomial.eval (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))
        (p t) = _ := h1
    rw [hzero, map_zero] at h1'
    have hone : (Matrix.of fun i j => ∑ r, Qk t i r *
        IsLocalRing.residue v.valuationSubring (dO (r, j).1 (r, j).2)) = 1 := by
      ext i j
      have hij := congrFun (congrFun hQd i) j
      rw [Matrix.mul_apply] at hij
      have hO : ∑ r, QO t i r * dO r j = (1 : Matrix ι ι v.valuationSubring) i j := by
        apply Subtype.ext
        have hc : ((∑ r, QO t i r * dO r j : v.valuationSubring) : C) = ∑ r, Q t i r * d r j := by
          push_cast
          rfl
        rw [hc, hij]
        by_cases hij' : i = j
        · subst hij'
          simp
        · simp [Matrix.one_apply_ne hij']
      simp only [Matrix.of_apply, Qk]
      calc ∑ r, IsLocalRing.residue v.valuationSubring (QO t i r) *
            IsLocalRing.residue v.valuationSubring (dO r j)
          = IsLocalRing.residue v.valuationSubring (∑ r, QO t i r * dO r j) := by
            simp [map_sum, map_mul]
        _ = (1 : Matrix ι ι (IsLocalRing.ResidueField v.valuationSubring)) i j := by
            rw [hO]
            by_cases hij' : i = j
            · subst hij'; simp
            · simp [Matrix.one_apply_ne hij']
    rw [hone, Matrix.det_one] at h1'
    exact zero_ne_one h1'
  have hP : ∏ t, p t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hp t
  obtain ⟨z, hz⟩ : ∃ z, MvPolynomial.eval z (∏ t, p t) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_prod] at hz
  have hzt : ∀ t, MvPolynomial.eval z (p t) ≠ 0 :=
    fun t => (Finset.prod_ne_zero_iff.mp hz) t (Finset.mem_univ _)
  choose y hy using fun x : σ × ι => IsLocalRing.residue_surjective (z x)
  refine ⟨Matrix.of fun r i => (y (r, i) : C), fun r i => (y (r, i)).2, fun t => ?_⟩
  let cO : Matrix σ ι v.valuationSubring := fun r i => y (r, i)
  have hcoe : (Q t * Matrix.of fun r i => (y (r, i) : C)).det =
      v.valuationSubring.subtype (QO t * cO).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum,
      map_mul]
    rfl
  rw [hcoe]
  apply v_eq_one_of_residue_ne_zero
  rw [RingHom.map_det]
  have hzt' := hzt t
  have he : MvPolynomial.eval z (p t) =
      Matrix.det (Matrix.of fun i j => ∑ r, Qk t i r * z (r, j)) := eval_det_gen (Qk t) z
  rw [he] at hzt'
  have hmat : (IsLocalRing.residue v.valuationSubring).mapMatrix (QO t * cO) =
      Matrix.of fun i j => ∑ r, Qk t i r * z (r, j) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply,
      map_sum, map_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hy (r, j)]
  rw [hmat]
  exact hzt'
end ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
