-- Prove2me | solution 1 for ThreeSigma.Upper.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T17:10:23.218686+00:00
-- url     : https://prove2.me/submissions/436c9bf5-1632-4eed-a4b4-efc8fdc4982a

import Mathlib

section
/-!
# Spencer's discrepancy theorem: complete upper and lower bounds

Self-contained (relative to Mathlib) combination of the original
`SpencerUpperBound.lean` and `SpencerLowerBound.lean` sources.

Requested toolchain: `leanprover/lean4:v4.36.0-rc2`.
The sources were originally developed against Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The final two theorem declarations are:
* `Stoc393.theorem_1_1 : Stoc393.LowerBoundClaim`
* `Stoc393.theorem_1_2 : Stoc393.UpperBoundClaim`

The proofs needed by earlier corollaries are named
`Stoc393.lowerBoundClaim_proof` and `Stoc393.upperBoundClaim_proof`.
-/

/- BEGIN original module: Stoc393.Basic -/
section

/-! Definitions and the nearest-sign rounding argument (Lemma 3.2).
The norm on `Fin d → ℝ` is the maximum absolute coordinate norm.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.Basic -/

/- BEGIN original module: Stoc393.Targets -/
section

/-! Exact main targets. `UpperBound.lean` proves `UpperBoundClaim`;
`LowerBound.lean` proves `LowerBoundClaim`.
The lower-bound probability is represented by exact uniform counting of all
random replacement matrices. The all-signings event is the meaning of
`disc(A) > threshold`, without needing to choose a minimizer.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.Targets -/

/- BEGIN original module: Stoc393.CappedTrace -/
section

/-! The capped trace argument underlying Lemma 3.4.
The orthonormal-basis construction follows the proof in the PDF, with the
heavy/light decomposition also used in the earlier local Spencer3.lean file.
-/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

/-- Capped trace in a finite-dimensional real inner product space. -/
theorem capped_trace {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (w : ι → ℝ) (K L : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : 0 < K) (hL : 0 < L)
    (ha : ∀ i, ‖a i‖ ^ 2 ≤ K)
    (hq : ∀ v : E, L * ‖v‖ ^ 2 ≤ ∑ i, w i * (inner ℝ (a i) v) ^ 2) :
    (finrank ℝ E : ℝ) ≤ K / L * ∑ i, min (w i) (L / K) := by
  classical
  let c := L / K
  let H : Finset ι := Finset.univ.filter (fun i => c ≤ w i)
  have mem_H (i : ι) : i ∈ H ↔ c ≤ w i := by simp [H]
  have hsplit : (∑ i, min (w i) c) =
      (H.card : ℝ) * c + ∑ i ∈ Hᶜ, w i := by
    calc
      (∑ i, min (w i) c) = (∑ i ∈ H, c) + ∑ i ∈ Hᶜ, w i := by
        rw [← Finset.sum_add_sum_compl H (fun i => min (w i) c)]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          exact min_eq_right ((mem_H i).mp hi)
        · apply Finset.sum_congr rfl
          intro i hi
          have hi' : ¬ c ≤ w i := by simpa only [Finset.mem_compl, mem_H] using hi
          exact min_eq_left (le_of_lt (lt_of_not_ge hi'))
      _ = (H.card : ℝ) * c + ∑ i ∈ Hᶜ, w i := by simp
  let S : Submodule ℝ E := Submodule.span ℝ (↑(H.image a) : Set E)
  let W : Submodule ℝ E := Sᗮ
  have hSdim : finrank ℝ S ≤ H.card :=
    (finrank_span_finset_le_card (R := ℝ) (H.image a)).trans Finset.card_image_le
  have hdim_sum : finrank ℝ S + finrank ℝ W = finrank ℝ E :=
    S.finrank_add_finrank_orthogonal
  have hdim : (finrank ℝ E : ℝ) ≤ H.card + (finrank ℝ W : ℝ) := by
    exact_mod_cast (show finrank ℝ E ≤ H.card + finrank ℝ W by omega)
  let b := stdOrthonormalBasis ℝ W
  let u : Fin (finrank ℝ W) → E := fun j => (b j : E)
  have hu : Orthonormal ℝ u := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hheavy (i : ι) (hi : i ∈ H) (j : Fin (finrank ℝ W)) :
      inner ℝ (a i) (u j) = 0 := by
    apply S.inner_right_of_mem_orthogonal
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · exact (b j).property
  have hbessel (i : ι) : ∑ j, (inner ℝ (a i) (u j)) ^ 2 ≤ K := by
    have h := hu.sum_inner_products_le (a i) (s := Finset.univ)
    simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm] using h.trans (ha i)
  have hrow (i : ι) : (∑ j, w i * (inner ℝ (a i) (u j)) ^ 2) ≤
      if i ∈ H then 0 else K * w i := by
    by_cases hi : i ∈ H
    · simp [hi, hheavy i hi]
    · rw [if_neg hi, ← Finset.mul_sum]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbessel i) (hw i)
  have htrace : (finrank ℝ W : ℝ) * L ≤ K * ∑ i ∈ Hᶜ, w i := by
    calc
      (finrank ℝ W : ℝ) * L = ∑ j : Fin (finrank ℝ W), L := by simp
      _ ≤ ∑ j, ∑ i, w i * (inner ℝ (a i) (u j)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [hu.norm_eq_one j, one_pow, mul_one] using hq (u j)
      _ = ∑ i, ∑ j, w i * (inner ℝ (a i) (u j)) ^ 2 := Finset.sum_comm
      _ ≤ ∑ i, if i ∈ H then 0 else K * w i := Finset.sum_le_sum (fun i _ => hrow i)
      _ = K * ∑ i ∈ Hᶜ, w i := by
        calc
          (∑ i, if i ∈ H then 0 else K * w i) =
              ∑ i, if i ∈ Hᶜ then K * w i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i ∈ H <;> simp [hi]
          _ = ∑ i ∈ Hᶜ, K * w i := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr (by ext i; simp)
            intro i _
            rfl
          _ = K * ∑ i ∈ Hᶜ, w i := (Finset.mul_sum _ _ _).symm
  have hcK : K * c = L := by dsimp [c]; field_simp
  have htotal : (finrank ℝ E : ℝ) * L ≤ K * ∑ i, min (w i) c := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right hdim hL.le]
  simpa only [div_mul_eq_mul_div] using (le_div_iff₀ hL).mpr htotal

/-- The same estimate for a subspace, using orthogonal projections of the rows. -/
theorem capped_trace_subspace {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (a : ι → E) (w : ι → ℝ) (K L : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : 0 < K) (hL : 0 < L)
    (ha : ∀ i, ‖a i‖ ^ 2 ≤ K)
    (hq : ∀ v : V, L * ‖v‖ ^ 2 ≤ ∑ i, w i * (inner ℝ (a i) (v : E)) ^ 2) :
    (finrank ℝ V : ℝ) ≤ K / L * ∑ i, min (w i) (L / K) := by
  apply capped_trace (fun i => V.orthogonalProjectionOnto (a i)) w K L hw hK hL
  · intro i
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (V.norm_orthogonalProjectionOnto_apply_le (a i)) |>.trans (ha i)
  · intro v
    simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] using hq v

end Stoc393

end
/- END original module: Stoc393.CappedTrace -/

/- BEGIN original module: Stoc393.ScalarReduction -/
section

/-! Algebraic implications surrounding the scalar inequality.
The comparison is an explicit hypothesis in this abstract reduction.
`ScalarBarrier.lean` proves it for the paper's concrete function.
-/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarReduction -/

/- BEGIN original module: Stoc393.ScalarCalculus -/
section

/-! Elementary scalar calculus from Appendix C.
No assertion of the unproved equation (27) is made in this module.
-/

set_option autoImplicit false

namespace Stoc393

open scoped Topology

end Stoc393

end
/- END original module: Stoc393.ScalarCalculus -/

/- BEGIN original module: Stoc393.ScalarPQ -/
section

/-! Analytic proof supplied by the user on 2026-10-30: the P + Q estimates. -/

open scoped BigOperators
set_option autoImplicit false
namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarPQ -/

/- BEGIN original module: Stoc393.ScalarBarrier -/
section

/-! Equation (27), completing the analytic argument supplied by the user.
The proof uses exact real inequalities and algebra, not sampled values.
-/

set_option autoImplicit false
namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.ScalarBarrier -/

/- BEGIN original module: Stoc393.SecondVariation -/
section

/-! The second variation of the reciprocal-sinh potential, Lemma 3.5.
The abstract curve rule adapts the checked local Spencer3.lean construction.
-/

open scoped Topology BigOperators
open Filter
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.SecondVariation -/

/- BEGIN original module: Stoc393.PotentialCompact -/
section

/-! The extended-real barrier, including its infinite boundary values, and compact minimization. -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.PotentialCompact -/

/- BEGIN original module: Stoc393.FaceTrace -/
section

/-! Capped trace after imposing the single orthogonality constraint on a cube face. -/

open scoped BigOperators
open Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.FaceTrace -/

/- BEGIN original module: Stoc393.MinimizerGeometry -/
section

/-! Feasible variations on cube faces and the contradiction at an interior minimizer. -/

open scoped Topology BigOperators ENNReal
open Filter Set Module
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.MinimizerGeometry -/

/- BEGIN original module: Stoc393.UpperBound -/
section

/-! Proposition 3.6 and the full upper bound (Theorems 1.2 and 3.1). -/

open scoped Topology BigOperators ENNReal
open Filter Set
set_option autoImplicit false

namespace Stoc393

end Stoc393

end
/- END original module: Stoc393.UpperBound -/

/- BEGIN original module: Stoc393.UpperCorollaries -/
section

/-! Discrepancy, the square-matrix bound, and its explicit numerical constants. -/

open scoped BigOperators
set_option autoImplicit false

namespace Stoc393

end Stoc393
end
end

section
namespace ThreeSigma.Upper

/-- Lemma 3.4 from the authors' weighted capped trace: rows normalised to unit length,
weights the squared row norms, `K = L = 1`. -/
theorem chk_lemma_3_4 {m n : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v ∈ V, ‖v‖ ^ 2 ≤ ∑ i, (inner ℝ (a i) v) ^ 2) :
    (Module.finrank ℝ V : ℝ) ≤ ∑ i, min (‖a i‖ ^ 2) (1 : ℝ) := by
  let b : Fin m → EuclideanSpace ℝ (Fin n) := fun i => ‖a i‖⁻¹ • a i
  let w : Fin m → ℝ := fun i => ‖a i‖ ^ 2
  have hb (i : Fin m) : ‖b i‖ ^ 2 ≤ 1 := by
    by_cases h : a i = 0
    · simp [b, h]
    · have : ‖b i‖ = 1 := by
        simp only [b, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)
      rw [this]; norm_num
  have hwb (i : Fin m) (v : EuclideanSpace ℝ (Fin n)) :
      w i * (inner ℝ (b i) v) ^ 2 = (inner ℝ (a i) v) ^ 2 := by
    by_cases h : a i = 0
    · simp [w, b, h]
    · have hn : ‖a i‖ ≠ 0 := norm_ne_zero_iff.mpr h
      simp only [w, b, inner_smul_left, RCLike.conj_to_real]
      field_simp
  have h := Stoc393.capped_trace_subspace V b w 1 1 (fun i => by positivity)
    one_pos one_pos hb (fun v => by
      simp only [one_mul, hwb]
      exact hV v v.2)
  simpa [w] using h

end ThreeSigma.Upper
end

theorem solution : type_of% @ThreeSigma.Upper.chk_lemma_3_4 := @ThreeSigma.Upper.chk_lemma_3_4
