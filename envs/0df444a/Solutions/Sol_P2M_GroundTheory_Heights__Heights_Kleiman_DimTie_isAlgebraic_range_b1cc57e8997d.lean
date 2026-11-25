-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_isAlgebraic_range_b1cc57e8997d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:41.212161+00:00
-- url     : https://prove2.me/submissions/bc42223b-dc44-4f48-a723-8c0cb52abbc9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution :
    Algebra.IsAlgebraic (dehom (k := k) y hi₀).range (Polynomial (ratioRing (k := k) y)) := by
  set R := (dehom (k := k) y hi₀).range
  have hmem : ∀ j, Polynomial.C (ratio (k := k) y hi₀ j) * Polynomial.X ∈ R :=
    fun j => ⟨X j, by simp [dehom]⟩
  have h1 : ratio (k := k) y hi₀ i₀ = 1 := Subtype.ext (div_self hi₀)
  have hX : IsAlgebraic R (Polynomial.X : Polynomial (ratioRing (k := k) y)) := by
    have h := hmem i₀
    rw [h1, Polynomial.C_1, one_mul] at h
    exact isAlgebraic_algebraMap (⟨_, h⟩ : R)
  have hb : ∀ j, IsAlgebraic R (Polynomial.C (ratio (k := k) y hi₀ j)) := fun j =>
    IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) hX
      (by rw [mul_comm]; exact isAlgebraic_algebraMap (⟨_, hmem j⟩ : R))
  have hgen : ∀ i j (hi : y i ≠ 0),
      IsAlgebraic R (Polynomial.C (⟨y j / y i, ratio_mem y hi j⟩ : ratioRing (k := k) y)) := by
    intro i j hi
    have hne : ratio (k := k) y hi₀ i ≠ 0 := fun h =>
      div_ne_zero hi hi₀ (congrArg Subtype.val h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (Polynomial.C_ne_zero.mpr hne))
      (hb i) ?_
    have he : ratio (k := k) y hi₀ i * ⟨y j / y i, ratio_mem y hi j⟩ = ratio (k := k) y hi₀ j := by
      apply Subtype.ext
      change y i / y i₀ * (y j / y i) = y j / y i₀
      field_simp
    rw [← Polynomial.C_mul, he]
    exact hb j
  have hCD : ∀ d : ratioRing (k := k) y, IsAlgebraic R (Polynomial.C d) := by
    let M : Subalgebra k (ratioRing (k := k) y) :=
      ((Subalgebra.algebraicClosure R (Polynomial (ratioRing (k := k) y))).restrictScalars k).comap
        (Polynomial.CAlgHom (R := k) (A := ratioRing (k := k) y))
    have hM : ratioRing (k := k) y ≤ M.map (ratioRing (k := k) y).val := Algebra.adjoin_le (by
      rintro _ ⟨i, j, hi, rfl⟩
      exact ⟨⟨y j / y i, ratio_mem y hi j⟩, hgen i j hi, rfl⟩)
    intro d
    obtain ⟨d', hd', he⟩ := hM d.2
    rw [show d = d' from Subtype.ext he.symm]
    exact hd'
  refine ⟨fun p => ?_⟩
  induction p using Polynomial.induction_on with
  | C a => exact hCD a
  | add p q hp hq => exact hp.add hq
  | monomial n a h => rw [pow_succ, ← mul_assoc]; exact h.mul hX
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
