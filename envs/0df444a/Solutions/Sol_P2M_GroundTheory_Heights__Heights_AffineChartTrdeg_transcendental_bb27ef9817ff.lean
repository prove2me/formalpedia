-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_transcendental_bb27ef9817ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:19.557488+00:00
-- url     : https://prove2.me/submissions/f4252a03-d3f9-4145-a616-60940beb0bc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_exists_isHomogeneous_5524448663c0
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_sup
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AffineChartTrdeg
variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.AffineChartTrdeg
theorem _root_.solution (hP : IsHomogIdeal P) (j : Fin n) (hj : X j ∉ P) :
    Transcendental (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹))
      (genPt P j) := by
  classical
  set A' := Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)
  set ξ := genPt P
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))
  rintro ⟨p, hp, hpe⟩
  set N := p.natDegree + 1
  choose D hD using fun e => exists_isHomogeneous P j hξ (p.coeff e).2
  set M := (Finset.range N).sup D
  have hh : ∀ e, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous M ∧ aeval ξ h = (p.coeff e : _) * ξ j ^ M := by
    intro e
    by_cases he : e < N
    · exact hD e M (Finset.le_sup (Finset.mem_range.2 he))
    · refine ⟨0, isHomogeneous_zero _ _ _, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  choose h hhom heval using hh
  set G := ∑ e ∈ Finset.range N, h e * X j ^ e
  have hG : G ∈ P := by
    rw [← aeval_genPt_eq_zero_iff]
    have h0 : Polynomial.aeval (ξ j) p = ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
      rw [Polynomial.aeval_eq_sum_range]
      rfl
    calc aeval ξ G = ξ j ^ M * ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
          simp only [G, map_sum, map_mul, map_pow, aeval_X, heval, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by rw [← h0, hpe, mul_zero]
  have hcoeff : ∀ e < N, p.coeff e = 0 := by
    intro e he
    have hcomp : homogeneousComponent (M + e) G = h e * X j ^ e := by
      simp only [G, map_sum]
      rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self ((hhom e).mul (isHomogeneous_X_pow j e))
      · intro b _ hb
        rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
          ((hhom b).mul (isHomogeneous_X_pow j b))), if_neg (by omega)]
      · intro hne
        exact absurd (Finset.mem_range.2 he) hne
    have hmem : h e * X j ^ e ∈ P := hcomp ▸ hP G hG (M + e)
    have hhe : h e ∈ P := by
      rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h1 | h1
      · exact h1
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹_› e h1) hj
    have h2 := heval e
    rw [(aeval_genPt_eq_zero_iff P _).2 hhe, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd (pow_eq_zero_iff'.1 h2).1 hξ
  refine hp (Polynomial.ext fun e => ?_)
  by_cases he : e < N
  · simpa using hcoeff e he
  · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)
end GroundTheory.Heights₂.Heights.AffineChartTrdeg
