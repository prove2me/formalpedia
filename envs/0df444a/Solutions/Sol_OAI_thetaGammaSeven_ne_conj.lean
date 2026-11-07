-- Prove2me | solution 1 for OAI.thetaGammaSeven_ne_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:46:04.982818+00:00
-- url     : https://prove2.me/submissions/12ad2476-9b03-48c1-8f45-5b19d0e5080e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_thetaGammaSeven_cube
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end
end ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
private theorem nonreal_cube_ne_conj (γ z : ℂ) (hz : z ≠ 0)
    (hIm : z.im ≠ 0)
    (hc : γ ^ 3 = -z / (‖z‖ : ℂ)) : γ ≠ star γ := by
  intro hγ
  have hstar : star (γ ^ 3) = γ ^ 3 := by
    rw [star_pow, ← hγ]
  have hn : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hq : -(star z) / (‖z‖ : ℂ) = -z / (‖z‖ : ℂ) := by
    calc
      -(star z) / (‖z‖ : ℂ) = star (γ ^ 3) := by
        rw [hc, star_div₀]
        simp
      _ = γ ^ 3 := hstar
      _ = _ := hc
  have heq : star z = z := by
    have hh := (div_left_inj' hn).mp hq
    exact neg_injective hh
  exact hIm (Complex.conj_eq_iff_im.mp heq)
private theorem pSeven_embedding_im_ne_zero : (eisEmbedding pSeven).im ≠ 0 := by
  rw [pSeven, ActualEisensteinCubic.eisEmbedding_eval]
  have h : ((((1 : ℤ) : ℂ) + ((3 : ℤ) : ℂ) * omega3).im) = 3 * omega3.im := by
    simp
  rw [h]
  exact mul_ne_zero (by norm_num) omega3_im_ne_zero
open MulChar AddChar
namespace ShortDraftLocal
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftLocal
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
namespace OAI
theorem _root_.solution : thetaGammaSeven ≠ star thetaGammaSeven := by
  have hz : eisEmbedding pSeven ≠ 0 := by
    intro h
    have := pSeven_embedding_im_ne_zero
    rw [h] at this
    exact this rfl
  exact nonreal_cube_ne_conj thetaGammaSeven (eisEmbedding pSeven) hz
    pSeven_embedding_im_ne_zero thetaGammaSeven_cube
end OAI
