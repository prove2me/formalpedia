-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplMinkowskiBox_proof_64297bba648b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:08.477912+00:00
-- url     : https://prove2.me/submissions/dfa0990f-9a2d-4a9b-a2ba-a7b35c0c28c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinkowskiBox
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_neg_02d1831fe01a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_box_convex_189faa4f77e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinkowskiBox_volume_fundamentalDomain_basisFun_562ffd935c98

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
open Matrix MeasureTheory
open PSymplMinkowskiBox
namespace GroundTheory.Heights₂.Heights
namespace SymplMinkowskiBox
theorem _root_.solution (h1 : SymplBoxVolume.Statement) : SymplMinkowskiBox.Statement := by
  intro ι _ _ A a hdet ha hprod
  have hdet0 : A.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    exact zero_ne_one hdet
  set s : Set (ι → ℝ) := {x | ∀ i, |(A *ᵥ x) i| < a i} with hs
  have hvol : volume s = ENNReal.ofReal (2 ^ Fintype.card ι * ∏ i, a i) := by
    rw [hs, h1 ι A a hdet0 ha, hdet, div_one, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hP : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hbig : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) * 2 ^ Module.finrank ℝ (ι → ℝ) <
      volume s := by
    rw [volume_fundamentalDomain_basisFun, one_mul, Module.finrank_fintype_fun_eq_card, hvol,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact lt_mul_of_one_lt_right hP hprod
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)))
    infer_instance
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup)
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume)
    (fun y hy => box_neg A a y hy) (box_convex A a) hbig
  have hint : ∀ i, ∃ z : ℤ, (z : ℝ) = (x : ι → ℝ) i := by
    intro i
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ (x : ι → ℝ)).mp x.2 i
    exact ⟨z, by simpa using hz⟩
  choose v hv using hint
  have hxv : intVec v = (x : ι → ℝ) := funext hv
  refine ⟨v, ?_, fun i => ?_⟩
  · rintro rfl
    apply hx0
    ext i
    rw [← hv i]
    simp
  · rw [hxv]
    exact hxs i
end SymplMinkowskiBox
end GroundTheory.Heights₂.Heights
