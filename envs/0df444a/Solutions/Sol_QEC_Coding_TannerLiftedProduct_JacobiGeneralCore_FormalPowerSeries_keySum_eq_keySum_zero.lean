-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.keySum_eq_keySum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:54:54.320911+00:00
-- url     : https://prove2.me/submissions/04cc7880-7cf0-40c9-bcc6-0b60f864bad1

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_keySum_sub_keySum_succ

set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
theorem _root_.solution (k : ℕ) : keySum (R := R) k = keySum 0 := by
  -- `S_j - S_{j+1}` is divisible by `X ^ N` for every `N`, hence zero.
  have key : ∀ N j : ℕ, ∃ g : R⟦X⟧, keySum (R := R) j - keySum (j + 1) = X ^ N * g := by
    intro N
    induction N with
    | zero => exact fun j => ⟨_, (one_mul _).symm⟩
    | succ N ih =>
      intro j
      obtain ⟨g, hg⟩ := ih (j + 1)
      refine ⟨-(X ^ j * g), ?_⟩
      rw [keySum_sub_keySum_succ j, ← neg_sub (keySum (R := R) (j + 1)), hg]
      ring
  have hzero : ∀ j : ℕ, keySum (R := R) j = keySum (j + 1) := by
    intro j
    rw [← sub_eq_zero]
    ext d
    obtain ⟨g, hg⟩ := key (d + 1) j
    rw [hg, PowerSeries.coeff_X_pow_mul', if_neg (by omega), map_zero]
  induction k with
  | zero => rfl
  | succ k ih => rw [← hzero k, ih]
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
