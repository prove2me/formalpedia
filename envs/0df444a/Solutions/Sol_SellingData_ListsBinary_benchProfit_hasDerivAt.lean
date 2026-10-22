-- Prove2me | solution 1 for SellingData.ListsBinary.benchProfit_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:43.237876+00:00
-- url     : https://prove2.me/submissions/4661a157-948c-498f-97a6-140f040b5d68

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting
set_option autoImplicit false
open SellingData.ListsBinary

lemma jj_sv (φ α uLo uHi : ℝ) (hφ : 0 < φ) (hφ1 : φ < 1) (h0 : 0 < α) (h1 : α < 1) :
    sigmaH φ α * (phiH φ α * uHi + (1 - phiH φ α) * uLo)
      = φ * α * uHi + (1 - φ) * (1 - α) * uLo := by
  have hs : sigmaH φ α ≠ 0 := by
    have := mul_pos hφ h0
    have := mul_pos (sub_pos.2 hφ1) (sub_pos.2 h1)
    unfold sigmaH; linarith
  unfold phiH
  unfold sigmaH at hs ⊢
  field_simp
  ring

theorem solution (M : Model) (θi c a k' : ℝ)
    (ha : a ∈ Set.Ioo M.aLo M.aHi) (hk : HasDerivAt M.k k' a) :
    HasDerivAt (fun α => M.benchProfit θi c α)
      (θi * (M.phi * (M.uHi - c) - (1 - M.phi) * (M.uLo - c) - k')) a := by
  have h0 : 0 < a := by linarith [ha.1, M.half_lt_aLo]
  have h1 : a < 1 := by linarith [ha.2, M.aHi_lt_one]
  set C0 : ℝ := (1 - M.phi) * M.uLo - c * (1 - M.phi) with hC0
  set C1 : ℝ := M.phi * M.uHi - (1 - M.phi) * M.uLo - c * (M.phi - (1 - M.phi)) with hC1
  have hev : (fun α => θi * ((C0 + C1 * α) - M.k α)) =ᶠ[nhds a]
      (fun α => M.benchProfit θi c α) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with α hα
    have key := jj_sv M.phi α M.uLo M.uHi M.phi_pos M.phi_lt_one hα.1 hα.2
    simp only [Model.benchProfit, vH]
    unfold sigmaH at key ⊢
    simp only [hC0, hC1]
    linear_combination (-θi) * key
  have hd := ((((hasDerivAt_id' a).const_mul C1).const_add C0).sub hk).const_mul θi
  refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [hC1]
  ring
