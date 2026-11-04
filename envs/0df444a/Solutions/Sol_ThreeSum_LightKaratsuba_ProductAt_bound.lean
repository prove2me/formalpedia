-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.ProductAt.bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:20.114192+00:00
-- url     : https://prove2.me/submissions/a1afca5b-a88b-4b50-bc81-4521a12e17fe

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Definitions.Def_WeightedCache3SUM_Alias_fb87d121ace1c0e2


set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
namespace ProductAt
theorem _root_.solution {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ} {U : ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) :
    ∀ j < 2 * n, |μ (out + j)| ≤ 2 * (n : ℤ) * U ^ 2 := by
  intro j hj
  rw [hp j hj]
  exact product_coeff_bound ha hb hA hB j
end ProductAt
end ThreeSum.LightKaratsuba
