-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.ProductAt.congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:23.639167+00:00
-- url     : https://prove2.me/submissions/0a81ef9b-ca1e-49fb-976f-dc7b8bd8aefc

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
namespace ProductAt
theorem _root_.solution {μ μ' : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs)
    (he : ∀ j < 2 * n, μ' (out + j) = μ (out + j)) :
    ProductAt μ' out n as bs := fun j hj => (he j hj).trans (hp j hj)
end ProductAt
end ThreeSum.LightKaratsuba
