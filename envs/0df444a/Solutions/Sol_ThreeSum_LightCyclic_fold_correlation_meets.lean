-- Prove2me | solution 1 for ThreeSum.LightCyclic.fold_correlation_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:28.928567+00:00
-- url     : https://prove2.me/submissions/f30b1bcd-f29e-4718-8e22-316855eebd5d

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_ThreeSum_LightCyclic_fold_meets
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Definitions.Def_WeightedCache3SUM_Alias_b64063ffc0d0e625
import Theorems.Thm_ThreeSum_CyclicFold_vector_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution {pLinear : ℕ}
    (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (hprod : ProductAt μ src n (padTo n (vector p F))
      (padTo n (vector p (fun z => H (-z)))))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧ SameOutside μ μ' dst p := by
  apply (fold_meets hLinear hw hpn hsrc hdst hsep
    (le_of_eq (vector_length _ _)) (le_of_eq (vector_length _ _)) hA hB hprod hword).mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr]
  exact cyclic_correlation F H r hr
end ThreeSum.LightCyclic
