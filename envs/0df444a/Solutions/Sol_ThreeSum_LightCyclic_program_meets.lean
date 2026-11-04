-- Prove2me | solution 1 for ThreeSum.LightCyclic.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:22.130948+00:00
-- url     : https://prove2.me/submissions/e5367d88-0e26-4685-8016-eb02c5cbf60c

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_WeightedCache3SUM_Alias_e1f688d1cacb0f6f
import Theorems.Thm_ThreeSum_LightCyclic_program_procs
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs


set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    Meets lim program 0 d [2^k, a, b, prod, dst, work, p] μ (combinedTime k p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j)) :=
  correlation_meets rfl program_procs F H hw hpn hAseg hBseg hA hB
    haf hbf hpf hdf hsep hspace hword hd
end ThreeSum.LightCyclic
