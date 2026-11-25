-- Prove2me | solution 1 for ReciprocityTheory.Cheb.isArithFrobAt_restrictNormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:44.754936+00:00
-- url     : https://prove2.me/submissions/624d3e94-d5e6-4a75-ba8f-42d1ac17ccbc

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {K M : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field M] [NumberField M]
    [Algebra K M] (g : Gal(M/ℚ)) (p : ℕ) (P : Ideal (𝓞 M)) (hP : P.IsPrime)
    (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) (h : IsArithFrobAt ℤ g P) :
    (P.under (𝓞 K)).IsPrime ∧ (P.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormal g K) (P.under (𝓞 K)) := by
  refine ⟨Ideal.IsPrime.under _ _, ⟨by rw [Ideal.under_under]; exact hPp.over⟩, ?_⟩
  intro y
  have hu : (P.under (𝓞 K)).under ℤ = P.under ℤ := Ideal.under_under P
  have hc : algebraMap (𝓞 K) (𝓞 M) ((AlgEquiv.restrictNormal g K) • y) =
      g • algebraMap (𝓞 K) (𝓞 M) y := by
    apply NumberField.RingOfIntegers.ext
    exact AlgEquiv.restrictNormal_commutes g K (y : K)
  show _ ∈ Ideal.comap _ P
  rw [Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply, hu, map_sub, map_pow, hc]
  simpa using h (algebraMap (𝓞 K) (𝓞 M) y)
end ReciprocityTheory.Cheb
