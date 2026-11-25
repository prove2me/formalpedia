-- Prove2me | solution 1 for ReciprocityTheory.Cheb.eq_one_of_restrict_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:42.30485+00:00
-- url     : https://prove2.me/submissions/9817efc2-247f-4ce5-82aa-d84c9ca43a49

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix

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
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (h : Gal(M/ℚ)) (hK : AlgEquiv.restrictNormal h K = 1) (h1 : h ζ = ζ) : h = 1 := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := K) hζ
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  have hx : x ∈ Algebra.adjoin K ({ζ} : Set M) := htop ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h1
  | algebraMap r =>
    have := AlgEquiv.restrictNormal_commutes h K r
    rw [hK, AlgEquiv.one_apply] at this
    exact this.symm
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]
end ReciprocityTheory.Cheb
