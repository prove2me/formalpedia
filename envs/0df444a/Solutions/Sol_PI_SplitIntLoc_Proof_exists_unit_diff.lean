-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.exists_unit_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:45.608551+00:00
-- url     : https://prove2.me/submissions/214c3da8-5c36-4bd2-8369-2f153388ba56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_prime_fst_ne_prime_snd
import Theorems.Thm_PI_SplitIntLoc_Proof_prime_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ b : 𝓞 E, IsUnit (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b - phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b) := by
  have h1 : (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (prime_ne_bot spl hspl _ (fun _ => rfl))
  have h2 : (P spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (prime_ne_bot spl hspl _ (fun _ => rfl))
  have htop := Ideal.IsMaximal.coprime_of_ne h1 h2 (prime_fst_ne_prime_snd spl hspl)
  have h1mem : (1 : 𝓞 E) ∈ P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) ⊔ P spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1mem
  refine ⟨b, ?_⟩
  have hsum := congrArg (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))) hab
  rw [map_add, map_one] at hsum
  have heq : phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b - phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b =
      1 - (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) a + phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b) := by
    rw [← hsum]; ring
  rw [heq]
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [← IsLocalRing.mem_maximalIdeal]
  have ha' : phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := ha
  have hb' : phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := hb
  exact Ideal.add_mem _ ha' hb'
end PI.SplitIntLoc.Proof
