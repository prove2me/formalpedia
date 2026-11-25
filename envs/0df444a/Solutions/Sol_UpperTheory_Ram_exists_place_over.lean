-- Prove2me | solution 1 for UpperTheory.Ram.exists_place_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:16.729869+00:00
-- url     : https://prove2.me/submissions/a7c62d09-e9ff-4cec-be18-5188179849c3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_CondSq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Ram
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace UpperTheory.Ram
theorem _root_.solution (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal := by
  haveI : Fact p.Prime := ⟨hp⟩
  set pZ : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)}
  haveI : pZ.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨⟨P, hP, hl⟩⟩ := (inferInstance : Nonempty (pZ.primesOver (𝓞 E)))
  have hz : ((p : ℕ) : ℤ) ∈ Ideal.under ℤ P := by
    rw [← (Ideal.liesOver_iff P pZ).1 hl]
    exact Ideal.subset_span rfl
  have hmem : ((p : ℕ) : 𝓞 E) ∈ P := by simpa [Ideal.under] using hz
  have hnb : P ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  exact ⟨⟨P, hP, hnb⟩, hmem⟩
end UpperTheory.Ram
