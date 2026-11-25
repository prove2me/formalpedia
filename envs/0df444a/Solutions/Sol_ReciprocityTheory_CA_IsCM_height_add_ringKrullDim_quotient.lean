-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.height_add_ringKrullDim_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:29.191092+00:00
-- url     : https://prove2.me/submissions/1afea353-bd48-4a9c-858b-d1a0a359e221

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Theorems.Thm_ReciprocityTheory_CA_length_le_height_of_isWeaklyRegular
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_associatedPrimes_eq_minimalPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_quotient_ofList
import Theorems.Thm_ReciprocityTheory_CA_IsCMMod_ringKrullDim_quotient_eq_supportDim
import Theorems.Thm_ReciprocityTheory_CA_IsCM_associatedPrimes_eq_minimalPrimes
import Theorems.Thm_ReciprocityTheory_CA_IsCM_exists_isRegular_of_le_height
import Theorems.Thm_ReciprocityTheory_CA_IsCM_quotient_ofList
import Theorems.Thm_ReciprocityTheory_CA_isCM_iff_isCMMod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
namespace IsCM
theorem _root_.solution (h : IsCM R) (P : Ideal R) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) = ringKrullDim R := by
  have hN : IsNoetherianRing R := h.1
  have hPt : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (P.height_ne_top hPt)
  obtain ⟨rs, hlen, hmem, hreg⟩ := h.exists_isRegular_of_le_height hPt hn.le
  have hmax : ∀ x ∈ rs, x ∈ maximalIdeal R := fun x hx => le_maximalIdeal hPt (hmem x hx)
  have hJP : Ideal.ofList rs ≤ P := by
    rw [Ideal.ofList, Ideal.span_le]; exact fun x hx => hmem x hx
  have hht : P.height ≤ (Ideal.ofList rs).height := by
    rw [(Ideal.ofList rs).height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun Q hQ => ?_
    have := hQ.isPrime
    rw [← hn, ← hlen]
    exact length_le_height_of_isWeaklyRegular Q
      (fun x hx => hQ.1.2 (Ideal.subset_span hx)) hreg.1
  have hPmin : P ∈ (Ideal.ofList rs).minimalPrimes := Ideal.mem_minimalPrimes_of_height_le hJP hht
  have hCM : IsCMMod R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) :=
    (isCM_iff_isCMMod.mp h).quotient_ofList hmax hreg
  have hJ : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := by simp
  have hann : Module.annihilator R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) =
      Ideal.ofList rs := by
    rw [hJ, Ideal.annihilator_quotient]
  have hass : P ∈ associatedPrimes R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) := by
    rw [hCM.associatedPrimes_eq_minimalPrimes, hann]; exact hPmin
  have e1 := hCM.ringKrullDim_quotient_eq_supportDim hass
  have e2 := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
  rw [Module.supportDim_self_eq_ringKrullDim] at e2
  rw [e1, ← e2, ← hn, ← hlen, add_comm]
  rfl
end IsCM
end ReciprocityTheory.CA
