-- Prove2me | solution 1 for PI.CompDegEF.locDegOf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:34.201817+00:00
-- url     : https://prove2.me/submissions/e53a17bc-7945-4967-a7bb-fae21468f9e6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_DenseSurj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_MemSpanLIff
import Theorems.Thm_PI_CompDegEF_mem_span_l_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
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
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution (hB : BallCard) (hD : DenseSurj) (hK : KerProp) (hN : NormCard) :
    LocDegOf := by
  intro l hl E _ _ φ K hφK hdense v hv hφv
  let ψ : 𝓞 E →+* ↥(ball K) :=
    { toFun := fun x => ⟨⟨φ (x : E), hφK _⟩, (hφv x).1⟩
      map_one' := Subtype.ext <| Subtype.ext <| by simp
      map_mul' := fun a b => Subtype.ext <| Subtype.ext <| by simp
      map_zero' := Subtype.ext <| Subtype.ext <| by simp
      map_add' := fun a b => Subtype.ext <| Subtype.ext <| by simp }
  let q := (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ↥(ball K))})).comp ψ
  have hsurj : Function.Surjective q := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hD l E φ K hφK hdense ((y : ↥K.1) : Om l) (y : ↥K.1).2 y.2
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ψ x) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq, mem_span_l_iff]
    have hc : (((ψ x - y : ↥(ball K)) : ↥K.1) : Om l) = φ (x : E) - ((y : ↥K.1) : Om l) := rfl
    rw [hc, norm_sub_rev]
    exact hx
  have hker : RingHom.ker q = v.asIdeal ^ v.asIdeal.ramificationIdx ℤ := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (ψ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_span_l_iff K (ψ x)).trans (hK l E φ v hv hφv x)
  have hcard : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Nat.card (↥(ball K) ⧸ Ideal.span {((l : ℕ) : ↥(ball K))}) := by
    rw [← hker]
    exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
  rw [hN l E v hv, hB l K] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm
end PI.CompDegEF
