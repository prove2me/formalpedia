-- Prove2me | solution 1 for PI.TameSurjW.liesOver_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:44.252694+00:00
-- url     : https://prove2.me/submissions/a194ca55-4473-4264-b023-4153c330119a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TameSurjectivity_RecUnram
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
noncomputable section
open NumberField IsDedekindDomain
open PI PI.TameSurjW
namespace PI.TameSurjW
theorem _root_.solution {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    P.LiesOver (Ideal.span {(p : ℤ)}) ↔ ((p : ℕ) : 𝓞 E) ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  constructor
  · intro h
    have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)})] at h1
    simpa using h1
  · intro h
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap]
    simpa using h
end PI.TameSurjW
