-- Prove2me | solution 1 for PI.PinHostLoc.UnitaryGroupMassFormula.unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:00.80973+00:00
-- url     : https://prove2.me/submissions/701e76d8-d20a-40ba-85ff-9f086c3bc645

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PinHostLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalResidueCharacter_ResCharEq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_vF_eq
import Theorems.Thm_PI_PinHostLoc_UnitaryGroupMassFormula_natVal
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel WithZero
open PI PI.PinHostLoc PI.PinHostLoc.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
namespace PI.PinHostLoc.UnitaryGroupMassFormula
theorem _root_.solution {n : ℕ} (hn : ((n : ℕ) : 𝓞 F) ∉ p.asIdeal) :
    ∃ u : 𝒪[A.Fp], IsUnit u ∧ (u : A.Fp) = A.ιF ((n : ℕ) : F) := by
  have hw : p.valuation F ((n : ℕ) : F) = 1 := by
    rw [natVal]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hn
  have hv : ValuativeRel.valuation A.Fp (A.ιF ((n : ℕ) : F)) = 1 := by
    have h := (vF_eq A ((n : ℕ) : F) 1).mpr (by rw [hw, map_one])
    simp only [map_one] at h
    exact h
  have hmem : A.ιF ((n : ℕ) : F) ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, hv]
  refine ⟨⟨A.ιF ((n : ℕ) : F), hmem⟩, ?_, rfl⟩
  by_contra hu
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hu
  exact absurd hv (ne_of_lt hu)
end PI.PinHostLoc.UnitaryGroupMassFormula
