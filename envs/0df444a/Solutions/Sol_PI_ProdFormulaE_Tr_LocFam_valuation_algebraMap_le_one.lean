-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.LocFam.valuation_algebraMap_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:05:42.646741+00:00
-- url     : https://prove2.me/submissions/ac44c7ca-fe36-4e79-a327-cef70ba5beeb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
import Theorems.Thm_P2M_PI_ProdFormulaE_Tr_valuation_natCast_le_one__3f84b4acff5c
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
namespace PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
private theorem isClosed_setOf_valuation_le_one {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : IsClosed {x : K | valuation K x ≤ 1} := by
  have h := IsValuativeTopology.isClosed_closedBall (R := K) (v := valuation K) 1
  first
  | (convert h using 3 with x; simp)
  | simpa [Valuation.restrict_le_one_iff] using h
  | simpa using h
end PI.ProdFormulaE.Tr
end
end

set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
namespace PI.ProdFormulaE.Tr
namespace LocFam
theorem _root_.solution (D : LocFam F ℓ ι) (i : ι) (c : ℚ_[ℓ]) (hc : ‖c‖ ≤ 1) :
    valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) c) ≤ 1 := by
  let c' : ℤ_[ℓ] := ⟨c, hc⟩
  change valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (c' : ℚ_[ℓ])) ≤ 1
  refine PadicInt.denseRange_natCast.induction_on c'
    (p := fun z : ℤ_[ℓ] => valuation (D.K i) (algebraMap ℚ_[ℓ] (D.K i) (z : ℚ_[ℓ])) ≤ 1) ?_ ?_
  · exact isClosed_setOf_valuation_le_one.preimage ((D.cont i).comp continuous_subtype_val)
  · intro n
    simpa using valuation_natCast_le_one' (K := D.K i) n
end LocFam
end PI.ProdFormulaE.Tr
