-- Prove2me | solution 1 for P2M_PI_ProdFormulaE_Tr_LocFam___tmul_c045d1bf3d1e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:27.384803+00:00
-- url     : https://prove2.me/submissions/8e782c05-2f4b-4fec-9be2-1505eb4bd247

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
attribute [instance] LocFam.fld LocFam.vr LocFam.top LocFam.lf LocFam.cz LocFam.alg LocFam.fin
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
namespace PI.ProdFormulaE.Tr
namespace LocFam
theorem _root_.solution (D : LocFam F ℓ ι) (c : ℚ_[ℓ]) (x : F) (i : ι) :
    D.Φ (c ⊗ₜ x) i = algebraMap ℚ_[ℓ] (D.K i) c * D.ιF i x := by
  simp [LocFam.Φ, Algebra.ofId_apply]
end LocFam
end PI.ProdFormulaE.Tr
