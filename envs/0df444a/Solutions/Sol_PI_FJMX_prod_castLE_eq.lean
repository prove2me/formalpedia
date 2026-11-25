-- Prove2me | solution 1 for PI.FJMX.prod_castLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:16.266457+00:00
-- url     : https://prove2.me/submissions/948da0f7-70f8-4bca-9373-72630fe35f76

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m : ℕ}
namespace PI.FJMX
theorem _root_.solution {M : Type*} [CommMonoid M] {t : ℕ} (h : t ≤ m) (g : Fin m → M) :
    ∏ i : Fin t, g (Fin.castLE h i) = ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) := by
  classical
  have e1 : ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) =
      ∏ i : Fin m, (if i.val < t then g i else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  rw [e1, ← Finset.prod_filter]
  have e2 : (Finset.univ.filter fun i : Fin m => i.val < t) = Finset.univ.map (Fin.castLEEmb h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    · rintro ⟨a, -, rfl⟩
      simp
  rw [e2, Finset.prod_map]
  rfl
end PI.FJMX
