-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_H_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:59.7387+00:00
-- url     : https://prove2.me/submissions/6a53e71a-7d76-4de4-a931-3794bc9eaeff

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : splitEH hirr χ ≠ ⊤ := by
  intro hH
  apply hχ
  apply MulChar.ext
  intro u
  have hm : (IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr).symm u ∈ splitEH hirr χ := by
    rw [hH]; exact Subgroup.mem_top _
  rw [splitEH, MonoidHom.mem_ker] at hm
  have := congrArg Units.val hm
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom] at this
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, Units.val_one] at this
  rw [this, MulChar.one_apply_coe]
end ReciprocityTheory.Cheb
