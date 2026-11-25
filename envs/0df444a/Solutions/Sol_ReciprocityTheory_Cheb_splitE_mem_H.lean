-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_mem_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:33.36916+00:00
-- url     : https://prove2.me/submissions/b7a216b4-dd50-434b-899d-9a07e57b2d1f

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_autEquivPow_eq

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
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) (hm : χ (m : ZMod l) = 1) :
    σ ∈ splitEH hirr χ := by
  rw [splitEH, MonoidHom.mem_ker]
  apply Units.ext
  rw [MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  simp only [MulEquiv.coe_toMonoidHom, Units.val_one]
  rw [splitE_autEquivPow_eq hirr σ m hσ, hm]
end ReciprocityTheory.Cheb
