-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_split_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:23.200777+00:00
-- url     : https://prove2.me/submissions/7b15a972-3b4d-4ba4-b430-57315555c207

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitE
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_count
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_two_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra E E') (k : ℕ), 2 ≤ k ∧
      ∀ q : Prm E, ¬ l ∣ Nrm q → χ ((Nrm q : ℕ) : ZMod l) = 1 →
        k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
  refine ⟨IntermediateField.fixedField (splitEH hirr χ), inferInstance, inferInstance, inferInstance,
    Module.finrank E (IntermediateField.fixedField (splitEH hirr χ)), splitE_two_le hirr χ hχ, ?_⟩
  intro q hl hq
  exact splitE_count hirr χ q hl hq _
    (fun x σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 x.2 σ hσ)
end ReciprocityTheory.Cheb
