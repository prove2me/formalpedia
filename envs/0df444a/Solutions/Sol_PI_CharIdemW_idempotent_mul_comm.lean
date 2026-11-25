-- Prove2me | solution 1 for PI.CharIdemW.idempotent_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:10.546799+00:00
-- url     : https://prove2.me/submissions/828203f3-9945-4c28-b6fd-8e5befa06594

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Central
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory
namespace PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
private theorem charIdem_mul_single_one_comm (V : FDRep ℂ G) (h : G) :
    PI.CharIdem.charIdem V * MonoidAlgebra.single h (1 : ℂ) = MonoidAlgebra.single h (1 : ℂ) * PI.CharIdem.charIdem V := by
  unfold PI.CharIdem.charIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
  let e : G ≃ G := ⟨fun g => h⁻¹ * g * h, fun g => h * g * h⁻¹, fun g => by group, fun g => by group⟩
  refine Fintype.sum_equiv e _ _ (fun g => ?_)
  have he : h * e g = g * h := by
    show h * (h⁻¹ * g * h) = g * h
    group
  have hi : (e g)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹ := by
    show (h⁻¹ * g * h)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹
    group
  rw [he, hi, FDRep.char_conj]
end PI.CharIdemW
end

set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
namespace PI.CharIdemW
theorem _root_.solution (V : FDRep ℂ G) (x : MonoidAlgebra ℂ G) :
    charIdem V * x = x * charIdem V := by
  refine MonoidAlgebra.induction_on (motive := fun y => PI.CharIdem.charIdem V * y = y * PI.CharIdem.charIdem V) x ?_ ?_ ?_
  · intro g
    simpa [MonoidAlgebra.of_apply] using charIdem_mul_single_one_comm V g
  · intro a b ha hb
    rw [mul_add, add_mul, ha, hb]
  · intro r a ha
    rw [mul_smul_comm, smul_mul_assoc, ha]
end PI.CharIdemW
