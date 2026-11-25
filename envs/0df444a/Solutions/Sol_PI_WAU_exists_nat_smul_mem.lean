-- Prove2me | solution 1 for PI.WAU.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:16.507793+00:00
-- url     : https://prove2.me/submissions/f92b8572-2dd9-4305-8be3-ff695c669711

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Definitions.Def_Lemmata_GeneralBFactThirdMore_Key
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Theorems.Thm_P2M_Bl_general_b_fact_third__goal1_122fd7030837


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
namespace PI.WAU
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  first | exact Bl.general_b_fact_third'.goal1 .. | (apply Bl.general_b_fact_third'.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third'.goal1 <;> assumption)
end PI.WAU
