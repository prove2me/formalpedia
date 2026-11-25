-- Prove2me | solution 1 for PI.WAU.lamAf_le_ohatL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:37:58.654025+00:00
-- url     : https://prove2.me/submissions/dcad36eb-f2bc-4b4d-8524-9b4c39cd1445

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Theorems.Thm_PI_WAU_smul_ohatL
import Theorems.Thm_PI_WAU_ohat_one


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
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨1, ohat_one, (l : Fin n → E), l.2, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul a x _ hx => exact smul_ohatL L a.2 x hx
end PI.WAU
