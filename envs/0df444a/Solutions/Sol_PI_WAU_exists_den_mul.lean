-- Prove2me | solution 1 for PI.WAU.exists_den_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:09.824979+00:00
-- url     : https://prove2.me/submissions/23ea12f3-9569-47ef-9903-d6128d276b9e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Theorems.Thm_PI_WAU_ohat_mul
import Theorems.Thm_PI_WAU_ohat_sum
import Theorems.Thm_PI_WAU_exists_den_fin
import Theorems.Thm_PI_WAU_smul_eq_algebraMap_mul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_coord_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
local notation "Af" => FiniteAdeleRing (𝓞 F) F
variable {b}
namespace PI.WAU
theorem _root_.solution (b : Module.Basis ι F E) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : E ⊗[F] Af, IntC b x → IntC b y → IntC b (m • (x * y)) := by
  obtain ⟨m, hm, h⟩ := exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨m, hm, fun x y hx hy k => ?_⟩
  rw [map_nsmul, coord_mul]
  simp only [Pi.smul_apply, Finset.smul_sum]
  refine ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_
  rw [smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]
  have h1 : (m : Af) * algebraMap F Af (b.repr (b i * b j) k) = algebraMap F Af ((m : F) * b.repr (b i * b j) k) := by
    simp
  rw [h1]
  exact ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))
end PI.WAU
