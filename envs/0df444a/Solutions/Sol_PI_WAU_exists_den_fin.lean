-- Prove2me | solution 1 for PI.WAU.exists_den_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:11.798801+00:00
-- url     : https://prove2.me/submissions/1bc09b89-0c47-4a7e-bc83-63b998bcd9eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CoordTmulOneMul
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_SmulEqAlgebraMapMul
import Theorems.Thm_PI_WAU_exists_den
import Theorems.Thm_PI_WAU_intF_of_int

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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU
theorem _root_.solution {κ : Type} [Fintype κ] (f : κ → F) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IntF ((m : F) * f i) := by
  classical
  choose m hm a ha using fun i => exists_den (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have key : ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((c : 𝓞 F) * a i) := by
    rw [hc, Nat.cast_mul, map_mul, ← ha i, map_natCast]; ring
  rw [key]
  exact intF_of_int _
end PI.WAU
