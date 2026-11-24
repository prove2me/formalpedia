-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.Gl.not_mem_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:22:50.74302+00:00
-- url     : https://prove2.me/submissions/ab9a369a-3245-43e7-84ca-e69e315198d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.Gl
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {m g : ℕ} (h : Nat.Coprime m g) (hg : (g : 𝓞 F) ∈ v.asIdeal) : (m : 𝓞 F) ∉ v.asIdeal := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * (m : ℤ) + b * (g : ℤ) : ℤ) : 𝓞 F) = 1 := by rw [hab, Int.cast_one]
  rw [← h1]
  push_cast
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hm) (v.asIdeal.mul_mem_left _ hg)
end PI.UnitaryGroupMassFormula.ScXuExists.Gl
