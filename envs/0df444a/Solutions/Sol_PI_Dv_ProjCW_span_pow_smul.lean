-- Prove2me | solution 1 for PI.Dv.ProjCW.span_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:35.280677+00:00
-- url     : https://prove2.me/submissions/74ab5fd7-d234-4cf0-99e0-9b58aa84df06

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSpans_SpanPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjCW
open Formalism.BasicNotions NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjCW
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (F : ℕ) (N : Submodule (𝓞 K) V) :
    Submodule.span K ((((w.asIdeal ^ F) • N : Submodule (𝓞 K) V)) : Set V) =
      Submodule.span K (N : Set V) := by
  apply le_antisymm
  · exact Submodule.span_mono (Submodule.smul_le_right (I := w.asIdeal ^ F) (N := N))
  · obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hbF : b ^ F ∈ w.asIdeal ^ F := Ideal.pow_mem_pow hb F
    have hbF0 : (algebraMap (𝓞 K) K (b ^ F)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact pow_ne_zero F hb0
    rw [Submodule.span_le]
    intro n hn
    have h1 : (b ^ F) • n ∈ ((w.asIdeal ^ F) • N : Submodule (𝓞 K) V) := Submodule.smul_mem_smul hbF hn
    have h2 : n = (algebraMap (𝓞 K) K (b ^ F))⁻¹ • ((algebraMap (𝓞 K) K (b ^ F)) • n) := by
      rw [smul_smul, inv_mul_cancel₀ hbF0, one_smul]
    rw [SetLike.mem_coe, h2, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
end PI.Dv.ProjCW
