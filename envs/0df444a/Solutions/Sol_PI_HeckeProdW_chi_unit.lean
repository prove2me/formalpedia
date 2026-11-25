-- Prove2me | solution 1 for PI.HeckeProdW.chi_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:29.23344+00:00
-- url     : https://prove2.me/submissions/5d401038-462e-49cd-a1a6-23e035a32b5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_PvLocalSelf
import Theorems.Thm_PI_HeckeProdW_Phi_single
import Theorems.Thm_PI_HeckeProdW_exists_strictHenselian_absolutely_closed_local_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct
open PI PI.HeckeProdW
variable {L : Type} [Field L] [NumberField L]
namespace PI.HeckeProdW
theorem _root_.solution (χ : HChar L) (u : Ideles L) (h1 : (u : AdeleRing (𝓞 L) L).1 = 1)
    (h2 : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1)
    (h3 : ∀ v, (u : AdeleRing (𝓞 L) L).2 v ≠ 1 → χ.UnrAt v) : χ.1 u = 1 := by
  classical
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (u : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (h2 v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (h2 v)
  let y : Pu L := fun v => (hunit v).unit
  have hu : u = Phi L y := Units.ext (Prod.ext (h1.trans rfl) (Subtype.ext (funext fun v => rfl)))
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, if_pos hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  rw [hu, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Phi_single]
  by_cases hv : χ.UnrAt v
  · exact hv _ (h2 v)
  · have hv1 : (u : AdeleRing (𝓞 L) L).2 v = 1 := by
      by_contra h
      exact hv (h3 v h)
    have hx : Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom (y v) = 1 := Units.ext hv1
    rw [hx, map_one, map_one]
end PI.HeckeProdW
