-- Prove2me | solution 1 for PI.IsoDetW.Loc.isLat_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:35.584855+00:00
-- url     : https://prove2.me/submissions/edebdd85-ad19-4baa-b788-9c3ff6301b4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_SpanSingletonAlgebraMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LocalLat
import Theorems.Thm_P2M_PI_IsoDetW_Loc_algebraMap_ne_zero__6cbe823fda71
import Theorems.Thm_PI_IsoDetW_Loc_map_sc_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors R) K
namespace PI.IsoDetW.Loc
theorem _root_.solution (g : Matrix ι ι K) (hg : g.det ≠ 0) {A : Submodule R (ι → K)} (hA : IsLat A) :
    IsLat (A.map (g.mulVecLin.restrictScalars R)) := by
  obtain ⟨s, hs, hA1, hA2⟩ := hA
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset ((ι × ι) ⊕ (ι × ι))) (Sum.elim (fun p => g p.1 p.2) (fun p => g⁻¹ p.1 p.2))
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hg1 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g i j) :=
    fun i j => hd (Sum.inl (i, j)) (Finset.mem_univ _)
  have hg2 : ∀ i j, IsLocalization.IsInteger R ((d : R) • g⁻¹ i j) :=
    fun i j => hd (Sum.inr (i, j)) (Finset.mem_univ _)
  have had := algebraMap_ne_zero' (K := K) hd0
  have has := algebraMap_ne_zero' (K := K) hs
  refine ⟨s * d, mul_ne_zero hs hd0, ?_, ?_⟩
  · intro v hv
    have hu := map_sc_le g⁻¹ hd0 hg2 _ (Submodule.mem_map_of_mem (f := g⁻¹.mulVecLin.restrictScalars R) hv)
    rw [map_mul, mul_inv_cancel_right₀ had] at hu
    refine ⟨g⁻¹.mulVec v, hA1 hu, ?_⟩
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hg), Matrix.one_mulVec]
  · refine (Submodule.map_mono hA2).trans ((map_sc_le g hd0 hg1 _).trans ?_)
    rw [map_mul, mul_inv]
end PI.IsoDetW.Loc
