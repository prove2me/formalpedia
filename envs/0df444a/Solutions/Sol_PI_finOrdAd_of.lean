-- Prove2me | solution 1 for PI.finOrdAd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:34:02.804136+00:00
-- url     : https://prove2.me/submissions/2f4bfc0f-7d23-4b12-8b30-756088156ec7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicFiniteOrder_Assembly
import Theorems.Thm_PI_charpoly_int_of_powers_in_compact
import Theorems.Thm_PI_continuous_conj_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI
open NumberField IsDedekindDomain TensorProduct Matrix
namespace PI
theorem _root_.solution (hU : UnitKron) (hP : PowBddInt) (hT : TensCpctDen) (hD : DefPosDef) : FinOrdAd := by
  intro F E _ _ _ _ _ hreal σ k J hH hDef U _hUle hUc y _hy γ hγ hbc
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
  · obtain ⟨hc, hdef⟩ := hD F E hreal σ k J hk hH hDef
    obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.mp hbc
    have hint := charpoly_int_of_powers_in_compact hT hP F E k (γ : Matrix (Fin k) (Fin k) E)
      (⋃ (i : Fin k) (j : Fin k), (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
        ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) '' (U : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j => hUc.image (continuous_conj_entry F E k y i j))
      (by
        intro n i j
        have h1 : bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) (γ ^ n) = y * u ^ n * y⁻¹ := by
          rw [map_pow, ← hyu, ← map_pow]
          rfl
        refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, u ^ n, U.pow_mem hu n, ?_⟩⟩
        show ((y * u ^ n * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j = _
        rw [← h1, ← Units.val_pow_eq_pow_val]
        rfl)
    have hγ' : ((γ : Matrix (Fin k) (Fin k) E).map (σ : E →+* E))ᵀ * J * (γ : Matrix (Fin k) (Fin k) E) = J := hγ
    obtain ⟨n, hn, hpow⟩ := hU E (σ : E →+* E) hc k J γ hdef hγ' hint
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.ext (by rw [Units.val_pow_eq_pow_val, hpow]; simp)⟩
end PI
