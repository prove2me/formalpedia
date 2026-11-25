-- Prove2me | solution 1 for PI.KerLat.PerPairProof.perPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:55:35.693353+00:00
-- url     : https://prove2.me/submissions/47581a1e-fb07-40b6-96af-c1165d10a8f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PeriodPairIndependence_IndepOfImNe
import Theorems.Thm_PI_KerLat_PerPairProof_indep_of_im_ne
import Theorems.Thm_PI_KerLat_PerPairProof_im_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ComplexConjugate
open scoped nonZeroDivisors
open PI PI.KerLat PI.KerLat.PerPairProof
namespace PI.KerLat.PerPairProof
theorem _root_.solution : PI.KerLat.PerPair := by
  intro K _ _ φ cc δ hK hφ hcc hδ
  classical
  let b0 := NumberField.RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, hK]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let bI : Module.Basis (Fin 2) ℤ cc := (Ideal.selfBasis b0 cc hcc).reindex e
  let f : cc →+ ℂ :=
    { toFun := fun c => δ * φ ((c : 𝓞 K) : K)
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  let ω : Fin 2 → ℂ := fun i => f (bI i)
  let g : cc →ₗ[ℤ] K :=
    ((algebraMap (𝓞 K) K).toAddMonoidHom.comp cc.subtype.toAddMonoidHom).toIntLinearMap
  have hg : LinearMap.ker g = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext (IsFractionRing.injective (𝓞 K) K hxy)
  have hliZ : LinearIndependent ℤ (fun i => ((bI i : 𝓞 K) : K)) :=
    bI.linearIndependent.map' g hg
  have hli : LinearIndependent ℚ (fun i => ((bI i : 𝓞 K) : K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 hliZ
  let B : Module.Basis (Fin 2) ℚ K :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hBi : ∀ i, B i = ((bI i : 𝓞 K) : K) := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hω : (conj (ω 0) * ω 1).im ≠ 0 := by
    have hB := im_ne φ hφ B
    rw [hBi, hBi] at hB
    have eq : conj (ω 0) * ω 1 =
        (Complex.normSq δ : ℂ) * (conj (φ ((bI 0 : 𝓞 K) : K)) * φ ((bI 1 : 𝓞 K) : K)) := by
      simp only [ω, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [Complex.normSq_eq_conj_mul_self, map_mul]
      ring
    rw [eq, Complex.im_ofReal_mul]
    exact mul_ne_zero (Complex.normSq_pos.2 hδ).ne' hB
  refine ⟨⟨ω 0, ω 1, indep_of_im_ne hω⟩, ?_⟩
  show (Submodule.span ℤ {ω 0, ω 1}).toAddSubgroup = _
  rw [← AddSubgroup.toIntSubmodule_closure]
  first
  | rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
  | change AddSubgroup.closure {ω 0, ω 1} = _
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro w (rfl | rfl)
    · exact ⟨bI 0, (bI 0).2, rfl⟩
    · exact ⟨bI 1, (bI 1).2, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    have hfc : δ * φ (c : K) = f ⟨c, hc⟩ := rfl
    rw [hfc, ← bI.sum_repr ⟨c, hc⟩, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl
end PI.KerLat.PerPairProof
