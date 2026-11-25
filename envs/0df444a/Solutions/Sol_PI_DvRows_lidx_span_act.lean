-- Prove2me | solution 1 for PI.DvRows.lidx_span_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:47.431886+00:00
-- url     : https://prove2.me/submissions/6fd6c57a-a3ab-4706-bbad-4dd35a9c41ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_lidx_map_inj
import Theorems.Thm_PI_DvRows_combo_apply
import Theorems.Thm_Formalism_DivisionValues_indexChange_of_det_ne_zero
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_LatIdxDetW_neg_log_valuation
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
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.DvRows
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (y : Fin d → V)
    (hy : LinearIndependent K y) (P : Matrix (Fin d) (Fin d) K) (hP : P.det ≠ 0) :
    lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y))
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ k, P k j • y k)) = vAdd w P.det := by
  set E : Fin d → Fin d → K := fun i => Pi.single i 1 with hE
  have hEli : LinearIndependent K E := by
    convert (Pi.basisFun K (Fin d)).linearIndependent using 1
    funext i
    rw [Pi.basisFun_apply]
  have h1 := Formalism.DivisionValues.indexChange_of_det_ne_zero w P hP E hEli
  rw [← PI.LatIdxDetW.neg_log_valuation w hP] at h1
  set f : (Fin d → K) →ₗ[𝓞 K] V := (combo y).restrictScalars (𝓞 K) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h2 : combo y (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    rw [combo_apply] at h2
    have := (Fintype.linearIndependent_iff.1 hy) _ h2
    funext i
    exact sub_eq_zero.1 (this i)
  have hsat : ∀ (s : 𝓞 K) (v : V), s ∈ w.asIdeal.primeCompl → s • v ∈ LinearMap.range f →
      v ∈ LinearMap.range f := by
    intro s v hs hv
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by simpa using h0
      rw [this]; exact w.asIdeal.zero_mem
    obtain ⟨x, hx⟩ := hv
    refine ⟨(algebraMap (𝓞 K) K s)⁻¹ • x, ?_⟩
    show combo y ((algebraMap (𝓞 K) K s)⁻¹ • x) = v
    rw [map_smul]
    have hx' : combo y x = s • v := hx
    rw [hx', ← algebraMap_smul K s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hfE : ∀ i, f (E i) = y i := by
    intro i
    show combo y (Pi.single i 1) = y i
    rw [combo_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
  have hfA : ∀ j, f (Formalism.DivisionValues.idxChangeAct E P j) = ∑ k, P k j • y k := by
    intro j
    show combo y (∑ k, P k j • E k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    congr 1
    exact hfE k
  have e1 : Submodule.span (𝓞 K) (Set.range y) = (Submodule.span (𝓞 K) (Set.range E)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext v
    simp only [Set.mem_range, Function.comp_apply, hfE]
  have e2 : Submodule.span (𝓞 K) (Set.range fun j => ∑ k, P k j • y k) =
      (Submodule.span (𝓞 K) (Set.range (Formalism.DivisionValues.idxChangeAct E P))).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext v
    simp only [Set.mem_range, Function.comp_apply, hfA]
  rw [e1, e2, lidx_map_inj w.asIdeal f hfinj hsat, h1]
  rfl
end PI.DvRows
