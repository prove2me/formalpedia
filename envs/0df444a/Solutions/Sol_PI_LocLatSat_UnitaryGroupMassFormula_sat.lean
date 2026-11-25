-- Prove2me | solution 1 for PI.LocLatSat.UnitaryGroupMassFormula.sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:54.314428+00:00
-- url     : https://prove2.me/submissions/9e7dfe13-d301-4aad-955d-8d07a458886c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_steps
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_baseChange_apply_baseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}
namespace PI.LocLatSat.UnitaryGroupMassFormula
theorem _root_.solution (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) (W : Submodule K (Fin n → K)) :
    (latG φ O (Λ ⊓ W.restrictScalars R) : Set (Fin n → S)) =
      (latG φ O Λ : Set (Fin n → S)) ∩ Submodule.span S (bcG φ '' (W : Set (Fin n → K))) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨?_, ?_⟩
    · exact Submodule.span_mono (Set.image_mono (fun v hv => hv.1)) hx
    · have hle : Submodule.span O (bcG φ '' ((Λ ⊓ W.restrictScalars R : Submodule R _) : Set (Fin n → K))) ≤
          (Submodule.span S (bcG φ '' (W : Set (Fin n → K)))).restrictScalars O := by
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact Submodule.subset_span ⟨v, hv.2, rfl⟩
      exact hle hx
  · rintro x ⟨hxΛ, hxW⟩

    let b := Module.Basis.ofVectorSpace K W.dualAnnihilator
    haveI : Fintype (Module.Basis.ofVectorSpaceIndex K W.dualAnnihilator) := Fintype.ofFinite _
    let g : Module.Basis.ofVectorSpaceIndex K W.dualAnnihilator → (Fin n → K) →ₗ[K] K := fun i => (b i : Module.Dual K _)
    have hg : ∀ i w, w ∈ W → g i w = 0 := by
      intro i w hw
      exact (Submodule.mem_dualAnnihilator _).mp (b i).2 w hw
    have h0 : ∀ i ∈ (Finset.univ : Finset _), fP φ (g i) x = 0 := by
      intro i _
      have hle : Submodule.span S (bcG φ '' (W : Set (Fin n → K))) ≤ LinearMap.ker (fP φ (g i)) := by
        rw [Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        show fP φ (g i) (bcG φ w) = 0
        rw [baseChange_apply_baseChange, hg i w hw, map_zero]
      exact hle hxW
    have hs := steps φ O g Λ hΛ hxΛ Finset.univ h0
    have hle2 : Λ ⊓ ⨅ i ∈ (Finset.univ : Finset _), (LinearMap.ker (g i)).restrictScalars R ≤
        Λ ⊓ W.restrictScalars R := by
      intro v hv
      refine ⟨hv.1, ?_⟩
      have hv2 : ∀ i, (b i : Module.Dual K (Fin n → K)) v = 0 := by
        intro i
        have h := (Submodule.mem_iInf _).mp ((Submodule.mem_inf.mp hv).2) i
        exact (Submodule.mem_iInf _).mp h (Finset.mem_univ i)
      show v ∈ W
      rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W), Submodule.mem_dualCoannihilator]
      intro ψ hψ
      have e := congrArg (fun d : W.dualAnnihilator => (d : Module.Dual K (Fin n → K)) v)
        (b.sum_repr ⟨ψ, hψ⟩)
      simp only at e
      rw [← e]
      rw [Submodule.coe_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Submodule.coe_smul, LinearMap.smul_apply, hv2, smul_zero]
    exact Submodule.span_mono (Set.image_mono hle2) hs
end PI.LocLatSat.UnitaryGroupMassFormula
