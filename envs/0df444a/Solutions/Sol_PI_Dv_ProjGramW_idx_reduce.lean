-- Prove2me | solution 1 for PI.Dv.ProjGramW.idx_reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:15.888663+00:00
-- url     : https://prove2.me/submissions/be6dc8a8-eede-420f-84b4-55518271dc26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_span_O_famC
import Theorems.Thm_PI_Dv_ProjGramW_idx_self
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} {b : Fin d → V}
    (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) (Set.range b)) (Submodule.span (𝓞 K) (Set.range (famC b C))) =
      idxStd w C := by
  classical
  set g : (Fin d →₀ K) →ₗ[K] V := Finsupp.linearCombination K b with hg
  have hgb : ∀ k, g (stdE d k) = b k := by
    intro k
    rw [hg]
    simp [stdE, Finsupp.linearCombination_single]
  have hker : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.mpr hb
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective g hker
  have hfg : ∀ x, f (g x) = x := fun x => by
    have := congrArg (fun (m : (Fin d →₀ K) →ₗ[K] (Fin d →₀ K)) => m x) hf
    simpa using this
  have hfb : ∀ k, f (b k) = stdE d k := fun k => by rw [← hgb k, hfg]
  have hfC : ∀ j, f (famC b C j) = famC (stdE d) C j := fun j => by
    simp only [famC, map_sum, map_smul, hfb]
  set M := Submodule.span (𝓞 K) (Set.range b) with hM
  set N := Submodule.span (𝓞 K) (Set.range (famC b C)) with hN
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span K (M : Set V) = Submodule.span K (N : Set V) :=
    (span_O_famC b C hC).symm
  have h3 := (hI K V w M N hMfg hNfg hsp).2.2.1 (Fin d →₀ K) f

  have hrange : ∀ (u : Fin d → V), (∀ k, u k ∈ LinearMap.range g) →
      Submodule.span (𝓞 K) (Set.range u) ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) = ⊥ := by
    intro u hu
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hle : Submodule.span (𝓞 K) (Set.range u) ≤ (LinearMap.range g).restrictScalars (𝓞 K) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hu k
    obtain ⟨y, rfl⟩ := hle hx1
    have : f (g y) = 0 := hx2
    rw [hfg] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  have hk1 : M ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) = ⊥ :=
    hrange b fun k => ⟨stdE d k, hgb k⟩
  have hk2 : N ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) = ⊥ := by
    refine hrange _ fun j => ⟨famC (stdE d) C j, ?_⟩
    simp only [famC, map_sum, map_smul, hgb]
  have hm1 : M.map (f.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)) := by
    rw [hM, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    exact hfb k
  have hm2 : N.map (f.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range (famC (stdE d) C)) := by
    rw [hN, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    exact hfC k
  rw [h3, hk1, hk2, hm1, hm2, idx_self hI w (Submodule.fg_bot), zero_add]
  rfl
end PI.Dv.ProjGramW
