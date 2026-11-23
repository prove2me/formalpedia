-- Prove2me | solution 1 for PI.Dv.TIW.idx_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:28.653538+00:00
-- url     : https://prove2.me/submissions/e45edf28-90b3-4798-b777-2ce8d4f2620d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Theorems.Thm_PI_Dv_TIW_idx_self
import Theorems.Thm_PI_Dv_TIW_span_pi_eq
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
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : ι → Submodule (𝓞 K) V) (hM : ∀ i, (M i).FG) (hN : ∀ i, (N i).FG)
    (hsp : ∀ i, Submodule.span K (M i : Set V) = Submodule.span K (N i : Set V)) :
    idxAt w (Submodule.pi Set.univ M) (Submodule.pi Set.univ N) = ∑ i, idxAt w (M i) (N i) := by
  have key : ∀ s : Finset ι, idxAt w (Submodule.pi Set.univ fun i => if i ∈ s then M i else ⊥)
      (Submodule.pi Set.univ fun i => if i ∈ s then N i else ⊥) = ∑ i ∈ s, idxAt w (M i) (N i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [idx_self]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih]
      have fg : ∀ P : ι → Submodule (𝓞 K) V, (∀ i, (P i).FG) →
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).FG := fun P hP =>
        Submodule.fg_pi fun i => by split_ifs; exacts [hP i, Submodule.fg_bot]
      have sp : Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then M i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
          Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then N i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) := by
        rw [span_pi_eq, span_pi_eq]
        congr 1; funext i; split_ifs
        · exact hsp i
        · simp
      have hc := (hI K (ι → V) w _ _ (fg M hM) (fg N hN) sp).2.2.1 V (LinearMap.proj a)
      have hker : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥) ⊓
            (LinearMap.ker (LinearMap.proj a : (ι → V) →ₗ[K] V)).restrictScalars (𝓞 K) =
          Submodule.pi Set.univ fun i => if i ∈ s then P i else ⊥ := by
        intro P
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ, true_implies,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.proj_apply]
        constructor
        · rintro ⟨h1, h2⟩ i
          by_cases hi : i = a
          · subst hi; simp [ha, h2]
          · have := h1 i; simpa [Finset.mem_insert, hi] using this
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · by_cases hi : i = a
            · subst hi; have := h i; simp only [ha, if_false, Submodule.mem_bot] at this; simp [this]
            · have := h i; simpa [Finset.mem_insert, hi] using this
          · have := h a; simpa [ha] using this
      have hmap : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).map
            ((LinearMap.proj a : (ι → V) →ₗ[K] V).restrictScalars (𝓞 K)) = P a := by
        intro P
        ext m
        simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
          LinearMap.coe_restrictScalars, LinearMap.proj_apply]
        constructor
        · rintro ⟨x, hx, rfl⟩; have := hx a; simpa using this
        · intro hm
          refine ⟨Pi.single a m, fun i => ?_, by simp⟩
          by_cases hi : i = a
          · subst hi; simpa using hm
          · simp [hi]
      rw [hc, hker, hker, hmap, hmap, add_comm]
  simpa using key Finset.univ
end PI.Dv.TIW
