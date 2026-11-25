-- Prove2me | solution 1 for PI.Dv.TIW.idx_matV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:06.798629+00:00
-- url     : https://prove2.me/submissions/e563699a-d95b-42d5-86e7-5635379a7102

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Theorems.Thm_PI_Dv_TIW_matV_apply
import Theorems.Thm_PI_Dv_TIW_matV_mul
import Theorems.Thm_P2M_PI_Dv_TIW_matV_inv_cancel__b95dfd786b3c
import Theorems.Thm_PI_Dv_TIW_span_latPow
import Theorems.Thm_PI_Dv_TIW_span_map_matV
import Theorems.Thm_PI_Dv_TIW_matV_transvection
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_fg_smulSub
import Theorems.Thm_PI_Dv_TIW_idx_chain
import Theorems.Thm_PI_Dv_TIW_idx_map
import Theorems.Thm_PI_Dv_TIW_idx_map_inj
import Theorems.Thm_PI_Dv_TIW_idx_pi
import Theorems.Thm_PI_Dv_TIW_idx_self
import Theorems.Thm_PI_Dv_TIW_idx_smulSub
import Theorems.Thm_PI_Dv_TIW_mem_smulSub
import Theorems.Thm_PI_Dv_TIW_span_smulSub
import Theorems.Thm_PI_Dv_TIW_vAdd_mul
import Theorems.Thm_PI_Dv_TIW_vAdd_prod
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
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {n : Type} [Fintype n] [DecidableEq n]
    (M : Submodule (𝓞 K) V) (hM : M.FG) (A : Matrix n n K) (hA : A.det ≠ 0) :
    idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det := by
  have hLfg : (latPow n M).FG := Submodule.fg_pi fun _ => hM
  have hsp := span_latPow (n := n) M
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun A => idxAt w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) =
      (Formalism.HN.rkK M : ℤ) * vAdd w A.det) A hA ?_ ?_ ?_
  ·
    intro D hD
    have hDk : ∀ k, D k ≠ 0 := fun k => by
      rw [Matrix.det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD k (Finset.mem_univ k)
    have hmap : (latPow n M).map ((matV (Matrix.diagonal D)).restrictScalars (𝓞 K)) =
        Submodule.pi Set.univ fun k => smulSub (D k) M := by
      ext x
      simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Submodule.mem_pi, Set.mem_univ,
        true_implies, latPow, mem_smulSub]
      constructor
      · rintro ⟨y, hy, rfl⟩ k
        exact ⟨y k, hy k, by rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul]⟩
      · intro h
        choose y hy hyx using h
        exact ⟨y, hy, by funext k; rw [matV_apply]; simp [Matrix.diagonal_apply, ite_smul, hyx]⟩
    rw [hmap, latPow, idx_pi hI w _ _ (fun _ => hM) (fun k => fg_smulSub _ M hM)
      (fun k => (span_smulSub _ (hDk k) M).symm), Matrix.det_diagonal,
      vAdd_prod w _ _ (fun k _ => hDk k), Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => idx_smulSub hI w (D k) (hDk k) M hM
  ·
    intro t
    rw [Matrix.TransvectionStruct.toMatrix, Matrix.det_transvection_of_ne _ _ t.hij]
    have hv1 : vAdd w (1 : K) = 0 := by simp [vAdd]
    rw [hv1, mul_zero]
    set φ : (n → V) →ₗ[K] (n → V) := LinearMap.id - (LinearMap.single K (fun _ => V) t.i) ∘ₗ LinearMap.proj t.i
      with hφ
    have hφapp : ∀ x : n → V, φ x = x - Pi.single t.i (x t.i) := fun x => by simp [hφ]
    have hφT : φ ∘ₗ matV (Matrix.transvection t.i t.j t.c) = φ := by
      apply LinearMap.ext; intro x
      rw [LinearMap.comp_apply, hφapp, hφapp, matV_transvection]
      funext k
      by_cases hk : k = t.i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    have hker0 : ∀ z : n → V, φ z = 0 ↔ ∀ k, k ≠ t.i → z k = 0 := by
      intro z
      rw [hφapp]
      constructor
      · intro h k hk
        have := congrFun h k
        simpa [Pi.single_apply, hk] using this
      · intro h
        funext k
        by_cases hk : k = t.i
        · subst hk; simp
        · simp [Pi.single_apply, hk, h k hk]
    have hfix : ∀ z : n → V, φ z = 0 → matV (Matrix.transvection t.i t.j t.c) z = z := by
      intro z hz
      rw [matV_transvection, (hker0 z).mp hz t.j (Ne.symm t.hij), smul_zero, Pi.single_zero, add_zero]
    have hT := span_map_matV (Matrix.transvection t.i t.j t.c)
      (by rw [Matrix.det_transvection_of_ne _ _ t.hij]; exact one_ne_zero) (latPow n M) _ hsp
    rw [idx_map hI w φ _ _ hLfg (hLfg.map _) (by rw [hT, hsp])]
    · rw [← Submodule.map_comp]
      have : ((φ.restrictScalars (𝓞 K)).comp ((matV (Matrix.transvection t.i t.j t.c)).restrictScalars (𝓞 K))) =
          φ.restrictScalars (𝓞 K) := by
        rw [← LinearMap.restrictScalars_comp, hφT]
      rw [this, idx_self]
    · ext z
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_map,
        LinearMap.coe_restrictScalars]
      constructor
      · rintro ⟨hz, hz0⟩
        exact ⟨⟨z, hz, hfix z hz0⟩, hz0⟩
      · rintro ⟨⟨x, hx, rfl⟩, hz0⟩
        have hx0 : φ x = 0 := by
          rw [← hz0, ← LinearMap.comp_apply, hφT]
        rw [hfix x hx0]
        exact ⟨hx, by rw [hfix x hx0] at hz0; exact hz0⟩
  ·
    intro A B hA hB hPA hPB
    have hsB := span_map_matV B hB (latPow n M) _ hsp
    have hsA := span_map_matV A hA (latPow n M) _ hsp
    have hsAB := span_map_matV A hA _ _ hsB
    have hcomp : (latPow n M).map ((matV (A * B)).restrictScalars (𝓞 K)) =
        ((latPow n M).map ((matV B).restrictScalars (𝓞 K))).map ((matV A).restrictScalars (𝓞 K)) := by
      rw [← Submodule.map_comp, matV_mul, LinearMap.restrictScalars_comp]
    rw [hcomp, idx_chain hI w (latPow n M) ((latPow n M).map ((matV A).restrictScalars (𝓞 K))) _ hLfg
      (hLfg.map _) ((hLfg.map _).map _) (by rw [hsA, hsp]) (by rw [hsAB, hsA])]
    have hinj : ∀ P : Submodule (𝓞 K) (n → V), ∀ x ∈ P, matV A x = 0 → x = 0 := by
      intro P x _ hx
      rw [← matV_inv_cancel' A hA x, hx, map_zero]
    rw [← idx_map_inj hI w (matV A) (latPow n M) _ hLfg (hLfg.map _) (by rw [hsB, hsp]) (hinj _) (hinj _),
      hPA, hPB, Matrix.det_mul, vAdd_mul w _ _ hA hB]
    ring
end PI.Dv.TIW
