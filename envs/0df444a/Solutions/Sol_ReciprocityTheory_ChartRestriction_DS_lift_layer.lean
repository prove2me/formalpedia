-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lift_layer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:20.286281+00:00
-- url     : https://prove2.me/submissions/3a836c4d-411a-4ffe-bb77-41eec8b12178

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Weights
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bAct_isKUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_layer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_finiteDimensional_ncV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_layer_succ_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ncV_kStable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_tensorAction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V (k + 1))
    (hperp : ∀ u ∈ layer ε E V k, inner ℂ u w = 0) {μ : Fin n → ℝ} (hμ : IsKHWVec ε E μ w)
    (hw0 : w ≠ 0) :
    ∃ P ∈ ncV ε V (k + 1), P ≠ 0 ∧ IsKHWVec ε (bAct E (k + 1)) μ P ∧
      ∀ F ∈ ncV ε V (k + 1), phi E (k + 1) F ∈ layer ε E V k → inner ℂ F P = 0 := by
  classical
  set Lk := layer ε E V k with hLk
  haveI : FiniteDimensional ℂ Lk := finiteDimensional_layer (ε := ε) (E := E) hVfd k
  set N := ncV ε V (k + 1) with hN
  haveI : FiniteDimensional ℂ N := finiteDimensional_ncV (ε := ε) hVfd (k + 1)
  set U : Submodule ℂ (Big n (k + 1) M) := N ⊓ Lk.comap (phi E (k + 1)) with hUdef
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le inf_le_left

  have hKu : ∀ a b, ε a = ε b → ∀ x y : M, inner ℂ x (E a b y) = inner ℂ (E b a x) y := by
    intro a b hab x y
    rw [hU b a x y]
    simp [adjSign, hab.symm]
  have hLkK : IsKStableSub ε E Lk := layer_kStable hE hVk k
  have hLkoK : ∀ a b, ε a = ε b → ∀ y ∈ Lkᗮ, E a b y ∈ Lkᗮ := by
    intro a b hab y hy
    rw [Submodule.mem_orthogonal] at hy ⊢
    intro u hu
    rw [hKu a b hab u y]
    exact hy _ (hLkK b a hab.symm u hu)
  have hBu := bAct_isKUnitary hU (k + 1)
  have hNK : IsKStableSub ε (bAct E (k + 1)) N := ncV_kStable hVk (k + 1)
  have hUK : ∀ a b, ε a = ε b → ∀ H ∈ U, bAct E (k + 1) a b H ∈ U := by
    intro a b hab H hH
    refine ⟨hNK a b hab H hH.1, ?_⟩
    show phi E (k + 1) (bAct E (k + 1) a b H) ∈ Lk
    rw [wordContraction_tensorAction hE]
    exact hLkK a b hab _ hH.2
  have hUoK : ∀ a b, ε a = ε b → ∀ H ∈ Uᗮ, bAct E (k + 1) a b H ∈ Uᗮ := by
    intro a b hab H hH
    rw [Submodule.mem_orthogonal] at hH ⊢
    intro u hu
    rw [← hBu b a hab.symm u H]
    exact hH _ (hUK b a hab.symm u hu)

  let Ψ : Big n (k + 1) M →ₗ[ℂ] M :=
    (LinearMap.id - ((Lk.starProjection : M →L[ℂ] M) : M →ₗ[ℂ] M)) ∘ₗ phi E (k + 1)
  have hΨ : ∀ H, Ψ H = phi E (k + 1) H - Lk.starProjection (phi E (k + 1) H) := fun H => rfl
  have hPmem : ∀ v, Lk.starProjection v ∈ Lk := fun v => by
    rw [Submodule.starProjection_apply]; exact SetLike.coe_mem _
  have hzero : ∀ x, x ∈ Lk → x ∈ Lkᗮ → x = 0 := by
    intro x h1 h2
    have hm : x ∈ Lk ⊓ Lkᗮ := ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact hm
  have hΨo : ∀ H, Ψ H ∈ Lkᗮ := fun H => by
    rw [hΨ]; exact Submodule.sub_starProjection_mem_orthogonal _
  have hΨeq : ∀ a b, ε a = ε b → ∀ H, Ψ (bAct E (k + 1) a b H) = E a b (Ψ H) := by
    intro a b hab H
    rw [← sub_eq_zero]
    apply hzero
    · rw [hΨ, hΨ, wordContraction_tensorAction hE, map_sub]
      have e : E a b (phi E (k + 1) H) - Lk.starProjection (E a b (phi E (k + 1) H)) -
          (E a b (phi E (k + 1) H) - E a b (Lk.starProjection (phi E (k + 1) H))) =
          E a b (Lk.starProjection (phi E (k + 1) H)) -
            Lk.starProjection (E a b (phi E (k + 1) H)) := by abel
      rw [e]
      exact Lk.sub_mem (hLkK a b hab _ (hPmem _)) (hPmem _)
    · exact Lkᗮ.sub_mem (hΨo _) (hLkoK a b hab _ (hΨo _))
  have hinj : ∀ H ∈ Uᗮ, H ∈ N → Ψ H = 0 → H = 0 := by
    intro H hHo hHN h0
    have hphi : phi E (k + 1) H ∈ Lk := by
      rw [hΨ, sub_eq_zero] at h0
      rw [h0]; exact hPmem _
    have hm : H ∈ U ⊓ Uᗮ := ⟨⟨hHN, hphi⟩, hHo⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hm
    exact hm

  obtain ⟨l, hl, y, hy, hly⟩ := Submodule.mem_sup.mp (layer_succ_le hE hVk k hw)
  obtain ⟨G0, hG0, rfl⟩ := Submodule.mem_map.mp hy
  have hUmem : U.starProjection G0 ∈ U := by
    rw [Submodule.starProjection_apply]; exact SetLike.coe_mem _
  set G := G0 - U.starProjection G0 with hG
  have hGo : G ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal G0
  have hGN : G ∈ N := N.sub_mem hG0 hUmem.1
  have hwo : w ∈ Lkᗮ := by rw [Submodule.mem_orthogonal]; exact hperp
  have hΨG : Ψ G = w := by
    rw [← sub_eq_zero]
    apply hzero
    · rw [hΨ, hG, map_sub, ← hly]
      have hpu : phi E (k + 1) (U.starProjection G0) ∈ Lk := hUmem.2
      have e : phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0) -
          Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) -
          (l + phi E (k + 1) G0) =
          -(phi E (k + 1) (U.starProjection G0)) -
            Lk.starProjection (phi E (k + 1) G0 - phi E (k + 1) (U.starProjection G0)) - l := by
        abel
      rw [e]
      exact Lk.sub_mem (Lk.sub_mem (Lk.neg_mem hpu) (hPmem _)) hl
    · exact Lkᗮ.sub_mem (hΨo G) hwo
  refine ⟨G, hGN, ?_, ?_, ?_⟩
  · intro h0
    apply hw0
    rw [← hΨG, h0, map_zero]
  · constructor
    · intro a
      have hD : bAct E (k + 1) a a G - ((μ a : ℂ)) • G = 0 := by
        apply hinj
        · exact Uᗮ.sub_mem (hUoK a a rfl G hGo) (Uᗮ.smul_mem _ hGo)
        · exact N.sub_mem (hNK a a rfl G hGN) (N.smul_mem _ hGN)
        · rw [map_sub, map_smul, hΨeq a a rfl, hΨG, hμ.1 a, sub_self]
      exact sub_eq_zero.mp hD
    · intro a b hab hεab
      apply hinj _ (hUoK a b hεab G hGo) (hNK a b hεab G hGN)
      rw [hΨeq a b hεab, hΨG, hμ.2 a b hab hεab]
  · intro F hF hphi
    rw [Submodule.mem_orthogonal] at hGo
    exact hGo F ⟨hF, hphi⟩
end ReciprocityTheory.ChartRestriction.DS
