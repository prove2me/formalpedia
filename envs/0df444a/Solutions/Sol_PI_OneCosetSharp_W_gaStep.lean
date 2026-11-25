-- Prove2me | solution 1 for PI.OneCosetSharp.W.gaStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:16.285683+00:00
-- url     : https://prove2.me/submissions/115989e2-afd6-4b17-9ee6-676ce210dd49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
import Theorems.Thm_PI_OneCosetSharp_W_eN_apply
import Theorems.Thm_PI_OneCosetSharp_W_XP_AP
import Theorems.Thm_PI_OneCosetSharp_W_lowProj_basisVec_of_le
import Theorems.Thm_PI_OneCosetSharp_W_lowProj_basisVec_of_lt
import Theorems.Thm_PI_OneCosetSharp_W_projA_eq_self_of_projX_eq_zero
import Theorems.Thm_PI_OneCosetSharp_W_fix_of_basis
import Theorems.Thm_PI_OneCosetSharp_W_lowProj_add_highProj
import Theorems.Thm_PI_OneCosetSharp_W_mem_Ufl
import Theorems.Thm_PI_OneCosetSharp_W_mem_flagUnipotent
import Theorems.Thm_PI_OneCosetSharp_W_projA_apply
import Theorems.Thm_PI_OneCosetSharp_W_projA_inX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}
private theorem fIdx_lt_add_of_lt_add {k₀ c n p : ℕ} (hp : p < n + c) : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega
private theorem fIdx_injOn_of_lt_add {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p = PI.OneCosetSharp.LocE.fIdx k₀ c n p') : p = p' := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega
private theorem mem_block_of_le_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c)
    (h : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p) : k₀ ≤ p ∧ p < k₀ + c := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega
private theorem lt_or_le_of_fIdx_lt {k₀ c n p : ℕ} (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n) :
    p < k₀ ∨ k₀ + c ≤ p := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega
private theorem allow_of_mem_block_of_le_right {k₀ m t N c p p' : ℕ} (hcm : c + 1 < m) (hp : k₀ ≤ p)
    (hpc : p < k₀ + c) (hp' : k₀ + c ≤ p') : PI.OneCosetSharp.Allow k₀ m t N p p' := by
  unfold PI.OneCosetSharp.Allow
  split_ifs
  · omega
  · left; omega
  · left; omega
end PI.OneCosetSharp.W
end
end

set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}
namespace PI.OneCosetSharp.W
theorem _root_.solution : GaStep := by
  intro k _ k₀ m t j n' c n hadm g hga hfree
  obtain ⟨hk₀, -, hm4, hj1, hjm, hc, hn', hn⟩ := hadm
  generalize j * t = s at hn
  generalize (j - 1) * t = s' at hn'
  have hkn : k₀ ≤ n := by omega
  have hcm : c + 1 < m := by omega
  obtain ⟨B, hB⟩ : ∃ B : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k),
      ∀ w, B w = AP (g (XP w)) :=
    ⟨AP ∘ₗ g.toLinearMap ∘ₗ XP, fun w => rfl⟩
  have hfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → g w = w :=
    fix_of_basis g hga
  have hB0 : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → B w = 0 := by
    intro w hw
    rw [hB, hw]
    simp
  have hBB : ∀ w, B (B w) = 0 := fun w => hB0 _ (by rw [hB]; exact XP_AP _)
  obtain ⟨κ, hκ, hκs⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ w, κ w = w + B w) ∧ ∀ w, κ.symm w = w - B w := by
    refine ⟨LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B) ?_ ?_, fun w => rfl, fun w => rfl⟩
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hBB, add_zero]
      abel
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_add, hBB, sub_zero]
      abel
  have hg : ∀ v, g v = g (XP v) + AP v := by
    intro v
    conv_lhs => rw [← lowProj_add_highProj (n := n) (c := c) v]
    rw [map_add, hfix _ (XP_AP v)]
  have hγ : ∀ v, (g * κ⁻¹) v = g (XP v) + AP v - AP (g (XP v)) := by
    intro v
    show g (κ.symm v) = _
    rw [hκs, map_sub, hfix (B v) (by rw [hB]; exact XP_AP _), hB, hg v]
  have hγl : ∀ v (l : Fin (n + c)), n ≤ l.1 → (g * κ⁻¹) v l = v l := by
    intro v l hl
    rw [hγ]
    simp only [Pi.sub_apply, Pi.add_apply, projA_apply, if_neg (not_lt.mpr hl)]
    ring
  have hγfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → (g * κ⁻¹) w = w := by
    intro w hw
    rw [hγ, hw]
    simp [projA_eq_self_of_projX_eq_zero hw]
  have hU : PI.OneCosetSharp.Loc.R1cond k n c (g * κ⁻¹) := by
    refine ⟨fun i v hv => ?_, hγfix _ (lowProj_basisVec_of_le n le_rfl), fun i => ?_⟩
    · rw [mem_Ufl] at hv ⊢
      intro l hl
      rw [hγl v l (by omega)]
      exact hv l hl
    · rw [hγfix _ (lowProj_basisVec_of_le (n + i) (Nat.le_add_right n i)), sub_self]
      exact Submodule.zero_mem _
  have hentry : ∀ p p' (hp : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c),
      PI.OneCosetSharp.ent k₀ c n c n κ.toLinearMap p p' =
        (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p') + B (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p'))) ⟨_, hp⟩ := by
    intro p p' hp
    simp only [PI.OneCosetSharp.ent, PI.OneCosetSharp.Loc.atN, dif_pos hp, LinearEquiv.coe_coe, hκ]
  have hBq : ∀ q (hq : q < n + c), B (PI.OneCosetSharp.Loc.eN k (n + c) q) ⟨q, hq⟩ = 0 := by
    intro q hq
    by_cases h : q < n
    · rw [hB, projA_apply]
      exact if_pos h
    · rw [hB0 _ (lowProj_basisVec_of_le q (not_lt.mp h))]
      rfl
  refine ⟨g * κ⁻¹, mem_flagUnipotent hU, κ, ⟨fun p' hp' => ?_, fun p p' hp hp' hne hent => ?_⟩, by simp⟩
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) (show p' < n + c by omega)
    rw [hentry p' p' hq, Pi.add_apply, hBq _ hq, add_zero, eN_apply]
    exact if_pos rfl
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) hp
    have hqq : PI.OneCosetSharp.LocE.fIdx k₀ c n p ≠ PI.OneCosetSharp.LocE.fIdx k₀ c n p' := fun h => hne (fIdx_injOn_of_lt_add hkn hp hp' h)
    rw [hentry p p' hq, Pi.add_apply, eN_apply, Fin.val_mk, if_neg hqq, zero_add] at hent
    by_cases hq'n : PI.OneCosetSharp.LocE.fIdx k₀ c n p' < n
    · rw [hB, lowProj_basisVec_of_lt _ hq'n] at hent
      rcases lt_or_le_of_fIdx_lt hq'n with h | h
      · obtain ⟨v, hv⟩ := hfree p' (by omega) (Or.inl h)
        rw [hv, projA_inX] at hent
        exact (hent rfl).elim
      · rw [projA_apply] at hent
        have hpn : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p := by
          by_contra h'
          exact hent (if_pos (not_le.mp h'))
        obtain ⟨hp1, hp2⟩ := mem_block_of_le_fIdx hkn hp hpn
        exact allow_of_mem_block_of_le_right hcm hp1 hp2 h
    · rw [hB0 _ (lowProj_basisVec_of_le _ (not_lt.mp hq'n))] at hent
      exact (hent rfl).elim
end PI.OneCosetSharp.W
