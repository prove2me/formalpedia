-- Prove2me | solution 1 for PI.TwNormLat.W.combinationEquiv_inv_mem_unipotentFlagGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:19.216567+00:00
-- url     : https://prove2.me/submissions/a15061cc-de93-4f2c-94bf-19bddc72502f

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup
import Theorems.Thm_PI_TwNormLat_W_comb_zab
import Theorems.Thm_PI_TwNormLat_W_combL_single
import Theorems.Thm_PI_TwNormLat_W_combE_apply
import Theorems.Thm_PI_TwNormLat_W_combE_symm_zab
import Theorems.Thm_PI_TwNormLat_W_eN_eq_single
import Theorems.Thm_PI_TwNormLat_W_eN_eq_zero
import Theorems.Thm_PI_TwNormLat_W_mem_Ufl_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
noncomputable section
namespace PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}
private theorem R1cond_combE {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd) := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [mem_Ufl_iff] at hv ⊢
    rw [combE_apply]
    exact comb_zab hb v _ hv
  · by_cases hN : N < N + c
    · have he : Loc.eN K (N + c) N = Pi.single (⟨N, hN⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N, hN⟩ : Fin (N + c))
      rw [he]
      change combL b (Pi.single _ 1) = _
      rw [combL_single, ha hN]
    · have he : Loc.eN K (N + c) N = 0 := eN_eq_zero (by omega)
      rw [he, map_zero]
  · rw [mem_Ufl_iff]
    by_cases hi : N + i < N + c
    · have he : Loc.eN K (N + c) (N + i) = Pi.single (⟨N + i, hi⟩ : Fin (N + c)) 1 := eN_eq_single (⟨N + i, hi⟩ : Fin (N + c))
      rw [he]
      change Zab (N + i) (combL b (Pi.single _ 1) - _)
      rw [combL_single]
      intro m hm
      simp only [Pi.sub_apply]
      rcases lt_or_eq_of_le hm with hlt | heq
      · have hne : m ≠ ⟨N + i, hi⟩ := by
          intro h
          subst h
          exact lt_irrefl _ hlt
        rw [hb _ _ (Fin.lt_def.2 hlt), Pi.single_eq_of_ne hne, sub_zero]
      · have hm' : m = ⟨N + i, hi⟩ := Fin.ext heq.symm
        subst hm'
        rw [Pi.single_eq_same, h1 _ (Nat.le_add_right N i), sub_self]
    · have he : Loc.eN K (N + c) (N + i) = 0 := eN_eq_zero (by omega)
      rw [he, map_zero, sub_zero]
      intro m _
      rfl
private theorem R1cond_combE_symm {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    Loc.R1cond K N c (combE hb hd).symm := by
  have hT := R1cond_combE hb hd h1 ha
  have hs : ∀ i, ∀ v ∈ Loc.Ufl K N c i, (combE hb hd).symm v ∈ Loc.Ufl K N c i := fun i v hv =>
    (mem_Ufl_iff _).2 (combE_symm_zab hb hd _ v ((mem_Ufl_iff _).1 hv))
  refine ⟨hs, (LinearEquiv.symm_apply_eq _).2 hT.2.1.symm, fun i => ?_⟩
  have h3 := hs i _ (hT.2.2 i)
  rw [map_sub, LinearEquiv.symm_apply_apply] at h3
  have h4 := (Loc.Ufl K N c i).neg_mem h3
  rwa [neg_sub] at h4
end PI.TwNormLat.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}
namespace PI.TwNormLat.W
theorem _root_.solution {N c : ℕ} {b : Fin (N + c) → Fin (N + c) → K} (hb : UT b) (hd : ∀ l, b l l ≠ 0)
    (h1 : ∀ l : Fin (N + c), N ≤ l.1 → b l l = 1) (ha : ∀ hN : N < N + c, b ⟨N, hN⟩ = Pi.single ⟨N, hN⟩ 1) :
    (combE hb hd)⁻¹ ∈ Loc.R1 K N c := by
  show Loc.R1cond K N c (combE hb hd)⁻¹ ∧ Loc.R1cond K N c (combE hb hd)⁻¹⁻¹
  rw [inv_inv]
  exact ⟨R1cond_combE_symm hb hd h1 ha, R1cond_combE hb hd h1 ha⟩
end PI.TwNormLat.W
