-- Prove2me | solution 1 for QuantumInfo.knill_laflamme_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:52:18.537469+00:00
-- url     : https://prove2.me/submissions/f587c441-61de-4563-b2c1-a0382080f2c1

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Definitions.Def_KnillLaflammeLean_Basic
public import Theorems.Thm_QuantumInfo_Channel_reindex_apply
public import Theorems.Thm_QuantumInfo_knillLaflamme_of_recovery_sum
public import Theorems.Thm_QuantumInfo_Channel_apply_sum
public import Theorems.Thm_QuantumInfo_exists_recovery_of_knillLaflamme


set_option autoImplicit false
@[expose] public section
public section
open Matrix
open QuantumInfo
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace QuantumInfo
theorem _root_.solution {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} (hP : IsCodeProjector P)
    (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (m : ℕ) (R : Channel n n (Fin m)) (lam : ℂ),
        ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (∑ i, E i * ρ * (E i)ᴴ) = lam • ρ := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme hP hP0 hc
    refine ⟨_, R.reindex (Fintype.equivFin (Option ι)), ∑ i, c i i, fun ρ hρ => ?_⟩
    rw [Channel.reindex_apply, Channel.apply_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => hR ρ hρ i i
  · rintro ⟨m, R, lam, h⟩
    exact knillLaflamme_of_recovery_sum hP R lam h
end QuantumInfo
