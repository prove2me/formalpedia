-- Prove2me | solution 1 for QuantumInfo.knill_laflamme
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:53:36.385631+00:00
-- url     : https://prove2.me/submissions/92fbd74a-be8a-49f9-b902-746dde40e27b

module
public import Definitions.Def_KnillLaflammeLean_QuantumInfo_KnillLaflamme
public import Definitions.Def_KnillLaflammeLean_Basic
public import Theorems.Thm_QuantumInfo_Channel_reindex_apply
public import Theorems.Thm_QuantumInfo_knillLaflamme_iff
public import Theorems.Thm_QuantumInfo_knillLaflamme_of_recovery


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
      ∃ (m : ℕ) (R : Channel n n (Fin m)) (lam : ι → ℂ),
        ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ := by
  constructor
  · intro h
    obtain ⟨R, lam, hR⟩ := (knillLaflamme_iff hP hP0).mp h
    refine ⟨_, R.reindex (Fintype.equivFin (Option ι)), lam, fun i ρ hρ => ?_⟩
    rw [Channel.reindex_apply]
    exact hR i ρ hρ
  · rintro ⟨m, R, lam, h⟩
    exact knillLaflamme_of_recovery hP R lam h
end QuantumInfo
