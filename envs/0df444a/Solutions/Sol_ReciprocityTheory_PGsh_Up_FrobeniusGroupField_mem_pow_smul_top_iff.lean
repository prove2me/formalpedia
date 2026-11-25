-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.mem_pow_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:35:43.12395+00:00
-- url     : https://prove2.me/submissions/860654a2-fd37-4339-91d7-23f194e52587

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) (k : ℕ) (x : M) :
    x ∈ ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.repr x i ∈ (maximalIdeal ℤ_[p]) ^ k := by
  constructor
  · intro hx i
    have hle : ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ≤
        Submodule.comap (b.coord i) ((maximalIdeal ℤ_[p]) ^ k) :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
