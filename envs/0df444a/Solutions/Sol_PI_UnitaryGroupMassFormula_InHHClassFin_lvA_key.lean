-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.lvA_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:22.540796+00:00
-- url     : https://prove2.me/submissions/c61e8229-fe21-4133-a8c1-57958a0cab82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvA_mulVec_int
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
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, ∃ z ∈ LA, (P * u * Q - 1) *ᵥ y = g • z := by
  intro y hy
  have hcy : ∀ i, (c₁ • y) i ∈ S := fun i => by
    simpa [Pi.smul_apply, smul_eq_mul] using h₁ y hy i
  have hw : ∀ i, ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))) i ∈ S :=
    lvA_mulVec_int S _ hP _ (lvA_mulVec_int S _ hN _ (lvA_mulVec_int S _ hQ _ hcy))
  refine ⟨c₂ • ((c • P) *ᵥ (N *ᵥ ((c • Q) *ᵥ (c₁ • y)))), h₂ _ hw, ?_⟩
  have hexp : P * u * Q - 1 = (g * c₂ * c * c * c₁) • (P * N * Q) := by
    rw [hu, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.mul_smul, Matrix.smul_mul]
    abel
  rw [hexp]
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, ← Matrix.mulVec_mulVec]
  congr 1
  ring
end PI.UnitaryGroupMassFormula.InHHClassFin
