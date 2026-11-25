-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.lvA_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:39:39.372796+00:00
-- url     : https://prove2.me/submissions/d6770779-029d-43f5-882d-bbba8bb3bd43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_LevelA
import Theorems.Thm_PI_UnitaryGroupMassFormula_InHHClassFin_lvA_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
variable {R : Type} [CommRing R] (S : Subring R) {n : ℕ}
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (LA : Submodule S (Fin n → R))
    (c₁ c₂ c g : R) (hg : g ∈ S)
    (h₁ : ∀ y ∈ LA, ∀ i, c₁ * y i ∈ S) (h₂ : ∀ y : Fin n → R, (∀ i, y i ∈ S) → c₂ • y ∈ LA)
    (P : Matrix (Fin n) ι R) (Q : Matrix ι (Fin n) R) (hPQ : P * Q = 1)
    (hP : ∀ i j, (c • P) i j ∈ S) (hQ : ∀ i j, (c • Q) i j ∈ S)
    (N : Matrix ι ι R) (hN : ∀ i j, N i j ∈ S) (u : Matrix ι ι R)
    (hu : u = 1 + (g * c₂ * c * c * c₁) • N) :
    ∀ y ∈ LA, (P * u * Q) *ᵥ y ∈ LA := by
  intro y hy
  obtain ⟨z, hz, hzeq⟩ := lvA_key S LA c₁ c₂ c g h₁ h₂ P Q hPQ hP hQ N hN u hu y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add'] at hzeq
  rw [hzeq]
  exact LA.add_mem hy (LA.smul_mem (⟨g, hg⟩ : S) hz)
end PI.UnitaryGroupMassFormula.InHHClassFin
