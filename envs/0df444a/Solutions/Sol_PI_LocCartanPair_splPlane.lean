-- Prove2me | solution 1 for PI.LocCartanPair.splPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:50.087381+00:00
-- url     : https://prove2.me/submissions/dd378110-bdfb-483b-95c8-f49e52ef8e0e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_SplPlane
import Theorems.Thm_PI_LocCartanPair_splPlane_core
import Theorems.Thm_PI_LocCartanPair_splPlane_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.LocCartanPair
variable {R : Type} [CommRing R] [StarRing R]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.LocCartanPair
theorem _root_.solution [IsLocalRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (hc : Fintype.card κ + 2 = Fintype.card ι) (A : Matrix ι ι R) (hA : Aᴴ = A)
    (x y : ι → R) (hxx : star x ⬝ᵥ (A *ᵥ x) = 0) (hyy : star y ⬝ᵥ (A *ᵥ y) = 0)
    (hxy : star x ⬝ᵥ (A *ᵥ y) = 1) :
    ∃ (u : Matrix ι (Fin 2 ⊕ κ) R) (v : Matrix (Fin 2 ⊕ κ) ι R) (A₁ : Matrix κ κ R),
      u * v = 1 ∧ v * u = 1 ∧ (∀ i, u i (.inl 0) = x i) ∧ (∀ i, u i (.inl 1) = y i) ∧
      uᴴ * A * u = fromBlocks !![0, 1; 1, 0] 0 0 A₁ ∧ A₁ᴴ = A₁ ∧
      (IsUnit A.det → IsUnit A₁.det) := by
  obtain ⟨i₀, j₀, hne, hu⟩ := splPlane_pair A hA x y hxx hxy
  have hc₀ : Fintype.card {j // j ≠ i₀ ∧ j ≠ j₀} = Fintype.card κ := by
    have := Fintype.card_congr (splEquiv i₀ j₀ hne)
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  let E : Fin 2 ⊕ κ ≃ ι :=
    (Equiv.sumCongr (Equiv.refl _) (Fintype.equivOfCardEq hc₀).symm).trans (splEquiv i₀ j₀ hne)
  have h0 : E (.inl 0) = i₀ := by simp [E, splEquiv]
  have h1 : E (.inl 1) = j₀ := by simp [E, splEquiv]
  exact splPlane_core E A hA x y hxx hyy hxy (by rw [h0, h1]; exact hu)
end PI.LocCartanPair
