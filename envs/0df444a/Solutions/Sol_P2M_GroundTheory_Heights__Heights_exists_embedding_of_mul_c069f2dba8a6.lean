-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_embedding_of_mul_c069f2dba8a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:32:07.650932+00:00
-- url     : https://prove2.me/submissions/d0ba50d4-5902-4bba-884d-726727f8dbff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (L : (Fin m → K) → ℂ)
    (hadd : ∀ u v, L (u + v) = L u + L v)
    (hmul : ∀ (j j' : Fin m) (a b a' b' : K), a * b = a' * b' →
      L (Pi.single j a) * L (Pi.single j' b) = L (Pi.single j a') * L (Pi.single j' b'))
    (hne : ∃ v, L v ≠ 0) :
    ∃ (σ : K →+* ℂ) (w : Fin m → ℂ), w ≠ 0 ∧ ∀ v, L v = ∑ j, σ (v j) * w j := by
  let Lh : (Fin m → K) →+ ℂ := AddMonoidHom.mk' L hadd
  have h0 : L 0 = 0 := Lh.map_zero
  have hsum : ∀ v, L v = ∑ j, L (Pi.single j (v j)) := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    exact map_sum Lh (fun j ↦ Pi.single j (v j)) Finset.univ
  have hj : ∃ j, L (Pi.single j 1) ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨v, hv⟩ := hne
    apply hv
    rw [hsum v]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have h := hmul j j (v j) (v j) (v j * v j) 1 (by ring)
    rw [hc j, mul_zero] at h
    exact mul_self_eq_zero.mp h
  obtain ⟨j₁, hc⟩ := hj
  let σ : K →+* ℂ :=
    { toFun := fun a ↦ L (Pi.single j₁ a) / L (Pi.single j₁ 1)
      map_one' := div_self hc
      map_mul' := fun a b ↦ by
        have h := hmul j₁ j₁ (a * b) 1 a b (by ring)
        field_simp
        linear_combination h
      map_zero' := by simp [h0]
      map_add' := fun a b ↦ by simp only [Pi.single_add, hadd, add_div] }
  refine ⟨σ, fun j ↦ L (Pi.single j 1), fun h ↦ hc (congrFun h j₁), fun v ↦ ?_⟩
  rw [hsum v]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h := hmul j j₁ (v j) 1 1 (v j) (by ring)
  change L (Pi.single j (v j)) = L (Pi.single j₁ (v j)) / L (Pi.single j₁ 1) * L (Pi.single j 1)
  field_simp
  linear_combination h
end GroundTheory.Heights₂.Heights
