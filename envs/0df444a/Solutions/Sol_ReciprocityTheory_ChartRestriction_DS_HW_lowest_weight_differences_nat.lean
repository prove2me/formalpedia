-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowest_weight_differences_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:00.884804+00:00
-- url     : https://prove2.me/submissions/9e77976e-c053-4057-8037-a91f0e5a48f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_nat_weight_sub_eq_of_highest_vector_in_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kRel_map


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Fin n → Fin n → Matrix ι ι ℂ} (hG : Formalism.REAL.KRel ε G) {ν : Fin n → ℝ} {f : ι → ℂ} (hf0 : f ≠ 0)
    (hfw : ∀ a, G a a *ᵥ f = ((ν a : ℝ) : ℂ) • f) (hfl : ∀ a b, b < a → ε a = ε b → G a b *ᵥ f = 0) :
    ∀ a b, a < b → ε a = ε b → ∃ m : ℕ, ν b - ν a = m := by
  intro a b hab he
  have hR : Formalism.REAL.KRel ε (fun a b => Matrix.toLinAlgEquiv' (G a b)) :=
    uq_kRel_map ε G (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] _).toRingEquiv.toRingHom hG
  have happ : ∀ a b (x : ι → ℂ), Matrix.toLinAlgEquiv' (G a b) x = G a b *ᵥ x := fun a b x => rfl
  obtain ⟨m, hm⟩ := exists_nat_weight_sub_eq_of_highest_vector_in_stable hR (ne_of_lt hab).symm he.symm (⊤ : Submodule ℂ (ι → ℂ))
    (fun _ _ => Submodule.mem_top) Submodule.mem_top hf0 (la := ((ν b : ℝ) : ℂ)) (lb := ((ν a : ℝ) : ℂ))
    (by rw [happ]; exact hfw b) (by rw [happ]; exact hfw a) (by rw [happ]; exact hfl b a hab he.symm)
  refine ⟨m, ?_⟩
  apply Complex.ofReal_injective
  push_cast
  exact hm
end ReciprocityTheory.ChartRestriction.DS.HW
