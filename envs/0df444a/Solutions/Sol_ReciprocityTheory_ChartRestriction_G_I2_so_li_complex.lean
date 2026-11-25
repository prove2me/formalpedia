-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.so_li_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:38.973348+00:00
-- url     : https://prove2.me/submissions/9b8a1397-4760-4d41-907c-229a8d16229d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitOA
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_soPsi_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_so_emb_inj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.soPsi_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution :
    LinearIndependent ℂ (fun i => soPsi (RingOfIntegers.basis E i : E)) := by
  classical
  let T : ((E →+* ℂ) → ℂ) →ₗ[ℂ] (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ) :=
    { toFun := fun v i => ∑ σ, v σ * σ (RingOfIntegers.basis E i : E)
      map_add' := fun v v' => by ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by ext i; simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    exact so_emb_inj v (fun i => congr_fun hv i)
  have hsurj : Function.Surjective T := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [Module.finrank_fintype_fun_eq_card, NumberField.Embeddings.card,
      ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hσ : ∀ σ : E →+* ℂ, ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0 := by
    intro σ
    have := congr_arg (fun v : EuclideanSpace ℂ (E →+* ℂ) => v σ) hc
    simpa using this
  obtain ⟨v, hv⟩ := hsurj (Pi.single i 1)
  have h0 : ∑ j, c j * T v j = 0 := by
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have h1 : v σ * ∑ j, c j * σ (RingOfIntegers.basis E j : E) = 0 := by rw [hσ σ, mul_zero]
    rw [Finset.mul_sum] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hv] at h0
  simpa [Pi.single_apply] using h0
end ReciprocityTheory.ChartRestriction.G.I2
