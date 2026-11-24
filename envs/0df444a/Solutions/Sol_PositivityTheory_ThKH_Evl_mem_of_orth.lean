-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.mem_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:50.762031+00:00
-- url     : https://prove2.me/submissions/99ddf772-2047-4ef2-87fe-5459dbdc39f2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
namespace PositivityTheory.ThKH.Evl
theorem _root_.solution (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (z : (κ → k) × (κ → k)) (hz : ∀ w ∈ large₂, w.1 ⬝ᵥ z.2 = z.1 ⬝ᵥ w.2) : z ∈ large₂ := by
  classical
  let Ω : ((κ → k) × (κ → k)) →ₗ[k] Module.Dual k ((κ → k) × (κ → k)) :=
    LinearMap.mk₂ k (fun z w => w.1 ⬝ᵥ z.2 - z.1 ⬝ᵥ w.2)
      (fun a b c => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b c => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun a b c => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hinj : Function.Injective Ω := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simpa [Ω] using LinearMap.congr_fun ha (0, Pi.single i 1)
    · simpa [Ω] using LinearMap.congr_fun ha (Pi.single i 1, 0)
  have hmem : ∀ z : (κ → k) × (κ → k), (∀ w ∈ large₂, w.1 ⬝ᵥ z.2 = z.1 ⬝ᵥ w.2) → Ω z ∈ large₂.dualAnnihilator := fun z hz => by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact sub_eq_zero.2 (hz w hw)
  have hle : large₂.map Ω ≤ large₂.dualAnnihilator := by
    rintro _ ⟨w, hw, rfl⟩
    exact hmem w fun w' hw' => hiso w' hw' w hw
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq large₂
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim] at h1
  have h2 : Module.finrank k (large₂.map Ω) = Module.finrank k large₂.dualAnnihilator := by
    rw [← (Submodule.equivMapOfInjective Ω hinj large₂).finrank_eq, hdim]
    omega
  have h3 := Submodule.eq_of_le_of_finrank_eq hle h2
  obtain ⟨w, hw, e⟩ : Ω z ∈ large₂.map Ω := h3 ▸ hmem z hz
  exact hinj e ▸ hw
end PositivityTheory.ThKH.Evl
