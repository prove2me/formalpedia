-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.exists_delta_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:28:33.504254+00:00
-- url     : https://prove2.me/submissions/11e4a278-ca34-451b-a378-419301adf7bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_primeOf_isPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_w_eq_count
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_exists_delta_count
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_diffExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution [IsGalois ℚ E] (ℓ a m : ℕ) (hℓ : ℓ.Prime) (hm : ¬ ℓ ∣ m)
    (hdisc : (discr E).natAbs = ℓ ^ a * m) (ψ : E →+* k) (hψ : Function.Injective ψ)
    (hℓψ : 0 < vV V (ψ (ℓ : E))) :
    ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      vV V (ψ (δ : E)) * Module.finrank ℚ E = a * vV V (ψ (ℓ : E)) := by
  set P := primeOf (V := V) ψ hψ
  have hPp : P.IsPrime := primeOf_isPrime ψ hψ
  have hℓ0 : (ℓ : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  have hℓP : (ℓ : 𝓞 E) ∈ P := Or.inl (by simpa using hℓψ)
  have hP0 : P ≠ ⊥ := fun h => hℓ0 (by rw [h] at hℓP; exact (Submodule.mem_bot _).1 hℓP)
  obtain ⟨π, hπ0, hw⟩ := w_eq_count ψ hψ hP0
  obtain ⟨δ, hδD, hδ0, hδc⟩ := exists_delta_count hPp hP0
  have hex := diffExp E ℓ a m hℓ hm hdisc P hPp hℓP
  have h1 := hw _ δ hδ0 rfl
  have h2 := hw _ (ℓ : 𝓞 E) hℓ0 rfl
  refine ⟨δ, hδD, hδ0, ?_⟩
  have e : ((ℓ : 𝓞 E) : E) = (ℓ : E) := by simp
  rw [e] at h2
  rw [h1, h2, hδc]
  have hex' : ((normalizedFactors (differentIdeal ℤ (𝓞 E))).count P : ℤ) * Module.finrank ℚ E =
      a * (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P := by exact_mod_cast hex
  linear_combination vV V (ψ (π : E)) * hex'
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
