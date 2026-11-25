-- Prove2me | solution 1 for UpperTheory.Mu.tame_par
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:38:47.469812+00:00
-- url     : https://prove2.me/submissions/03dfd024-0e7e-4c7c-9d1c-08fdf6dcb2da

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_ResidueEisenstein
import Theorems.Thm_UpperTheory_Mu_tame_ext_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open UpperTheory UpperTheory.Mu
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
namespace UpperTheory.Mu
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    {I : Type} [Fintype I] (φ : I → L →+* ℂ) (e : I → ℤ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      (∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i) * ((θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
  classical
  let f : I → (𝓞 L)ˣ →* ℂˣ := fun i =>
    (zpowGroupHom (e i)).comp (Units.map ((φ i).toMonoidHom.comp (algebraMap (𝓞 L) L).toMonoidHom))
  obtain ⟨θ, hθ, hθε⟩ := tame_ext_prime v hp hw hv (∏ i, f i)⁻¹
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  have hf : (((∏ i, f i ζ : ℂˣ)) : ℂ) = ∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [f, Units.val_zpow_eq_zpow_val]
  rw [hθε ζ hζ, MonoidHom.inv_apply, MonoidHom.finset_prod_apply, ← hf]
  exact Units.mul_inv _
end UpperTheory.Mu
