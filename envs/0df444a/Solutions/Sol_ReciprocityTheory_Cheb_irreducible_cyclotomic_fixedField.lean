-- Prove2me | solution 1 for ReciprocityTheory.Cheb.irreducible_cyclotomic_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:14.425671+00:00
-- url     : https://prove2.me/submissions/76691799-906c-4412-a4fc-d4bd5dacd106

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
import Theorems.Thm_ReciprocityTheory_Cheb_pow_apply_zeta_eq_units_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open ReciprocityTheory ReciprocityTheory.Cheb
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) :
    Irreducible (cyclotomic l (IntermediateField.fixedField (Subgroup.zpowers g))) := by
  have hlp := (Fact.out : l.Prime)
  have hl : NeZero l := ⟨hlp.ne_zero⟩
  set E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hint : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  set p := minpoly E ζ with hp
  have hcard : Fintype.card (ZMod l)ˣ = l - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hlp]

  have htop : Subgroup.zpowers τ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hτ, Nat.card_eq_fintype_card, hcard]

  have hroot : ∀ u : (ZMod l)ˣ, aeval (ζ ^ (u : ZMod l).val) p = 0 := by
    intro u
    have hu : u ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top u
    obtain ⟨k, hk : τ ^ k = u⟩ := mem_powers_iff_mem_zpowers.mpr hu
    have hgk : g ^ k ∈ IntermediateField.fixingSubgroup E := by
      rw [IntermediateField.fixingSubgroup_fixedField]
      exact Subgroup.npow_mem_zpowers g k
    set ψ := IntermediateField.fixingSubgroupEquiv E ⟨g ^ k, hgk⟩
    have hψ : ψ ζ = ζ ^ (u : ZMod l).val := by
      change (g ^ k) ζ = _
      rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hk]
    rw [← hψ, Polynomial.aeval_algEquiv, AlgHom.comp_apply, hp, minpoly.aeval, map_zero]
  have hdvd : p ∣ cyclotomic l E := by
    apply minpoly.dvd
    rw [← Polynomial.eval_map_algebraMap, Polynomial.map_cyclotomic]
    exact (hζ.isRoot_cyclotomic (NeZero.pos l))
  have hp0 : p.map (algebraMap E M) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
  classical
  let Z : Finset M := Finset.univ.image (fun u : (ZMod l)ˣ => ζ ^ (u : ZMod l).val)
  have hZcard : Z.card = l - 1 := by
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, hcard]
    intro u v huv
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) huv
    exact Units.ext (ZMod.val_injective l this)
  have hZ : Z.val ⊆ (p.map (algebraMap E M)).roots := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact hroot u
  have hdeg := Polynomial.card_le_degree_of_subset_roots hZ
  rw [hZcard, Polynomial.natDegree_map] at hdeg
  have heq : cyclotomic l E = p := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic l E) hdvd ?_
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hlp]
    exact hdeg
  rw [heq]
  exact minpoly.irreducible hint
end ReciprocityTheory.Cheb
