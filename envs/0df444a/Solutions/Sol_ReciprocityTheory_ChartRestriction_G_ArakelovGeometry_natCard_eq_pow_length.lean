-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCard_eq_pow_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:22.113801+00:00
-- url     : https://prove2.me/submissions/30920409-e2d9-439f-acf8-b4ece4edc941

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NatCardEqPowLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {A : Type*} [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : A, p • x = 0) : Nat.card A = p ^ (Module.length ℤ A).toNat := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Module (ZMod p) A := AddCommGroup.zmodModule h
  have hlen : Module.length ℤ A = Module.length (ZMod p) A :=
    Module.length_eq_of_surjective (fun x => ⟨(x.val : ℤ), by simp⟩)
  have hfin : Module.length (ZMod p) A = (Module.finrank (ZMod p) A : ℕ∞) :=
    @Module.length_eq_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  have hcard : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A :=
    @Module.natCard_eq_pow_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  rw [hlen, hfin, ENat.toNat_coe, hcard, Nat.card_zmod]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
