-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.alphaBarEnum_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:59:17.563605+00:00
-- url     : https://prove2.me/submissions/497e7098-86c8-46de-a4ad-434febd1720a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaBarEnum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_card_killSub_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_pow_eq_one_of_kill
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_sep_core


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (hW : WeilSt) (hM : MulNSt) : AlphaBarEnumStatement := by
  intro E _ _ _ H V _ _ _ t P hTor α N hN1 hαN huu hNV F _ _ _ Dw hI
  letI := H.starRing
  obtain ⟨u, u', huu⟩ := huu
  classical
  haveI : IsLocallyNoetherian (Sp (FractionRing V)) := by
    first
      | infer_instance
      | (unfold Sp; infer_instance)
  let ρ := P.oA.toRingAct
  have hNF : ((N : ℕ) : F) ≠ 0 := by
    have h1 := (hNV.map (algebraMap V (FractionRing V))).map (algebraMap (FractionRing V) F)
    simp only [map_natCast] at h1
    exact h1.ne_zero
  have hcardN := (hM (Sp (FractionRing V)) P.A N hN1).2.2.2.2 F (jFK (R := V) F) hNF
  have hkA : ∀ x ∈ killSub F P.A ρ α, x ^ N = 1 := fun x hx =>
    pow_eq_one_of_kill ρ (show star α * α = (N : 𝓞 E) by rw [mul_comm]; exact hαN) x hx
  have hkB : ∀ x ∈ killSub F P.A ρ (star α), x ^ N = 1 := fun x hx =>
    pow_eq_one_of_kill ρ hαN x hx
  let eqv := torsionEquiv F P.A ρ N α (star α) u u' hαN huu
  have htot : Nat.card {y : TFK (R := V) F ⟶ P.A.A // y ^ N = 1} =
      Nat.card (killSub F P.A ρ α) * Nat.card (killSub F P.A ρ (star α)) := by
    rw [Nat.card_congr eqv, Nat.card_prod]
  have hpos : Nat.card {y : TFK (R := V) F ⟶ P.A.A // y ^ N = 1} ≠ 0 := by
    rw [hcardN]
    exact pow_ne_zero _ (by omega)
  haveI hfin : Finite {y : TFK (R := V) F ⟶ P.A.A // y ^ N = 1} := Nat.finite_of_card_ne_zero hpos
  haveI : Finite (killSub F P.A ρ α × killSub F P.A ρ (star α)) := Finite.of_equiv _ eqv
  haveI : Finite (killSub F P.A ρ α) := Finite.prod_left (killSub F P.A ρ (star α))
  haveI : Finite (killSub F P.A ρ (star α)) := Finite.prod_right (killSub F P.A ρ α)
  have sep1 : ∀ x ∈ killSub F P.A ρ (star α), ∀ x' ∈ killSub F P.A ρ (star α), x ≠ x' →
      ∃ z ∈ killSub F P.A ρ α, ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
        WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c' := by
    intro x hx x' hx' hne
    obtain ⟨z, hz, rest⟩ := sep_core (F := F) P.A P.oA Dw hI N hN1 α u u' hαN huu x x' hx hx' hne
    exact ⟨z, hz, rest⟩
  have sep2 : ∀ x ∈ killSub F P.A ρ α, ∀ x' ∈ killSub F P.A ρ α, x ≠ x' →
      ∃ z ∈ killSub F P.A ρ (star α), ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
        WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c' := by
    intro x hx x' hx' hne
    have h1 : star α * star (star α) = (N : 𝓞 E) := by rw [star_star, mul_comm]; exact hαN
    have h2 : u' * star α + u * star (star α) = 1 := by rw [star_star, add_comm]; exact huu
    obtain ⟨z, hz, rest⟩ := sep_core (F := F) P.A P.oA Dw hI N hN1 (star α) u' u h1 h2 x x'
      (by rw [star_star]; exact hx) (by rw [star_star]; exact hx') hne
    exact ⟨z, hz, rest⟩
  have hle1 := card_killSub_le F hW P.A ρ N (star α) α hkB hkA sep1
  have hle2 := card_killSub_le F hW P.A ρ N α (star α) hkA hkB sep2
  have hc2 : Nat.card (killSub F P.A ρ (star α)) = N ^ P.A.g := by
    have hsq : Nat.card (killSub F P.A ρ (star α)) ^ 2 = (N ^ P.A.g) ^ 2 := by
      rw [sq, ← pow_mul, mul_comm P.A.g 2, ← hcardN, htot, le_antisymm hle2 hle1]
    exact Nat.pow_left_injective two_ne_zero hsq
  let ev := (Finite.equivFinOfCardEq hc2).symm
  obtain ⟨f, hToA, hsurj, -⟩ := hTor F (1 * N) (by omega)
  have hx1 : ∀ b, ((ev b).1) ^ (1 * N) = 1 := fun b => by
    rw [Nat.one_mul]
    exact hkB _ (ev b).2
  refine ⟨fun b => (hsurj _ (hx1 b)).choose, fun b => (ev b).1, fun b => ?_, fun b => (ev b).2, ?_, ?_⟩
  · exact (hToA _ _).2 (hsurj _ (hx1 b)).choose_spec.symm
  · exact Subtype.val_injective.comp ev.injective
  · intro y hy
    exact ⟨ev.symm ⟨y, hy⟩, by simp⟩
end ReciprocityTheory.ChartRestriction.G.H1
