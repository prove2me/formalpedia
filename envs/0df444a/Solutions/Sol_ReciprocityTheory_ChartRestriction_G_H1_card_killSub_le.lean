-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.card_killSub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:02.721391+00:00
-- url     : https://prove2.me/submissions/a3a9cc30-1522-4d7e-a83c-242f97253a4c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaBarEnum

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
variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (hW : WeilSt) (A : PolAV (Sp (FractionRing R))) {O : Type} [Ring O] (ρ : RingAct A.A O)
    (N : ℕ) (ga gb : O) (hga : ∀ x ∈ killSub F A ρ ga, x ^ N = 1) (hgb : ∀ z ∈ killSub F A ρ gb, z ^ N = 1)
    [Finite (killSub F A ρ ga)] [Finite (killSub F A ρ gb)]
    (sep : ∀ x ∈ killSub F A ρ ga, ∀ x' ∈ killSub F A ρ ga, x ≠ x' → ∃ z ∈ killSub F A ρ gb,
      ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
        WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c') :
    Nat.card (killSub F A ρ ga) ≤ Nat.card (killSub F A ρ gb) := by
  classical
  haveI : IsLocallyNoetherian (Sp (FractionRing R)) := by
    first
      | infer_instance
      | (unfold Sp; infer_instance)
  obtain ⟨hEx, hMul, -, -⟩ := hW (Sp (FractionRing R)) A N (TFK (R := R) F)
  have huniq : ∀ (z x : TFK (R := R) F ⟶ A.A) (hz : z ^ N = 1) (hx : x ^ N = 1)
      (c : Γ((TFK (R := R) F).left, ⊤)ˣ), WeilIs A.A A.L N z x c → c = (hEx z x hz hx).exists.choose :=
    fun z x hz hx c hc => (hEx z x hz hx).unique hc (hEx z x hz hx).exists.choose_spec
  let χ : killSub F A ρ ga → (killSub F A ρ gb →* Γ((TFK (R := R) F).left, ⊤)ˣ) := fun x =>
    MonoidHom.mk' (fun z => (hEx z.1 x.1 (hgb _ z.2) (hga _ x.2)).exists.choose) (fun z z' =>
      (huniq (z * z').1 x.1 (hgb _ (z * z').2) (hga _ x.2) _ (hMul _ _ _ _ _ (hEx z.1 x.1 (hgb _ z.2) (hga _ x.2)).exists.choose_spec
        (hEx z'.1 x.1 (hgb _ z'.2) (hga _ x.2)).exists.choose_spec)).symm)
  have hinj : Function.Injective χ := by
    intro x x' hxx
    by_contra hne
    obtain ⟨z, hz, c, c', hc, hc', hcc⟩ := sep x.1 x.2 x'.1 x'.2 (fun h => hne (Subtype.ext h))
    have e1 := huniq z x.1 (hgb z hz) (hga _ x.2) c hc
    have e2 := huniq z x'.1 (hgb z hz) (hga _ x'.2) c' hc'
    have e3 : χ x ⟨z, hz⟩ = χ x' ⟨z, hz⟩ := by rw [hxx]
    exact hcc (e1.trans (e3.trans e2.symm))
  let ψ : killSub F A ρ ga → (killSub F A ρ gb →* Γ((TFK (R := R) F).left, ⊤)) := fun x =>
    (Units.coeHom _).comp (χ x)
  have hψ : Function.Injective ψ := by
    intro x x' h
    apply hinj
    refine MonoidHom.ext fun z => Units.ext ?_
    exact congrArg (fun f => f z) h
  haveI : IsDomain Γ((TFK (R := R) F).left, ⊤) := by
    first
      | infer_instance
      | exact Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1
  have hli := (linearIndependent_monoidHom (killSub F A ρ gb) Γ((TFK (R := R) F).left, ⊤)).comp ψ hψ
  haveI := Fintype.ofFinite (killSub F A ρ ga)
  haveI := Fintype.ofFinite (killSub F A ρ gb)
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hcard
end ReciprocityTheory.ChartRestriction.G.H1
