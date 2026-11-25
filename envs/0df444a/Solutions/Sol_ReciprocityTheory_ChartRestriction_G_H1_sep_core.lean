-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.sep_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:38:03.628668+00:00
-- url     : https://prove2.me/submissions/e158cab0-f2a0-49c0-baa0-39d161318804

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_AlphaPair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_pow_eq_one_of_kill
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_unitOn_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_mem_nsmul_of_dvd

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (A : PolAV (Sp (FractionRing R))) : letI := H.starRing
    ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a)
        (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N : ℕ), 1 ≤ N →
      ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 →
      ∀ x x' : TFK (R := R) F ⟶ A.A, x ≫ oA.act (star β) = 1 → x' ≫ oA.act (star β) = 1 → x ≠ x' →
        ∃ z : TFK (R := R) F ⟶ A.A, z ≫ oA.act β = 1 ∧
          ∃ c c' : Γ((TFK (R := R) F).left, ⊤)ˣ,
            WeilIs A.A A.L N z x c ∧ WeilIs A.A A.L N z x' c' ∧ c ≠ c' := by
  let _ := H.starRing
  intro oA Dw I N hN β u u' hβ huu x x' hx hx' hne
  have hN0 : 0 < N := hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev N (c • b) = I.ev N b ≫ oA.act c := fun c b => I.lin N c b
  obtain ⟨a, rfl⟩ := (I.onto N hN0 x).1 (pow_eq_one_of_kill oA.toRingAct hβ x hx)
  obtain ⟨a', rfl⟩ := (I.onto N hN0 x').1 (pow_eq_one_of_kill oA.toRingAct hβ x' hx')
  obtain ⟨e, he⟩ := (I.ker N hN0 (star β • a)).1 (by rw [hlin]; exact hx)
  obtain ⟨e', he'⟩ := (I.ker N hN0 (star β • a')).1 (by rw [hlin]; exact hx')
  have hdN : ∀ f : Dw.La, a - a' ≠ N • f := by
    intro f hf
    apply hne
    have : a = a' + N • f := by rw [← hf]; abel
    rw [this, I.add, (I.ker N hN0 _).2 ⟨f, rfl⟩, _root_.mul_one]
  obtain ⟨b0, hb0⟩ : ∃ b0 : Dw.La, ¬ ((N : ℤ) ∣ Dw.EF b0 (a - a')) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨f, hf⟩ := mem_nsmul_of_dvd Dw N (a - a') hcon
    exact hdN f hf
  have h1 : Dw.EF b0 (a - a') = Dw.EF ((u * β) • b0) (a - a') + Dw.EF ((u' * star β) • b0) (a - a') := by
    rw [← LinearMap.add_apply, ← map_add, ← add_smul, huu, one_smul]
  have h2 : (N : ℤ) ∣ Dw.EF ((u * β) • b0) (a - a') := by
    have hd' : H.bar (u * β) • (a - a') = N • (H.bar u • (e - e')) := by
      rw [map_mul, mul_smul, smul_sub]
      change H.bar u • (star β • a - star β • a') = _
      rw [he, he', ← smul_sub]
      exact smul_comm _ _ _
    rw [Dw.adj, hd', map_nsmul, nsmul_eq_mul]
    exact Dvd.intro _ rfl
  have hb : ¬ (N : ℤ) ∣ Dw.EF ((u' * star β) • b0) (a - a') := fun h => hb0 (by rw [h1]; exact dvd_add h2 h)
  refine ⟨I.ev N ((u' * star β) • b0), ?_, ?_⟩
  · rw [← hlin, smul_smul, show β * (u' * star β) = (N : 𝓞 E) * u' by rw [← hβ]; ring, mul_smul,
      Nat.cast_smul_eq_nsmul]
    exact (I.ker N hN0 _).2 ⟨_, rfl⟩
  · refine ⟨unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a), unitOn (I.ζ N ^ Dw.EF ((u' * star β) • b0) a'),
      I.isom N hN0 _ _, I.isom N hN0 _ _, fun hc => hb ?_⟩
    have hc' := unitOn_injective hc
    rw [← (I.ζ_prim N hN0).zpow_eq_one_iff_dvd, map_sub, zpow_sub, hc', _root_.mul_inv_cancel]
end ReciprocityTheory.ChartRestriction.G.H1
