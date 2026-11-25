-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction.local_len
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:28.71285+00:00
-- url     : https://prove2.me/submissions/fe13ef80-a289-4087-b60f-63583d05c42a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalLengthFraction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_exists_length_quotient_span_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
variable {K₁ : Type} [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁))
variable {U : Type} [AddCommGroup U] [Module K₁ U] [FiniteDimensional K₁ U]
  [Module (Rv K₁ w) U] [IsScalarTower (Rv K₁ w) K₁ U]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
theorem _root_.solution (hL : QuotLocalStatement) (P : Submodule K₁ U) (Mw : Submodule (Rv K₁ w) U)
    (hMw : Mw.FG) (hMspan : Submodule.span K₁ (Mw : Set U) = ⊤) {ρ : ℕ}
    (hρ : finrank K₁ (U ⧸ P) = ρ) (e : Fin ρ → U) (he : ∀ j, e j ∈ Mw)
    (c : Fin ρ → U →ₗ[K₁] K₁) (hcP : ∀ i, ∀ x ∈ P, c i x = 0) (s : Fin ρ → ℝ) (β : ℝ)
    (hint : ∀ i, ∀ y ∈ Mw, c i y ≠ 0 → -β ≤ (ordAt w (c i y) : ℝ) + s i)
    (hdet : (Matrix.of fun i j => c i (e j)).det ≠ 0) :
    ∃ n : ℕ, Module.length (Rv K₁ w) (Mw ⧸ ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
        Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype) = n ∧
      (n : ℝ) ≤ (ordAt w (Matrix.of fun i j => c i (e j)).det : ℝ) + ∑ i, s i + ρ * β := by
  classical
  set N : Submodule (Rv K₁ w) Mw := (Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw).comap Mw.subtype
    with hN
  set T : Submodule (Rv K₁ w) Mw := ((Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
      Submodule.span (Rv K₁ w) (Set.range e)).comap Mw.subtype with hT

  have hspanP : ∀ x : U, x ∈ Submodule.span (Rv K₁ w) (P : Set U) → x ∈ P := fun x hx =>
    (Submodule.span_le (p := P.restrictScalars (Rv K₁ w))).mpr (fun y hy => hy) hx
  have hmemN : ∀ y : Mw, y ∈ N ↔ (y : U) ∈ P := by
    intro y
    constructor
    · intro hy
      exact hspanP _ (Submodule.mem_inf.mp (Submodule.mem_comap.mp hy)).1
    · intro hy
      exact Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨Submodule.subset_span hy, y.2⟩)

  let cQ : Fin ρ → (Mw ⧸ N) →ₗ[Rv K₁ w] K₁ := fun i =>
    N.liftQ (((c i).restrictScalars (Rv K₁ w)).comp Mw.subtype) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact hcP i _ ((hmemN y).mp hy))
  have hc' : ∀ i (q : Mw ⧸ N), cQ i q ≠ 0 → -β ≤ (ordAt w (cQ i q) : ℝ) + s i := by
    intro i q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact hint i y y.2 hq
  let e' : Fin ρ → Mw := fun j => ⟨e j, he j⟩
  let th : Fin ρ → Mw ⧸ N := fun j => N.mkQ (e' j)
  have hdet' : (Matrix.of fun i j => cQ i (th j)).det ≠ 0 := hdet

  let ι : (Mw ⧸ N) →ₗ[Rv K₁ w] (U ⧸ P) :=
    N.liftQ ((P.mkQ.restrictScalars (Rv K₁ w)).comp Mw.subtype) (by
      intro y hy
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero P (x := (y : U))).mpr ((hmemN y).mp hy))
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr ?_
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    exact (Submodule.Quotient.mk_eq_zero N (x := y)).mpr
      ((hmemN y).mpr ((Submodule.Quotient.mk_eq_zero P (x := (y : U))).mp hq))
  haveI : Module.Finite (Rv K₁ w) Mw := Module.Finite.iff_fg.mpr hMw
  haveI : NoZeroSMulDivisors (Rv K₁ w) (Mw ⧸ N) := by
    refine ⟨fun {r q} hrq => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply hι
    rw [map_zero]
    have h1 : r • ι q = 0 := by rw [← map_smul, hrq, map_zero]
    have hr' : (r • (1 : K₁)) ≠ 0 := by
      rw [Subring.smul_def, smul_eq_mul, mul_one]
      exact fun h => hr (Subtype.ext h)
    have h2 : (r • (1 : K₁)) • ι q = 0 := by rw [smul_one_smul]; exact h1
    exact (smul_eq_zero.mp h2).resolve_left hr'
  haveI : Module.Free (Rv K₁ w) (Mw ⧸ N) := Module.free_of_finite_type_torsion_free'

  have hthli : LinearIndependent (Rv K₁ w) th := by
    apply LinearIndependent.of_comp (LinearMap.pi fun i => cQ i)
    have hK : LinearIndependent K₁ (fun j => Matrix.transpose (Matrix.of fun i j => c i (e j)) j) :=
      Matrix.linearIndependent_cols_of_isUnit
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
    exact (LinearIndependent.iff_fractionRing (Rv K₁ w) K₁).mpr hK
  have hle1 : ρ ≤ Module.finrank (Rv K₁ w) (Mw ⧸ N) := by
    simpa using hthli.fintype_card_le_finrank
  have hle2 : Module.finrank (Rv K₁ w) (Mw ⧸ N) ≤ ρ := by
    let b := Module.Free.chooseBasis (Rv K₁ w) (Mw ⧸ N)
    have hli : LinearIndependent (Rv K₁ w) (ι ∘ b) :=
      b.linearIndependent.map' ι (LinearMap.ker_eq_bot.mpr hι)
    have hliK : LinearIndependent K₁ (ι ∘ b) :=
      (LinearIndependent.iff_fractionRing (Rv K₁ w) K₁).mp hli
    rw [Module.finrank_eq_card_chooseBasisIndex, ← hρ]
    exact hliK.fintype_card_le_finrank
  have hb : Nonempty (Module.Basis (Fin ρ) (Rv K₁ w) (Mw ⧸ N)) :=
    ⟨Module.finBasisOfFinrankEq _ _ (le_antisymm hle2 hle1)⟩
  obtain ⟨n, hn, hle⟩ := exists_length_quotient_span_le hL w (Mw ⧸ N) ρ hb cQ s β th hc' hdet'

  have hmapE : (Submodule.span (Rv K₁ w) (Set.range e')).map Mw.subtype =
      Submodule.span (Rv K₁ w) (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hmapTh : (Submodule.span (Rv K₁ w) (Set.range e')).map N.mkQ =
      Submodule.span (Rv K₁ w) (Set.range th) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hNT : N ≤ T := Submodule.comap_mono le_sup_left
  have hspan : T.map N.mkQ = Submodule.span (Rv K₁ w) (Set.range th) := by
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap]
      have hy' : (y : U) ∈ (Submodule.span (Rv K₁ w) (P : Set U) ⊓ Mw) ⊔
          Submodule.span (Rv K₁ w) (Set.range e) := hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
      rw [← hmapE] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have hyab : y = ⟨a, ha.2⟩ + b' := Subtype.ext (by simpa using hab.symm)
      have h0 : N.mkQ ⟨a, ha.2⟩ = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact (hmemN _).mpr (hspanP a ha.1)
      rw [hyab, map_add, h0, zero_add, ← hmapTh]
      exact Submodule.mem_map_of_mem hb'
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨e' j, Submodule.mem_comap.mpr
        (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)), rfl⟩
  let E : ((Mw ⧸ N) ⧸ Submodule.span (Rv K₁ w) (Set.range th)) ≃ₗ[Rv K₁ w] (Mw ⧸ T) :=
    (Submodule.quotEquivOfEq _ _ hspan.symm).trans (Submodule.quotientQuotientEquivQuotient N T hNT)
  exact ⟨n, (LinearEquiv.length_eq E).symm.trans hn, hle⟩
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalLengthFraction
